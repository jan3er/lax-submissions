import Lax3Proofs.RamBfs

/-!
The **parent-recording** variant of the masked breadth-first search of
`Lax3Proofs.RamBfs`, together with the pass that reads a shortest path
back out of the parent array — the program-side realization of the
paths the splitter strategy maintains.

`RamBfs` answers *how far*; the splitter needs *which way*. Its move at
each level isolates, for every connector vertex already played, a short
path from that vertex to the new one, taken in the arena of the round it
was played in; and `Lax3Proofs.SplitterWinOracle` states exactly what
the strategy needs of those paths, in the three fields of `PathOracle`:
a set of vertices per pair, the fact that between vertices within
distance `r` the set is the support of a genuine walk of length at most
`r`, and a bound of `r + 1` on its size. This file produces those two
facts from a machine run.

### The delta on the search

One array and one store. When the relaxation `dn < dist[w]` fires, the
expanding vertex is written into `par[w]` beside the distance; the
source is given itself as its parent, by a single store in the seed. No
other line of the search changes, and no clause of `RamBfs.Frontier`
changes either — `ParFrontier` is that invariant with one more
conjunct, and every clause of it is discharged by the corresponding
clause of `RamBfs`'s.

The parent clause is the obvious one — *a discovered vertex other than
the source has a parent one level below it, adjacent to it in the arena*
— and it survives the relaxation for one reason worth naming: the
vertex being relaxed carries the sentinel. `RamBfs`'s `qcap` already
rules out relaxing a vertex that is on the queue, and `qall` then says
that a vertex not on the queue and alive is undiscovered; so the
relaxed vertex has `dist = d + 1`, which is what makes it impossible
for it to be anybody's parent yet. That is the whole of the extra work.

### Reading the path back

`extractPathCom` walks the parent array back from a target `t` into the
output buffer `path`: `path[0] = t`, `path[1] = par[t]`, and so on for
`dist[t] + 1` cells. The machine terminates because the loop is
counted — `dist[t]` turns, one per cell — and it is *correct* because
the distance strictly decreases along parents, which is the invariant's
own clause. The buffer therefore holds the iterated parent
`parIter P t i` at cell `i`, and nothing more delicate than that is
maintained.

The walk itself is built once, math-side, by induction on the distance:
a vertex at distance `k + 1` hangs a last edge on the walk to its
parent, and the support of the result is the support of the parent's
walk together with the vertex — which is the same recursion the buffer
performs. So the buffer's cells and the walk's support are the same
set, and that equation is `PathOracle.spec`'s conclusion with the walk
existentially quantified, which is all the oracle ever asks for.

### What the driver does with it

The oracle is not computable and is not meant to be: its `path` field
is defined math-side by `Classical.choice` over the machine run, and
what a definition by choice needs is exactly an existence statement.
`bfsPath_spec` is that statement — for every state the composed program
reaches, a walk of length at most the cap whose support is the buffer's
set — and `bfsPath_ncard_le` is the `card` field. The recipe is in the
final section.
-/

namespace Lax3Proofs.RamBfsPaths

open Lax3.ColoredGraphs Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance
open Lax3Proofs.RamBfs

variable {n ns d s : ℕ} {G : SimpleGraph (Fin n)} {M O T : ℕ → ℕ}

/-! ### The invariant, with the parent clause

`RamBfs.Frontier` unchanged, plus what the parent array holds. The
clause is conditioned on the vertex being discovered — a vertex still
carrying the sentinel has whatever junk the memory started with in its
parent cell, and the search never looks at it. -/

/-- What holds of the distance array, the queue and the **parent array**
at every point of the search. -/
structure ParFrontier {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d s : ℕ)
    (D Q P : ℕ → ℕ) (head tail : ℕ) : Prop where
  /-- The search itself, as `RamBfs` states it. -/
  base : Frontier G M d s D Q head tail
  /-- The source is its own parent. -/
  root : P s = s
  /-- A discovered vertex other than the source has its parent one level
  below it. -/
  pdist : ∀ w < n, w ≠ s → D w ≤ d → D (P w) + 1 = D w
  /-- And that parent is a neighbour of it in the arena. -/
  padj : ∀ w < n, w ≠ s → D w ≤ d → MAdj G M (P w) w

namespace ParFrontier

variable {D Q P : ℕ → ℕ} {head tail : ℕ}

/-- **The vertex a relaxation fires at is undiscovered.** `qcap` bounds
everything on the queue by the head's distance plus one, so a vertex
strictly above that is not on the queue; `qall` then says that an alive
vertex off the queue has not been discovered, and the only value left is
the sentinel. This is the fact the parent clause turns on: a vertex at
`d + 1` is nobody's parent, so overwriting its distance cannot falsify
anybody else's clause. -/
theorem sentinel_of_relax (hF : Frontier G M d s D Q head tail) (hht : head < tail)
    {w : ℕ} (hadj : MAdj G M (Q head) w) (hlt : D (Q head) + 1 < D w) : D w = d + 1 := by
  have hw : w < n := hadj.lt_right
  have hcapw : D w ≤ d + 1 := hF.cap w hw
  have hnq : ∀ i < tail, Q i ≠ w := by
    intro i hi hqi
    have := hF.qcap i hi head le_rfl hht
    rw [hqi] at this
    omega
  by_contra hne
  obtain ⟨i, hi, hqi⟩ := hF.qall w hw hadj.alive_right (by omega)
  exact hnq i hi hqi

/-- **The one change the arrays ever undergo**, with the parent written
beside the distance. Every clause of `RamBfs.Frontier` survives for the
reasons `RamBfs.Frontier.relax` gives; the parent clause survives
because the relaxed vertex carried the sentinel, so no other vertex can
have had it for a parent. -/
theorem relax (hF : ParFrontier G M d s D Q P head tail) (hht : head < tail)
    {w : ℕ} (hadj : MAdj G M (Q head) w) (hlt : D (Q head) + 1 < D w) :
    ParFrontier G M d s (upd D w (D (Q head) + 1)) (upd Q tail w) (upd P w (Q head))
      head (tail + 1) := by
  have hdw : D w = d + 1 := sentinel_of_relax hF.base hht hadj hlt
  have hws : s ≠ w := by
    intro hse; rw [← hse, hF.base.src] at hdw; omega
  have hwv : w ≠ Q head := by
    intro hwe; rw [hwe] at hlt; omega
  refine ⟨hF.base.relax hht hadj hlt, (upd_of_ne _ hws).trans hF.root, fun z hz hzs hzd => ?_,
    fun z hz hzs hzd => ?_⟩
  · by_cases hzw : z = w
    · subst hzw
      rw [upd_self, upd_self, upd_of_ne _ (Ne.symm hwv)]
    · rw [upd_of_ne _ hzw] at hzd ⊢
      have hpz : P z ≠ w := by
        intro hpe
        have := hF.pdist z hz hzs hzd
        rw [hpe, hdw] at this
        omega
      rw [upd_of_ne _ hzw, upd_of_ne _ hpz]
      exact hF.pdist z hz hzs hzd
  · by_cases hzw : z = w
    · subst hzw
      rw [upd_self]
      exact hadj
    · rw [upd_of_ne _ hzw] at hzd
      rw [upd_of_ne _ hzw]
      exact hF.padj z hz hzs hzd

end ParFrontier

/-! The two states the seed can leave. Neither of them has discovered
anything but the source, so the parent clause is vacuous in both and the
only content is that the source is its own parent. -/

/-- A live source goes on the queue, and is its own parent. -/
theorem parFrontier_seed_alive (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d : ℕ) (hs : s < n)
    (hms : M s ≠ 0) {g Q p : ℕ → ℕ} (hg : ∀ j < n, g j = d + 1) (hQ : Q 0 = s) :
    ParFrontier G M d s (upd g s 0) Q (upd p s s) 0 1 := by
  have hval : ∀ z, z < n → z ≠ s → upd g s 0 z = d + 1 := fun z hz hzs => by
    rw [upd_of_ne _ hzs]; exact hg z hz
  exact ⟨frontier_seed_alive G M d hs hms hg hQ, upd_self .., fun z hz hzs hzd => by
      rw [hval z hz hzs] at hzd; omega,
    fun z hz hzs hzd => by rw [hval z hz hzs] at hzd; omega⟩

/-- A dead source does not go on the queue, and is still its own
parent. -/
theorem parFrontier_seed_dead (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d : ℕ) (hs : s < n)
    (hms : M s = 0) {g Q p : ℕ → ℕ} (hg : ∀ j < n, g j = d + 1) :
    ParFrontier G M d s (upd g s 0) Q (upd p s s) 0 0 := by
  have hval : ∀ z, z < n → z ≠ s → upd g s 0 z = d + 1 := fun z hz hzs => by
    rw [upd_of_ne _ hzs]; exact hg z hz
  exact ⟨frontier_seed_dead G M d hs hms hg, upd_self .., fun z hz hzs hzd => by
      rw [hval z hz hzs] at hzd; omega,
    fun z hz hzs hzd => by rw [hval z hz hzs] at hzd; omega⟩

/-! ### What the search leaves in the two arrays

The exit reading, as a predicate on the two cell functions alone: it is
what the extraction pass is handed, and it mentions neither the queue
nor the machine. -/

/-- **A shortest-path tree**, as two arrays: the distances decide every
threshold up to the cap, and the parents step down towards the source
along edges of the arena. -/
structure ParTree {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d s : ℕ) (D P : ℕ → ℕ) :
    Prop where
  /-- Nothing exceeds the sentinel. -/
  cap : ∀ w < n, D w ≤ d + 1
  /-- The source is at distance zero. -/
  root : D s = 0
  /-- And is its own parent. -/
  self : P s = s
  /-- A written distance is achieved by a walk of the arena. -/
  sound : ∀ w < n, D w ≤ d → WD G M (D w) s w
  /-- And nothing the arena puts within the cap is missed. -/
  reach : ∀ k ≤ d, ∀ w, WD G M k s w → D w ≤ k
  /-- A discovered vertex other than the source has its parent one level
  below it. -/
  pdist : ∀ w < n, w ≠ s → D w ≤ d → D (P w) + 1 = D w
  /-- And that parent is a neighbour of it in the arena. -/
  padj : ∀ w < n, w ≠ s → D w ≤ d → MAdj G M (P w) w

/-- **The exit reading.** Once the queue is empty the invariant is the
answer: `RamBfs.Frontier.complete` supplies the one clause that is not
already a clause of the invariant. -/
theorem ParFrontier.tree {D Q P : ℕ → ℕ} {tail : ℕ}
    (hF : ParFrontier G M d s D Q P tail tail) : ParTree G M d s D P :=
  ⟨hF.base.cap, hF.base.src, hF.root, hF.base.sound, hF.base.complete, hF.pdist, hF.padj⟩

namespace ParTree

variable {D P : ℕ → ℕ}

/-- The threshold reading of the distance array, as `RamBfs` states
it. -/
theorem dist_le_iff (hT : ParTree G M d s D P) {w : ℕ} (hw : w < n) {k : ℕ} (hk : k ≤ d) :
    D w ≤ k ↔ WD G M k s w :=
  ⟨fun h => (hT.sound w hw (by omega)).mono h, hT.reach k hk w⟩

/-- Only the source is at distance zero. -/
theorem eq_src_of_dist_zero (hT : ParTree G M d s D P) {w : ℕ} (hw : w < n) (h : D w = 0) :
    w = s := by
  have := hT.sound w hw (by omega)
  rw [h] at this
  exact (this.eq_of_zero).symm

end ParTree

/-! ### Iterated parents

The buffer the extraction pass fills holds the iterated parent, so that
is the one function the specification of the pass speaks. Both ways of
peeling an iterate are wanted: the program peels from the outside, the
walk construction peels from the inside. -/

/-- The `i`-th ancestor of `t` in the parent array. -/
def parIter (P : ℕ → ℕ) (t i : ℕ) : ℕ := P^[i] t

@[simp] theorem parIter_zero (P : ℕ → ℕ) (t : ℕ) : parIter P t 0 = t := rfl

/-- One more step, taken at the far end: what the program does. -/
theorem parIter_succ (P : ℕ → ℕ) (t i : ℕ) : parIter P t (i + 1) = P (parIter P t i) :=
  Function.iterate_succ_apply' P i t

/-- One more step, taken at the near end: what the walk construction
does. -/
theorem parIter_succ' (P : ℕ → ℕ) (t i : ℕ) : parIter P t (i + 1) = parIter P (P t) i :=
  Function.iterate_succ_apply P i t

/-- **The ancestors of a discovered vertex are discovered**, one level
lower at each step. This is what makes the extraction loop's reads in
range and its counter enough for termination. -/
theorem ParTree.chain {D P : ℕ → ℕ} (hT : ParTree G M d s D P) {t : ℕ} (ht : t < n)
    (hdt : D t ≤ d) : ∀ i ≤ D t, parIter P t i < n ∧ D (parIter P t i) = D t - i := by
  intro i
  induction i with
  | zero => intro _; exact ⟨ht, by simp⟩
  | succ i ih =>
      intro hi
      obtain ⟨hlt, heq⟩ := ih (by omega)
      have hne : parIter P t i ≠ s := by
        intro hse
        rw [hse, hT.root] at heq
        omega
      have hle : D (parIter P t i) ≤ d := by omega
      have hpd := hT.pdist _ hlt hne hle
      have hpa := hT.padj _ hlt hne hle
      rw [parIter_succ]
      exact ⟨hpa.lt_left, by omega⟩

/-- The last ancestor is the source. -/
theorem ParTree.chain_last {D P : ℕ → ℕ} (hT : ParTree G M d s D P) {t : ℕ} (ht : t < n)
    (hdt : D t ≤ d) : parIter P t (D t) = s := by
  obtain ⟨hlt, heq⟩ := hT.chain ht hdt (D t) le_rfl
  exact hT.eq_src_of_dist_zero hlt (by omega)

/-! ### The set a buffer names

The oracle's `path` field is a set of vertices, and the buffer is a
prefix of an array of numbers; this is the one translation between
them. -/

/-- The vertices the first `L + 1` cells of `Buf` name. -/
def bufSet (n L : ℕ) (Buf : ℕ → ℕ) : Set (Fin n) := {z : Fin n | ∃ i ≤ L, (z : ℕ) = Buf i}

theorem mem_bufSet {n L : ℕ} {Buf : ℕ → ℕ} {z : Fin n} :
    z ∈ bufSet n L Buf ↔ ∃ i ≤ L, (z : ℕ) = Buf i := Iff.rfl

/-- Only the cells that are read matter. -/
theorem bufSet_congr {n L : ℕ} {Buf Buf' : ℕ → ℕ} (h : ∀ i ≤ L, Buf i = Buf' i) :
    bufSet n L Buf = bufSet n L Buf' := by
  ext z
  simp only [mem_bufSet]
  exact ⟨fun ⟨i, hi, hz⟩ => ⟨i, hi, by rw [hz, h i hi]⟩,
    fun ⟨i, hi, hz⟩ => ⟨i, hi, by rw [hz, ← h i hi]⟩⟩

/-! ### The walk

Built once, by induction on the distance, and built so that its support
is *the ancestors of its endpoint* — which is what the buffer holds.
The recursion is the same on both sides: a vertex at distance `k + 1`
hangs a last edge on its parent's walk, and its ancestors are its
parent's ancestors together with itself. -/

/-- **The path the parent array records.** A vertex at distance `k` is
joined to the source by a walk of the arena of length exactly `k`, whose
support is the set of the vertex's first `k` ancestors. -/
theorem ParTree.walk {D P : ℕ → ℕ} (hT : ParTree G M d s D P) (hs : s < n) :
    ∀ k ≤ d, ∀ v : Fin n, D (v : ℕ) = k →
      ∃ p : (masked G M).Walk ⟨s, hs⟩ v, p.length = k ∧
        {z : Fin n | z ∈ p.support} = bufSet n k (parIter P (v : ℕ)) := by
  intro k
  induction k with
  | zero =>
      intro _ v hv
      obtain rfl : v = ⟨s, hs⟩ := Fin.ext (hT.eq_src_of_dist_zero v.isLt hv)
      refine ⟨.nil, rfl, ?_⟩
      ext z
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton, Set.mem_setOf_eq, mem_bufSet]
      constructor
      · rintro rfl; exact ⟨0, le_rfl, rfl⟩
      · rintro ⟨i, hi, hz⟩
        have : i = 0 := by omega
        subst this
        exact Fin.ext hz
  | succ k ih =>
      intro hk v hv
      have hvs : (v : ℕ) ≠ s := by
        intro hse
        rw [hse, hT.root] at hv
        omega
      have hle : D (v : ℕ) ≤ d := by omega
      have hpd := hT.pdist _ v.isLt hvs hle
      obtain ⟨hu, hv', hadjm⟩ := hT.padj _ v.isLt hvs hle
      have hadj : (masked G M).Adj ⟨P (v : ℕ), hu⟩ v := hadjm
      obtain ⟨p, hplen, hpsup⟩ :=
        ih (by omega) ⟨P (v : ℕ), hu⟩ (by simp only []; omega)
      refine ⟨p.concat hadj, by rw [SimpleGraph.Walk.length_concat, hplen], ?_⟩
      ext z
      simp only [SimpleGraph.Walk.support_concat, List.mem_append,
        List.mem_singleton, Set.mem_setOf_eq, mem_bufSet]
      constructor
      · rintro (hz | rfl)
        · have : z ∈ {z : Fin n | z ∈ p.support} := hz
          rw [hpsup] at this
          obtain ⟨i, hi, hzi⟩ := this
          exact ⟨i + 1, by omega, by rw [hzi, parIter_succ']⟩
        · exact ⟨0, by omega, rfl⟩
      · rintro ⟨i, hi, hz⟩
        cases i with
        | zero => exact Or.inr (Fin.ext hz)
        | succ i =>
            refine Or.inl ?_
            have : z ∈ bufSet n k (parIter P (P (v : ℕ))) :=
              ⟨i, by omega, by rw [hz, parIter_succ']⟩
            rw [← hpsup] at this
            exact this

/-- **The size of the recorded path.** A walk of length `k` has at most
`k + 1` vertices on it, so the set its support names is that small. -/
theorem ncard_support_le {u v : Fin n} {A : SimpleGraph (Fin n)} (p : A.Walk u v) {k : ℕ}
    (hp : p.length ≤ k) : ({z : Fin n | z ∈ p.support}).ncard ≤ k + 1 := by
  classical
  have hcoe : {z : Fin n | z ∈ p.support} = (p.support.toFinset : Set (Fin n)) := by
    ext z; simp
  rw [hcoe, Set.ncard_coe_finset]
  calc p.support.toFinset.card ≤ p.support.length := List.toFinset_card_le _
    _ = p.length + 1 := p.length_support
    _ ≤ k + 1 := by omega

/-! ### The program

`RamBfs`'s five arrays and one more, `par`. The distance fill is
`RamBfs.initDist` unchanged — the parent array needs no fill, since the
invariant says nothing about a vertex that is still carrying the
sentinel and the search never reads such a cell. -/

/-- Seed the search: `RamBfs.seedSrc` with one more store. The source is
its own parent, which is what makes the walk back terminate at it. -/
def seedSrcPar : Com :=
  .seq (.ite (.lt (.lit 0) (.get "alv" (.var "src")))
          (.assign "tail" (.lit 1)) (.assign "tail" (.lit 0)))
    (.seq (.store "dist" (.var "src") (.lit 0))
      (.seq (.store "par" (.var "src") (.var "src"))
        (.seq (.store "q" (.lit 0) (.var "src"))
          (.seq (.assign "head" (.lit 0)) (.assign "sc" (.lit 0))))))

/-- One slot of the block being scanned: `RamBfs.scanSlot` with the
expanding vertex recorded beside the distance on the relaxing path. -/
def scanSlotPar : Com :=
  .seq (.assign "w" (.get "tgt" (.var "j")))
    (.seq (.ite (.lt (.lit 0) (.get "alv" (.var "w")))
            (.ite (.lt (.var "dn") (.get "dist" (.var "w")))
              (.seq (.store "dist" (.var "w") (.var "dn"))
                (.seq (.store "par" (.var "w") (.var "v"))
                  (.seq (.store "q" (.var "tail") (.var "w"))
                    (.assign "tail" (.add (.var "tail") (.lit 1))))))
              .skip)
            .skip)
      (.seq (.assign "sc" (.add (.var "sc") (.lit 1)))
        (.assign "j" (.add (.var "j") (.lit 1)))))

/-- Take the next vertex off the queue and scan its whole block. -/
def expandRowPar : Com :=
  .seq (.assign "v" (.get "q" (.var "head")))
    (.seq (.assign "dv" (.get "dist" (.var "v")))
      (.seq (.assign "dn" (.add (.var "dv") (.lit 1)))
        (.seq (Csr.loadRow "off" "v" "j" "jend")
          (.seq (Csr.scan "j" "jend" scanSlotPar)
            (.assign "head" (.add (.var "head") (.lit 1)))))))

/-- The search itself: empty the queue. -/
def bfsParDrain : Com := Queue.drain "head" "tail" expandRowPar

/-- **The parent-recording search.** Clear the distances, seed the
source, search. -/
def bfsParCom (d : ℕ) : Com := .seq (initDist d) (.seq seedSrcPar bfsParDrain)

/-! ### The state of the machine -/

/-- `RamBfs.SearchEnv` and the parent array. -/
def SearchEnvPar (n ns s : ℕ) (O T M D Q P : ℕ → ℕ) (τ : Env) : Prop :=
  SearchEnv n ns s O T M D Q τ ∧ τ.arrs "par" = arrOf n P

/-- The invariant of the block scan: `RamBfs.ScanInv` with the parent
array carried along. -/
def ScanInvPar {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (ns d s head v dv sc₀ : ℕ)
    (O T Q₀ : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ D Q P, SearchEnvPar n ns s O T M D Q P τ ∧
    ParFrontier G M d s D Q P head (τ.vars "tail") ∧
    τ.vars "head" = head ∧ head < τ.vars "tail" ∧ Q head = v ∧ D v = dv ∧
    τ.vars "v" = v ∧ τ.vars "dv" = dv ∧ τ.vars "dn" = dv + 1 ∧
    τ.vars "jend" = O (v + 1) ∧ O v ≤ τ.vars "j" ∧ τ.vars "j" ≤ O (v + 1) ∧
    τ.vars "sc" = sc₀ + (τ.vars "j" - O v) ∧
    (∀ j', O v ≤ j' → j' < τ.vars "j" → M (T j') ≠ 0 → D (T j') ≤ dv + 1) ∧
    (∀ i < head, Q i = Q₀ i)

/-- One slot of the block of `v`. The three paths are `RamBfs`'s three,
and the relaxing one is `ParFrontier.relax`. -/
theorem scanSlotPar_run {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {head v dv sc₀ : ℕ} (hv : v < n) (hsc₀ : sc₀ + Csr.rowLen O v ≤ ns)
    {Q₀ : ℕ → ℕ} {τ : Env} (hI : ScanInvPar G M ns d s head v dv sc₀ O T Q₀ τ)
    (hjlt : τ.vars "j" < O (v + 1)) :
    ∃ τ' K, Run B scanSlotPar τ τ' K ∧ K ≤ 44 ∧
      ScanInvPar G M ns d s head v dv sc₀ O T Q₀ τ' ∧ τ'.vars "j" = τ.vars "j" + 1 := by
  obtain ⟨D, Q, P, ⟨⟨hn, hsrc, hoff, htgt, halv, hdist, hq⟩, hpar⟩, hF, hhead, hht, hqv, hDv,
    hvv, hdvv, hdnv, hje, hj₁, hj₂, hsc, hscan, hq₀⟩ := hI
  obtain ⟨hvn', hdvle, hmv⟩ := hF.base.qmem head hht
  rw [hqv] at hvn' hdvle hmv
  rw [hDv] at hdvle
  have hrow : Csr.rowLen O v = O (v + 1) - O v := rfl
  have hns : O (v + 1) ≤ ns := hcsr.le_ns (by omega)
  have hjns : τ.vars "j" < ns := by omega
  have hwn : T (τ.vars "j") < n := hcsr.target_lt' hv hjlt
  have hrj : (τ.arrs "tgt").getD (τ.vars "j") 0 = T (τ.vars "j") := by
    rw [htgt, getD_arrOf T hjns]
  have hrj' : (τ.arrs "tgt")[τ.vars "j"]?.getD 0 = T (τ.vars "j") := by
    rw [← List.getD_eq_getElem?_getD]; exact hrj
  have hjlen : τ.vars "j" < (τ.arrs "tgt").length := by rw [htgt, length_arrOf]; omega
  have hwB : (τ.arrs "tgt").getD (τ.vars "j") 0 < B := by rw [hrj]; omega
  have halvlen : (τ.arrs "tgt").getD (τ.vars "j") 0 < (τ.arrs "alv").length := by
    rw [hrj, halv, length_arrOf]; exact hwn
  have halvv : (τ.arrs "alv").getD ((τ.arrs "tgt").getD (τ.vars "j") 0) 0
      = M (T (τ.vars "j")) := by rw [hrj, halv, getD_arrOf M hwn]
  have halvB : (τ.arrs "alv").getD ((τ.arrs "tgt").getD (τ.vars "j") 0) 0 < B := by
    rw [halvv]; exact hMB _ hwn
  have hdistlen : (τ.arrs "tgt").getD (τ.vars "j") 0 < (τ.arrs "dist").length := by
    rw [hrj, hdist, length_arrOf]; exact hwn
  have hparlen : (τ.arrs "tgt").getD (τ.vars "j") 0 < (τ.arrs "par").length := by
    rw [hrj, hpar, length_arrOf]; exact hwn
  have hdistv : (τ.arrs "dist").getD ((τ.arrs "tgt").getD (τ.vars "j") 0) 0
      = D (T (τ.vars "j")) := by rw [hrj, hdist, getD_arrOf D hwn]
  have hdistB : (τ.arrs "dist").getD ((τ.arrs "tgt").getD (τ.vars "j") 0) 0 < B := by
    rw [hdistv]; have := hF.base.cap _ hwn; omega
  have hqlen : (τ.arrs "q").length = n := by rw [hq, length_arrOf]
  have hscB : τ.vars "sc" + 1 < B := by omega
  have hjB : τ.vars "j" + 1 < B := by omega
  have hdnB : τ.vars "dn" < B := by omega
  have hvB : τ.vars "v" < B := by omega
  have hMw : M (T (τ.vars "j")) < B := hMB _ hwn
  have hDw : D (T (τ.vars "j")) ≤ d + 1 := hF.base.cap _ hwn
  have htlB : τ.vars "tail" ≤ n := hF.base.tl
  -- the two reads the two conditionals make, in the shape the walk states them
  have hbrAlv : ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).arrs "alv").getD
      ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "w") 0
      = M (T (τ.vars "j")) := by rw [arrs_setVar, vars_setVar]; simpa using halvv
  have hbrDist : ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).arrs "dist").getD
      ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "w") 0
      = D (T (τ.vars "j")) := by rw [arrs_setVar, vars_setVar]; simpa using hdistv
  have hbrDn : (τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "dn" = dv + 1 := by
    simpa using hdnv
  -- **the room argument**, which only the relaxing path needs
  have hroom : dv + 1 < D (T (τ.vars "j")) → τ.vars "tail" < n := by
    intro hlt'
    refine hF.base.tail_lt hwn ?_
    intro i hi hqi
    have hc := hF.base.qcap i hi head le_rfl hht
    rw [hqi, hqv, hDv] at hc
    omega
  have hvne : dv + 1 < D (T (τ.vars "j")) → v ≠ T (τ.vars "j") := by
    intro hlt' hve
    rw [← hve, hDv] at hlt'
    omega
  run_vcg
  · -- the slot names a live vertex, and it takes the offer
    have hmw : M (T (τ.vars "j")) ≠ 0 := by omega
    have hlt' : dv + 1 < D (T (τ.vars "j")) := by omega
    have hadj : MAdj G M (Q head) (T (τ.vars "j")) := by
      rw [hqv]; exact hcsr.madj_of_slot hv hj₁ hjlt hmv hmw
    have hltq : D (Q head) + 1 < D (T (τ.vars "j")) := by rw [hqv, hDv]; exact hlt'
    have hrelax := hF.relax hht hadj hltq
    rw [hqv, hDv] at hrelax
    refine ⟨⟨upd D (T (τ.vars "j")) (dv + 1), upd Q (τ.vars "tail") (T (τ.vars "j")),
      upd P (T (τ.vars "j")) v,
      ⟨⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt], by simp [halv],
          by simp [hdist, hrj', hdnv, set_arrOf_eq_upd],
          by simp [hq, hrj', set_arrOf_eq_upd]⟩,
        by simp [hpar, hrj', hvv, set_arrOf_eq_upd]⟩,
      by simpa using hrelax, by simp [hhead], by simp; omega,
      (upd_of_ne _ (show head ≠ τ.vars "tail" by omega)).trans hqv,
      (upd_of_ne _ (hvne hlt')).trans hDv,
      by simp [hvv], by simp [hdvv], by simp [hdnv], by simp [hje], by simp; omega,
      by simp; omega, by simp [hsc]; omega, ?_,
      fun i hi => (upd_of_ne _ (by omega)).trans (hq₀ i hi)⟩, by simp⟩
    intro j' hj₁' hj₂' hmj'
    simp only [vars_setVar] at hj₂'
    by_cases hje' : T j' = T (τ.vars "j")
    · rw [hje', upd_self]
    · rw [upd_of_ne _ hje']
      rcases Nat.lt_or_ge j' (τ.vars "j") with hlt'' | hge''
      · exact hscan j' hj₁' hlt'' hmj'
      · exact absurd (show j' = τ.vars "j" by simp at hj₂'; omega) (by rintro rfl; exact hje' rfl)
  · -- live, but already at most one level below: nothing is written
    refine ⟨⟨D, Q, P, ⟨⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt],
        by simp [halv], by simp [hdist], by simp [hq]⟩, by simp [hpar]⟩,
      by simpa using hF, by simp [hhead], by simp [hht], by simp [hqv], hDv,
      by simp [hvv], by simp [hdvv], by simp [hdnv], by simp [hje], by simp; omega,
      by simp; omega, by simp [hsc]; omega, ?_, hq₀⟩, by simp⟩
    intro j' hj₁' hj₂' hmj'
    simp only [vars_setVar] at hj₂'
    rcases Nat.lt_or_ge j' (τ.vars "j") with hlt'' | hge''
    · exact hscan j' hj₁' hlt'' hmj'
    · have : j' = τ.vars "j" := by simp at hj₂'; omega
      subst this
      omega
  · -- a dead target is passed over
    refine ⟨⟨D, Q, P, ⟨⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt],
        by simp [halv], by simp [hdist], by simp [hq]⟩, by simp [hpar]⟩,
      by simpa using hF, by simp [hhead], by simp [hht], by simp [hqv], hDv,
      by simp [hvv], by simp [hdvv], by simp [hdnv], by simp [hje], by simp; omega,
      by simp; omega, by simp [hsc]; omega, ?_, hq₀⟩, by simp⟩
    intro j' hj₁' hj₂' hmj'
    simp only [vars_setVar] at hj₂'
    rcases Nat.lt_or_ge j' (τ.vars "j") with hlt'' | hge''
    · exact hscan j' hj₁' hlt'' hmj'
    · have : j' = τ.vars "j" := by simp at hj₂'; omega
      subst this
      omega

/-- **The whole block of `v`, scanned**: the kit's row scan, at
forty-eight per slot. -/
theorem scanPar_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {head v dv sc₀ : ℕ} (hv : v < n) (hsc₀ : sc₀ + Csr.rowLen O v ≤ ns) {Q₀ : ℕ → ℕ} :
    Spec B (fun τ => ScanInvPar G M ns d s head v dv sc₀ O T Q₀ τ ∧ τ.vars "j" = O v)
      (Csr.scan "j" "jend" scanSlotPar)
      (fun _ τ' => ScanInvPar G M ns d s head v dv sc₀ O T Q₀ τ' ∧ τ'.vars "j" = O (v + 1))
      (48 * Csr.rowLen O v + 4) := by
  have hrow : Csr.rowLen O v = O (v + 1) - O v := rfl
  have hns : O (v + 1) ≤ ns := hcsr.le_ns (by omega)
  refine Csr.rowScan_spec B (48 * Csr.rowLen O v + 4) (O (v + 1)) 44 "j" "jend" scanSlotPar
    (ScanInvPar G M ns d s head v dv sc₀ O T Q₀) (by omega) (fun σ hσ => ?_)
    (fun σ hσ hlt => ?_) (fun _ hσ => hσ.1) (fun σ hσ => by rw [hσ.2]; omega)
  · obtain ⟨D, Q, P, -, -, -, -, -, -, -, -, -, hje, -, hjle, -, -, -⟩ := hσ
    exact ⟨hje, hjle⟩
  · obtain ⟨σ', K', hr, hK, hI', hj'⟩ := scanSlotPar_run hcsr hnB hnsB hdB hMB hv hsc₀ hσ hlt
    exact ⟨σ', K', hr, hI', hj', hK⟩

/-! ### Emptying the queue -/

/-- The invariant of the search loop. -/
def DrainInvPar {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (ns d s : ℕ) (O T : ℕ → ℕ)
    (τ : Env) : Prop :=
  ∃ D Q P, SearchEnvPar n ns s O T M D Q P τ ∧
    ParFrontier G M d s D Q P (τ.vars "head") (τ.vars "tail") ∧
    τ.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head"), Csr.rowLen O (Q i)

/-- Taking one vertex off the queue and scanning its whole block. -/
theorem expandRowPar_run {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B) {D Q P : ℕ → ℕ} {τ : Env}
    (hse : SearchEnvPar n ns s O T M D Q P τ)
    (hF : ParFrontier G M d s D Q P (τ.vars "head") (τ.vars "tail"))
    (hht : τ.vars "head" < τ.vars "tail")
    (hsum : τ.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head"), Csr.rowLen O (Q i)) :
    ∃ τ' K, Run B expandRowPar τ τ' K ∧ K ≤ 48 * Csr.rowLen O (Q (τ.vars "head")) + 30 ∧
      DrainInvPar G M ns d s O T τ' ∧ τ'.vars "head" = τ.vars "head" + 1 ∧
      τ'.vars "sc" = τ.vars "sc" + Csr.rowLen O (Q (τ.vars "head")) := by
  obtain ⟨⟨hn, hsrc, hoff, htgt, halv, hdist, hq⟩, hpar⟩ := id hse
  have htln := hF.base.tl
  have hhn : τ.vars "head" < n := by omega
  obtain ⟨v, hvdef⟩ : ∃ v, Q (τ.vars "head") = v := ⟨_, rfl⟩
  rw [hvdef]
  obtain ⟨hvn, hdvd, hmv⟩ := hF.base.qmem _ hht
  rw [hvdef] at hvn hdvd hmv
  have hrow : Csr.rowLen O v = O (v + 1) - O v := rfl
  have hns : O (v + 1) ≤ ns := hcsr.le_ns (by omega)
  have hov : O v ≤ O (v + 1) := hcsr.mono v hvn
  -- the block of the vertex just dequeued is paid for out of the target array
  have hsc₀ : τ.vars "sc" + Csr.rowLen O v ≤ ns := by
    have hstep : ∑ i ∈ Finset.range (τ.vars "head" + 1), Csr.rowLen O (Q i) ≤ ns :=
      hcsr.sum_rowLen_queue (fun i hi => (hF.base.qmem i (by omega)).1)
        (fun i hi j hj hqe => hF.base.qinj i (by omega) j (by omega) hqe)
    rw [Finset.sum_range_succ, hvdef] at hstep
    omega
  have hcsrRel : Csr "off" "tgt" n ns n O T τ :=
    ⟨hoff, htgt, fun i hi => hcsr.mono i hi, hcsr.last, fun p hp => hcsr.target_lt p hp⟩
  have hrv : (τ.arrs "q").getD (τ.vars "head") 0 = v := by
    rw [hq, getD_arrOf Q hhn, hvdef]
  have hrv' : (τ.arrs "q")[τ.vars "head"]?.getD 0 = v := by
    rw [← List.getD_eq_getElem?_getD]; exact hrv
  have hqlen : τ.vars "head" < (τ.arrs "q").length := by rw [hq, length_arrOf]; omega
  have hvB : (τ.arrs "q").getD (τ.vars "head") 0 < B := by rw [hrv]; omega
  have hdlen : ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).vars "v")
      < ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).arrs "dist").length := by
    rw [arrs_setVar, vars_setVar, hdist, length_arrOf]; simpa [hrv'] using hvn
  have hdval : ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).arrs "dist").getD
      ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).vars "v") 0 = D v := by
    rw [arrs_setVar, vars_setVar]
    simp only [hrv, hdist]
    exact getD_arrOf D hvn
  have hdval' : (τ.arrs "dist")[(τ.arrs "q")[τ.vars "head"]?.getD 0]?.getD 0 = D v := by
    rw [hrv', ← List.getD_eq_getElem?_getD, hdist, getD_arrOf D hvn]
  have hdB' : ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).arrs "dist").getD
      ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).vars "v") 0 < B := by
    rw [hdval]; omega
  have hdvB : ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).setVar "dv"
      (((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).arrs "dist").getD
        ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).vars "v") 0)).vars "dv" = D v := by
    simp [hdval']
  have hheadB : τ.vars "head" + 1 < B := by omega
  -- the scan, stated so that what it gives back is what this turn owes
  have hscanSpec : Spec B
      (fun σ => ScanInvPar G M ns d s (τ.vars "head") v (D v) (τ.vars "sc") O T Q σ ∧
        σ.vars "j" = O v)
      (Csr.scan "j" "jend" scanSlotPar)
      (fun _ σ' => DrainInvPar G M ns d s O T (σ'.setVar "head" (τ.vars "head" + 1)) ∧
        σ'.vars "head" = τ.vars "head" ∧
        σ'.vars "sc" = τ.vars "sc" + Csr.rowLen O v ∧ σ'.vars "head" + 1 < B)
      (48 * Csr.rowLen O v + 4) :=
    (scanPar_spec hcsr hnB hnsB hdB hMB hvn hsc₀ (Q₀ := Q)).post fun _ σ' _ hQ => by
      obtain ⟨⟨D', Q', P', hse', hF', hhead', hht', hqv', hDv', hvv', hdvv', hdnv', hje',
        hjge', hjle', hsc', hscanned, hq₀'⟩, hj₄⟩ := hQ
      obtain ⟨⟨hn', hsrc', hoff', htgt', halv', hdist', hq'⟩, hpar'⟩ := id hse'
      have hscv : σ'.vars "sc" = τ.vars "sc" + Csr.rowLen O v := by rw [hsc', hj₄, hrow]
      refine ⟨⟨D', Q', P', ⟨⟨by simp [hn'], by simp [hsrc'], by simp [hoff'], by simp [htgt'],
          by simp [halv'], by simp [hdist'], by simp [hq']⟩, by simp [hpar']⟩, ?_, ?_⟩,
        hhead', hscv, by omega⟩
      · -- the search is live one vertex further along
        refine ⟨⟨hF'.base.cap, hF'.base.src, hF'.base.sound, by simp; omega,
          by simpa using hF'.base.tl, by simpa using hF'.base.qmem,
          by simpa using hF'.base.qall, by simpa using hF'.base.qinj,
          by simpa using hF'.base.qmono, ?_, ?_⟩, hF'.root, hF'.pdist, hF'.padj⟩
        · intro i hi j hj₁ hj₂
          simp at hi hj₁ hj₂
          exact hF'.base.qcap i hi j (by omega) hj₂
        · intro i hi z hz
          simp at hi
          rcases Nat.lt_or_ge i (τ.vars "head") with hlt | hge
          · exact hF'.base.exp i hlt z hz
          · have hie : i = τ.vars "head" := by omega
            subst hie
            rw [hqv'] at hz ⊢
            rw [hDv']
            obtain ⟨j', hj'₁, hj'₂, hj'₃⟩ := hcsr.slot_of_madj hz
            rw [← hj'₃]
            exact hscanned j' hj'₁ (by rw [hj₄]; exact hj'₂) (by rw [hj'₃]; exact hz.alive_right)
      · -- the count of scanned slots is the sum over the queue
        show σ'.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head" + 1), Csr.rowLen O (Q' i)
        rw [Finset.sum_range_succ,
          Finset.sum_congr rfl fun i hi => by rw [hq₀' i (Finset.mem_range.1 hi)],
          ← hsum, hqv', hscv]
  run_vcg [Csr.loadRow_spec B n ns n "off" "tgt" "v" "j" "jend" O T (by decide) (by decide),
    hscanSpec]
  · -- what the block did is what the scan handed back
    simp_all
  · -- the two offset reads: a row of the structure, and its number a word
    exact ⟨⟨by simpa using hcsrRel, by omega, hnsB⟩, by simp [hrv']; omega,
      by simp [hrv']; omega⟩
  · -- the scan starts at the top of the block, in the state the reads left
    obtain ⟨-, -, -, rfl⟩ := ‹Csr.LoadRowPost "off" "tgt" "v" "j" "jend" n ns n O T _ _›
    refine ⟨⟨D, Q, P, ⟨⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt],
        by simp [halv], by simp [hdist], by simp [hq]⟩, by simp [hpar]⟩,
      by simpa using hF, by simp, by simpa using hht, hvdef, rfl, by simp [hrv'],
      by simp [hdval'], by simp [hdval'], by simp [hrv'], by simp [hrv'],
      by simpa [hrv'] using hov, by simp [hrv'], ?_, fun i _ => rfl⟩, by simp [hrv']⟩
    intro j' h₁ h₂ h₃
    simp [hrv'] at h₂
    omega

/-- The potential the search is paid out of: forty-eight units per slot
not yet looked at, forty-four per vertex not yet enqueued, and
forty-four per vertex still waiting on the queue. It is `RamBfs.Pot`
with the constants raised by the store the parent array costs. -/
def PotPar (n ns : ℕ) (τ : Env) : ℕ :=
  48 * (ns - τ.vars "sc") + 44 * (n - τ.vars "tail") + 44 * (τ.vars "tail" - τ.vars "head")

/-- **The search.** The queue is emptied, and the whole cost of doing so
is paid out of the potential. -/
theorem drainPar_run {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B) {τ : Env}
    (hI : DrainInvPar G M ns d s O T τ) :
    ∃ τ' K, Run B bfsParDrain τ τ' K ∧ DrainInvPar G M ns d s O T τ' ∧
      τ'.vars "head" = τ'.vars "tail" ∧ K + PotPar n ns τ' ≤ PotPar n ns τ + 4 := by
  refine Queue.drain_run B n n "q" "head" "tail" expandRowPar (DrainInvPar G M ns d s O T)
    (PotPar n ns) (fun σ hσ => ?_) hnB (fun σ hσ hlt => ?_) hI
  · obtain ⟨D₁, Q₁, P₁, ⟨⟨-, -, -, -, -, -, hq⟩, -⟩, hFr, -⟩ := hσ
    exact ⟨Q₁, σ.vars "head", σ.vars "tail", hq, rfl, rfl, hFr.base.hd, hFr.base.tl,
      fun i hi => (hFr.base.qmem i hi).1⟩
  · obtain ⟨D₁, Q₁, P₁, hse, hFr, hsum⟩ := hσ
    obtain ⟨σ', K, hrun, hK, hI', hhead', hsc'⟩ :=
      expandRowPar_run hcsr hnB hnsB hdB hMB hse hFr hlt hsum
    refine ⟨σ', K, hrun, hI', ?_⟩
    obtain ⟨D₂, Q₂, P₂, -, hFr', hsum'⟩ := hI'
    have hhd := hFr'.base.hd
    have htl := hFr'.base.tl
    have hsc₂ : σ'.vars "sc" ≤ ns := by
      rw [hsum']
      exact hcsr.sum_rowLen_queue (fun i hi => (hFr'.base.qmem i (by omega)).1)
        (fun i hi j hj hqe => hFr'.base.qinj i (by omega) j (by omega) hqe)
    have hhd0 := hFr.base.hd
    have htl0 := hFr.base.tl
    simp only [PotPar]
    omega

/-! ### Seeding -/

/-- Putting the source at distance zero, at the front of the queue when
it is alive, and at its own parent. -/
theorem seedSrcPar_run {B : ℕ} (hs : s < n) (hnB : n < B) (hdB : d + 1 < B)
    (hMB : ∀ z < n, M z < B) {g g' g'' : ℕ → ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hsrc : σ.vars "src" = s)
    (hoff : σ.arrs "off" = arrOf (n + 1) O) (htgt : σ.arrs "tgt" = arrOf ns T)
    (halv : σ.arrs "alv" = arrOf n M) (hdist : σ.arrs "dist" = arrOf n g)
    (hgd : ∀ j < n, g j = d + 1) (hq : σ.arrs "q" = arrOf n g')
    (hpar : σ.arrs "par" = arrOf n g'') :
    ∃ σ' K, Run B seedSrcPar σ σ' K ∧ K ≤ 24 ∧ DrainInvPar G M ns d s O T σ' ∧
      σ'.vars "head" = 0 ∧ σ'.vars "sc" = 0 := by
  have hsB : σ.vars "src" < B := by rw [hsrc]; omega
  have hdlen : σ.vars "src" < (σ.arrs "dist").length := by
    rw [hdist, length_arrOf, hsrc]; exact hs
  have hplen : σ.vars "src" < (σ.arrs "par").length := by
    rw [hpar, length_arrOf, hsrc]; exact hs
  have hqlen : (σ.arrs "q").length = n := by rw [hq, length_arrOf]
  have halvlen : (σ.arrs "alv").length = n := by rw [halv, length_arrOf]
  have halvv : (σ.arrs "alv").getD (σ.vars "src") 0 = M s := by
    rw [halv, hsrc, getD_arrOf M hs]
  have halvv' : (σ.arrs "alv")[σ.vars "src"]?.getD 0 = M s := by
    rw [← List.getD_eq_getElem?_getD]; exact halvv
  have hMs : M s < B := hMB s hs
  run_vcg
  · -- an alive source goes on the queue
    refine ⟨⟨upd g s 0, upd g' 0 s, upd g'' s s,
      ⟨⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt], by simp [halv],
          by simp [hdist, hsrc, set_arrOf_eq_upd],
          by simp [hq, hsrc, set_arrOf_eq_upd]⟩,
        by simp [hpar, hsrc, set_arrOf_eq_upd]⟩, ?_, by simp⟩, by simp, by simp⟩
    have h := parFrontier_seed_alive G M d hs (p := g'') (by omega) hgd (upd_self g' 0 s)
    simpa using h
  · -- a dead source does not
    refine ⟨⟨upd g s 0, upd g' 0 s, upd g'' s s,
      ⟨⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt], by simp [halv],
          by simp [hdist, hsrc, set_arrOf_eq_upd],
          by simp [hq, hsrc, set_arrOf_eq_upd]⟩,
        by simp [hpar, hsrc, set_arrOf_eq_upd]⟩, ?_, by simp⟩, by simp, by simp⟩
    have h := parFrontier_seed_dead G M d hs (g := g) (Q := upd g' 0 s) (p := g'')
      (by omega) hgd
    simpa using h

/-! ### The primitive -/

/-- **Depth-capped breadth-first search with parents.** Everything
`RamBfs.bfs_spec` leaves in `dist`, and in `par` a shortest-path tree
towards the source. -/
theorem bfsPar_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hs : s < n) (hnB : n < B)
    (hnsB : ns < B) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
        σ.arrs "alv" = arrOf n M ∧ (∃ g, σ.arrs "dist" = arrOf n g) ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "par" = arrOf n g))
      (bfsParCom d)
      (fun _ σ' => ∃ D P, σ'.arrs "dist" = arrOf n D ∧ σ'.arrs "par" = arrOf n P ∧
        (∀ (v : Fin n) (k : ℕ), k ≤ d →
          (D (v : ℕ) ≤ k ↔ WithinDist (masked G M) k ⟨s, hs⟩ v)) ∧
        ParTree G M d s D P)
      (55 * n + 48 * ns + 34) := by
  have hwv : "n" ∉ (initDist d).wvars := by simp [initDist, Fill.put, Com.wvars]
  have hwv' : "src" ∉ (initDist d).wvars := by simp [initDist, Fill.put, Com.wvars]
  have hwa₁ : "off" ∉ (initDist d).warrs := by simp [initDist, Fill.put, Com.warrs]
  have hwa₂ : "tgt" ∉ (initDist d).warrs := by simp [initDist, Fill.put, Com.warrs]
  have hwa : "alv" ∉ (initDist d).warrs := by simp [initDist, Fill.put, Com.warrs]
  have hwa' : "q" ∉ (initDist d).warrs := by simp [initDist, Fill.put, Com.warrs]
  have hwa'' : "par" ∉ (initDist d).warrs := by simp [initDist, Fill.put, Com.warrs]
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hsrc, hoff, htgt, halv, ⟨g₀, hdist⟩, ⟨g₁, hq⟩, ⟨g₂, hpar⟩⟩ := hσ
  obtain ⟨σ₁, hrun₁, ⟨⟨g, hdist₁, hgd⟩, -⟩, hfv, hfa, -, -⟩ :=
    ((Fill.loop_spec B n "dist" "i" "n" (.lit (d + 1)) (fun _ => d + 1) (by decide) hnB
      (fun _ _ _ _ => evalB_lit hdB)).frame).run (σ := σ) ⟨⟨g₀, hdist⟩, hn⟩
  obtain ⟨σ₂, K₂, hrun₂, hK₂, hI₂, hhead₂, hsc₂⟩ :=
    seedSrcPar_run (G := G) (O := O) (T := T) (ns := ns) hs hnB hdB hMB
      (by rw [hfv "n" hwv]; exact hn) (by rw [hfv "src" hwv']; exact hsrc)
      (by rw [hfa "off" hwa₁]; exact hoff) (by rw [hfa "tgt" hwa₂]; exact htgt)
      (by rw [hfa "alv" hwa]; exact halv) hdist₁ hgd (by rw [hfa "q" hwa']; exact hq)
      (by rw [hfa "par" hwa'']; exact hpar)
  obtain ⟨σ₃, K₃, hrun₃, hI₃, hhead₃, hpay⟩ := drainPar_run hcsr hnB hnsB hdB hMB hI₂
  obtain ⟨D₂, Q₂, P₂, -, hFr₂, -⟩ := hI₂
  obtain ⟨D, Q, P, ⟨⟨-, -, -, -, -, hdist₃, -⟩, hpar₃⟩, hFr, -⟩ := hI₃
  have htl₂ : σ₂.vars "tail" ≤ n := hFr₂.base.tl
  have hpot₂ : PotPar n ns σ₂ = 48 * ns + 44 * n := by
    simp only [PotPar, hhead₂, hsc₂]; omega
  rw [hhead₃] at hFr
  have hT : ParTree G M d s D P := hFr.tree
  refine ⟨σ₃, _, (hrun₁.seq (hrun₂.seq hrun₃)).mono ?_, le_rfl, D, P, hdist₃, hpar₃,
    fun v k hk => (hT.dist_le_iff v.isLt hk).trans (wd_iff_withinDist hs v.isLt), hT⟩
  rw [hpot₂] at hpay
  simp only [size_lit]
  omega

/-! ### Reading the path back

The parent array is walked from the target towards the source, one cell
of the output buffer per turn. The loop is *counted* — `dist[t] + 1`
turns, held in `plen` — so termination on the machine is the counter
and nothing else; what the invariant is for is that the cell the turn
writes is the right one. And it is the right one for a reason the
arithmetic already carries: the distance drops by one at every parent
step, so the vertex reached after `i` steps is at distance
`dist[t] - i`, and it is still a vertex — which is what makes the read
`par[cur]` in range. -/

/-- One step back along the parents. -/
def extractStep : Com :=
  .seq (.store "path" (.var "i") (.var "cur"))
    (.seq (.assign "cur" (.get "par" (.var "cur")))
      (.assign "i" (.add (.var "i") (.lit 1))))

/-- **The extraction pass.** Take the target out of `tv`, read off its
distance, and walk the parents into `path` for one turn more than that
distance — so the buffer's cells `0 … dist[t]` hold the target, its
parent, and so on down to the source. -/
def extractPathCom : Com :=
  .seq (.assign "cur" (.var "tv"))
    (.seq (.assign "pl" (.get "dist" (.var "cur")))
      (.seq (.assign "plen" (.add (.var "pl") (.lit 1)))
        (.seq (.assign "i" (.lit 0))
          (.while (.lt (.var "i") (.var "plen")) extractStep))))

/-- The invariant of the walk back: the buffer holds the ancestors
already passed, and the pointer stands at the next one. -/
def ExtractInv (n d t L : ℕ) (P : ℕ → ℕ) (σ : Env) : Prop :=
  ∃ Buf, σ.arrs "path" = arrOf (d + 1) Buf ∧ σ.arrs "par" = arrOf n P ∧
    σ.vars "pl" = L ∧ σ.vars "plen" = L + 1 ∧ σ.vars "i" ≤ L + 1 ∧
    σ.vars "cur" = parIter P t (σ.vars "i") ∧ (∀ j < σ.vars "i", Buf j = parIter P t j)

/-- **The ancestors the pass visits are all vertices**, the source's own
parent included: it is the source again, so the turn after the last one
reads a cell that is there. -/
theorem ParTree.chain_lt {D P : ℕ → ℕ} (hT : ParTree G M d s D P) {t : ℕ} (ht : t < n)
    (hdt : D t ≤ d) : ∀ i ≤ D t + 1, parIter P t i < n := by
  intro i hi
  have hlast : parIter P t (D t) = s := hT.chain_last ht hdt
  have hsn : s < n := hlast ▸ (hT.chain ht hdt (D t) le_rfl).1
  rcases Nat.lt_or_ge i (D t + 1) with hlt | hge
  · exact (hT.chain ht hdt i (by omega)).1
  · have hie : i = D t + 1 := by omega
    subst hie
    rw [parIter_succ, hlast, hT.self]
    exact hsn

/-- One turn of the walk back. -/
theorem extractStep_spec {B : ℕ} {D P : ℕ → ℕ} (hT : ParTree G M d s D P) (hnB : n < B)
    (hdB : d + 1 < B) {t : ℕ} (ht : t < n) (hdt : D t ≤ d) :
    Spec B (fun σ => ExtractInv n d t (D t) P σ ∧ σ.vars "i" < D t + 1) extractStep
      (fun σ σ' => ExtractInv n d t (D t) P σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 12 := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨⟨Buf, hpath, hpar, hpl, hplen, hile, hcur, hbuf⟩, hilt⟩ := hσ
  have hcn : σ.vars "cur" < n := by rw [hcur]; exact hT.chain_lt ht hdt _ hile
  have hstep : P (σ.vars "cur") = parIter P t (σ.vars "i" + 1) := by rw [parIter_succ, hcur]
  have hpn : P (σ.vars "cur") < n := by
    rw [hstep]; exact hT.chain_lt ht hdt _ (by omega)
  have hpathlen : σ.vars "i" < (σ.arrs "path").length := by rw [hpath, length_arrOf]; omega
  have hparlen : σ.vars "cur" < (σ.arrs "par").length := by rw [hpar, length_arrOf]; exact hcn
  have hparv : (σ.arrs "par").getD (σ.vars "cur") 0 = P (σ.vars "cur") := by
    rw [hpar, getD_arrOf P hcn]
  have hparv' : (σ.arrs "par")[σ.vars "cur"]?.getD 0 = P (σ.vars "cur") := by
    rw [← List.getD_eq_getElem?_getD]; exact hparv
  have hparB : (σ.arrs "par").getD (σ.vars "cur") 0 < B := by rw [hparv]; omega
  have hparB' : (σ.arrs "par")[σ.vars "cur"]?.getD 0 < B := by rw [hparv']; omega
  have hiB : σ.vars "i" + 1 < B := by omega
  have hcB : σ.vars "cur" < B := by omega
  run_vcg
  refine ⟨⟨upd Buf (σ.vars "i") (σ.vars "cur"), by simp [hpath, set_arrOf_eq_upd],
    by simp [hpar], by simp [hpl], by simp [hplen], by simp; omega,
    by simp [hparv', hstep], ?_⟩, by simp⟩
  intro j hj
  have hj' : j < σ.vars "i" + 1 := by simpa using hj
  by_cases hje : j = σ.vars "i"
  · subst hje; rw [upd_self, hcur]
  · rw [upd_of_ne _ hje]; exact hbuf j (by omega)

/-- **The pass.** The buffer's first `dist[t] + 1` cells hold the
iterated parent of the target, and `pl` holds the distance itself. -/
theorem extractPath_spec {B : ℕ} {D P : ℕ → ℕ} (hT : ParTree G M d s D P) (hnB : n < B)
    (hdB : d + 1 < B) {t : ℕ} (ht : t < n) (hdt : D t ≤ d) :
    Spec B
      (fun σ => σ.vars "tv" = t ∧ σ.arrs "dist" = arrOf n D ∧ σ.arrs "par" = arrOf n P ∧
        (∃ g, σ.arrs "path" = arrOf (d + 1) g))
      extractPathCom
      (fun _ σ' => σ'.vars "pl" = D t ∧ ∃ Buf, σ'.arrs "path" = arrOf (d + 1) Buf ∧
        ∀ j ≤ D t, Buf j = parIter P t j)
      (16 * d + 32) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨htv, hdist, hpar, ⟨g, hpath⟩⟩ := hσ
  have hloop := Spec.forRangeZero (B := B) "i" "plen" (ExtractInv n d t (D t) P) (D t + 1) 12
    (by omega) (fun σ' h => h.choose_spec.2.2.2.2.1) (fun σ' h => h.choose_spec.2.2.2.1)
    (extractStep_spec hT hnB hdB ht hdt)
  have htvB : σ.vars "tv" < B := by omega
  have hdlen : σ.vars "tv" < (σ.arrs "dist").length := by
    rw [hdist, length_arrOf, htv]; exact ht
  have hdv : (σ.arrs "dist").getD (σ.vars "tv") 0 = D t := by
    rw [hdist, htv, getD_arrOf D ht]
  have hdv' : (σ.arrs "dist")[σ.vars "tv"]?.getD 0 = D t := by
    rw [← List.getD_eq_getElem?_getD]; exact hdv
  have hdvB : (σ.arrs "dist").getD (σ.vars "tv") 0 < B := by rw [hdv]; omega
  have hdvB' : (σ.arrs "dist")[σ.vars "tv"]?.getD 0 < B := by rw [hdv']; omega
  have hdvB1 : (σ.arrs "dist").getD (σ.vars "tv") 0 + 1 < B := by rw [hdv]; omega
  have hdvB1' : (σ.arrs "dist")[σ.vars "tv"]?.getD 0 + 1 < B := by rw [hdv']; omega
  run_vcg [hloop]
  · -- what the loop left is what the pass owes
    obtain ⟨⟨Buf, hpath', hpar', hpl', hplen', hile', hcur', hbuf'⟩, hiN⟩ :=
      ‹ExtractInv n d t (D t) P _ ∧ _›
    exact ⟨hpl', Buf, hpath', fun j hj => hbuf' j (by omega)⟩
  · -- the loop starts with the target in hand and nothing written
    refine ⟨g, by simp [hpath], by simp [hpar], by simp [hdv'], by simp [hdv'],
      by simp, by simp [htv], fun j hj => absurd hj (by simp)⟩

/-! ### The two passes together

`bfsPathCom d` is the search and the walk back, and its specification is
the one shaped like `Lax3Proofs.SplitterWinOracle.PathOracle`'s two
fields: from a machine state the program reaches, a walk of the arena of
length at most the cap whose support is exactly the set the buffer
names, and a bound of `cap + 1` on the size of that set. -/

/-- **The path the search found.** -/
def bfsPathCom (d : ℕ) : Com := .seq (bfsParCom d) extractPathCom

/-- **What the driver consumes.** Run from a source `s` and asked for a
target `t` the arena puts within the cap, the program leaves in `path`
a buffer whose first `pl + 1` cells name exactly the vertices of a walk
from `s` to `t` of length at most the cap — which is
`PathOracle.spec`'s conclusion — and that set has at most `cap + 1`
vertices, which is `PathOracle.card`. -/
theorem bfsPath_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hs : s < n) {t : ℕ} (ht : t < n)
    (hnB : n < B) (hnsB : ns < B) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    (hwd : WithinDist (masked G M) d ⟨s, hs⟩ ⟨t, ht⟩) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧ σ.vars "tv" = t ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
        σ.arrs "alv" = arrOf n M ∧ (∃ g, σ.arrs "dist" = arrOf n g) ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "par" = arrOf n g) ∧
        (∃ g, σ.arrs "path" = arrOf (d + 1) g))
      (bfsPathCom d)
      (fun _ σ' => ∃ (L : ℕ) (Buf : ℕ → ℕ), σ'.vars "pl" = L ∧
        σ'.arrs "path" = arrOf (d + 1) Buf ∧ L ≤ d ∧
        ∃ p : (masked G M).Walk ⟨s, hs⟩ ⟨t, ht⟩, p.length ≤ d ∧
          bufSet n L Buf = {z : Fin n | z ∈ p.support} ∧
          (bufSet n L Buf).ncard ≤ d + 1)
      (55 * n + 48 * ns + 16 * d + 66) := by
  have hwtv : "tv" ∉ (bfsParCom d).wvars := by
    simp [bfsParCom, initDist, seedSrcPar, bfsParDrain, expandRowPar, scanSlotPar, Fill.put,
      Csr.loadRow, Csr.scan, Queue.drain, Com.wvars]
  have hwpath : "path" ∉ (bfsParCom d).warrs := by
    simp [bfsParCom, initDist, seedSrcPar, bfsParDrain, expandRowPar, scanSlotPar, Fill.put,
      Csr.loadRow, Csr.scan, Queue.drain, Com.warrs]
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hsrc, htv, hoff, htgt, halv, hdi, hqq, hpp, ⟨g, hpath⟩⟩ := hσ
  obtain ⟨σ₁, hrun₁, ⟨D, P, hdist₁, hpar₁, -, hT⟩, hfv, hfa, -, -⟩ :=
    ((bfsPar_spec hcsr hs hnB hnsB hdB hMB).frame).run (σ := σ)
      ⟨hn, hsrc, hoff, htgt, halv, hdi, hqq, hpp⟩
  have hdt : D t ≤ d := hT.reach d le_rfl t ⟨hs, ht, hwd⟩
  obtain ⟨σ₂, hrun₂, hpl₂, Buf, hpath₂, hbuf₂⟩ :=
    (extractPath_spec hT hnB hdB ht hdt).run (σ := σ₁)
      ⟨by rw [hfv "tv" hwtv]; exact htv, hdist₁, hpar₁, ⟨g, by rw [hfa "path" hwpath]; exact hpath⟩⟩
  obtain ⟨p, hplen, hpsup⟩ := hT.walk hs (D t) hdt ⟨t, ht⟩ rfl
  refine ⟨σ₂, _, (hrun₁.seq hrun₂).mono (by omega), le_rfl, D t, Buf, hpl₂, hpath₂, hdt,
    p, by omega, ?_, ?_⟩
  · rw [bufSet_congr hbuf₂, ← hpsup]
  · rw [bufSet_congr hbuf₂, ← hpsup]
    exact ncard_support_le p (by omega)

/-! ### The oracle, instantiated

Nothing here is computable and nothing here needs to be: the oracle's
`path` field is a *set* per pair of vertices, and the driver defines it
by choice over the machine run. `PathOracle`'s radius `r` is this file's
cap `d` — a walk of length at most `d` is what both sides mean — and the
`WithinDist` the oracle's `spec` is given is `bfsPath_spec`'s `hwd`, so
the two hypotheses are the same statement.

Fix the block structure `O`, `T`, the mask `M` and the source `s`, and
let `hσ` be a state satisfying `bfsPath_spec`'s precondition. Then, for
a target `t` the arena puts within `d`:

* `(bfsPath_spec … hwd).run hσ` hands back the final state together with
  the length `L`, the buffer `Buf`, and the four facts below;
* `bufSet n L Buf` is the set to offer — a `Classical.choice` over the
  outcomes, which the same lemma shows nonempty, turns it into a
  function of the pair alone, and that function is `path`;
* `spec` is the last conjunct: `∃ p, p.length ≤ d ∧ bufSet n L Buf =
  {z | z ∈ p.support}`, which is `PathOracle.spec`'s conclusion with
  `path A u v` already rewritten to `bufSet n L Buf`;
* `card` is the conjunct beside it, `(bufSet n L Buf).ncard ≤ d + 1`.

A driver that wants the oracle at pairs the arena does *not* connect
offers `∅` there and reads `card` off `Set.ncard_empty`; `spec` asks
nothing of those pairs, which is the whole point of
`SplitterWinOracle`'s interface. -/

/-! ### The worked example

The graph is `RamBfs.Demo`'s: the path `0—1—2—3` with an isolated
vertex `4`, built by the program's own stores. The search runs from `0`
and the walk back from the vertex in `tv`, and what is written out is
the length and the first four cells of the buffer — the path itself,
from the target backwards. -/

namespace Demo

open Lax3Proofs.RamBfs.Demo (demoOff demoTgt demoAlv)

/-- Five vertices, six slots, the search from `0`, the path to `tv`. -/
def demoSetup (a2 tv : ℕ) : Com :=
  .seq (.assign "n" (.lit 5))
    (.seq (.assign "src" (.lit 0))
      (.seq (.assign "tv" (.lit tv))
        (.seq demoOff (.seq demoTgt (demoAlv a2)))))

/-- The length of the path, then its first four vertices. -/
def demoReport : Com :=
  .seq (.write (.var "pl"))
    (.seq (.write (.get "path" (.lit 0)))
      (.seq (.write (.get "path" (.lit 1)))
        (.seq (.write (.get "path" (.lit 2)))
          (.write (.get "path" (.lit 3))))))

/-- Build the structure, search, walk back, report. -/
def demoWatched (a2 tv d : ℕ) : Com :=
  .seq (demoSetup a2 tv) (.seq (bfsPathCom d) demoReport)

/-- Sixteen scalars, seven arrays, four temporaries. -/
def demoLayout : Lax13Proofs.Compile.Layout :=
  ⟨["n", "src", "tv", "i", "head", "tail", "sc", "v", "w", "dv", "dn", "j", "jend",
    "cur", "pl", "plen"],
   ["off", "tgt", "alv", "dist", "q", "par", "path"], 4⟩

/-- The machine program. -/
def demoProg (a2 tv d : ℕ) : Lax13.Ram.Program :=
  Lax13Proofs.Compile.compileProgram demoLayout (demoWatched a2 tv d)

/-- The layout covers the block, so the compilation is the one the
simulation theorem is about. -/
theorem demoWatched_ok (a2 tv d : ℕ) :
    Lax13Proofs.Compile.Com.Ok demoLayout (demoWatched a2 tv d) := by
  simp [demoWatched, demoSetup, Lax3Proofs.RamBfs.Demo.demoOff,
    Lax3Proofs.RamBfs.Demo.demoTgt, Lax3Proofs.RamBfs.Demo.demoAlv, demoReport, bfsPathCom,
    bfsParCom, initDist, seedSrcPar, bfsParDrain, expandRowPar, scanSlotPar, extractPathCom,
    extractStep, Fill.put, Csr.loadRow, Csr.scan, Queue.drain, demoLayout,
    Lax13Proofs.Compile.Com.Ok, Lax13Proofs.Compile.Cond.Ok, Lax13Proofs.Compile.condExpr,
    Lax13Proofs.Compile.Expr.Ok]

/-- Run it at a word length that holds every number this graph
produces. -/
def demoRun (a2 tv d : ℕ) : Option (List ℕ × ℕ) :=
  runOut 16 400000 (demoProg a2 tv d) (Lax13.Ram.initState []) 0

-- the path to the far end of the path graph: length three, and the
-- buffer is `3 2 1 0` — the walk read off backwards, from the target
#guard demoRun 1 3 3 = some ([3, 3, 2, 1, 0], 1501)
-- a neighbour of the source: length one, buffer `1 0`, the two cells
-- beyond it never written and so still zero
#guard demoRun 1 1 3 = some ([1, 1, 0, 0, 0], 1425)
-- killing vertex `2` does not separate `0` from `1`, so the same answer
-- comes back out of a smaller search
#guard demoRun 0 1 3 = some ([1, 1, 0, 0, 0], 965)
-- the source itself: length zero, and the buffer holds it alone
#guard demoRun 1 0 3 = some ([0, 0, 0, 0, 0], 1387)
-- and the vertex the arena does not reach, which `bfsPath_spec` says
-- nothing about — its distance is the sentinel and the cells beyond the
-- first are the memory's own zeros. The machine still halts, because
-- the walk back is counted and not tested
#guard demoRun 1 4 3 = some ([4, 4, 0, 0, 0], 1539)

end Demo

end Lax3Proofs.RamBfsPaths
