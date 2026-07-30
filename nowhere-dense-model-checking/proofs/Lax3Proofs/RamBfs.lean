import Lax3Proofs.WalkDistance
import Lax3Proofs.SplitterBasics
import Lax3Proofs.CsrWide
import Lax11.GraphEncoding
import Lax13Proofs.Lib.Csr
import Lax13Proofs.Lib.Queue
import Lax13Proofs.Lib.Fill

/-!
Depth-capped breadth-first search over a masked block structure, as a
word-RAM program with its correctness and its running time.

This is the one search the evaluator of this submission ever performs.
Every arena it works in is a subgraph of the input obtained by *killing*
vertices — the splitter's moves, the vertices already fixed by an outer
quantifier, the centres a cover has already claimed — and killing is not
deletion: the carrier stays and the edges incident to the killed set go
away, which is exactly Lax12's `deleteVerts`. So an arena is materialized
as one bit per vertex, an **alive mask**, laid over a block structure that
is never rebuilt, and the search reads the mask instead of a fresh graph.
The vocabulary the specification speaks is therefore the campaign's own:
the graph is `Lax12.UniformQuasiWideness.deleteVerts G S` with `S` the
dead vertices, and a distance bound is
`Lax3.ColoredGraphs.WithinDist` — the predicate `∃ walk, length ≤ k` that
`Lax3Proofs.WalkDistance` develops and that the cover, scatter and
distance-profile arguments are all stated in.

### What it computes

Given a block structure for `G` on `n` vertices, a mask `M`, a source `s`
and a cap `d`, the program leaves in the array `dist` the function

* `dist v = ` the least length of a walk from `s` to `v` in the masked
  graph, when that is at most `d`;
* `dist v = d + 1` otherwise.

The sentinel is `d + 1` and not a separate marker, and that is the one
design decision the rest of the program follows from: the relaxation test
is then plain `dn < dist[w]`, and it does the work of *three* tests at
once — it rejects a vertex already discovered, it rejects a vertex
discovered at this very level, and, because a vertex at level `d` has
`dn = d + 1 = dist[w]` for every undiscovered `w`, it caps the search
without the program ever mentioning `d` again. Only the initial fill
names the cap.

The specification is stated one threshold at a time,

    ∀ v < n, ∀ k ≤ d, dist v ≤ k ↔ WithinDist (deleteVerts G S) k s v,

rather than as an equation between `dist v` and a distance function.
That is the form the consumers want: a distance-profile colour is
`{v | WithinDist A a v w}`, a cover's ball is `{v | WithinDist A r c v}`,
and each of those is one instance of the `↔` at its own radius, with no
minimality argument in between.

### The mask, the source, and the one asymmetry

`deleteVerts` isolates: an edge survives only if *both* of its endpoints
are alive. A dead source therefore has no edges at all, and its balls
degenerate to `{s}`. The program handles that without a side condition
and without a second code path: the source is given distance zero
unconditionally — `WithinDist A 0 s s` holds in every graph — and is put
on the queue only if it is alive. So `qall`, the clause that says every
discovered vertex is on the queue, is stated for *alive* vertices only,
and that single weakening is the whole cost of admitting a dead source.
Nothing else in the proof knows about the case.

### The invariant

Stated once, in `Frontier`, and it is the classical breadth-first
frontier invariant with the mask folded in: a written distance is
achieved by a walk (`sound`); the queue holds exactly the discovered
alive vertices, without repetition (`qmem`, `qall`, `qinj`); the queue is
sorted by distance (`qmono`) and spans at most one level more than
whatever is still pending (`qcap`); and everything before `head` has had
its whole row looked at, its masked neighbours ending up at distance at
most one more than its own (`exp`).

`qcap` is what makes the sentinel trick honest: it is the clause that
rules out the branch in which `dn < dist[w]` fires at an *already*
discovered `w`, which would enqueue `w` twice. And `exp` needs no side
condition on the cap, because a vertex at level `d` scans its row and
relaxes nothing, while `cap` already puts every distance at `d + 1` or
below.

Completeness — that a vertex the masked graph puts within `k` really gets
a distance at most `k` — is not an invariant of the loop at all. It is
proved once at the exit, by induction on `k`, from `exp` and the fact
that at the exit `head = tail`: the last edge of a walk of length `k + 1`
runs from a vertex the induction hypothesis has placed at distance at
most `k`, that vertex is alive because masked adjacency says so, hence it
is on the queue, hence it is expanded. That is `Lax11Proofs.CC`'s exit
argument for reachability, one level up.

### What the campaign reuses

The distance-profile pass runs this once per centre and reads off the
colours `{v | WithinDist A a v w}` as the threshold instances of the
specification; the cover pass runs it to radius `r` from each centre it
claims; the scatter pass runs it from a candidate with the already-chosen
vertices killed, which is a mask change and not a graph change; and the
strategy-path pass runs it in the arena the splitter has already cut
down. All four hand back the same `dist` array and none of them needs to
re-establish anything about the block structure, which no run of this
program ever writes to.
-/

namespace Lax3Proofs.RamBfs

open Lax3.ColoredGraphs Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance

variable {n ns nt d s : ℕ} {G : SimpleGraph (Fin n)} {M O T : ℕ → ℕ}

/-! ### The masked graph, and distances in it

The mask is one cell per vertex and a vertex is dead when its cell is
zero; the arena is `G` with the dead vertices isolated. Two lemmas name
the adjacency and nothing else is unfolded: `deleteVerts` is a concept
definition and `SplitterBasics.deleteVerts_adj` is its clause lemma. -/

/-- The vertices the mask kills. -/
def deadSet (n : ℕ) (M : ℕ → ℕ) : Set (Fin n) := {v | M (v : ℕ) = 0}

/-- The arena: `G` with the dead vertices isolated. -/
def masked {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) : SimpleGraph (Fin n) :=
  Lax12.UniformQuasiWideness.deleteVerts G (deadSet n M)

/-- The adjacency of the arena: an edge survives iff both of its
endpoints are alive. -/
theorem masked_adj {u v : Fin n} :
    (masked G M).Adj u v ↔ G.Adj u v ∧ M (u : ℕ) ≠ 0 ∧ M (v : ℕ) ≠ 0 :=
  Lax3Proofs.SplitterBasics.deleteVerts_adj

/-! Everything the program does is indexed by vertex *numbers*, so
adjacency and the distance bound are restated on `ℕ`, carrying their own
range conditions — `Lax11Proofs.CC`'s `Adjn`/`Rch` for this submission's
metric notions. -/

/-- The vertices numbered `a` and `b` are adjacent in the arena. -/
def MAdj {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (a b : ℕ) : Prop :=
  ∃ (ha : a < n) (hb : b < n), (masked G M).Adj ⟨a, ha⟩ ⟨b, hb⟩

/-- The vertex numbered `b` is within distance `k` of the one numbered
`a` in the arena. -/
def WD {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (k a b : ℕ) : Prop :=
  ∃ (ha : a < n) (hb : b < n), WithinDist (masked G M) k ⟨a, ha⟩ ⟨b, hb⟩

theorem MAdj.lt_left {a b : ℕ} (h : MAdj G M a b) : a < n := h.1

theorem MAdj.lt_right {a b : ℕ} (h : MAdj G M a b) : b < n := h.2.1

theorem MAdj.alive_left {a b : ℕ} (h : MAdj G M a b) : M a ≠ 0 :=
  (masked_adj.1 h.2.2).2.1

theorem MAdj.alive_right {a b : ℕ} (h : MAdj G M a b) : M b ≠ 0 :=
  (masked_adj.1 h.2.2).2.2

theorem MAdj.adj {a b : ℕ} (h : MAdj G M a b) : G.Adj ⟨a, h.lt_left⟩ ⟨b, h.lt_right⟩ :=
  (masked_adj.1 h.2.2).1

theorem MAdj.symm {a b : ℕ} (h : MAdj G M a b) : MAdj G M b a :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

/-- A slot of the block of an alive vertex, whose target is alive, names
a neighbour in the arena. -/
theorem madj_of_adj {a b : ℕ} (ha : a < n) (hb : b < n) (hab : G.Adj ⟨a, ha⟩ ⟨b, hb⟩)
    (hma : M a ≠ 0) (hmb : M b ≠ 0) : MAdj G M a b :=
  ⟨ha, hb, masked_adj.2 ⟨hab, hma, hmb⟩⟩

theorem WD.lt_left {k a b : ℕ} (h : WD G M k a b) : a < n := h.1

theorem WD.lt_right {k a b : ℕ} (h : WD G M k a b) : b < n := h.2.1

/-- Every vertex is within any distance of itself. -/
theorem WD.refl (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (k : ℕ) {a : ℕ} (ha : a < n) :
    WD G M k a a :=
  ⟨ha, ha, withinDist_refl _ _ _⟩

/-- The bound may be loosened. -/
theorem WD.mono {k k' a b : ℕ} (hk : k ≤ k') (h : WD G M k a b) : WD G M k' a b :=
  ⟨h.1, h.2.1, withinDist_mono_radius hk h.2.2⟩

/-- One more edge, one more unit of distance. -/
theorem WD.step {k a b c : ℕ} (h : WD G M k a b) (hbc : MAdj G M b c) : WD G M (k + 1) a c :=
  ⟨h.1, hbc.2.1, withinDist_trans h.2.2 (withinDist_of_adj hbc.2.2)⟩

/-- Distance zero is equality. -/
theorem WD.eq_of_zero {a b : ℕ} (h : WD G M 0 a b) : a = b := by
  obtain ⟨ha, hb, p, hp⟩ := h
  cases p with
  | nil => rfl
  | cons _ q => simp at hp

/-! The one walk lemma the exit argument needs: a walk of length at most
`k + 1` either is short enough already, or has a last edge, whose far end
is within `k`. It is proved at the head of the walk — where `cases` on a
walk is not dependent — and reflected to the tail by
`WalkDistance.withinDist_symm`. -/

/-- A walk of length at most `k + 1` either has length at most `k` or
starts with an edge. -/
theorem withinDist_head {V : Type*} {A : SimpleGraph V} {u v : V} {k : ℕ}
    (h : WithinDist A (k + 1) u v) : u = v ∨ ∃ c, A.Adj u c ∧ WithinDist A k c v := by
  obtain ⟨p, hp⟩ := h
  cases p with
  | nil => exact Or.inl rfl
  | cons hadj q => exact Or.inr ⟨_, hadj, q, by simpa using hp⟩

/-- **The last edge.** A vertex within `k + 1` of the source is either
within `k` of it, or a neighbour of a vertex that is. -/
theorem WD.tail {k a b : ℕ} (h : WD G M (k + 1) a b) :
    WD G M k a b ∨ ∃ c, WD G M k a c ∧ MAdj G M c b := by
  obtain ⟨ha, hb, hw⟩ := h
  rcases withinDist_head (withinDist_symm hw) with hbe | ⟨c, hadj, hc⟩
  · exact Or.inl ⟨ha, hb, withinDist_of_eq _ _ hbe.symm⟩
  · exact Or.inr ⟨(c : ℕ), ⟨ha, c.2, withinDist_symm hc⟩, ⟨c.2, hb, hadj.symm⟩⟩

/-! ### The block structure as a view of the graph

The kit's `Lib.Csr` relation is about two arrays of numbers and says
nothing about a graph; `Lax11.GraphEncoding.EncodesGraph` is about a
*tape word*, which an arena materialized in memory is not. What the
search needs is the middle term: two cell functions that list, block by
block, the neighbours of `G`. -/

/-- `CsrGraph G ns O T`: the offsets `O` and the targets `T` are a block
structure for `G`, with `ns` slots in all. This is `EncodesGraph` with
the tape bookkeeping taken out — an arena is built in memory, not
read. -/
structure CsrGraph {n : ℕ} (G : SimpleGraph (Fin n)) (ns : ℕ) (O T : ℕ → ℕ) : Prop where
  /-- The first block starts at the start of the target array. -/
  zero : O 0 = 0
  /-- The last block ends at its end. -/
  last : O n = ns
  /-- The offsets do not decrease, so they cut the array into blocks. -/
  mono : ∀ i < n, O i ≤ O (i + 1)
  /-- Every target is a vertex. -/
  target_lt : ∀ j < ns, T j < n
  /-- The block of a vertex lists exactly its neighbours. -/
  adj_iff : ∀ u v : Fin n, G.Adj u v ↔ ∃ j, O (u : ℕ) ≤ j ∧ j < O ((u : ℕ) + 1) ∧ T j = (v : ℕ)

namespace CsrGraph

variable {i k : ℕ}

/-- The offsets do not decrease, all the way up. -/
theorem mono' (h : CsrGraph G ns O T) (hik : i ≤ k) (hk : k ≤ n) : O i ≤ O k := by
  induction k with
  | zero => have : i = 0 := by omega
            subst this; exact le_rfl
  | succ k ih =>
      rcases Nat.lt_or_ge i (k + 1) with hlt | hge
      · exact le_trans (ih (by omega) (by omega)) (h.mono k (by omega))
      · have : i = k + 1 := by omega
        subst this; exact le_rfl

/-- Every offset is inside the target array. -/
theorem le_ns (h : CsrGraph G ns O T) (hi : i ≤ n) : O i ≤ ns :=
  h.last ▸ h.mono' hi le_rfl

/-- Everything a block names is a vertex. -/
theorem target_lt' (h : CsrGraph G ns O T) (ha : i < n) (hj : k < O (i + 1)) : T k < n :=
  h.target_lt k (lt_of_lt_of_le hj (h.le_ns (by omega)))

/-- **A slot names a neighbour in the arena**, as soon as both ends are
alive. -/
theorem madj_of_slot (h : CsrGraph G ns O T) (ha : i < n) (h₁ : O i ≤ k) (h₂ : k < O (i + 1))
    (hma : M i ≠ 0) (hmb : M (T k) ≠ 0) : MAdj G M i (T k) :=
  madj_of_adj ha (h.target_lt' ha h₂)
    ((h.adj_iff ⟨i, ha⟩ ⟨T k, h.target_lt' ha h₂⟩).2 ⟨k, h₁, h₂, rfl⟩) hma hmb

/-- **And conversely**: a neighbour in the arena is named by a slot of
the block. -/
theorem slot_of_madj (h : CsrGraph G ns O T) {a b : ℕ} (hab : MAdj G M a b) :
    ∃ j, O a ≤ j ∧ j < O (a + 1) ∧ T j = b :=
  (h.adj_iff ⟨a, hab.lt_left⟩ ⟨b, hab.lt_right⟩).1 hab.adj

/-! The blocks tile the target array, which is what the running-time
argument is paid out of. `Csr.rowLen` is the kit's name for the size of a
block. -/

/-- The blocks of the first `k` vertices tile the array up to the `k`-th
offset. -/
theorem sum_rowLen (h : CsrGraph G ns O T) (hk : k ≤ n) :
    ∑ i ∈ Finset.range k, Csr.rowLen O i = O k - O 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h₁ : O 0 ≤ O k := h.mono' (Nat.zero_le _) (by omega)
      have h₂ : O k ≤ O (k + 1) := h.mono k (by omega)
      rw [Finset.sum_range_succ, ih (by omega)]
      simp only [Csr.rowLen]
      omega

/-- The blocks of a set of distinct vertices fit inside the array. -/
theorem sum_rowLen_le (h : CsrGraph G ns O T) {A : Finset ℕ} (hA : ∀ v ∈ A, v < n) :
    ∑ v ∈ A, Csr.rowLen O v ≤ ns := by
  have hsub : A ⊆ Finset.range n := fun v hv => Finset.mem_range.2 (hA v hv)
  calc ∑ v ∈ A, Csr.rowLen O v ≤ ∑ v ∈ Finset.range n, Csr.rowLen O v :=
        Finset.sum_le_sum_of_subset hsub
    _ = O n - O 0 := h.sum_rowLen le_rfl
    _ ≤ ns := by rw [h.last]; omega

/-- The form the search uses it in: the blocks of the vertices the queue
holds fit inside the array, the queue's injectivity standing in for
distinctness. -/
theorem sum_rowLen_queue (h : CsrGraph G ns O T) {Q : ℕ → ℕ} {k : ℕ}
    (hQ : ∀ i < k, Q i < n) (hinj : ∀ i < k, ∀ j < k, Q i = Q j → i = j) :
    ∑ i ∈ Finset.range k, Csr.rowLen O (Q i) ≤ ns := by
  have himg : ∑ v ∈ (Finset.range k).image Q, Csr.rowLen O v
      = ∑ i ∈ Finset.range k, Csr.rowLen O (Q i) :=
    Finset.sum_image
      (fun i hi j hj hq => hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hq)
  rw [← himg]
  refine h.sum_rowLen_le fun v hv => ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
  exact hQ i (Finset.mem_range.1 hi)

end CsrGraph

/-! A caller that does read its graph off a tape gets the view for
nothing: `EncodesGraph` is the same list of conditions with the offsets
and the targets read out of the word. -/

/-- The offsets of an encoding do not decrease, all the way up. -/
theorem offset_mono' {x : List ℕ} (hx : EncodesGraph x n G) {i k : ℕ} (hik : i ≤ k)
    (hk : k ≤ n) : offset x i ≤ offset x k := by
  induction k with
  | zero => have : i = 0 := by omega
            subst this; exact le_rfl
  | succ k ih =>
      rcases Nat.lt_or_ge i (k + 1) with hlt | hge
      · exact le_trans (ih (by omega) (by omega)) (hx.offset_mono k (by omega))
      · have : i = k + 1 := by omega
        subst this; exact le_rfl

/-- **A tape encoding is a block structure.** -/
theorem csrGraph_of_encodesGraph {x : List ℕ} (hx : EncodesGraph x n G)
    (hO : ∀ i ≤ n, O i = offset x i) (hT : ∀ j < 2 * edgeCount x, T j = target x j) :
    CsrGraph G (2 * edgeCount x) O T where
  zero := by rw [hO 0 (by omega), hx.offset_zero]
  last := by rw [hO n le_rfl, hx.offset_last]
  mono i hi := by rw [hO i (by omega), hO (i + 1) (by omega)]; exact hx.offset_mono i hi
  target_lt j hj := by rw [hT j hj]; exact hx.target_lt j hj
  adj_iff u v := by
    rw [hx.adj_iff u v]
    constructor
    · rintro ⟨j, h₁, h₂, h₃⟩
      have hj : j < 2 * edgeCount x :=
        lt_of_lt_of_le h₂ (hx.offset_last ▸ offset_mono' hx (by omega) le_rfl)
      exact ⟨j, by rw [hO _ (by omega)]; exact h₁, by rw [hO _ (by omega)]; exact h₂,
        by rw [hT j hj]; exact h₃⟩
    · rintro ⟨j, h₁, h₂, h₃⟩
      rw [hO _ (by omega)] at h₁
      rw [hO _ (by omega)] at h₂
      have hj : j < 2 * edgeCount x :=
        lt_of_lt_of_le h₂ (hx.offset_last ▸ offset_mono' hx (by omega) le_rfl)
      exact ⟨j, h₁, h₂, by rw [← hT j hj]; exact h₃⟩

/-! ### The program

Five arrays — the two of the block structure, the mask, the distances
and the queue — and the scalars the kit's combinators want: the two queue
pointers, the two block pointers, and `sc`, which counts the slots
already looked at and exists only so that the running-time potential is a
function of the environment.

The cap `d` occurs in the program text exactly once, as the value the
initial fill writes. It is a literal because a radius in this submission
comes from the *formula* and not from the input — the quantifier rank
fixes it — so `bfsCom` is a family of programs, one per cap, and nothing
downstream has to pass a radius at run time. -/

/-- Mark every vertex undiscovered: the whole distance array gets the
sentinel `d + 1`. This is the kit's array fill and nothing else. -/
def initDist (d : ℕ) : Com :=
  .seq (.assign "i" (.lit 0))
    (.while (.lt (.var "i") (.var "n")) (Fill.put "dist" "i" (.lit (d + 1))))

/-- Seed the search: the source is put at distance zero whatever the mask
says — a walk of length zero needs no edges — and on the queue only if it
is alive. -/
def seedSrc : Com :=
  .seq (.ite (.lt (.lit 0) (.get "alv" (.var "src")))
          (.assign "tail" (.lit 1)) (.assign "tail" (.lit 0)))
    (.seq (.store "dist" (.var "src") (.lit 0))
      (.seq (.store "q" (.lit 0) (.var "src"))
        (.seq (.assign "head" (.lit 0)) (.assign "sc" (.lit 0)))))

/-- One slot of the block being scanned: a dead target is passed over,
and a live one is relaxed exactly when the distance on offer beats the
one it carries. That single test rejects an already-discovered vertex,
rejects one discovered at this very level, and caps the search — a vertex
at level `d` offers `d + 1`, which is what an undiscovered vertex already
holds. -/
def scanSlot : Com :=
  .seq (.assign "w" (.get "tgt" (.var "j")))
    (.seq (.ite (.lt (.lit 0) (.get "alv" (.var "w")))
            (.ite (.lt (.var "dn") (.get "dist" (.var "w")))
              (.seq (.store "dist" (.var "w") (.var "dn"))
                (.seq (.store "q" (.var "tail") (.var "w"))
                  (.assign "tail" (.add (.var "tail") (.lit 1)))))
              .skip)
            .skip)
      (.seq (.assign "sc" (.add (.var "sc") (.lit 1)))
        (.assign "j" (.add (.var "j") (.lit 1)))))

/-- Take the next vertex off the queue and scan its whole block. The
queue pointer moves *after* the scan, so that "everything before `head`
has been expanded" is an invariant of the scan as well. -/
def expandRow : Com :=
  .seq (.assign "v" (.get "q" (.var "head")))
    (.seq (.assign "dv" (.get "dist" (.var "v")))
      (.seq (.assign "dn" (.add (.var "dv") (.lit 1)))
        (.seq (Csr.loadRow "off" "v" "j" "jend")
          (.seq (Csr.scan "j" "jend" scanSlot)
            (.assign "head" (.add (.var "head") (.lit 1)))))))

/-- The search itself: empty the queue. -/
def bfsDrain : Com := Queue.drain "head" "tail" expandRow

/-- The whole primitive: clear the distances, seed the source, search. -/
def bfsCom (d : ℕ) : Com := .seq (initDist d) (.seq seedSrc bfsDrain)

/-! ### The invariant

Stated once, and every clause of it is here because some step of the
proof asks for it. `qmono` and `qcap` are the two that a textbook leaves
implicit: `qcap` — the queue never spans more than one level beyond what
is still pending — is what rules out the branch in which the relaxation
test fires at an already discovered vertex, which would put that vertex
on the queue twice, and `qmono` is what keeps `qcap` going. -/

/-- What holds of the distance array and the queue at every point of the
search. -/
structure Frontier {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d s : ℕ)
    (D Q : ℕ → ℕ) (head tail : ℕ) : Prop where
  /-- Nothing ever exceeds the sentinel. -/
  cap : ∀ w < n, D w ≤ d + 1
  /-- The source is at distance zero, alive or not. -/
  src : D s = 0
  /-- A written distance is achieved by a walk of the arena. -/
  sound : ∀ w < n, D w ≤ d → WD G M (D w) s w
  /-- The queue is a segment. -/
  hd : head ≤ tail
  /-- It holds vertices. -/
  tl : tail ≤ n
  /-- Everything on it is a discovered live vertex. -/
  qmem : ∀ i < tail, Q i < n ∧ D (Q i) ≤ d ∧ M (Q i) ≠ 0
  /-- Every discovered live vertex is on it. A dead source is the one
  vertex this clause lets through: it is discovered and never enqueued,
  and nothing else in the proof has to know. -/
  qall : ∀ w < n, M w ≠ 0 → D w ≤ d → ∃ i < tail, Q i = w
  /-- Nothing is on it twice. -/
  qinj : ∀ i < tail, ∀ j < tail, Q i = Q j → i = j
  /-- It is sorted by distance. -/
  qmono : ∀ i j, i ≤ j → j < tail → D (Q i) ≤ D (Q j)
  /-- It spans at most one level beyond whatever is still pending. -/
  qcap : ∀ i < tail, ∀ j, head ≤ j → j < tail → D (Q i) ≤ D (Q j) + 1
  /-- Everything before `head` has had its whole block looked at, its
  neighbours in the arena ending up one level below it at worst. -/
  exp : ∀ i < head, ∀ w, MAdj G M (Q i) w → D w ≤ D (Q i) + 1

namespace Frontier

variable {D Q : ℕ → ℕ} {head tail : ℕ}

/-- **There is room for one more.** A vertex that is not on the queue
witnesses that the queue is shorter than the graph, since the queue holds
distinct vertices. -/
theorem tail_lt (hF : Frontier G M d s D Q head tail) {w : ℕ} (hw : w < n)
    (hnot : ∀ i < tail, Q i ≠ w) : tail < n := by
  have hsub : (Finset.range tail).image Q ⊆ (Finset.range n).erase w := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
    have hi' := Finset.mem_range.1 hi
    exact Finset.mem_erase.2 ⟨hnot i hi', Finset.mem_range.2 (hF.qmem i hi').1⟩
  have hcard : ((Finset.range tail).image Q).card = tail := by
    rw [Finset.card_image_of_injOn (fun i hi j hj hq =>
      hF.qinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hq)]
    exact Finset.card_range tail
  have := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_range.2 hw), Finset.card_range] at this
  omega

/-- **The one change the arrays ever undergo.** The vertex at the head of
the queue offers its neighbour `w` a distance one greater than its own,
and `w` carries more than that; so `w` takes the offer and goes on the
back of the queue. Every clause survives, and two of them for reasons
worth naming: `w` was not on the queue, because `qcap` bounds everything
on it by the head's distance plus one, and `w` is not a neighbour of
anything already expanded, because `exp` would then have bounded it the
same way. -/
theorem relax (hF : Frontier G M d s D Q head tail) (hht : head < tail)
    {w : ℕ} (hadj : MAdj G M (Q head) w) (hlt : D (Q head) + 1 < D w) :
    Frontier G M d s (upd D w (D (Q head) + 1)) (upd Q tail w) head (tail + 1) := by
  obtain ⟨hvn, hdv, hmv⟩ := hF.qmem head hht
  have hw : w < n := hadj.lt_right
  have hmw : M w ≠ 0 := hadj.alive_right
  have hcapw : D w ≤ d + 1 := hF.cap w hw
  have hd1 : D (Q head) + 1 ≤ d := by omega
  -- nothing on the queue can be `w`: `qcap` bounds it by the head's distance plus one
  have hnq : ∀ i < tail, Q i ≠ w := by
    intro i hi hqi
    have := hF.qcap i hi head le_rfl hht
    rw [hqi] at this
    omega
  have htn : tail < n := hF.tail_lt hw hnq
  have hwv : w ≠ Q head := by
    intro hwe; rw [hwe] at hlt; omega
  have hws : s ≠ w := by
    intro hse; rw [← hse, hF.src] at hlt; omega
  have hQhead : upd Q tail w head = Q head := upd_of_ne _ (by omega)
  have hDhead : upd D w (D (Q head) + 1) (Q head) = D (Q head) := upd_of_ne _ (Ne.symm hwv)
  refine ⟨fun z hz => ?_, ?_, fun z hz hzd => ?_, by omega, by omega, fun i hi => ?_,
    fun z hz hmz hzd => ?_, fun i hi j hj hij => ?_, fun i j hij hj => ?_,
    fun i hi j hj₁ hj₂ => ?_, fun i hi z hz => ?_⟩
  · by_cases hzw : z = w
    · rw [hzw, upd_self]; omega
    · rw [upd_of_ne _ hzw]; exact hF.cap z hz
  · rw [upd_of_ne _ hws]; exact hF.src
  · by_cases hzw : z = w
    · subst hzw
      rw [upd_self]
      exact (hF.sound _ hvn hdv).step hadj
    · rw [upd_of_ne _ hzw] at hzd ⊢; exact hF.sound z hz hzd
  · by_cases hit : i = tail
    · rw [hit, upd_self, upd_self]; exact ⟨hw, by omega, hmw⟩
    · have hi' : i < tail := by omega
      rw [upd_of_ne _ hit, upd_of_ne _ (hnq i hi')]
      exact hF.qmem i hi'
  · by_cases hzw : z = w
    · exact ⟨tail, by omega, by rw [upd_self, hzw]⟩
    · rw [upd_of_ne _ hzw] at hzd
      obtain ⟨i, hi, rfl⟩ := hF.qall z hz hmz hzd
      exact ⟨i, by omega, upd_of_ne _ (by omega)⟩
  · by_cases hit : i = tail <;> by_cases hjt : j = tail
    · omega
    · rw [hit, upd_self, upd_of_ne _ hjt] at hij
      exact absurd hij.symm (hnq j (by omega))
    · rw [hjt, upd_self, upd_of_ne _ hit] at hij
      exact absurd hij (hnq i (by omega))
    · rw [upd_of_ne _ hit, upd_of_ne _ hjt] at hij
      exact hF.qinj i (by omega) j (by omega) hij
  · by_cases hjt : j = tail
    · rw [hjt, upd_self, upd_self]
      by_cases hit : i = tail
      · rw [hit, upd_self, upd_self]
      · rw [upd_of_ne _ hit, upd_of_ne _ (hnq i (by omega))]
        have := hF.qcap i (by omega) head le_rfl hht
        omega
    · rw [upd_of_ne _ hjt, upd_of_ne _ (hnq j (by omega))]
      have hit : i ≠ tail := by omega
      rw [upd_of_ne _ hit, upd_of_ne _ (hnq i (by omega))]
      exact hF.qmono i j hij (by omega)
  · by_cases hjt : j = tail
    · rw [hjt, upd_self, upd_self]
      by_cases hit : i = tail
      · rw [hit, upd_self, upd_self]; omega
      · rw [upd_of_ne _ hit, upd_of_ne _ (hnq i (by omega))]
        have := hF.qcap i (by omega) head le_rfl hht
        omega
    · have hj' : j < tail := by omega
      have hdvj : D (Q head) ≤ D (Q j) := hF.qmono head j hj₁ hj'
      rw [upd_of_ne _ hjt, upd_of_ne _ (hnq j hj')]
      by_cases hit : i = tail
      · rw [hit, upd_self, upd_self]; omega
      · rw [upd_of_ne _ hit, upd_of_ne _ (hnq i (by omega))]
        exact hF.qcap i (by omega) j hj₁ hj'
  · have hit : i ≠ tail := by omega
    rw [upd_of_ne _ hit] at hz ⊢
    rw [upd_of_ne _ (hnq i (by omega))]
    by_cases hzw : z = w
    · exfalso
      have h₁ := hF.exp i hi w (by rw [← hzw]; exact hz)
      have h₂ := hF.qmono i head (by omega) hht
      omega
    · rw [upd_of_ne _ hzw]; exact hF.exp i hi z hz

/-- **The exit argument.** Once the queue is empty, every threshold below
the cap is decided correctly, and the proof is an induction on the
threshold rather than a clause of the loop invariant. The last edge of a
walk of length `k + 1` runs from a vertex the induction hypothesis has
placed at distance at most `k`; that vertex is alive, since an edge of
the arena has two live ends, hence it is on the queue, hence — the queue
being empty — it has been expanded. -/
theorem complete (hF : Frontier G M d s D Q tail tail) :
    ∀ k, k ≤ d → ∀ w, WD G M k s w → D w ≤ k := by
  intro k
  induction k with
  | zero =>
      intro _ w hwd
      rw [← hwd.eq_of_zero, hF.src]
  | succ k ih =>
      intro hk w hwd
      rcases hwd.tail with hshort | ⟨c, hc, hcw⟩
      · have := ih (by omega) w hshort; omega
      · have hcd : D c ≤ k := ih (by omega) c hc
        obtain ⟨i, hi, hQi⟩ := hF.qall c hc.lt_right hcw.alive_left (by omega)
        have hstep := hF.exp i hi w (by rw [hQi]; exact hcw)
        rw [hQi] at hstep
        omega

/-- **What the primitive computes**, as the ↔ at each threshold that the
distance-profile colours of this submission consume directly. -/
theorem dist_le_iff (hF : Frontier G M d s D Q tail tail) {w : ℕ} (hw : w < n) {k : ℕ}
    (hk : k ≤ d) : D w ≤ k ↔ WD G M k s w :=
  ⟨fun h => (hF.sound w hw (by omega)).mono h, hF.complete k hk w⟩

end Frontier

/-! The two states the seed can leave, one per branch of its
conditional. -/

/-- A live source goes on the queue. -/
theorem frontier_seed_alive (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d : ℕ) (hs : s < n)
    (hms : M s ≠ 0) {g Q : ℕ → ℕ} (hg : ∀ j < n, g j = d + 1) (hQ : Q 0 = s) :
    Frontier G M d s (upd g s 0) Q 0 1 := by
  have hval : ∀ z, z < n → z ≠ s → upd g s 0 z = d + 1 := fun z hz hzs => by
    rw [upd_of_ne _ hzs]; exact hg z hz
  refine ⟨fun z hz => ?_, upd_self .., fun z hz hzd => ?_, by omega, by omega, fun i hi => ?_,
    fun z hz hmz hzd => ?_, fun i hi j hj hij => by omega, fun i j hij hj => ?_,
    fun i hi j hj₁ hj₂ => ?_, fun i hi => absurd hi (by omega)⟩
  · by_cases hzs : z = s
    · rw [hzs, upd_self]; omega
    · rw [hval z hz hzs]
  · have hzs : z = s := by by_contra hne; rw [hval z hz hne] at hzd; omega
    subst hzs
    rw [upd_self]
    exact WD.refl G M 0 hs
  · have hi0 : i = 0 := by omega
    rw [hi0, hQ, upd_self]
    exact ⟨hs, by omega, hms⟩
  · have hzs : z = s := by by_contra hne; rw [hval z hz hne] at hzd; omega
    exact ⟨0, by omega, by rw [hQ, hzs]⟩
  · have : i = 0 ∧ j = 0 := by omega
    rw [this.1, this.2]
  · have : i = 0 ∧ j = 0 := by omega
    rw [this.1, this.2]; omega

/-- A dead source does not: its balls in the arena are `{s}`, which the
sentinel already says. -/
theorem frontier_seed_dead (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d : ℕ) (hs : s < n)
    (hms : M s = 0) {g Q : ℕ → ℕ} (hg : ∀ j < n, g j = d + 1) :
    Frontier G M d s (upd g s 0) Q 0 0 := by
  have hval : ∀ z, z < n → z ≠ s → upd g s 0 z = d + 1 := fun z hz hzs => by
    rw [upd_of_ne _ hzs]; exact hg z hz
  refine ⟨fun z hz => ?_, upd_self .., fun z hz hzd => ?_, by omega, by omega,
    fun i hi => absurd hi (by omega), fun z hz hmz hzd => ?_,
    fun i hi j hj hij => absurd hi (by omega), fun i j hij hj => absurd hj (by omega),
    fun i hi j hj₁ hj₂ => absurd hj₂ (by omega), fun i hi => absurd hi (by omega)⟩
  · by_cases hzs : z = s
    · rw [hzs, upd_self]; omega
    · rw [hval z hz hzs]
  · have hzs : z = s := by by_contra hne; rw [hval z hz hne] at hzd; omega
    subst hzs
    rw [upd_self]
    exact WD.refl G M 0 hs
  · exfalso
    have hzs : z = s := by by_contra hne; rw [hval z hz hne] at hzd; omega
    rw [hzs] at hmz; exact hmz hms

/-! ### The state of the machine -/

/-- The five arrays the search works on and the two scalars it never
moves.

**The target array's width** is `nt` (rebase B5-cont-2), and the block
structure's slot count enters nowhere in this relation: it is
`CsrGraph G ns O T` that says how far the structure reaches, and the
walk below carries `ns ≤ nt` alongside it. That separation is the
whole of the widening here — the search reads only slots below
`O n = ns`, so a target array with a tail above the slot count changes
nothing it does. -/
def SearchEnv (n nt s : ℕ) (O T M D Q : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "n" = n ∧ τ.vars "src" = s ∧
  τ.arrs "off" = arrOf (n + 1) O ∧ τ.arrs "tgt" = arrOf nt T ∧
  τ.arrs "alv" = arrOf n M ∧ τ.arrs "dist" = arrOf n D ∧ τ.arrs "q" = arrOf n Q

/-- The invariant of the block scan: a search in progress, the position
reached in the block of `v`, and the two facts that make the scan a step
of the search — every live target already passed is at most one level
below `v`, and the queue below `head` has not moved. -/
def ScanInv {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (nt d s head v dv sc₀ : ℕ)
    (O T Q₀ : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ D Q, SearchEnv n nt s O T M D Q τ ∧ Frontier G M d s D Q head (τ.vars "tail") ∧
    τ.vars "head" = head ∧ head < τ.vars "tail" ∧ Q head = v ∧ D v = dv ∧
    τ.vars "v" = v ∧ τ.vars "dv" = dv ∧ τ.vars "dn" = dv + 1 ∧
    τ.vars "jend" = O (v + 1) ∧ O v ≤ τ.vars "j" ∧ τ.vars "j" ≤ O (v + 1) ∧
    τ.vars "sc" = sc₀ + (τ.vars "j" - O v) ∧
    (∀ j', O v ≤ j' → j' < τ.vars "j" → M (T j') ≠ 0 → D (T j') ≤ dv + 1) ∧
    (∀ i < head, Q i = Q₀ i)

/-- One slot of the block of `v`. The block is walked by `run_vcg`; what
is left is what the three paths *did*, and on the relaxing path that is
`Frontier.relax`. -/
theorem scanSlot_run {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {head v dv sc₀ : ℕ} (hv : v < n) (hsc₀ : sc₀ + Csr.rowLen O v ≤ ns)
    {Q₀ : ℕ → ℕ} {τ : Env} (hI : ScanInv G M nt d s head v dv sc₀ O T Q₀ τ)
    (hjlt : τ.vars "j" < O (v + 1)) :
    ∃ τ' K, Run B scanSlot τ τ' K ∧ K ≤ 40 ∧
      ScanInv G M nt d s head v dv sc₀ O T Q₀ τ' ∧ τ'.vars "j" = τ.vars "j" + 1 := by
  obtain ⟨D, Q, ⟨hn, hsrc, hoff, htgt, halv, hdist, hq⟩, hF, hhead, hht, hqv, hDv, hvv,
    hdvv, hdnv, hje, hj₁, hj₂, hsc, hscan, hq₀⟩ := hI
  obtain ⟨hvn', hdvle, hmv⟩ := hF.qmem head hht
  rw [hqv] at hvn' hdvle hmv
  rw [hDv] at hdvle
  have hrow : Csr.rowLen O v = O (v + 1) - O v := rfl
  have hns : O (v + 1) ≤ ns := hcsr.le_ns (by omega)
  have hjns : τ.vars "j" < ns := by omega
  have hwn : T (τ.vars "j") < n := hcsr.target_lt' hv hjlt
  have hrj : (τ.arrs "tgt").getD (τ.vars "j") 0 = T (τ.vars "j") := by
    rw [htgt, getD_arrOf T (by omega)]
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
  have hdistv : (τ.arrs "dist").getD ((τ.arrs "tgt").getD (τ.vars "j") 0) 0
      = D (T (τ.vars "j")) := by rw [hrj, hdist, getD_arrOf D hwn]
  have hdistB : (τ.arrs "dist").getD ((τ.arrs "tgt").getD (τ.vars "j") 0) 0 < B := by
    rw [hdistv]; have := hF.cap _ hwn; omega
  have hqlen : (τ.arrs "q").length = n := by rw [hq, length_arrOf]
  have hscB : τ.vars "sc" + 1 < B := by omega
  have hjB : τ.vars "j" + 1 < B := by omega
  have hdnB : τ.vars "dn" < B := by omega
  have hMw : M (T (τ.vars "j")) < B := hMB _ hwn
  have hDw : D (T (τ.vars "j")) ≤ d + 1 := hF.cap _ hwn
  have htlB : τ.vars "tail" ≤ n := hF.tl
  -- the two reads the two conditionals make, in the shape the walk states
  -- them: the environment the second command of the block runs in
  have hbrAlv : ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).arrs "alv").getD
      ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "w") 0
      = M (T (τ.vars "j")) := by rw [arrs_setVar, vars_setVar]; simpa using halvv
  have hbrDist : ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).arrs "dist").getD
      ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "w") 0
      = D (T (τ.vars "j")) := by rw [arrs_setVar, vars_setVar]; simpa using hdistv
  have hbrDn : (τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "dn" = dv + 1 := by
    simpa using hdnv
  -- **the room argument**, which only the relaxing path needs: a vertex
  -- carrying more than one level below the head is not on the queue, by
  -- `qcap`, so the queue is shorter than the graph
  have hroom : dv + 1 < D (T (τ.vars "j")) → τ.vars "tail" < n := by
    intro hlt'
    refine hF.tail_lt hwn ?_
    intro i hi hqi
    have hc := hF.qcap i hi head le_rfl hht
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
      ⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt], by simp [halv],
        by simp [hdist, hrj', hdnv, set_arrOf_eq_upd],
        by simp [hq, hrj', set_arrOf_eq_upd]⟩,
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
    refine ⟨⟨D, Q, ⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt],
        by simp [halv], by simp [hdist], by simp [hq]⟩,
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
    refine ⟨⟨D, Q, ⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt],
        by simp [halv], by simp [hdist], by simp [hq]⟩,
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
/-- **The whole block of `v`, scanned.** The loop is the kit's row scan:
the caller says what a slot does and how far it moves the pointer, and
the combinator supplies the loop condition, the exit fact and the cost —
forty-four per slot of the block. -/
theorem scan_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {head v dv sc₀ : ℕ} (hv : v < n) (hsc₀ : sc₀ + Csr.rowLen O v ≤ ns) {Q₀ : ℕ → ℕ} :
    Spec B (fun τ => ScanInv G M nt d s head v dv sc₀ O T Q₀ τ ∧ τ.vars "j" = O v)
      (Csr.scan "j" "jend" scanSlot)
      (fun _ τ' => ScanInv G M nt d s head v dv sc₀ O T Q₀ τ' ∧ τ'.vars "j" = O (v + 1))
      (44 * Csr.rowLen O v + 4) := by
  have hrow : Csr.rowLen O v = O (v + 1) - O v := rfl
  have hns : O (v + 1) ≤ ns := hcsr.le_ns (by omega)
  refine Csr.rowScan_spec B (44 * Csr.rowLen O v + 4) (O (v + 1)) 40 "j" "jend" scanSlot
    (ScanInv G M nt d s head v dv sc₀ O T Q₀) (by omega) (fun σ hσ => ?_) (fun σ hσ hlt => ?_)
    (fun _ hσ => hσ.1) (fun σ hσ => by rw [hσ.2]; omega)
  · obtain ⟨D, Q, -, -, -, -, -, -, -, -, -, hje, -, hjle, -, -, -⟩ := hσ
    exact ⟨hje, hjle⟩
  · obtain ⟨σ', K', hr, hK, hI', hj'⟩ :=
      scanSlot_run hcsr hnB hnsB hnt hdB hMB hv hsc₀ hσ hlt
    exact ⟨σ', K', hr, hI', hj', hK⟩

/-! ### Emptying the queue -/

/-- The invariant of the search loop. -/
def DrainInv {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (nt d s : ℕ) (O T : ℕ → ℕ)
    (τ : Env) : Prop :=
  ∃ D Q, SearchEnv n nt s O T M D Q τ ∧
    Frontier G M d s D Q (τ.vars "head") (τ.vars "tail") ∧
    τ.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head"), Csr.rowLen O (Q i)

/-- Taking one vertex off the queue and scanning its whole block. The
block is walked end to end — the two offset reads in the middle of it are
the kit's `Csr.loadRow_spec`, matched against a *prefix* of it — and the
scan is handed over already stated so that what it gives back is what
this turn owes. -/
theorem expandRow_run {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B) {D Q : ℕ → ℕ} {τ : Env}
    (hse : SearchEnv n nt s O T M D Q τ)
    (hF : Frontier G M d s D Q (τ.vars "head") (τ.vars "tail"))
    (hht : τ.vars "head" < τ.vars "tail")
    (hsum : τ.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head"), Csr.rowLen O (Q i)) :
    ∃ τ' K, Run B expandRow τ τ' K ∧ K ≤ 44 * Csr.rowLen O (Q (τ.vars "head")) + 30 ∧
      DrainInv G M nt d s O T τ' ∧ τ'.vars "head" = τ.vars "head" + 1 ∧
      τ'.vars "sc" = τ.vars "sc" + Csr.rowLen O (Q (τ.vars "head")) := by
  obtain ⟨hn, hsrc, hoff, htgt, halv, hdist, hq⟩ := id hse
  have htln := hF.tl
  have hhn : τ.vars "head" < n := by omega
  obtain ⟨v, hvdef⟩ : ∃ v, Q (τ.vars "head") = v := ⟨_, rfl⟩
  rw [hvdef]
  obtain ⟨hvn, hdvd, hmv⟩ := hF.qmem _ hht
  rw [hvdef] at hvn hdvd hmv
  have hrow : Csr.rowLen O v = O (v + 1) - O v := rfl
  have hns : O (v + 1) ≤ ns := hcsr.le_ns (by omega)
  have hov : O v ≤ O (v + 1) := hcsr.mono v hvn
  -- the block of the vertex just dequeued is paid for out of the target array
  have hsc₀ : τ.vars "sc" + Csr.rowLen O v ≤ ns := by
    have hstep : ∑ i ∈ Finset.range (τ.vars "head" + 1), Csr.rowLen O (Q i) ≤ ns :=
      hcsr.sum_rowLen_queue (fun i hi => (hF.qmem i (by omega)).1)
        (fun i hi j hj hqe => hF.qinj i (by omega) j (by omega) hqe)
    rw [Finset.sum_range_succ, hvdef] at hstep
    omega
  -- the offsets and the targets are the kit's block structure, at the
  -- widened relation: the structure occupies the prefix `ns ≤ nt`
  have hcsrRel : CsrWide.CsrW "off" "tgt" n ns nt n O T τ :=
    ⟨hoff, htgt, fun i hi => hcsr.mono i hi, hcsr.last, hnt,
      fun p hp => hcsr.target_lt p hp⟩
  -- what the read at the head of the queue owes
  have hrv : (τ.arrs "q").getD (τ.vars "head") 0 = v := by
    rw [hq, getD_arrOf Q hhn, hvdef]
  have hrv' : (τ.arrs "q")[τ.vars "head"]?.getD 0 = v := by
    rw [← List.getD_eq_getElem?_getD]; exact hrv
  have hqlen : τ.vars "head" < (τ.arrs "q").length := by rw [hq, length_arrOf]; omega
  have hvB : (τ.arrs "q").getD (τ.vars "head") 0 < B := by rw [hrv]; omega
  -- and the distance read at what it named, in the environment that read runs in
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
      (fun σ => ScanInv G M nt d s (τ.vars "head") v (D v) (τ.vars "sc") O T Q σ ∧
        σ.vars "j" = O v)
      (Csr.scan "j" "jend" scanSlot)
      (fun _ σ' => DrainInv G M nt d s O T (σ'.setVar "head" (τ.vars "head" + 1)) ∧
        σ'.vars "head" = τ.vars "head" ∧
        σ'.vars "sc" = τ.vars "sc" + Csr.rowLen O v ∧ σ'.vars "head" + 1 < B)
      (44 * Csr.rowLen O v + 4) :=
    (scan_spec hcsr hnB hnsB hnt hdB hMB hvn hsc₀ (Q₀ := Q)).post fun _ σ' _ hQ => by
      obtain ⟨⟨D', Q', hse', hF', hhead', hht', hqv', hDv', hvv', hdvv', hdnv', hje',
        hjge', hjle', hsc', hscanned, hq₀'⟩, hj₄⟩ := hQ
      obtain ⟨hn', hsrc', hoff', htgt', halv', hdist', hq'⟩ := id hse'
      have hscv : σ'.vars "sc" = τ.vars "sc" + Csr.rowLen O v := by rw [hsc', hj₄, hrow]
      refine ⟨⟨D', Q', ⟨by simp [hn'], by simp [hsrc'], by simp [hoff'], by simp [htgt'],
          by simp [halv'], by simp [hdist'], by simp [hq']⟩, ?_, ?_⟩,
        hhead', hscv, by omega⟩
      · -- the search is live one vertex further along
        refine ⟨hF'.cap, hF'.src, hF'.sound, by simp; omega, by simpa using hF'.tl,
          by simpa using hF'.qmem, by simpa using hF'.qall, by simpa using hF'.qinj,
          by simpa using hF'.qmono, ?_, ?_⟩
        · intro i hi j hj₁ hj₂
          simp at hi hj₁ hj₂
          exact hF'.qcap i hi j (by omega) hj₂
        · intro i hi z hz
          simp at hi
          rcases Nat.lt_or_ge i (τ.vars "head") with hlt | hge
          · exact hF'.exp i hlt z hz
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
  run_vcg [CsrWide.loadRow_spec B n ns nt n "off" "tgt" "v" "j" "jend" O T (by decide)
      (by decide),
    hscanSpec]
  · -- what the block did is what the scan handed back
    simp_all
  · -- the two offset reads: a row of the structure, and its number a word
    exact ⟨⟨by simpa using hcsrRel, by omega, hnsB⟩, by simp [hrv']; omega,
      by simp [hrv']; omega⟩
  · -- the scan starts at the top of the block, in the state the reads left
    obtain ⟨-, -, -, rfl⟩ :=
      ‹CsrWide.LoadRowPostW "off" "tgt" "v" "j" "jend" n ns nt n O T _ _›
    refine ⟨⟨D, Q, ⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt],
        by simp [halv], by simp [hdist], by simp [hq]⟩, by simpa using hF, by simp,
      by simpa using hht, hvdef, rfl, by simp [hrv'], by simp [hdval'], by simp [hdval'],
      by simp [hrv'], by simp [hrv'], by simpa [hrv'] using hov, by simp [hrv'], ?_,
      fun i _ => rfl⟩, by simp [hrv']⟩
    intro j' h₁ h₂ h₃
    simp [hrv'] at h₂
    omega

/-- The potential the search is paid out of: forty-four units per slot
not yet looked at, forty per vertex not yet enqueued, and forty per
vertex still waiting on the queue. It is global — the searches of a whole
pass draw on the same budget — which is why the loop rule takes a
potential and not a constant per turn. -/
def Pot (n ns : ℕ) (τ : Env) : ℕ :=
  44 * (ns - τ.vars "sc") + 40 * (n - τ.vars "tail") + 40 * (τ.vars "tail" - τ.vars "head")

/-- **The search.** The queue is emptied, and the whole cost of doing so
is paid out of the potential — including the scans, whose cost no
constant per turn of the loop could bound. The loop is the kit's
`Queue.drain_run`: the queue supplies the loop condition and the exit
fact `head = tail`, and what is left here is the one thing that is this
algorithm's, that a turn pays for itself. -/
theorem drain_run {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B) {τ : Env}
    (hI : DrainInv G M nt d s O T τ) :
    ∃ τ' K, Run B bfsDrain τ τ' K ∧ DrainInv G M nt d s O T τ' ∧
      τ'.vars "head" = τ'.vars "tail" ∧ K + Pot n ns τ' ≤ Pot n ns τ + 4 := by
  refine Queue.drain_run B n n "q" "head" "tail" expandRow (DrainInv G M nt d s O T)
    (Pot n ns) (fun σ hσ => ?_) hnB (fun σ hσ hlt => ?_) hI
  · -- the invariant carries a queue: the discovered vertices, in arrival order
    obtain ⟨D₁, Q₁, ⟨-, -, -, -, -, -, hq⟩, hFr, -⟩ := hσ
    exact ⟨Q₁, σ.vars "head", σ.vars "tail", hq, rfl, rfl, hFr.hd, hFr.tl,
      fun i hi => (hFr.qmem i hi).1⟩
  · -- a turn pays for itself out of the potential
    obtain ⟨D₁, Q₁, hse, hFr, hsum⟩ := hσ
    obtain ⟨σ', K, hrun, hK, hI', hhead', hsc'⟩ :=
      expandRow_run hcsr hnB hnsB hnt hdB hMB hse hFr hlt hsum
    refine ⟨σ', K, hrun, hI', ?_⟩
    obtain ⟨D₂, Q₂, -, hFr', hsum'⟩ := hI'
    have hhd := hFr'.hd
    have htl := hFr'.tl
    have hsc₂ : σ'.vars "sc" ≤ ns := by
      rw [hsum']
      exact hcsr.sum_rowLen_queue (fun i hi => (hFr'.qmem i (by omega)).1)
        (fun i hi j hj hqe => hFr'.qinj i (by omega) j (by omega) hqe)
    have hhd0 := hFr.hd
    have htl0 := hFr.tl
    simp only [Pot]
    omega

/-! ### Seeding

The one command of the whole program that mentions the source: it is
given distance zero unconditionally, put at the front of the queue, and
counted in only if the mask says it is alive. -/

/-- Putting the source at distance zero and, when it is alive, on the
queue. The two branches of the conditional are the two states
`frontier_seed_alive` and `frontier_seed_dead` describe. -/
theorem seedSrc_run {B : ℕ} (hs : s < n) (hnB : n < B) (hdB : d + 1 < B)
    (hMB : ∀ z < n, M z < B) {g g' : ℕ → ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hsrc : σ.vars "src" = s)
    (hoff : σ.arrs "off" = arrOf (n + 1) O) (htgt : σ.arrs "tgt" = arrOf nt T)
    (halv : σ.arrs "alv" = arrOf n M) (hdist : σ.arrs "dist" = arrOf n g)
    (hgd : ∀ j < n, g j = d + 1) (hq : σ.arrs "q" = arrOf n g') :
    ∃ σ' K, Run B seedSrc σ σ' K ∧ K ≤ 20 ∧ DrainInv G M nt d s O T σ' ∧
      σ'.vars "head" = 0 ∧ σ'.vars "sc" = 0 := by
  have hsB : σ.vars "src" < B := by rw [hsrc]; omega
  have hdlen : σ.vars "src" < (σ.arrs "dist").length := by
    rw [hdist, length_arrOf, hsrc]; exact hs
  have hqlen : (σ.arrs "q").length = n := by rw [hq, length_arrOf]
  have halvlen : (σ.arrs "alv").length = n := by rw [halv, length_arrOf]
  have halvv : (σ.arrs "alv").getD (σ.vars "src") 0 = M s := by
    rw [halv, hsrc, getD_arrOf M hs]
  have halvv' : (σ.arrs "alv")[σ.vars "src"]?.getD 0 = M s := by
    rw [← List.getD_eq_getElem?_getD]; exact halvv
  have hMs : M s < B := hMB s hs
  run_vcg
  · -- an alive source goes on the queue
    refine ⟨⟨upd g s 0, upd g' 0 s, ⟨by simp [hn], by simp [hsrc], by simp [hoff],
        by simp [htgt], by simp [halv], by simp [hdist, hsrc, set_arrOf_eq_upd],
        by simp [hq, hsrc, set_arrOf_eq_upd]⟩, ?_, by simp⟩, by simp, by simp⟩
    have h := frontier_seed_alive G M d hs (by omega) hgd (upd_self g' 0 s)
    simpa using h
  · -- a dead source does not
    refine ⟨⟨upd g s 0, upd g' 0 s, ⟨by simp [hn], by simp [hsrc], by simp [hoff],
        by simp [htgt], by simp [halv], by simp [hdist, hsrc, set_arrOf_eq_upd],
        by simp [hq, hsrc, set_arrOf_eq_upd]⟩, ?_, by simp⟩, by simp, by simp⟩
    have h := frontier_seed_dead G M d hs (g := g) (Q := upd g' 0 s) (by omega) hgd
    simpa using h

/-! ### The primitive

The three phases in one specification: the fill, the seed and the search.
The cost is `51 n + 44 ns + 30` — linear in the graph, which is what the
evaluator's per-cluster budget is spent against; the sharp charging is a
later phase's business and nothing here anticipates it. -/

/-- The number-level distance bound is the concepts' `WithinDist` in the
concepts' `deleteVerts`, with the range conditions moved into the
statement. -/
theorem wd_iff_withinDist {k a b : ℕ} (ha : a < n) (hb : b < n) :
    WD G M k a b ↔ WithinDist (masked G M) k ⟨a, ha⟩ ⟨b, hb⟩ :=
  ⟨fun h => h.2.2, fun h => ⟨ha, hb, h⟩⟩

/-- And the arena really is the isolation of the dead vertices. -/
theorem masked_def (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) :
    masked G M = Lax12.UniformQuasiWideness.deleteVerts G {u : Fin n | M (u : ℕ) = 0} := rfl

/-- **Depth-capped breadth-first search over a masked block structure.**
Handed a block structure for `G`, a mask, a source and two arrays of the
right length, `bfsCom d` leaves in `dist` a function that decides, at
every threshold up to the cap, the distance bound of the arena — the
graph `G` with the mask's dead vertices isolated. Nothing is asked of the
source but that it is a vertex: a dead one is at distance zero from
itself and from nothing else, which is what the arena says too.

**At the widened target array** (rebase B5-cont-2): the block structure
is read out of an array of the caller's own width `nt`, the structure's
slot count `ns` being only a lower bound of it. Nothing the search
addresses moves — every slot it reads lies below `O n = ns ≤ nt`, which
is what `CsrWide.CsrW` states and what the two straight-line reads of
`expandRow` go through — and neither the postcondition nor the cost
mentions the width: the potential is still `44·ns`, because it is the
*slots* the search pays for and not the array. `bfs_spec` is this
walk at `nt = ns`. -/
theorem bfs_specW {B : ℕ} (hcsr : CsrGraph G ns O T) (hs : s < n) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
        σ.arrs "alv" = arrOf n M ∧ (∃ g, σ.arrs "dist" = arrOf n g) ∧
        (∃ g, σ.arrs "q" = arrOf n g))
      (bfsCom d)
      (fun _ σ' => ∃ D, σ'.arrs "dist" = arrOf n D ∧
        ∀ (v : Fin n) (k : ℕ), k ≤ d →
          (D (v : ℕ) ≤ k ↔ WithinDist (masked G M) k ⟨s, hs⟩ v))
      (51 * n + 44 * ns + 30) := by
  -- what the fill may touch, read off its syntax: the counter and `dist`
  have hwv : "n" ∉ (initDist d).wvars := by simp [initDist, Fill.put, Com.wvars]
  have hwv' : "src" ∉ (initDist d).wvars := by simp [initDist, Fill.put, Com.wvars]
  have hwa₁ : "off" ∉ (initDist d).warrs := by simp [initDist, Fill.put, Com.warrs]
  have hwa₂ : "tgt" ∉ (initDist d).warrs := by simp [initDist, Fill.put, Com.warrs]
  have hwa : "alv" ∉ (initDist d).warrs := by simp [initDist, Fill.put, Com.warrs]
  have hwa' : "q" ∉ (initDist d).warrs := by simp [initDist, Fill.put, Com.warrs]
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hsrc, hoff, htgt, halv, ⟨g₀, hdist⟩, ⟨g₁, hq⟩⟩ := hσ
  -- the fill: the kit's array pass, with the sentinel as the cell function
  obtain ⟨σ₁, hrun₁, ⟨⟨g, hdist₁, hgd⟩, -⟩, hfv, hfa, -, -⟩ :=
    ((Fill.loop_spec B n "dist" "i" "n" (.lit (d + 1)) (fun _ => d + 1) (by decide) hnB
      (fun _ _ _ _ => evalB_lit hdB)).frame).run (σ := σ) ⟨⟨g₀, hdist⟩, hn⟩
  -- the seed, in the state the fill left
  obtain ⟨σ₂, K₂, hrun₂, hK₂, hI₂, hhead₂, hsc₂⟩ :=
    seedSrc_run (G := G) (O := O) (T := T) (nt := nt) hs hnB hdB hMB
      (by rw [hfv "n" hwv]; exact hn) (by rw [hfv "src" hwv']; exact hsrc)
      (by rw [hfa "off" hwa₁]; exact hoff) (by rw [hfa "tgt" hwa₂]; exact htgt)
      (by rw [hfa "alv" hwa]; exact halv) hdist₁ hgd (by rw [hfa "q" hwa']; exact hq)
  -- and the search
  obtain ⟨σ₃, K₃, hrun₃, hI₃, hhead₃, hpay⟩ := drain_run hcsr hnB hnsB hnt hdB hMB hI₂
  obtain ⟨D₂, Q₂, -, hFr₂, -⟩ := hI₂
  obtain ⟨D, Q, ⟨-, -, -, -, -, hdist₃, -⟩, hFr, -⟩ := hI₃
  have htl₂ : σ₂.vars "tail" ≤ n := hFr₂.tl
  have hpot₂ : Pot n ns σ₂ = 44 * ns + 40 * n := by
    simp only [Pot, hhead₂, hsc₂]; omega
  refine ⟨σ₃, _, (hrun₁.seq (hrun₂.seq hrun₃)).mono ?_, le_rfl, D, hdist₃, fun v k hk => ?_⟩
  · rw [hpot₂] at hpay
    simp only [size_lit]
    omega
  · rw [hhead₃] at hFr
    exact (hFr.dist_le_iff v.isLt hk).trans (wd_iff_withinDist hs v.isLt)

/-- **The search at the pinned target array** — the frozen export,
which is the widened walk at `nt = ns`. Nothing is re-proved: the two
preconditions are the same proposition there. -/
theorem bfs_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hs : s < n) (hnB : n < B)
    (hnsB : ns < B) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
        σ.arrs "alv" = arrOf n M ∧ (∃ g, σ.arrs "dist" = arrOf n g) ∧
        (∃ g, σ.arrs "q" = arrOf n g))
      (bfsCom d)
      (fun _ σ' => ∃ D, σ'.arrs "dist" = arrOf n D ∧
        ∀ (v : Fin n) (k : ℕ), k ≤ d →
          (D (v : ℕ) ≤ k ↔ WithinDist (masked G M) k ⟨s, hs⟩ v))
      (51 * n + 44 * ns + 30) :=
  bfs_specW hcsr hs hnB hnsB le_rfl hdB hMB

section Falsification

/-! The widening's one authored delta is `SearchEnv`'s `tgt` clause,
and its refutable reading is that it is no delta — that the search's
environment at a width above the slot count is the environment at the
slot count. It is not: a search with no vertices and no slots, in a
length-one target array, already separates them, because the pinned
reading asks for the array at the slot count on the nose. -/

/-- No vertices, no slots, and one cell in `tgt`. -/
private def wideBfsEnv : Env where
  vars := fun _ => 0
  arrs := fun a => if a = "off" ∨ a = "tgt" then [0] else []
  inp := []
  out := []

-- the search's environment holds of it at width `1` …
example : SearchEnv 0 1 0 (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) wideBfsEnv :=
  ⟨rfl, rfl, by simp [wideBfsEnv, arrOf], by simp [wideBfsEnv, arrOf],
    by simp [wideBfsEnv, arrOf], by simp [wideBfsEnv, arrOf], by simp [wideBfsEnv, arrOf]⟩

-- … and is **refuted** at the slot count `0`, at every target function:
-- the length is the width, not the number of slots.
example : ¬ ∃ T, SearchEnv 0 0 0 (fun _ => 0) T (fun _ => 0) (fun _ => 0)
    (fun _ => 0) wideBfsEnv := by
  rintro ⟨T, -, -, -, htgt, -⟩
  simp [wideBfsEnv, arrOf] at htgt

end Falsification

/-! ### The worked example

House discipline: what the specification says is also *seen*. The graph
is the path `0—1—2—3` with an isolated vertex `4`; the program builds its
block structure with its own stores, since the machine's memory starts
zeroed, and writes the five distances out.

The mask on vertex `2` is the parameter, so the same program shows both
sides of the isolation: with `2` alive the four distances are the path's,
and with `2` dead the arena falls apart into `{0,1}` and `{2,3}` and
everything beyond `1` reads the sentinel. The cap is the other parameter,
and lowering it truncates the readings from the far end. -/

namespace Demo

/-- The offsets of the path `0—1—2—3` with an isolated vertex `4`. -/
def demoOff : Com :=
  .seq (.store "off" (.lit 0) (.lit 0))
    (.seq (.store "off" (.lit 1) (.lit 1))
      (.seq (.store "off" (.lit 2) (.lit 3))
        (.seq (.store "off" (.lit 3) (.lit 5))
          (.seq (.store "off" (.lit 4) (.lit 6))
            (.store "off" (.lit 5) (.lit 6))))))

/-- Its targets: `1 | 0 2 | 1 3 | 2 |`. -/
def demoTgt : Com :=
  .seq (.store "tgt" (.lit 0) (.lit 1))
    (.seq (.store "tgt" (.lit 1) (.lit 0))
      (.seq (.store "tgt" (.lit 2) (.lit 2))
        (.seq (.store "tgt" (.lit 3) (.lit 1))
          (.seq (.store "tgt" (.lit 4) (.lit 3))
            (.store "tgt" (.lit 5) (.lit 2))))))

/-- The mask, with the bit of vertex `2` left open. -/
def demoAlv (a2 : ℕ) : Com :=
  .seq (.store "alv" (.lit 0) (.lit 1))
    (.seq (.store "alv" (.lit 1) (.lit 1))
      (.seq (.store "alv" (.lit 2) (.lit a2))
        (.seq (.store "alv" (.lit 3) (.lit 1))
          (.store "alv" (.lit 4) (.lit 1)))))

/-- Five vertices, six slots, the search starting at `0`. -/
def demoSetup (a2 : ℕ) : Com :=
  .seq (.assign "n" (.lit 5))
    (.seq (.assign "src" (.lit 0))
      (.seq demoOff (.seq demoTgt (demoAlv a2))))

/-- The five distances, in vertex order. -/
def demoReport : Com :=
  .seq (.write (.get "dist" (.lit 0)))
    (.seq (.write (.get "dist" (.lit 1)))
      (.seq (.write (.get "dist" (.lit 2)))
        (.seq (.write (.get "dist" (.lit 3)))
          (.write (.get "dist" (.lit 4))))))

/-- Build the structure, search, report. -/
def demoWatched (a2 d : ℕ) : Com := .seq (demoSetup a2) (.seq (bfsCom d) demoReport)

/-- Twelve scalars, the five arrays, four temporaries. -/
def demoLayout : Lax13Proofs.Compile.Layout :=
  ⟨["n", "src", "i", "head", "tail", "sc", "v", "w", "dv", "dn", "j", "jend"],
   ["off", "tgt", "alv", "dist", "q"], 4⟩

/-- The machine program. -/
def demoProg (a2 d : ℕ) : Lax13.Ram.Program :=
  Lax13Proofs.Compile.compileProgram demoLayout (demoWatched a2 d)

/-- The layout covers the block, so the compilation is the one the
simulation theorem is about and not an accident. -/
theorem demoWatched_ok (a2 d : ℕ) :
    Lax13Proofs.Compile.Com.Ok demoLayout (demoWatched a2 d) := by
  simp [demoWatched, demoSetup, demoOff, demoTgt, demoAlv, demoReport, bfsCom, initDist,
    seedSrc, bfsDrain, expandRow, scanSlot, Fill.put, Csr.loadRow, Csr.scan, Queue.drain,
    demoLayout, Lax13Proofs.Compile.Com.Ok, Lax13Proofs.Compile.Cond.Ok,
    Lax13Proofs.Compile.condExpr, Lax13Proofs.Compile.Expr.Ok]

/-- Run it at a word length that holds every number this graph
produces. -/
def demoRun (a2 d : ℕ) : Option (List ℕ × ℕ) :=
  runOut 16 400000 (demoProg a2 d) (Lax13.Ram.initState []) 0

-- vertex `2` alive, cap `3`: the path's own distances, the isolated
-- vertex `4` at the sentinel
#guard demoRun 1 3 = some ([0, 1, 2, 3, 4], 1139)
-- vertex `2` dead: the arena falls apart, and only `0` and `1` are reached
#guard demoRun 0 3 = some ([0, 1, 4, 4, 4], 747)
-- and lowering the cap truncates from the far end
#guard demoRun 1 1 = some ([0, 1, 2, 2, 2], 763)
#guard demoRun 1 0 = some ([0, 1, 1, 1, 1], 544)

end Demo

end Lax3Proofs.RamBfs
