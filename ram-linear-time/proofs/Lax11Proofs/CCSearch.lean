import Lax11Proofs.CCGraph
import Lax11Proofs.CCPhases
import Lax13Proofs.Lib.Csr

/-!
The search: scanning one block, emptying the queue, and the sweep over
the vertices.

Everything rests on one observation, which is what keeps the invariant
small: **a label, once written, is already the right one.** A vertex is
labelled only when it is found from a root `u` that was unlabelled when
the sweep reached it, and such a `u` is the least vertex of its own
component; so the label written is the label the answer calls for. The
array therefore always holds, at each vertex, either the marker `n` or
the true label, and the algorithm's remaining job is only to *reach*
every vertex.

`Base` is what holds throughout the run, whichever search is going on:
the labels are right or absent, the queue holds exactly the labelled
vertices without repetition, and everything before `head` has had its
whole block looked at — with its neighbours getting *its* label, not
the current root's, which is what makes that clause survive the change
of root. `Live` adds what holds only inside a search from `u`.

The queue is never reset, so `Base` speaks about all of it and the
searches are told apart only by `Live.cur`, the fact that the part
still to be expanded belongs to the current search. That is what buys
the cost argument its global budget.

Two numbers bound everything the search produces: `n`, which every
vertex, label and queue pointer stays below, and `2m`, which every
offset, scan pointer and slot counter stays below. So the value bound
of the bounded semantics enters as the two hypotheses `n < B` and
`2 * m < B` and adds nothing to the invariants — with one exception,
the slot counter, whose bound is the amortization argument itself and
is therefore passed in as `sc₀ + deg x v ≤ 2 * m` where the scan needs
it.

Two things here are the kit's rather than this driver's. The body of
the scan is walked by `run_vcg`, so what is left of `scanBody_run` is
what the two paths *did*; and the scan itself is `Csr.rowScan_spec`,
which supplies the loop condition, the exit fact `j = off (v+1)` and
the cost of thirty a slot. The three reads that open `expandBody` are
still written out: they are a chain, the index of each being the value
the one before read, and stating their obligations for the walk costs
what building their `Run`s costs.
-/

namespace Lax11Proofs.CC

open Lax13.Ram Lax11.GraphEncoding Lax11.ConnectedComponents
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning
open Lax13Proofs.Reasoning.Lib

variable {x : List ℕ} {B n m u head tail : ℕ} {G : SimpleGraph (Fin n)} {O T L Q : ℕ → ℕ}

/-! ### What holds throughout the run -/

/-- The state of the label array and the queue, at any point of the
run. -/
structure Base (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) (L Q : ℕ → ℕ)
    (head tail : ℕ) : Prop where
  /-- A written label is the right label. -/
  lab : ∀ w < n, L w = n ∨ L w = lbl G w
  /-- The queue is a segment. -/
  hd : head ≤ tail
  /-- The queue holds vertices. -/
  tl : tail ≤ n
  /-- Everything on the queue is a labelled vertex. -/
  qmem : ∀ i < tail, Q i < n ∧ L (Q i) ≠ n
  /-- Every labelled vertex is on the queue. -/
  qall : ∀ w < n, L w ≠ n → ∃ i < tail, Q i = w
  /-- Nothing is on the queue twice. -/
  qinj : ∀ i < tail, ∀ j < tail, Q i = Q j → i = j
  /-- The block of a vertex before `head` has been looked at, and its
  neighbours carry that vertex's own label. -/
  exp : ∀ i < head, ∀ j, offset x (Q i) ≤ j → j < offset x (Q i + 1) →
    L (target x j) = L (Q i)

/-- Every entry of the label array is a vertex or the marker, so it is
at most `n`: the one bound the search needs of a label. -/
theorem Base.lab_le (hB : Base x n G L Q head tail) {w : ℕ} (hw : w < n) : L w ≤ n :=
  (hB.lab w hw).elim (fun h => h.le) (fun h => le_of_lt (h ▸ lbl_lt hw))

/-- What holds during a search from the root `u`. -/
structure Live (x : List ℕ) (n u : ℕ) (G : SimpleGraph (Fin n)) (L Q : ℕ → ℕ)
    (head tail : ℕ) : Prop where
  /-- The state of the arrays. -/
  base : Base x n G L Q head tail
  /-- Every component below `u` is done. -/
  done : ∀ w < n, lbl G w < u → L w ≠ n
  /-- No label above `u` has been written. -/
  low : ∀ w < n, L w ≠ n → L w ≤ u
  /-- The root is labelled. -/
  root : L u ≠ n
  /-- What is left on the queue belongs to this search. -/
  cur : ∀ i, head ≤ i → i < tail → L (Q i) = u

/-- An unlabelled vertex is not on the queue, so there is room for one
more. -/
theorem Base.tail_lt (hB : Base x n G L Q head tail) {w : ℕ} (hw : w < n)
    (hL : L w = n) : tail < n := by
  have hsub : (Finset.range tail).image Q ⊆ (Finset.range n).erase w := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
    have hi' := Finset.mem_range.1 hi
    refine Finset.mem_erase.2 ⟨fun h => (hB.qmem i hi').2 (h ▸ hL), ?_⟩
    exact Finset.mem_range.2 (hB.qmem i hi').1
  have hcard : ((Finset.range tail).image Q).card = tail := by
    rw [Finset.card_image_of_injOn (fun i hi j hj h =>
      hB.qinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) h)]
    exact Finset.card_range tail
  have := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_range.2 hw), Finset.card_range] at this
  omega

/-- **The exit argument.** When the queue is empty, the labelled
vertices are closed under adjacency, hence under reachability. -/
theorem Base.rch_labelled (hx : EncodesGraph x n G) (hB : Base x n G L Q tail tail)
    {a b : ℕ} (h : Rch G a b) (ha : L a ≠ n) : L b ≠ n := by
  refine rch_closed (P := fun z => L z ≠ n) ?_ h ha
  intro c d hcd hc
  obtain ⟨i, hi, rfl⟩ := hB.qall c hcd.1 hc
  obtain ⟨j, hj₁, hj₂, hj₃⟩ := slot_of_adjn hx hcd
  rw [← hj₃, hB.exp i hi j hj₁ hj₂]
  exact hc

/-! ### The one change the arrays ever undergo

Labelling an unlabelled vertex with its own label and putting it on the
back of the queue: that is the whole of what the search writes, and the
sweep writes it too when it starts a search from a root. So the clauses
of `Base` and `Live` are re-established here once rather than at each of
the two sites. -/

/-- Labelling the unlabelled vertex `w` with its own label and enqueuing
it. The queue clauses survive because `w` was not on the queue — nothing
unlabelled is — and the expansion clause because nothing already
expanded can name `w` either. -/
theorem Base.enqueue (hB : Base x n G L Q head tail) {w : ℕ} (hw : w < n)
    (hnew : L w = n) (hlw : lbl G w = u) :
    Base x n G (upd L w u) (upd Q tail w) head (tail + 1) := by
  have hun : u < n := hlw ▸ lbl_lt hw
  have htail : tail < n := hB.tail_lt hw hnew
  have hhd := hB.hd
  have hQne : ∀ p, p < tail → Q p ≠ w := fun p hp hpw => (hB.qmem p hp).2 (by rw [hpw, hnew])
  refine ⟨fun z hz => ?_, by omega, by omega, fun i hi => ?_, fun z hz hlz => ?_,
    fun i hi j hj hij => ?_, fun i hi j hj₁ hj₂ => ?_⟩
  · by_cases hzw : z = w
    · exact Or.inr (by rw [hzw, hlw]; simp)
    · simpa [upd_of_ne _ hzw] using hB.lab z hz
  · by_cases hit : i = tail
    · rw [hit, upd_self, upd_self]; exact ⟨hw, by omega⟩
    · have hi' : i < tail := by omega
      rw [upd_of_ne _ hit, upd_of_ne _ (hQne i hi')]
      exact hB.qmem i hi'
  · by_cases hzw : z = w
    · exact ⟨tail, by omega, by rw [upd_self, hzw]⟩
    · rw [upd_of_ne _ hzw] at hlz
      obtain ⟨i, hi, rfl⟩ := hB.qall z hz hlz
      exact ⟨i, by omega, upd_of_ne _ (by omega)⟩
  · by_cases hit : i = tail <;> by_cases hjt : j = tail
    · omega
    · rw [hit, upd_self, upd_of_ne _ hjt] at hij
      exact absurd hij.symm (hQne j (by omega))
    · rw [hjt, upd_self, upd_of_ne _ hit] at hij
      exact absurd hij (hQne i (by omega))
    · rw [upd_of_ne _ hit, upd_of_ne _ hjt] at hij
      exact hB.qinj i (by omega) j (by omega) hij
  · have hit : i ≠ tail := by omega
    rw [upd_of_ne _ hit] at hj₁ hj₂ ⊢
    have hnotw : target x j ≠ w := fun hjw => by
      have h₁ := hB.exp i hi j hj₁ hj₂
      rw [hjw, hnew] at h₁
      exact (hB.qmem i (by omega)).2 h₁.symm
    rw [upd_of_ne _ hnotw, upd_of_ne _ (hQne i (by omega))]
    exact hB.exp i hi j hj₁ hj₂

/-- The same step inside a live search, when the vertex found carries
the label of the search: the root stays labelled and what is left on the
queue still belongs to this search, the new entry included. -/
theorem Live.enqueue (hL : Live x n u G L Q head tail) {w : ℕ} (hw : w < n)
    (hnew : L w = n) (hlw : lbl G w = u) :
    Live x n u G (upd L w u) (upd Q tail w) head (tail + 1) := by
  have hun : u < n := hlw ▸ lbl_lt hw
  have hQne : ∀ p, p < tail → Q p ≠ w :=
    fun p hp hpw => (hL.base.qmem p hp).2 (by rw [hpw, hnew])
  refine ⟨hL.base.enqueue hw hnew hlw, fun z hz hlz => ?_, fun z hz hlz => ?_, ?_,
    fun i hi₁ hi₂ => ?_⟩
  · by_cases hzw : z = w
    · rw [hzw, upd_self]; omega
    · rw [upd_of_ne _ hzw]; exact hL.done z hz hlz
  · by_cases hzw : z = w
    · rw [hzw, upd_self]
    · rw [upd_of_ne _ hzw] at hlz ⊢; exact hL.low z hz hlz
  · by_cases huw : u = w
    · rw [huw, upd_self]; omega
    · rw [upd_of_ne _ huw]; exact hL.root
  · by_cases hit : i = tail
    · rw [hit, upd_self, upd_self]
    · rw [upd_of_ne _ hit, upd_of_ne _ (hQne i (by omega))]
      exact hL.cur i hi₁ (by omega)

/-! ### The state of the machine -/

/-- The arrays and the three scalars that a search does not move. -/
def SearchEnv (n m u : ℕ) (O T L Q : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "n" = n ∧ τ.vars "u" = u ∧
  τ.arrs "off" = arrOf (n + 1) O ∧ τ.arrs "tgt" = arrOf (2 * m) T ∧
  τ.arrs "lab" = arrOf n L ∧ τ.arrs "q" = arrOf n Q

/-- The potential the search is paid out of: thirty units per adjacency
slot not yet looked at, twenty-three per vertex not yet enqueued, and
twenty-three per vertex waiting on the queue. -/
def Pot (n m : ℕ) (τ : Env) : ℕ :=
  30 * (2 * m - τ.vars "sc") + 23 * (n - τ.vars "tail") +
    23 * (τ.vars "tail" - τ.vars "head")

/-! ### Scanning one block -/

/-- The invariant of the scan loop: a live search, the position reached
in the block of `v`, and the two facts that make the scan a step of the
search — what has been looked at is labelled `u`, and the queue below
`head` has not moved. -/
def ScanInv (x : List ℕ) (n m u v head sc₀ : ℕ) (G : SimpleGraph (Fin n))
    (O T Q₀ : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ L Q, SearchEnv n m u O T L Q τ ∧ Live x n u G L Q head (τ.vars "tail") ∧
    τ.vars "head" = head ∧ head < τ.vars "tail" ∧ Q head = v ∧
    τ.vars "v" = v ∧ τ.vars "jend" = offset x (v + 1) ∧
    offset x v ≤ τ.vars "j" ∧ τ.vars "j" ≤ offset x (v + 1) ∧
    τ.vars "sc" = sc₀ + (τ.vars "j" - offset x v) ∧
    (∀ j', offset x v ≤ j' → j' < τ.vars "j" → L (target x j') = u) ∧
    (∀ i < head, Q i = Q₀ i)

/-- One slot of the block of `v`: if it names an unlabelled vertex, that
vertex is labelled and enqueued. The block is walked by `run_vcg`; what
is left is what the two paths *did*, and on the labelling path that is
`Live.enqueue`. -/
theorem scanBody_run (hx : EncodesGraph x n G) (hm : edgeCount x = m)
    (hT : ∀ j < 2 * m, T j = target x j) (hu : u < n) {v head sc₀ : ℕ} (hv : v < n)
    (hnB : n < B) (hmB : 2 * m < B) (hsc₀ : sc₀ + deg x v ≤ 2 * m)
    {Q₀ : ℕ → ℕ} {τ : Env} (hI : ScanInv x n m u v head sc₀ G O T Q₀ τ)
    (hjlt : τ.vars "j" < offset x (v + 1)) :
    ∃ τ' K, Run B scanBody τ τ' K ∧ K ≤ 26 ∧
      ScanInv x n m u v head sc₀ G O T Q₀ τ' ∧ τ'.vars "j" = τ.vars "j" + 1 := by
  obtain ⟨L, Q, ⟨hn, hup, hoff, htgt, hlab, hq⟩, hL, hhead, hht, hqv, hvv, hje,
    hj₁, hj₂, hsc, hscan, hq₀⟩ := hI
  have hB := hL.base
  have htl := hB.tl
  have hhd := hB.hd
  have h2m : offset x (v + 1) ≤ 2 * m := hm ▸ offset_le hx (by omega)
  have hjm : τ.vars "j" < 2 * m := by omega
  have hdegv : deg x v = offset x (v + 1) - offset x v := rfl
  -- the slot names a neighbour of `v`, and `v` carries the label of this search
  obtain ⟨w, hw⟩ : ∃ w, target x (τ.vars "j") = w := ⟨_, rfl⟩
  have hwn : w < n := hw ▸ target_lt' hx hv hjlt
  have hLv : L v = u := hqv ▸ hL.cur head le_rfl hht
  have hlw : lbl G w = u := by
    have h₁ := (hB.lab v hv).resolve_left (by rw [hLv]; omega)
    have h₂ := lbl_eq_of_rch (Rch.of_adjn (hw ▸ adjn_of_slot hx hv hj₁ hjlt))
    omega
  -- what the walk owes: the slot read, the label read at what it names,
  -- and the scalars the block moves
  have hrj : (τ.arrs "tgt").getD (τ.vars "j") 0 = w := by
    rw [htgt, getD_arrOf T hjm, hT _ hjm, hw]
  have hrj' : (τ.arrs "tgt")[τ.vars "j"]?.getD 0 = w := by
    rw [← List.getD_eq_getElem?_getD]; exact hrj
  have hvw : (τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "w"
      = (τ.arrs "tgt").getD (τ.vars "j") 0 := by simp
  have hbr : ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).arrs "lab").getD
      ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "w") 0 = L w := by
    rw [arrs_setVar, hvw, hrj, hlab, getD_arrOf L hwn]
  have hbn : (τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "n" = n := by simp [hn]
  have hjlen : τ.vars "j" < (τ.arrs "tgt").length := by rw [htgt, length_arrOf]; omega
  have hwB : (τ.arrs "tgt").getD (τ.vars "j") 0 < B := by rw [hrj]; omega
  have hwlen : (τ.arrs "tgt").getD (τ.vars "j") 0 < (τ.arrs "lab").length := by
    rw [hrj, hlab, length_arrOf]; exact hwn
  have hLwB : L w < B := by have := hB.lab_le hwn; omega
  have hscB : τ.vars "sc" + 1 < B := by omega
  have hjB : τ.vars "j" + 1 < B := by omega
  have hnB' : τ.vars "n" < B := by omega
  have huB : τ.vars "u" < B := by omega
  run_vcg
  · -- the vertex found is unlabelled: it is labelled and enqueued
    have hnew : L w = n := by omega
    have htail : τ.vars "tail" < n := hB.tail_lt hwn hnew
    refine ⟨⟨upd L w u, upd Q (τ.vars "tail") w,
      ⟨by simp [hn], by simp [hup], by simp [hoff], by simp [htgt],
        by simp [hlab, hrj', hup, set_arrOf_eq_upd], by simp [hq, hrj', set_arrOf_eq_upd]⟩,
      by simpa using hL.enqueue hwn hnew hlw, by simp [hhead], by simp; omega,
      by rw [upd_of_ne _ (by omega : head ≠ τ.vars "tail")]; exact hqv,
      by simp [hvv], by simp [hje], by simp; omega, by simp; omega, by simp [hsc]; omega,
      ?_, fun i hi => by rw [upd_of_ne _ (by omega : i ≠ τ.vars "tail")]; exact hq₀ i hi⟩,
      by simp⟩
    intro j' hj₁' hj₂'
    simp at hj₂'
    by_cases hyw : target x j' = w
    · rw [hyw, upd_self]
    · rw [upd_of_ne _ hyw]
      rcases Nat.lt_or_ge j' (τ.vars "j") with h | h
      · exact hscan j' hj₁' h
      · exact absurd (show j' = τ.vars "j" by omega) (by rintro rfl; exact hyw hw)
  · -- already labelled, and by this search, so nothing is written
    have hLw : L w = u := by
      have := (hB.lab w hwn).resolve_left (show ¬ L w = n by omega); omega
    refine ⟨⟨L, Q, ⟨by simp [hn], by simp [hup], by simp [hoff],
      by simp [htgt], by simp [hlab], by simp [hq]⟩, by simpa using hL, by simp [hhead],
      by simp [hht], hqv, by simp [hvv], by simp [hje], by simp; omega, by simp; omega,
      by simp [hsc]; omega, ?_, hq₀⟩, by simp⟩
    intro j' hj₁' hj₂'
    simp at hj₂'
    rcases Nat.lt_or_ge j' (τ.vars "j") with h | h
    · exact hscan j' hj₁' h
    · rw [show j' = τ.vars "j" by omega, hw]; exact hLw
  -- what the walk deferred: the queue has room, because the vertex just
  -- found is unlabelled and so is not on it
  all_goals
    (have hnew : L w = n := by omega
     have := hB.tail_lt hwn hnew
     simp [hq]
     omega)

/-- **The whole block of `v`, scanned.** The loop is the kit's row scan:
the caller says what a slot does and how far it moves the pointer, and
the combinator supplies the loop condition, the exit fact and the cost —
thirty per slot of the block. -/
theorem scan_spec (hx : EncodesGraph x n G) (hm : edgeCount x = m)
    (hT : ∀ j < 2 * m, T j = target x j) (hu : u < n) {v head sc₀ : ℕ} (hv : v < n)
    (hnB : n < B) (hmB : 2 * m < B) (hsc₀ : sc₀ + deg x v ≤ 2 * m) {Q₀ : ℕ → ℕ} :
    Spec B (fun τ => ScanInv x n m u v head sc₀ G O T Q₀ τ ∧ τ.vars "j" = offset x v)
      (.while (.lt (.var "j") (.var "jend")) scanBody)
      (fun _ τ' => ScanInv x n m u v head sc₀ G O T Q₀ τ' ∧ τ'.vars "j" = offset x (v + 1))
      (30 * deg x v + 4) := by
  have h2m : offset x (v + 1) ≤ 2 * m := hm ▸ offset_le hx (by omega)
  have hdegv : deg x v = offset x (v + 1) - offset x v := rfl
  refine Csr.rowScan_spec B (30 * deg x v + 4) (offset x (v + 1)) 26 "j" "jend" scanBody
    (ScanInv x n m u v head sc₀ G O T Q₀) (by omega)
    (fun σ hσ => by obtain ⟨-, -, -, -, -, -, -, -, hje, -, hjle, -⟩ := hσ; exact ⟨hje, hjle⟩)
    (fun σ hσ hlt => by
      obtain ⟨σ', K', hr, hK, hI', hj'⟩ := scanBody_run hx hm hT hu hv hnB hmB hsc₀ hσ hlt
      exact ⟨σ', K', hr, hI', hj', hK⟩) (fun _ hσ => hσ.1)
    (fun σ hσ => by rw [hσ.2]; omega)

/-! ### Emptying the queue -/

/-- The invariant of the search loop. -/
def DrainInv (x : List ℕ) (n m u : ℕ) (G : SimpleGraph (Fin n)) (O T : ℕ → ℕ)
    (τ : Env) : Prop :=
  ∃ L Q, SearchEnv n m u O T L Q τ ∧ Live x n u G L Q (τ.vars "head") (τ.vars "tail") ∧
    τ.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head"), deg x (Q i)

/-- Taking one vertex off the queue and scanning its block: the cost is
thirty per slot of that block and nineteen besides. The three reads are
written out rather than walked (see this file's header); the scan enters
as one step, by its specification. -/
theorem expandBody_run (hx : EncodesGraph x n G) (hm : edgeCount x = m)
    (hO : ∀ i ≤ n, O i = offset x i) (hT : ∀ j < 2 * m, T j = target x j) (hu : u < n)
    (hnB : n < B) (hmB : 2 * m < B)
    {τ : Env} (hSE : SearchEnv n m u O T L Q τ)
    (hL : Live x n u G L Q (τ.vars "head") (τ.vars "tail"))
    (hht : τ.vars "head" < τ.vars "tail")
    (hsc : τ.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head"), deg x (Q i)) :
    ∃ (τ' : Env) (K : ℕ), Run B expandBody τ τ' K ∧
      K ≤ 30 * deg x (Q (τ.vars "head")) + 19 ∧ DrainInv x n m u G O T τ' ∧
      τ'.vars "head" = τ.vars "head" + 1 ∧
      τ'.vars "sc" = τ.vars "sc" + deg x (Q (τ.vars "head")) := by
  obtain ⟨hn, hup, hoff, htgt, hlab, hq⟩ := hSE
  have hB := hL.base
  have hheadn : τ.vars "head" < n := by have := hB.tl; omega
  obtain ⟨v, hvdef⟩ : ∃ v, Q (τ.vars "head") = v := ⟨_, rfl⟩
  rw [hvdef]
  have hvn : v < n := hvdef ▸ (hB.qmem _ hht).1
  have htln := hB.tl
  -- the block of the vertex just dequeued is paid for out of the target array
  have hsum : τ.vars "sc" + deg x v ≤ 2 * m := by
    have hstep : ∑ i ∈ Finset.range (τ.vars "head" + 1), deg x (Q i) ≤ 2 * m := by
      rw [← hm]
      exact sum_deg_queue hx (fun i hi => (hB.qmem i (by omega)).1)
        (fun i hi j hj h => hB.qinj i (by omega) j (by omega) h)
    rw [Finset.sum_range_succ, hvdef] at hstep
    omega
  have hoffv : offset x v ≤ 2 * m := hm ▸ offset_le hx (by omega)
  have hoffv' : offset x (v + 1) ≤ 2 * m := hm ▸ offset_le hx (by omega)
  -- read the vertex, its block start and its block end
  have e₁ : (Expr.get "q" (.var "head")).evalB B τ = some v := by
    simp [hq, getElem?_arrOf Q hheadn, hvdef]; omega
  have e₂ : (Expr.get "off" (.var "v")).evalB B (τ.setVar "v" v) = some (offset x v) := by
    simp [hoff, getElem?_arrOf O (show v < n + 1 by omega), hO v (by omega)]; omega
  have e₃ : (Expr.get "off" (.add (.var "v") (.lit 1))).evalB B
      ((τ.setVar "v" v).setVar "j" (offset x v)) = some (offset x (v + 1)) := by
    simp [hoff, getElem?_arrOf O (show v + 1 < n + 1 by omega), hO (v + 1) (by omega)]
    omega
  -- the scan
  have hI₃ : ScanInv x n m u v (τ.vars "head") (τ.vars "sc") G O T Q
      (((τ.setVar "v" v).setVar "j" (offset x v)).setVar "jend" (offset x (v + 1))) :=
    ⟨L, Q, ⟨by simp [hn], by simp [hup], by simp [hoff], by simp [htgt],
        by simp [hlab], by simp [hq]⟩, by simpa using hL, by simp, by simpa using hht,
      hvdef, by simp, by simp, by simp,
      by simpa using offset_mono' hx (Nat.le_succ v) (show v + 1 ≤ n by omega),
      by simp, by intro j' h₁ h₂; simp at h₂; omega, fun i _ => rfl⟩
  obtain ⟨τ₄, hscan, hI₄, hj₄⟩ :=
    (scan_spec (B := B) hx hm hT hu hvn hnB hmB hsum (Q₀ := Q)).run ⟨hI₃, by simp⟩
  obtain ⟨L', Q', ⟨hn', hup', hoff', htgt', hlab', hq'⟩, hL', hhead', hht', hqv',
    hvv', hje', hjge', hjle', hsc', hscanned, hq₀'⟩ := hI₄
  have htl' := hL'.base.tl
  have hscv : τ₄.vars "sc" = τ.vars "sc" + deg x v := by rw [hsc', hj₄, deg]
  refine ⟨τ₄.setVar "head" (τ.vars "head" + 1), _,
    Run.seq (Run.assign (v := v) e₁)
      (Run.seq (Run.assign (v := offset x v) e₂)
        (Run.seq (Run.assign (v := offset x (v + 1)) e₃)
          (Run.seq hscan (Run.assign (v := τ.vars "head" + 1) (by simp [hhead']; omega))))),
    by simp; omega,
    ⟨L', Q', ⟨by simp [hn'], by simp [hup'], by simp [hoff'], by simp [htgt'],
      by simp [hlab'], by simp [hq']⟩, ?_, ?_⟩,
    by simp, by simpa using hscv⟩
  · -- the search is live one step further along
    have hLv : L' v = u := by rw [← hqv']; exact hL'.cur _ le_rfl hht'
    refine ⟨⟨hL'.base.lab, by simp; omega, by simpa using hL'.base.tl,
      by simpa using hL'.base.qmem, by simpa using hL'.base.qall,
      by simpa using hL'.base.qinj, ?_⟩,
      hL'.done, hL'.low, hL'.root, ?_⟩
    · intro i hi j hj₁ hj₂
      simp at hi
      rcases Nat.lt_or_ge i (τ.vars "head") with h | h
      · exact hL'.base.exp i h j hj₁ hj₂
      · have hie : i = τ.vars "head" := by omega
        subst hie
        rw [hqv'] at hj₁ hj₂ ⊢
        rw [hLv]
        exact hscanned j hj₁ (by rw [hj₄]; exact hj₂)
    · intro i hi₁ hi₂
      simp at hi₁ hi₂
      exact hL'.cur i (by omega) hi₂
  · -- the count of scanned slots is the sum over the queue
    show τ₄.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head" + 1), deg x (Q' i)
    rw [Finset.sum_range_succ,
      Finset.sum_congr rfl fun i hi => by rw [hq₀' i (Finset.mem_range.1 hi)],
      ← hsc, hqv', hsc', hj₄, deg]

/-- **The search.** The queue is emptied, and the whole cost of doing
so is paid out of the potential — including the scans, whose cost no
constant per turn of the loop could bound. -/
theorem drain_run (hx : EncodesGraph x n G) (hm : edgeCount x = m)
    (hO : ∀ i ≤ n, O i = offset x i) (hT : ∀ j < 2 * m, T j = target x j) (hu : u < n)
    (hnB : n < B) (hmB : 2 * m < B)
    {τ : Env} (hI : DrainInv x n m u G O T τ) :
    ∃ (τ' : Env) (K : ℕ), Run B drain τ τ' K ∧ DrainInv x n m u G O T τ' ∧
      τ'.vars "head" = τ'.vars "tail" ∧ K + Pot n m τ' ≤ Pot n m τ + 4 := by
  obtain ⟨τ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := Cond.lt (.var "head") (.var "tail")) (c := expandBody)
      (DrainInv x n m u G O T) (Pot n m)
      (fun σ hσ => by
        obtain ⟨L', Q', -, hLive, -⟩ := hσ
        have hhd := hLive.base.hd
        have htl := hLive.base.tl
        exact evalB_condLt_vars (by omega) (by omega))
      (fun σ hσ hc => by
        obtain ⟨L₁, Q₁, hSE, hLive, hsum⟩ := hσ
        obtain ⟨σ', K, hrun, hK, hI', hhead', hsc'⟩ :=
          expandBody_run hx hm hO hT hu hnB hmB hSE hLive (lt_of_condLt_true hc) hsum
        refine ⟨σ', K, hrun, hI', ?_⟩
        obtain ⟨L₂, Q₂, -, hLive', hsum'⟩ := hI'
        have hhd := hLive'.base.hd
        have htl := hLive'.base.tl
        have h2m : σ'.vars "sc" ≤ 2 * m := by
          rw [hsum', ← hm]
          exact sum_deg_queue hx (fun i hi => (hLive'.base.qmem i (by omega)).1)
            (fun i hi j hj h => hLive'.base.qinj i (by omega) j (by omega) h)
        have hhd0 := hLive.base.hd
        have htl0 := hLive.base.tl
        simp only [Pot, size_condLt, size_var]
        omega)
      hI
  refine ⟨τ', K, hrun, hI', ?_, by simpa using hpay⟩
  obtain ⟨L₁, Q₁, -, hL₁, -⟩ := hI'
  have := hL₁.base.hd
  have := le_of_condLt_false hfalse
  omega

end Lax11Proofs.CC
