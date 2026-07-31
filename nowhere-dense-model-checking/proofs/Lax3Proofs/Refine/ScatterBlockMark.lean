import Lax3Proofs.Refine.ScatterBlockProg

/-!
# Marking the ball: the walk of `markBall`

The landed engine's marking sweep is a flat pass over the whole distance
array. The active-set engine's is a pass over the queue the block search
handed back — and the queue *is* the ball — followed by one
unconditional store at the source, which is the cell a dead source
occupies without ever being enqueued.

This file is that walk, and nothing else. It mirrors
`Refine/BfsBlock.lean`'s `unwind_run` limb for limb: a counted
`Csr.scan` over `q[0 .. tail)` through `Csr.rowScan_spec`, then the
source's own store. The walk is simpler than the unwind's — a literal is
stored rather than a read-back distance, and no second output array is
written — so the invariant carries two working clauses where the
unwind's carries four: the cells the walk has passed hold `1`, and the
cells it has not hold what they held. Queue injectivity is not needed at
all, because the walk only ever writes the same value.

### The guard, and what it does *not* buy

`markSlot`'s test `mw < n` was put there so that the store into `exc`
has a range obligation the caller can discharge without the bound
`∀ i < tail, Q i < n` that `BfsBlock.bfsBlock_spec` drops at its
interface. It does buy that. It does **not** buy the walk, because the
store is not the first thing the slot does: the slot *reads* `q[ri]`
first, and in IMP+ an array read whose value does not fit the word is
stuck exactly as an out-of-range store is (`evalB_get_iff`'s last
conjunct). So the walk still needs a word bound on the queue's entries,
and `markSlot_run` and `markBall_run` below take it as `hqB`.

`hqB` is the weakest hypothesis that makes the read run, and it is
implied by either repair: exporting `Frontier.qmem`'s first component
from `bfsBlock_spec` — the fact already named `hqn` inside
`bfsBlock_specW`'s own proof — gives `Q i < n < B` at once. Until one of
those lands, `hqB` is where the obligation sits, stated rather than
hidden.

### The charge

The body costs fourteen — three for the read, seven for the guarded
store, four for the bump — the scan combinator adds four per turn and
four at the exit, and the two limbs around it cost two and three:
`18 tf + 9`, which is `markBall_run_tight`. The fixed charge
`markBallK tf = 30 tf + 20` is met with a third of its linear term to
spare, which is the slack `ScatterBlockCost.lean` says its numerals were
chosen with. Without the guard the body would cost ten and the walk
`14 tf + 9`; the guard is four per ball vertex.
-/

namespace Lax3Proofs.Refine.ScatterBlock

open Lax3.ColoredGraphs Lax3.ScatterSentences
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs Lax3Proofs.RamScatter

/-! ### The invariant

Where the walk stands after `ri` entries: the exclusion cells named by
the vertices among `q[0 .. ri)` are set, and every other cell below `n`
is untouched. Both clauses are relativised to `w < n`, which is what
makes the guard invisible: a suppressed store could only ever have fired
outside that range.

The queue, the carrier size, the source's name and the bound are pinned
because the scan combinator hands the whole invariant back as its
postcondition — `n` is read by the guard, and `src` and the arrays are
what the final store and the export need. -/

/-- **What holds part-way through the marking walk.** -/
def MarkInv (n s tf : ℕ) (Q E : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ E', τ.vars "n" = n ∧ τ.vars "src" = s ∧ τ.vars "tail" = tf ∧
    τ.arrs "q" = arrOf n Q ∧ τ.arrs "exc" = arrOf n E' ∧
    τ.vars "ri" ≤ tf ∧
    (∀ w, w < n → (∃ i, i < τ.vars "ri" ∧ Q i = w) → E' w = 1) ∧
    (∀ w, w < n → ¬ (∃ i, i < τ.vars "ri" ∧ Q i = w) → E' w = E w)

/-- **One entry of the ball.** Read the vertex off the queue, set its
exclusion bit if it is a vertex, advance. The guard supplies the store's
range obligation; `hqB` supplies the read's word obligation. Cost
fourteen: three, seven and four. -/
theorem markSlot_run {B n s tf : ℕ} (hnB : n < B) (htf : tf ≤ n)
    {Q E : ℕ → ℕ} (hqB : ∀ i, i < tf → Q i < B)
    {τ : Env} (hI : MarkInv n s tf Q E τ) (hlt : τ.vars "ri" < tf) :
    ∃ τ' K, Run B markSlot τ τ' K ∧ K ≤ 14 ∧
      MarkInv n s tf Q E τ' ∧ τ'.vars "ri" = τ.vars "ri" + 1 := by
  obtain ⟨E', hn, hsrc, htl, hq, hexc, hri, hmark, hkeep⟩ := hI
  have hrin : τ.vars "ri" < n := by omega
  -- the read at the queue
  have hrq : (τ.arrs "q").getD (τ.vars "ri") 0 = Q (τ.vars "ri") := by
    rw [hq, getD_arrOf Q hrin]
  have hrq' : (τ.arrs "q")[τ.vars "ri"]?.getD 0 = Q (τ.vars "ri") := by
    rw [← List.getD_eq_getElem?_getD]; exact hrq
  have hqlen : τ.vars "ri" < (τ.arrs "q").length := by rw [hq, length_arrOf]; exact hrin
  have hvB : (τ.arrs "q").getD (τ.vars "ri") 0 < B := by rw [hrq]; exact hqB _ hlt
  -- the guard's two operands, and the store's array
  have hexclen : (τ.arrs "exc").length = n := by rw [hexc, length_arrOf]
  have h1B : 1 < B := by omega
  have hriB : τ.vars "ri" + 1 < B := by omega
  run_vcg
  · -- the guard held: the entry is a vertex, and its bit goes up
    refine ⟨⟨upd E' (Q (τ.vars "ri")) 1,
      by simp [hn], by simp [hsrc], by simp [htl], by simp [hq],
      by simp [hexc, hrq', set_arrOf_eq_upd], by simp; omega, ?_, ?_⟩, by simp⟩
    · intro w hw hex
      by_cases hwq : w = Q (τ.vars "ri")
      · rw [hwq, upd_self]
      · rw [upd_of_ne _ hwq]
        obtain ⟨i, hi, hQi⟩ := hex
        simp at hi
        have hine : i ≠ τ.vars "ri" := by rintro rfl; exact hwq hQi.symm
        exact hmark w hw ⟨i, by omega, hQi⟩
    · intro w hw hex
      have hwq : w ≠ Q (τ.vars "ri") := by
        rintro rfl; exact hex ⟨τ.vars "ri", by simp, rfl⟩
      rw [upd_of_ne _ hwq]
      refine hkeep w hw fun h => hex ?_
      obtain ⟨i, hi, hQi⟩ := h
      exact ⟨i, by simp; omega, hQi⟩
  · -- the guard failed: the entry is not a vertex, and nothing is written
    rename_i hguard
    have hg : n ≤ Q (τ.vars "ri") := by simpa [vars_setVar, hn, hrq, hrq'] using hguard
    refine ⟨⟨E', by simp [hn], by simp [hsrc], by simp [htl], by simp [hq],
      by simp [hexc], by simp; omega, ?_, ?_⟩, by simp⟩
    · intro w hw hex
      obtain ⟨i, hi, hQi⟩ := hex
      simp at hi
      have hine : i ≠ τ.vars "ri" := by rintro rfl; omega
      exact hmark w hw ⟨i, by omega, hQi⟩
    · intro w hw hex
      refine hkeep w hw fun h => hex ?_
      obtain ⟨i, hi, hQi⟩ := h
      exact ⟨i, by simp; omega, hQi⟩
  · -- the guarded store is in range, which is what the guard is for
    rename_i hguard
    simp only [arrs_setVar, hexclen]
    simpa [vars_setVar, hn] using hguard

/-- **The ball, walked.** The kit's counted loop at a body cost of
fourteen: eighteen per entry of the queue plus the exit test. -/
theorem markBall_scan_spec {B n s tf : ℕ} (hnB : n < B) (htf : tf ≤ n)
    {Q E : ℕ → ℕ} (hqB : ∀ i, i < tf → Q i < B) :
    Spec B (fun τ => MarkInv n s tf Q E τ ∧ τ.vars "ri" = 0)
      (Csr.scan "ri" "tail" markSlot)
      (fun _ τ' => MarkInv n s tf Q E τ' ∧ τ'.vars "ri" = tf)
      (18 * tf + 4) := by
  refine Csr.rowScan_spec B (18 * tf + 4) tf 14 "ri" "tail" markSlot
    (MarkInv n s tf Q E) (by omega) (fun σ hσ => ?_) (fun σ hσ hlt => ?_)
    (fun _ hσ => hσ.1) (fun σ hσ => by rw [hσ.2]; omega)
  · obtain ⟨E₁, -, -, htl, -, -, hri, -⟩ := hσ
    exact ⟨htl, hri⟩
  · obtain ⟨σ', K', hr, hK, hI', hri'⟩ := markSlot_run hnB htf hqB hσ hlt
    exact ⟨σ', K', hr, hI', hri', hK⟩

/-- **Marking the ball, end to end, at the cost the walk actually
achieves.** The queue segment is walked and every vertex on it excluded;
then the source's own bit is set unconditionally, because the block
search writes a dead source's distance cell but never enqueues it. What
comes out is the queue untouched and the exclusion array agreeing with
what came in off the marked set, which is the queue segment together
with the source. -/
theorem markBall_run_tight {B : ℕ} {n tf s : ℕ} {Q E : ℕ → ℕ} {τ : Env}
    (hnB : n < B) (hs : s < n) (htf : tf ≤ n) (hqB : ∀ i, i < tf → Q i < B)
    (hn : τ.vars "n" = n) (hsrc : τ.vars "src" = s) (htl : τ.vars "tail" = tf)
    (hq : τ.arrs "q" = arrOf n Q) (hexc : τ.arrs "exc" = arrOf n E) :
    ∃ τ' K, Run B markBall τ τ' K ∧ K ≤ 18 * tf + 9 ∧
      τ'.arrs "q" = arrOf n Q ∧
      ∃ E', τ'.arrs "exc" = arrOf n E' ∧
        (∀ w, w < n → ((∃ i, i < tf ∧ Q i = w) ∨ w = s) → E' w = 1) ∧
        (∀ w, w < n → ¬ ((∃ i, i < tf ∧ Q i = w) ∨ w = s) → E' w = E w) := by
  have h1B : 1 < B := by omega
  have hscanSpec := markBall_scan_spec (n := n) (s := s) (B := B) hnB htf hqB (Q := Q) (E := E)
  run_vcg [hscanSpec]
  · -- what the loop left, plus the source's own cell
    rename_i w hpost
    obtain ⟨⟨E', hn', hsrc', htl', hq', hexc', -, hmark', hkeep'⟩, hriend⟩ := hpost
    refine ⟨by simp [hq'], upd E' s 1, by simp [hexc', hsrc', set_arrOf_eq_upd], ?_, ?_⟩
    · intro z hz hmem
      by_cases hzs : z = s
      · rw [hzs, upd_self]
      · rw [upd_of_ne _ hzs]
        rcases hmem with ⟨i, hi, hQi⟩ | h
        · exact hmark' z hz ⟨i, by omega, hQi⟩
        · exact absurd h hzs
    · intro z hz hmem
      have hzs : z ≠ s := fun h => hmem (Or.inr h)
      rw [upd_of_ne _ hzs]
      refine hkeep' z hz fun h => hmem (Or.inl ?_)
      obtain ⟨i, hi, hQi⟩ := h
      exact ⟨i, by omega, hQi⟩
  · -- the loop starts at the top of the queue
    exact ⟨⟨E, by simp [hn], by simp [hsrc], by simp [htl], by simp [hq], by simp [hexc],
      by simp, fun z _ hex => by obtain ⟨i, hi, -⟩ := hex; simp at hi,
      fun _ _ _ => rfl⟩, by simp⟩
  · -- the source's number is a word
    rename_i w hleft hpost
    obtain ⟨⟨E', -, hsrc', -⟩, -⟩ := hpost
    rw [hsrc']; omega
  · -- and its cell is inside the exclusion array
    rename_i w hleft hpost
    obtain ⟨⟨E', -, hsrc', -, -, hexc', -⟩, -⟩ := hpost
    rw [hsrc', hexc', length_arrOf]; exact hs

/-- **The walk, against the fixed charge.** `markBallK tf = 30 tf + 20`
is met with room: the walk costs `18 tf + 9`. -/
theorem markBall_run {B : ℕ} {n tf s : ℕ} {Q E : ℕ → ℕ} {τ : Env}
    (hnB : n < B) (hs : s < n) (htf : tf ≤ n) (hqB : ∀ i, i < tf → Q i < B)
    (hn : τ.vars "n" = n) (hsrc : τ.vars "src" = s) (htl : τ.vars "tail" = tf)
    (hq : τ.arrs "q" = arrOf n Q) (hexc : τ.arrs "exc" = arrOf n E) :
    ∃ τ' K, Run B markBall τ τ' K ∧ K ≤ markBallK tf ∧
      τ'.arrs "q" = arrOf n Q ∧
      ∃ E', τ'.arrs "exc" = arrOf n E' ∧
        (∀ w, w < n → ((∃ i, i < tf ∧ Q i = w) ∨ w = s) → E' w = 1) ∧
        (∀ w, w < n → ¬ ((∃ i, i < tf ∧ Q i = w) ∨ w = s) → E' w = E w) := by
  obtain ⟨τ', K, hrun, hK, hrest⟩ := markBall_run_tight hnB hs htf hqB hn hsrc htl hq hexc
  exact ⟨τ', K, hrun, by simp only [markBallK]; omega, hrest⟩

#print axioms markBall_run

end Lax3Proofs.Refine.ScatterBlock
