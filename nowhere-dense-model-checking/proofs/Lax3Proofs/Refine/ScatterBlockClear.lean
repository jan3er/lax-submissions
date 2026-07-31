import Lax3Proofs.Refine.ScatterBlockProg

/-!
# The clearing pass, at the active set

`RamScatter.clearExc` fills all `n` exclusion bits and charges `11 n` for
it. `clearMem` walks the member list instead and clears the `mm` cells
the scan will ever read. This file is that walk.

The postcondition has the two clauses the relativised invariant needs and
no more: every member of `X` comes out cleared — which is
`MemList.complete`, every member is listed — and every carrier cell that
is *not* a member comes out untouched — which is `MemList.sound`,
everything listed is a member, so nothing else is ever stored to. The
carrier cells outside `X` keep whatever the previous atom left there, and
`ProgressA` is exactly the invariant that does not ask about them.
-/

namespace Lax3Proofs.Refine.ScatterBlock

open Lax3.ColoredGraphs Lax3.ScatterSentences
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs Lax3Proofs.RamScatter

/-! ### §1 What holds part-way through the clear

Three clauses carry the work: the loop's own bound and pointer, the
member list unchanged in `mem`, and an exclusion array which is zero at
every member the walk has passed and untouched everywhere else. The
"everywhere else" is stated at the *carrier*, not at the members: it is
the clause that says the pass writes nowhere it was not asked to. -/

/-- The invariant of the member-list clearing scan. -/
def ClearInv (n mm : ℕ) (Mem E : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "mm" = mm ∧ τ.arrs "mem" = arrOf mm Mem ∧ τ.vars "mj" ≤ mm ∧
    ∃ E', τ.arrs "exc" = arrOf n E' ∧
      (∀ i, i < τ.vars "mj" → E' (Mem i) = 0) ∧
      (∀ w, w < n → (∀ i, i < τ.vars "mj" → Mem i ≠ w) → E' w = E w)

/-! ### §2 One member

Read the member off the list, clear its bit, advance. Ten steps: three
for the read, three for the store, four for the bump. The store is in
range because `MemList.lt` says a listed entry is a vertex. -/

/-- **One entry of the member list, cleared.** -/
theorem clearSlot_run {B n mm : ℕ} {Mem E : ℕ → ℕ} (hnB : n < B) (hmmB : mm < B)
    (hml : ∀ j, j < mm → Mem j < n) {τ : Env} (hI : ClearInv n mm Mem E τ)
    (hj : τ.vars "mj" < mm) :
    ∃ τ' K, Run B clearSlot τ τ' K ∧ K ≤ 10 ∧ ClearInv n mm Mem E τ' ∧
      τ'.vars "mj" = τ.vars "mj" + 1 := by
  obtain ⟨hmm, hmem, hjle, E', hexc, hzero, hkeep⟩ := hI
  have hmjn : Mem (τ.vars "mj") < n := hml _ hj
  -- the read at the member list
  have hrm : (τ.arrs "mem").getD (τ.vars "mj") 0 = Mem (τ.vars "mj") := by
    rw [hmem, getD_arrOf Mem hj]
  have hrm' : (τ.arrs "mem")[τ.vars "mj"]?.getD 0 = Mem (τ.vars "mj") := by
    rw [← List.getD_eq_getElem?_getD]; exact hrm
  have hmemlen : τ.vars "mj" < (τ.arrs "mem").length := by
    rw [hmem, length_arrOf]; exact hj
  have hvB : (τ.arrs "mem").getD (τ.vars "mj") 0 < B := by rw [hrm]; omega
  -- and the store at the exclusion array, in the environment that store runs in
  have hexclen : (τ.arrs "exc").length = n := by rw [hexc, length_arrOf]
  have hstlen : ((τ.setVar "mv" ((τ.arrs "mem").getD (τ.vars "mj") 0)).vars "mv")
      < ((τ.setVar "mv" ((τ.arrs "mem").getD (τ.vars "mj") 0)).arrs "exc").length := by
    rw [arrs_setVar, vars_setVar, hexclen]
    rw [if_pos rfl, hrm]; exact hmjn
  have hB0 : 0 < B := by omega
  have hmj1B : τ.vars "mj" + 1 < B := by omega
  run_vcg
  refine ⟨⟨by simp [hmm], by simp [hmem], by simp; omega,
    upd E' (Mem (τ.vars "mj")) 0, by simp [hexc, hrm', set_arrOf_eq_upd], ?_, ?_⟩, by simp⟩
  · -- every member passed is now zero
    intro i hi
    simp at hi
    by_cases hie : Mem i = Mem (τ.vars "mj")
    · rw [hie, upd_self]
    · rw [upd_of_ne _ hie]
      have hine : i ≠ τ.vars "mj" := fun h => hie (by rw [h])
      exact hzero i (by omega)
  · -- and nothing else moved
    intro w hw hne
    simp at hne
    have hwne : Mem (τ.vars "mj") ≠ w := hne _ (by omega)
    rw [upd_of_ne _ hwne.symm]
    exact hkeep w hw (fun i hi => hne i (by omega))

/-! ### §3 The walk

The kit's counted loop, at fourteen per member: ten for the body and four
for the test that let it run. -/

/-- **The member list, walked.** -/
theorem clearMem_scan_spec {B n mm : ℕ} {Mem E : ℕ → ℕ} (hnB : n < B) (hmmB : mm < B)
    (hml : ∀ j, j < mm → Mem j < n) :
    Spec B (fun τ => ClearInv n mm Mem E τ ∧ τ.vars "mj" = 0)
      (Csr.scan "mj" "mm" clearSlot)
      (fun _ τ' => ClearInv n mm Mem E τ' ∧ τ'.vars "mj" = mm)
      (14 * mm + 4) := by
  refine Csr.rowScan_spec B (14 * mm + 4) mm 10 "mj" "mm" clearSlot
    (ClearInv n mm Mem E) hmmB (fun σ hσ => ⟨hσ.1, hσ.2.2.1⟩) (fun σ hσ hlt => ?_)
    (fun _ hσ => hσ.1) (fun σ hσ => by rw [hσ.2]; omega)
  obtain ⟨σ', K', hr, hK, hI', hj'⟩ := clearSlot_run hnB hmmB hml hσ hlt
  exact ⟨σ', K', hr, hI', hj', hK⟩

/-! ### §4 The pass

`mj := 0` and then the walk. Fourteen per member plus six, against the
`25 mm + 12` the charge fixed before the walk existed. -/

/-- **The clearing pass, end to end, at the cost the program actually
has.** Every member of `X` comes out with its exclusion bit zero, and
every carrier cell that is not a member comes out exactly as it went in.
The member list itself is untouched.

The charge `clearMemK mm = 25 mm + 12` was fixed before this walk
existed; the walk comes in under it, at `14 mm + 6`, and the slack is
recorded here rather than spent. -/
theorem clearMem_run_tight {B : ℕ} {n mm : ℕ} {Mem E : ℕ → ℕ} {X : Set (Fin n)} {τ : Env}
    (hnB : n < B) (hmmB : mm < B) (hml : MemList n mm Mem X)
    (hmm : τ.vars "mm" = mm)
    (hmemarr : τ.arrs "mem" = arrOf mm Mem)
    (hexc : τ.arrs "exc" = arrOf n E) :
    ∃ τ' K, Run B clearMem τ τ' K ∧ K ≤ 14 * mm + 6 ∧
      τ'.arrs "mem" = arrOf mm Mem ∧
      ∃ E', τ'.arrs "exc" = arrOf n E' ∧
        (∀ w, MemOf X w → E' w = 0) ∧
        (∀ w, w < n → ¬ MemOf X w → E' w = E w) := by
  have hscanSpec := clearMem_scan_spec (n := n) (mm := mm) (Mem := Mem) (E := E) (B := B)
    hnB hmmB hml.lt
  have hB0 : 0 < B := by omega
  run_vcg [hscanSpec]
  · -- what the loop left, read back through the member list
    rename_i w hpost
    obtain ⟨⟨hmm', hmem', -, E', hexc', hzero', hkeep'⟩, hjend⟩ := hpost
    refine ⟨hmem', E', hexc', fun z hz => ?_, fun z hz hnm => ?_⟩
    · obtain ⟨j, hj, hMj⟩ := hml.complete z hz
      have := hzero' j (by rw [hjend]; exact hj)
      rwa [hMj] at this
    · refine hkeep' z hz (fun i hi hMi => hnm ?_)
      rw [← hMi]
      exact hml.sound i (by rw [← hjend]; exact hi)
  · -- and the loop starts at the top of the list
    exact ⟨⟨by simp [hmm], by simp [hmemarr], by simp, E, by simp [hexc],
      fun i hi => by simp at hi, fun z _ _ => rfl⟩, by simp⟩

/-- **The clearing pass, at the charge.** The same walk, weakened to the
constant `ScatterBlockCost` fixed for it; this is the form the engine
wires. -/
theorem clearMem_run {B : ℕ} {n mm : ℕ} {Mem E : ℕ → ℕ} {X : Set (Fin n)} {τ : Env}
    (hnB : n < B) (hmmB : mm < B) (hml : MemList n mm Mem X)
    (hn : τ.vars "n" = n) (hmm : τ.vars "mm" = mm)
    (hmemarr : τ.arrs "mem" = arrOf mm Mem)
    (hexc : τ.arrs "exc" = arrOf n E) :
    ∃ τ' K, Run B clearMem τ τ' K ∧ K ≤ clearMemK mm ∧
      τ'.arrs "mem" = arrOf mm Mem ∧
      ∃ E', τ'.arrs "exc" = arrOf n E' ∧
        (∀ w, MemOf X w → E' w = 0) ∧
        (∀ w, w < n → ¬ MemOf X w → E' w = E w) := by
  obtain ⟨τ', K, hrun, hK, hrest⟩ := clearMem_run_tight hnB hmmB hml hmm hmemarr hexc
  exact ⟨τ', K, hrun, by simp only [clearMemK]; omega, hrest⟩

#print axioms clearMem_run

end Lax3Proofs.Refine.ScatterBlock
