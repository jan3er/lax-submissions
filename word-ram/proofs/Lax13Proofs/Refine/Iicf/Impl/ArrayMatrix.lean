import Lax13Proofs.Refine.Iicf.Intf.Matrix
import Lax13Proofs.Refine.Iicf.IicfArray

/-!
# Row-major array matrices

Faithful adaptation of `Refine_Imperative_HOL/IICF/Impl/IICF_Array_Matrix.thy`
from `maxhaslbeck/Sepreftime` commit
`c1c987b45ec886d289ba215768182ac87b82f20d`.

`amtx1Rel N M` is the source's `is_amtx N M`: a length-`N*M` row-major
array represents a matrix at index `i*M+j`, and the abstract matrix is zero
outside the rectangle.  The source's general tabulator allocates and invokes
a higher-order heap callback.  P0 has neither allocation nor runtime function
pointers, so `amtxTabulateModel` retains its full semantics but is not given a
fake executable rule.  Executable initialization is the honest caller-owned
default fill; get and set calculate the row-major index with actual `mul` and
`add` instructions before the array access.

The source's SepLogicTime/enat scalar bounds (`3*N*M+3` for tabulation,
`N*M+1` for default fill, and `1` for get/set) are recorded below only as
provenance.  They are not equated with this IR's vector-valued `ECost`.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

def amtxIndex (M i j : ℕ) : ℕ := i * M + j

def amtx1Rel (N M : ℕ) : Set (List ℕ × Matrix ℕ) :=
  {p | p.1.length = N * M ∧
    (∀ i < N, ∀ j < M, p.1[amtxIndex M i j]! = p.2 (i, j)) ∧
    ∀ i j, N ≤ i ∨ M ≤ j → p.2 (i, j) = 0}

theorem amtx_index_bound {N M i j : ℕ} (hi : i < N) (hj : j < M) :
    amtxIndex M i j < N * M := by
  unfold amtxIndex
  calc
    i * M + j < i * M + M := Nat.add_lt_add_left hj _
    _ = (i + 1) * M := by simp [Nat.add_mul]
    _ ≤ N * M := Nat.mul_le_mul_right M (Nat.succ_le_iff.mpr hi)

theorem amtx_index_unique {M i j i' j' : ℕ} (hj : j < M) (hj' : j' < M) :
    amtxIndex M i j = amtxIndex M i' j' ↔ i = i' ∧ j = j' := by
  have hM : 0 < M := Nat.zero_lt_of_lt hj
  constructor
  · intro h
    have hi : i = i' := by
      have hd := congrArg (fun k => k / M) h
      simpa [amtxIndex, Nat.mul_comm, Nat.mul_add_div hM,
        Nat.div_eq_of_lt hj, Nat.div_eq_of_lt hj'] using hd
    subst i'
    exact ⟨rfl, Nat.add_left_cancel h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem amtx_index_unique_bounded {N M i j i' j' : ℕ}
    (_hi : i < N) (hj : j < M) (_hi' : i' < N) (hj' : j' < M) :
    amtxIndex M i j = amtxIndex M i' j' ↔ i = i' ∧ j = j' :=
  amtx_index_unique hj hj'

theorem amtx1Rel_singleValued (N M : ℕ) : SingleValued (amtx1Rel N M) := by
  intro xs a b ha hb
  funext p
  rcases p with ⟨i, j⟩
  by_cases hi : i < N
  · by_cases hj : j < M
    · exact (ha.2.1 i hi j hj).symm.trans (hb.2.1 i hi j hj)
    · exact (ha.2.2 i j (Or.inr (Nat.le_of_not_gt hj))).trans
        (hb.2.2 i j (Or.inr (Nat.le_of_not_gt hj))).symm
  · exact (ha.2.2 i j (Or.inl (Nat.le_of_not_gt hi))).trans
      (hb.2.2 i j (Or.inl (Nat.le_of_not_gt hi))).symm

theorem amtx1Rel_nonzero_bounded {N M : ℕ} {xs : List ℕ} {c : Matrix ℕ}
    (h : (xs, c) ∈ amtx1Rel N M) :
    mtxNonzero c ⊆ {p | p.1 < N ∧ p.2 < M} := by
  rintro ⟨i, j⟩ hc
  by_contra hout
  simp only [Set.mem_setOf_eq, not_and_or, not_lt] at hout
  exact hc (h.2.2 i j hout)

def amtxRel {α : Type} (N M : ℕ) (A : α → ℕ → Assn) :
    Set (List ℕ × Matrix α) :=
  relComp (amtx1Rel N M) (mtxRel (thePure A))

/-- The exact zero-preservation fragment needed to transfer the source's
bounded-support fact through a generic pure value relation. -/
def amtxPresZeroUnique {α : Type} [Zero α] (R : Set (ℕ × α)) : Prop :=
  ∀ a b, (a, b) ∈ R → (a = 0 ↔ b = 0)

theorem amtxRel_nonzero_bounded {α : Type} [Zero α]
    {N M : ℕ} {A : α → ℕ → Assn} {xs : List ℕ} {m : Matrix α}
    (hz : amtxPresZeroUnique (thePure A)) (h : (xs, m) ∈ amtxRel N M A) :
    mtxNonzero m ⊆ {p | p.1 < N ∧ p.2 < M} := by
  obtain ⟨c, hxc, hcm⟩ := h
  intro p hmp
  have hcp := hcm p p ⟨rfl, rfl⟩
  have hcnz : c p ≠ 0 := by
    intro hc0
    exact hmp ((hz (c p) (m p) hcp).mp hc0)
  exact amtx1Rel_nonzero_bounded hxc hcnz

def arrayMatrixAssn {α : Type} (N M : ℕ) (A : α → ℕ → Assn) :
    Matrix α → String → Assn :=
  hrComp arrayAssn (amtxRel N M A)

@[intf_of_assn] theorem arrayMatrixAssn_intf {α : Type} (N M : ℕ)
    (A : α → ℕ → Assn) :
    intfOfAssn (arrayMatrixAssn N M A) (MatrixI α) := trivial

/-! ## General tabulation and default initialization semantics -/

def amtxTabulateModel (N M : ℕ) (c : Matrix ℕ) : List ℕ :=
  List.ofFn fun k : Fin (N * M) => c (k / M, k % M)

def amtxDefaultMatrix (N M v : ℕ) : Matrix ℕ := fun p =>
  if p.1 < N ∧ p.2 < M then v else 0

def amtxDefaultModel (N M v : ℕ) : List ℕ :=
  List.replicate (N * M) v

def amtxDefaultIn (N M v : ℕ) (xs : List ℕ) : Option (List ℕ) :=
  if xs.length = N * M then some (List.replicate (N * M) v) else none

theorem amtxTabulateModel_refines {N M : ℕ} {c : Matrix ℕ}
    (hz : ∀ i j, N ≤ i ∨ M ≤ j → c (i, j) = 0) :
    (amtxTabulateModel N M c, c) ∈ amtx1Rel N M := by
  refine ⟨by simp [amtxTabulateModel], ?_, hz⟩
  intro i hi j hj
  have hk : amtxIndex M i j < N * M := amtx_index_bound hi hj
  rw [getElem!_pos _ _ (by simpa [amtxTabulateModel] using hk)]
  simp only [amtxTabulateModel, List.getElem_ofFn]
  have hM : 0 < M := Nat.zero_lt_of_lt hj
  simp [amtxIndex, Nat.mul_comm, Nat.mul_add_div hM,
    Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]

theorem amtxDefaultModel_refines (N M v : ℕ) :
    (amtxDefaultModel N M v, amtxDefaultMatrix N M v) ∈ amtx1Rel N M := by
  refine ⟨by simp [amtxDefaultModel], ?_, ?_⟩
  · intro i hi j hj
    have hk := amtx_index_bound hi hj
    rw [getElem!_pos _ _ (by simpa [amtxDefaultModel] using hk)]
    simp [amtxDefaultModel, amtxDefaultMatrix, hi, hj]
  · intro i j hout
    have hnot : ¬(i < N ∧ j < M) := by omega
    simp [amtxDefaultMatrix, hnot]

theorem amtxDefaultIn_refines {N M v : ℕ} {xs ys : List ℕ}
    (h : amtxDefaultIn N M v xs = some ys) :
    (ys, amtxDefaultMatrix N M v) ∈ amtx1Rel N M := by
  simp only [amtxDefaultIn] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst ys
    exact amtxDefaultModel_refines N M v
  · contradiction

/-! ## Functional get/set and square interface refinements -/

def amtxGet (M : ℕ) (xs : List ℕ) (p : ℕ × ℕ) : Option ℕ :=
  if amtxIndex M p.1 p.2 < xs.length then
    some xs[amtxIndex M p.1 p.2]!
  else none

def amtxSet (M : ℕ) (xs : List ℕ) (p : ℕ × ℕ) (v : ℕ) : Option (List ℕ) :=
  if amtxIndex M p.1 p.2 < xs.length then
    some (xs.set (amtxIndex M p.1 p.2) v)
  else none

private theorem getElem!_set_amtx (xs : List ℕ) (i j v : ℕ)
    (hj : j < xs.length) :
    (xs.set i v)[j]! = if j = i then v else xs[j]! := by
  induction xs generalizing i j with
  | nil => simp at hj
  | cons x xs ih =>
      cases i with
      | zero => cases j <;> simp
      | succ i =>
          cases j with
          | zero => simp
          | succ j => simpa using ih i j (by simpa using hj)

theorem amtxGet_refines {N M : ℕ} {xs : List ℕ} {c : Matrix ℕ}
    (h : (xs, c) ∈ amtx1Rel N M) {i j : ℕ} (hi : i < N) (hj : j < M) :
    amtxGet M xs (i, j) = some (c (i, j)) := by
  have hk : amtxIndex M i j < xs.length := by
    rw [h.1]
    exact amtx_index_bound hi hj
  rw [amtxGet, if_pos hk]
  congr 1
  exact h.2.1 i hi j hj

theorem amtxSet_refines {N M : ℕ} {xs : List ℕ} {c : Matrix ℕ}
    (h : (xs, c) ∈ amtx1Rel N M) {i j v : ℕ} (hi : i < N) (hj : j < M) :
    ∃ ys, amtxSet M xs (i, j) v = some ys ∧
      (ys, Function.update c (i, j) v) ∈ amtx1Rel N M := by
  have hk : amtxIndex M i j < xs.length := by
    rw [h.1]
    exact amtx_index_bound hi hj
  refine ⟨xs.set (amtxIndex M i j) v, by simp [amtxSet, hk], by simp [h.1], ?_, ?_⟩
  · intro i' hi' j' hj'
    rw [getElem!_set_amtx xs _ _ v (by
      rw [h.1]; exact amtx_index_bound hi' hj')]
    by_cases hp : (i', j') = (i, j)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      simp [Function.update]
    · have hidx : amtxIndex M i' j' ≠ amtxIndex M i j := by
        intro heq
        exact hp (Prod.ext (amtx_index_unique hj' hj |>.mp heq).1
          (amtx_index_unique hj' hj |>.mp heq).2)
      simp [hidx, Function.update, hp, h.2.1 i' hi' j' hj']
  · intro i' j' hout
    have hp : (i', j') ≠ (i, j) := by
      intro heq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      omega
    simp only [Function.update_apply, if_neg hp]
    exact h.2.2 i' j' hout

noncomputable def amtxGetOp (M : ℕ) (xs : List ℕ) (p : ℕ × ℕ) :
    NRest ℕ ECost :=
  match amtxGet M xs p with
  | some v => NRest.returnT v
  | none => NRest.fail

noncomputable def amtxSetOp (M : ℕ) (xs : List ℕ) (p : ℕ × ℕ) (v : ℕ) :
    NRest (List ℕ) ECost :=
  match amtxSet M xs p v with
  | some ys => NRest.returnT ys
  | none => NRest.fail

@[sepref_fref_thms] theorem amtxGetOp_refines {α : Type} (N M : ℕ)
    (A : α → ℕ → Assn) :
    (amtxGetOp M, op_mtx_get α) ∈
      fref (fun _ : Matrix α => True) (amtxRel N M A)
        (fun _ => fref (fun p : ℕ × ℕ => p.1 < N ∧ p.2 < M)
          (Set.diagonal ℕ ×ᵣ Set.diagonal ℕ)
          (fun _ => NRest.nrestRel (thePure A))) := by
  intro xs m _ hrel p q hp hpq
  obtain ⟨c, hxc, hcm⟩ := hrel
  rcases p with ⟨i, j⟩
  rcases q with ⟨i', j'⟩
  obtain ⟨hii, hjj⟩ := hpq
  change i = i' at hii
  change j = j' at hjj
  subst i'
  subst j'
  have hg := amtxGet_refines hxc hp.1 hp.2
  simp [amtxGetOp, hg, op_mtx_get]
  exact NRest.param_returnT (hcm (i, j) (i, j) ⟨rfl, rfl⟩)

@[sepref_fref_thms] theorem amtxSetOp_refines {α : Type} (N M : ℕ)
    (A : α → ℕ → Assn) :
    (amtxSetOp M, op_mtx_set α) ∈
      fref (fun _ : Matrix α => True) (amtxRel N M A)
        (fun _ => fref (fun p : ℕ × ℕ => p.1 < N ∧ p.2 < M)
          (Set.diagonal ℕ ×ᵣ Set.diagonal ℕ)
          (fun _ => thePure A →ᵣ NRest.nrestRel (amtxRel N M A))) := by
  intro xs m _ hrel p q hp hpq v a hva
  obtain ⟨c, hxc, hcm⟩ := hrel
  rcases p with ⟨i, j⟩
  rcases q with ⟨i', j'⟩
  obtain ⟨hii, hjj⟩ := hpq
  change i = i' at hii
  change j = j' at hjj
  subst i'
  subst j'
  change (xs, c) ∈ amtx1Rel N M at hxc
  change (c, m) ∈ mtxRel (thePure A) at hcm
  obtain ⟨ys, hys, hyc⟩ := amtxSet_refines hxc hp.1 hp.2
  change amtxSet M xs (i, j) v = some ys at hys
  change (ys, Function.update c (i, j) v) ∈ amtx1Rel N M at hyc
  change (amtxSetOp M xs (i, j) v,
    op_mtx_set α m (i, j) a) ∈ NRest.nrestRel (amtxRel N M A)
  rw [show amtxSetOp M xs (i, j) v = NRest.returnT ys by
    simp [amtxSetOp, hys]]
  simp only [op_mtx_set]
  apply NRest.param_returnT
  refine ⟨Function.update c (i, j) v, hyc, ?_⟩
  intro r s hrs
  rcases r with ⟨x, y⟩
  rcases s with ⟨x', y'⟩
  obtain ⟨hxx, hyy⟩ := hrs
  change x = x' at hxx
  change y = y' at hyy
  subst x'
  subst y'
  by_cases heq : (x, y) = (i, j)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    simpa using hva
  · simp [Function.update, heq]
    exact hcm (x, y) (x, y) ⟨rfl, rfl⟩

/-- The source specializes these rules to square matrices. -/
@[sepref_fref_thms] theorem amtxSquareGetOp_refines {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) :
    (amtxGetOp N, op_mtx_get α) ∈
      fref (fun _ : Matrix α => True) (amtxRel N N A)
        (fun _ => fref (fun p : ℕ × ℕ => p.1 < N ∧ p.2 < N)
          (Set.diagonal ℕ ×ᵣ Set.diagonal ℕ)
          (fun _ => NRest.nrestRel (thePure A))) :=
  amtxGetOp_refines N N A

@[sepref_fref_thms] theorem amtxSquareSetOp_refines {α : Type} (N : ℕ)
    (A : α → ℕ → Assn) :
    (amtxSetOp N, op_mtx_set α) ∈
      fref (fun _ : Matrix α => True) (amtxRel N N A)
        (fun _ => fref (fun p : ℕ × ℕ => p.1 < N ∧ p.2 < N)
          (Set.diagonal ℕ ×ᵣ Set.diagonal ℕ)
          (fun _ => thePure A →ᵣ NRest.nrestRel (amtxRel N N A))) :=
  amtxSetOp_refines N N A

/-- General tabulation refines matrix `new` semantically.  It deliberately
has no executable rule: evaluating `c` at runtime would require the source's
higher-order heap callback. -/
noncomputable def amtxTabulateOp (N M : ℕ) (c : Matrix ℕ) :
    NRest (List ℕ) ECost :=
  NRest.returnT (amtxTabulateModel N M c)

@[sepref_fref_thms] theorem amtxTabulateOp_refines_nat (N M : ℕ) :
    (amtxTabulateOp N M, op_mtx_new ℕ) ∈
      fref (fun c : Matrix ℕ =>
          mtxNonzero c ⊆ {p | p.1 < N ∧ p.2 < M})
        (Set.diagonal (Matrix ℕ))
        (fun _ => NRest.nrestRel (amtx1Rel N M)) := by
  intro c c' hc hcc
  change c = c' at hcc
  subst c'
  apply NRest.param_returnT
  apply amtxTabulateModel_refines
  intro i j hout
  by_contra hnz
  have hb : i < N ∧ j < M := hc (show (i, j) ∈ mtxNonzero c from hnz)
  exact hout.elim (fun hi => (Nat.not_lt_of_ge hi) hb.1)
    (fun hj => (Nat.not_lt_of_ge hj) hb.2)

/-- Public source-facing tabulation/new rule.  The source callback's concrete
`Nat` matrix is related pointwise to the abstract matrix by the pure value
relation.  Zero uniqueness transports the abstract bounded-support
precondition back to the concrete callback, which is exactly what the
row-major tabulation proof needs. -/
@[sepref_fref_thms] theorem amtxTabulateOp_refines {α : Type} [Zero α]
    (N M : ℕ) (A : α → ℕ → Assn)
    (hz : amtxPresZeroUnique (thePure A)) :
    (amtxTabulateOp N M, op_mtx_new α) ∈
      fref (fun m : Matrix α =>
          mtxNonzero m ⊆ {p | p.1 < N ∧ p.2 < M})
        (mtxRel (thePure A))
        (fun _ => NRest.nrestRel (amtxRel N M A)) := by
  intro c m hm hcm
  simp only [amtxTabulateOp, op_mtx_new]
  apply NRest.param_returnT
  refine ⟨c, ?_, hcm⟩
  apply amtxTabulateModel_refines
  intro i j hout
  by_contra hcnz
  have hrel := hcm (i, j) (i, j) ⟨rfl, rfl⟩
  have hmnz : m (i, j) ≠ 0 := by
    intro hm0
    exact hcnz ((hz (c (i, j)) (m (i, j)) hrel).mpr hm0)
  have hb : i < N ∧ j < M := hm
    (show (i, j) ∈ mtxNonzero m from hmnz)
  exact hout.elim (fun hi => (Nat.not_lt_of_ge hi) hb.1)
    (fun hj => (Nat.not_lt_of_ge hj) hb.2)

/-! ## Exact executable caller-owned operations -/

noncomputable def amtxDefaultRaw (xs : List ℕ) (v : ℕ) :
    NRest (List ℕ) ECost :=
  mop_array_fill xs v

noncomputable def amtxGetRaw (M : ℕ) (xs : List ℕ) (i j : ℕ) :
    NRest ℕ ECost :=
  NRest.bindT (mopBinop .mul i M) fun row =>
    NRest.bindT (mopBinop .add row j) fun idx =>
      mopAget xs idx

noncomputable def amtxSetRaw (M : ℕ) (xs : List ℕ) (i j v : ℕ) :
    NRest (List ℕ) ECost :=
  NRest.bindT (mopBinop .mul i M) fun row =>
    NRest.bindT (mopBinop .add row j) fun idx =>
      mopAset xs idx v

noncomputable def amtxDefaultCost (N M : ℕ) : ECost :=
  fillCost (N * M)

noncomputable def amtxGetCost : ECost :=
  irUnit Currency.mul + irUnit Currency.add + irUnit Currency.aget

noncomputable def amtxSetCost : ECost :=
  irUnit Currency.mul + irUnit Currency.add + irUnit Currency.aset

noncomputable def amtxDefaultExecSpec (xs : List ℕ) (v : ℕ) :
    NRest (List ℕ) ECost :=
  NRest.consume (NRest.returnT (List.replicate xs.length v))
    (fillCost xs.length)

noncomputable def amtxGetExecSpec (M : ℕ) (xs : List ℕ) (i j : ℕ) :
    NRest ℕ ECost :=
  NRest.consume (NRest.returnT xs[amtxIndex M i j]!) amtxGetCost

noncomputable def amtxSetExecSpec (M : ℕ) (xs : List ℕ) (i j v : ℕ) :
    NRest (List ℕ) ECost :=
  NRest.consume (NRest.returnT (xs.set (amtxIndex M i j) v)) amtxSetCost

theorem amtxDefaultRaw_eq (xs : List ℕ) (v : ℕ) :
    amtxDefaultRaw xs v = amtxDefaultExecSpec xs v := rfl

theorem amtxGetRaw_eq (M : ℕ) (xs : List ℕ) (i j : ℕ)
    (hk : amtxIndex M i j < xs.length) :
    amtxGetRaw M xs i j = amtxGetExecSpec M xs i j := by
  have hk' : i * M + j < xs.length := by simpa [amtxIndex] using hk
  simp [amtxGetRaw, amtxGetExecSpec, amtxIndex, amtxGetCost,
    mopBinop_def, mopAget_def, NRest.assert_pos hk',
    NRest.bindT_consume NRest.addSupContinuousB_acost,
    NRest.consume_consume, binopCurrency_mul, binopCurrency_add]
  ac_rfl

theorem amtxSetRaw_eq (M : ℕ) (xs : List ℕ) (i j v : ℕ)
    (hk : amtxIndex M i j < xs.length) :
    amtxSetRaw M xs i j v = amtxSetExecSpec M xs i j v := by
  have hk' : i * M + j < xs.length := by simpa [amtxIndex] using hk
  simp [amtxSetRaw, amtxSetExecSpec, amtxIndex, amtxSetCost,
    mopBinop_def, mopAset_def, NRest.assert_pos hk',
    NRest.bindT_consume NRest.addSupContinuousB_acost,
    NRest.consume_consume, binopCurrency_mul, binopCurrency_add]
  ac_rfl

sepref_synth amtxDefaultSynth (idx A value one n : String)
    (xs : List ℕ) (v : ℕ) :
  hnRefine (junkCell idx ∗ hnCtxt arrayAssn xs A ∗ hnCtxt natAssn v value ∗
      hnCtxt natAssn xs.length n ∗ hnCtxt natAssn 1 one)
    _ _ A arrayAssn (amtxDefaultRaw xs v)

sepref_synth amtxGetSynth (A rows row col prod idx out : String)
    (M : ℕ) (xs : List ℕ) (i j : ℕ) :
  hnRefine (hnCtxt arrayAssn xs A ∗ hnCtxt natAssn M rows ∗
      hnCtxt natAssn i row ∗ hnCtxt natAssn j col ∗
      junkCell prod ∗ junkCell idx ∗ junkCell out)
    _ _ out natAssn (amtxGetRaw M xs i j)

sepref_synth amtxSetSynth (A rows row col value prod idx : String)
    (M : ℕ) (xs : List ℕ) (i j v : ℕ) :
  hnRefine (hnCtxt arrayAssn xs A ∗ hnCtxt natAssn M rows ∗
      hnCtxt natAssn i row ∗ hnCtxt natAssn j col ∗
      hnCtxt natAssn v value ∗ junkCell prod ∗ junkCell idx)
    _ _ A arrayAssn (amtxSetRaw M xs i j v)

def amtxDefaultCom := fillCom

def amtxGetCom (A rows row col prod idx out : String) : Com :=
  (Com.binop .mul prod row rows).seq
    ((Com.binop .add idx prod col).seq (Com.aget out A idx))

def amtxSetCom (A rows row col value prod idx : String) : Com :=
  (Com.binop .mul prod row rows).seq
    ((Com.binop .add idx prod col).seq (Com.aset A idx value))

@[sepref_fr_rules] theorem amtxDefault_exec_hnr
    (idx A value one n : String) (xs : List ℕ) (v : ℕ) :
    hnRefine (junkCell idx ∗ hnCtxt arrayAssn xs A ∗
        hnCtxt natAssn v value ∗ hnCtxt natAssn xs.length n ∗
        hnCtxt natAssn 1 one)
      (amtxDefaultCom idx A value one n)
      (junkCell idx ∗ hnCtxt natAssn v value ∗
        hnCtxt natAssn xs.length n ∗ hnCtxt natAssn 1 one)
      A arrayAssn (amtxDefaultExecSpec xs v) := by
  rw [← amtxDefaultRaw_eq xs v]
  exact amtxDefaultSynth idx A value one n xs v

@[sepref_fr_rules] theorem amtxGet_exec_hnr
    (A rows row col prod idx out : String)
    (M : ℕ) (xs : List ℕ) (i j : ℕ)
    (hk : amtxIndex M i j < xs.length) :
    hnRefine (hnCtxt arrayAssn xs A ∗ hnCtxt natAssn M rows ∗
        hnCtxt natAssn i row ∗ hnCtxt natAssn j col ∗
        junkCell prod ∗ junkCell idx ∗ junkCell out)
      (amtxGetCom A rows row col prod idx out)
      (hnCtxt arrayAssn xs A ∗ junkCell idx ∗ junkCell prod ∗
        hnCtxt natAssn j col ∗ hnCtxt natAssn i row ∗
        hnCtxt natAssn M rows)
      out natAssn (amtxGetExecSpec M xs i j) := by
  rw [← amtxGetRaw_eq M xs i j hk]
  simpa only [amtxGetCom] using
    (amtxGetSynth A rows row col prod idx out M xs i j)

@[sepref_fr_rules] theorem amtxSet_exec_hnr
    (A rows row col value prod idx : String)
    (M : ℕ) (xs : List ℕ) (i j v : ℕ)
    (hk : amtxIndex M i j < xs.length) :
    hnRefine (hnCtxt arrayAssn xs A ∗ hnCtxt natAssn M rows ∗
        hnCtxt natAssn i row ∗ hnCtxt natAssn j col ∗
        hnCtxt natAssn v value ∗ junkCell prod ∗ junkCell idx)
      (amtxSetCom A rows row col value prod idx)
      (junkCell idx ∗ hnCtxt natAssn v value ∗ junkCell prod ∗
        hnCtxt natAssn j col ∗ hnCtxt natAssn i row ∗
        hnCtxt natAssn M rows)
      A arrayAssn (amtxSetExecSpec M xs i j v) := by
  rw [← amtxSetRaw_eq M xs i j v hk]
  simpa only [amtxSetCom] using
    (amtxSetSynth A rows row col value prod idx M xs i j v)

/-! ## Whole-state executable bridges -/

theorem amtxDefaultExecSpec_refines {N M v : ℕ} {xs : List ℕ}
    (hlen : xs.length = N * M) :
    amtxDefaultExecSpec xs v = NRest.consume
        (NRest.returnT (List.replicate (N * M) v)) (amtxDefaultCost N M) ∧
      (List.replicate (N * M) v, amtxDefaultMatrix N M v) ∈
        amtx1Rel N M := by
  exact ⟨by simp [amtxDefaultExecSpec, amtxDefaultCost, hlen],
    amtxDefaultModel_refines N M v⟩

theorem amtxGetExecSpec_refines {N M : ℕ} {xs : List ℕ} {c : Matrix ℕ}
    (h : (xs, c) ∈ amtx1Rel N M) {i j : ℕ} (hi : i < N) (hj : j < M) :
    amtxGetExecSpec M xs i j =
      NRest.consume (NRest.returnT (c (i, j))) amtxGetCost := by
  have hv := h.2.1 i hi j hj
  simp [amtxGetExecSpec, hv]

theorem amtxSetExecSpec_refines {N M : ℕ} {xs : List ℕ} {c : Matrix ℕ}
    (h : (xs, c) ∈ amtx1Rel N M) {i j v : ℕ} (hi : i < N) (hj : j < M) :
    amtxSetExecSpec M xs i j v = NRest.consume
        (NRest.returnT (xs.set (amtxIndex M i j) v)) amtxSetCost ∧
      (xs.set (amtxIndex M i j) v, Function.update c (i, j) v) ∈
        amtx1Rel N M := by
  refine ⟨rfl, ?_⟩
  obtain ⟨ys, hys, hyrel⟩ := amtxSet_refines h hi hj
  have hk : amtxIndex M i j < xs.length := by
    rw [h.1]
    exact amtx_index_bound hi hj
  have : ys = xs.set (amtxIndex M i j) v := by
    symm
    simpa [amtxSet, hk] using hys
  subst ys
  exact hyrel

/-! Allocation-backed tabulation/default creation, `imp_for'`'s heap
callback, deallocation, and function-pointer export are unsupported.  The
general tabulation theorem is semantic only; `amtxDefault_exec_hnr` is the
caller-owned initialization boundary.  No zero-cost placeholder is emitted. -/

/-! ## Rectangular regression, provenance, and gates -/

def amtxRegressionMatrix : Matrix ℕ := fun p =>
  if p.1 < 2 ∧ p.2 < 3 then 10 * p.1 + p.2 else 0

def amtxRegressionArray : List ℕ :=
  amtxTabulateModel 2 3 amtxRegressionMatrix

def amtxRegressionSet : Option (List ℕ) :=
  amtxSet 3 amtxRegressionArray (1, 1) 99

#guard amtxRegressionArray.length = 6
#guard amtxGet 3 amtxRegressionArray (1, 2) = some 12
#guard (amtxRegressionSet.bind (fun xs => amtxGet 3 xs (1, 1))) = some 99
#guard amtxRegressionMatrix (2, 0) = 0

def amtxSourceTabulateBound (N M : ℕ) : ℕ := 3 * N * M + 3
def amtxSourceDefaultBound (N M : ℕ) : ℕ := N * M + 1
def amtxSourceGetBound : ℕ := 1
def amtxSourceSetBound : ℕ := 1

#guard amtxSourceTabulateBound 2 3 = 21
#guard amtxSourceDefaultBound 2 3 = 7
#guard amtxSourceGetBound = 1
#guard amtxSourceSetBound = 1

#guard amtxDefaultCom "idx" "A" "value" "one" "n" =
  fillCom "idx" "A" "value" "one" "n"
#guard amtxGetCom "A" "rows" "row" "col" "prod" "idx" "out" =
  (Com.binop .mul "prod" "row" "rows").seq
    ((Com.binop .add "idx" "prod" "col").seq (Com.aget "out" "A" "idx"))
#guard amtxSetCom "A" "rows" "row" "col" "value" "prod" "idx" =
  (Com.binop .mul "prod" "row" "rows").seq
    ((Com.binop .add "idx" "prod" "col").seq (Com.aset "A" "idx" "value"))

theorem amtxDefaultCost_aset : (amtxDefaultCost 2 3).toFun Currency.aset = 6 := by decide +kernel
theorem amtxDefaultCost_add : (amtxDefaultCost 2 3).toFun Currency.add = 6 := by decide +kernel
theorem amtxDefaultCost_while : (amtxDefaultCost 2 3).toFun Currency.«while» = 7 := by decide +kernel
theorem amtxDefaultCost_const : (amtxDefaultCost 2 3).toFun Currency.const = 1 := by decide +kernel
theorem amtxGetCost_mul : amtxGetCost.toFun Currency.mul = 1 := by decide +kernel
theorem amtxGetCost_add : amtxGetCost.toFun Currency.add = 1 := by decide +kernel
theorem amtxGetCost_aget : amtxGetCost.toFun Currency.aget = 1 := by decide +kernel
theorem amtxSetCost_mul : amtxSetCost.toFun Currency.mul = 1 := by decide +kernel
theorem amtxSetCost_add : amtxSetCost.toFun Currency.add = 1 := by decide +kernel
theorem amtxSetCost_aset : amtxSetCost.toFun Currency.aset = 1 := by decide +kernel

private theorem ecost_ne_zero_of_pos_amtx (C : ECost) (c : String)
    (h : 0 < C.toFun c) : C ≠ 0 := by
  intro hz
  rw [hz] at h
  simp at h

theorem amtxDefaultCost_ne_zero : amtxDefaultCost 2 3 ≠ 0 :=
  ecost_ne_zero_of_pos_amtx _ Currency.aset (by simp [amtxDefaultCost_aset])
theorem amtxGetCost_ne_zero : amtxGetCost ≠ 0 :=
  ecost_ne_zero_of_pos_amtx _ Currency.aget (by simp [amtxGetCost_aget])
theorem amtxSetCost_ne_zero : amtxSetCost ≠ 0 :=
  ecost_ne_zero_of_pos_amtx _ Currency.aset (by simp [amtxSetCost_aset])

run_cmd do
  let frefs ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``amtxGetOp_refines, ``amtxSetOp_refines,
      ``amtxSquareGetOp_refines, ``amtxSquareSetOp_refines,
      ``amtxTabulateOp_refines, ``amtxTabulateOp_refines_nat] do
    unless frefs.contains n do
      throwError "array-matrix source rule missing from DB: {n}"
  let frules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fr_rules
  for n in #[``amtxDefault_exec_hnr, ``amtxGet_exec_hnr,
      ``amtxSet_exec_hnr] do
    unless frules.contains n do
      throwError "array-matrix executable rule missing from DB: {n}"

/-! Every registered executable operation has a positive exact vector cost.
Unsupported allocation/callback operations have no rule and no invented
budget. -/

/-! ## Kernel-three gates -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.amtx1Rel_singleValued' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms amtx1Rel_singleValued

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.amtxSetOp_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amtxSetOp_refines

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.amtxGet_exec_hnr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amtxGet_exec_hnr

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.amtxTabulateOp_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amtxTabulateOp_refines

end Lax13Proofs.Refine.Sepref.Iicf
