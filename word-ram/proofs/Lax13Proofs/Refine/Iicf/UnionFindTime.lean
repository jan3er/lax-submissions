import Lax13Proofs.Refine.Iicf.IicfArray
import Lax13Proofs.Refine.Iicf.UnionFindAbstract

/-!
# Timed loop-form union-find

This module ports the executable union-find layer from the pinned Sepreftime
sources.  The local IR has no allocation and no recursive commands, so the
implementation owns two caller-provided arrays and uses bounded loops.

Source accounting:

| source | range | disposition |
|---|---:|---|
| `UnionFind_Impl.thy` | 7--40 | landed below as the closed-form MOP operations |
| same | 44--86 | open: the implementation interface is completed after find/union land |
| `Union_Find_Time.thy` | 651--666 | landed: two-array representation `ufAssn` |
| same | 667--703 | landed: no-allocation `ufInit` from two `junkArrayOfLen` buffers |
| same | 707--844 | open: bounded root search and compression loops |
| same | 850--897 | open: comparison |
| same | 899--1174 | open: union-by-size and both rank-preservation branches |
| same | 1177--1204 | open: final interface interpretation |

The initialization loop and its price are synthesized from primitive array
writes.  Thus its cost is a vector over the actual IR currencies, rather than
the scalar source constant.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf.UnionFindTime

open Ir NRest
open Lax13Proofs.Refine.Iicf.UnionFind

set_option autoImplicit true

/-! ## MOP surface -/

noncomputable def mopPerInit (n : ℕ) : NRest (Per ℕ) ECost :=
  NRest.returnT (perInitNat n)

noncomputable def mopPerCompare (R : Per ℕ) (a b : ℕ) : NRest Bool ECost :=
  by
    classical
    exact NRest.returnT (decide (perCompare R a b))

noncomputable def mopPerUnion (R : Per ℕ) (a b : ℕ) : NRest (Per ℕ) ECost :=
  NRest.returnT (perUnion R a b)

/-! ## Representation -/

abbrev UfArrays := List ℕ × List ℕ

def UfArrays.Wf (u : UfArrays) : Prop :=
  ufaInvar u.1 ∧ u.1.length = u.2.length ∧ rankInvar u.1 u.2

def ufAssn (R : Per ℕ) (c : String × String) : Assn :=
  ∃ᵃ u, ⌜UfArrays.Wf u ∧ ufaAlpha u.1 = R⌝ ∗
    (arrayAssn u.1 c.1 ∗ arrayAssn u.2 c.2)

theorem ufAssn_unfold (R : Per ℕ) (c : String × String) :
    ufAssn R c = ∃ᵃ u, ⌜UfArrays.Wf u ∧ ufaAlpha u.1 = R⌝ ∗
      (arrayAssn u.1 c.1 ∗ arrayAssn u.2 c.2) := rfl

/-! ## Parent-range initialization loop -/

def rangeFilled : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | j + 1, xs => (rangeFilled j xs).set j j

@[simp] theorem rangeFilled_zero (xs : List ℕ) : rangeFilled 0 xs = xs := rfl

theorem rangeFilled_succ (j : ℕ) (xs : List ℕ) :
    rangeFilled (j + 1) xs = (rangeFilled j xs).set j j := rfl

@[simp] theorem rangeFilled_length (j : ℕ) (xs : List ℕ) :
    (rangeFilled j xs).length = xs.length := by
  induction j with
  | zero => rfl
  | succ j ih => simp [rangeFilled_succ, ih]

theorem rangeFilled_get (xs : List ℕ) :
    ∀ {j k : ℕ} (hk : k < j) (hj : j ≤ xs.length),
      (rangeFilled j xs)[k]'(by rw [rangeFilled_length]; omega) = k := by
  intro j
  induction j with
  | zero => intro k hk; omega
  | succ j ih =>
      intro k hk hj
      simp only [rangeFilled_succ, List.getElem_set]
      by_cases hkj : k = j
      · simp [hkj]
      · rw [if_neg (Ne.symm hkj)]
        exact ih (by omega) (by omega)

theorem rangeFilled_all (xs : List ℕ) : rangeFilled xs.length xs = List.range xs.length := by
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    rw [rangeFilled_get xs (by simpa using hj₂) (le_refl _)]
    exact (List.getElem_range hj₂).symm

abbrev RangeState := ℕ × (ℕ × List ℕ)

def rangeI (n : ℕ) (s : RangeState) : Prop :=
  s.2.2.length = n ∧ s.1 ≤ n ∧ s.2.1 = s.1

def rangeB (n : ℕ) (s : RangeState) : Bool := decide (s.1 < n)

def rangeStep (s : RangeState) : RangeState :=
  (s.1 + 1, (s.1 + 1, s.2.2.set s.1 s.2.1))

noncomputable def rangeF (s : RangeState) : NRest RangeState ECost :=
  NRest.bindT (mopAset s.2.2 s.1 s.2.1) fun xs' =>
    NRest.bindT (mopBinop Imp.Bop.add s.1 1) fun j' =>
      NRest.bindT (mopBinop Imp.Bop.add s.2.1 1) fun v' =>
        NRest.bindT (mopPair v' xs') fun tail =>
          mopPair j' tail

noncomputable def rangeStepCost : ECost :=
  irUnit Currency.aset + irUnit Currency.add + irUnit Currency.add +
    irUnit Currency.skip + irUnit Currency.skip

theorem rangeF_eq (s : RangeState) (h : s.1 < s.2.2.length) (heq : s.2.1 = s.1) :
    rangeF s = NRest.consume (NRest.returnT (rangeStep s)) rangeStepCost := by
  show NRest.bindT (mopAset s.2.2 s.1 s.2.1) _ = _
  simp only [mopAset_def, mopBinop_def, mopPair_def, NRest.assert_pos h,
    NRest.returnT_bindT, bindT_unit, NRest.consume_consume, rangeStep,
    rangeStepCost, Imp.Bop.apply_add, binopCurrency_add]
  rw [heq]
  congr 1
  ac_rfl

def rangeV (n : ℕ) : RangeState → ℕ := fun s => n - s.1

theorem range_variant (n : ℕ) : LOOP_VARIANT (rangeI n) (rangeB n) rangeF (rangeV n) := by
  intro s s' hI hb hle
  have hlt : s.1 < n := by simpa [rangeB] using hb
  have hidx : s.1 < s.2.2.length := by rw [hI.1]; exact hlt
  rw [rangeF_eq s hidx hI.2.2, NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hs' : s' = rangeStep s := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  subst s'
  show n - (s.1 + 1) < n - s.1
  omega

noncomputable def rangeProg (xs : List ℕ) : NRest RangeState ECost :=
  NRest.bindT (mopConstN 0) fun z =>
    NRest.bindT (mopConstN 0) fun v =>
      NRest.bindT (mopPair v xs) fun tail =>
        NRest.bindT (mopPair z tail) fun s₀ =>
          irWhileIT (rangeI xs.length) (rangeB xs.length) rangeF s₀

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
sepref_synth rangeLoop (i v A one n : String) (xs : List ℕ)
    (hv : LOOP_VARIANT (rangeI xs.length) (rangeB xs.length) rangeF (rangeV xs.length)) :
  hnRefine (junkCell i ∗ junkCell v ∗ hnCtxt arrayAssn xs A ∗ hnCtxt natAssn 1 one ∗
      hnCtxt natAssn xs.length n)
    _ _ (i, (v, A)) (natAssn ×ₐ (natAssn ×ₐ arrayAssn)) (rangeProg xs)

noncomputable def rangeRest (n j : ℕ) : ECost :=
  (n - j) • rangeStepCost + (n - j + 1) • irUnit Currency.«while»

theorem rangeLoop_value (n : ℕ) (xs : List ℕ) (hlen : xs.length = n) :
    ∀ (m j : ℕ), n - j ≤ m → j ≤ n →
      irWhileIT (rangeI n) (rangeB n) rangeF (j, (j, rangeFilled j xs)) =
        NRest.consume (NRest.returnT (n, (n, rangeFilled n xs))) (rangeRest n j) := by
  intro m
  induction m with
  | zero =>
      intro j hm hj
      have hjn : j = n := by omega
      have hI : rangeI n (j, (j, rangeFilled j xs)) := by
        exact ⟨by simp [hlen], hj, rfl⟩
      have hb : rangeB n (j, (j, rangeFilled j xs)) = false := by
        simp [rangeB, hjn]
      rw [irWhileIT_of_false hI hb, hjn]
      congr 1
      simp [rangeRest]
  | succ m ih =>
      intro j hm hj
      have hI : rangeI n (j, (j, rangeFilled j xs)) := by
        exact ⟨by simp [hlen], hj, rfl⟩
      by_cases hjn : j = n
      · have hb : rangeB n (j, (j, rangeFilled j xs)) = false := by simp [rangeB, hjn]
        rw [irWhileIT_of_false hI hb, hjn]
        congr 1
        simp [rangeRest]
      · have hjlt : j < n := by omega
        have hb : rangeB n (j, (j, rangeFilled j xs)) = true := by simp [rangeB, hjlt]
        have hidx : j < (rangeFilled j xs).length := by simpa [hlen] using hjlt
        rw [irWhileIT_of_true hI hb, rangeF_eq _ hidx rfl]
        simp only [rangeStep]
        rw [← rangeFilled_succ]
        rw [
          bindT_unit, ih (j + 1) (by omega) (by omega), NRest.consume_consume,
          NRest.consume_consume]
        congr 1
        have hd : n - j = (n - (j + 1)) + 1 := by omega
        simp only [rangeRest, hd, succ_nsmul]
        abel

noncomputable def rangeCost (n : ℕ) : ECost :=
  2 • irUnit Currency.const + 2 • irUnit Currency.skip +
    (n • rangeStepCost + (n + 1) • irUnit Currency.«while»)

theorem rangeProg_value (xs : List ℕ) :
    rangeProg xs = NRest.consume (NRest.returnT (xs.length, (xs.length, List.range xs.length)))
      (rangeCost xs.length) := by
  have h := rangeLoop_value xs.length xs rfl xs.length 0 (by omega) (by omega)
  rw [rangeFilled_zero, rangeFilled_all] at h
  show NRest.bindT (mopConstN 0) _ = _
  simp only [mopConstN_def, mopPair_def, bindT_unit]
  rw [h]
  simp only [NRest.consume_consume]
  congr 1
  simp [rangeCost, rangeRest]
  abel

def rangeCom (i v A one n : String) : Com :=
  .seq (.const i 0)
    (.seq (.const v 0)
      (.seq .skip (.seq .skip
        (.while (.lt (.cell i) (.cell n))
          (.seq (.aset A i v)
            (.seq (.binop .add i i one)
              (.seq (.binop .add v v one) (.seq .skip .skip))))))))

@[sepref_fr_rules]
theorem hnr_range_init (i v A one n : String) (xs : List ℕ) :
    hnRefine (junkCell i ∗ junkCell v ∗ hnCtxt arrayAssn xs A ∗ hnCtxt natAssn 1 one ∗
        hnCtxt natAssn xs.length n)
      (rangeCom i v A one n)
      (junkCell i ∗ junkCell v ∗ hnCtxt natAssn 1 one ∗ hnCtxt natAssn xs.length n)
      A arrayAssn
      (NRest.consume (NRest.returnT (List.range xs.length)) (rangeCost xs.length)) := by
  have h := rangeLoop i v A one n xs (range_variant xs.length)
  rw [rangeProg_value] at h
  refine hnRefine_res_cast' h ?_
  simp only [hnCtxt_def, prodAssn_apply]
  refine entails_trans
    (Q := (natAssn xs.length i ∗ natAssn xs.length v) ∗
      ((natAssn 1 one ∗ natAssn xs.length n) ∗ arrayAssn (List.range xs.length) A))
    (entails_of_eq ?_) ?_
  · ac_rfl
  · refine entails_trans
      (Q := (junkCell i ∗ junkCell v) ∗
        ((natAssn 1 one ∗ natAssn xs.length n) ∗ arrayAssn (List.range xs.length) A))
      (conj_entails_mono
        (conj_entails_mono (natAssn_entails_junkCell _ i) (natAssn_entails_junkCell _ v))
        (entails_refl _)) (entails_of_eq ?_)
    ac_rfl

/-! ## Initialization from two caller-owned buffers -/

noncomputable def ufInitCost (n : ℕ) : ECost := rangeCost n + fillCost n + irUnit Currency.skip

noncomputable def ufInitMop (n : ℕ) : NRest (Per ℕ) ECost :=
  NRest.consume (NRest.returnT (perInitNat n)) (ufInitCost n)

noncomputable def ufInitProg (parents sizes : List ℕ) : NRest UfArrays ECost :=
  NRest.bindT
    (NRest.consume (NRest.returnT (List.range parents.length)) (rangeCost parents.length)) fun p =>
      NRest.bindT (mop_array_fill sizes 1) fun s => mopPair p s

set_option maxHeartbeats 1000000 in
sepref_synth ufInitRaw (i v P S oneVal oneInc NP NS : String)
    (parents sizes : List ℕ) :
  hnRefine (junkCell i ∗ junkCell v ∗ hnCtxt arrayAssn parents P ∗
      hnCtxt arrayAssn sizes S ∗ hnCtxt natAssn 1 oneVal ∗ hnCtxt natAssn 1 oneInc ∗
      hnCtxt natAssn parents.length NP ∗ hnCtxt natAssn sizes.length NS)
    _ _ (P, S) (arrayAssn ×ₐ arrayAssn) (ufInitProg parents sizes)

theorem ufInitProg_value (parents sizes : List ℕ) (hlen : sizes.length = parents.length) :
    ufInitProg parents sizes =
      NRest.consume
        (NRest.returnT (List.range parents.length, List.replicate parents.length 1))
        (ufInitCost parents.length) := by
  simp only [ufInitProg, mop_array_fill_def, mopPair_def, bindT_unit,
    NRest.consume_consume, hlen, ufInitCost]
  congr 1
  ac_rfl

def ufInitCom (i v P S oneVal oneInc NP NS : String) : Com :=
  .seq (rangeCom i v P oneVal NP) (.seq (fillCom i S oneVal oneInc NS) .skip)

theorem heightOf_init (hj : j < n) : heightOf (List.range n) j = 0 := by
  apply heightOfRoot (ufaInitInvar n) (by simpa using hj)
  rw [getElem!_pos]
  exact List.getElem_range (by simpa using hj)

theorem hOf_init (_hi : i < n) : hOf (List.range n) i = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold hOf
  apply Finset.sup_le
  intro j hj
  simp only [Finset.mem_range, List.length_range] at hj
  split
  · exact Nat.le_zero.mpr (heightOf_init hj)
  · exact Nat.le_refl 0

theorem rankInvar_init (n : ℕ) : rankInvar (List.range n) (List.replicate n 1) := by
  constructor
  · simp
  constructor
  · simp only [List.length_range]
    calc
      (Finset.range n).sum
          (fun i => if (List.range n)[i]! = i then (List.replicate n 1)[i]! else 0) =
          (Finset.range n).sum (fun _ => 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hin : i < n := by simpa using hi
            simp [getElem!_pos, hin, List.getElem_range]
      _ = n := by simp
  · intro i hi hroot
    have hin : i < n := by simpa using hi
    simp [hOf_init hin, getElem!_pos, hin]

theorem ufArrays_init_wf (n : ℕ) :
    UfArrays.Wf (List.range n, List.replicate n 1) := by
  exact ⟨ufaInitInvar n, by simp, rankInvar_init n⟩

@[sepref_fr_rules]
theorem hnr_ufInit (n : ℕ) (i v P S oneVal oneInc NP NS : String) :
    hnRefine (junkArrayOfLen n P ∗ junkArrayOfLen n S ∗ junkCell i ∗ junkCell v ∗
        hnCtxt natAssn 1 oneVal ∗ hnCtxt natAssn 1 oneInc ∗
        hnCtxt natAssn n NP ∗ hnCtxt natAssn n NS)
      (ufInitCom i v P S oneVal oneInc NP NS)
      (junkCell i ∗ junkCell v ∗ hnCtxt natAssn 1 oneVal ∗
        hnCtxt natAssn 1 oneInc ∗ hnCtxt natAssn n NP ∗ hnCtxt natAssn n NS)
      (P, S) ufAssn (ufInitMop n) := by
  refine hnRefine_junkArrayOfLen fun parents hp => ?_
  refine hnRefine_cons_pre
    (hnRefine_junkArrayOfLen (a := S) (n := n)
      (Γ := arrayAssn parents P ∗ junkCell i ∗ junkCell v ∗
        hnCtxt natAssn 1 oneVal ∗ hnCtxt natAssn 1 oneInc ∗
        hnCtxt natAssn n NP ∗ hnCtxt natAssn n NS)
      fun sizes hs => ?_) (by iicf_perm)
  have hraw := ufInitRaw i v P S oneVal oneInc NP NS parents sizes
  rw [ufInitProg_value parents sizes (hs.trans hp.symm), hp, hs] at hraw
  refine hnRefine_cons_pre (hnRefine_res_cast' hraw ?_) (by iicf_perm)
  refine entails_trans (entails_of_eq ?_)
    (conj_entails_mono (entails_refl _)
      (show (arrayAssn (List.range n) P ∗ arrayAssn (List.replicate n 1) S) ⊢
          ufAssn (perInitNat n) (P, S) from ?_))
  · simp only [hnCtxt_def, prodAssn_apply]
    ac_rfl
  · rw [ufAssn_unfold]
    intro q hq
    refine ⟨(List.range n, List.replicate n 1), predLift_sepConj_iff.2 ⟨?_, hq⟩⟩
    exact ⟨ufArrays_init_wf n, ufaInitCorrect n⟩

/-! ## Exact vector-cost gates for the landed loop -/

theorem rangeCost_aset : (rangeCost 3).toFun Currency.aset = 3 := by decide +kernel
theorem rangeCost_add : (rangeCost 3).toFun Currency.add = 6 := by decide +kernel
theorem rangeCost_while : (rangeCost 3).toFun Currency.«while» = 4 := by decide +kernel
theorem rangeCost_const : (rangeCost 3).toFun Currency.const = 2 := by decide +kernel
theorem rangeCost_skip : (rangeCost 3).toFun Currency.skip = 8 := by decide +kernel
theorem rangeCost_copy : (rangeCost 3).toFun Currency.copy = 0 := by decide +kernel
theorem rangeCost_aget : (rangeCost 3).toFun Currency.aget = 0 := by decide +kernel

theorem ufInitCost_aset : (ufInitCost 3).toFun Currency.aset = 6 := by decide +kernel
theorem ufInitCost_add : (ufInitCost 3).toFun Currency.add = 9 := by decide +kernel
theorem ufInitCost_while : (ufInitCost 3).toFun Currency.«while» = 8 := by decide +kernel
theorem ufInitCost_const : (ufInitCost 3).toFun Currency.const = 3 := by decide +kernel
theorem ufInitCost_skip : (ufInitCost 3).toFun Currency.skip = 13 := by decide +kernel

/-! ## Kernel-three guards -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.UnionFindTime.hnr_range_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_range_init

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.UnionFindTime.ufArrays_init_wf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ufArrays_init_wf

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.UnionFindTime.hnr_ufInit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_ufInit

end Lax13Proofs.Refine.Sepref.Iicf.UnionFindTime
