import Lax13Proofs.Refine.Iicf.IicfArray
import Lax13Proofs.Refine.Iicf.UnionFindAbstract
import Mathlib.Data.Nat.Bitwise

/-!
# Timed loop-form union-find

This module ports the executable union-find layer from the pinned Sepreftime
sources.  The local IR has no allocation and no recursive commands, so the
implementation owns two caller-provided arrays and uses bounded loops.

Source accounting:

| source | range | disposition |
|---|---:|---|
| `UnionFind_Impl.thy` | 7--40 | landed below as the closed-form MOP operations |
| same | 44--86 | landed: timed implementation certificate over the three HNR rules |
| `Union_Find_Time.thy` | 651--666 | landed: two-array representation `ufAssn` |
| same | 667--703 | landed: no-allocation `ufInit` from two `junkArrayOfLen` buffers |
| same | 707--844 | landed: height-bounded root search and in-place path compression |
| same | 850--897 | landed: bounds-checked same-set comparison with compression |
| same | 899--1174 | landed: union-by-size and both rank-preservation branches |
| same | 1177--1204 | landed: final timed interface interpretation and bounds |

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

/-! ## Bounded representative search -/

/- The primitive library has an in-place arithmetic rule but not the
array-read analogue.  Root search needs precisely `x := parents[x]`; the
following rule owns the index cell once and is proved directly against
the IR semantics. -/
private theorem aget_self_triple (x a : String) (k w : Val) (xs : List Val)
    (hw : xs[k]? = some w) :
    irTriple (¤¤Currency.aget 1 ∗ x ↦ᵥ k ∗ a ↦ₐ xs) (.aget x a x)
      (x ↦ᵥ w ∗ a ↦ₐ xs) := by
  intro F p hp
  obtain ⟨s, cr⟩ := p
  rw [sepConj_assoc] at hp
  obtain ⟨hafford, hrest⟩ := costCredits_split hp
  rw [sepConj_assoc] at hrest
  have hx : s.vars x = some k := ptoVar_vars hrest
  have ha : s.arrs a = some xs := ptoArr_arrs (irSTATE_rot hrest)
  rw [wp_aget]
  refine ⟨by rw [hx]; simp, k, xs, w, hx, ha, hw, hafford, ?_⟩
  rw [sepConj_assoc]
  exact ptoVar_setVar hrest

private theorem aget_self_mop_rule (x a : String) (xs : List ℕ) (k : ℕ)
    (hk : k < xs.length) :
    irHtriple (¤(irUnit Currency.aget) ∗
        (hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k x))
      (.aget x a x) (hnCtxt arrayAssn xs a ∗ natAssn xs[k]! x) := by
  have hval : xs[k]! = xs[k] := getElem!_pos xs k hk
  have hw : xs[k]? = some xs[k]! := by rw [hval, List.getElem?_eq_getElem hk]
  have e₁ : (¤(irUnit Currency.aget) ∗
      (hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k x)) =
      (¤¤Currency.aget 1 ∗ x ↦ᵥ k ∗ a ↦ₐ xs) := by
    rw [costCredits_one]
    simp only [hnCtxt_def, natAssn_def, arrayAssn_def]
    ac_rfl
  have e₂ : (hnCtxt arrayAssn xs a ∗ natAssn xs[k]! x) =
      (x ↦ᵥ xs[k]! ∗ a ↦ₐ xs) := by
    simp only [hnCtxt_def, natAssn_def, arrayAssn_def]
    ac_rfl
  rw [e₁, e₂]
  exact (aget_self_triple x a k xs[k]! xs hw).gc

@[sepref_fr_rules]
private theorem hnr_mop_aget_self (x a : String) (xs : List ℕ) (k : ℕ) :
    hnRefine (hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k x) (.aget x a x)
      (hnCtxt arrayAssn xs a) x natAssn (mopAget xs k) := by
  rw [mopAget_def]
  exact hnr_assert fun hk => hnRefineI_spect (aget_self_mop_rule x a xs k hk)

theorem heightOf_le_length (hW : UfArrays.Wf (parents, sizes)) (hx : x < parents.length) :
    heightOf parents x ≤ parents.length := by
  have hpow := heightPowLeLength hW.2.2 hW.1 hx
  have hself : ∀ k : ℕ, k ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        have hp : 1 ≤ 2 ^ k := by simpa using Nat.one_le_pow' k 1
        omega
  exact (hself _).trans hpow

private theorem aget_overwrite_mop_rule (d a i : String) (old k : ℕ)
    (xs : List ℕ) (hk : k < xs.length) :
    irHtriple (¤(irUnit Currency.aget) ∗
        (hnCtxt natAssn old d ∗ hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i))
      (.aget d a i)
      ((hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i) ∗ natAssn xs[k]! d) := by
  have hval : xs[k]! = xs[k] := getElem!_pos xs k hk
  have hw : xs[k]? = some xs[k]! := by rw [hval, List.getElem?_eq_getElem hk]
  have e₁ : (¤(irUnit Currency.aget) ∗
      (hnCtxt natAssn old d ∗ hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i)) =
      (¤¤Currency.aget 1 ∗ d ↦ᵥ old ∗ a ↦ₐ xs ∗ i ↦ᵥ k) := by
    rw [costCredits_one]
    simp only [hnCtxt_def, natAssn_def, arrayAssn_def]
  have e₂ : ((hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i) ∗ natAssn xs[k]! d) =
      (d ↦ᵥ xs[k]! ∗ a ↦ₐ xs ∗ i ↦ᵥ k) := by
    simp only [hnCtxt_def, natAssn_def, arrayAssn_def]
    ac_rfl
  rw [e₁, e₂]
  exact (aget_triple d a i old k xs[k]! xs hw).gc

private theorem hnr_mop_aget_overwrite (d a i : String) (old : ℕ)
    (xs : List ℕ) (k : ℕ) :
    hnRefine (hnCtxt natAssn old d ∗ hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i)
      (.aget d a i) (hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i)
      d natAssn (mopAget xs k) := by
  rw [mopAget_def]
  exact hnr_assert fun hk => hnRefineI_spect (aget_overwrite_mop_rule d a i old k xs hk)

noncomputable def mopAgetOverwrite (_old : ℕ) (xs : List ℕ) (k : ℕ) :
    NRest ℕ ECost := mopAget xs k

@[sepref_fr_rules]
private theorem hnr_mop_agetOverwrite (d a i : String) (old : ℕ)
    (xs : List ℕ) (k : ℕ) :
    hnRefine (hnCtxt natAssn old d ∗ hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i)
      (.aget d a i) (hnCtxt arrayAssn xs a ∗ hnCtxt natAssn k i)
      d natAssn (mopAgetOverwrite old xs k) := by
  exact hnr_mop_aget_overwrite d a i old xs k

abbrev FindState := ℕ × (ℕ × List ℕ)
abbrev findStateAssn := natAssn ×ₐ (natAssn ×ₐ arrayAssn)

/-- The scalar flag is zero exactly at a root. -/
def findI (parents : List ℕ) (s : FindState) : Prop :=
  s.2.2 = parents ∧ s.1 < parents.length ∧
    s.2.1 = Nat.xor parents[s.1]! s.1

def findB (s : FindState) : Bool := decide (0 < s.2.1)

def findState (parents : List ℕ) (i : ℕ) : FindState :=
  (i, (Nat.xor parents[i]! i, parents))

def findStep (s : FindState) : FindState :=
  findState s.2.2 s.2.2[s.1]!

/-- Marker for an in-place scalar operation; it is extensionally `mopBinop`
but fixes the destination choice for the small body synthesizer. -/
noncomputable def mopBinopSelf (op : Imp.Bop) (m n : ℕ) : NRest ℕ ECost :=
  mopBinop op m n

@[sepref_fr_rules]
private theorem hnr_mop_binopSelf (op : Imp.Bop) (x z : String) (m n : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn n z) (.binop op x x z)
      (hnCtxt natAssn n z) x natAssn (mopBinopSelf op m n) :=
  hnr_mop_binop_self op x z m n

noncomputable def findF (s : FindState) : NRest FindState ECost :=
  NRest.bindT (mopBinopSelf Imp.Bop.xor s.1 s.2.1) fun p =>
    NRest.bindT (mopAgetOverwrite s.2.1 s.2.2 p) fun q =>
      NRest.bindT (mopBinopSelf Imp.Bop.xor q p) fun d =>
        NRest.bindT (mopPair d s.2.2) fun t => mopPair p t

noncomputable def findStepCost : ECost :=
  irUnit Currency.xor + irUnit Currency.aget + irUnit Currency.xor +
    2 • irUnit Currency.skip

noncomputable def findInitF (parents : List ℕ) (x : ℕ) : NRest FindState ECost :=
  NRest.bindT (mopAget parents x) fun p =>
    NRest.bindT (mopBinop Imp.Bop.xor p x) fun d =>
      NRest.bindT (mopPair d parents) fun t => mopPair x t

noncomputable def findInitCost : ECost :=
  irUnit Currency.aget + irUnit Currency.xor + 2 • irUnit Currency.skip

noncomputable def findRestCost (h : ℕ) : ECost :=
  h • findStepCost + (h + 1) • irUnit Currency.«while»

noncomputable def findCost (h : ℕ) : ECost := findInitCost + findRestCost h

noncomputable def findProg (parents : List ℕ) (x : ℕ) : NRest FindState ECost :=
  NRest.bindT (findInitF parents x) fun s₀ => irWhileIT (findI parents) findB findF s₀

noncomputable def findV (parents : List ℕ) : FindState → ℕ := fun s => heightOf parents s.1

theorem findState_inv (_hI : ufaInvar parents) (hi : i < parents.length) :
    findI parents (findState parents i) := by simp [findI, findState, hi]

private theorem xor_flag_parent (h : d = Nat.xor p i) : Nat.xor i d = p := by
  subst d
  change i ^^^ (p ^^^ i) = p
  rw [Nat.xor_comm p i, Nat.xor_xor_cancel_left]

theorem findF_eq (hU : ufaInvar parents) (hI : findI parents s)
    (_hb : findB s = true) :
    findF s = NRest.consume (NRest.returnT (findStep s)) findStepCost := by
  obtain ⟨rfl, hcur, hflag⟩ := hI
  have hp : Nat.xor s.1 s.2.1 = s.2.2[s.1]! := xor_flag_parent hflag
  have hpbound : s.2.2[s.1]! < s.2.2.length := (ufaInvarD hU hcur).1
  simp only [findF, mopBinopSelf, mopBinop_def, mopAgetOverwrite, mopAget_def, mopPair_def,
    NRest.assert_pos hpbound, NRest.returnT_bindT, bindT_unit, NRest.consume_consume,
    Imp.Bop.apply_xor, binopCurrency_xor, hp, findStep, findState, findStepCost]
  congr 1
  simp [two_nsmul]
  ac_rfl

theorem findStep_inv (hU : ufaInvar parents) (hI : findI parents s)
    (_hb : findB s = true) : findI parents (findStep s) := by
  obtain ⟨rfl, hcur, hflag⟩ := hI
  have hp : Nat.xor s.1 s.2.1 = s.2.2[s.1]! := xor_flag_parent hflag
  have hpbound : s.2.2[s.1]! < s.2.2.length := (ufaInvarD hU hcur).1
  exact findState_inv hU hpbound

theorem findStep_variant (hU : ufaInvar parents) (hI : findI parents s)
    (hb : findB s = true) : findV parents (findStep s) < findV parents s := by
  obtain ⟨rfl, hcur, hflag⟩ := hI
  have hdpos : 0 < s.2.1 := by simpa [findB] using hb
  have hne : s.2.2[s.1]! ≠ s.1 := by
    intro heq
    have hz : s.2.1 = 0 := by simp [hflag, heq]
    rw [hz] at hdpos
    omega
  change heightOf s.2.2 s.2.2[s.1]! < heightOf s.2.2 s.1
  rw [heightOfStep hU hcur hne]
  omega

theorem find_variant (hU : ufaInvar parents) :
    LOOP_VARIANT (findI parents) findB findF (findV parents) := by
  intro s s' hI hb hle
  rw [findF_eq hU hI hb, NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hs' : s' = findStep s := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  subst s'
  exact findStep_variant hU hI hb

theorem findLoop_value (hU : ufaInvar parents) :
    ∀ (m i : ℕ), heightOf parents i ≤ m → i < parents.length →
      irWhileIT (findI parents) findB findF (findState parents i) =
        NRest.consume
          (NRest.returnT (repOf parents i, (0, parents)))
          (findRestCost (heightOf parents i)) := by
  intro m
  induction m with
  | zero =>
      intro i hh hi
      have hroot : parents[i]! = i := by
        by_contra hne
        rw [heightOfStep hU hi hne] at hh
        omega
      have hI := findState_inv hU hi
      have hb : findB (findState parents i) = false := by
        simp [findB, findState, hroot]
      rw [irWhileIT_of_false hI hb, repOfRefl hU hi hroot,
        heightOfRoot hU hi hroot]
      congr 1
      · simp [findState, hroot]
      · simp only [findRestCost, zero_nsmul, one_nsmul, zero_add]
  | succ m ih =>
      intro i hh hi
      by_cases hroot : parents[i]! = i
      · have hI := findState_inv hU hi
        have hb : findB (findState parents i) = false := by
          simp [findB, findState, hroot]
        rw [irWhileIT_of_false hI hb, repOfRefl hU hi hroot,
          heightOfRoot hU hi hroot]
        congr 1
        · simp [findState, hroot]
        · simp only [findRestCost, zero_nsmul, one_nsmul, zero_add]
      · have hI := findState_inv hU hi
        have hxorne : Nat.xor parents[i]! i ≠ 0 := by
          intro hz
          exact hroot (Nat.eq_of_xor_eq_zero hz)
        have hb : findB (findState parents i) = true := by
          change decide (0 < Nat.xor parents[i]! i) = true
          simp only [decide_eq_true_eq]
          exact Nat.pos_of_ne_zero hxorne
        have hp : parents[i]! < parents.length := (ufaInvarD hU hi).1
        have hheight := heightOfStep hU hi hroot
        have hchild : heightOf parents parents[i]! ≤ m := by omega
        rw [irWhileIT_of_true hI hb, findF_eq hU hI hb]
        simp only [findStep, findState]
        rw [bindT_unit]
        change
          (NRest.consume
              (NRest.consume
                (irWhileIT (findI parents) findB findF (findState parents parents[i]!))
                findStepCost)
              (irUnit Currency.«while»)) = _
        rw [ih parents[i]! hchild hp, NRest.consume_consume,
          NRest.consume_consume, repOfStep hU hi hroot]
        congr 1
        simp only [findRestCost, hheight, succ_nsmul]
        abel

theorem findInitF_eq (hi : x < parents.length) :
    findInitF parents x =
      NRest.consume (NRest.returnT (findState parents x)) findInitCost := by
  simp only [findInitF, mopAget_def, NRest.assert_pos hi, mopBinop_def, mopPair_def,
    Imp.Bop.apply_xor, binopCurrency_xor, NRest.returnT_bindT, bindT_unit,
    NRest.consume_consume, findState, findInitCost]
  congr 1
  simp [two_nsmul]
  ac_rfl

theorem findProg_value (hU : ufaInvar parents) (hi : x < parents.length) :
    findProg parents x =
      NRest.consume (NRest.returnT (repOf parents x, (0, parents)))
        (findCost (heightOf parents x)) := by
  unfold findProg
  rw [findInitF_eq hi, bindT_unit,
    findLoop_value hU (heightOf parents x) x (Nat.le_refl _) hi,
    NRest.consume_consume]
  congr 1

sepref_synth findInitSynth (X D P : String) (parents : List ℕ) (x : ℕ) :
  hnRefine (hnCtxt natAssn x X ∗ junkCell D ∗ hnCtxt arrayAssn parents P)
    _ _ (X, (D, P)) findStateAssn (findInitF parents x)

def findInitCom (X D P : String) : Com :=
  (Com.aget D P X).seq
    ((Com.binop .xor D D X).seq (Com.skip.seq Com.skip))

def findBodyCom (X D P : String) : Com :=
  (Com.binop .xor X X D).seq
    ((Com.aget D P X).seq
      ((Com.binop .xor D D X).seq (Com.skip.seq Com.skip)))

theorem findBodyHnr (X D P : String) (s : FindState) :
  hnRefine (hnCtxt natAssn s.1 X ∗ hnCtxt natAssn s.2.1 D ∗
      hnCtxt arrayAssn s.2.2 P)
    (findBodyCom X D P) (□ : Assn) (X, (D, P)) findStateAssn (findF s) := by
  unfold findF findBodyCom
  have h₁ :
      hnRefine (hnCtxt natAssn s.1 X ∗ hnCtxt natAssn s.2.1 D ∗
          hnCtxt arrayAssn s.2.2 P)
        (.binop .xor X X D)
        (hnCtxt natAssn s.2.1 D ∗ hnCtxt arrayAssn s.2.2 P)
        X natAssn (mopBinopSelf .xor s.1 s.2.1) := by
    exact hnRefine_frame_perm (by ac_rfl)
      (hnr_mop_binopSelf .xor X D s.1 s.2.1)
  apply hnr_bind h₁
  · intro p _
    have h₂ :
        hnRefine (hnCtxt natAssn p X ∗
            (hnCtxt natAssn s.2.1 D ∗ hnCtxt arrayAssn s.2.2 P))
          (.aget D P X)
          (hnCtxt arrayAssn s.2.2 P ∗ hnCtxt natAssn p X)
          D natAssn (mopAgetOverwrite s.2.1 s.2.2 p) := by
      exact hnRefine_pre_perm (by ac_rfl)
        (hnr_mop_agetOverwrite D P X s.2.1 s.2.2 p)
    apply hnr_bind h₂
    · intro q _
      have h₃ :
          hnRefine (hnCtxt natAssn q D ∗
              (hnCtxt arrayAssn s.2.2 P ∗ hnCtxt natAssn p X))
            (.binop .xor D D X)
            (hnCtxt natAssn p X ∗ hnCtxt arrayAssn s.2.2 P)
            D natAssn (mopBinopSelf .xor q p) := by
        exact hnRefine_frame_perm (by ac_rfl)
          (hnr_mop_binopSelf .xor D X q p)
      apply hnr_bind h₃
      · intro d _
        have h₄ :
            hnRefine (hnCtxt natAssn d D ∗
                (hnCtxt natAssn p X ∗ hnCtxt arrayAssn s.2.2 P))
              .skip (hnCtxt natAssn p X) (D, P) (natAssn ×ₐ arrayAssn)
              (mopPair d s.2.2) := by
          have h := hnRefine_frame_perm
            (Γ := hnCtxt natAssn d D ∗
              (hnCtxt natAssn p X ∗ hnCtxt arrayAssn s.2.2 P))
            (P := hnCtxt natAssn d D ∗ hnCtxt arrayAssn s.2.2 P)
            (F := hnCtxt natAssn p X) (by ac_rfl)
            (hnr_mop_pair natAssn arrayAssn d s.2.2 D P)
          simpa only [emp_sepConj] using h
        apply hnr_bind h₄
        · intro t _
          exact hnRefine_pre_perm (by simp only [hnCtxt_def, prodAssn_apply]; ac_rfl)
            (hnr_mop_pair natAssn (natAssn ×ₐ arrayAssn) p t X (D, P))
        · intro t
          exact entails_refl (□ : Assn)
      · intro d
        exact entails_refl (□ : Assn)
    · intro q
      exact entails_refl (□ : Assn)
  · intro p
    exact entails_refl (□ : Assn)

def findCond (D : String) : Cond := .lt (.lit 0) (.cell D)

def findLoopCom (X D P : String) : Com :=
  .while (findCond D) (findBodyCom X D P)

theorem findCondRefine (X D P : String) (s : FindState) (_hI : findI parents s) :
    CondRefine (hnCtxt findStateAssn s (X, (D, P))) (findCond D) (findB s) := by
  apply CondRefine_perm
    (P := hnCtxt natAssn s.2.1 D)
    (F := hnCtxt natAssn s.1 X ∗ hnCtxt arrayAssn s.2.2 P)
  · simp only [hnCtxt_def, prodAssn_apply]
    ac_rfl
  · exact condRefine_lt_lit_cell 0 s.2.1 D

theorem findWhileHnr (X D P : String) (parents : List ℕ) (s : FindState)
    (hU : ufaInvar parents) :
    hnRefine (hnCtxt findStateAssn s (X, (D, P))) (findLoopCom X D P) (□ : Assn)
      (X, (D, P)) findStateAssn (irWhileIT (findI parents) findB findF s) := by
  unfold findLoopCom
  have h := hnr_while_measured
      (Rs := findStateAssn) (Γ := (□ : Assn)) (d := (X, (D, P)))
      (cond := findCond D) (cbody := findBodyCom X D P) (findV parents)
      (fun t ht => by simpa only [sepConj_emp] using findCondRefine X D P t ht)
      (fun t _ _ => by
        simpa only [sepConj_emp, hnCtxt_def, prodAssn_apply] using findBodyHnr X D P t)
      (find_variant hU) s
  simpa only [sepConj_emp] using h

def findCom (X D P : String) : Com :=
  (findInitCom X D P).seq (findLoopCom X D P)

theorem findRawHnr (X D P : String) (parents : List ℕ) (x : ℕ)
    (hU : ufaInvar parents) :
    hnRefine (hnCtxt natAssn x X ∗ junkCell D ∗ hnCtxt arrayAssn parents P)
      (findCom X D P) (□ : Assn) (X, (D, P)) findStateAssn (findProg parents x) := by
  unfold findCom findProg
  have hinit :
      hnRefine (hnCtxt natAssn x X ∗ junkCell D ∗ hnCtxt arrayAssn parents P)
        (findInitCom X D P) (□ : Assn) (X, (D, P)) findStateAssn
        (findInitF parents x) := by
    simpa only [findInitCom] using findInitSynth X D P parents x
  apply hnr_bind hinit
  · intro s _
    simpa only [sepConj_emp] using findWhileHnr X D P parents s hU
  · intro s
    exact entails_refl (□ : Assn)

theorem findRawExactHnr (X D P : String) (parents : List ℕ) (x : ℕ)
    (hU : ufaInvar parents) (hi : x < parents.length) :
    hnRefine (hnCtxt natAssn x X ∗ junkCell D ∗ hnCtxt arrayAssn parents P)
      (findCom X D P) (□ : Assn) (X, (D, P)) findStateAssn
      (NRest.consume (NRest.returnT (repOf parents x, (0, parents)))
        (findCost (heightOf parents x))) := by
  have h := findRawHnr X D P parents x hU
  rw [findProg_value hU hi] at h
  exact h

theorem ufAssn_pack (hW : UfArrays.Wf (parents, sizes)) (hAlpha : ufaAlpha parents = R)
    (P S : String) :
    arrayAssn parents P ∗ arrayAssn sizes S ⊢ ufAssn R (P, S) := by
  rw [ufAssn_unfold]
  intro q hq
  refine ⟨(parents, sizes), predLift_sepConj_iff.2 ⟨?_, hq⟩⟩
  exact ⟨hW, hAlpha⟩

/-- End-to-end B1 bridge: return the representative in `X`, restore the
two-array union-find assertion unchanged, and expose the exact height cost. -/
theorem hnr_ufFind (R : Per ℕ) (parents sizes : List ℕ) (x : ℕ)
    (hW : UfArrays.Wf (parents, sizes)) (hAlpha : ufaAlpha parents = R)
    (hi : x < parents.length) (X D P S : String) :
    hnRefine (hnCtxt natAssn x X ∗ junkCell D ∗
        hnCtxt arrayAssn parents P ∗ hnCtxt arrayAssn sizes S)
      (findCom X D P) (junkCell D ∗ ufAssn R (P, S)) X natAssn
      (NRest.consume (NRest.returnT (repOf parents x))
        (findCost (heightOf parents x))) := by
  have hraw := findRawExactHnr X D P parents x hW.1 hi
  have hframe := hnRefine_frame' (F := arrayAssn sizes S) hraw
  refine hnRefine_cons_pre (hnRefine_res_cast' hframe ?_) (by iicf_perm)
  refine entails_trans (entails_of_eq ?_)
    (conj_entails_mono
      (conj_entails_mono (natAssn_entails_junkCell 0 D)
        (ufAssn_pack hW hAlpha P S))
      (entails_refl (natAssn (repOf parents x) X)))
  simp only [prodAssn_apply, emp_sepConj]
  ac_rfl

/-! ## Height-bounded path compression -/

theorem ufaCompress_isRoot_iff (hU : ufaInvar parents) (hx : x < parents.length)
    (hi : i < parents.length) :
    (ufaCompress parents x)[i]! = i ↔ parents[i]! = i := by
  by_cases hix : i = x
  · subst i
    constructor
    · intro hnew
      have hr : repOf parents x = x := by simpa [ufaCompress, hx] using hnew
      exact hr ▸ repOfRoot hU hx
    · intro hold
      have hr := repOfRefl hU hx hold
      simp [ufaCompress, hx, hr]
  · simp [ufaCompress, hi, Ne.symm hix]

private theorem ufaCompress_isRootD_iff (hU : ufaInvar parents)
    (hx : x < parents.length) (hi : i < parents.length) :
    (ufaCompress parents x)[i]?.getD 0 = i ↔ parents[i]?.getD 0 = i := by
  have hinew : i < (ufaCompress parents x).length := by simpa [ufaCompress] using hi
  have h := ufaCompress_isRoot_iff hU hx hi
  rw [getElem!_pos (ufaCompress parents x) i hinew, getElem!_pos parents i hi] at h
  simpa [List.getElem?_eq_getElem hinew, List.getElem?_eq_getElem hi] using h

theorem rankInvar_compress (hR : rankInvar parents sizes) (hU : ufaInvar parents)
    (hx : x < parents.length) : rankInvar (ufaCompress parents x) sizes := by
  constructor
  · simpa [ufaCompress] using hR.1
  constructor
  · rw [show (ufaCompress parents x).length = parents.length by simp [ufaCompress]]
    calc
      (∑ i ∈ Finset.range parents.length,
          if (ufaCompress parents x)[i]! = i then sizes[i]! else 0) =
          ∑ i ∈ Finset.range parents.length,
            if parents[i]! = i then sizes[i]! else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hib : i < parents.length := by simpa using hi
        have hiff := ufaCompress_isRootD_iff hU hx hib
        by_cases hold : parents[i]?.getD 0 = i
        · have hnew := hiff.mpr hold
          simp [hold, hnew]
        · have hnew := not_congr hiff |>.mpr hold
          simp [hold, hnew]
      _ = parents.length := hR.2.1
  · intro i hiNew hrootNew
    have hi : i < parents.length := by simpa [ufaCompress] using hiNew
    have hroot : parents[i]! = i := (ufaCompress_isRoot_iff hU hx hi).mp hrootNew
    exact (Nat.pow_le_pow_right (by omega) (hOfCompress hU hx)).trans
      (hR.2.2 i hi hroot)

/-! ## Union-by-size invariant core -/

noncomputable def unionSizes (parents sizes : List ℕ) (x y : ℕ) : List ℕ :=
  sizes.set (repOf parents y) (sizes[repOf parents x]! + sizes[repOf parents y]!)

/-- Linking one root below a root of at least its recorded size preserves the
source rank invariant.  This is the common argument behind both orientations
of union-by-size. -/
theorem rankInvar_union_roots (hU : ufaInvar parents)
    (hR : rankInvar parents sizes) (hx : x < parents.length)
    (hy : y < parents.length) (hne : repOf parents x ≠ repOf parents y)
    (hsize : sizes[repOf parents x]! ≤ sizes[repOf parents y]!) :
    rankInvar (ufaUnion parents x y) (unionSizes parents sizes x y) := by
  let rx := repOf parents x
  let ry := repOf parents y
  have hrx : rx < parents.length := repOfBound hU hx
  have hry : ry < parents.length := repOfBound hU hy
  have hrootx : parents[rx]! = rx := repOfRoot hU hx
  have hrooty : parents[ry]! = ry := repOfRoot hU hy
  have hrootx' : parents[rx] = rx := by
    rw [← getElem!_pos parents rx hrx]
    exact hrootx
  have hrooty' : parents[ry] = ry := by
    rw [← getElem!_pos parents ry hry]
    exact hrooty
  have hrxy : rx ≠ ry := by simpa [rx, ry] using hne
  have hlen : sizes.length = parents.length := hR.1.symm
  have hsize' : sizes[rx]! ≤ sizes[ry]! := by simpa [rx, ry] using hsize
  constructor
  · simp [ufaUnion, unionSizes, hR.1]
  constructor
  · rw [show (ufaUnion parents x y).length = parents.length by simp [ufaUnion]]
    let oldWeight := fun (k : ℕ) => if parents[k]! = k then sizes[k]! else 0
    let newWeight := fun (k : ℕ) =>
      if (ufaUnion parents x y)[k]! = k then (unionSizes parents sizes x y)[k]! else 0
    have hrxMem : rx ∈ Finset.range parents.length := by simpa using hrx
    have hryMem : ry ∈ (Finset.range parents.length).erase rx := by
      simp [hry, Ne.symm hrxy]
    have hcommon :
        ∑ k ∈ ((Finset.range parents.length).erase rx).erase ry, newWeight k =
          ∑ k ∈ ((Finset.range parents.length).erase rx).erase ry, oldWeight k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkRange : k < parents.length := by simpa using (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk))
      have hkx : k ≠ rx := by
        exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
      have hky : k ≠ ry := by exact Finset.ne_of_mem_erase hk
      simp [newWeight, oldWeight, ufaUnion, unionSizes, rx, ry, hkRange,
        Ne.symm hkx, Ne.symm hky]
    change ∑ k ∈ Finset.range parents.length, newWeight k = parents.length
    have hnewParentRx : (ufaUnion parents x y)[rx]! = ry := by
      simp [ufaUnion, rx, ry, hrx]
    have hnewParentRy : (ufaUnion parents x y)[ry]! = ry := by
      rw [getElem!_pos _ ry (by simpa [ufaUnion] using hry)]
      change (parents.set rx ry)[ry]'(by simpa using hry) = ry
      rw [List.getElem_set_ne hrxy]
      exact hrooty'
    have hnewSizeRy : (unionSizes parents sizes x y)[ry]! = sizes[rx]! + sizes[ry]! := by
      simp [unionSizes, rx, ry, hry, hlen]
    have hnewRx : newWeight rx = 0 := by
      change (if (ufaUnion parents x y)[rx]! = rx then
        (unionSizes parents sizes x y)[rx]! else 0) = 0
      rw [hnewParentRx]
      simp [Ne.symm hrxy]
    have hnewRy : newWeight ry = sizes[rx]! + sizes[ry]! := by
      change (if (ufaUnion parents x y)[ry]! = ry then
        (unionSizes parents sizes x y)[ry]! else 0) = sizes[rx]! + sizes[ry]!
      rw [hnewParentRy, if_pos rfl, hnewSizeRy]
    have holdRx : oldWeight rx = sizes[rx]! := by
      change (if parents[rx]! = rx then sizes[rx]! else 0) = sizes[rx]!
      rw [hrootx, if_pos rfl]
    have holdRy : oldWeight ry = sizes[ry]! := by
      change (if parents[ry]! = ry then sizes[ry]! else 0) = sizes[ry]!
      rw [hrooty, if_pos rfl]
    have hsplitNewRx :
        (∑ k ∈ Finset.range parents.length, newWeight k) =
          newWeight rx + ∑ k ∈ (Finset.range parents.length).erase rx, newWeight k := by
      simpa only [Finset.sdiff_singleton_eq_erase] using
        (Finset.sum_eq_add_sum_diff_singleton rx newWeight
          (fun hnot => (hnot hrxMem).elim))
    have hsplitNewRy :
        (∑ k ∈ (Finset.range parents.length).erase rx, newWeight k) =
          newWeight ry +
            ∑ k ∈ ((Finset.range parents.length).erase rx).erase ry, newWeight k := by
      simpa only [Finset.sdiff_singleton_eq_erase] using
        (Finset.sum_eq_add_sum_diff_singleton ry newWeight
          (fun hnot => (hnot hryMem).elim))
    have hsplitOldRx :
        (∑ k ∈ Finset.range parents.length, oldWeight k) =
          oldWeight rx + ∑ k ∈ (Finset.range parents.length).erase rx, oldWeight k := by
      simpa only [Finset.sdiff_singleton_eq_erase] using
        (Finset.sum_eq_add_sum_diff_singleton rx oldWeight
          (fun hnot => (hnot hrxMem).elim))
    have hsplitOldRy :
        (∑ k ∈ (Finset.range parents.length).erase rx, oldWeight k) =
          oldWeight ry +
            ∑ k ∈ ((Finset.range parents.length).erase rx).erase ry, oldWeight k := by
      simpa only [Finset.sdiff_singleton_eq_erase] using
        (Finset.sum_eq_add_sum_diff_singleton ry oldWeight
          (fun hnot => (hnot hryMem).elim))
    calc
      (∑ k ∈ Finset.range parents.length, newWeight k) =
          newWeight rx + ∑ k ∈ (Finset.range parents.length).erase rx, newWeight k := by
            exact hsplitNewRx
      _ = newWeight rx +
          (newWeight ry +
            ∑ k ∈ ((Finset.range parents.length).erase rx).erase ry, newWeight k) := by
            rw [hsplitNewRy]
      _ = oldWeight rx +
          (oldWeight ry +
            ∑ k ∈ ((Finset.range parents.length).erase rx).erase ry, oldWeight k) := by
            rw [hcommon]
            rw [hnewRx, hnewRy, holdRx, holdRy]
            omega
      _ = ∑ k ∈ Finset.range parents.length, oldWeight k := by
            rw [hsplitOldRx, hsplitOldRy]
      _ = parents.length := hR.2.1
  · intro k hkNew hrootNew
    have hk : k < parents.length := by simpa [ufaUnion] using hkNew
    by_cases hky : k = ry
    · subst k
      have htouched := hOfUnionTouched hU hx hy hry (repOfRefl hU hry hrooty)
        rfl (by simpa [rx, ry] using Ne.symm hrxy)
      have hxRank := hR.2.2 rx hrx hrootx
      have hyRank := hR.2.2 ry hry hrooty
      have hpowMax :
          (2 : ℕ) ^ max (hOf parents ry) (Nat.succ (hOf parents rx)) =
            max (2 ^ hOf parents ry) (2 ^ Nat.succ (hOf parents rx)) := by
        by_cases hle : hOf parents ry ≤ Nat.succ (hOf parents rx)
        · rw [max_eq_right hle,
              max_eq_right (Nat.pow_le_pow_right (by omega) hle)]
        · have hge : Nat.succ (hOf parents rx) ≤ hOf parents ry :=
            Nat.le_of_not_ge hle
          rw [max_eq_left hge,
            max_eq_left (Nat.pow_le_pow_right (by omega) hge)]
      have hpow :
          2 ^ max (hOf parents ry) (Nat.succ (hOf parents rx)) ≤
            sizes[rx]! + sizes[ry]! := by
        rw [hpowMax, pow_succ]
        apply max_le
        · omega
        · omega
      have hnewSizeRy : (unionSizes parents sizes x y)[ry]! =
          sizes[rx]! + sizes[ry]! := by simp [unionSizes, rx, ry, hry, hlen]
      rw [hnewSizeRy]
      exact (Nat.pow_le_pow_right (by omega) htouched).trans hpow
    · have hkx : k ≠ rx := by
        intro h
        subst k
        have hnewParentRx : (ufaUnion parents x y)[rx]! = ry := by
          simp [ufaUnion, rx, ry, hrx]
        rw [hnewParentRx] at hrootNew
        exact hrxy hrootNew.symm
      have hroot : parents[k]! = k := by
        simpa [ufaUnion, rx, hk, hkx, Ne.symm hkx] using hrootNew
      have huntouched := hOfUnionUntouched hU hx hy hk hroot
        (by simpa [rx] using hkx) (by simpa [ry] using hky)
      rw [huntouched]
      simpa [unionSizes, ry, hk, hky, Ne.symm hky] using hR.2.2 k hk hroot

noncomputable def unionArrays (u : UfArrays) (i j : ℕ) : UfArrays :=
  let parents := u.1
  let sizes := u.2
  if repOf parents i = repOf parents j then u
  else if sizes[repOf parents i]! < sizes[repOf parents j]! then
    (ufaUnion parents i j, unionSizes parents sizes i j)
  else
    (ufaUnion parents j i, unionSizes parents sizes j i)

theorem unionArrays_wf (hW : UfArrays.Wf (parents, sizes))
    (hi : i < parents.length) (hj : j < parents.length) :
    UfArrays.Wf (unionArrays (parents, sizes) i j) := by
  have hU := hW.1
  have hR := hW.2.2
  by_cases heq : repOf parents i = repOf parents j
  · simpa [unionArrays, heq] using hW
  · by_cases hlt : sizes[repOf parents i]! < sizes[repOf parents j]!
    · have hrank := rankInvar_union_roots hU hR hi hj heq (Nat.le_of_lt hlt)
      rw [unionArrays, if_neg heq, if_pos hlt]
      refine ⟨ufaUnionInvar hU hi hj, ?_, hrank⟩
      simp [ufaUnion, unionSizes, hW.2.1]
    · have hrank := rankInvar_union_roots hU hR hj hi (Ne.symm heq)
        (Nat.le_of_not_gt hlt)
      rw [unionArrays, if_neg heq, if_neg hlt]
      refine ⟨ufaUnionInvar hU hj hi, ?_, hrank⟩
      simp [ufaUnion, unionSizes, hW.2.1]

theorem unionArrays_alpha (hU : ufaInvar parents)
    (hi : i < parents.length) (hj : j < parents.length) :
    ufaAlpha (unionArrays (parents, sizes) i j).1 =
      perUnion (ufaAlpha parents) i j := by
  by_cases heq : repOf parents i = repOf parents j
  · rw [unionArrays, if_pos heq]
    exact (perUnionCompare ufaAlphaPartEquiv
      ((ufaFindCorrect hU hi hj).mp heq)).symm
  · by_cases hlt : sizes[repOf parents i]! < sizes[repOf parents j]!
    · rw [unionArrays, if_neg heq, if_pos hlt]
      exact ufaUnionCorrect hU hi hj
    · rw [unionArrays, if_neg heq, if_neg hlt, ufaUnionCorrect hU hj hi,
        perUnionComm]

theorem unionArrays_refines (Rel : Per ℕ) (hW : UfArrays.Wf (parents, sizes))
    (hAlpha : ufaAlpha parents = Rel) (hi : i < parents.length)
    (hj : j < parents.length) :
    UfArrays.Wf (unionArrays (parents, sizes) i j) ∧
      ufaAlpha (unionArrays (parents, sizes) i j).1 = perUnion Rel i j := by
  refine ⟨unionArrays_wf hW hi hj, ?_⟩
  rw [← hAlpha]
  exact unionArrays_alpha hW.1 hi hj

noncomputable def unionRootsAbs (parents sizes : List ℕ) (ri rj : ℕ) :
    NRest UfArrays ECost :=
  irIf (decide (ri = rj))
    (mopPair parents sizes)
    (NRest.bindT (mopAget sizes ri) fun si =>
      NRest.bindT (mopAget sizes rj) fun sj =>
        irIf (decide (si < sj))
          (NRest.bindT (mopAset parents ri rj) fun parents' =>
            NRest.bindT (mopBinop .add si sj) fun total =>
              NRest.bindT (mopAset sizes rj total) fun sizes' =>
                mopPair parents' sizes')
          (NRest.bindT (mopAset parents rj ri) fun parents' =>
            NRest.bindT (mopBinop .add sj si) fun total =>
              NRest.bindT (mopAset sizes ri total) fun sizes' =>
                mopPair parents' sizes'))

noncomputable def unionRootsCost (ri rj : ℕ) : ECost :=
  if ri = rj then irUnit Currency.ite + irUnit Currency.skip
  else irUnit Currency.ite + 2 • irUnit Currency.aget + irUnit Currency.ite +
    2 • irUnit Currency.aset + irUnit Currency.add + irUnit Currency.skip

theorem unionRootsAbs_eq (hri : ri < parents.length) (hrj : rj < parents.length)
    (hlen : parents.length = sizes.length) :
    unionRootsAbs parents sizes ri rj =
      NRest.consume
        (NRest.returnT
          (if ri = rj then (parents, sizes)
          else if sizes[ri]! < sizes[rj]! then
            (parents.set ri rj, sizes.set rj (sizes[ri]! + sizes[rj]!))
          else (parents.set rj ri, sizes.set ri (sizes[rj]! + sizes[ri]!))))
        (unionRootsCost ri rj) := by
  have hriS : ri < sizes.length := by omega
  have hrjS : rj < sizes.length := by omega
  by_cases heq : ri = rj
  · simp [unionRootsAbs, unionRootsCost, heq, irIf_true, mopPair_def,
      NRest.consume_consume]
  · by_cases hlt : sizes[ri]! < sizes[rj]!
    · have hlt' : sizes[ri] < sizes[rj] := by
        rwa [getElem!_pos sizes ri hriS, getElem!_pos sizes rj hrjS] at hlt
      simp [unionRootsAbs, unionRootsCost, heq, hlt', irIf_false,
        mopAget_def, mopAset_def, mopBinop_def, mopPair_def, hri, hrj, hriS,
        hrjS, NRest.returnT_bindT, bindT_unit, NRest.consume_consume,
        Imp.Bop.apply_add, binopCurrency_add, two_nsmul]
      congr 1
      ac_rfl
    · have hlt' : ¬ sizes[ri] < sizes[rj] := by
        rwa [getElem!_pos sizes ri hriS, getElem!_pos sizes rj hrjS] at hlt
      simp [unionRootsAbs, unionRootsCost, heq, hlt', irIf_false,
        mopAget_def, mopAset_def, mopBinop_def, mopPair_def, hri, hrj, hriS,
        hrjS, NRest.returnT_bindT, bindT_unit, NRest.consume_consume,
        Imp.Bop.apply_add, binopCurrency_add, two_nsmul]
      congr 1
      ac_rfl

sepref_synth unionRootsSynth (Ri Rj Si Sj Total P S : String)
    (parents sizes : List ℕ) (ri rj : ℕ) :
    hnRefine (hnCtxt natAssn ri Ri ∗ hnCtxt natAssn rj Rj ∗ junkCell Si ∗
        junkCell Sj ∗ junkCell Total ∗ hnCtxt arrayAssn parents P ∗
        hnCtxt arrayAssn sizes S)
      _ _ (P, S) (arrayAssn ×ₐ arrayAssn) (unionRootsAbs parents sizes ri rj)

def unionRootsCom (Ri Rj Si Sj Total P S : String) : Com :=
  Com.ite (.eq (.cell Ri) (.cell Rj)) Com.skip
    ((Com.aget Si S Ri).seq
      ((Com.aget Sj S Rj).seq
        (Com.ite (.lt (.cell Si) (.cell Sj))
          ((Com.aset P Ri Rj).seq
            ((Com.binop .add Total Si Sj).seq ((Com.aset S Rj Total).seq Com.skip)))
          ((Com.aset P Rj Ri).seq
            ((Com.binop .add Total Sj Si).seq ((Com.aset S Ri Total).seq Com.skip))))))

theorem unionRootsResult_eq (parents sizes : List ℕ) (i j : ℕ) :
    (if repOf parents i = repOf parents j then (parents, sizes)
    else if sizes[repOf parents i]! < sizes[repOf parents j]! then
      (parents.set (repOf parents i) (repOf parents j),
        sizes.set (repOf parents j)
          (sizes[repOf parents i]! + sizes[repOf parents j]!))
    else
      (parents.set (repOf parents j) (repOf parents i),
        sizes.set (repOf parents i)
          (sizes[repOf parents j]! + sizes[repOf parents i]!))) =
      unionArrays (parents, sizes) i j := by
  rfl

theorem unionRootsExactHnr (Ri Rj Si Sj Total P S : String)
    (parents sizes : List ℕ) (i j : ℕ) (hU : ufaInvar parents)
    (hi : i < parents.length) (hj : j < parents.length)
    (hlen : parents.length = sizes.length) :
    hnRefine (hnCtxt natAssn (repOf parents i) Ri ∗
        hnCtxt natAssn (repOf parents j) Rj ∗ junkCell Si ∗ junkCell Sj ∗
        junkCell Total ∗ hnCtxt arrayAssn parents P ∗ hnCtxt arrayAssn sizes S)
      (unionRootsCom Ri Rj Si Sj Total P S)
      (hnCtxt natAssn (repOf parents i) Ri ∗
        hnCtxt natAssn (repOf parents j) Rj ∗ junkCell Si ∗ junkCell Sj ∗
        junkCell Total)
      (P, S) (arrayAssn ×ₐ arrayAssn)
      (NRest.consume (NRest.returnT (unionArrays (parents, sizes) i j))
        (unionRootsCost (repOf parents i) (repOf parents j))) := by
  have h := unionRootsSynth Ri Rj Si Sj Total P S parents sizes
    (repOf parents i) (repOf parents j)
  rw [unionRootsAbs_eq (repOfBound hU hi) (repOfBound hU hj) hlen,
    unionRootsResult_eq] at h
  simpa only [unionRootsCom] using h

theorem unionRootsPublicHnr (Ri Rj Si Sj Total P S : String)
    (Rel : Per ℕ) (parents sizes : List ℕ) (i j : ℕ)
    (hW : UfArrays.Wf (parents, sizes)) (hAlpha : ufaAlpha parents = Rel)
    (hi : i < parents.length) (hj : j < parents.length) :
    hnRefine (hnCtxt natAssn (repOf parents i) Ri ∗
        hnCtxt natAssn (repOf parents j) Rj ∗ junkCell Si ∗ junkCell Sj ∗
        junkCell Total ∗ hnCtxt arrayAssn parents P ∗ hnCtxt arrayAssn sizes S)
      (unionRootsCom Ri Rj Si Sj Total P S)
      (junkCell Ri ∗ junkCell Rj ∗ junkCell Si ∗ junkCell Sj ∗ junkCell Total)
      (P, S) ufAssn
      (NRest.consume (NRest.returnT (perUnion Rel i j))
        (unionRootsCost (repOf parents i) (repOf parents j))) := by
  have hout := unionArrays_refines Rel hW hAlpha hi hj
  have hraw := unionRootsExactHnr Ri Rj Si Sj Total P S parents sizes i j
    hW.1 hi hj hW.2.1
  refine hnRefine_res_cast' hraw ?_
  refine entails_trans (entails_of_eq ?_)
    (conj_entails_mono
      (conj_entails_mono
        (natAssn_entails_junkCell (repOf parents i) Ri)
        (conj_entails_mono
          (natAssn_entails_junkCell (repOf parents j) Rj)
          (conj_entails_mono (entails_refl (junkCell Si))
            (conj_entails_mono (entails_refl (junkCell Sj))
              (entails_refl (junkCell Total))))))
      (ufAssn_pack hout.1 hout.2 P S))
  simp only [prodAssn_apply, hnCtxt_def]
  ac_rfl

abbrev CompressState := ℕ × (ℕ × List ℕ)
abbrev compressStateAssn := natAssn ×ₐ (natAssn ×ₐ arrayAssn)

def compressI (root : ℕ) (s : CompressState) : Prop :=
  ufaInvar s.2.2 ∧ s.1 < s.2.2.length ∧ root < s.2.2.length ∧
    repOf s.2.2 s.1 = root ∧ s.2.1 = Nat.xor s.1 root

def compressB (s : CompressState) : Bool := decide (0 < s.2.1)

def compressState (root : ℕ) (parents : List ℕ) (i : ℕ) : CompressState :=
  (i, (Nat.xor i root, parents))

noncomputable def compressStep (root : ℕ) (s : CompressState) : CompressState :=
  (s.2.2[s.1]!, (Nat.xor s.2.2[s.1]! root, s.2.2.set s.1 root))

noncomputable def mopCopyOverwrite (_old new : ℕ) : NRest ℕ ECost := mopCopy new

@[sepref_fr_rules]
private theorem hnr_mop_copyOverwrite (x y : String) (old new : ℕ) :
    hnRefine (hnCtxt natAssn old x ∗ hnCtxt natAssn new y) (.copy x y)
      (hnCtxt natAssn new y) x natAssn (mopCopyOverwrite old new) := by
  unfold mopCopyOverwrite
  exact hnRefine_cons_pre (hnr_mop_copy x y new)
    (conj_entails_mono (natAssn_entails_junkCell old x) (entails_refl _))

noncomputable def compressF (root : ℕ) (s : CompressState) : NRest CompressState ECost :=
  NRest.bindT (mopAgetOverwrite s.2.1 s.2.2 s.1) fun next =>
    NRest.bindT (mopAset s.2.2 s.1 root) fun parents' =>
      NRest.bindT (mopCopyOverwrite s.1 next) fun i' =>
        NRest.bindT (mopBinopSelf .xor next root) fun flag =>
          NRest.bindT (mopPair flag parents') fun t => mopPair i' t

noncomputable def compressStepCost : ECost :=
  irUnit Currency.aget + irUnit Currency.aset + irUnit Currency.copy +
    irUnit Currency.xor + 2 • irUnit Currency.skip

noncomputable def compressRestCost (steps : ℕ) : ECost :=
  steps • compressStepCost + (steps + 1) • irUnit Currency.«while»

noncomputable def compressV (s : CompressState) : ℕ := heightOf s.2.2 s.1

theorem compressStep_eq_ufaCompress (hI : compressI root s) :
    (compressStep root s).2.2 = ufaCompress s.2.2 s.1 := by
  simp only [compressStep, ufaCompress, hI.2.2.2.1]

theorem compressF_eq (hI : compressI root s) (_hb : compressB s = true) :
    compressF root s =
      NRest.consume (NRest.returnT (compressStep root s)) compressStepCost := by
  have hi := hI.2.1
  simp only [compressF, mopAgetOverwrite, mopAget_def, NRest.assert_pos hi,
    mopAset_def, mopCopyOverwrite, mopCopy, mopBinopSelf, mopBinop_def, mopPair_def,
    NRest.returnT_bindT, bindT_unit, NRest.consume_consume, Imp.Bop.apply_xor,
    binopCurrency_xor, compressStep, compressStepCost]
  congr 1
  simp [two_nsmul]
  ac_rfl

private theorem compress_nonroot (hI : compressI root s) (hb : compressB s = true) :
    s.1 ≠ root := by
  have hpos : 0 < s.2.1 := by simpa [compressB] using hb
  intro heq
  subst root
  simp [hI.2.2.2.2] at hpos

theorem compressStep_inv (hI : compressI root s) (hb : compressB s = true) :
    compressI root (compressStep root s) := by
  rcases hI with ⟨hU, hi, hr, hrep, hflag⟩
  have hneRoot : s.1 ≠ root := compress_nonroot ⟨hU, hi, hr, hrep, hflag⟩ hb
  have hnext : s.2.2[s.1]! < s.2.2.length := (ufaInvarD hU hi).1
  have hparentNe : s.2.2[s.1]! ≠ s.1 := by
    intro hp
    have hrefl := repOfRefl hU hi hp
    exact hneRoot (hrefl.symm.trans hrep)
  have hU' := ufaCompressInvar hU hi
  have hrootOld : s.2.2[root]! = root := by
    rw [← hrep]
    exact repOfRoot hU hi
  have hrootNew : (ufaCompress s.2.2 s.1)[root]! = root := by
    exact (ufaCompress_isRoot_iff hU hi hr).mpr hrootOld
  have hrepNextOld : repOf s.2.2 s.2.2[s.1]! = root := by
    rw [repOfIndex hU hi]
    exact hrep
  have hmem : (s.2.2[s.1]!, root) ∈ ufaAlpha (ufaCompress s.2.2 s.1) := by
    rw [ufaCompressCorrect hU hi]
    exact (ufaFindCorrect hU hnext hr).mp (by
      rw [hrepNextOld, repOfRefl hU hr hrootOld])
  have hrepNew : repOf (ufaCompress s.2.2 s.1) s.2.2[s.1]! = root := by
    have heq := (ufaFindCorrect hU' (by simpa [ufaCompress] using hnext)
      (by simpa [ufaCompress] using hr)).mpr hmem
    rw [repOfRefl hU' (by simpa [ufaCompress] using hr) hrootNew] at heq
    exact heq
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · simpa [compressStep_eq_ufaCompress ⟨hU, hi, hr, hrep, hflag⟩] using hU'
  · simpa [compressStep, ufaCompress] using hnext
  · simpa [compressStep, ufaCompress] using hr
  · simpa [compressStep, ufaCompress, hrep] using hrepNew

theorem compressStep_variant (hI : compressI root s) (hb : compressB s = true) :
    compressV (compressStep root s) < compressV s := by
  have hnext := (ufaInvarD hI.1 hI.2.1).1
  have hneRoot := compress_nonroot hI hb
  have hparentNe : s.2.2[s.1]! ≠ s.1 := by
    intro hp
    have hrefl := repOfRefl hI.1 hI.2.1 hp
    exact hneRoot (hrefl.symm.trans hI.2.2.2.1)
  have hle := heightOfCompress hI.1 hnext hI.2.1
  unfold compressV
  simp only [compressStep]
  change heightOf (s.2.2.set s.1 root) s.2.2[s.1]! < heightOf s.2.2 s.1
  rw [show s.2.2.set s.1 root = ufaCompress s.2.2 s.1 by
    simp [ufaCompress, hI.2.2.2.1]]
  rw [heightOfStep hI.1 hI.2.1 hparentNe]
  omega

theorem compress_variant (root : ℕ) :
    LOOP_VARIANT (compressI root) compressB (compressF root) compressV := by
  intro s s' hI hb hle
  rw [compressF_eq hI hb, NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hs' : s' = compressStep root s := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  subst s'
  exact compressStep_variant hI hb

noncomputable def compressExec (root : ℕ) : ℕ → CompressState → CompressState
  | 0, s => s
  | fuel + 1, s =>
      if compressB s then compressExec root fuel (compressStep root s) else s

noncomputable def compressCount (root : ℕ) : ℕ → CompressState → ℕ
  | 0, _ => 0
  | fuel + 1, s =>
      if compressB s then compressCount root fuel (compressStep root s) + 1 else 0

theorem compressCount_le (root : ℕ) (fuel : ℕ) (s : CompressState) :
    compressCount root fuel s ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp [compressCount]
  | succ fuel ih =>
      simp only [compressCount]
      split
      · exact Nat.succ_le_succ (ih _)
      · omega

theorem compressExec_inv (hI : compressI root s) :
    ∀ fuel, compressI root (compressExec root fuel s) := by
  intro fuel
  induction fuel generalizing s with
  | zero => simpa [compressExec]
  | succ fuel ih =>
      simp only [compressExec]
      split
      next hb => exact ih (compressStep_inv hI hb)
      next => exact hI

theorem compressExec_preserves (hI : compressI root s)
    (hR : rankInvar s.2.2 sizes) : ∀ fuel,
    ufaAlpha (compressExec root fuel s).2.2 = ufaAlpha s.2.2 ∧
      rankInvar (compressExec root fuel s).2.2 sizes := by
  intro fuel
  induction fuel generalizing s with
  | zero => exact ⟨rfl, hR⟩
  | succ fuel ih =>
      simp only [compressExec]
      split
      next hb =>
        have hstepI := compressStep_inv hI hb
        have hstepEq := compressStep_eq_ufaCompress hI
        have hstepR : rankInvar (compressStep root s).2.2 sizes := by
          rw [hstepEq]
          exact rankInvar_compress hR hI.1 hI.2.1
        obtain ⟨ha, hr⟩ := ih hstepI hstepR
        refine ⟨ha.trans ?_, hr⟩
        rw [hstepEq, ufaCompressCorrect hI.1 hI.2.1]
      next => exact ⟨rfl, hR⟩

theorem compressLoop_value : ∀ (fuel : ℕ) (s : CompressState),
    compressV s ≤ fuel → compressI root s →
      irWhileIT (compressI root) compressB (compressF root) s =
        NRest.consume (NRest.returnT (compressExec root fuel s))
          (compressRestCost (compressCount root fuel s)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s hv hI
      have hb : compressB s = false := by
        by_contra hbne
        have hbtrue : compressB s = true := by simpa using hbne
        have := compressStep_variant hI hbtrue
        omega
      rw [irWhileIT_of_false hI hb]
      simp only [compressExec, compressCount]
      congr 1
      simp only [compressRestCost, zero_nsmul, one_nsmul, zero_add]
  | succ fuel ih =>
      intro s hv hI
      by_cases hb : compressB s = true
      · have hv' : compressV (compressStep root s) ≤ fuel := by
          have := compressStep_variant hI hb
          omega
        rw [irWhileIT_of_true hI hb, compressF_eq hI hb, bindT_unit,
          ih (compressStep root s) hv' (compressStep_inv hI hb),
          NRest.consume_consume, NRest.consume_consume]
        simp only [compressExec, compressCount, hb, if_true]
        congr 1
        simp only [compressRestCost, succ_nsmul]
        abel
      · have hbfalse : compressB s = false := by simpa using hb
        rw [irWhileIT_of_false hI hbfalse]
        simp [compressExec, compressCount, hbfalse]
        congr 1
        simp only [compressRestCost, zero_nsmul, one_nsmul, zero_add]

noncomputable def compressPath (parents : List ℕ) (x : ℕ) : List ℕ :=
  let root := repOf parents x
  (compressExec root (heightOf parents x) (compressState root parents x)).2.2

noncomputable def compressSteps (parents : List ℕ) (x : ℕ) : ℕ :=
  let root := repOf parents x
  compressCount root (heightOf parents x) (compressState root parents x)

theorem compressState_inv (hU : ufaInvar parents) (hx : x < parents.length) :
    compressI (repOf parents x) (compressState (repOf parents x) parents x) := by
  exact ⟨hU, hx, repOfBound hU hx, rfl, rfl⟩

theorem compressSteps_le_height (parents : List ℕ) (x : ℕ) :
    compressSteps parents x ≤ heightOf parents x := by
  exact compressCount_le _ _ _

theorem compressPath_preserves (hW : UfArrays.Wf (parents, sizes))
    (hx : x < parents.length) :
    ufaAlpha (compressPath parents x) = ufaAlpha parents ∧
      UfArrays.Wf (compressPath parents x, sizes) := by
  have hI := compressState_inv hW.1 hx
  have h := compressExec_preserves hI hW.2.2 (heightOf parents x)
  have houtI := compressExec_inv hI (heightOf parents x)
  change ufaAlpha
      (compressExec (repOf parents x) (heightOf parents x)
        (compressState (repOf parents x) parents x)).2.2 = ufaAlpha parents ∧ _
  exact ⟨h.1, houtI.1, h.2.1, h.2⟩

noncomputable def compressInitF (root : ℕ) (parents : List ℕ) (x : ℕ) :
    NRest CompressState ECost :=
  NRest.bindT (mopBinop .xor x root) fun flag =>
    NRest.bindT (mopPair flag parents) fun t => mopPair x t

noncomputable def compressInitCost : ECost :=
  irUnit Currency.xor + 2 • irUnit Currency.skip

noncomputable def compressCost (steps : ℕ) : ECost :=
  compressInitCost + compressRestCost steps

noncomputable def compressProg (root : ℕ) (parents : List ℕ) (x : ℕ) :
    NRest CompressState ECost :=
  NRest.bindT (compressInitF root parents x) fun s₀ =>
    irWhileIT (compressI root) compressB (compressF root) s₀

theorem compressInitF_eq :
    compressInitF root parents x =
      NRest.consume (NRest.returnT (compressState root parents x)) compressInitCost := by
  simp only [compressInitF, mopBinop_def, mopPair_def, Imp.Bop.apply_xor,
    binopCurrency_xor, bindT_unit, NRest.consume_consume,
    compressState, compressInitCost]
  congr 1
  simp [two_nsmul]

theorem compressProg_value (hU : ufaInvar parents) (hx : x < parents.length) :
    compressProg (repOf parents x) parents x =
      NRest.consume
        (NRest.returnT
          (compressExec (repOf parents x) (heightOf parents x)
            (compressState (repOf parents x) parents x)))
        (compressCost (compressSteps parents x)) := by
  unfold compressProg
  rw [compressInitF_eq, bindT_unit,
    compressLoop_value (heightOf parents x) _ (Nat.le_refl _)
      (compressState_inv hU hx), NRest.consume_consume]
  congr 1

sepref_synth compressInitSynth (X D P Root : String)
    (root x : ℕ) (parents : List ℕ) :
  hnRefine (hnCtxt natAssn x X ∗ junkCell D ∗ hnCtxt arrayAssn parents P ∗
      hnCtxt natAssn root Root)
    _ _ (X, (D, P)) compressStateAssn
    (compressInitF root parents x)

def compressBodyCom (X D P Root : String) : Com :=
  (Com.aget D P X).seq
    ((Com.aset P X Root).seq
      ((Com.copy X D).seq
        ((Com.binop .xor D D Root).seq (Com.skip.seq Com.skip))))

theorem compressBodyHnr (X D P Root : String) (root : ℕ) (s : CompressState) :
    hnRefine (hnCtxt natAssn s.1 X ∗ hnCtxt natAssn s.2.1 D ∗
        hnCtxt arrayAssn s.2.2 P ∗ hnCtxt natAssn root Root)
      (compressBodyCom X D P Root) (hnCtxt natAssn root Root)
      (X, (D, P)) compressStateAssn (compressF root s) := by
  unfold compressF compressBodyCom
  have h₁ :
      hnRefine (hnCtxt natAssn s.1 X ∗ hnCtxt natAssn s.2.1 D ∗
          hnCtxt arrayAssn s.2.2 P ∗ hnCtxt natAssn root Root)
        (.aget D P X)
        ((hnCtxt arrayAssn s.2.2 P ∗ hnCtxt natAssn s.1 X) ∗
          hnCtxt natAssn root Root)
        D natAssn (mopAgetOverwrite s.2.1 s.2.2 s.1) := by
    exact hnRefine_frame_perm (by ac_rfl)
      (hnr_mop_agetOverwrite D P X s.2.1 s.2.2 s.1)
  apply hnr_bind h₁
  · intro next _
    have h₂ :
        hnRefine (hnCtxt natAssn next D ∗
            ((hnCtxt arrayAssn s.2.2 P ∗ hnCtxt natAssn s.1 X) ∗
              hnCtxt natAssn root Root))
          (.aset P X Root)
          ((hnCtxt natAssn s.1 X ∗ hnCtxt natAssn root Root) ∗
            hnCtxt natAssn next D)
          P arrayAssn (mopAset s.2.2 s.1 root) := by
      exact hnRefine_frame_perm (by ac_rfl)
        (hnr_mop_aset P X Root s.2.2 s.1 root)
    apply hnr_bind h₂
    · intro parents' _
      have h₃ :
          hnRefine (hnCtxt arrayAssn parents' P ∗
              ((hnCtxt natAssn s.1 X ∗ hnCtxt natAssn root Root) ∗
                hnCtxt natAssn next D))
            (.copy X D)
            (hnCtxt natAssn next D ∗
              (hnCtxt arrayAssn parents' P ∗ hnCtxt natAssn root Root))
            X natAssn (mopCopyOverwrite s.1 next) := by
        exact hnRefine_frame_perm (by ac_rfl)
          (hnr_mop_copyOverwrite X D s.1 next)
      apply hnr_bind h₃
      · intro current _
        have h₄ :
            hnRefine (hnCtxt natAssn current X ∗
                (hnCtxt natAssn next D ∗
                  (hnCtxt arrayAssn parents' P ∗ hnCtxt natAssn root Root)))
              (.binop .xor D D Root)
              (hnCtxt natAssn root Root ∗
                (hnCtxt natAssn current X ∗ hnCtxt arrayAssn parents' P))
              D natAssn (mopBinopSelf .xor next root) := by
          exact hnRefine_frame_perm (by ac_rfl)
            (hnr_mop_binopSelf .xor D Root next root)
        apply hnr_bind h₄
        · intro flag _
          have h₅ :
              hnRefine (hnCtxt natAssn flag D ∗
                  (hnCtxt natAssn root Root ∗
                    (hnCtxt natAssn current X ∗ hnCtxt arrayAssn parents' P)))
                .skip
                (hnCtxt natAssn current X ∗ hnCtxt natAssn root Root)
                (D, P) (natAssn ×ₐ arrayAssn) (mopPair flag parents') := by
            have h := hnRefine_frame_perm
              (Γ := hnCtxt natAssn flag D ∗
                (hnCtxt natAssn root Root ∗
                  (hnCtxt natAssn current X ∗ hnCtxt arrayAssn parents' P)))
              (P := hnCtxt natAssn flag D ∗ hnCtxt arrayAssn parents' P)
              (F := hnCtxt natAssn current X ∗ hnCtxt natAssn root Root)
              (by ac_rfl)
              (hnr_mop_pair natAssn arrayAssn flag parents' D P)
            simpa only [emp_sepConj] using h
          apply hnr_bind h₅
          · intro t _
            have h := hnRefine_frame_perm
                (Γ := hnCtxt (natAssn ×ₐ arrayAssn) t (D, P) ∗
                  (hnCtxt natAssn current X ∗ hnCtxt natAssn root Root))
                (P := hnCtxt natAssn current X ∗
                  hnCtxt (natAssn ×ₐ arrayAssn) t (D, P))
                (F := hnCtxt natAssn root Root) (by ac_rfl)
                (hnr_mop_pair natAssn (natAssn ×ₐ arrayAssn) current t X (D, P))
            simpa only [emp_sepConj] using h
          · intro t
            exact entails_refl (hnCtxt natAssn root Root)
        · intro flag
          exact entails_refl (hnCtxt natAssn root Root)
      · intro current
        exact entails_refl (hnCtxt natAssn root Root)
    · intro parents'
      exact entails_refl (hnCtxt natAssn root Root)
  · intro next
    exact entails_refl (hnCtxt natAssn root Root)

def compressInitCom (X D Root : String) : Com :=
  (Com.binop .xor D X Root).seq (Com.skip.seq Com.skip)

def compressCond (D : String) : Cond := .lt (.lit 0) (.cell D)

def compressLoopCom (X D P Root : String) : Com :=
  .while (compressCond D) (compressBodyCom X D P Root)

theorem compressCondRefine (X D P Root : String) (root : ℕ) (s : CompressState)
    (_hI : compressI root s) :
    CondRefine
      (hnCtxt compressStateAssn s (X, (D, P)) ∗ hnCtxt natAssn root Root)
      (compressCond D) (compressB s) := by
  apply CondRefine_perm
    (P := hnCtxt natAssn s.2.1 D)
    (F := hnCtxt natAssn s.1 X ∗ hnCtxt arrayAssn s.2.2 P ∗
      hnCtxt natAssn root Root)
  · simp only [hnCtxt_def, prodAssn_apply]
    ac_rfl
  · exact condRefine_lt_lit_cell 0 s.2.1 D

theorem compressWhileHnr (X D P Root : String) (root : ℕ) (s : CompressState) :
    hnRefine
      (hnCtxt compressStateAssn s (X, (D, P)) ∗ hnCtxt natAssn root Root)
      (compressLoopCom X D P Root) (hnCtxt natAssn root Root)
      (X, (D, P)) compressStateAssn
      (irWhileIT (compressI root) compressB (compressF root) s) := by
  unfold compressLoopCom
  have h := hnr_while_measured
      (Rs := compressStateAssn) (Γ := hnCtxt natAssn root Root)
      (d := (X, (D, P))) (cond := compressCond D)
      (cbody := compressBodyCom X D P Root) compressV
      (fun t ht => compressCondRefine X D P Root root t ht)
      (fun t _ _ => by
        exact hnRefine_pre_perm
          (by simp only [hnCtxt_def, prodAssn_apply]; ac_rfl)
          (compressBodyHnr X D P Root root t))
      (compress_variant root) s
  exact h

def compressCom (X D P Root : String) : Com :=
  (compressInitCom X D Root).seq (compressLoopCom X D P Root)

theorem compressRawHnr (X D P Root : String) (root x : ℕ) (parents : List ℕ) :
    hnRefine (hnCtxt natAssn x X ∗ junkCell D ∗ hnCtxt arrayAssn parents P ∗
        hnCtxt natAssn root Root)
      (compressCom X D P Root) (hnCtxt natAssn root Root)
      (X, (D, P)) compressStateAssn (compressProg root parents x) := by
  unfold compressCom compressProg
  have hinit :
      hnRefine (hnCtxt natAssn x X ∗ junkCell D ∗ hnCtxt arrayAssn parents P ∗
          hnCtxt natAssn root Root)
        (compressInitCom X D Root) (hnCtxt natAssn root Root)
        (X, (D, P)) compressStateAssn (compressInitF root parents x) := by
    simpa only [compressInitCom] using compressInitSynth X D P Root root x parents
  apply hnr_bind hinit
  · intro s _
    exact compressWhileHnr X D P Root root s
  · intro s
    exact entails_refl (hnCtxt natAssn root Root)

theorem compressRawExactHnr (X D P Root : String) (parents : List ℕ) (x : ℕ)
    (hU : ufaInvar parents) (hx : x < parents.length) :
    hnRefine (hnCtxt natAssn x X ∗ junkCell D ∗ hnCtxt arrayAssn parents P ∗
        hnCtxt natAssn (repOf parents x) Root)
      (compressCom X D P Root) (hnCtxt natAssn (repOf parents x) Root)
      (X, (D, P)) compressStateAssn
      (NRest.consume
        (NRest.returnT
          (compressExec (repOf parents x) (heightOf parents x)
            (compressState (repOf parents x) parents x)))
        (compressCost (compressSteps parents x))) := by
  have h := compressRawHnr X D P Root (repOf parents x) x parents
  rw [compressProg_value hU hx] at h
  exact h

/-- End-to-end path-compression bridge. The representative supplied by the
find phase remains the result, while the traversed path is rewritten to it. -/
theorem hnr_ufCompress (R : Per ℕ) (parents sizes : List ℕ) (x : ℕ)
    (hW : UfArrays.Wf (parents, sizes)) (hAlpha : ufaAlpha parents = R)
    (hx : x < parents.length) (X D P S Root : String) :
    hnRefine (hnCtxt natAssn x X ∗ junkCell D ∗
        hnCtxt arrayAssn parents P ∗ hnCtxt arrayAssn sizes S ∗
        hnCtxt natAssn (repOf parents x) Root)
      (compressCom X D P Root)
      (junkCell X ∗ junkCell D ∗ ufAssn R (P, S)) Root natAssn
      (NRest.consume (NRest.returnT (repOf parents x))
        (compressCost (compressSteps parents x))) := by
  let out := compressExec (repOf parents x) (heightOf parents x)
    (compressState (repOf parents x) parents x)
  have hI := compressState_inv hW.1 hx
  have houtI : compressI (repOf parents x) out := by
    exact compressExec_inv hI (heightOf parents x)
  have hout := compressExec_preserves hI hW.2.2 (heightOf parents x)
  have houtW : UfArrays.Wf (out.2.2, sizes) :=
    ⟨houtI.1, hout.2.1, hout.2⟩
  have houtAlpha : ufaAlpha out.2.2 = R := hout.1.trans hAlpha
  have hraw := compressRawExactHnr X D P Root parents x hW.1 hx
  have hframe := hnRefine_frame' (F := arrayAssn sizes S) hraw
  refine hnRefine_cons_pre (hnRefine_res_cast' hframe ?_) (by iicf_perm)
  refine entails_trans (entails_of_eq ?_)
    (conj_entails_mono
      (conj_entails_mono
        (natAssn_entails_junkCell out.1 X)
        (conj_entails_mono
          (natAssn_entails_junkCell out.2.1 D)
          (ufAssn_pack houtW houtAlpha P S)))
      (entails_refl (natAssn (repOf parents x) Root)))
  simp only [out, hnCtxt_def, prodAssn_apply]
  ac_rfl

/-! ## Same-set comparison -/

theorem findExplicitExactHnr (X D P : String) (parents : List ℕ) (x : ℕ)
    (hU : ufaInvar parents) (hx : x < parents.length) :
    hnRefine (hnCtxt natAssn x X ∗ junkCell D ∗ hnCtxt arrayAssn parents P)
      (findCom X D P) (junkCell D ∗ hnCtxt arrayAssn parents P)
      X natAssn
      (NRest.consume (NRest.returnT (repOf parents x))
        (findCost (heightOf parents x))) := by
  have hraw := findRawExactHnr X D P parents x hU hx
  refine hnRefine_res_cast' hraw ?_
  refine entails_trans (entails_of_eq ?_)
    (conj_entails_mono
      (conj_entails_mono (natAssn_entails_junkCell 0 D)
        (entails_refl (arrayAssn parents P)))
      (entails_refl (natAssn (repOf parents x) X)))
  simp only [prodAssn_apply, emp_sepConj]
  ac_rfl

/-! ## Source-shaped union-by-size command -/

noncomputable def unionCost (parents : List ℕ) (i j : ℕ) : ECost :=
  2 • irUnit Currency.copy + findCost (heightOf parents i) +
    findCost (heightOf parents j) +
      unionRootsCost (repOf parents i) (repOf parents j)

noncomputable def unionAbs (Rel : Per ℕ) (parents : List ℕ) (i j : ℕ) :
    NRest (Per ℕ) ECost :=
  NRest.bindT (mopCopy i) fun _ =>
    NRest.bindT
      (NRest.consume (NRest.returnT (repOf parents i))
        (findCost (heightOf parents i))) fun _ =>
      NRest.bindT (mopCopy j) fun _ =>
        NRest.bindT
          (NRest.consume (NRest.returnT (repOf parents j))
            (findCost (heightOf parents j))) fun _ =>
          NRest.consume (NRest.returnT (perUnion Rel i j))
            (unionRootsCost (repOf parents i) (repOf parents j))

theorem unionAbs_eq (Rel : Per ℕ) :
    unionAbs Rel parents i j =
      NRest.consume (mopPerUnion Rel i j) (unionCost parents i j) := by
  simp only [unionAbs, mopCopy, mopPerUnion, bindT_unit, NRest.consume_consume,
    unionCost, two_nsmul]
  congr 1
  ac_rfl

def unionCom (I J Ri Rj D Si Sj Total P S : String) : Com :=
  (Com.copy Ri I).seq
    ((findCom Ri D P).seq
      ((Com.copy Rj J).seq
        ((findCom Rj D P).seq (unionRootsCom Ri Rj Si Sj Total P S))))

/-- Public union boundary.  As in the source rule, the indices are domain
preconditions; an out-of-domain call is not replaced by a totalized update. -/
@[sepref_fr_rules]
theorem hnr_ufUnion (I J Ri Rj D Si Sj Total P S : String) (Rel : Per ℕ)
    (parents sizes : List ℕ) (i j : ℕ) (hW : UfArrays.Wf (parents, sizes))
    (hAlpha : ufaAlpha parents = Rel) (hi : i < parents.length)
    (hj : j < parents.length) :
    hnRefine (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell Ri ∗
        junkCell Rj ∗ junkCell D ∗ junkCell Si ∗ junkCell Sj ∗
        junkCell Total ∗ hnCtxt arrayAssn parents P ∗ hnCtxt arrayAssn sizes S)
      (unionCom I J Ri Rj D Si Sj Total P S)
      (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell Ri ∗
        junkCell Rj ∗ junkCell D ∗ junkCell Si ∗ junkCell Sj ∗ junkCell Total)
      (P, S) ufAssn
      (NRest.consume (mopPerUnion Rel i j) (unionCost parents i j)) := by
  rw [← unionAbs_eq]
  unfold unionCom unionAbs
  let Final := hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell Ri ∗
    junkCell Rj ∗ junkCell D ∗ junkCell Si ∗ junkCell Sj ∗ junkCell Total
  have hcopyI :
      hnRefine (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell Ri ∗
          junkCell Rj ∗ junkCell D ∗ junkCell Si ∗ junkCell Sj ∗
          junkCell Total ∗ hnCtxt arrayAssn parents P ∗ hnCtxt arrayAssn sizes S)
        (.copy Ri I)
        (hnCtxt natAssn i I ∗
          (hnCtxt natAssn j J ∗ junkCell Rj ∗ junkCell D ∗ junkCell Si ∗
            junkCell Sj ∗ junkCell Total ∗ hnCtxt arrayAssn parents P ∗
            hnCtxt arrayAssn sizes S))
        Ri natAssn (mopCopy i) := by
    exact hnRefine_frame_perm (by ac_rfl) (hnr_mop_copy Ri I i)
  apply hnr_bind (Γ₂ := fun _ => Final) hcopyI
  · intro copiedI hcopiedI
    have hcopiedI' : copiedI = i :=
      bind_ref_tag_pin (by simpa [mopCopy] using hcopiedI)
    subst copiedI
    have hfindI :
        hnRefine (hnCtxt natAssn i Ri ∗
            (hnCtxt natAssn i I ∗
              (hnCtxt natAssn j J ∗ junkCell Rj ∗ junkCell D ∗ junkCell Si ∗
                junkCell Sj ∗ junkCell Total ∗ hnCtxt arrayAssn parents P ∗
                hnCtxt arrayAssn sizes S)))
          (findCom Ri D P)
          ((junkCell D ∗ hnCtxt arrayAssn parents P) ∗
            (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell Rj ∗
              junkCell Si ∗ junkCell Sj ∗ junkCell Total ∗
              hnCtxt arrayAssn sizes S))
          Ri natAssn
          (NRest.consume (NRest.returnT (repOf parents i))
            (findCost (heightOf parents i))) := by
      exact hnRefine_frame_perm (by ac_rfl)
        (findExplicitExactHnr Ri D P parents i hW.1 hi)
    apply hnr_bind (Γ₂ := fun _ => Final) hfindI
    · intro rootI hrootI
      have hrootI' : rootI = repOf parents i := bind_ref_tag_pin hrootI
      subst rootI
      have hcopyJ :
          hnRefine (hnCtxt natAssn (repOf parents i) Ri ∗
              ((junkCell D ∗ hnCtxt arrayAssn parents P) ∗
                (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell Rj ∗
                  junkCell Si ∗ junkCell Sj ∗ junkCell Total ∗
                  hnCtxt arrayAssn sizes S)))
            (.copy Rj J)
            (hnCtxt natAssn j J ∗
              (hnCtxt natAssn (repOf parents i) Ri ∗ hnCtxt natAssn i I ∗
                junkCell D ∗ junkCell Si ∗ junkCell Sj ∗ junkCell Total ∗
                hnCtxt arrayAssn parents P ∗ hnCtxt arrayAssn sizes S))
            Rj natAssn (mopCopy j) := by
        exact hnRefine_frame_perm (by ac_rfl) (hnr_mop_copy Rj J j)
      apply hnr_bind (Γ₂ := fun _ => Final) hcopyJ
      · intro copiedJ hcopiedJ
        have hcopiedJ' : copiedJ = j :=
          bind_ref_tag_pin (by simpa [mopCopy] using hcopiedJ)
        subst copiedJ
        have hfindJ :
            hnRefine (hnCtxt natAssn j Rj ∗
                (hnCtxt natAssn j J ∗
                  (hnCtxt natAssn (repOf parents i) Ri ∗ hnCtxt natAssn i I ∗
                    junkCell D ∗ junkCell Si ∗ junkCell Sj ∗ junkCell Total ∗
                    hnCtxt arrayAssn parents P ∗ hnCtxt arrayAssn sizes S)))
              (findCom Rj D P)
              ((junkCell D ∗ hnCtxt arrayAssn parents P) ∗
                (hnCtxt natAssn j J ∗ hnCtxt natAssn (repOf parents i) Ri ∗
                  hnCtxt natAssn i I ∗ junkCell Si ∗ junkCell Sj ∗
                  junkCell Total ∗ hnCtxt arrayAssn sizes S))
              Rj natAssn
              (NRest.consume (NRest.returnT (repOf parents j))
                (findCost (heightOf parents j))) := by
          exact hnRefine_frame_perm (by ac_rfl)
            (findExplicitExactHnr Rj D P parents j hW.1 hj)
        apply hnr_bind (Γ₂ := fun _ => Final) hfindJ
        · intro rootJ hrootJ
          have hrootJ' : rootJ = repOf parents j := bind_ref_tag_pin hrootJ
          subst rootJ
          have hroot := unionRootsPublicHnr Ri Rj Si Sj Total P S Rel
            parents sizes i j hW hAlpha hi hj
          have hframed := hnRefine_frame_perm
            (F := hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell D)
            (by ac_rfl) hroot
          exact hnRefine_cons_pre
            (hnRefine_cons_post hframed
              (entails_of_eq (by dsimp [Final]; ac_rfl)))
            (entails_of_eq (by ac_rfl))
        · intro _
          exact entails_refl Final
      · intro _
        exact entails_refl Final
    · intro _
      exact entails_refl Final
  · intro _
    dsimp [Final]
    exact entails_refl _

theorem unionCost_eq_phases :
    unionCost parents i j =
      2 • irUnit Currency.copy + findCost (heightOf parents i) +
        findCost (heightOf parents j) +
          unionRootsCost (repOf parents i) (repOf parents j) := rfl

theorem union_height_bounds (hW : UfArrays.Wf (parents, sizes))
    (hi : i < parents.length) (hj : j < parents.length) :
    heightOf parents i ≤ heightUb parents.length ∧
      heightOf parents j ≤ heightUb parents.length := by
  exact ⟨heightOfLeHeightUb hW.2.2 hW.1 hi,
    heightOfLeHeightUb hW.2.2 hW.1 hj⟩

theorem compressExplicitExactHnr (X D P Root : String) (parents : List ℕ) (x : ℕ)
    (hU : ufaInvar parents) (hx : x < parents.length) :
    hnRefine (hnCtxt natAssn x X ∗ junkCell D ∗ hnCtxt arrayAssn parents P ∗
        hnCtxt natAssn (repOf parents x) Root)
      (compressCom X D P Root)
      (junkCell X ∗ junkCell D ∗ hnCtxt arrayAssn (compressPath parents x) P)
      Root natAssn
      (NRest.consume (NRest.returnT (repOf parents x))
        (compressCost (compressSteps parents x))) := by
  let out := compressExec (repOf parents x) (heightOf parents x)
    (compressState (repOf parents x) parents x)
  have hraw := compressRawExactHnr X D P Root parents x hU hx
  refine hnRefine_res_cast' hraw ?_
  refine entails_trans (entails_of_eq ?_)
    (conj_entails_mono
      (conj_entails_mono (natAssn_entails_junkCell out.1 X)
        (conj_entails_mono (natAssn_entails_junkCell out.2.1 D)
          (entails_refl (arrayAssn (compressPath parents x) P))))
      (entails_refl (natAssn (repOf parents x) Root)))
  simp only [out, compressPath, hnCtxt_def, prodAssn_apply]
  ac_rfl

noncomputable def repCompressCost (parents : List ℕ) (x : ℕ) : ECost :=
  2 • irUnit Currency.copy + findCost (heightOf parents x) +
    compressCost (compressSteps parents x)

noncomputable def repCompressAbs (parents : List ℕ) (x : ℕ) : NRest ℕ ECost :=
  NRest.bindT (mopCopy x) fun _ =>
    NRest.bindT
      (NRest.consume (NRest.returnT (repOf parents x))
        (findCost (heightOf parents x))) fun _ =>
      NRest.bindT (mopCopy x) fun _ =>
        NRest.consume (NRest.returnT (repOf parents x))
          (compressCost (compressSteps parents x))

theorem repCompressAbs_eq :
    repCompressAbs parents x =
      NRest.consume (NRest.returnT (repOf parents x))
        (repCompressCost parents x) := by
  simp only [repCompressAbs, mopCopy, bindT_unit, NRest.consume_consume,
    repCompressCost]
  congr 1
  simp [two_nsmul]
  ac_rfl

def repCompressCom (I Root D F P : String) : Com :=
  (Com.copy Root I).seq
    ((findCom Root D P).seq
      ((Com.copy D I).seq (compressCom D F P Root)))

theorem repCompressHnr (I Root D F P : String) (parents : List ℕ) (x : ℕ)
    (hU : ufaInvar parents) (hx : x < parents.length) :
    hnRefine (hnCtxt natAssn x I ∗ junkCell Root ∗ junkCell D ∗ junkCell F ∗
        hnCtxt arrayAssn parents P)
      (repCompressCom I Root D F P)
      (hnCtxt natAssn x I ∗ junkCell D ∗ junkCell F ∗
        hnCtxt arrayAssn (compressPath parents x) P)
      Root natAssn (repCompressAbs parents x) := by
  unfold repCompressCom repCompressAbs
  have hcopyRoot :
      hnRefine (hnCtxt natAssn x I ∗ junkCell Root ∗ junkCell D ∗ junkCell F ∗
          hnCtxt arrayAssn parents P)
        (.copy Root I)
        (hnCtxt natAssn x I ∗
          (junkCell D ∗ junkCell F ∗ hnCtxt arrayAssn parents P))
        Root natAssn (mopCopy x) := by
    exact hnRefine_frame_perm (by ac_rfl) (hnr_mop_copy Root I x)
  apply hnr_bind
    (Γ₂ := fun _ => hnCtxt natAssn x I ∗ junkCell D ∗ junkCell F ∗
      hnCtxt arrayAssn (compressPath parents x) P) hcopyRoot
  · intro root₀ hroot₀
    have hroot₀' : root₀ = x := bind_ref_tag_pin (by simpa [mopCopy] using hroot₀)
    subst root₀
    have hfind :
        hnRefine (hnCtxt natAssn x Root ∗
            (hnCtxt natAssn x I ∗
              (junkCell D ∗ junkCell F ∗ hnCtxt arrayAssn parents P)))
          (findCom Root D P)
          ((junkCell D ∗ hnCtxt arrayAssn parents P) ∗
            (hnCtxt natAssn x I ∗ junkCell F))
          Root natAssn
          (NRest.consume (NRest.returnT (repOf parents x))
            (findCost (heightOf parents x))) := by
      exact hnRefine_frame_perm (by ac_rfl)
        (findExplicitExactHnr Root D P parents x hU hx)
    apply hnr_bind
      (Γ₂ := fun _ => hnCtxt natAssn x I ∗ junkCell D ∗ junkCell F ∗
        hnCtxt arrayAssn (compressPath parents x) P) hfind
    · intro root hroot
      have hroot' : root = repOf parents x := bind_ref_tag_pin hroot
      subst root
      have hcopyD :
          hnRefine (hnCtxt natAssn (repOf parents x) Root ∗
              ((junkCell D ∗ hnCtxt arrayAssn parents P) ∗
                (hnCtxt natAssn x I ∗ junkCell F)))
            (.copy D I)
            (hnCtxt natAssn x I ∗
              (hnCtxt natAssn (repOf parents x) Root ∗
                (hnCtxt arrayAssn parents P ∗ junkCell F)))
            D natAssn (mopCopy x) := by
        exact hnRefine_frame_perm (by ac_rfl) (hnr_mop_copy D I x)
      apply hnr_bind
        (Γ₂ := fun _ => hnCtxt natAssn x I ∗ junkCell D ∗ junkCell F ∗
          hnCtxt arrayAssn (compressPath parents x) P) hcopyD
      · intro original horiginal
        have horiginal' : original = x :=
          bind_ref_tag_pin (by simpa [mopCopy] using horiginal)
        subst original
        have hcompress :
            hnRefine (hnCtxt natAssn x D ∗
                (hnCtxt natAssn x I ∗
                  (hnCtxt natAssn (repOf parents x) Root ∗
                    (hnCtxt arrayAssn parents P ∗ junkCell F))))
              (compressCom D F P Root)
              (hnCtxt natAssn x I ∗ junkCell D ∗ junkCell F ∗
                hnCtxt arrayAssn (compressPath parents x) P)
              Root natAssn
              (NRest.consume (NRest.returnT (repOf parents x))
                (compressCost (compressSteps parents x))) := by
          exact hnRefine_cons_post
            (hnRefine_frame_perm (F := hnCtxt natAssn x I) (by ac_rfl)
              (compressExplicitExactHnr D F P Root parents x hU hx))
            (entails_of_eq (by ac_rfl))
        exact hcompress
      · intro original
        exact entails_of_eq (by ac_rfl)
    · intro root
      exact entails_of_eq (by ac_rfl)
  · intro root₀
    exact entails_of_eq (by ac_rfl)

theorem repCompressExactHnr (I Root D F P : String) (parents : List ℕ) (x : ℕ)
    (hU : ufaInvar parents) (hx : x < parents.length) :
    hnRefine (hnCtxt natAssn x I ∗ junkCell Root ∗ junkCell D ∗ junkCell F ∗
        hnCtxt arrayAssn parents P)
      (repCompressCom I Root D F P)
      (hnCtxt natAssn x I ∗ junkCell D ∗ junkCell F ∗
        hnCtxt arrayAssn (compressPath parents x) P)
      Root natAssn
      (NRest.consume (NRest.returnT (repOf parents x))
        (repCompressCost parents x)) := by
  rw [← repCompressAbs_eq]
  exact repCompressHnr I Root D F P parents x hU hx

theorem ufaCompressRep_local (hI : ufaInvar parents) (hx : x < parents.length)
    (hi : i < parents.length) :
    repOf (ufaCompress parents x) i = repOf parents i := by
  have hI' := ufaCompressInvar hI hx
  have hi' : i < (ufaCompress parents x).length := by simpa [ufaCompress] using hi
  have hr := repOfBound hI hi
  have hr' : repOf parents i < (ufaCompress parents x).length := by
    simpa [ufaCompress] using hr
  have hroot' : (ufaCompress parents x)[repOf parents i]! = repOf parents i :=
    (ufaCompress_isRoot_iff hI hx hr).mpr (repOfRoot hI hi)
  have hmem : (i, repOf parents i) ∈ ufaAlpha (ufaCompress parents x) := by
    rw [ufaCompressCorrect hI hx]
    exact (ufaFindCorrect hI hi hr).mp (repOfIdem hI hi).symm
  have heq := (ufaFindCorrect hI' hi' hr').mpr hmem
  rwa [repOfRefl hI' hr' hroot'] at heq

theorem compressExec_rep (hI : compressI root s) (hi : i < s.2.2.length) :
    ∀ fuel, repOf (compressExec root fuel s).2.2 i = repOf s.2.2 i := by
  intro fuel
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      simp only [compressExec]
      split
      next hb =>
        have hstepI := compressStep_inv hI hb
        have hstepEq := compressStep_eq_ufaCompress hI
        have hi' : i < (compressStep root s).2.2.length := by
          rw [hstepEq]
          simpa [ufaCompress] using hi
        calc
          repOf (compressExec root fuel (compressStep root s)).2.2 i =
              repOf (compressStep root s).2.2 i := ih hstepI hi'
          _ = repOf s.2.2 i := by
            rw [hstepEq]
            exact ufaCompressRep_local hI.1 hI.2.1 hi
      next => rfl

theorem compressPath_rep (hU : ufaInvar parents) (hx : x < parents.length)
    (hi : i < parents.length) :
    repOf (compressPath parents x) i = repOf parents i := by
  exact compressExec_rep (compressState_inv hU hx) hi (heightOf parents x)

noncomputable def rootsEqAbs (a b : ℕ) : NRest ℕ ECost :=
  irIf (decide (a = b)) (mopConstN 1) (mopConstN 0)

noncomputable def rootsEqCost : ECost :=
  irUnit Currency.ite + irUnit Currency.const

theorem rootsEqAbs_eq :
    rootsEqAbs a b =
      NRest.consume (NRest.returnT (if decide (a = b) then 1 else 0)) rootsEqCost := by
  by_cases h : a = b
  · simp [rootsEqAbs, rootsEqCost, h, irIf_true, mopConstN,
      NRest.consume_consume, add_comm]
  · simp [rootsEqAbs, rootsEqCost, h, irIf_false, mopConstN,
      NRest.consume_consume, add_comm]

sepref_synth rootsEqSynth (A B R : String) (a b : ℕ) :
  hnRefine (hnCtxt natAssn a A ∗ hnCtxt natAssn b B ∗ junkCell R)
    _ _ R natAssn (rootsEqAbs a b)

def rootsEqCom (A B R : String) : Com :=
  .ite (.eq (.cell A) (.cell B)) (.const R 1) (.const R 0)

theorem rootsEqExactHnr (A B R : String) (a b : ℕ) :
    hnRefine (hnCtxt natAssn a A ∗ hnCtxt natAssn b B ∗ junkCell R)
      (rootsEqCom A B R) (hnCtxt natAssn a A ∗ hnCtxt natAssn b B)
      R natAssn
      (NRest.consume (NRest.returnT (if decide (a = b) then 1 else 0))
        rootsEqCost) := by
  rw [← rootsEqAbs_eq]
  simpa only [rootsEqCom, emp_sepConj] using rootsEqSynth A B R a b

noncomputable def compareCoreCost (parents : List ℕ) (i j : ℕ) : ECost :=
  repCompressCost parents i + repCompressCost (compressPath parents i) j + rootsEqCost

noncomputable def compareCoreAbs (parents : List ℕ) (i j : ℕ) : NRest ℕ ECost :=
  NRest.bindT
    (NRest.consume (NRest.returnT (repOf parents i)) (repCompressCost parents i)) fun _ =>
      NRest.bindT
        (NRest.consume
          (NRest.returnT (repOf (compressPath parents i) j))
          (repCompressCost (compressPath parents i) j)) fun _ =>
            NRest.consume
              (NRest.returnT
                (if decide (repOf parents i = repOf (compressPath parents i) j)
                  then 1 else 0)) rootsEqCost

theorem compareCoreAbs_eq :
    compareCoreAbs parents i j =
      NRest.consume
        (NRest.returnT
          (if decide (repOf parents i = repOf (compressPath parents i) j) then 1 else 0))
        (compareCoreCost parents i j) := by
  simp only [compareCoreAbs, bindT_unit, NRest.consume_consume, compareCoreCost]
  congr 1
  ac_rfl

def compareCoreCom (I J Ri Rj D F P R : String) : Com :=
  (repCompressCom I Ri D F P).seq
    ((repCompressCom J Rj D F P).seq (rootsEqCom Ri Rj R))

theorem compareCoreRawHnr (I J Ri Rj D F P S R : String)
    (parents sizes : List ℕ) (i j : ℕ) (hW : UfArrays.Wf (parents, sizes))
    (hi : i < parents.length) (hj : j < parents.length) :
    let parentsI := compressPath parents i
    let parentsIJ := compressPath parentsI j
    hnRefine (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell Ri ∗
        junkCell Rj ∗ junkCell D ∗ junkCell F ∗ hnCtxt arrayAssn parents P ∗
        hnCtxt arrayAssn sizes S ∗ junkCell R)
      (compareCoreCom I J Ri Rj D F P R)
      (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell D ∗ junkCell F ∗
        hnCtxt natAssn (repOf parents i) Ri ∗
        hnCtxt natAssn (repOf parentsI j) Rj ∗
        hnCtxt arrayAssn parentsIJ P ∗ hnCtxt arrayAssn sizes S)
      R natAssn (compareCoreAbs parents i j) := by
  dsimp only
  let parentsI := compressPath parents i
  let parentsIJ := compressPath parentsI j
  have hpresI := compressPath_preserves hW hi
  have hWI : UfArrays.Wf (parentsI, sizes) := by
    simpa only [parentsI] using hpresI.2
  have hjI : j < parentsI.length := by
    rw [hWI.2.1, ← hW.2.1]
    exact hj
  unfold compareCoreCom compareCoreAbs
  have hphaseI :
      hnRefine (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell Ri ∗
          junkCell Rj ∗ junkCell D ∗ junkCell F ∗ hnCtxt arrayAssn parents P ∗
          hnCtxt arrayAssn sizes S ∗ junkCell R)
        (repCompressCom I Ri D F P)
        ((hnCtxt natAssn i I ∗ junkCell D ∗ junkCell F ∗
            hnCtxt arrayAssn parentsI P) ∗
          (hnCtxt natAssn j J ∗ junkCell Rj ∗ hnCtxt arrayAssn sizes S ∗ junkCell R))
        Ri natAssn
        (NRest.consume (NRest.returnT (repOf parents i))
          (repCompressCost parents i)) := by
    exact hnRefine_frame_perm (by ac_rfl)
      (repCompressExactHnr I Ri D F P parents i hW.1 hi)
  apply hnr_bind
    (Γ₂ := fun _ => hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell D ∗
      junkCell F ∗ hnCtxt natAssn (repOf parents i) Ri ∗
      hnCtxt natAssn (repOf parentsI j) Rj ∗
      hnCtxt arrayAssn parentsIJ P ∗ hnCtxt arrayAssn sizes S) hphaseI
  · intro rootI hrootI
    have hrootI' : rootI = repOf parents i := bind_ref_tag_pin hrootI
    subst rootI
    have hphaseJ :
        hnRefine (hnCtxt natAssn (repOf parents i) Ri ∗
            ((hnCtxt natAssn i I ∗ junkCell D ∗ junkCell F ∗
                hnCtxt arrayAssn parentsI P) ∗
              (hnCtxt natAssn j J ∗ junkCell Rj ∗
                hnCtxt arrayAssn sizes S ∗ junkCell R)))
          (repCompressCom J Rj D F P)
          ((hnCtxt natAssn j J ∗ junkCell D ∗ junkCell F ∗
              hnCtxt arrayAssn parentsIJ P) ∗
            (hnCtxt natAssn i I ∗ hnCtxt natAssn (repOf parents i) Ri ∗
              hnCtxt arrayAssn sizes S ∗ junkCell R))
          Rj natAssn
          (NRest.consume (NRest.returnT (repOf parentsI j))
            (repCompressCost parentsI j)) := by
      exact hnRefine_frame_perm (by ac_rfl)
        (repCompressExactHnr J Rj D F P parentsI j hWI.1 hjI)
    apply hnr_bind
      (Γ₂ := fun _ => hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell D ∗
        junkCell F ∗ hnCtxt natAssn (repOf parents i) Ri ∗
        hnCtxt natAssn (repOf parentsI j) Rj ∗
        hnCtxt arrayAssn parentsIJ P ∗ hnCtxt arrayAssn sizes S) hphaseJ
    · intro rootJ hrootJ
      have hrootJ' : rootJ = repOf parentsI j := bind_ref_tag_pin hrootJ
      subst rootJ
      have heq :
          hnRefine (hnCtxt natAssn (repOf parentsI j) Rj ∗
              ((hnCtxt natAssn j J ∗ junkCell D ∗ junkCell F ∗
                  hnCtxt arrayAssn parentsIJ P) ∗
                (hnCtxt natAssn i I ∗ hnCtxt natAssn (repOf parents i) Ri ∗
                  hnCtxt arrayAssn sizes S ∗ junkCell R)))
            (rootsEqCom Ri Rj R)
            (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell D ∗ junkCell F ∗
              hnCtxt natAssn (repOf parents i) Ri ∗
              hnCtxt natAssn (repOf parentsI j) Rj ∗
              hnCtxt arrayAssn parentsIJ P ∗ hnCtxt arrayAssn sizes S)
            R natAssn
            (NRest.consume
              (NRest.returnT
                (if decide (repOf parents i = repOf parentsI j) then 1 else 0))
              rootsEqCost) := by
        exact hnRefine_cons_post
          (hnRefine_frame_perm
            (F := hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell D ∗
              junkCell F ∗ hnCtxt arrayAssn parentsIJ P ∗
              hnCtxt arrayAssn sizes S) (by ac_rfl)
            (rootsEqExactHnr Ri Rj R (repOf parents i) (repOf parentsI j)))
          (entails_of_eq (by ac_rfl))
      exact heq
    · intro rootJ
      exact entails_of_eq (by ac_rfl)
  · intro rootI
    exact entails_of_eq (by ac_rfl)

noncomputable def perCompareB (Rel : Per ℕ) (i j : ℕ) : Bool := by
  classical
  exact decide (perCompare Rel i j)

theorem compareRoots_correct (Rel : Per ℕ) (hU : ufaInvar parents)
    (hAlpha : ufaAlpha parents = Rel)
    (hi : i < parents.length) (hj : j < parents.length) :
    decide (repOf parents i = repOf (compressPath parents i) j) =
      perCompareB Rel i j := by
  classical
  unfold perCompareB
  have hjrep := compressPath_rep hU hi hj
  have hiff : repOf parents i = repOf parents j ↔ perCompare Rel i j := by
    simpa [perCompare, hAlpha] using ufaFindCorrect hU hi hj
  rw [hjrep]
  by_cases h : repOf parents i = repOf parents j
  · have := hiff.mp h
    simp [h, this]
  · have : ¬perCompare Rel i j := fun hr => h (hiff.mpr hr)
    simp [h, this]

theorem compareCoreHnr (I J Ri Rj D F P S R : String) (Rel : Per ℕ)
    (parents sizes : List ℕ) (i j : ℕ) (hW : UfArrays.Wf (parents, sizes))
    (hAlpha : ufaAlpha parents = Rel) (hi : i < parents.length)
    (hj : j < parents.length) :
    hnRefine (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell Ri ∗
        junkCell Rj ∗ junkCell D ∗ junkCell F ∗ hnCtxt arrayAssn parents P ∗
        hnCtxt arrayAssn sizes S ∗ junkCell R)
      (compareCoreCom I J Ri Rj D F P R)
      (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell Ri ∗ junkCell Rj ∗
        junkCell D ∗ junkCell F ∗ ufAssn Rel (P, S))
      R natAssn
      (NRest.consume
        (NRest.returnT (if perCompareB Rel i j then 1 else 0))
        (compareCoreCost parents i j)) := by
  let parentsI := compressPath parents i
  let parentsIJ := compressPath parentsI j
  have hpresI := compressPath_preserves hW hi
  have hWI : UfArrays.Wf (parentsI, sizes) := by simpa [parentsI] using hpresI.2
  have hjI : j < parentsI.length := by rw [hWI.2.1, ← hW.2.1]; exact hj
  have hpresJ := compressPath_preserves hWI hjI
  have hWIJ : UfArrays.Wf (parentsIJ, sizes) := by simpa [parentsIJ] using hpresJ.2
  have hAlphaIJ : ufaAlpha parentsIJ = Rel := by
    simpa [parentsI, parentsIJ] using hpresJ.1.trans (hpresI.1.trans hAlpha)
  have hflag := compareRoots_correct Rel hW.1 hAlpha hi hj
  have hraw := compareCoreRawHnr I J Ri Rj D F P S R parents sizes i j hW hi hj
  rw [compareCoreAbs_eq] at hraw
  refine hnRefine_res_cast' hraw ?_
  refine entails_trans (entails_of_eq ?_)
    (conj_entails_mono
      (conj_entails_mono (entails_refl (natAssn i I))
        (conj_entails_mono (entails_refl (natAssn j J))
          (conj_entails_mono
            (natAssn_entails_junkCell (repOf parents i) Ri)
            (conj_entails_mono
              (natAssn_entails_junkCell (repOf parentsI j) Rj)
              (conj_entails_mono (entails_refl (junkCell D))
                (conj_entails_mono (entails_refl (junkCell F))
                  (ufAssn_pack hWIJ hAlphaIJ P S)))))))
      (entails_refl
        (natAssn (if perCompareB Rel i j then 1 else 0) R)))
  simp only [parentsI, parentsIJ, hnCtxt_def, hflag]
  ac_rfl

noncomputable def compareCost (parents : List ℕ) (i j : ℕ) : ECost :=
  if i < parents.length then
    irUnit Currency.ite +
      if j < parents.length then irUnit Currency.ite + compareCoreCost parents i j
      else irUnit Currency.ite + irUnit Currency.const
  else irUnit Currency.ite + irUnit Currency.const

noncomputable def compareAbs (Rel : Per ℕ) (parents : List ℕ) (i j : ℕ) :
    NRest ℕ ECost :=
  irIf (decide (i < parents.length))
    (irIf (decide (j < parents.length))
      (NRest.consume
        (NRest.returnT (if perCompareB Rel i j then 1 else 0))
        (compareCoreCost parents i j))
      (mopConstN 0))
    (mopConstN 0)

theorem perCompareB_false_left (Rel : Per ℕ) (hAlpha : ufaAlpha parents = Rel)
    (hi : ¬i < parents.length) : perCompareB Rel i j = false := by
  classical
  unfold perCompareB perCompare
  rw [← hAlpha]
  simp [ufaAlpha, hi]

theorem perCompareB_false_right (Rel : Per ℕ) (hAlpha : ufaAlpha parents = Rel)
    (hj : ¬j < parents.length) : perCompareB Rel i j = false := by
  classical
  unfold perCompareB perCompare
  rw [← hAlpha]
  simp [ufaAlpha, hj]

theorem compareAbs_eq (Rel : Per ℕ) (hAlpha : ufaAlpha parents = Rel) :
    compareAbs Rel parents i j =
      NRest.consume
        (NRest.returnT (if perCompareB Rel i j then 1 else 0))
        (compareCost parents i j) := by
  by_cases hi : i < parents.length
  · by_cases hj : j < parents.length
    · simp [compareAbs, compareCost, hi, hj, irIf_true, NRest.consume_consume]
    · have hfalse := perCompareB_false_right (i := i) Rel hAlpha hj
      simp [compareAbs, compareCost, hi, hj, hfalse, irIf_true, irIf_false,
        mopConstN, NRest.consume_consume, add_comm]
  · have hfalse := perCompareB_false_left (j := j) Rel hAlpha hi
    simp [compareAbs, compareCost, hi, hfalse, irIf_false, mopConstN,
      NRest.consume_consume, add_comm]

def compareCom (I J N Ri Rj D F P R : String) : Com :=
  .ite (.lt (.cell I) (.cell N))
    (.ite (.lt (.cell J) (.cell N)) (compareCoreCom I J Ri Rj D F P R)
      (.const R 0))
    (.const R 0)

theorem compareFalseHnr (I J N Ri Rj D F P S R : String) (Rel : Per ℕ)
    (parents sizes : List ℕ) (i j : ℕ) (hW : UfArrays.Wf (parents, sizes))
    (hAlpha : ufaAlpha parents = Rel) :
    hnRefine (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
        hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
        junkCell D ∗ junkCell F ∗ hnCtxt arrayAssn parents P ∗
        hnCtxt arrayAssn sizes S ∗ junkCell R)
      (.const R 0)
      (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
        hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
        junkCell D ∗ junkCell F ∗ ufAssn Rel (P, S))
      R natAssn (mopConstN 0) := by
  let Frame := hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
    hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
    junkCell D ∗ junkCell F ∗ hnCtxt arrayAssn parents P ∗
    hnCtxt arrayAssn sizes S
  have h :
      hnRefine (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
          hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
          junkCell D ∗ junkCell F ∗ hnCtxt arrayAssn parents P ∗
          hnCtxt arrayAssn sizes S ∗ junkCell R)
        (.const R 0) ((□ : Assn) ∗ Frame) R natAssn (mopConstN 0) := by
    exact hnRefine_frame_perm (F := Frame) (by dsimp [Frame]; ac_rfl)
      (hnr_mop_constN R 0)
  refine hnRefine_cons_post h ?_
  refine entails_trans
    (entails_of_eq (by simp only [Frame, emp_sepConj, hnCtxt_def])) <|
      (conj_entails_mono (entails_refl (natAssn i I))
        (conj_entails_mono (entails_refl (natAssn j J))
          (conj_entails_mono (entails_refl (natAssn parents.length N))
            (conj_entails_mono (entails_refl (junkCell Ri))
              (conj_entails_mono (entails_refl (junkCell Rj))
                (conj_entails_mono (entails_refl (junkCell D))
                  (conj_entails_mono (entails_refl (junkCell F))
                    (ufAssn_pack hW hAlpha P S))))))))

theorem compareRawHnr (I J N Ri Rj D F P S R : String) (Rel : Per ℕ)
    (parents sizes : List ℕ) (i j : ℕ) (hW : UfArrays.Wf (parents, sizes))
    (hAlpha : ufaAlpha parents = Rel) :
    hnRefine (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
        hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
        junkCell D ∗ junkCell F ∗ hnCtxt arrayAssn parents P ∗
        hnCtxt arrayAssn sizes S ∗ junkCell R)
      (compareCom I J N Ri Rj D F P R)
      (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
        hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
        junkCell D ∗ junkCell F ∗ ufAssn Rel (P, S))
      R natAssn (compareAbs Rel parents i j) := by
  unfold compareCom compareAbs
  let Γ' := hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
    hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
    junkCell D ∗ junkCell F ∗ ufAssn Rel (P, S)
  apply hnr_If
  · exact CondRefine_perm
      (P := hnCtxt natAssn i I ∗ hnCtxt natAssn parents.length N)
      (F := hnCtxt natAssn j J ∗ junkCell Ri ∗ junkCell Rj ∗ junkCell D ∗
        junkCell F ∗ hnCtxt arrayAssn parents P ∗ hnCtxt arrayAssn sizes S ∗ junkCell R)
      (by ac_rfl) (condRefine_lt_cells i parents.length I N)
  · intro hbi
    have hi : i < parents.length := of_decide_eq_true hbi
    apply hnr_If
    · exact CondRefine_perm
        (P := hnCtxt natAssn j J ∗ hnCtxt natAssn parents.length N)
        (F := hnCtxt natAssn i I ∗ junkCell Ri ∗ junkCell Rj ∗ junkCell D ∗
          junkCell F ∗ hnCtxt arrayAssn parents P ∗ hnCtxt arrayAssn sizes S ∗ junkCell R)
        (by ac_rfl) (condRefine_lt_cells j parents.length J N)
    · intro hbj
      have hj : j < parents.length := of_decide_eq_true hbj
      have hcore :
          hnRefine (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
              hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
              junkCell D ∗ junkCell F ∗ hnCtxt arrayAssn parents P ∗
              hnCtxt arrayAssn sizes S ∗ junkCell R)
            (compareCoreCom I J Ri Rj D F P R) Γ' R natAssn
            (NRest.consume
              (NRest.returnT (if perCompareB Rel i j then 1 else 0))
              (compareCoreCost parents i j)) := by
        exact hnRefine_cons_post
          (hnRefine_frame_perm
            (Γ := hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
              hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
              junkCell D ∗ junkCell F ∗ hnCtxt arrayAssn parents P ∗
              hnCtxt arrayAssn sizes S ∗ junkCell R)
            (F := hnCtxt natAssn parents.length N) (by ac_rfl)
            (compareCoreHnr I J Ri Rj D F P S R Rel parents sizes i j hW hAlpha hi hj))
          (entails_of_eq (by dsimp [Γ']; ac_rfl))
      exact hcore
    · intro _
      exact compareFalseHnr I J N Ri Rj D F P S R Rel parents sizes i j hW hAlpha
    · exact MERGE_triv Γ'
  · intro _
    exact compareFalseHnr I J N Ri Rj D F P S R Rel parents sizes i j hW hAlpha
  · exact MERGE_triv Γ'

def boolNatAssn (b : Bool) (R : String) : Assn :=
  natAssn (if b then 1 else 0) R

theorem mopPerCompare_eq (Rel : Per ℕ) :
    mopPerCompare Rel i j = NRest.returnT (perCompareB Rel i j) := by
  rfl

theorem compareCost_eq_phases (hi : i < parents.length) (hj : j < parents.length) :
    compareCost parents i j =
      2 • irUnit Currency.ite + repCompressCost parents i +
        repCompressCost (compressPath parents i) j + rootsEqCost := by
  rw [compareCost, if_pos hi, if_pos hj]
  simp only [compareCoreCost, two_nsmul]
  ac_rfl

theorem compareCost_oob_left (hi : ¬i < parents.length) :
    compareCost parents i j = irUnit Currency.ite + irUnit Currency.const := by
  simp [compareCost, hi]

theorem compareCost_oob_right (hi : i < parents.length) (hj : ¬j < parents.length) :
    compareCost parents i j =
      2 • irUnit Currency.ite + irUnit Currency.const := by
  simp only [compareCost, hi, hj, if_true, if_false, two_nsmul]
  ac_rfl

/-- Public comparison boundary. `N` carries the array length because the local
IR deliberately has no array-length instruction; it is preserved unchanged. -/
theorem hnr_ufCompare (I J N Ri Rj D F P S R : String) (Rel : Per ℕ)
    (parents sizes : List ℕ) (i j : ℕ) (hW : UfArrays.Wf (parents, sizes))
    (hAlpha : ufaAlpha parents = Rel) :
    hnRefine (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
        hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
        junkCell D ∗ junkCell F ∗ hnCtxt arrayAssn parents P ∗
        hnCtxt arrayAssn sizes S ∗ junkCell R)
      (compareCom I J N Ri Rj D F P R)
      (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
        hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
        junkCell D ∗ junkCell F ∗ ufAssn Rel (P, S))
      R boolNatAssn
      (NRest.consume (mopPerCompare Rel i j) (compareCost parents i j)) := by
  have h := compareRawHnr I J N Ri Rj D F P S R Rel parents sizes i j hW hAlpha
  rw [compareAbs_eq Rel hAlpha] at h
  have hcast :
      hnRefine (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
          hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
          junkCell D ∗ junkCell F ∗ hnCtxt arrayAssn parents P ∗
          hnCtxt arrayAssn sizes S ∗ junkCell R)
        (compareCom I J N Ri Rj D F P R)
        (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
          hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
          junkCell D ∗ junkCell F ∗ ufAssn Rel (P, S))
        R boolNatAssn
        (NRest.consume (NRest.returnT (perCompareB Rel i j))
          (compareCost parents i j)) := by
    refine hnRefine_res_cast' h ?_
    exact entails_refl _
  simpa only [mopPerCompare_eq] using hcast

theorem compare_height_bounds (hW : UfArrays.Wf (parents, sizes))
    (hi : i < parents.length) (hj : j < parents.length) :
    let parentsI := compressPath parents i
    heightOf parents i ≤ heightUb parents.length ∧
      compressSteps parents i ≤ heightUb parents.length ∧
      heightOf parentsI j ≤ heightUb parents.length ∧
      compressSteps parentsI j ≤ heightUb parents.length := by
  dsimp only
  let parentsI := compressPath parents i
  have hpresI := compressPath_preserves hW hi
  have hWI : UfArrays.Wf (parentsI, sizes) := by simpa [parentsI] using hpresI.2
  have hlen : parentsI.length = parents.length := by
    rw [hWI.2.1, hW.2.1]
  have hjI : j < parentsI.length := by simpa [hlen] using hj
  have hiUb := heightOfLeHeightUb hW.2.2 hW.1 hi
  have hjUb := heightOfLeHeightUb hWI.2.2 hWI.1 hjI
  rw [hlen] at hjUb
  exact ⟨hiUb, (compressSteps_le_height parents i).trans hiUb,
    hjUb, (compressSteps_le_height parentsI j).trans hjUb⟩

/-! ## Final timed implementation interface -/

noncomputable def perSize (Rel : Per ℕ) : ℕ :=
  by
    classical
    exact if h : ∃ n, relDomain Rel = Set.Iio n then Nat.find h else 0

private theorem Iio_nat_injective {a b : ℕ}
    (h : (Set.Iio a : Set ℕ) = Set.Iio b) : a = b := by
  apply le_antisymm
  · by_contra hn
    have hba : b < a := Nat.lt_of_not_ge hn
    have hb : b ∈ (Set.Iio a : Set ℕ) := hba
    rw [h] at hb
    exact (Nat.lt_irrefl b hb)
  · by_contra hn
    have hab : a < b := Nat.lt_of_not_ge hn
    have ha : a ∈ (Set.Iio b : Set ℕ) := hab
    rw [← h] at ha
    exact (Nat.lt_irrefl a ha)

theorem perSize_eq_length (Rel : Per ℕ) (hAlpha : ufaAlpha parents = Rel) :
    perSize Rel = parents.length := by
  classical
  have hdom : relDomain Rel = Set.Iio parents.length := by
    rw [← hAlpha, ufaAlphaDomain]
  have hex : ∃ n, relDomain Rel = Set.Iio n := ⟨parents.length, hdom⟩
  rw [perSize, dif_pos hex]
  exact Iio_nat_injective ((Nat.find_spec hex).symm.trans hdom)

theorem findCost_mono (hab : a ≤ b) : findCost a ≤ findCost b := by
  intro currency
  simp only [findCost, findRestCost, ACost.toFun_add, ACost.toFun_nsmul]
  exact add_le_add le_rfl
    (add_le_add (nsmul_le_nsmul_left bot_le hab)
      (nsmul_le_nsmul_left bot_le (Nat.add_le_add_right hab 1)))

theorem compressCost_mono (hab : a ≤ b) : compressCost a ≤ compressCost b := by
  intro currency
  simp only [compressCost, compressRestCost, ACost.toFun_add, ACost.toFun_nsmul]
  exact add_le_add le_rfl
    (add_le_add (nsmul_le_nsmul_left bot_le hab)
      (nsmul_le_nsmul_left bot_le (Nat.add_le_add_right hab 1)))

noncomputable def repCompressTime (n : ℕ) : ECost :=
  2 • irUnit Currency.copy + findCost (heightUb n) + compressCost (heightUb n)

noncomputable def ufCompareTime (n : ℕ) : ECost :=
  2 • irUnit Currency.ite + 2 • repCompressTime n + rootsEqCost

noncomputable def ufUnionTime (n : ℕ) : ECost :=
  2 • irUnit Currency.copy + 2 • findCost (heightUb n) +
    (irUnit Currency.ite + 2 • irUnit Currency.aget + irUnit Currency.ite +
      2 • irUnit Currency.aset + irUnit Currency.add + irUnit Currency.skip)

theorem unionRootsCost_le_time :
    unionRootsCost ri rj ≤
      irUnit Currency.ite + 2 • irUnit Currency.aget + irUnit Currency.ite +
        2 • irUnit Currency.aset + irUnit Currency.add + irUnit Currency.skip := by
  intro currency
  by_cases h : ri = rj
  · rw [unionRootsCost, if_pos h]
    calc
      (irUnit Currency.ite + irUnit Currency.skip).toFun currency ≤
          ((irUnit Currency.ite + irUnit Currency.skip) +
            (2 • irUnit Currency.aget + irUnit Currency.ite +
              2 • irUnit Currency.aset + irUnit Currency.add)).toFun currency := by
            rw [ACost.toFun_add]
            exact le_self_add
      _ = (irUnit Currency.ite + 2 • irUnit Currency.aget + irUnit Currency.ite +
          2 • irUnit Currency.aset + irUnit Currency.add +
          irUnit Currency.skip).toFun currency := by
            congr 1
            ac_rfl
  · rw [unionRootsCost, if_neg h]

theorem repCompressCost_le_time (hW : UfArrays.Wf (parents, sizes))
    (hi : i < parents.length) :
    repCompressCost parents i ≤ repCompressTime parents.length := by
  unfold repCompressCost repCompressTime
  exact add_le_add
    (add_le_add le_rfl
      (findCost_mono (heightOfLeHeightUb hW.2.2 hW.1 hi)))
    (compressCost_mono
      ((compressSteps_le_height parents i).trans
        (heightOfLeHeightUb hW.2.2 hW.1 hi)))

theorem compareCost_le_time (hW : UfArrays.Wf (parents, sizes))
    (hi : i < parents.length) (hj : j < parents.length) :
    compareCost parents i j ≤ ufCompareTime parents.length := by
  let parentsI := compressPath parents i
  have hpresI := compressPath_preserves hW hi
  have hWI : UfArrays.Wf (parentsI, sizes) := by simpa [parentsI] using hpresI.2
  have hlen : parentsI.length = parents.length := by
    rw [hWI.2.1, hW.2.1]
  have hjI : j < parentsI.length := by simpa [hlen] using hj
  rw [compareCost_eq_phases hi hj]
  have hfirst := repCompressCost_le_time hW hi
  have hsecond := repCompressCost_le_time hWI hjI
  rw [hlen] at hsecond
  calc
    2 • irUnit Currency.ite + repCompressCost parents i +
        repCompressCost parentsI j + rootsEqCost ≤
      2 • irUnit Currency.ite + repCompressTime parents.length +
        repCompressTime parents.length + rootsEqCost :=
          add_le_add (add_le_add
            (add_le_add le_rfl hfirst) hsecond) le_rfl
    _ = ufCompareTime parents.length := by
      unfold ufCompareTime
      simp only [two_nsmul]
      ac_rfl

theorem unionCost_le_time (hW : UfArrays.Wf (parents, sizes))
    (hi : i < parents.length) (hj : j < parents.length) :
    unionCost parents i j ≤ ufUnionTime parents.length := by
  rw [unionCost_eq_phases]
  unfold ufUnionTime
  have hiCost := findCost_mono (heightOfLeHeightUb hW.2.2 hW.1 hi)
  have hjCost := findCost_mono (heightOfLeHeightUb hW.2.2 hW.1 hj)
  calc
    2 • irUnit Currency.copy + findCost (heightOf parents i) +
        findCost (heightOf parents j) +
          unionRootsCost (repOf parents i) (repOf parents j) ≤
      2 • irUnit Currency.copy + findCost (heightUb parents.length) +
        findCost (heightUb parents.length) +
          (irUnit Currency.ite + 2 • irUnit Currency.aget + irUnit Currency.ite +
            2 • irUnit Currency.aset + irUnit Currency.add + irUnit Currency.skip) :=
        add_le_add (add_le_add (add_le_add le_rfl hiCost) hjCost)
          unionRootsCost_le_time
    _ = ufUnionTime parents.length := by
      unfold ufUnionTime
      simp only [two_nsmul]
      ac_rfl

theorem mem_relDomain_iff (Rel : Per ℕ) (hAlpha : ufaAlpha parents = Rel) :
    i ∈ relDomain Rel ↔ i < parents.length := by
  rw [← hAlpha, ufaAlphaDomain]
  rfl

theorem ufInitMop_eq :
    ufInitMop n = NRest.consume (mopPerInit n) (ufInitCost n) := rfl

theorem hnr_ufInit_interface (n : ℕ) (i v P S oneVal oneInc NP NS : String) :
    hnRefine (junkArrayOfLen n P ∗ junkArrayOfLen n S ∗ junkCell i ∗ junkCell v ∗
        hnCtxt natAssn 1 oneVal ∗ hnCtxt natAssn 1 oneInc ∗
        hnCtxt natAssn n NP ∗ hnCtxt natAssn n NS)
      (ufInitCom i v P S oneVal oneInc NP NS)
      (junkCell i ∗ junkCell v ∗ hnCtxt natAssn 1 oneVal ∗
        hnCtxt natAssn 1 oneInc ∗ hnCtxt natAssn n NP ∗ hnCtxt natAssn n NS)
      (P, S) ufAssn
      (NRest.consume (mopPerInit n) (ufInitCost n)) := by
  rw [← ufInitMop_eq]
  exact hnr_ufInit n i v P S oneVal oneInc NP NS

theorem hnr_ufUnion_domain (I J Ri Rj D Si Sj Total P S : String)
    (Rel : Per ℕ) (parents sizes : List ℕ) (i j : ℕ)
    (hW : UfArrays.Wf (parents, sizes)) (hAlpha : ufaAlpha parents = Rel)
    (hi : i ∈ relDomain Rel) (hj : j ∈ relDomain Rel) :
    hnRefine (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell Ri ∗
        junkCell Rj ∗ junkCell D ∗ junkCell Si ∗ junkCell Sj ∗
        junkCell Total ∗ hnCtxt arrayAssn parents P ∗ hnCtxt arrayAssn sizes S)
      (unionCom I J Ri Rj D Si Sj Total P S)
      (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell Ri ∗
        junkCell Rj ∗ junkCell D ∗ junkCell Si ∗ junkCell Sj ∗ junkCell Total)
      (P, S) ufAssn
      (NRest.consume (mopPerUnion Rel i j) (unionCost parents i j)) := by
  exact hnr_ufUnion I J Ri Rj D Si Sj Total P S Rel parents sizes i j hW hAlpha
    ((mem_relDomain_iff Rel hAlpha).mp hi) ((mem_relDomain_iff Rel hAlpha).mp hj)

theorem compareCost_le_domain_time (Rel : Per ℕ)
    (hW : UfArrays.Wf (parents, sizes)) (hAlpha : ufaAlpha parents = Rel)
    (hi : i ∈ relDomain Rel) (hj : j ∈ relDomain Rel) :
    compareCost parents i j ≤ ufCompareTime (perSize Rel) := by
  rw [perSize_eq_length Rel hAlpha]
  exact compareCost_le_time hW ((mem_relDomain_iff Rel hAlpha).mp hi)
    ((mem_relDomain_iff Rel hAlpha).mp hj)

theorem unionCost_le_domain_time (Rel : Per ℕ)
    (hW : UfArrays.Wf (parents, sizes)) (hAlpha : ufaAlpha parents = Rel)
    (hi : i ∈ relDomain Rel) (hj : j ∈ relDomain Rel) :
    unionCost parents i j ≤ ufUnionTime (perSize Rel) := by
  rw [perSize_eq_length Rel hAlpha]
  exact unionCost_le_time hW ((mem_relDomain_iff Rel hAlpha).mp hi)
    ((mem_relDomain_iff Rel hAlpha).mp hj)

def UfInitInterfaceRule : Prop :=
  ∀ (n : ℕ) (i v P S oneVal oneInc NP NS : String),
    hnRefine (junkArrayOfLen n P ∗ junkArrayOfLen n S ∗ junkCell i ∗ junkCell v ∗
        hnCtxt natAssn 1 oneVal ∗ hnCtxt natAssn 1 oneInc ∗
        hnCtxt natAssn n NP ∗ hnCtxt natAssn n NS)
      (ufInitCom i v P S oneVal oneInc NP NS)
      (junkCell i ∗ junkCell v ∗ hnCtxt natAssn 1 oneVal ∗
        hnCtxt natAssn 1 oneInc ∗ hnCtxt natAssn n NP ∗ hnCtxt natAssn n NS)
      (P, S) ufAssn (NRest.consume (mopPerInit n) (ufInitCost n))

def UfCompareInterfaceRule : Prop :=
  ∀ (I J N Ri Rj D F P S R : String) (Rel : Per ℕ)
    (parents sizes : List ℕ) (i j : ℕ),
    UfArrays.Wf (parents, sizes) → ufaAlpha parents = Rel →
    hnRefine (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
        hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
        junkCell D ∗ junkCell F ∗ hnCtxt arrayAssn parents P ∗
        hnCtxt arrayAssn sizes S ∗ junkCell R)
      (compareCom I J N Ri Rj D F P R)
      (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗
        hnCtxt natAssn parents.length N ∗ junkCell Ri ∗ junkCell Rj ∗
        junkCell D ∗ junkCell F ∗ ufAssn Rel (P, S))
      R boolNatAssn (NRest.consume (mopPerCompare Rel i j) (compareCost parents i j))

def UfUnionInterfaceRule : Prop :=
  ∀ (I J Ri Rj D Si Sj Total P S : String) (Rel : Per ℕ)
    (parents sizes : List ℕ) (i j : ℕ),
    UfArrays.Wf (parents, sizes) → ufaAlpha parents = Rel →
      i ∈ relDomain Rel → j ∈ relDomain Rel →
    hnRefine (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell Ri ∗
        junkCell Rj ∗ junkCell D ∗ junkCell Si ∗ junkCell Sj ∗
        junkCell Total ∗ hnCtxt arrayAssn parents P ∗ hnCtxt arrayAssn sizes S)
      (unionCom I J Ri Rj D Si Sj Total P S)
      (hnCtxt natAssn i I ∗ hnCtxt natAssn j J ∗ junkCell Ri ∗
        junkCell Rj ∗ junkCell D ∗ junkCell Si ∗ junkCell Sj ∗ junkCell Total)
      (P, S) ufAssn (NRest.consume (mopPerUnion Rel i j) (unionCost parents i j))

structure TimedUnionFindImplementation : Prop where
  initRule : UfInitInterfaceRule
  compareRule : UfCompareInterfaceRule
  unionRule : UfUnionInterfaceRule
  compareBound : ∀ (Rel : Per ℕ) (parents sizes : List ℕ) (i j : ℕ),
    UfArrays.Wf (parents, sizes) → ufaAlpha parents = Rel →
      i ∈ relDomain Rel → j ∈ relDomain Rel →
      compareCost parents i j ≤ ufCompareTime (perSize Rel)
  unionBound : ∀ (Rel : Per ℕ) (parents sizes : List ℕ) (i j : ℕ),
    UfArrays.Wf (parents, sizes) → ufaAlpha parents = Rel →
      i ∈ relDomain Rel → j ∈ relDomain Rel →
      unionCost parents i j ≤ ufUnionTime (perSize Rel)
  logarithmicHeight :
    (fun n : ℕ => ((heightUb n : ℕ) : ℝ)) =Θ[Filter.atTop]
      (fun n => Real.log (n : ℝ))

theorem unionFindTimedImplementation : TimedUnionFindImplementation where
  initRule := hnr_ufInit_interface
  compareRule := fun I J N Ri Rj D F P S R Rel parents sizes i j hW hAlpha =>
    hnr_ufCompare I J N Ri Rj D F P S R Rel parents sizes i j hW hAlpha
  unionRule := fun I J Ri Rj D Si Sj Total P S Rel parents sizes i j hW hAlpha hi hj =>
    hnr_ufUnion_domain I J Ri Rj D Si Sj Total P S Rel parents sizes i j
      hW hAlpha hi hj
  compareBound := fun Rel parents sizes i j hW hAlpha hi hj =>
    compareCost_le_domain_time (parents := parents) (sizes := sizes) (i := i) (j := j)
      Rel hW hAlpha hi hj
  unionBound := fun Rel parents sizes i j hW hAlpha hi hj =>
    unionCost_le_domain_time (parents := parents) (sizes := sizes) (i := i) (j := j)
      Rel hW hAlpha hi hj
  logarithmicHeight := heightUbThetaLog

/-! ## Exact vector-cost and execution gates for the landed loops -/

private theorem twoRootsInvar : ufaInvar [0, 1] := by
  intro i hi
  norm_num at hi
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · refine ⟨by decide, 0, 1, ?_⟩; decide
  · refine ⟨by decide, 1, 1, ?_⟩; decide

private theorem twoRootsRep0 : repOf [0, 1] 0 = 0 := by
  exact repOfRefl twoRootsInvar (by decide) (by decide)

private theorem twoRootsRep1 : repOf [0, 1] 1 = 1 := by
  exact repOfRefl twoRootsInvar (by decide) (by decide)

theorem unionArrays_left_orientation :
    unionArrays ([0, 1], [1, 2]) 0 1 = ([1, 1], [1, 3]) := by
  simp [unionArrays, twoRootsRep0, twoRootsRep1, unionSizes, ufaUnion]

theorem unionArrays_right_orientation :
    unionArrays ([0, 1], [2, 1]) 0 1 = ([0, 0], [3, 1]) := by
  simp [unionArrays, twoRootsRep0, twoRootsRep1, unionSizes, ufaUnion]

theorem unionArrays_same_root_noop :
    unionArrays ([0, 1], [1, 1]) 0 0 = ([0, 1], [1, 1]) := by
  simp [unionArrays, twoRootsRep0]

theorem unionRootsAbs_left_orientation :
    unionRootsAbs [0, 1] [1, 2] 0 1 =
      NRest.consume (NRest.returnT ([1, 1], [1, 3])) (unionRootsCost 0 1) := by
  simpa using unionRootsAbs_eq (parents := [0, 1]) (sizes := [1, 2])
    (ri := 0) (rj := 1) (by decide) (by decide) (by decide)

theorem unionRootsAbs_right_orientation :
    unionRootsAbs [0, 1] [2, 1] 0 1 =
      NRest.consume (NRest.returnT ([0, 0], [3, 1])) (unionRootsCost 0 1) := by
  simpa using unionRootsAbs_eq (parents := [0, 1]) (sizes := [2, 1])
    (ri := 0) (rj := 1) (by decide) (by decide) (by decide)

theorem unionRootsAbs_same_root_noop :
    unionRootsAbs [0, 1] [1, 1] 0 0 =
      NRest.consume (NRest.returnT ([0, 1], [1, 1])) (unionRootsCost 0 0) := by
  simpa using unionRootsAbs_eq (parents := [0, 1]) (sizes := [1, 1])
    (ri := 0) (rj := 0) (by decide) (by decide) (by decide)

theorem unionRootsCost_same_ite :
    (unionRootsCost 0 0).toFun Currency.ite = 1 := by decide +kernel
theorem unionRootsCost_same_aset :
    (unionRootsCost 0 0).toFun Currency.aset = 0 := by decide +kernel
theorem unionRootsCost_distinct_ite :
    (unionRootsCost 0 1).toFun Currency.ite = 2 := by decide +kernel
theorem unionRootsCost_distinct_aget :
    (unionRootsCost 0 1).toFun Currency.aget = 2 := by decide +kernel
theorem unionRootsCost_distinct_aset :
    (unionRootsCost 0 1).toFun Currency.aset = 2 := by decide +kernel
theorem unionRootsCost_distinct_add :
    (unionRootsCost 0 1).toFun Currency.add = 1 := by decide +kernel

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

private theorem singletonInvar : ufaInvar [0] := by
  intro i hi
  norm_num at hi
  have hi0 : i = 0 := by omega
  subst i
  refine ⟨by decide, 0, 1, ?_⟩
  decide

private theorem compressedInvar : ufaInvar [0, 0, 0] := by
  intro i hi
  norm_num at hi
  have his : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases his with rfl | rfl | rfl
  · refine ⟨by decide, 0, 1, ?_⟩; decide
  · refine ⟨by decide, 0, 2, ?_⟩; decide
  · refine ⟨by decide, 0, 2, ?_⟩; decide

private theorem chainInvar : ufaInvar [0, 0, 1] := by
  intro i hi
  norm_num at hi
  have his : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases his with rfl | rfl | rfl
  · refine ⟨by decide, 0, 1, ?_⟩; decide
  · refine ⟨by decide, 0, 2, ?_⟩; decide
  · refine ⟨by decide, 0, 3, ?_⟩; decide

theorem height_singleton : heightOf [0] 0 = 0 := by
  exact heightOfRoot singletonInvar (by decide) (by decide)

theorem height_compressed : heightOf [0, 0, 0] 2 = 1 := by
  rw [heightOfStep compressedInvar (by decide) (by decide),
    heightOfRoot compressedInvar (by decide) (by decide)]

theorem height_chain : heightOf [0, 0, 1] 2 = 2 := by
  rw [heightOfStep chainInvar (by decide) (by decide),
    heightOfStep chainInvar (by decide) (by decide),
    heightOfRoot chainInvar (by decide) (by decide)]

theorem findCost0_aget : (findCost 0).toFun Currency.aget = 1 := by decide +kernel
theorem findCost0_xor : (findCost 0).toFun Currency.xor = 1 := by decide +kernel
theorem findCost0_skip : (findCost 0).toFun Currency.skip = 2 := by decide +kernel
theorem findCost0_while : (findCost 0).toFun Currency.«while» = 1 := by decide +kernel

theorem findCost1_aget : (findCost 1).toFun Currency.aget = 2 := by decide +kernel
theorem findCost1_xor : (findCost 1).toFun Currency.xor = 3 := by decide +kernel
theorem findCost1_skip : (findCost 1).toFun Currency.skip = 4 := by decide +kernel
theorem findCost1_while : (findCost 1).toFun Currency.«while» = 2 := by decide +kernel

theorem findCost2_aget : (findCost 2).toFun Currency.aget = 3 := by decide +kernel
theorem findCost2_xor : (findCost 2).toFun Currency.xor = 5 := by decide +kernel
theorem findCost2_skip : (findCost 2).toFun Currency.skip = 6 := by decide +kernel
theorem findCost2_while : (findCost 2).toFun Currency.«while» = 3 := by decide +kernel

theorem singleton_cheaper_than_chain :
    (findCost 0).toFun Currency.«while» < (findCost 2).toFun Currency.«while» := by
  decide +kernel

theorem compressed_cheaper_than_chain :
    (findCost 1).toFun Currency.«while» < (findCost 2).toFun Currency.«while» := by
  decide +kernel

theorem findProg_singleton :
    findProg [0] 0 =
      NRest.consume (NRest.returnT (0, (0, [0]))) (findCost 0) := by
  have h := findProg_value singletonInvar (x := 0) (parents := [0]) (by decide)
  rw [height_singleton, repOfRefl singletonInvar (by decide) (by decide)] at h
  exact h

theorem findProg_compressed :
    findProg [0, 0, 0] 2 =
      NRest.consume (NRest.returnT (0, (0, [0, 0, 0]))) (findCost 1) := by
  have h := findProg_value compressedInvar (x := 2) (parents := [0, 0, 0]) (by decide)
  rw [height_compressed, repOfStep compressedInvar (by decide) (by decide),
    repOfRefl compressedInvar (by decide) (by decide)] at h
  exact h

theorem findProg_chain :
    findProg [0, 0, 1] 2 =
      NRest.consume (NRest.returnT (0, (0, [0, 0, 1]))) (findCost 2) := by
  have h := findProg_value chainInvar (x := 2) (parents := [0, 0, 1]) (by decide)
  rw [height_chain, repOfStep chainInvar (by decide) (by decide),
    repOfStep chainInvar (by decide) (by decide),
    repOfRefl chainInvar (by decide) (by decide)] at h
  exact h

private theorem rep_compressed : repOf [0, 0, 0] 2 = 0 := by
  rw [repOfStep compressedInvar (by decide) (by decide),
    repOfRefl compressedInvar (by decide) (by decide)]
  decide

private theorem rep_chain : repOf [0, 0, 1] 2 = 0 := by
  rw [repOfStep chainInvar (by decide) (by decide),
    repOfStep chainInvar (by decide) (by decide),
    repOfRefl chainInvar (by decide) (by decide)]
  decide

theorem compressExec_compressed :
    compressExec 0 1 (compressState 0 [0, 0, 0] 2) =
      (0, (0, [0, 0, 0])) := by
  decide +kernel

theorem compressExec_chain :
    compressExec 0 2 (compressState 0 [0, 0, 1] 2) =
      (0, (0, [0, 0, 0])) := by
  decide +kernel

theorem compressSteps_compressed : compressSteps [0, 0, 0] 2 = 1 := by
  rw [compressSteps, height_compressed, rep_compressed]
  decide +kernel

theorem compressSteps_chain : compressSteps [0, 0, 1] 2 = 2 := by
  rw [compressSteps, height_chain, rep_chain]
  decide +kernel

theorem compressPath_compressed : compressPath [0, 0, 0] 2 = [0, 0, 0] := by
  rw [compressPath, height_compressed, rep_compressed, compressExec_compressed]

theorem compressPath_chain : compressPath [0, 0, 1] 2 = [0, 0, 0] := by
  rw [compressPath, height_chain, rep_chain, compressExec_chain]

theorem compressCost1_aset : (compressCost 1).toFun Currency.aset = 1 := by
  decide +kernel
theorem compressCost1_aget : (compressCost 1).toFun Currency.aget = 1 := by
  decide +kernel
theorem compressCost1_copy : (compressCost 1).toFun Currency.copy = 1 := by
  decide +kernel
theorem compressCost1_xor : (compressCost 1).toFun Currency.xor = 2 := by
  decide +kernel
theorem compressCost1_skip : (compressCost 1).toFun Currency.skip = 4 := by
  decide +kernel
theorem compressCost1_while : (compressCost 1).toFun Currency.«while» = 2 := by
  decide +kernel

theorem compressCost2_aset : (compressCost 2).toFun Currency.aset = 2 := by
  decide +kernel
theorem compressCost2_aget : (compressCost 2).toFun Currency.aget = 2 := by
  decide +kernel
theorem compressCost2_copy : (compressCost 2).toFun Currency.copy = 2 := by
  decide +kernel
theorem compressCost2_xor : (compressCost 2).toFun Currency.xor = 3 := by
  decide +kernel
theorem compressCost2_skip : (compressCost 2).toFun Currency.skip = 6 := by
  decide +kernel
theorem compressCost2_while : (compressCost 2).toFun Currency.«while» = 3 := by
  decide +kernel

theorem compressed_compression_cheaper_than_chain :
    (compressCost 1).toFun Currency.«while» <
      (compressCost 2).toFun Currency.«while» := by
  decide +kernel

theorem compressProg_compressed :
    compressProg 0 [0, 0, 0] 2 =
      NRest.consume (NRest.returnT (0, (0, [0, 0, 0]))) (compressCost 1) := by
  have h := compressProg_value compressedInvar (x := 2) (parents := [0, 0, 0])
    (by decide)
  rw [rep_compressed, height_compressed, compressSteps_compressed,
    compressExec_compressed] at h
  exact h

theorem compressProg_chain :
    compressProg 0 [0, 0, 1] 2 =
      NRest.consume (NRest.returnT (0, (0, [0, 0, 0]))) (compressCost 2) := by
  have h := compressProg_value chainInvar (x := 2) (parents := [0, 0, 1])
    (by decide)
  rw [rep_chain, height_chain, compressSteps_chain, compressExec_chain] at h
  exact h

private theorem compareForestInvar : ufaInvar [0, 0, 2] := by
  intro i hi
  norm_num at hi
  have his : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases his with rfl | rfl | rfl
  · refine ⟨by decide, 0, 1, ?_⟩; decide
  · refine ⟨by decide, 0, 2, ?_⟩; decide
  · refine ⟨by decide, 2, 1, ?_⟩; decide

private theorem compareForest_rep0 : repOf [0, 0, 2] 0 = 0 := by
  exact repOfRefl compareForestInvar (by decide) (by decide)

private theorem compareForest_rep1 : repOf [0, 0, 2] 1 = 0 := by
  rw [repOfStep compareForestInvar (by decide) (by decide)]
  simpa using compareForest_rep0

private theorem compareForest_rep2 : repOf [0, 0, 2] 2 = 2 := by
  exact repOfRefl compareForestInvar (by decide) (by decide)

private theorem compareForest_height0 : heightOf [0, 0, 2] 0 = 0 := by
  exact heightOfRoot compareForestInvar (by decide) (by decide)

private theorem compareForest_height1 : heightOf [0, 0, 2] 1 = 1 := by
  rw [heightOfStep compareForestInvar (by decide) (by decide)]
  simpa using congrArg Nat.succ compareForest_height0

private theorem compareForest_height2 : heightOf [0, 0, 2] 2 = 0 := by
  exact heightOfRoot compareForestInvar (by decide) (by decide)

private theorem compareForestRank : rankInvar [0, 0, 2] [2, 0, 1] := by
  constructor
  · decide
  constructor
  · decide
  · intro i hi hroot
    norm_num at hi
    have his : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases his with rfl | rfl | rfl
    · have hh : hOf [0, 0, 2] 0 ≤ 1 := by
        unfold hOf
        apply Finset.sup_le
        intro j hj
        simp only [Finset.mem_range] at hj
        norm_num at hj
        have hjs : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases hjs with rfl | rfl | rfl
        · simp [compareForest_rep0, compareForest_height0]
        · simp [compareForest_rep1, compareForest_height1]
        · simp [compareForest_rep2]
      exact (Nat.pow_le_pow_right (by omega) hh).trans (by decide)
    · norm_num at hroot
    · have hh : hOf [0, 0, 2] 2 ≤ 0 := by
        unfold hOf
        apply Finset.sup_le
        intro j hj
        simp only [Finset.mem_range] at hj
        norm_num at hj
        have hjs : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases hjs with rfl | rfl | rfl
        · simp [compareForest_rep0]
        · simp [compareForest_rep1]
        · simp [compareForest_rep2, compareForest_height2]
      exact (Nat.pow_le_pow_right (by omega) hh).trans (by decide)

private theorem compareForestWf : UfArrays.Wf ([0, 0, 2], [2, 0, 1]) :=
  ⟨compareForestInvar, by decide, compareForestRank⟩

private theorem compareForest_path0 : compressPath [0, 0, 2] 0 = [0, 0, 2] := by
  rw [compressPath, compareForest_height0, compareForest_rep0]
  rfl

private theorem compareForest_path1 : compressPath [0, 0, 2] 1 = [0, 0, 2] := by
  rw [compressPath, compareForest_height1, compareForest_rep1]
  decide +kernel

private theorem compareForest_steps0 : compressSteps [0, 0, 2] 0 = 0 := by
  rw [compressSteps, compareForest_height0, compareForest_rep0]
  rfl

private theorem compareForest_steps1 : compressSteps [0, 0, 2] 1 = 1 := by
  rw [compressSteps, compareForest_height1, compareForest_rep1]
  decide +kernel

private theorem compareForest_steps2 : compressSteps [0, 0, 2] 2 = 0 := by
  rw [compressSteps, compareForest_height2, compareForest_rep2]
  rfl

theorem compare_true_forest :
    perCompareB (ufaAlpha [0, 0, 2]) 0 1 = true := by
  classical
  unfold perCompareB perCompare
  rw [decide_eq_true_eq]
  exact (ufaFindCorrect compareForestInvar (by decide) (by decide)).mp (by
    rw [compareForest_rep0, compareForest_rep1])

theorem compare_false_forest :
    perCompareB (ufaAlpha [0, 0, 2]) 1 2 = false := by
  classical
  unfold perCompareB perCompare
  rw [decide_eq_false_iff_not]
  intro hmem
  have heq := (ufaFindCorrect compareForestInvar (by decide) (by decide)).mpr hmem
  rw [compareForest_rep1, compareForest_rep2] at heq
  omega

theorem compareAbs_true_forest :
    compareAbs (ufaAlpha [0, 0, 2]) [0, 0, 2] 0 1 =
      NRest.consume (NRest.returnT 1) (compareCost [0, 0, 2] 0 1) := by
  rw [compareAbs_eq (ufaAlpha [0, 0, 2]) rfl, compare_true_forest]
  rfl

theorem compareAbs_false_forest :
    compareAbs (ufaAlpha [0, 0, 2]) [0, 0, 2] 1 2 =
      NRest.consume (NRest.returnT 0) (compareCost [0, 0, 2] 1 2) := by
  rw [compareAbs_eq (ufaAlpha [0, 0, 2]) rfl, compare_false_forest]
  rfl

theorem compare_true_while_cost :
    (compareCost [0, 0, 2] 0 1).toFun Currency.«while» = 6 := by
  rw [compareCost_eq_phases (by decide) (by decide), compareForest_path0]
  simp only [repCompressCost, compareForest_height0, compareForest_height1,
    compareForest_steps0, compareForest_steps1]
  decide +kernel

theorem compare_false_while_cost :
    (compareCost [0, 0, 2] 1 2).toFun Currency.«while» = 6 := by
  rw [compareCost_eq_phases (by decide) (by decide), compareForest_path1]
  simp only [repCompressCost, compareForest_height1, compareForest_height2,
    compareForest_steps1, compareForest_steps2]
  decide +kernel

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

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.UnionFindTime.hnr_ufFind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_ufFind

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.UnionFindTime.hnr_ufCompress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_ufCompress

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.UnionFindTime.hnr_ufCompare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_ufCompare

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.UnionFindTime.hnr_ufUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_ufUnion

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.UnionFindTime.unionFindTimedImplementation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms unionFindTimedImplementation

end Lax13Proofs.Refine.Sepref.Iicf.UnionFindTime
