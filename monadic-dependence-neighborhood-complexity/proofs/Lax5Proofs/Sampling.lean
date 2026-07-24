import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Lemma 12 of DMMPT26 — Lemma 10 of arXiv:2311.18740 (FOCS'24): in a
bipartite graph with no isolated vertices there are subsets `X' ⊆ X`
and `Y' ⊆ Y` with `|Y'| ≥ |Y| / (150 (ln |X| + 1))` such that every
vertex of `Y'` has exactly one neighbor in `X'`.

Stated for an abstract relation between two finsets — the machinery
applies it to the merge relation `VPos`/`VNeg` between a vertex set and
a family of traces. The paper's denominator `150 ln |X|` is replaced by
`150 (ln |X| + 1)`, which the same proof delivers and which remains
meaningful at `|X| = 1` (there the statement is witnessed by
`X' := X`, `Y' := Y`).

The proof simplifies the FOCS'24 constants: bucket the `Y`-degrees by
powers of `2` (at most `2 ln |X| + 1` nonempty buckets, so some bucket
`Y₀` carries that fraction of `Y`); for the bucket with degrees in
`[2^j, 2^(j+1))` sample each `x ∈ X` independently with probability
`p = 1/2^(j+1)`. A vertex of `Y₀` then keeps exactly one neighbor with
probability `deg·p·(1−p)^(deg−1) ≥ (1/2)·(1−1/M)^M ≥ (1/2)(1/8)` where
`M = 2^(j+1)`, using `(1+1/(M−1))^M ≤ e² < 8`. Expectation over the
finite cube (a weighted sum over `X.powerset`) yields a sample keeping
a `1/16` fraction of `Y₀`, hence a `1/(32(ln|X|+1))` fraction of `Y` —
comfortably inside the stated `150`.
-/

namespace Lax5Proofs.Sampling

open Finset

variable {α : Type*} [DecidableEq α]

/-- Binomial expansion over the powerset: the total weight of all
samples is `(p+q)^|X|`. -/
theorem sum_pow_mul_pow_sdiff (X : Finset α) (p q : ℝ) :
    ∑ S ∈ X.powerset, p ^ S.card * q ^ (X \ S).card = (p + q) ^ X.card := by
  calc ∑ S ∈ X.powerset, p ^ S.card * q ^ (X \ S).card
      = ∑ S ∈ X.powerset, (∏ _i ∈ S, p) * ∏ _i ∈ X \ S, q := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.prod_const, Finset.prod_const]
    _ = ∏ _i ∈ X, (p + q) := (Finset.prod_add _ _ _).symm
    _ = (p + q) ^ X.card := by rw [Finset.prod_const]

/-- Marginalization: the total weight of the samples with a prescribed
intersection `T` with `N` is the weight of `T` inside `N`. -/
theorem sum_weight_inter_eq {X N T : Finset α} (hN : N ⊆ X) (hT : T ⊆ N)
    {p q : ℝ} (hpq : p + q = 1) :
    ∑ S ∈ X.powerset.filter (fun S => S ∩ N = T),
      p ^ S.card * q ^ (X \ S).card =
      p ^ T.card * q ^ (N \ T).card := by
  calc ∑ S ∈ X.powerset.filter (fun S => S ∩ N = T),
        p ^ S.card * q ^ (X \ S).card
      = ∑ S' ∈ (X \ N).powerset,
          p ^ T.card * q ^ (N \ T).card *
            (p ^ S'.card * q ^ ((X \ N) \ S').card) := by
        refine Finset.sum_nbij' (i := fun S => S \ N) (j := fun S' => T ∪ S')
          ?_ ?_ ?_ ?_ ?_
        · intro S hS
          obtain ⟨hSX, -⟩ := Finset.mem_filter.1 hS
          rw [Finset.mem_powerset] at hSX ⊢
          exact Finset.sdiff_subset_sdiff hSX (Finset.Subset.refl N)
        · intro S' hS'
          rw [Finset.mem_powerset] at hS'
          refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 ?_, ?_⟩
          · exact Finset.union_subset (hT.trans hN)
              (hS'.trans Finset.sdiff_subset)
          · ext x
            simp only [Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨hxT | hxS', hxN⟩
              · exact hxT
              · exact absurd hxN (Finset.mem_sdiff.1 (hS' hxS')).2
            · intro hxT
              exact ⟨Or.inl hxT, hT hxT⟩
        · intro S hS
          obtain ⟨hSX, hST⟩ := Finset.mem_filter.1 hS
          ext x
          simp only [Finset.mem_union, Finset.mem_sdiff]
          constructor
          · rintro (hxT | ⟨hxS, -⟩)
            · have hx : x ∈ S ∩ N := by rw [hST]; exact hxT
              exact (Finset.mem_inter.1 hx).1
            · exact hxS
          · intro hxS
            by_cases hxN : x ∈ N
            · refine Or.inl ?_
              rw [← hST]
              exact Finset.mem_inter.2 ⟨hxS, hxN⟩
            · exact Or.inr ⟨hxS, hxN⟩
        · intro S' hS'
          rw [Finset.mem_powerset] at hS'
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨hxT | hxS', hxN⟩
            · exact absurd (hT hxT) hxN
            · exact hxS'
          · intro hxS'
            exact ⟨Or.inr hxS', (Finset.mem_sdiff.1 (hS' hxS')).2⟩
        · intro S hS
          obtain ⟨hSX, hST⟩ := Finset.mem_filter.1 hS
          rw [Finset.mem_powerset] at hSX
          have hcard1 : S.card = T.card + (S \ N).card := by
            rw [← Finset.card_union_of_disjoint (by
              rw [Finset.disjoint_left]
              intro x hxT hxS
              exact (Finset.mem_sdiff.1 hxS).2 (hT hxT))]
            congr 1
            ext x
            simp only [Finset.mem_union, Finset.mem_sdiff]
            constructor
            · intro hxS
              by_cases hxN : x ∈ N
              · refine Or.inl ?_
                rw [← hST]
                exact Finset.mem_inter.2 ⟨hxS, hxN⟩
              · exact Or.inr ⟨hxS, hxN⟩
            · rintro (hxT | ⟨hxS, -⟩)
              · have hx : x ∈ S ∩ N := by rw [hST]; exact hxT
                exact (Finset.mem_inter.1 hx).1
              · exact hxS
          have hcard2 : (X \ S).card = (N \ T).card + ((X \ N) \ (S \ N)).card := by
            rw [← Finset.card_union_of_disjoint (by
              rw [Finset.disjoint_left]
              intro x hx1 hx2
              exact (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hx2).1).2
                (Finset.mem_sdiff.1 hx1).1)]
            congr 1
            ext x
            simp only [Finset.mem_union, Finset.mem_sdiff]
            constructor
            · rintro ⟨hxX, hxS⟩
              by_cases hxN : x ∈ N
              · refine Or.inl ⟨hxN, fun hxT => hxS ?_⟩
                have hx : x ∈ S ∩ N := by rw [hST]; exact hxT
                exact (Finset.mem_inter.1 hx).1
              · exact Or.inr ⟨⟨hxX, hxN⟩, fun h => hxS h.1⟩
            · rintro (⟨hxN, hxT⟩ | ⟨⟨hxX, hxN⟩, hxSN⟩)
              · refine ⟨hN hxN, fun hxS => hxT ?_⟩
                rw [← hST]
                exact Finset.mem_inter.2 ⟨hxS, hxN⟩
              · exact ⟨hxX, fun hxS => hxSN ⟨hxS, hxN⟩⟩
          rw [hcard1, hcard2, pow_add, pow_add]
          ring
    _ = p ^ T.card * q ^ (N \ T).card *
          ∑ S' ∈ (X \ N).powerset, p ^ S'.card * q ^ ((X \ N) \ S').card := by
        rw [Finset.mul_sum]
    _ = p ^ T.card * q ^ (N \ T).card := by
        rw [sum_pow_mul_pow_sdiff, hpq, one_pow, mul_one]

/-- The total weight of the samples meeting `N` in exactly one element
is `|N| · p · q^(|N|−1)`. -/
theorem sum_weight_inter_card_one {X N : Finset α} (hN : N ⊆ X)
    {p q : ℝ} (hpq : p + q = 1) :
    ∑ S ∈ X.powerset.filter (fun S => (S ∩ N).card = 1),
      p ^ S.card * q ^ (X \ S).card =
      (N.card : ℝ) * (p * q ^ (N.card - 1)) := by
  have hsplit : X.powerset.filter (fun S => (S ∩ N).card = 1) =
      N.biUnion fun x => X.powerset.filter (fun S => S ∩ N = {x}) := by
    ext S
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hSX, hcard⟩
      obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hcard
      have hxSN : x ∈ S ∩ N := hx ▸ Finset.mem_singleton_self x
      exact ⟨x, (Finset.mem_inter.1 hxSN).2, hSX, hx⟩
    · rintro ⟨x, hxN, hSX, hxS⟩
      exact ⟨hSX, by rw [hxS, Finset.card_singleton]⟩
  rw [hsplit, Finset.sum_biUnion (by
    intro x hx x' hx' hxx'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro S hS hS'
    exact hxx' (Finset.singleton_injective
      (((Finset.mem_filter.1 hS).2).symm.trans (Finset.mem_filter.1 hS').2)))]
  calc ∑ x ∈ N, ∑ S ∈ X.powerset.filter (fun S => S ∩ N = {x}),
        p ^ S.card * q ^ (X \ S).card
      = ∑ x ∈ N, p * q ^ (N.card - 1) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hNx : (N \ {x}).card = N.card - 1 := by
          rw [Finset.card_sdiff, Finset.singleton_inter_of_mem hx,
            Finset.card_singleton]
        rw [sum_weight_inter_eq hN (Finset.singleton_subset_iff.2 hx) hpq,
          Finset.card_singleton, pow_one, hNx]
    _ = (N.card : ℝ) * (p * q ^ (N.card - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- `(1 − 1/M)^M ≥ 1/8` for natural `M ≥ 2`, via
`(1 + 1/(M−1))^M ≤ e² < 8`. -/
theorem one_div_eight_le_pow {M : ℕ} (hM : 2 ≤ M) :
    (1 / 8 : ℝ) ≤ (1 - 1 / (M : ℝ)) ^ M := by
  have hm : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hm0 : (M : ℝ) ≠ 0 := by linarith
  have hm10 : (M : ℝ) - 1 ≠ 0 := by
    intro h
    have : (M : ℝ) = 1 := by linarith
    linarith
  have hm1pos : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hbase : (0 : ℝ) < 1 + 1 / ((M : ℝ) - 1) := by
    have := one_div_pos.2 hm1pos
    linarith
  have h1 : 1 + 1 / ((M : ℝ) - 1) ≤ Real.exp (1 / ((M : ℝ) - 1)) := by
    have := Real.add_one_le_exp (1 / ((M : ℝ) - 1))
    linarith
  have h2 : (1 + 1 / ((M : ℝ) - 1)) ^ M ≤
      Real.exp (1 / ((M : ℝ) - 1)) ^ M :=
    pow_le_pow_left₀ hbase.le h1 M
  have h3 : Real.exp (1 / ((M : ℝ) - 1)) ^ M =
      Real.exp ((M : ℝ) / ((M : ℝ) - 1)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [mul_one_div]
  have h4 : (M : ℝ) / ((M : ℝ) - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have h6 : Real.exp 2 < 8 := by
    have h := Real.exp_one_lt_d9
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos 1]
  have h7 : (1 + 1 / ((M : ℝ) - 1)) ^ M ≤ 8 := by
    calc (1 + 1 / ((M : ℝ) - 1)) ^ M
        ≤ Real.exp ((M : ℝ) / ((M : ℝ) - 1)) := h3 ▸ h2
      _ ≤ Real.exp 2 := Real.exp_le_exp.2 h4
      _ ≤ 8 := h6.le
  have h9 : 1 + 1 / ((M : ℝ) - 1) = (M : ℝ) / ((M : ℝ) - 1) := by
    field_simp
    ring
  have heq : 1 - 1 / (M : ℝ) = 1 / (1 + 1 / ((M : ℝ) - 1)) := by
    rw [h9, one_div_div, sub_div, div_self hm0]
  have hTpos : (0 : ℝ) < (1 + 1 / ((M : ℝ) - 1)) ^ M := pow_pos hbase M
  rw [heq, div_pow, one_pow, div_le_div_iff₀ (by norm_num) hTpos]
  linarith

/-- Lemma 12 of DMMPT26: unique-neighbor subsets in bipartite graphs
without isolated vertices. -/
theorem exists_unique_neighbor_subsets {α β : Type*}
    (X : Finset α) (Y : Finset β) (R : α → β → Prop)
    (hX : ∀ x ∈ X, ∃ y ∈ Y, R x y) (hY : ∀ y ∈ Y, ∃ x ∈ X, R x y) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y,
      (Y.card : ℝ) ≤ 150 * (Real.log X.card + 1) * Y'.card ∧
      ∀ y ∈ Y', ∃! x, x ∈ X' ∧ R x y := by
  classical
  rcases Y.eq_empty_or_nonempty with rfl | hYne
  · exact ⟨X, Finset.Subset.refl X, ∅, Finset.empty_subset _, by simp,
      fun y hy => absurd hy (Finset.notMem_empty y)⟩
  obtain ⟨y₀, hy₀⟩ := hYne
  obtain ⟨x₀, hx₀, -⟩ := hY y₀ hy₀
  have hX0 : X.card ≠ 0 := Finset.card_ne_zero_of_mem hx₀
  set deg : β → ℕ := fun y => (X.filter fun x => R x y).card with hdeg
  have hdegpos : ∀ y ∈ Y, deg y ≠ 0 := by
    intro y hy
    obtain ⟨x, hx, hR⟩ := hY y hy
    exact Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨hx, hR⟩)
  have hdegle : ∀ y, deg y ≤ X.card := fun y =>
    Finset.card_le_card (Finset.filter_subset _ _)
  set J := Nat.log 2 X.card with hJ
  set bucket : β → ℕ := fun y => Nat.log 2 (deg y) with hbucket
  have hbmem : ∀ y ∈ Y, bucket y ∈ Finset.range (J + 1) := by
    intro y hy
    rw [Finset.mem_range]
    have hb : bucket y ≤ J := by
      rw [hbucket, hJ]
      exact Nat.log_mono_right (hdegle y)
    omega
  have hsum : ∑ j ∈ Finset.range (J + 1),
      (Y.filter fun y => bucket y = j).card = Y.card :=
    (Finset.card_eq_sum_card_fiberwise hbmem).symm
  obtain ⟨j₀, -, hj₀max⟩ := Finset.exists_max_image (Finset.range (J + 1))
    (fun j => (Y.filter fun y => bucket y = j).card)
    ⟨0, Finset.mem_range.2 (by omega)⟩
  set Y₀ := Y.filter (fun y => bucket y = j₀) with hY₀
  have hYbound : Y.card ≤ (J + 1) * Y₀.card := by
    calc Y.card = ∑ j ∈ Finset.range (J + 1),
          (Y.filter fun y => bucket y = j).card := hsum.symm
      _ ≤ ∑ _j ∈ Finset.range (J + 1), Y₀.card :=
          Finset.sum_le_sum fun j hj => hj₀max j hj
      _ = (J + 1) * Y₀.card := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_range]
  -- the sampling parameters for the winning bucket
  set M : ℕ := 2 ^ (j₀ + 1) with hM
  have hM2 : 2 ≤ M := by
    rw [hM]
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (j₀ + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  set p : ℝ := 1 / (M : ℝ) with hp
  set q : ℝ := 1 - p with hq
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hp_half : p ≤ 1 / 2 := by
    rw [hp]
    rw [div_le_div_iff₀ hMpos (by norm_num)]
    linarith
  have hq_half : (1 / 2 : ℝ) ≤ q := by rw [hq]; linarith
  have hq_pos : 0 < q := lt_of_lt_of_le (by norm_num) hq_half
  have hq_le1 : q ≤ 1 := by rw [hq]; linarith
  have hpq : p + q = 1 := by rw [hq]; ring
  have hdegbounds : ∀ y ∈ Y₀, 2 ^ j₀ ≤ deg y ∧ deg y < M := by
    intro y hy
    obtain ⟨hyY, hyb⟩ := Finset.mem_filter.1 hy
    refine ⟨?_, ?_⟩
    · calc 2 ^ j₀ = 2 ^ bucket y := by rw [hyb]
        _ ≤ deg y := Nat.pow_log_le_self 2 (hdegpos y hyY)
    · calc deg y < 2 ^ (bucket y + 1) :=
          Nat.lt_pow_succ_log_self (by omega) _
        _ = M := by rw [hyb, hM]
  -- expected unique-neighbor count per bucket vertex
  have hPy : ∀ y ∈ Y₀, (1 / 16 : ℝ) ≤
      ∑ S ∈ X.powerset.filter
        (fun S => (S ∩ X.filter fun x => R x y).card = 1),
        p ^ S.card * q ^ (X \ S).card := by
    intro y hy
    obtain ⟨hlow, hhigh⟩ := hdegbounds y hy
    rw [sum_weight_inter_card_one (Finset.filter_subset _ _) hpq]
    have hdp : (1 / 2 : ℝ) ≤ (deg y : ℝ) * p := by
      have hcast : ((2 : ℝ)) ^ j₀ = (M : ℝ) / 2 := by
        rw [hM]
        push_cast
        rw [pow_succ]
        ring
      have hdlow : ((2 : ℝ)) ^ j₀ ≤ (deg y : ℝ) := by exact_mod_cast hlow
      rw [hp, mul_one_div, le_div_iff₀ hMpos]
      nlinarith
    have hqd : (1 / 8 : ℝ) ≤ q ^ (deg y - 1) := by
      have h8 : (1 / 8 : ℝ) ≤ q ^ M := by
        rw [hq, hp]
        exact one_div_eight_le_pow hM2
      have hmono : q ^ M ≤ q ^ (deg y - 1) :=
        pow_le_pow_of_le_one hq_pos.le hq_le1 (by omega)
      linarith
    calc (1 / 16 : ℝ) = (1 / 2) * (1 / 8) := by norm_num
      _ ≤ ((deg y : ℝ) * p) * q ^ (deg y - 1) :=
          mul_le_mul hdp hqd (by norm_num) (by positivity)
      _ = (deg y : ℝ) * (p * q ^ (deg y - 1)) := by ring
  -- the weighted count of unique-neighbor vertices, and the best sample
  set w : Finset α → ℝ := fun S => p ^ S.card * q ^ (X \ S).card with hw
  have hw0 : ∀ S, 0 ≤ w S := fun S => by
    simp only [hw]
    positivity
  have hwsum : ∑ S ∈ X.powerset, w S = 1 := by
    simp only [hw]
    rw [sum_pow_mul_pow_sdiff X p q, hpq, one_pow]
  set cnt : Finset α → ℕ := fun S =>
    (Y₀.filter fun y => (S ∩ X.filter fun x => R x y).card = 1).card
    with hcnt
  have hexp : (Y₀.card : ℝ) / 16 ≤ ∑ S ∈ X.powerset, w S * cnt S := by
    have hswap : ∑ S ∈ X.powerset, w S * cnt S =
        ∑ y ∈ Y₀, ∑ S ∈ X.powerset.filter
          (fun S => (S ∩ X.filter fun x => R x y).card = 1), w S := by
      calc ∑ S ∈ X.powerset, w S * cnt S
          = ∑ S ∈ X.powerset, ∑ y ∈ Y₀,
              if (S ∩ X.filter fun x => R x y).card = 1 then w S else 0 := by
            refine Finset.sum_congr rfl fun S _ => ?_
            simp only [hcnt]
            rw [Finset.card_filter]
            push_cast
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            split_ifs <;> simp
        _ = ∑ y ∈ Y₀, ∑ S ∈ X.powerset,
              if (S ∩ X.filter fun x => R x y).card = 1 then w S else 0 :=
            Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun y _ =>
            (Finset.sum_filter _ _).symm
    rw [hswap]
    calc (Y₀.card : ℝ) / 16 = ∑ _y ∈ Y₀, (1 / 16 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum fun y hy => hPy y hy
  obtain ⟨S₀, hS₀mem, hS₀max⟩ := Finset.exists_max_image X.powerset cnt
    ⟨∅, Finset.empty_mem_powerset X⟩
  have hbest : (Y₀.card : ℝ) / 16 ≤ (cnt S₀ : ℝ) := by
    have hstep : ∑ S ∈ X.powerset, w S * cnt S ≤
        ∑ S ∈ X.powerset, w S * cnt S₀ :=
      Finset.sum_le_sum fun S hS => mul_le_mul_of_nonneg_left
        (by exact_mod_cast hS₀max S hS) (hw0 S)
    rw [← Finset.sum_mul, hwsum, one_mul] at hstep
    linarith [hexp]
  -- bucket count versus `log`
  have hJle : (J : ℝ) ≤ 2 * Real.log X.card := by
    have h2J : ((2 : ℝ)) ^ J ≤ (X.card : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 hX0
    have hlog := Real.log_le_log (by positivity) h2J
    rw [Real.log_pow] at hlog
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  have hlogpos : (0 : ℝ) ≤ Real.log X.card :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hX0)
  refine ⟨S₀, Finset.mem_powerset.1 hS₀mem,
    Y₀.filter (fun y => (S₀ ∩ X.filter fun x => R x y).card = 1),
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _), ?_, ?_⟩
  · -- the cardinality bound
    have hYb : (Y.card : ℝ) ≤ ((J : ℝ) + 1) * (Y₀.card : ℝ) := by
      exact_mod_cast hYbound
    have hcnt0 : (0 : ℝ) ≤ (cnt S₀ : ℝ) := Nat.cast_nonneg _
    have h1 : (Y₀.card : ℝ) ≤ 16 * cnt S₀ := by linarith
    have hJ1pos : (0 : ℝ) ≤ (J : ℝ) + 1 := by positivity
    calc (Y.card : ℝ) ≤ ((J : ℝ) + 1) * (Y₀.card : ℝ) := hYb
      _ ≤ ((J : ℝ) + 1) * (16 * cnt S₀) :=
          mul_le_mul_of_nonneg_left h1 hJ1pos
      _ ≤ (2 * Real.log X.card + 1) * (16 * cnt S₀) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ 150 * (Real.log X.card + 1) * cnt S₀ := by nlinarith
  · -- the unique-neighbor property
    intro y hy
    obtain ⟨-, hyuniq⟩ := Finset.mem_filter.1 hy
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hyuniq
    have hxmem : x ∈ S₀ ∩ X.filter fun x => R x y :=
      hx ▸ Finset.mem_singleton_self x
    refine ⟨x, ⟨(Finset.mem_inter.1 hxmem).1,
      (Finset.mem_filter.1 (Finset.mem_inter.1 hxmem).2).2⟩, ?_⟩
    rintro x' ⟨hx'S, hx'R⟩
    have hx'X : x' ∈ X := Finset.mem_powerset.1 hS₀mem hx'S
    have hx'mem : x' ∈ S₀ ∩ X.filter fun x => R x y :=
      Finset.mem_inter.2 ⟨hx'S, Finset.mem_filter.2 ⟨hx'X, hx'R⟩⟩
    rw [hx] at hx'mem
    exact Finset.mem_singleton.1 hx'mem

end Lax5Proofs.Sampling
