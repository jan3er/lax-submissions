import Lax14.TupleRamsey
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Card
import Mathlib.Order.Monotone.Basic

/-!
Ramsey for colorings of arbitrary `ℓ`-tuples over a linear order, with
homogeneity up to the tuple's order type, and the two-sided version for
pairs of tuples (Mählmann's thesis, Lemma 4.15).

The Erdős–Rado core is no longer proved here: `tuple_ramsey` is a
repackaging of `Lax14.TupleRamsey.exists_orderType_homogeneous`, the
statement of the `finite-ramsey` submission, into the monotone-unbounded
`Finset` form the subdivided-biclique argument consumes.  Its signature
and that of `orderType` are unchanged, so
`Lax5Proofs.SubdividedBicliqueRamsey` needs no edits.
-/

namespace Lax5Proofs.TupleRamsey

/-- Order type of a tuple `a : Fin ℓ → V` (`V` linearly ordered). For
each pair `(i, j) : Fin ℓ × Fin ℓ`, records whether `a i < a j`,
`a i = a j`, or `a i > a j`. Mählmann p. 28 writes this as `otp(a)`. -/
def orderType {V : Type*} [LinearOrder V] {ℓ : ℕ} (a : Fin ℓ → V) :
    Fin ℓ × Fin ℓ → Ordering :=
  fun p => compare (a p.1) (a p.2)

section Helpers

/-- Generic packaging helper: convert a size-indexed Ramsey bound into the
monotone-unbounded form used throughout the entry.

Given a property `P n M` trivial at `M = 0` and a bound function `Nfin`
with `Nfin M ≤ n → P n M`, produce a monotone unbounded `N : ℕ → ℕ` with
`P n (N n)` for all `n`. The bound `N` is the largest `M ≤ n` with
`Nfin' M ≤ n`, where `Nfin'` is a monotone envelope of `Nfin`. -/
private lemma existsMonotoneUnbounded {P : ℕ → ℕ → Prop}
    (hP_zero : ∀ n, P n 0)
    (Nfin : ℕ → ℕ) (hNfin : ∀ M n, Nfin M ≤ n → P n M) :
    ∃ N : ℕ → ℕ, Monotone N ∧ (∀ K : ℕ, ∃ n, K ≤ N n) ∧ ∀ n, P n (N n) := by
  classical
  let Nfin' : ℕ → ℕ := fun M =>
    (Finset.range (M + 1)).sup (fun M' => max M' (Nfin M'))
  have hNfin'_mono : Monotone Nfin' := by
    intro a b hab
    apply Finset.sup_mono
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hNfin'_geId : ∀ M, M ≤ Nfin' M := by
    intro M
    have h1 : M ≤ max M (Nfin M) := le_max_left _ _
    have h2 : max M (Nfin M) ≤ Nfin' M := by
      apply Finset.le_sup (f := fun M' => max M' (Nfin M'))
        (s := Finset.range (M + 1))
      exact Finset.self_mem_range_succ M
    exact h1.trans h2
  have hNfin'_geNfin : ∀ M, Nfin M ≤ Nfin' M := by
    intro M
    have h1 : Nfin M ≤ max M (Nfin M) := le_max_right _ _
    have h2 : max M (Nfin M) ≤ Nfin' M := by
      apply Finset.le_sup (f := fun M' => max M' (Nfin M'))
        (s := Finset.range (M + 1))
      exact Finset.self_mem_range_succ M
    exact h1.trans h2
  refine ⟨fun n => Nat.findGreatest (fun M => Nfin' M ≤ n) n, ?_, ?_, ?_⟩
  · intro a b hab
    refine Nat.findGreatest_mono ?_ hab
    intro M hM
    exact hM.trans hab
  · intro K
    refine ⟨Nfin' K, ?_⟩
    exact Nat.le_findGreatest (hNfin'_geId K) le_rfl
  · intro n
    show P n (Nat.findGreatest (fun M => Nfin' M ≤ n) n)
    by_cases h : Nfin' 0 ≤ n
    · have hspec : Nfin' (Nat.findGreatest (fun M => Nfin' M ≤ n) n) ≤ n :=
        Nat.findGreatest_spec (P := fun M => Nfin' M ≤ n) (Nat.zero_le n) h
      exact hNfin _ n ((hNfin'_geNfin _).trans hspec)
    · push Not at h
      have hzero : Nat.findGreatest (fun M => Nfin' M ≤ n) n = 0 := by
        rw [Nat.findGreatest_eq_zero_iff]
        intro k hk0 _
        have : Nfin' 0 ≤ Nfin' k := hNfin'_mono (Nat.zero_le k)
        omega
      rw [hzero]
      exact hP_zero n

/-- The `Ordering`-valued order type used throughout this entry determines
the `Prop`-valued order type of the assumed statement: two tuples compared
the same way are, in particular, ordered the same way. -/
private lemma orderTypeProp_eq_of_orderType_eq {V : Type*} [LinearOrder V]
    {ℓ : ℕ} {a b : Fin ℓ → V} (h : orderType a = orderType b) :
    Lax14.OrderTypes.orderType a = Lax14.OrderTypes.orderType b := by
  funext i j
  have hij : compare (a i) (a j) = compare (b i) (b j) :=
    congrArg (fun ot => ot (i, j)) h
  apply propext
  constructor
  · intro hlt
    have hlt' : a i < a j := hlt
    have hcmp : compare (b i) (b j) = Ordering.lt := by
      rw [← hij]; exact compare_lt_iff_lt.mpr hlt'
    exact compare_lt_iff_lt.mp hcmp
  · intro hlt
    have hlt' : b i < b j := hlt
    have hcmp : compare (a i) (a j) = Ordering.lt := by
      rw [hij]; exact compare_lt_iff_lt.mpr hlt'
    exact compare_lt_iff_lt.mp hcmp

/-- Hypergraph Ramsey for arbitrary `ℓ`-tuples with order-type homogeneity,
in the monotone-unbounded form used throughout this entry.  Repackaging of
the assumed statement `Lax14.TupleRamsey.exists_orderType_homogeneous`: its
per-size bound is fed to `existsMonotoneUnbounded`, its `Set` witness is
converted to a `Finset`, and the factoring function `f` is rebuilt from
homogeneity by picking, for each realized order type, a tuple realizing
it. -/
theorem tuple_ramsey (k ℓ : ℕ) (hk : 0 < k) :
    ∃ N : ℕ → ℕ, Monotone N ∧ (∀ M : ℕ, ∃ n : ℕ, M ≤ N n) ∧
      ∀ (n : ℕ) (c : (Fin ℓ → Fin n) → Fin k),
        ∃ I : Finset (Fin n), N n ≤ I.card ∧
          ∃ f : (Fin ℓ × Fin ℓ → Ordering) → Fin k,
            ∀ (a : Fin ℓ → Fin n), (∀ i, a i ∈ I) →
              c a = f (orderType a) := by
  classical
  let P : ℕ → ℕ → Prop := fun n M =>
    ∀ c : (Fin ℓ → Fin n) → Fin k,
      ∃ I : Finset (Fin n), M ≤ I.card ∧
        ∃ f : (Fin ℓ × Fin ℓ → Ordering) → Fin k,
          ∀ a : Fin ℓ → Fin n, (∀ i, a i ∈ I) → c a = f (orderType a)
  have hP_zero : ∀ n, P n 0 := by
    intro n c
    by_cases hℓ : ℓ = 0
    · subst hℓ
      refine ⟨∅, by simp, fun _ => c Fin.elim0, ?_⟩
      intro a _
      have : a = Fin.elim0 := funext (fun i => Fin.elim0 i)
      rw [this]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hℓ
      refine ⟨∅, by simp, fun _ => ⟨0, hk⟩, ?_⟩
      intro a hmem
      exact absurd (hmem 0) (Finset.notMem_empty _)
  let Nfin : ℕ → ℕ := fun M =>
    (Lax14.TupleRamsey.exists_orderType_homogeneous k ℓ M).choose
  have hNfin : ∀ M n, Nfin M ≤ n → P n M := by
    intro M n hn c
    obtain ⟨I, hIcard, hIhom⟩ :=
      (Lax14.TupleRamsey.exists_orderType_homogeneous k ℓ M).choose_spec n c hn
    refine ⟨I.toFinset, ?_, ?_⟩
    · rw [← Set.ncard_eq_toFinset_card']
      exact hIcard
    · refine ⟨fun ot =>
        if h : ∃ a : Fin ℓ → Fin n, (∀ i, a i ∈ I) ∧ orderType a = ot then
          c (Classical.choose h)
        else ⟨0, hk⟩, ?_⟩
      intro a hmem
      have hmem' : ∀ i, a i ∈ I := fun i => Set.mem_toFinset.mp (hmem i)
      have hex : ∃ a' : Fin ℓ → Fin n, (∀ i, a' i ∈ I) ∧ orderType a' = orderType a :=
        ⟨a, hmem', rfl⟩
      obtain ⟨hmem'', hot⟩ := Classical.choose_spec hex
      have hc : c a = c (Classical.choose hex) :=
        (hIhom _ a hmem'' hmem' (orderTypeProp_eq_of_orderType_eq hot)).symm
      simpa [hex] using hc
  obtain ⟨N, hNmono, hNunb, hN⟩ := existsMonotoneUnbounded hP_zero Nfin hNfin
  exact ⟨N, hNmono, hNunb, fun n c => hN n c⟩

/-- Glue two order types of `ℓ₁`- and `ℓ₂`-tuples into an order type of
a `(ℓ₁ + ℓ₂)`-tuple, assuming (virtually) that every entry of the first
tuple is strictly less than every entry of the second. Cross-coordinates
are set to `.lt` (left-right) or `.gt` (right-left). -/
def glueLT {ℓ₁ ℓ₂ : ℕ}
    (ot₁ : Fin ℓ₁ × Fin ℓ₁ → Ordering)
    (ot₂ : Fin ℓ₂ × Fin ℓ₂ → Ordering) :
    Fin (ℓ₁ + ℓ₂) × Fin (ℓ₁ + ℓ₂) → Ordering :=
  fun p => Fin.addCases
    (fun i₁ => Fin.addCases
      (fun j₁ => ot₁ (i₁, j₁))
      (fun _ => Ordering.lt)
      p.2)
    (fun i₂ => Fin.addCases
      (fun _ => Ordering.gt)
      (fun j₂ => ot₂ (i₂, j₂))
      p.2)
    p.1

/-- When every coordinate of `a` is strictly less than every coordinate
of `b`, the order type of the concatenation `Fin.append a b` factors
through the pair `(orderType a, orderType b)` via `glueLT`. -/
lemma orderType_append_of_lt {V : Type*} [LinearOrder V]
    {ℓ₁ ℓ₂ : ℕ} {a : Fin ℓ₁ → V} {b : Fin ℓ₂ → V}
    (hab : ∀ (i : Fin ℓ₁) (j : Fin ℓ₂), a i < b j) :
    orderType (Fin.append a b) = glueLT (orderType a) (orderType b) := by
  ext ⟨i, j⟩
  refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
  · refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
    · simp [orderType, glueLT, Fin.append_left, Fin.addCases_left]
    · simp only [orderType, glueLT, Fin.append_left, Fin.append_right,
        Fin.addCases_left, Fin.addCases_right]
      exact compare_lt_iff_lt.mpr (hab i₁ j₂)
  · refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
    · simp only [orderType, glueLT, Fin.append_left, Fin.append_right,
        Fin.addCases_left, Fin.addCases_right]
      exact compare_gt_iff_gt.mpr (hab j₁ i₂)
    · simp [orderType, glueLT, Fin.append_right, Fin.addCases_right]

end Helpers

/-- Mählmann Lemma 4.15 (Bipartite Ramsey). -/
theorem bipartite_tuple_ramsey (k ℓ₁ ℓ₂ : ℕ) (hk : 0 < k) :
    ∃ U : ℕ → ℕ, Monotone U ∧ (∀ N : ℕ, ∃ n : ℕ, N ≤ U n) ∧
      ∀ (n : ℕ) (c : (Fin ℓ₁ → Fin n) → (Fin ℓ₂ → Fin n) → Fin k),
        ∃ I₁ I₂ : Finset (Fin n),
          U n ≤ I₁.card ∧ U n ≤ I₂.card ∧
          ∃ f : (Fin ℓ₁ × Fin ℓ₁ → Ordering) →
                (Fin ℓ₂ × Fin ℓ₂ → Ordering) → Fin k,
            ∀ (a : Fin ℓ₁ → Fin n) (b : Fin ℓ₂ → Fin n),
              (∀ i, a i ∈ I₁) → (∀ j, b j ∈ I₂) →
                c a b = f (orderType a) (orderType b) := by
  classical
  obtain ⟨N, hNmono, hNunb, hN⟩ := tuple_ramsey k (ℓ₁ + ℓ₂) hk
  refine ⟨fun n => N n / 2, ?_, ?_, ?_⟩
  -- Monotonicity of `N n / 2`.
  · intro m n hmn
    exact Nat.div_le_div_right (hNmono hmn)
  -- Unboundedness: given `M`, pick `n` with `N n ≥ 2M`; then
  -- `N n / 2 ≥ M`.
  · intro M
    obtain ⟨n, hn⟩ := hNunb (2 * M)
    refine ⟨n, ?_⟩
    show M ≤ N n / 2
    calc M = 2 * M / 2 :=
            (Nat.mul_div_cancel_left M (by decide : (0 : ℕ) < 2)).symm
      _ ≤ N n / 2 := Nat.div_le_div_right hn
  · intro n c
    -- View `c` as a coloring of `(Fin (ℓ₁ + ℓ₂) → Fin n)` tuples via
    -- concatenation.
    let c' : (Fin (ℓ₁ + ℓ₂) → Fin n) → Fin k := fun t =>
      c (fun i => t (Fin.castAdd ℓ₂ i)) (fun j => t (Fin.natAdd ℓ₁ j))
    obtain ⟨I, hIcard, f', hf'⟩ := hN n c'
    let emb : Fin I.card ↪o Fin n := I.orderEmbOfFin rfl
    let half : ℕ := I.card / 2
    have hhalf_le : half ≤ I.card := Nat.div_le_self _ _
    have hdouble_half : 2 * half ≤ I.card := Nat.mul_div_le I.card 2
    -- `I₁` := image of `{0, …, half-1} ⊂ Fin I.card` under `emb`.
    let I₁ : Finset (Fin n) :=
      (Finset.univ : Finset (Fin half)).image
        (fun i => emb ⟨i.val, lt_of_lt_of_le i.isLt hhalf_le⟩)
    -- `I₂` := image of `{half, …, I.card-1} ⊂ Fin I.card` under `emb`.
    let I₂ : Finset (Fin n) :=
      (Finset.univ : Finset (Fin (I.card - half))).image
        (fun i => emb ⟨half + i.val, by
          have := i.isLt; omega⟩)
    let f : (Fin ℓ₁ × Fin ℓ₁ → Ordering) →
            (Fin ℓ₂ × Fin ℓ₂ → Ordering) → Fin k :=
      fun ot₁ ot₂ => f' (glueLT ot₁ ot₂)
    refine ⟨I₁, I₂, ?_, ?_, f, ?_⟩
    -- |I₁| ≥ N n / 2.
    · have hinj : Function.Injective
          (fun i : Fin half =>
            emb ⟨i.val, lt_of_lt_of_le i.isLt hhalf_le⟩) := by
        intro i j hij
        have h : (⟨i.val, lt_of_lt_of_le i.isLt hhalf_le⟩ : Fin I.card) =
                 ⟨j.val, lt_of_lt_of_le j.isLt hhalf_le⟩ :=
          emb.injective hij
        exact Fin.ext (Fin.mk_eq_mk.mp h)
      have hcard : I₁.card = half := by
        simp [I₁, Finset.card_image_of_injective _ hinj]
      rw [hcard]
      exact Nat.div_le_div_right hIcard
    -- |I₂| ≥ N n / 2.
    · have hinj : Function.Injective
          (fun i : Fin (I.card - half) =>
            emb ⟨half + i.val, by have := i.isLt; omega⟩) := by
        intro i j hij
        have h : (⟨half + i.val, by have := i.isLt; omega⟩ : Fin I.card) =
                 ⟨half + j.val, by have := j.isLt; omega⟩ :=
          emb.injective hij
        have h' : half + i.val = half + j.val := Fin.mk_eq_mk.mp h
        exact Fin.ext (by omega)
      have hcard : I₂.card = I.card - half := by
        simp [I₂, Finset.card_image_of_injective _ hinj]
      rw [hcard]
      have h1 : N n / 2 ≤ half := Nat.div_le_div_right hIcard
      have h2 : half ≤ I.card - half := by omega
      exact le_trans h1 h2
    -- Homogeneity: `c a b = f (otp a) (otp b)` for `a ∈ I₁^ℓ₁, b ∈ I₂^ℓ₂`.
    · intro a b ha hb
      -- Lift `a`, `b` to `Fin I.card` preimages under `emb`.
      have hamem : ∀ i, ∃ k : Fin half,
          emb ⟨k.val, lt_of_lt_of_le k.isLt hhalf_le⟩ = a i := by
        intro i
        have hm := ha i
        simp only [I₁, Finset.mem_image, Finset.mem_univ, true_and] at hm
        exact hm
      have hbmem : ∀ j, ∃ k : Fin (I.card - half),
          emb ⟨half + k.val, by have := k.isLt; omega⟩ = b j := by
        intro j
        have hm := hb j
        simp only [I₂, Finset.mem_image, Finset.mem_univ, true_and] at hm
        exact hm
      choose ka hka using hamem
      choose kb hkb using hbmem
      let t : Fin (ℓ₁ + ℓ₂) → Fin n := Fin.append a b
      -- `t i ∈ I` for every `i`.
      have hIt : ∀ i, t i ∈ I := by
        intro i
        refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
        · show (Fin.append a b) (Fin.castAdd ℓ₂ i₁) ∈ I
          rw [Fin.append_left, ← hka i₁]
          exact Finset.orderEmbOfFin_mem I rfl _
        · show (Fin.append a b) (Fin.natAdd ℓ₁ i₂) ∈ I
          rw [Fin.append_right, ← hkb i₂]
          exact Finset.orderEmbOfFin_mem I rfl _
      -- Every `a`-coord is strictly less than every `b`-coord.
      have hab_lt : ∀ (i : Fin ℓ₁) (j : Fin ℓ₂), a i < b j := by
        intro i j
        rw [← hka i, ← hkb j]
        apply emb.strictMono
        simp only [Fin.mk_lt_mk]
        have h1 : (ka i).val < half := (ka i).isLt
        omega
      -- Combine.
      have htsplit : c' t = f' (orderType t) := hf' t hIt
      have hca : c a b = c' t := by
        show c a b = c (fun i => (Fin.append a b) (Fin.castAdd ℓ₂ i))
                       (fun j => (Fin.append a b) (Fin.natAdd ℓ₁ j))
        simp [Fin.append_left, Fin.append_right]
      have hot : orderType t = glueLT (orderType a) (orderType b) :=
        orderType_append_of_lt hab_lt
      show c a b = f' (glueLT (orderType a) (orderType b))
      rw [hca, htsplit, hot]


end Lax5Proofs.TupleRamsey
