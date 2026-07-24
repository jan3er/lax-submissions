import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Order.Monotone.Basic

/-!
Ramsey for colorings of arbitrary `ℓ`-tuples over a linear order, with
homogeneity up to the tuple's order type (Erdős–Rado chain building over
strict-monotone tuples, then factoring through rank patterns), and the
two-sided version for pairs of tuples (Mählmann's thesis, Lemma 4.15).
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

/-- Chain-building bound for the strict-monotone Ramsey induction.
Given a per-size bound `ih : ℕ → ℕ`, `chainBound ih T` is the size needed
to perform `T` iterations of the Erdős–Rado chain-building step. -/
private def chainBound : (ℕ → ℕ) → ℕ → ℕ
  | _,  0     => 0
  | ih, T + 1 => ih (chainBound ih T) + 1

/-- Chain-building step for the strict-monotone hypergraph Ramsey induction.
Given an `(m'-tuple)`-level Ramsey bound `ih_fn`, build for each `T : ℕ` a
set `I ⊆ S` of size `T` together with a coloring `cols` of its elements
such that every strict-monotone `(m'+1)`-tuple from `I` has color
`cols (a 0)` (the color of its minimum). -/
private lemma buildChain (k m' : ℕ) (ih_fn : ℕ → ℕ)
    (ih_spec : ∀ (r : ℕ) {n : ℕ} (S : Finset (Fin n)),
      ih_fn r ≤ S.card → ∀ c : (Fin m' → Fin n) → Fin k,
        ∃ I : Finset (Fin n), I ⊆ S ∧ r ≤ I.card ∧ ∃ col : Fin k,
          ∀ a : Fin m' → Fin n, StrictMono a → (∀ i, a i ∈ I) → c a = col) :
    ∀ (T : ℕ) {n : ℕ} (S : Finset (Fin n))
      (c : (Fin (m' + 1) → Fin n) → Fin k),
      chainBound ih_fn T ≤ S.card →
      ∃ I : Finset (Fin n), I ⊆ S ∧ T ≤ I.card ∧
        ∃ cols : Fin n → Fin k,
          ∀ a : Fin (m' + 1) → Fin n, StrictMono a → (∀ i, a i ∈ I) →
            c a = cols (a 0) := by
  classical
  intro T
  induction T with
  | zero =>
      intro n S c _
      refine ⟨∅, Finset.empty_subset _, ?_, fun x => c (fun _ => x), ?_⟩
      · simp
      · intro a _ hmem
        exact absurd (hmem 0) (Finset.notMem_empty _)
  | succ T' ihT =>
      intro n S c hS
      have hSpos : 0 < S.card := by
        change ih_fn (chainBound ih_fn T') + 1 ≤ S.card at hS
        omega
      have hSne : S.Nonempty := Finset.card_pos.mp hSpos
      let v : Fin n := S.min' hSne
      have hvmem : v ∈ S := S.min'_mem hSne
      let S₁ : Finset (Fin n) := S.erase v
      have hS₁card : ih_fn (chainBound ih_fn T') ≤ S₁.card := by
        have h1 : S₁.card = S.card - 1 :=
          Finset.card_erase_of_mem hvmem
        change ih_fn (chainBound ih_fn T') + 1 ≤ S.card at hS
        omega
      let c' : (Fin m' → Fin n) → Fin k := fun b => c (Fin.cons v b)
      obtain ⟨J, hJsub, hJcard, col_v, hJhomo⟩ :=
        ih_spec (chainBound ih_fn T') S₁ hS₁card c'
      obtain ⟨I', hI'sub, hI'card, cols', hI'homo⟩ := ihT J c hJcard
      have hvNotI' : v ∉ I' := by
        intro hv
        have hvJ : v ∈ J := hI'sub hv
        have hvS₁ : v ∈ S₁ := hJsub hvJ
        exact (Finset.notMem_erase v S) hvS₁
      have hvLT : ∀ x ∈ S, x ≠ v → v < x := by
        intro x hxS hxne
        have hle : v ≤ x := S.min'_le x hxS
        exact lt_of_le_of_ne hle (Ne.symm hxne)
      refine ⟨insert v I', ?_, ?_, ?_⟩
      · -- insert v I' ⊆ S
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxI'
        · exact hvmem
        · have hxS₁ : x ∈ S₁ := hJsub (hI'sub hxI')
          exact (Finset.mem_erase.mp hxS₁).2
      · -- T'+1 ≤ |insert v I'|
        rw [Finset.card_insert_of_notMem hvNotI']
        omega
      · -- Homogeneity.
        refine ⟨fun x => if x = v then col_v else cols' x, ?_⟩
        intro a ha hmem
        by_cases h0 : a 0 = v
        · -- Case: a 0 = v. Tail lives in I'.
          have h_tail_mem : ∀ i : Fin m', (Fin.tail a) i ∈ I' := by
            intro i
            have hmem_succ : a i.succ ∈ insert v I' := hmem i.succ
            have hne : a i.succ ≠ v := by
              have hlt : a 0 < a i.succ := ha (Fin.succ_pos i)
              rw [h0] at hlt
              exact ne_of_gt hlt
            rcases Finset.mem_insert.mp hmem_succ with heq | hI'
            · exact absurd heq hne
            · exact hI'
          have h_tail_strict : StrictMono (Fin.tail a) := by
            intro i j hij
            exact ha (Fin.succ_lt_succ_iff.mpr hij)
          have h_tail_J : ∀ i, (Fin.tail a) i ∈ J := fun i =>
            hI'sub (h_tail_mem i)
          have hc' : c (Fin.cons v (Fin.tail a)) = col_v :=
            hJhomo (Fin.tail a) h_tail_strict h_tail_J
          have h_eq : a = Fin.cons v (Fin.tail a) := by
            apply funext
            intro i
            refine Fin.cases ?_ ?_ i
            · simp [Fin.cons_zero, h0]
            · intro j; simp [Fin.cons_succ, Fin.tail]
          have : c a = col_v := by rw [h_eq]; exact hc'
          simp [h0, this]
        · -- Case: a 0 ≠ v. Whole image lives in I'.
          have h_mem_I' : ∀ i, a i ∈ I' := by
            intro i
            have hmem_i : a i ∈ insert v I' := hmem i
            by_cases hi : i = 0
            · subst hi
              rcases Finset.mem_insert.mp hmem_i with heq | hI'
              · exact absurd heq h0
              · exact hI'
            · -- a i > a 0 > v, so a i ≠ v
              have h_a0_S : a 0 ∈ S := by
                have : a 0 ∈ insert v I' := hmem 0
                rcases Finset.mem_insert.mp this with heq | hI'
                · rw [heq]; exact hvmem
                · have hS₁ : a 0 ∈ S₁ := hJsub (hI'sub hI')
                  exact (Finset.mem_erase.mp hS₁).2
              have hv_lt_a0 : v < a 0 := hvLT (a 0) h_a0_S h0
              have h_a0_lt_ai : a 0 < a i := ha (Fin.pos_of_ne_zero hi)
              have hne : a i ≠ v := ne_of_gt (lt_trans hv_lt_a0 h_a0_lt_ai)
              rcases Finset.mem_insert.mp hmem_i with heq | hI'
              · exact absurd heq hne
              · exact hI'
          have hc' : c a = cols' (a 0) := hI'homo a ha h_mem_I'
          have h_a0_ne_v : a 0 ≠ v := h0
          simp [h_a0_ne_v, hc']

/-- Hypergraph Ramsey for strict-monotone `m`-tuples (Finset form).
Given a finite subset `S` of `Fin n` large enough, every `k`-coloring of
strict-monotone `m`-tuples from `Fin n` has a monochromatic subset of `S`
of size `M`. Proved by induction on `m` via Erdős–Rado. -/
private lemma strictMonoRamseyFinset (k : ℕ) :
    ∀ (m M : ℕ), ∃ Nfin : ℕ, ∀ {n : ℕ} (S : Finset (Fin n)),
      Nfin ≤ S.card → ∀ c : (Fin m → Fin n) → Fin k,
        ∃ I : Finset (Fin n), I ⊆ S ∧ M ≤ I.card ∧ ∃ col : Fin k,
          ∀ a : Fin m → Fin n, StrictMono a → (∀ i, a i ∈ I) → c a = col := by
  intro m
  induction m with
  | zero =>
      intro M
      refine ⟨M, ?_⟩
      intro n S hS c
      refine ⟨S, Finset.Subset.refl _, hS, c Fin.elim0, ?_⟩
      intro a _ _
      have : a = Fin.elim0 := funext (fun i => Fin.elim0 i)
      rw [this]
  | succ m' ih =>
      classical
      intro M
      -- Extract ih as a function.
      let ih_fn : ℕ → ℕ := fun r => (ih r).choose
      have ih_spec : ∀ (r : ℕ) {n : ℕ} (S : Finset (Fin n)),
          ih_fn r ≤ S.card → ∀ c : (Fin m' → Fin n) → Fin k,
            ∃ I : Finset (Fin n), I ⊆ S ∧ r ≤ I.card ∧ ∃ col : Fin k,
              ∀ a : Fin m' → Fin n, StrictMono a →
                (∀ i, a i ∈ I) → c a = col :=
        fun r => (ih r).choose_spec
      -- T = M · k + 1 rounds (loose; M·k gives pigeonhole M occurrences).
      let T : ℕ := M * k + 1
      refine ⟨chainBound ih_fn T, ?_⟩
      intro n S hS c
      obtain ⟨I, hIsub, hIcard, cols, hIhomo⟩ :=
        buildChain k m' ih_fn ih_spec T S c hS
      -- Pigeonhole on `cols` restricted to `I`.
      have hcard_lt : k * M < I.card := by
        have : T ≤ I.card := hIcard
        have : M * k + 1 ≤ I.card := this
        have hmk : M * k = k * M := Nat.mul_comm _ _
        omega
      -- There is a color appearing more than `M` times in `I`.
      have : ∃ col : Fin k, M < (I.filter (fun x => cols x = col)).card := by
        by_contra hneg
        push Not at hneg
        -- Sum of (filter).card = I.card (since every elt of I has some color).
        have hsum : ∑ col : Fin k, (I.filter (fun x => cols x = col)).card
                    = I.card := by
          have := @Finset.card_eq_sum_card_fiberwise _ _ _ cols I
                    Finset.univ (fun x _ => Finset.mem_univ _)
          simpa using this.symm
        have hbound : ∑ col : Fin k, (I.filter (fun x => cols x = col)).card
                      ≤ k * M := by
          calc ∑ col : Fin k, (I.filter (fun x => cols x = col)).card
              ≤ ∑ _col : Fin k, M := Finset.sum_le_sum (fun col _ => hneg col)
            _ = k * M := by simp [Finset.sum_const, Finset.card_univ]
        omega
      obtain ⟨col, hcol⟩ := this
      refine ⟨I.filter (fun x => cols x = col), ?_, ?_, col, ?_⟩
      · exact (Finset.filter_subset _ _).trans hIsub
      · exact hcol.le
      · intro a ha hmem
        have hmemI : ∀ i, a i ∈ I := fun i =>
          (Finset.mem_filter.mp (hmem i)).1
        have ha0_col : cols (a 0) = col :=
          (Finset.mem_filter.mp (hmem 0)).2
        rw [hIhomo a ha hmemI, ha0_col]

private def Shape (ℓ : ℕ) :=
  Σ m : Fin (ℓ + 1), {σ : Fin ℓ → Fin m.1 // Function.Surjective σ}

private def Shape.arity {ℓ : ℕ} (s : Shape ℓ) : ℕ :=
  s.1.1

private def Shape.pattern {ℓ : ℕ} (s : Shape ℓ) : Fin ℓ → Fin s.arity :=
  s.2.1

private lemma Shape.pattern_surjective {ℓ : ℕ} (s : Shape ℓ) :
    Function.Surjective s.pattern :=
  s.2.2

private instance shapeFintype (ℓ : ℕ) : Fintype (Shape ℓ) := by
  classical
  unfold Shape
  infer_instance

private lemma orderType_comp_strictMono {α β : Type*} [LinearOrder α] [LinearOrder β]
    {ℓ : ℕ} {σ : Fin ℓ → α} {e : α → β} (he : StrictMono e) :
    orderType (e ∘ σ) = orderType σ := by
  ext p
  rcases lt_trichotomy (σ p.1) (σ p.2) with hlt | heq | hgt
  · simp [orderType, Function.comp, compare_lt_iff_lt.mpr hlt,
      compare_lt_iff_lt.mpr (he hlt)]
  · simp [orderType, Function.comp, heq]
  · simp [orderType, Function.comp, compare_gt_iff_gt.mpr hgt,
      compare_gt_iff_gt.mpr (he hgt)]

private lemma factorThroughShape {ℓ m n : ℕ} {σ : Fin ℓ → Fin m}
    (hσsurj : Function.Surjective σ) (a : Fin ℓ → Fin n)
    (hot : orderType σ = orderType a) :
    ∃ e : Fin m → Fin n, StrictMono e ∧ a = e ∘ σ := by
  classical
  let τ : Fin m → Fin ℓ := fun r => Classical.choose (hσsurj r)
  have hτ : Function.RightInverse τ σ := fun r => Classical.choose_spec (hσsurj r)
  let e : Fin m → Fin n := fun r => a (τ r)
  have he : StrictMono e := by
    intro r s hrs
    have hcmp : compare (e r) (e s) = Ordering.lt := by
      simpa [e, orderType, hτ r, hτ s, compare_lt_iff_lt.mpr hrs] using
        (congrArg (fun ot => ot (τ r, τ s)) hot).symm
    exact compare_lt_iff_lt.mp hcmp
  refine ⟨e, he, funext fun i => ?_⟩
  have hcmp0 : compare (a i) (a (τ (σ i))) = compare (σ i) (σ (τ (σ i))) := by
    simpa [orderType] using (congrArg (fun ot => ot (i, τ (σ i))) hot).symm
  have hcmp : compare (a i) (e (σ i)) = Ordering.eq := by
    simpa [e, hτ (σ i)] using hcmp0
  exact compare_eq_iff_eq.mp hcmp

private lemma decomposeTuple {ℓ n : ℕ} (a : Fin ℓ → Fin n) :
    ∃ s : Shape ℓ, ∃ e : Fin s.arity → Fin n, StrictMono e ∧ a = e ∘ s.pattern := by
  classical
  let A : Finset (Fin n) := Finset.univ.image a
  have hAcard : A.card ≤ ℓ := by
    simpa [A] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin ℓ))) (f := a))
  let m : Fin (ℓ + 1) := ⟨A.card, Nat.lt_succ_of_le hAcard⟩
  let emb : Fin m.1 ↪o Fin n := A.orderEmbOfFin rfl
  have ha_mem_range : ∀ i : Fin ℓ, a i ∈ Finset.image emb Finset.univ := by
    intro i
    simp [A, emb]
  have hpre : ∀ i : Fin ℓ, ∃ j : Fin m.1, emb j = a i := by
    intro i
    rcases Finset.mem_image.mp (ha_mem_range i) with ⟨j, _, hj⟩
    exact ⟨j, hj⟩
  choose σ hσ using hpre
  have hσsurj : Function.Surjective σ := by
    intro j
    have hjA : emb j ∈ A := Finset.orderEmbOfFin_mem A rfl j
    have hjim : emb j ∈ Finset.univ.image a := by simpa [A] using hjA
    rcases Finset.mem_image.mp hjim with ⟨i, -, hi⟩
    refine ⟨i, ?_⟩
    apply emb.injective
    simpa [hσ i] using hi
  let s : Shape ℓ := ⟨m, ⟨σ, hσsurj⟩⟩
  refine ⟨s, emb, emb.strictMono, ?_⟩
  ext i
  exact congrArg Fin.val (hσ i).symm

private lemma shapeRamseyFamily (k ℓ M : ℕ) (hk : 0 < k) :
    ∀ T : Finset (Shape ℓ), ∃ Nfin : ℕ, ∀ {n : ℕ} (S : Finset (Fin n)),
      Nfin ≤ S.card → ∀ c : (Fin ℓ → Fin n) → Fin k,
        ∃ I : Finset (Fin n), I ⊆ S ∧ M ≤ I.card ∧
          ∃ cols : Shape ℓ → Fin k,
            ∀ s ∈ T, ∀ e : Fin s.arity → Fin n, StrictMono e →
              (∀ i, e i ∈ I) → c (e ∘ s.pattern) = cols s := by
  intro T
  classical
  refine Finset.induction_on T ?_ ?_
  · refine ⟨M, ?_⟩
    intro n S hS c
    refine ⟨S, Finset.Subset.rfl, hS, fun _ => ⟨0, by omega⟩, ?_⟩
    intro s hs
    exact False.elim (Finset.notMem_empty _ hs)
  · intro s T hs ih
    obtain ⟨NT, hT⟩ := ih
    obtain ⟨Ns, hspec⟩ := strictMonoRamseyFinset k s.arity NT
    refine ⟨Ns, ?_⟩
    intro n S hS c
    obtain ⟨J, hJsub, hJcard, col_s, hJhom⟩ :=
      hspec S hS (fun e => c (e ∘ s.pattern))
    obtain ⟨I, hIsub, hIcard, colsT, hIhom⟩ :=
      hT J hJcard c
    refine ⟨I, hIsub.trans hJsub, hIcard, Function.update colsT s col_s, ?_⟩
    intro t ht e he hemem
    rcases Finset.mem_insert.mp ht with rfl | htT
    · simp [Function.update]
      exact hJhom e he (fun i => hIsub (hemem i))
    · have hts : t ≠ s := by
        intro hts
        subst hts
        exact hs htT
      simp [Function.update, hts]
      exact hIhom t htT e he hemem

/-- Hypergraph Ramsey at a given size, for arbitrary (not necessarily
strict-monotone) `ℓ`-tuples with order-type homogeneity.

**Proof strategy (not yet formalized).** Given a `k`-coloring
`c : (Fin ℓ → Fin n) → Fin k`, factor each tuple `a : Fin ℓ → V` through
its rank pattern: `a = ã ∘ σ` with `σ : Fin ℓ → Fin m` (`m ≤ ℓ`, the
number of distinct values of `a`) and `ã : Fin m → V` strict-monotone.
The pair `(m, σ)` is fully determined by `orderType a`.

Iterate `strictMonoRamseyFinset` over the finite shape type
`Σ m : Fin (ℓ+1), Fin ℓ → Fin m.val`: for each shape `(m, σ)`, apply
`strictMonoRamseyFinset k m _` to the induced coloring
`c_σ ã := c (ã ∘ σ)` and shrink `S`. After all shapes are processed,
define `f : orderType → Fin k` by looking up the color assigned to the
shape induced by each order type. -/
private lemma tupleRamseyAtSize (k ℓ M : ℕ) (hk : 0 < k) :
    ∃ Nfin : ℕ, ∀ {n : ℕ} (S : Finset (Fin n)),
      Nfin ≤ S.card → ∀ c : (Fin ℓ → Fin n) → Fin k,
        ∃ I : Finset (Fin n), I ⊆ S ∧ M ≤ I.card ∧
          ∃ f : (Fin ℓ × Fin ℓ → Ordering) → Fin k,
            ∀ a : Fin ℓ → Fin n, (∀ i, a i ∈ I) → c a = f (orderType a) := by
  classical
  obtain ⟨Nfin, hNfin⟩ := shapeRamseyFamily k ℓ M hk (Finset.univ : Finset (Shape ℓ))
  refine ⟨Nfin, ?_⟩
  intro n S hS c
  obtain ⟨I, hIsub, hIcard, cols, hIhom⟩ := hNfin S hS c
  refine ⟨I, hIsub, hIcard, ?_⟩
  refine ⟨fun ot => if h : ∃ s : Shape ℓ, orderType s.pattern = ot then cols (Classical.choose h)
    else ⟨0, hk⟩, ?_⟩
  intro a hmem
  have hex : ∃ s : Shape ℓ, orderType s.pattern = orderType a := by
    obtain ⟨s, e, he, hfac⟩ := decomposeTuple a
    refine ⟨s, ?_⟩
    simpa [hfac] using (orderType_comp_strictMono (σ := s.pattern) he).symm
  let s : Shape ℓ := Classical.choose hex
  have hs_ot : orderType s.pattern = orderType a := Classical.choose_spec hex
  obtain ⟨e, he, hfac⟩ := factorThroughShape s.pattern_surjective a hs_ot
  have hemem : ∀ i, e i ∈ I := by
    intro i
    rcases s.pattern_surjective i with ⟨j, rfl⟩
    simpa [hfac] using hmem j
  have hc : c a = cols s := by
    rw [hfac]
    exact hIhom s (by simp) e he hemem
  simpa [hex] using hc

theorem tuple_ramsey (k ℓ : ℕ) (hk : 0 < k) :
    ∃ N : ℕ → ℕ, Monotone N ∧ (∀ M : ℕ, ∃ n : ℕ, M ≤ N n) ∧
      ∀ (n : ℕ) (c : (Fin ℓ → Fin n) → Fin k),
        ∃ I : Finset (Fin n), N n ≤ I.card ∧
          ∃ f : (Fin ℓ × Fin ℓ → Ordering) → Fin k,
            ∀ (a : Fin ℓ → Fin n), (∀ i, a i ∈ I) →
              c a = f (orderType a) := by
  -- Package `tupleRamseyAtSize` into the monotone-unbounded form via
  -- `existsMonotoneUnbounded`.
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
  let Nfin : ℕ → ℕ := fun M => (tupleRamseyAtSize k ℓ M hk).choose
  have hNfin : ∀ M n, Nfin M ≤ n → P n M := by
    intro M n hn c
    obtain ⟨I, hIsub, hIcard, f, hf⟩ :=
      (tupleRamseyAtSize k ℓ M hk).choose_spec (S := (Finset.univ : Finset (Fin n))) (by simpa using hn) c
    exact ⟨I, hIcard, f, hf⟩
  obtain ⟨N, hNmono, hNunb, hN⟩ := existsMonotoneUnbounded hP_zero Nfin hNfin
  refine ⟨N, hNmono, hNunb, ?_⟩
  intro n c
  exact hN n c

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
