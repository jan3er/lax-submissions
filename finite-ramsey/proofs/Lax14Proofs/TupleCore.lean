import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Order.Monotone.Basic

/-!
Ported Erdős–Rado core: Ramsey for colourings of arbitrary `ℓ`-tuples over
a linear order, with homogeneity up to the tuple's order type.  Chain
building over strict-monotone tuples, then factoring an arbitrary tuple
through its rank pattern.  Helpers only — the frontmattered proof of the
submitted statement lives in `Lax14Proofs.TupleRamsey`.
-/

namespace Lax14Proofs.TupleCore

/-- Order type of a tuple `a : Fin ℓ → V` (`V` linearly ordered), in the
three-valued form used by this ported development. For each pair
`(i, j) : Fin ℓ × Fin ℓ`, records whether `a i < a j`, `a i = a j`, or
`a i > a j`. Mählmann p. 28 writes this as `otp(a)`. -/
def otp {V : Type*} [LinearOrder V] {ℓ : ℕ} (a : Fin ℓ → V) :
    Fin ℓ × Fin ℓ → Ordering :=
  fun p => compare (a p.1) (a p.2)

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

private lemma otp_comp_strictMono {α β : Type*} [LinearOrder α] [LinearOrder β]
    {ℓ : ℕ} {σ : Fin ℓ → α} {e : α → β} (he : StrictMono e) :
    otp (e ∘ σ) = otp σ := by
  ext p
  rcases lt_trichotomy (σ p.1) (σ p.2) with hlt | heq | hgt
  · simp [otp, Function.comp, compare_lt_iff_lt.mpr hlt,
      compare_lt_iff_lt.mpr (he hlt)]
  · simp [otp, Function.comp, heq]
  · simp [otp, Function.comp, compare_gt_iff_gt.mpr hgt,
      compare_gt_iff_gt.mpr (he hgt)]

private lemma factorThroughShape {ℓ m n : ℕ} {σ : Fin ℓ → Fin m}
    (hσsurj : Function.Surjective σ) (a : Fin ℓ → Fin n)
    (hot : otp σ = otp a) :
    ∃ e : Fin m → Fin n, StrictMono e ∧ a = e ∘ σ := by
  classical
  let τ : Fin m → Fin ℓ := fun r => Classical.choose (hσsurj r)
  have hτ : Function.RightInverse τ σ := fun r => Classical.choose_spec (hσsurj r)
  let e : Fin m → Fin n := fun r => a (τ r)
  have he : StrictMono e := by
    intro r s hrs
    have hcmp : compare (e r) (e s) = Ordering.lt := by
      simpa [e, otp, hτ r, hτ s, compare_lt_iff_lt.mpr hrs] using
        (congrArg (fun ot => ot (τ r, τ s)) hot).symm
    exact compare_lt_iff_lt.mp hcmp
  refine ⟨e, he, funext fun i => ?_⟩
  have hcmp0 : compare (a i) (a (τ (σ i))) = compare (σ i) (σ (τ (σ i))) := by
    simpa [otp] using (congrArg (fun ot => ot (i, τ (σ i))) hot).symm
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

**Proof strategy.** Given a `k`-coloring
`c : (Fin ℓ → Fin n) → Fin k`, factor each tuple `a : Fin ℓ → V` through
its rank pattern: `a = ã ∘ σ` with `σ : Fin ℓ → Fin m` (`m ≤ ℓ`, the
number of distinct values of `a`) and `ã : Fin m → V` strict-monotone.
The pair `(m, σ)` is fully determined by `otp a`.

Iterate `strictMonoRamseyFinset` over the finite shape type
`Σ m : Fin (ℓ+1), Fin ℓ → Fin m.val`: for each shape `(m, σ)`, apply
`strictMonoRamseyFinset k m _` to the induced coloring
`c_σ ã := c (ã ∘ σ)` and shrink `S`. After all shapes are processed,
define `f` on order types by looking up the color assigned to the
shape induced by each order type. -/
lemma tupleRamseyAtSize (k ℓ M : ℕ) (hk : 0 < k) :
    ∃ Nfin : ℕ, ∀ {n : ℕ} (S : Finset (Fin n)),
      Nfin ≤ S.card → ∀ c : (Fin ℓ → Fin n) → Fin k,
        ∃ I : Finset (Fin n), I ⊆ S ∧ M ≤ I.card ∧
          ∃ f : (Fin ℓ × Fin ℓ → Ordering) → Fin k,
            ∀ a : Fin ℓ → Fin n, (∀ i, a i ∈ I) → c a = f (otp a) := by
  classical
  obtain ⟨Nfin, hNfin⟩ := shapeRamseyFamily k ℓ M hk (Finset.univ : Finset (Shape ℓ))
  refine ⟨Nfin, ?_⟩
  intro n S hS c
  obtain ⟨I, hIsub, hIcard, cols, hIhom⟩ := hNfin S hS c
  refine ⟨I, hIsub, hIcard, ?_⟩
  refine ⟨fun ot => if h : ∃ s : Shape ℓ, otp s.pattern = ot then cols (Classical.choose h)
    else ⟨0, hk⟩, ?_⟩
  intro a hmem
  have hex : ∃ s : Shape ℓ, otp s.pattern = otp a := by
    obtain ⟨s, e, he, hfac⟩ := decomposeTuple a
    refine ⟨s, ?_⟩
    simpa [hfac] using (otp_comp_strictMono (σ := s.pattern) he).symm
  let s : Shape ℓ := Classical.choose hex
  have hs_ot : otp s.pattern = otp a := Classical.choose_spec hex
  obtain ⟨e, he, hfac⟩ := factorThroughShape s.pattern_surjective a hs_ot
  have hemem : ∀ i, e i ∈ I := by
    intro i
    rcases s.pattern_surjective i with ⟨j, rfl⟩
    simpa [hfac] using hmem j
  have hc : c a = cols s := by
    rw [hfac]
    exact hIhom s (by simp) e he hemem
  simpa [hex] using hc

end Lax14Proofs.TupleCore
