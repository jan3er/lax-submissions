import Lax5Proofs.Sparsification
import Lax5Proofs.TransductionCalculus
import Lax5Proofs.Corollary6
import Mathlib.Data.Finset.Sort

/-!
Lemmas 23 and 24 of DMMPT26 in the R1 architecture.

Because the formula tuple of a definable sparsification is the *fixed*
tuple `sparsFormulas k`, the transduction of Lemma 23 has nothing to
guess: `sparsTransduction k` marks the two sides with two fresh colors
`L`, `R` and interprets adjacency by the symmetrized disjunction of the
lifted tuple. The class `sparsGraphs C k` is its image class over `C`,
intersected with `K_{k+1,k+1}`-freeness; it is weakly sparse by
definition, monadically dependent whenever `C` is (by
`Transduces.trans`), and therefore has almost linear neighborhood
complexity by Corollary 6. Lemma 23 becomes the statement that the
sparsification graph of a definable sparsification, on the carrier
`A ∪ reps`, belongs to this class; Lemma 24 follows by counting label
tuples inside neighborhood traces.
-/

namespace Lax5Proofs

open FirstOrder Lax5.Transductions Lax5.GraphClasses
open Lax5.MonadicDependence Lax5.NeighborhoodComplexity
open Lax5.WeaklySparseDependent
open scoped SimpleGraph

variable {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)} {k : ℕ}

/-- The transduction of Lemma 23 (R1 form): two colors beyond the `5k`
of the formula tuple mark the `A`-side (`L`, slot `5k`) and the
representative side (`R`, slot `5k+1`); adjacency is the symmetrized
disjunction of the fixed formula tuple, guarded by the side marks; the
domain is the union of the marks. -/
noncomputable def sparsTransduction (k : ℕ) :
    Transduction Language.graph Language.graph where
  colors := 5 * k + 2
  domain :=
    colorAtom (⟨5 * k, by omega⟩ : Fin (5 * k + 2))
        (Language.Term.var (Sum.inl 0)) ⊔
      colorAtom (⟨5 * k + 1, by omega⟩ : Fin (5 * k + 2))
        (Language.Term.var (Sum.inl 0))
  rel := fun R => match R with
    | .adj =>
      let φ : Fin k → (withColors Language.graph (5 * k + 2)).Formula (Fin 2) :=
        fun j => liftFormula (by omega) (sparsFormulas k j)
      let sL : Fin (5 * k + 2) := ⟨5 * k, by omega⟩
      let sR : Fin (5 * k + 2) := ⟨5 * k + 1, by omega⟩
      let x : (withColors Language.graph (5 * k + 2)).Term (Fin 2 ⊕ Fin 0) :=
        Language.Term.var (Sum.inl 0)
      let y : (withColors Language.graph (5 * k + 2)).Term (Fin 2 ⊕ Fin 0) :=
        Language.Term.var (Sum.inl 1)
      (colorAtom sL x ⊓ colorAtom sR y ⊓
        Language.BoundedFormula.iSup fun j =>
          Language.Formula.relabel ![1, 0] (φ j)) ⊔
      (colorAtom sL y ⊓ colorAtom sR x ⊓
        Language.BoundedFormula.iSup fun j => φ j)

/-- The image class of the Lemma-23 transduction over `C`, intersected
with `K_{k+1,k+1}`-freeness: the graph class against which the
terminal sparsification is counted. -/
def sparsGraphs (C : GraphClass) (k : ℕ) : GraphClass := fun m H =>
  TransductionCalculus.transductionImage (sparsTransduction k)
    (Lax5.GraphTransductions.structureClass C) m H.structure ∧
  ¬ completeBipartiteGraph (Fin (k + 1)) (Fin (k + 1)) ⊑ H

theorem weaklySparse_sparsGraphs (C : GraphClass) (k : ℕ) :
    WeaklySparse (sparsGraphs C k) :=
  ⟨k + 1, fun _ _ hH => hH.2⟩

theorem transduces_sparsGraphs (C : GraphClass) (k : ℕ) :
    Lax5.GraphTransductions.Transduces C (sparsGraphs C k) :=
  TransductionCalculus.Transduces.mono_target
    (TransductionCalculus.transduces_transductionImage
      (sparsTransduction k) (Lax5.GraphTransductions.structureClass C))
    fun _ _ hS => by
      obtain ⟨H, hH, rfl⟩ := hS
      exact hH.1

theorem monadicallyDependent_sparsGraphs {C : GraphClass}
    (hC : MonadicallyDependent C) (k : ℕ) :
    MonadicallyDependent (sparsGraphs C k) := fun h =>
  hC (TransductionCalculus.Transduces.trans (transduces_sparsGraphs C k) h)

theorem hasAlmostLinearNC_sparsGraphs {C : GraphClass}
    (hC : MonadicallyDependent C) (k : ℕ) :
    HasAlmostLinearNC (sparsGraphs C k) :=
  Lax5Proofs.Corollary6.hasAlmostLinearNC_of_weaklySparse_of_monadicallyDependent
    _ (weaklySparse_sparsGraphs C k) (monadicallyDependent_sparsGraphs hC k)

/-- The sparsification graph on the ambient vertex set: each
representative `b ∈ reps` is joined to its labels `f j b`. -/
noncomputable def sparsGraphAux (S : Sparsification G A B k)
    (reps : Finset (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x y => x ∈ reps ∧ ∃ j, S.f j x = y

/-- The sparsification graph on the carrier `A ∪ reps`, the graph `H`
of Lemma 24. -/
noncomputable def sparsGraphOn (S : Sparsification G A B k)
    (reps : Finset (Fin n)) : SimpleGraph (Fin (A ∪ reps).card) :=
  (sparsGraphAux S reps).comap fun i =>
    ((A ∪ reps).orderIsoOfFin rfl i : Fin n)

/-- Lemma 23 of DMMPT26 (R1 form): the sparsification graph of a
definable sparsification, restricted to a set of part representatives,
belongs to `sparsGraphs C k`. Producing it: color the member `G` by
the witness colors of definability plus `L := A` and `R := reps`, and
embed the carrier by `orderIsoOfFin`; `K_{k+1,k+1}`-freeness holds
since `reps`-vertices have degree at most `k` and `A` is disjoint from
`reps ⊆ B`. Open obligation of step 4b. -/
theorem sparsGraphOn_mem_sparsGraphs {C : GraphClass} (hG : C n G)
    (hAB : Disjoint A B) (S : Sparsification G A B k)
    (hdef : S.Definable) {reps : Finset (Fin n)} (hsub : reps ⊆ S.supp)
    (hinj : Set.InjOn S.tup reps) :
    sparsGraphs C k _ (sparsGraphOn S reps) := by
  sorry

/-- Lemma 24 of DMMPT26: over a monadically dependent class, a
definable terminal `k`-sparsification has size at most
`c · |A|^(1+ε)`.

Proof plan: pick one representative per label tuple (`reps`), so
`S.partsCount = reps.card` and `S.size ≤ 2 * reps.card` by
terminality. In `H := sparsGraphOn S reps`, the neighborhood of a
representative is exactly its label set (disjointness of `A` and `B`),
so an `H`-trace `T` on the `A`-side is realized by at most
`|T|^k ≤ k^k` representatives — their label tuples are distinct and
have all coordinates in `T`. Hence
`reps.card ≤ k^k · traceCount H (A-side)`, and `traceCount` is bounded
by `hasAlmostLinearNC_sparsGraphs` via `sparsGraphOn_mem_sparsGraphs`,
transporting traces along `orderIsoOfFin`. Open obligation of step
4b. -/
theorem size_le_of_terminal (C : GraphClass) (hC : MonadicallyDependent C)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A B : Finset (Fin n), Disjoint A B → A.Nonempty →
        ∀ S : Sparsification G A B k, S.Definable → S.Terminal →
          (S.size : ℝ) ≤ c * (A.card : ℝ) ^ (1 + ε) := by
  classical
  obtain ⟨c₀, hc₀⟩ := hasAlmostLinearNC_sparsGraphs hC k ε hε
  refine ⟨2 * (k : ℝ) ^ k * max c₀ 0,
    mul_nonneg (by positivity) (le_max_right c₀ 0), ?_⟩
  intro n G hG A B hAB hA S hdef hterm
  obtain ⟨a₀, ha₀⟩ := hA
  -- one representative per label tuple
  set r : (Fin k → Fin n) → Fin n := fun τ =>
    if h : ∃ b ∈ S.supp, S.tup b = τ then h.choose else a₀ with hr_def
  have hrmem : ∀ τ ∈ S.labels, r τ ∈ S.supp ∧ S.tup (r τ) = τ := by
    intro τ hτ
    obtain ⟨b, hb, hbτ⟩ := Finset.mem_image.1 hτ
    have hex : ∃ b ∈ S.supp, S.tup b = τ := ⟨b, hb, hbτ⟩
    rw [hr_def]
    simp only [dif_pos hex]
    exact ⟨hex.choose_spec.1, hex.choose_spec.2⟩
  set reps : Finset (Fin n) := S.labels.image r with hreps_def
  have hrepsub : reps ⊆ S.supp := by
    intro b hb
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hb
    exact (hrmem τ hτ).1
  have htupinj : Set.InjOn S.tup ↑reps := by
    intro b hb b' hb' htt
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    obtain ⟨τ', hτ', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb')
    rw [(hrmem τ hτ).2, (hrmem τ' hτ').2] at htt
    rw [htt]
  have hcard_reps : reps.card = S.partsCount := by
    rw [hreps_def, Finset.card_image_of_injOn]
    · rfl
    · intro τ hτ τ' hτ' hrr
      rw [← (hrmem τ (Finset.mem_coe.1 hτ)).2, hrr,
        (hrmem τ' (Finset.mem_coe.1 hτ')).2]
  -- the sparsification graph and its `A`-side
  have hb_union : ∀ b ∈ reps, b ∈ A ∪ reps := fun b hb =>
    Finset.mem_union_right _ hb
  set e := (A ∪ reps).orderIsoOfFin rfl with he_def
  set E : Fin (A ∪ reps).card → Fin n := fun i => (e i : Fin n) with hE_def
  have hEinj : Function.Injective E := fun i j h =>
    e.injective (Subtype.ext h)
  set H := sparsGraphOn S reps with hH_def
  have hmem : sparsGraphs C k _ H :=
    sparsGraphOn_mem_sparsGraphs hG hAB S hdef hrepsub htupinj
  have hHAdj : ∀ i x, H.Adj i x ↔
      (sparsGraphAux S reps).Adj (E i) (E x) := fun i x => Iff.rfl
  set A' : Set (Fin (A ∪ reps).card) := {i | E i ∈ A} with hA'_def
  have hA'ne : A'.Nonempty := by
    refine ⟨e.symm ⟨a₀, Finset.mem_union_left _ ha₀⟩, ?_⟩
    show E (e.symm ⟨a₀, Finset.mem_union_left _ ha₀⟩) ∈ A
    rw [hE_def]
    simpa using ha₀
  have hEA' : E '' A' = ↑A := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hx
      refine ⟨e.symm ⟨x, Finset.mem_union_left _ (Finset.mem_coe.1 hx)⟩,
        ?_, ?_⟩
      · show E _ ∈ A
        rw [hE_def]
        simpa using Finset.mem_coe.1 hx
      · rw [hE_def]
        simp
  have hA'card : A'.ncard = A.card := by
    have h := Set.ncard_image_of_injective A' hEinj
    rw [hEA'] at h
    rw [← h]
    exact Set.ncard_coe_finset A
  -- neighborhoods of representatives are exactly their label sets
  set LB : Fin n → Finset (Fin n) := fun b =>
    Finset.univ.image fun j : Fin k => S.f j b with hLB_def
  have hLBsub : ∀ b ∈ reps, LB b ⊆ A := by
    intro b hb x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hx
    exact S.f_mem j b (hrepsub hb)
  have hLBcard : ∀ b, (LB b).card ≤ k := fun b =>
    le_trans Finset.card_image_le (by simp)
  have hAdjAux : ∀ b ∈ reps, ∀ y : Fin n,
      (sparsGraphAux S reps).Adj b y ↔ y ∈ LB b := by
    intro b hb y
    have hbB : b ∈ B := S.supp_subset (hrepsub hb)
    constructor
    · intro hadj
      rw [sparsGraphAux, SimpleGraph.fromRel_adj] at hadj
      obtain ⟨hne, h | h⟩ := hadj
      · obtain ⟨-, j, rfl⟩ := h
        exact Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩
      · obtain ⟨hyreps, j, hjb⟩ := h
        exact absurd hbB
          (Finset.disjoint_left.1 hAB (hjb ▸ S.f_mem j y (hrepsub hyreps)))
    · intro hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      rw [sparsGraphAux, SimpleGraph.fromRel_adj]
      refine ⟨fun heq => ?_, Or.inl ⟨hb, j, rfl⟩⟩
      exact Finset.disjoint_left.1 hAB (S.f_mem j b (hrepsub hb))
        (heq ▸ hbB)
  have htrace : ∀ b (hb : b ∈ reps),
      H.neighborSet (e.symm ⟨b, hb_union b hb⟩) ∩ A' =
        E ⁻¹' ↑(LB b) := by
    intro b hb
    have hEb : E (e.symm ⟨b, hb_union b hb⟩) = b := by
      rw [hE_def]
      simp
    ext x
    simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet,
      Set.mem_preimage, Finset.mem_coe]
    rw [hHAdj, hEb, hAdjAux b hb (E x)]
    constructor
    · rintro ⟨hy, -⟩
      exact hy
    · intro hy
      exact ⟨hy, hLBsub b hb hy⟩
  -- at most `k^k` representatives share a label set
  have hfiber : ∀ ℒ : Finset (Fin n),
      (reps.filter fun b => LB b = ℒ).card ≤ k ^ k := by
    intro ℒ
    rcases Finset.eq_empty_or_nonempty (reps.filter fun b => LB b = ℒ)
      with he | ⟨b₀, hb₀⟩
    · simp [he]
    have hb₀reps := (Finset.mem_filter.1 hb₀).1
    have hLb₀ := (Finset.mem_filter.1 hb₀).2
    have hcardℒ : ℒ.card ≤ k := hLb₀ ▸ hLBcard b₀
    calc (reps.filter fun b => LB b = ℒ).card
        ≤ (Fintype.piFinset fun _ : Fin k => ℒ).card := by
          refine Finset.card_le_card_of_injOn S.tup ?_
            (htupinj.mono (Finset.coe_subset.2 (Finset.filter_subset _ _)))
          intro b hb
          obtain ⟨hbr, hbe⟩ := Finset.mem_filter.1 hb
          simp only [Finset.mem_coe, Fintype.mem_piFinset]
          intro j
          rw [← hbe]
          exact Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩
      _ = ℒ.card ^ k := by
          simp [Fintype.card_piFinset]
      _ ≤ k ^ k := Nat.pow_le_pow_left hcardℒ k
  have hreps_bound : reps.card ≤ (reps.image LB).card * k ^ k := by
    calc reps.card
        = ∑ ℒ ∈ reps.image LB, (reps.filter fun b => LB b = ℒ).card :=
          Finset.card_eq_sum_card_fiberwise fun b hb =>
            Finset.mem_image_of_mem _ hb
      _ ≤ ∑ _ℒ ∈ reps.image LB, k ^ k :=
          Finset.sum_le_sum fun ℒ _ => hfiber ℒ
      _ = (reps.image LB).card * k ^ k := by
          rw [Finset.sum_const, smul_eq_mul]
  -- distinct label sets give distinct traces of `H` on the `A`-side
  have himgcount : (reps.image LB).card ≤ traceCount H A' := by
    have hsubrange : ∀ ℒ ∈ reps.image LB, (↑ℒ : Set (Fin n)) ⊆
        Set.range E := by
      intro ℒ hℒ x hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hℒ
      refine ⟨e.symm ⟨x, Finset.mem_union_left _
        (hLBsub b hb (Finset.mem_coe.1 hx))⟩, ?_⟩
      rw [hE_def]
      simp
    have hinjpre : Set.InjOn (fun ℒ : Finset (Fin n) => E ⁻¹' ↑ℒ)
        ↑(reps.image LB) := by
      intro ℒ₁ h₁ ℒ₂ h₂ hpre
      replace hpre : E ⁻¹' ↑ℒ₁ = E ⁻¹' ↑ℒ₂ := hpre
      apply Finset.coe_injective
      ext x
      constructor
      · intro hx
        obtain ⟨i, rfl⟩ := hsubrange ℒ₁ (Finset.mem_coe.1 h₁) hx
        have hx₁ : i ∈ E ⁻¹' ↑ℒ₁ := hx
        rw [hpre] at hx₁
        exact hx₁
      · intro hx
        obtain ⟨i, rfl⟩ := hsubrange ℒ₂ (Finset.mem_coe.1 h₂) hx
        have hx₂ : i ∈ E ⁻¹' ↑ℒ₂ := hx
        rw [← hpre] at hx₂
        exact hx₂
    have h1 : ((fun ℒ : Finset (Fin n) => E ⁻¹' ↑ℒ) '' ↑(reps.image LB)).ncard
        = (reps.image LB).card := by
      rw [hinjpre.ncard_image, Set.ncard_coe_finset]
    have hfin : {T : Set (Fin (A ∪ reps).card) |
        ∃ v, T = H.neighborSet v ∩ A'}.Finite := by
      have heq : {T : Set (Fin (A ∪ reps).card) |
          ∃ v, T = H.neighborSet v ∩ A'} =
          Set.range fun v => H.neighborSet v ∩ A' := by
        ext T
        simp [Set.mem_range, eq_comm]
      rw [heq]
      exact Set.finite_range _
    have h2 : ((fun ℒ : Finset (Fin n) => E ⁻¹' ↑ℒ) '' ↑(reps.image LB)) ⊆
        {T : Set (Fin (A ∪ reps).card) | ∃ v, T = H.neighborSet v ∩ A'} := by
      rintro T ⟨ℒ, hℒ, rfl⟩
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hℒ)
      exact ⟨e.symm ⟨b, hb_union b hb⟩, (htrace b hb).symm⟩
    calc (reps.image LB).card
        = ((fun ℒ : Finset (Fin n) => E ⁻¹' ↑ℒ) '' ↑(reps.image LB)).ncard :=
          h1.symm
      _ ≤ traceCount H A' := Set.ncard_le_ncard h2 hfin
  -- assemble
  have htcount : (traceCount H A' : ℝ) ≤ c₀ * (A.card : ℝ) ^ (1 + ε) := by
    have := hc₀ _ H hmem A' hA'ne
    rwa [hA'card] at this
  have hsize : S.size ≤ 2 * (traceCount H A' * k ^ k) := by
    calc S.size ≤ 2 * S.partsCount := hterm
      _ = 2 * reps.card := by rw [hcard_reps]
      _ ≤ 2 * ((reps.image LB).card * k ^ k) :=
          Nat.mul_le_mul_left 2 hreps_bound
      _ ≤ 2 * (traceCount H A' * k ^ k) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ himgcount)
  calc (S.size : ℝ)
      ≤ 2 * ((traceCount H A' : ℝ) * (k : ℝ) ^ k) := by exact_mod_cast hsize
    _ = 2 * (k : ℝ) ^ k * (traceCount H A' : ℝ) := by ring
    _ ≤ 2 * (k : ℝ) ^ k * (c₀ * (A.card : ℝ) ^ (1 + ε)) :=
        mul_le_mul_of_nonneg_left htcount (by positivity)
    _ ≤ 2 * (k : ℝ) ^ k * (max c₀ 0 * (A.card : ℝ) ^ (1 + ε)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = 2 * (k : ℝ) ^ k * max c₀ 0 * (A.card : ℝ) ^ (1 + ε) := by ring

end Lax5Proofs
