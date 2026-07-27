import Lax14.TupleRamsey
import Lax14Proofs.TupleCore

/-!
Ramsey's theorem for tuples in the submitted form.  The ported development of
`Lax14Proofs.TupleCore` records order types as `Ordering`-valued functions on
pairs of coordinates; the submitted statement records them as `Prop`-valued
relations.  The bridge below shows that the coarser-looking `Prop`-valued
notion still determines the `Ordering`-valued one, which is all the transport
needs.
-/

namespace Lax14Proofs.TupleRamsey

open Lax14.OrderTypes

/-- Equal `Prop`-valued order types force equal `Ordering`-valued ones: in a
linear order the strict-order pattern determines the equality pattern. -/
theorem otp_eq_of_orderType_eq {V : Type*} [LinearOrder V] {ℓ : ℕ}
    {a b : Fin ℓ → V} (h : orderType a = orderType b) :
    TupleCore.otp a = TupleCore.otp b := by
  funext p
  obtain ⟨i, j⟩ := p
  have hij : a i < a j ↔ b i < b j := iff_of_eq (congrFun (congrFun h i) j)
  have hji : a j < a i ↔ b j < b i := iff_of_eq (congrFun (congrFun h j) i)
  show compare (a i) (a j) = compare (b i) (b j)
  rcases lt_trichotomy (a i) (a j) with hlt | heq | hgt
  · rw [compare_lt_iff_lt.mpr hlt, compare_lt_iff_lt.mpr (hij.mp hlt)]
  · have hnij : ¬ a i < a j := by rw [heq]; exact lt_irrefl _
    have hnji : ¬ a j < a i := by rw [heq]; exact lt_irrefl _
    have heqb : b i = b j :=
      le_antisymm (not_lt.mp fun hb => hnji (hji.mpr hb))
        (not_lt.mp fun hb => hnij (hij.mpr hb))
    rw [compare_eq_iff_eq.mpr heq, compare_eq_iff_eq.mpr heqb]
  · rw [compare_gt_iff_gt.mpr hgt, compare_gt_iff_gt.mpr (hji.mp hgt)]

/--
---
conclusion: Lax14.TupleRamsey.exists_orderType_homogeneous
---
Every colouring of the `ℓ`-tuples over a large enough linearly ordered finite
set with `k` colours admits a subset of size `s` on which the colour of a
tuple depends only on its order type: the finite Ramsey theorem for
hypergraphs of Erdős and Rado, in the order-type form.

# Proof strategy

The mathematical content is the ported `Lax14Proofs.TupleCore.tupleRamseyAtSize`.
That development first proves Ramsey for *strict-monotone* tuples by the
Erdős–Rado chain-building induction on the arity: for arity `m + 1` one
repeatedly extracts the minimum `v` of the current set, applies the arity-`m`
statement to the colouring `b ↦ c (v ::ᵥ b)` on the rest, and thereby colours
the elements of a long chain by the colour their tuples receive; a pigeonhole
on that colouring of elements produces the homogeneous set.  An arbitrary
tuple is then factored as `a = e ∘ σ` with `σ : Fin ℓ → Fin m` surjective (its
rank pattern, determined by the order type) and `e` strict-monotone, and the
strict-monotone statement is applied once per *shape* `(m, σ)` — a finite type
— shrinking the set each time.  The resulting set is homogeneous for every
shape at once, so the colour of a tuple is read off its shape alone.

Two bridges lead from there to the submitted statement.  The ground set is
taken to be all of `Fin n`, so the ported hypothesis `Nfin ≤ S.card` becomes
`Nfin ≤ n` and the returned `Finset` is coerced to a `Set` with
`Set.ncard_coe_finset`.  And the ported statement concludes with a function
`f` from `Ordering`-valued order types to colours through which the colouring
factors, while the submitted statement says instead that tuples with equal
`Prop`-valued order types get equal colours.  The lemma
`otp_eq_of_orderType_eq` closes that gap in the direction needed: if the
strict-order patterns of two tuples agree then so do their `Ordering`-valued
patterns, because in a linear order `a i = a j` holds exactly when neither
`a i < a j` nor `a j < a i` does.  Both colours are then rewritten through `f`
and coincide.

The submitted statement carries no positivity hypothesis on the number of
colours, whereas the ported one needs one to have a default colour available.
The case `k = 0` is split off first and closed outright: with `N := 1` the
carrier `Fin n` is nonempty, so the assumed colouring applied to the constant
tuple produces an element of `Fin 0`, which is absurd.

# Attribution

The proof is ported from the proof package of the submission
*Monadic dependence and neighborhood complexity*
(`Lax5Proofs/TupleRamsey.lean`).  The theorem is due to Erdős and Rado,
*Combinatorial theorems on classifications of subsets of a given set* (Proc.
London Math. Soc. 1952); the order-type formulation followed here is the one
of Mählmann, *Monadically stable and monadically dependent graph classes*
(PhD thesis, TU Wien 2024), Section 4.
-/
theorem exists_orderType_homogeneous (k ℓ s : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (c : (Fin ℓ → Fin n) → Fin k), N ≤ n →
      ∃ I : Set (Fin n), s ≤ I.ncard ∧
        ∀ a b : Fin ℓ → Fin n, (∀ i, a i ∈ I) → (∀ i, b i ∈ I) →
          orderType a = orderType b → c a = c b := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, fun n c hn => ?_⟩
    exact (c fun _ => ⟨0, hn⟩).elim0
  · obtain ⟨Nfin, hNfin⟩ := TupleCore.tupleRamseyAtSize k ℓ s hk
    refine ⟨Nfin, fun n c hn => ?_⟩
    have hcard : Nfin ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hn
    obtain ⟨I, -, hIcard, f, hf⟩ := hNfin (Finset.univ : Finset (Fin n)) hcard c
    refine ⟨(↑I : Set (Fin n)), ?_, ?_⟩
    · rw [Set.ncard_coe_finset]
      exact hIcard
    · intro a b ha hb hot
      rw [hf a fun i => Finset.mem_coe.mp (ha i),
        hf b fun i => Finset.mem_coe.mp (hb i),
        otp_eq_of_orderType_eq hot]

end Lax14Proofs.TupleRamsey
