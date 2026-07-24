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
  sorry

end Lax5Proofs
