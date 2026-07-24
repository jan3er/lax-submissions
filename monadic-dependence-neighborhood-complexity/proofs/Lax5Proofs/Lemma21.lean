import Lax5.MonadicDependence
import Lax5.NeighborhoodComplexity
import Mathlib.Combinatorics.SetFamily.Shatter

/-!
Top of the Appendix-A machinery (DMMPT26). This module states the
interface the headline theorem consumes: Lemma 21 in *semi-induced*
form — in a monadically dependent class, any vertex set `B` whose
members leave pairwise distinct neighborhood traces on a nonempty
vertex set `A` has size at most `c · |A|^(1+ε)` — together with the
ingredient [VC] (neighborhood set systems of a monadically dependent
class have uniformly bounded VC dimension).

Stating Lemma 21 on the class itself, rather than for a class of
bipartite graphs as the paper does, pushes the bipartite-encoding
choices below this interface: the reduction of the paper's Theorem 2
becomes a choice of trace representatives (see `Theorem2`), and the
transduction onto the semi-induced bipartite class happens inside the
proof of this lemma.

TODO(step 4, expansion — see `pipeline.md` §1):
  Lem 21 ← [VC] + Lem 26 (iterated sparsification) + Lem 24 (terminal
  sparsification small, via Lem 23 + Cor 6); Lem 26 ← Lem 25 ← Lem 19,
  Cor 9/Lem 8 (HLW), Lem 10/Lem 7, Lem 12.
-/

namespace Lax5Proofs.Lemma21

open Lax5.GraphClasses Lax5.MonadicDependence Lax5.NeighborhoodComplexity

/-- The neighborhood traces of `G` on the finite vertex set `A`, as a
finite set family: `Finset` counterpart of the trace set underlying
`traceCount`, in the shape mathlib's `Finset.vcDim` consumes. -/
noncomputable def traceFamily {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  letI := Classical.decRel G.Adj
  Finset.univ.image fun v => A.filter (G.Adj v)

/-- Ingredient [VC]: the neighborhood set systems of a monadically
dependent class have uniformly bounded VC dimension. Contrapositive
route: unbounded shattering lets the class transduce all graphs. -/
theorem exists_vcDim_traceFamily_le (C : GraphClass)
    (hC : MonadicallyDependent C) :
    ∃ d : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A : Finset (Fin n), (traceFamily G A).vcDim ≤ d := by
  sorry

/-- Lemma 21 (semi-induced form): in a monadically dependent class,
vertices with pairwise distinct neighborhood traces on a nonempty set
`A` number at most `c · |A|^(1+ε)`. -/
theorem ncard_le_rpow_of_injOn_traces (C : GraphClass)
    (hC : MonadicallyDependent C) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A B : Set (Fin n), A.Nonempty →
        Set.InjOn (fun v => G.neighborSet v ∩ A) B →
        (B.ncard : ℝ) ≤ c * (A.ncard : ℝ) ^ (1 + ε) := by
  sorry

end Lax5Proofs.Lemma21
