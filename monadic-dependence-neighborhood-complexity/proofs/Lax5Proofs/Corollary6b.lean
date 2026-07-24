import Lax5.NowhereDenseNC

/-!
Corollary 6b at radius 1: nowhere dense classes have almost linear
neighborhood complexity. Top of the sparsity chain surveyed in
`pipeline.md` §3a.

TODO(step 4, expansion — see `pipeline.md` §3a):
  K_{t,t}-freeness (item 2) → elementary VC bounds (item 3) →
  densification ∇₁ ≤ f(ε)·n^ε (item 4, the bulk) → wcol₂ ≤ n^ε
  (item 5) → counting with weak coloring orders (item 6) →
  localization + assembly (item 7).
-/

namespace Lax5Proofs.Corollary6b

open Lax5.GraphClasses Lax5.NeighborhoodComplexity Lax5.NowhereDenseClasses

/--
---
conclusion: Lax5.NowhereDenseNC.hasAlmostLinearNC_of_nowhereDense
---
Nowhere dense graph classes have almost linear neighborhood complexity:
the radius-1 case of the theorem of Eickmeyer, Giannopoulou, Kreutzer,
Kwon, Pilipczuk, Rabinovich, Siebertz.

# Proof strategy

Radius-1 specialization of the generalized-coloring-number route: a
nowhere dense class is K_{t,t}-free, so its neighborhood set systems
have VC dimension O(t + log t); Dvořák's densification bounds the
depth-1 grad by f(ε)·n^ε, which bounds the weak 2-coloring number;
counting neighborhood traces along a weak coloring order then yields
|A| · n^ε traces, and localization to a polynomially small witness set
rescales this to c · |A|^(1+ε).

# Attribution

Sparsity lecture notes of Pilipczuk, Pilipczuk, Siebertz (chapters 1,
2, 5), specialized to radius 1; densification following Dvořák.
-/
theorem hasAlmostLinearNC_of_nowhereDense (C : GraphClass)
    (h : NowhereDense C) : HasAlmostLinearNC C := by
  sorry

end Lax5Proofs.Corollary6b
