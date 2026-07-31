import Mathlib.Tactic

/-!
The two lemma collections of `NREST_Automation.thy`.

They live in their own module because Lean's generated simp attributes
cannot be used in the module that declares them.  `Automation.lean`
imports this file, populates both collections, and implements the tactics
that consume them.
-/

namespace Lax13Proofs.Refine

/-- Normalization rules for cost vectors and exchange expressions. -/
register_simp_attr norm_cost

/-- Normalization rules for compositions of exchange rates. -/
register_simp_attr norm_pp

end Lax13Proofs.Refine
