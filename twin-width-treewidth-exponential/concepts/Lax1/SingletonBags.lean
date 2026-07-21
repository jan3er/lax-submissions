import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic

/-!
---
title: Singleton bag partition
---
For a finite vertex type $V$, $\mathrm{singletonBags}(V)$ is the family
$$\{\{v\}: v\in V\}.$$
-/


namespace Lax1.SingletonBags

noncomputable section

/-- The singleton-bag partition of a finite vertex type. -/
def singletonBags (V : Type) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.image (fun v : V => ({v} : Finset V))

end

end Lax1.SingletonBags
