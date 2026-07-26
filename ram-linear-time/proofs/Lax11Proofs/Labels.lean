import Lax11.ConnectedComponents
import Mathlib.Tactic

/-!
Basic facts about the component labelling, and sanity checks against
concrete graphs: the labelling of the complete graph on two vertices is
`[0, 0]`, that of the edgeless graph on two vertices is `[0, 1]`.

The characterization `label_eq` is the form in which later work will
use the labelling: it is the least vertex of the component, so it is
determined by exhibiting a reachable vertex that is at most every
reachable vertex.
-/

namespace Lax11Proofs.Labels

open Lax11.ConnectedComponents

/-- The label of `v` is `u` as soon as `u` is reachable from `v` and no
vertex reachable from `v` is smaller. -/
theorem label_eq {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (hu : G.Reachable u v) (hmin : ∀ w : Fin n, G.Reachable w v → u ≤ w) :
    label G v = u := by
  have hne : (Fin.val '' {w : Fin n | G.Reachable w v}).Nonempty :=
    ⟨u, u, hu, rfl⟩
  refine le_antisymm (Nat.sInf_le ⟨u, hu, rfl⟩) ?_
  obtain ⟨w, hw, hwval⟩ := Nat.sInf_mem hne
  show (u : ℕ) ≤ sInf (Fin.val '' {w : Fin n | G.Reachable w v})
  rw [← hwval]
  exact Fin.le_def.mp (hmin w hw)

/-- Every vertex of the complete graph on two vertices is labelled by
its least vertex. -/
theorem ccLabels_top : ccLabels (⊤ : SimpleGraph (Fin 2)) = [0, 0] := by
  have h : ∀ v : Fin 2, label (⊤ : SimpleGraph (Fin 2)) v = 0 := by
    intro v
    refine label_eq _ 0 v (SimpleGraph.reachable_top) (fun w _ => Fin.zero_le w)
  simp [ccLabels, List.ofFn_succ, h]

/-- In the edgeless graph every vertex is its own component, so it is
labelled by itself. -/
theorem ccLabels_bot : ccLabels (⊥ : SimpleGraph (Fin 2)) = [0, 1] := by
  have h : ∀ v : Fin 2, label (⊥ : SimpleGraph (Fin 2)) v = v := by
    intro v
    refine label_eq _ v v (SimpleGraph.Reachable.refl v) (fun w hw => ?_)
    exact le_of_eq (SimpleGraph.reachable_bot.mp hw).symm
  simp [ccLabels, List.ofFn_succ, h]

end Lax11Proofs.Labels
