import Lax3.SplitterGame

/-!
Clause lemmas for `Lax3.SplitterGame.SplitterWins` and the win on an
edgeless arena. The recursion of `SplitterWins` reduces definitionally
on its budget constructors, so both clauses are `Iff.rfl`; they are
stated here once so that no proof ever hands the concept-side
definition name to a tactic. The same is done for the adjacency of
Lax12's `deleteVerts`, the isolation move both clauses recurse
through.
-/

namespace Lax3Proofs.SplitterBasics

open Lax3.ColoredGraphs Lax3.SplitterGame
open Lax12.UniformQuasiWideness

variable {n : ℕ} {m r ℓ : ℕ} {G : SimpleGraph (Fin n)}

/-- With no rounds left, Splitter has won exactly if the arena is
edgeless. -/
theorem splitterWins_zero_iff : SplitterWins m r 0 G ↔ G = ⊥ := Iff.rfl

/-- With a round left, Splitter wins if the arena is edgeless or every
Connector move admits a batch after which he wins the rest. -/
theorem splitterWins_succ_iff :
    SplitterWins m r (ℓ + 1) G ↔ G = ⊥ ∨
      ∀ v : Fin n, ∃ W : Set (Fin n), W ⊆ ball G r v ∧ W.ncard ≤ m ∧
        SplitterWins m r ℓ (deleteVerts (deleteVerts G (ball G r v)ᶜ) W) :=
  Iff.rfl

/-- An edgeless arena is a winning position at every budget. -/
theorem splitterWins_of_eq_bot (h : G = ⊥) : SplitterWins m r ℓ G :=
  match ℓ with
  | 0 => h
  | _ + 1 => Or.inl h

/-- The adjacency of an isolation, by definition. -/
theorem deleteVerts_adj {V : Type*} {G : SimpleGraph V} {S : Set V} {u v : V} :
    (deleteVerts G S).Adj u v ↔ G.Adj u v ∧ u ∉ S ∧ v ∉ S := Iff.rfl

end Lax3Proofs.SplitterBasics
