import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries

/-- A graph class is a predicate on finite simple graphs, where the vertex type
    may vary. -/
abbrev GraphClass :=
  ∀ {V : Type}, [DecidableEq V] → [Fintype V] → SimpleGraph V → Prop

end Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries
