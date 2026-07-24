import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries.Full

open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor
open Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries

namespace Lax5Proofs.Source.Catalog.SparsityLectures.NowhereDense

/-- A uniform excluded-clique bound on depth-`d` minors of graphs in `C`.
    The parameter `t` is the allowed clique size, so the excluded graph is
    `K_{t+1}`. -/
def HasShallowCliqueBound (C : GraphClass) (d t : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V),
    C G → ¬IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) G d

/-- A class `C` of graphs is nowhere dense if for every depth `d` there is a
    bound `t` such that no graph in `C` contains `K_{t+1}` as a depth-`d`
    minor. (Def 2.6) -/
def IsNowhereDense (C : GraphClass) : Prop :=
  ∀ d : ℕ, ∃ t : ℕ, HasShallowCliqueBound C d t

end Lax5Proofs.Source.Catalog.SparsityLectures.NowhereDense
