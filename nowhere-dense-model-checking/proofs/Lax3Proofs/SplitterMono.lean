import Lax3Proofs.SplitterBasics
import Lax3Proofs.WalkDistance

/-!
Monotonicity of Splitter's winning positions in the isolation splitter
game `Lax3.SplitterGame.SplitterWins`.

Arenas of a play only ever lose edges: restricting to Connector's ball
is `deleteVerts` of the ball's complement and isolating Splitter's batch
is `deleteVerts` of the batch, so both moves of a round produce a
`≤`-smaller graph on the same vertex set. The main lemma
`splitterWins_anti` says that Splitter's winning positions are closed
under exactly that relation: if he wins on `G` within `ℓ` rounds, he
wins within `ℓ` rounds on every subgraph `H ≤ G`. One lemma therefore
covers both moves downstream, and no separate statement about
restrictions or isolations is needed.

The strategy transports as follows. Against Connector's vertex `v` in
`H`, Splitter plays the batch `W` he would have played against `v` in
`G`, cut down to the `r`-ball of `v` in `H`. The intersection only
serves the requirement that the batch lie inside the ball Connector just
restricted to — balls shrink with the graph, so `W` itself need not —
and it costs nothing: a vertex of `W` outside that ball has already lost
all its edges to the restriction, so isolating it would change nothing.
The two arenas then compare edge by edge, and the induction hypothesis
applies.

The remaining two lemmas record the obvious about the numerical
parameters: a larger round budget and a larger batch size only help
Splitter. Enlarging the batch reuses the very same batches, and
enlarging the budget reduces to the one-round step `splitterWins_succ`,
which is where the convention that an edgeless arena wins at every
budget pays off — a Splitter who has already won simply keeps winning
for the extra rounds.
-/

namespace Lax3Proofs.SplitterMono

open Lax3.ColoredGraphs Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax3Proofs.SplitterBasics Lax3Proofs.WalkDistance

variable {n : ℕ} {m m' r ℓ ℓ' : ℕ} {G H : SimpleGraph (Fin n)}

/-! ### Passing to a subgraph -/

/-- The arena reached by a round of the game on `H` is a subgraph of the
arena reached by the corresponding round on any `G ≥ H`, provided
Splitter's batch on `H` is his batch `W` on `G` cut down to the smaller
ball. Both restrictions keep only edges of the smaller graph, and a
vertex of the smaller ball escapes the cut-down batch only by escaping
`W`. -/
theorem round_le (hHG : H ≤ G) (v : Fin n) (W : Set (Fin n)) :
    deleteVerts (deleteVerts H (ball H r v)ᶜ) (W ∩ ball H r v) ≤
      deleteVerts (deleteVerts G (ball G r v)ᶜ) W := by
  intro a b hab
  obtain ⟨hrest, haW, hbW⟩ := deleteVerts_adj.mp hab
  obtain ⟨hadj, haC, hbC⟩ := deleteVerts_adj.mp hrest
  have haH : a ∈ ball H r v := not_not.mp haC
  have hbH : b ∈ ball H r v := not_not.mp hbC
  exact deleteVerts_adj.mpr
    ⟨deleteVerts_adj.mpr ⟨hHG hadj,
        fun hc => hc (ball_mono_graph v hHG haH),
        fun hc => hc (ball_mono_graph v hHG hbH)⟩,
      fun hw => haW ⟨hw, haH⟩, fun hw => hbW ⟨hw, hbH⟩⟩

/-- Splitter's winning positions are closed under passing to a subgraph
on the same vertex set: if he wins on `G` within `ℓ` rounds then he wins
within `ℓ` rounds on every `H ≤ G`. As both moves of a round only delete
edges, this single lemma is what lets a win be inherited by every later
arena of a play. -/
theorem splitterWins_anti (hHG : H ≤ G) (h : SplitterWins m r ℓ G) :
    SplitterWins m r ℓ H := by
  induction ℓ generalizing G H with
  | zero => exact splitterWins_zero_iff.mpr (le_bot_iff.mp (splitterWins_zero_iff.mp h ▸ hHG))
  | succ ℓ ih =>
    rcases splitterWins_succ_iff.mp h with hbot | hmove
    · exact splitterWins_of_eq_bot (le_bot_iff.mp (hbot ▸ hHG))
    refine splitterWins_succ_iff.mpr (Or.inr fun v => ?_)
    obtain ⟨W, -, hcard, hwin⟩ := hmove v
    refine ⟨W ∩ ball H r v, Set.inter_subset_right, ?_, ?_⟩
    · exact (Set.ncard_le_ncard Set.inter_subset_left W.toFinite).trans hcard
    · exact ih (round_le hHG v W) hwin

/-! ### Monotonicity in the parameters -/

/-- A round of budget is never a burden: a position won within `ℓ`
rounds is won within `ℓ + 1`. Splitter plays his `ℓ`-round strategy and
the arena it leaves is edgeless, hence a win with the round to spare. -/
theorem splitterWins_succ (h : SplitterWins m r ℓ G) : SplitterWins m r (ℓ + 1) G := by
  induction ℓ generalizing G with
  | zero => exact splitterWins_of_eq_bot (splitterWins_zero_iff.mp h)
  | succ ℓ ih =>
    rcases splitterWins_succ_iff.mp h with hbot | hmove
    · exact splitterWins_of_eq_bot hbot
    refine splitterWins_succ_iff.mpr (Or.inr fun v => ?_)
    obtain ⟨W, hball, hcard, hwin⟩ := hmove v
    exact ⟨W, hball, hcard, ih hwin⟩

/-- Splitter's winning positions grow with the round budget. -/
theorem splitterWins_mono_budget (hℓ : ℓ ≤ ℓ') (h : SplitterWins m r ℓ G) :
    SplitterWins m r ℓ' G := by
  induction ℓ', hℓ using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact splitterWins_succ ih

/-- Splitter's winning positions grow with the batch size: the same
batches are still legal when more vertices per round are allowed. -/
theorem splitterWins_mono_batch (hm : m ≤ m') (h : SplitterWins m r ℓ G) :
    SplitterWins m' r ℓ G := by
  induction ℓ generalizing G with
  | zero => exact splitterWins_of_eq_bot (splitterWins_zero_iff.mp h)
  | succ ℓ ih =>
    rcases splitterWins_succ_iff.mp h with hbot | hmove
    · exact splitterWins_of_eq_bot hbot
    refine splitterWins_succ_iff.mpr (Or.inr fun v => ?_)
    obtain ⟨W, hball, hcard, hwin⟩ := hmove v
    exact ⟨W, hball, hcard.trans hm, ih hwin⟩

end Lax3Proofs.SplitterMono
