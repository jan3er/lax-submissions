import Lax3Proofs.Refine.BfsBlock
import Lax3Proofs.Refine.CoverBlock

/-!
# The block engine's charge, in the cover's vocabulary

`BfsBlock.lean` states the engine's cost in the two numbers the walk
actually pays out of — the ball's slot weight and the ball's size. The
cover's per-centre obligation, `CoverBlock.CentreImplementsB`, is stated
in `MassWeight.blockWeight`. This file is the bridge, and it is short,
because the weight side is entirely landed: `slotWeight_csrW_eq` already
reads `slotWeight n (csrW n O)` as `blockSize + blockRowSum`, which is
exactly "members plus row slots", which is exactly what the engine
charges.

The consequence is the one E3a's §5 said it was waiting for. That
section recorded the obligation as *open at nested arenas*, because
"the package's only search export is `Refine.BfsBridge.bfsQCom_spec` at
a carrier cost". It is no longer the only one, and
`centreObligation_of_ballCost` below is the ball-weight twin of
`centreObligation_of_carrierCost`: a per-centre body running at
`bfsBlockK` discharges the obligation at `kc = 80`, with no root
hypothesis and no `n`.

The wiring itself — which body, which `I`, which counter — is E6's, and
this file does not presume it. What it lands is the step that makes the
wiring one application.
-/

namespace Lax3Proofs.Refine.BfsBlock

open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-- **The engine's charge fits a centre's budget at `kc = 80`.** The
ball's size and slot weight are read against the block the cover hands
the centre, in `MassWeight`'s own vocabulary, and the two readings meet
at `slotWeight_csrW_eq` with nothing left over. -/
theorem ballCost_le_slotWeight {n : ℕ} (O Xoff Xmem : ℕ → ℕ) {c : ℕ}
    (hmem : ∀ p, Xoff c ≤ p → p < Xoff (c + 1) → Xmem p < n)
    {bw nb : ℕ} (hnb : nb ≤ MassMath.blockSize Xoff c)
    (hbw : bw ≤ MassWeight.blockRowSum O Xoff Xmem c) :
    bfsBlockK bw nb
      ≤ 80 * (MassWeight.slotWeight n (MassWeight.csrW n O) Xoff Xmem c + 1) := by
  rw [MassWeight.slotWeight_csrW_eq O Xoff Xmem hmem]
  exact le_trans (bfsBlockK_mono hbw hnb) (bfsBlockK_le_weight _ _)

/-- **The ball-weight discharge of the cover's per-centre obligation.**
The twin of `CoverBlock.centreObligation_of_carrierCost`, and the point
of the whole engine: a body that runs at the block engine's charge meets
the obligation at every arena, not only at the root, because
`bfsBlockK` mentions no carrier. The caller supplies, per centre, the
fit of that centre's ball inside that centre's block — which is
`ballCost_le_slotWeight` at each `k`. -/
theorem centreObligation_of_ballCost {B : ℕ} {body : Com} {I : Env → Prop} {x : String}
    {mlen : ℕ} {bw bws nbs : ℕ → ℕ}
    (hfit : ∀ k, k < mlen → bfsBlockK (bws k) (nbs k) ≤ 80 * (bw k + 1))
    (h : ∀ k, k < mlen → Spec B (fun σ => I σ ∧ σ.vars x = k) body
      (fun _ σ' => I σ' ∧ σ'.vars x = k + 1) (bfsBlockK (bws k) (nbs k))) :
    CoverBlock.CentreImplementsB B x body I mlen 80 bw :=
  fun k hk => (h k hk).mono (by
    simpa only [CoverBlock.centreK] using hfit k hk)

/-- The loop's own budget then follows from the landed rule, with the
cover's constant read at `80` rather than the root's `150`. -/
theorem coverLoopK_of_ballCost {B : ℕ} {body : Com} {I : Env → Prop}
    (x mlenName : String) {mlen : ℕ} {bw bws nbs : ℕ → ℕ} (hNB : mlen < B)
    (hxN : ∀ σ, I σ → σ.vars x ≤ mlen) (hm : ∀ σ, I σ → σ.vars mlenName = mlen)
    (hfit : ∀ k, k < mlen → bfsBlockK (bws k) (nbs k) ≤ 80 * (bw k + 1))
    (h : ∀ k, k < mlen → Spec B (fun σ => I σ ∧ σ.vars x = k) body
      (fun _ σ' => I σ' ∧ σ'.vars x = k + 1) (bfsBlockK (bws k) (nbs k))) :
    Spec B (fun σ => I (σ.setVar x 0)) (CoverBlock.centreLoopCom x mlenName body)
      (fun _ σ' => I σ' ∧ σ'.vars x = mlen) (CoverBlock.coverLoopK 80 mlen bw) :=
  CoverBlock.centreLoop_spec x mlenName mlen 80 bw hNB hxN hm
    (centreObligation_of_ballCost hfit h)

/-! ### The gap the engine closes, on data

E3a's `carrierCentre_no_ball_bound` says a carrier-charged centre cost
admits **no** ball-weight budget: for any pair of constants there is an
instance that breaks it. The block engine's does, at a fixed constant,
on the same instances — that contrast is the whole delta of this wave. -/

/-! A centre whose ball is four vertices and six slots, inside carriers
of `10³` and `10⁶`: the landed per-centre charge tracks the carrier, and
the block engine's does not move. -/
#guard RamCover.centreCost 1000 2000 = 200100
#guard RamCover.centreCost 1000000 2000000 = 200000100
#guard bfsBlockK 6 4 = 644
#guard bfsBlockK 6 4 < RamCover.centreCost 1000 2000
#guard bfsBlockK 6 4 ≤ 80 * (4 + 6 + 1)

/-! And the budget the cover asks for is met at the ball, where the
carrier reading is not: `centreK 80 10` is the block's own budget. -/
#guard bfsBlockK 6 4 ≤ CoverBlock.centreK 80 10
#guard ¬ (RamCover.centreCost 1000 2000 ≤ CoverBlock.centreK 80 10)

/-! ### The clock, against the landed search itself

`BfsBridge.bfsQCost n ns = 56 n + 40 ns + 65` is the package's landed
search charge, and `G2CostProbe.bfsQCost_le_weight` reads it against the
*carrier's* weight. At a four-vertex ball with six slots the block
engine's charge is `644` however large the carrier grows; the landed one
tracks it. These two lines are the same ball at two carriers. -/

#guard BfsBridge.bfsQCost 400 6 = 22705
#guard BfsBridge.bfsQCost 100000 6 = 5600305
#guard bfsBlockK 6 4 < BfsBridge.bfsQCost 400 6
#guard bfsBlockK 6 4 < BfsBridge.bfsQCost 100000 6

#print axioms centreObligation_of_ballCost
#print axioms ballCost_le_slotWeight

end Lax3Proofs.Refine.BfsBlock
