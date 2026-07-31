import Lax3Proofs.TgtWidenProbe
import Lax3Proofs.Refine.G2CostProbe
import Lax3Proofs.Refine.ScatterBlockProg

/-!
# ND-MC rebase G2/E-order — the order phase's carrier floor, compiled,
and the no-escape theorem

Wave E-order was tasked with discharging the ordering phase at the
arena-charged cost `G2CostProbe.orderCostA` and re-threading the root's
`hKo` slot to the §2.1 form, closing `g2_plug`'s `hKo` implication.
**This file is the wave's honest compiled verdict: the discharge is not
reachable from the landed package by any interface move, because the
program half is missing at every pass.** Three findings, each compiled:

1. **The overcharge, on data** (§1 — the wave's falsification gate).
   The CURRENT `RamDriver.orderCom` text is run through
   `TgtWidenProbe.execC` at a two-vertex arena inside a 100- and a
   200-vertex carrier, and at the empty arena. The clock is affine in
   the CARRIER at a fixed arena — `650·n + c` at `R = 0`, `1455·n + c`
   at `R = 1` — and the whole arena's own share of a 100-carrier run is
   `496` of `66 146`. The concrete twin of `G2CostProbe.hKo_gap`: the
   200-carrier clock refutes `orderCostA` read at the arena's weight
   `4`, and the SAME clock fits `orderCostA` read at the root weight
   `202` — the mismatch is purely the reading point. The empty-arena
   clock is `Ω(n)`, so no budget for THIS text can have the
   `O(1)`-class empty-arena charge that `hKo_gap`'s route needs dead:
   the repair is a program delta, not a sharper walk of the same text.

2. **The no-escape theorem** (§2). Against the REAL slot shapes of
   `RamDriverRoot.levelAt` — its `hKs` at `turnCostSize` and its
   Σ-shaped `hKl`, byte for byte — ANY budget family whose level-1
   order slot charges even `c` on the EMPTY arena has root cost
   `≥ m·(c + 11)` at every root weight `m`
   (`nested_emptyCharge_floor`). Corollary `emptyCharge_route_dead`:
   at the probe's own ε = 1 numerals a `1·n` empty-arena charge —
   1600× below the landed budget's carrier coefficient — already
   exceeds the `g2_exists` closed form at `n = 10¹¹`, generically in
   the formula and the turn-cost family. So the §4-fallback of the
   wave brief ("weakest sufficient form") is PINNED: every solvable
   `hKo` form is `O(1)`-class on the empty arena, i.e. is
   `orderCostA`-class; there is no interface between the landed
   carrier form and the arena form. The program half is unavoidable.

3. **The after-side control** (§3). The member-list pattern the
   interior must adopt EXISTS in the package and is carrier-free on
   the same instrument: E4b's `Refine.ScatterBlock.clearMem` (walks
   `mem[0..mm)`, clears exactly the listed cells, `MemList`
   sound/complete vocabulary, budget `clearMemK mm = 25·mm + 12`)
   clocks **34 at `n = 100` and 34 at `n = 200`** at two members —
   against the order text's `+650` per carrier vertex. The revision
   target is compiled as a differential the successor wave must
   reproduce pass by pass.

## Why the program half exceeds one wave (the E6-survey scope, sharpened)

Every pass of `orderCom R j` is carrier-bounded: `saveCsr`/`restoreCsr`
and the `ioff → doff` copy walk `n + 1` offset cells; the mask copy,
the rank inversion, the `alv` fill and the eight zeroing fills of
`orderZeroCom` walk `n`; `symCom`'s offset fill walks `n + 1` and
`forVerts` walks `n`; the two `RamElim.elimCom` entries and each
`augRoundCom` (three prep fills at `n`/`n + 1`, `RamAugment.augCom`,
nine relink passes at `n`/`n + 1`) scan the carrier. The E2b live-width
copies (`gtg`/`dtg`/`ntg` at `"lw"`) are the ONLY arena-driven walks in
the phase. There is no member list to drive the rest with: R1.6 is
unbuilt — `LevelPre` threads masks, not member lists, and no phase
produces one (building it from the mask is itself a carrier scan, so it
must be handed down by the parent's descend pass, which enumerates the
block's members already).

## The exact next surface (the successor waves' brief, in order)

1. **Member-list threading** (driver-stack wave): `LevelPre` gains a
   member-list clause (`memName j` array + alive-count scalar, dense
   prefix, `MemList`-sound/complete against the mask);
   `RamDriverDescend`'s child-mask writes also emit the child's member
   list; every phase's frame section carries the new names.
2. **Member-driven engines** (one wave per family, the E6 survey's
   scope): elimination (`RamElim.elimCom`'s init scan and bucket walk
   at the member list — the bucket-pointer walk needs the amortized
   reading), augmentation rounds + relink/prep bookkeeping at the
   member list and the live width, symmetrization, and the phase's
   fills via the `clearMem` pattern (§3). The `n + 1`-cell offset
   walks die only with the compacted arena CSR (design §3(c)).
3. **The phase text + walk** (E-order re-run): `orderCom` rebuilt from
   the member-driven passes, `OrderImplementsRL` re-discharged at
   `orderCostA (bsq d D₁ R) R (arena weight)`, `levelAt`'s `hKo` at the
   §2.1 form, `g2_plug`'s `hKo` implication deleted. The gate:
   this file's §1 clocks re-run against the new text must drop to
   arena-affine, and the §1 refutation guard must flip.

Nothing here edits a frozen surface; the landed `orderImplements₀` /
`orderImplementsR` stand — sound, carrier-charged — and the §1 sanity
guards check the landed budgets still cover the text's clock.
-/

namespace Lax3Proofs.Refine.OrderBlockProbe

open Lax3Proofs.TgtWidenProbe Lax13Proofs.Imp

/-! ### §1 The overcharge, on data (the falsification gate)

The instrument is E2b's cost-carrying interpreter
`TgtWidenProbe.execC`; the instances are the brief's: a two-vertex
arena — vertices `0, 1` joined by one edge, arena weight
`(1 + 1) + (1 + 1) = 4` — inside carriers of 100 and 200 vertices
(every other vertex dead and isolated, `ns = 2`, `m = 1`), and the
empty arena (`ns = m = 0`). The states are `TgtWidenProbe.ordStAt`'s
shape at a parametric carrier: the level's CSR in `off`/`tgt` (the
target array at the allocation width `W`), the reserved pair, the
depth-0 masks, and the engines' scratch fresh from `augSt`. `W = 8`
at `R = 0`; `W = 40` at `R = 1` (room for the round's chain, as
`ordStAt`'s `K₁,₄` gate needs at width 64 for `n = 5` — the double
star's chain; the light arena's chain is small). -/

/-- The two-vertex arena in an `n`-carrier: one edge `0 — 1`, everyone
else dead and isolated. -/
def edgeArenaSt (n W : ℕ) : PSt :=
  { augSt n W W (List.replicate (n + 1) 0) [] with
    vars := [("n", n), ("m", 1), ("lw", W)]
    arrs :=
      ("off", 0 :: 1 :: List.replicate (n - 1) 2) ::
      ("tgt", [1, 0] ++ List.replicate (W - 2) 0) ::
      ("gof", List.replicate (n + 1) 0) :: ("gtg", List.replicate W 0) ::
      (RamDriver.alvName 0, [1, 1] ++ List.replicate (n - 2) 0) ::
      (RamDriver.gamName 0, List.replicate n 1) ::
      (RamDriver.ordName 0, List.replicate n 0) ::
      (augSt n W W (List.replicate (n + 1) 0) []).arrs }

/-- The empty arena in an `n`-carrier: no member, no slot. -/
def emptyArenaSt (n W : ℕ) : PSt :=
  { augSt n W W (List.replicate (n + 1) 0) [] with
    vars := [("n", n), ("m", 0), ("lw", W)]
    arrs :=
      ("off", List.replicate (n + 1) 0) ::
      ("tgt", List.replicate W 0) ::
      ("gof", List.replicate (n + 1) 0) :: ("gtg", List.replicate W 0) ::
      (RamDriver.alvName 0, List.replicate n 0) ::
      (RamDriver.gamName 0, List.replicate n 1) ::
      (RamDriver.ordName 0, List.replicate n 0) ::
      (augSt n W W (List.replicate (n + 1) 0) []).arrs }

/-- The phase's clock on a probe state. -/
def orderClock (R : ℕ) (st : PSt) : ℕ := (execC pB pF (RamDriver.orderCom R 0) st).2

-- the phase completes on every instance
#guard (execC pB pF (RamDriver.orderCom 0 0) (edgeArenaSt 100 8)).1.isOk
#guard (execC pB pF (RamDriver.orderCom 0 0) (edgeArenaSt 200 8)).1.isOk
#guard (execC pB pF (RamDriver.orderCom 0 0) (emptyArenaSt 100 8)).1.isOk
#guard (execC pB pF (RamDriver.orderCom 0 0) (emptyArenaSt 200 8)).1.isOk
#guard (execC pB pF (RamDriver.orderCom 1 0) (edgeArenaSt 100 40)).1.isOk
#guard (execC pB pF (RamDriver.orderCom 1 0) (edgeArenaSt 200 40)).1.isOk

-- **the pinned clocks**: affine in the carrier at a FIXED arena
#guard orderClock 0 (edgeArenaSt 100 8) = 66146
#guard orderClock 0 (edgeArenaSt 200 8) = 131146
#guard orderClock 0 (emptyArenaSt 100 8) = 65650
#guard orderClock 0 (emptyArenaSt 200 8) = 130650
#guard orderClock 1 (edgeArenaSt 100 40) = 149184
#guard orderClock 1 (edgeArenaSt 200 40) = 294684

-- **the affine law**: +650 per carrier vertex at `R = 0`, +1455 at
-- `R = 1` — with the arena UNCHANGED (every added vertex is dead)
#guard orderClock 0 (edgeArenaSt 200 8) - orderClock 0 (edgeArenaSt 100 8) = 650 * 100
#guard orderClock 0 (emptyArenaSt 200 8) - orderClock 0 (emptyArenaSt 100 8) = 650 * 100
#guard orderClock 1 (edgeArenaSt 200 40) - orderClock 1 (edgeArenaSt 100 40) = 1455 * 100

-- **the arena's own share is noise**: adding the whole two-vertex
-- arena to the empty one moves a 100-carrier run by 496 of 66 146
#guard orderClock 0 (edgeArenaSt 100 8) - orderClock 0 (emptyArenaSt 100 8) = 496

-- **the concrete twin of `hKo_gap`**: the 200-carrier clock refutes
-- the §2.1 budget read at the arena's weight 4 …
#guard ¬ (orderClock 0 (edgeArenaSt 200 8) ≤
  G2CostProbe.orderCostA (G2CostProbe.bsq 2 2 0) 0 4)
-- … and the SAME clock fits the SAME budget read at the root weight —
-- the defect is the reading point, not the coefficient
#guard orderClock 0 (edgeArenaSt 200 8) ≤
  G2CostProbe.orderCostA (G2CostProbe.bsq 2 2 0) 0 (200 + 2)

-- **the empty-arena charge is Ω(n), not O(1)**: the route `hKo_gap`
-- needs dead is alive in the text itself, at both carriers
#guard ¬ (orderClock 0 (emptyArenaSt 100 8) ≤
  G2CostProbe.orderCostA (G2CostProbe.bsq 2 2 0) 0 0)
#guard ¬ (orderClock 0 (emptyArenaSt 200 8) ≤
  G2CostProbe.orderCostA (G2CostProbe.bsq 2 2 0) 0 0)

-- **sanity, the landed direction**: the landed carrier budgets still
-- cover the text's clock on these instances — the walks are sound;
-- only their charging point is carrier-bound
#guard orderClock 0 (edgeArenaSt 100 8) ≤ RamDriverCompose.orderPhaseCost 100 2 8
#guard orderClock 0 (emptyArenaSt 200 8) ≤ RamDriverCompose.orderPhaseCost 200 0 8
#guard orderClock 1 (edgeArenaSt 100 40) ≤ RamDriverCompose.orderPhaseCostR 100 2 40 1

/-! ### §2 The no-escape theorem

`RamDriverRoot.levelAt`'s two Σ-interface slots, byte for byte — `hKs`
at `turnCostSize` (whose `Kin` summand is the nested level's own
budget) and the Σ-shaped `hKl` — force any empty-arena order charge to
multiply into the root by the block count. The derivation is the
C0Probe floor's route with everything stripped but the one load it
needs: `t := m` empty blocks (`bs := 0` satisfies every mass bound),
each block's turn contains the level below it, and the level below
pays its order slot on the empty arena. -/

/-- **Any empty-arena order charge multiplies into the root.** Against
the real slot shapes, a budget family whose level-1 order slot pays
`Ko 1 0` on the empty arena has root cost at least `m · (Ko 1 0 + 11)`
at every root weight `m`. (With `Ko 1 0` of the order of `n` — which
§1 shows the current text forces on every budget that covers it — this
is the `Ω(n²)` floor; with `Ko 1 0` constant it is harmless, which is
exactly `orderCostA`'s empty-arena reading,
`G2CostProbe.emptyArena_charge_const`.) -/
theorem nested_emptyCharge_floor {n ns cap mb q_top ℓ Kmass : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {Ksc : ℕ → ℕ} {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}
    (hℓ : 2 ≤ ℓ)
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      RamDriverRoot.turnCostSize n ns cap mb q_top j φ (Ksc j) t (Kl (j + 1) t) ≤ Ks j t)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m) :
    ∀ m, m * (Ko 1 0 + 11) ≤ Kl 0 m := by
  intro m
  -- the turn contains the level below it
  have hKin : Kl 1 0 ≤ Ks 0 0 := by
    refine le_trans ?_ (hKs 0 (by omega) 0)
    simp only [RamDriverRoot.turnCostSize, RamDriverRoot.turnCost, Nat.zero_add]
    omega
  -- the level below pays its order slot on the empty arena
  have h1 : Ko 1 0 ≤ Kl 1 0 := by
    have h := hKl 1 (by omega) 0 0 le_rfl (fun _ => 0) (by simp)
    simp only [Finset.range_zero, Finset.sum_empty] at h
    omega
  -- `m` empty blocks at the root level
  have h0 := hKl 0 (by omega) m m le_rfl (fun _ => 0) (by simp)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h0
  have hmul : m * (Ko 1 0 + 11) ≤ m * (Ks 0 0 + 11) :=
    Nat.mul_le_mul_left m (by have := le_trans h1 hKin; omega)
  refine le_trans hmul ?_
  generalize hP : m * (Ks 0 0 + 11) = P at h0 ⊢
  omega

/-- **The fallback route is dead, compiled.** Generically in the
formula, the word parameters and the turn-cost family: no budget
family satisfies the real slot shapes, charges even `1·n` on the
level-1 empty arena — 1600× below the landed `orderPhaseCost`'s
carrier coefficient — and still closes to the `g2_exists` witness's
budget, at the probe's own ε = 1 numerals read at `n = 10¹¹`. Every
solvable `hKo` form is therefore `O(1)`-class on the empty arena —
`orderCostA`-class — and §1 shows the current text supports no such
form: the member-list interior is the only route to the §2.1 slot. -/
theorem emptyCharge_route_dead (cap mb q_top : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (Ksc : ℕ → ℕ) :
    ¬ ∃ (Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ),
      (∀ j < 3, ∀ t : ℕ,
        RamDriverRoot.turnCostSize (10 ^ 11) (2 * (10 ^ 11 - 1)) cap mb q_top j φ
          (Ksc j) t (Kl (j + 1) t) ≤ Ks j t) ∧
      (∀ j < 3, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
        (∑ c ∈ Finset.range t, bs c) ≤ 8 * (m + 1) →
        Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
          ≤ Kl j m) ∧
      (10 ^ 11 ≤ Ko 1 0) ∧
      (∀ w, Kl 0 w ≤
        (3 * G2CostProbe.g2A 2 2 1 (10 ^ 4) (10 ^ 4) (10 ^ 4) (10 ^ 4) 8 + 10 ^ 4) *
          (8 + 1) ^ 3 * (w + 1)) := by
  rintro ⟨Ko, Kc, Kd, Ks, Kl, hKs, hKl, hKo1, hclose⟩
  have hfloor := nested_emptyCharge_floor (by omega) hKs hKl
    (10 ^ 11 + 2 * (10 ^ 11 - 1))
  have hup := hclose (10 ^ 11 + 2 * (10 ^ 11 - 1))
  have hcharge : (10 ^ 11 + 2 * (10 ^ 11 - 1)) * (10 ^ 11 + 11) ≤
      (10 ^ 11 + 2 * (10 ^ 11 - 1)) * (Ko 1 0 + 11) :=
    Nat.mul_le_mul_left _ (by omega)
  have hcontra : (10 ^ 11 + 2 * (10 ^ 11 - 1)) * (10 ^ 11 + 11) ≤
      (3 * G2CostProbe.g2A 2 2 1 (10 ^ 4) (10 ^ 4) (10 ^ 4) (10 ^ 4) 8 + 10 ^ 4) *
        (8 + 1) ^ 3 * ((10 ^ 11 + 2 * (10 ^ 11 - 1)) + 1) :=
    le_trans hcharge (le_trans hfloor hup)
  exact absurd hcontra (by decide +kernel)

/-! ### §3 The after-side control: the member-list pattern is
carrier-free, on the same instrument

E4b's clearing engine `Refine.ScatterBlock.clearMem` — the landed
member-list pass (`MemList` sound/complete, budget
`clearMemK mm = 25·mm + 12`) — run on two members inside the same two
carriers §1 used. The clock does not read the carrier at all: `34` at
`n = 100` and `34` at `n = 200`, against the order text's `+650` per
carrier vertex. This is the differential the successor wave's phase
revision must reproduce pass by pass: after the member-driven interior
lands, §1's clocks re-run arena-affine and §1's refutation guard
flips. -/

/-- Two members inside an `n`-carrier, for the clearing engine. -/
def clearSt (n : ℕ) : PSt :=
  { vars := [("mm", 2)]
    arrs := [("mem", [0, 1]), ("exc", List.replicate n 1)]
    inp := [] }

#guard (execC pB pF Refine.ScatterBlock.clearMem (clearSt 100)).1.isOk
#guard (execC pB pF Refine.ScatterBlock.clearMem (clearSt 200)).1.isOk

-- the member pass's clock is a function of the member count alone
#guard (execC pB pF Refine.ScatterBlock.clearMem (clearSt 100)).2 = 34
#guard (execC pB pF Refine.ScatterBlock.clearMem (clearSt 200)).2 = 34

-- and it does the job: both members' cells cleared, every carrier
-- cell above them untouched
#guard (execC pB pF Refine.ScatterBlock.clearMem (clearSt 200)).1.cell "exc" 0 = 0
#guard (execC pB pF Refine.ScatterBlock.clearMem (clearSt 200)).1.cell "exc" 1 = 0
#guard (List.range 198).all fun k =>
  (execC pB pF Refine.ScatterBlock.clearMem (clearSt 200)).1.cell "exc" (2 + k) == 1

end Lax3Proofs.Refine.OrderBlockProbe
