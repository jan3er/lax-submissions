import Lax3Proofs.Refine.G2CostProbe
import Lax3Proofs.Refine.OrderSigProbeM
import Lax3Proofs.Refine.DriverRootD
import Lax13Proofs.Refine.Sepref.SpaceBudgetProbe

/-!
# `g2_exists`, re-validated against the two substrates that moved

`Refine/G2CostProbe.lean`'s existence probe was compiled against the
**pre-P4.5** tower cost model and against phase budgets read at an
abstract arena weight. Two things have moved under it since:

1. **the space substrate (P4.5, ledger E25–E29/E41).** Allocation is
   O(1) (bump pointer), deallocation is LIFO, and the binding law is
   the E41 **iff**: a descending driver's peak is `setup + levels·aw`,
   and it fits a word length linear in `|x|` *exactly when* `levels·aw`
   is linear in `|x|` (`SpaceBudget.nested_fits_iff`,
   `SpaceBudget.no_word_size_for_nested`). Per-turn fresh allocation is
   budget-fatal and touched-only reset is the loop-interior discipline;
   neither is re-derived here — both are consumed.

2. **the time shape of a phase (P4.6, wave M).**
   `Refine/OrderSigProbeM.lean` **measured** a member-driven order phase
   on the tower's own executable semantics: `phaseClockK m = 68·m + 12`,
   with the carrier `n` ABSENT and the empty-member charge the constant
   `12`. The re-derived order/cover/dead phases will therefore carry
   costs of the shape `a·m + b` at member count `m` — not the landed
   size-blind `orderPhaseCost n ns W`.

The campaign's standing rule is *compiled costs both directions*: before
a re-derivation wave family launches, the closed-form `Kl` must be shown
to **satisfy** the proposed side conditions at the target shape, not
merely to escape the old floors. This file is that gate.

## What is compiled here

* **§1** the M-class phase form `phaseM a b m = a·m + b`, tied by `rfl`
  to the measured `OrderSigProbeM.phaseClockK`, with the empty-arena
  charge compiled constant and the arena-weight domination that carries
  it into the Σ interface.
* **§2** `g2m_exists` — the re-validated witness: for every level count,
  mass coefficient, round count and M-class constant family there are
  cost functions satisfying the **M-class** phase slots, the landed
  Σ-interface shapes of `RamDriverRoot.driverRoot_decides_sentence`
  verbatim (`hKmono`, `hKs`, the Σ-shaped `hKl`), and closing to
  `(ℓ·A + Cb)·(D+1)^ℓ·(w+1)`. The witness is `CostRecurrence`'s
  canonical solution; nothing is bespoke.
* **§3** the C0 close: the closed form inside `n^{1+ε}` at the C0 target
  shape, `#guard`ed at ε = 1 and ε = 1/2 on the star instance family,
  with **one gate at the measured 68/12**.
* **§4** the space side: the driver-shaped skeleton at M-class per-level
  arenas satisfies the E41 law — `mclass_driver_fits` is
  `nested_fits_iff`'s `←` consumed at a weight-linear setup and arena,
  and `mclass_space_needs_bounded_depth` is `no_word_size_for_nested`
  consumed at growing depth. Neither peak is re-derived.
* **§5** the negative control that bites: the SAME arithmetic with the
  order slot left at the landed size-blind `orderPhaseCost n ns W`
  reproduces `C0Probe.level_interface_floor`'s mechanism through the new
  Σ shape (`mixed_order_slot_floor`) and is then **unsatisfiable**
  together with the M-class closed form at the C0 numerals
  (`mclass_order_slot_load_bearing`). So the M-class charging is
  load-bearing, not decorative.
* **§6** the root term: `decodeDLCost = decodeCost + dedupCost + 4` (the
  decode, the dedup `31n + 50ns + 29`, and `lwCom`'s `4`) is
  weight-linear at coefficient `87`, and the restated root's cost text
  `Kdec + (Kl 0 (n + dedupNs x) + Ksent)` closes inside the same budget
  — read at the input weight `n + ns`, since `dedupNs x ≤ ns`.

## What this file does NOT claim

Nothing here edits, re-states or attributes any landed declaration. No
member list is threaded into any driver state; the M-class constants are
free parameters everywhere except at the gates, where they are the
measured `68`/`12`. That the *landed* walks do not meet the M-class
slots is the compiled gap ledger of `G2CostProbe` §7 and is unchanged by
this file — this file's question is the other one: **is the arithmetic
the re-derivation road proposes satisfiable at all, at the shapes P4.5
and P4.6 left behind?** The answer it compiles is yes.
-/

namespace Lax3Proofs.Refine.G2ExistsRevalidation

open Finset
open Lax3Proofs.Refine.G2CostProbe (turnCostSizeA orderCostA bsq chainWidthE g2_c0_shape)

/-! ### §1 The M-class phase form

P4.6 measured the shape, not a bound: the synthesized member-driven
phase's clock is `68·m + 12` at member count `m`, at two carrier widths,
with the carrier absent. `phaseM` is that shape with the constants free;
`phaseMR` charges `R + 1` of them (the base phase plus its `R`
augment/relink rounds, each a member-driven sweep family). -/

/-- **The M-class phase cost**: linear in the arena's MEMBER count, with
a constant empty-arena charge. The carrier size does not occur. -/
def phaseM (a b m : ℕ) : ℕ := a * m + b

/-- The same, over `R + 1` rounds. -/
def phaseMR (a b R m : ℕ) : ℕ := (1 + R) * phaseM a b m

/-- The weight-read budget an M-class phase fits into: at the arena
weight `w` (alive vertices plus their degree sum), the member count is
at most `w`, so `a·m + b` sits inside `(a + b)·(w + 1)`. -/
def phaseBudgetM (a b R w : ℕ) : ℕ := (1 + R) * (a + b) * (w + 1)

/-- **The measured law IS the M-class shape** — the tie to
`OrderSigProbeM.phaseClockK`, which was pinned on the tower's executable
semantics at `m ∈ {0, 2, 3}` and two carrier widths. -/
theorem phaseClockK_eq_phaseM (m : ℕ) :
    Lax3Proofs.Refine.OrderSigProbeM.phaseClockK m = phaseM 68 12 m := rfl

/-- **The empty-arena charge is a constant** — the P4.6 fact, in the
form the level recursion consumes: a nested level that runs no member
pays `(1 + R)·b`, with no `n` and no `W`. This is the exact place
`C0Probe.level_interface_floor` extracted its `Ω(n + W)`. -/
theorem phaseMR_empty (a b R : ℕ) : phaseMR a b R 0 = (1 + R) * b := by
  simp [phaseMR, phaseM]

/-- **M-class costs are arena-weight-linear**: at any member count the
arena weight dominates, so an M-class phase fits the Σ interface's
weight-read budget at coefficient `(1 + R)·(a + b)`. -/
theorem phaseMR_le_budget {m w : ℕ} (h : m ≤ w) (a b R : ℕ) :
    phaseMR a b R m ≤ phaseBudgetM a b R w := by
  simp only [phaseMR, phaseM, phaseBudgetM]
  have : a * m + b ≤ (a + b) * (w + 1) := by nlinarith
  nlinarith

/-- The budget is exactly its coefficient times the weight — the shape
`CostRecurrence.exists_driverCostsSigma`'s `hKo`/`hKc` slots want. -/
theorem phaseBudgetM_eq (a b R w : ℕ) :
    phaseBudgetM a b R w = ((1 + R) * (a + b)) * (w + 1) := rfl

/-! ### §2 The re-validated existence witness

The per-level constant of the recurrence, with the three phase slots at
M-class coefficients instead of the landed size-blind forms. The turn
slot keeps `G2CostProbe.turnCostSizeA` verbatim — the size-READING turn
cost — since nothing in P4.5/P4.6 moved it. -/

/-- The per-level constant of the M-class recurrence: the order phase
over its `R + 1` rounds, the cover and dead-sweep phases, and the turn's
own leaves at the mass coefficient. -/
def g2M (ao bo ac bc ad bd R ct ksc D : ℕ) : ℕ :=
  (1 + R) * (ao + bo) + (((ac + bc) + (ad + bd)) + ((ct + ksc + 3) * (D + 1) + 14))

/-- **The existence probe, re-validated at M-class phase costs.**

For every level count, mass coefficient, base coefficient, round count
and M-class constant family there are cost functions satisfying,
verbatim:

* the three **M-class** phase slots — each stated at an arbitrary member
  count `m ≤ w`, so the budget must pay the phase at every arena the
  weight admits, and is `O(1)` in the carrier on the empty arena;
* the landed Σ-interface shapes of
  `RamDriverRoot.driverRoot_decides_sentence` byte for byte — the base
  clause, `hKmono`, `hKs` at the size-reading `turnCostSizeA`, and the
  Σ-shaped `hKl` at `Kmass := D`;

with the root budget geometric in `D + 1` and linear in the arena
weight. The witness is `CostRecurrence`'s canonical solution.

This is the positive half of the standing rule: the proposed side
conditions are not merely floor-free, they are **satisfied**, and the
satisfying family is exhibited. -/
theorem g2m_exists (ℓ D Cb R ao bo ac bc ad bd ct ksc : ℕ) (Ksc : ℕ → ℕ)
    (hKsc : ∀ j < ℓ, Ksc j ≤ ksc) :
    ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
      -- the M-class phase slots (member-read, carrier-blind)
      (∀ j w m, m ≤ w → phaseMR ao bo R m ≤ Ko j w) ∧
      (∀ j w m, m ≤ w → phaseMR ac bc 0 m ≤ Kc j w) ∧
      (∀ j w m, m ≤ w → phaseMR ad bd 0 m ≤ Kd j w) ∧
      (∀ w, Cb * (w + 1) ≤ Kl ℓ w) ∧
      -- landed Σ-interface shapes, verbatim
      (∀ j, Monotone (Kl j)) ∧
      (∀ j < ℓ, ∀ s : ℕ, turnCostSizeA ct (Ksc j) s (Kl (j + 1) s) ≤ Ks j s) ∧
      (∀ j < ℓ, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
        (∑ c ∈ Finset.range t, bs c) ≤ D * (w + 1) →
        Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
          ≤ Kl j w) ∧
      -- the closed form: geometric in `D + 1`, linear in the weight
      (∀ w, Kl 0 w ≤ (ℓ * g2M ao bo ac bc ad bd R ct ksc D + Cb) * (D + 1) ^ ℓ * (w + 1)) := by
  classical
  obtain ⟨Kl, Kt, hbase, hmono, hKt, hKlS, hKl0, -⟩ :=
    CostRecurrence.exists_driverCostsSigma ℓ D Cb
      (fun _ => (1 + R) * (ao + bo)) (fun _ => (ac + bc) + (ad + bd))
      (fun j => ct + Ksc j + 3)
      (fun _ w => phaseBudgetM ao bo R w)
      (fun _ w => phaseBudgetM ac bc 0 w + phaseBudgetM ad bd 0 w)
      (fun j s => (ct + Ksc j) * (s + 1) + 3)
      (fun j s Kin => turnCostSizeA ct (Ksc j) s Kin + 3)
      (fun _ _ => le_rfl)
      (fun _ m => by simp only [phaseBudgetM]; ring_nf; omega)
      (fun j s => by nlinarith)
      (fun j s Kin => by simp only [turnCostSizeA]; omega)
  refine ⟨fun _ w => phaseBudgetM ao bo R w, fun _ w => phaseBudgetM ac bc 0 w,
    fun _ w => phaseBudgetM ad bd 0 w,
    fun j s => turnCostSizeA ct (Ksc j) s (Kl (j + 1) s), Kl,
    fun _ _ _ h => phaseMR_le_budget h _ _ _, fun _ _ _ h => phaseMR_le_budget h _ _ _,
    fun _ _ _ h => phaseMR_le_budget h _ _ _, hbase, hmono,
    fun _ _ _ => le_rfl, ?_, ?_⟩
  · -- the landed `hKl` shape, from the solver's, via the `+3` turn shift
    exact RamDriverRoot.levelCost_of_sigma
      (fun j s => hKt j s) (fun j hj m t htm bs hbs => hKlS j hj m t htm bs hbs)
  · -- the closed form, bounded geometrically
    intro w
    rw [hKl0 w]
    refine Nat.mul_le_mul_right _ ?_
    have hs : (∑ j ∈ Finset.range ℓ,
          CostRecurrence.driverASigma (fun _ => (1 + R) * (ao + bo))
            (fun _ => (ac + bc) + (ad + bd)) (fun j => ct + Ksc j + 3) D j * (D + 1) ^ j) +
          Cb * (D + 1) ^ ℓ =
        CostRecurrence.solve
          (CostRecurrence.driverASigma (fun _ => (1 + R) * (ao + bo))
            (fun _ => (ac + bc) + (ad + bd)) (fun j => ct + Ksc j + 3) D)
          (fun _ => D + 1) Cb ℓ 0 :=
      (CostRecurrence.solve_const _ _ _ _).symm
    rw [hs]
    refine CostRecurrence.solve_sigma_le fun j hj => ?_
    have h1 : (ct + Ksc j + 3) * (D + 1) ≤ (ct + ksc + 3) * (D + 1) :=
      Nat.mul_le_mul_right _ (by have := hKsc j hj; omega)
    simp only [CostRecurrence.driverASigma, g2M]
    omega

/-! ### §3 The C0 close, and the numerics at the measured constants

The witness's root budget is `C · (D + 1)^ℓ · (w + 1)` and
`G2CostProbe.g2_c0_shape` carries it to `n^{1+ε}` at the cover-degree
parameter `D = ⌈c·w^{ε/ℓ}⌉₊`. The instance family is `C0Probe`'s own —
sparse members, `|x| = 3·n + 3`, all constants chosen before `n`:
`R = 0`, `D = 8`, `ℓ = 3`, `ct = 200` (`G2CostProbe.blockLeaves_le_weight`),
`ksc = Cb = ksent = 10⁴` (the scatter leaf is NOT yet M-class — E4b's
`ScatterBlock` is landed but unwired, `G2CostProbe.hbnd_gap` — so its
coefficient is left at the landed probe's numeral), `kdec = 87` (§6). -/

/-- The witness's root budget at level count `ℓ`, base `Cb` and the
M-class constant family: the closed form of `g2m_exists`, plus the
root's own weight-linear reads (§6). -/
def rootBudgetM (ℓ Cb ao bo ac bc ad bd R ct ksc D kdec ksent : ℕ) : ℕ :=
  (kdec + ksent + (ℓ * g2M ao bo ac bc ad bd R ct ksc D + Cb)) * (D + 1) ^ ℓ

/-- **The C0 shape, end to end, at M-class phase costs**: the witness's
root budget, read at the cover-degree parameter `⌈c·w^{ε/ℓ}⌉₊`, is
inside `n^{1+ε}`. `G2CostProbe.g2_c0_shape` is consumed, not
re-derived. -/
theorem mclass_c0_shape {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {C w K : ℕ} (hw : 1 ≤ w)
    (hK : K ≤ C * (⌈c * (w : ℝ) ^ (ε / (ℓ : ℝ))⌉₊ + 1) ^ ℓ * (w + 1)) :
    (K : ℝ) ≤ ((C : ℝ) * (c + 2) ^ ℓ) * ((w : ℝ) + 1) ^ (1 + ε) :=
  g2_c0_shape hc hε hℓ hw hK

-- **The gate at the measured constants**: all three phase slots at the
-- P4.6 law `68·m + 12`, `R = 0`, `D = 8`, `ℓ = 3`, `ct = 200`,
-- `ksc = 10⁴`. The per-level constant, cell by cell.
#guard g2M 68 12 68 12 68 12 0 200 (10 ^ 4) 8 =
  (1 + 0) * (68 + 12) + (((68 + 12) + (68 + 12)) + ((200 + 10 ^ 4 + 3) * 9 + 14))
#guard g2M 68 12 68 12 68 12 0 200 (10 ^ 4) 8 = 92081

-- and the root budget it induces (`kdec = 87`, `ksent = Cb = 10⁴`)
#guard rootBudgetM 3 (10 ^ 4) 68 12 68 12 68 12 0 200 (10 ^ 4) 8 87 (10 ^ 4) =
  296330 * 729

-- **ε = 1** (the guard `C0Probe`'s cubic floor LOST at `c = 10⁹`,
-- `n = 10⁹`, on the star carrier `ns = 2·(n − 1)`): the M-class witness
-- budget clears it with ten orders to spare
#guard rootBudgetM 3 (10 ^ 4) 68 12 68 12 68 12 0 200 (10 ^ 4) 8 87 (10 ^ 4) *
    (10 ^ 9 + 2 * (10 ^ 9 - 1) + 1)
  ≤ 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2

-- **ε = 1/2** (`C0Probe`'s second guard, squared form): at `n = 10⁸`
-- the witness budget clears `c·(3n+4)^{3/2}` at `c = 10⁷`
#guard (rootBudgetM 3 (10 ^ 4) 68 12 68 12 68 12 0 200 (10 ^ 4) 8 87 (10 ^ 4) *
    (10 ^ 8 + 2 * (10 ^ 8 - 1) + 1)) ^ 2
  ≤ (10 ^ 7) ^ 2 * (3 * 10 ^ 8 + 4) ^ 3

-- **The rounds are affordable too**: at `R = 4` augment/relink rounds
-- the same ε = 1 gate still clears — the M-class order phase's round
-- factor is `(1 + R)` on a constant, not on the carrier
#guard rootBudgetM 3 (10 ^ 4) 68 12 68 12 68 12 4 200 (10 ^ 4) 8 87 (10 ^ 4) *
    (10 ^ 9 + 2 * (10 ^ 9 - 1) + 1)
  ≤ 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2

/-! ### §4 The space side (P4.5 / E41)

The re-derived driver is the **descending** skeleton: within a turn it
descends `levels` deep holding one arena live per level and then unwinds
LIFO. `SpaceBudget.peak_nestedSkel` and `SpaceBudget.nested_peak_attained`
pin its peak at `setup + levels·aw` exactly, and `nested_fits_iff` turns
that into the word-length law. Both directions are consumed here; no
peak is re-derived.

The M-class time law does NOT by itself discharge the space law — that
is `mclass_space_needs_bounded_depth` below, and it is why the
re-derivation road has to keep `levels·aw` linear as a separate
obligation. -/

/-- **The peak arithmetic**: a setup and a per-level arena that are both
weight-linear give a peak weight-linear at coefficient
`kset + levels·kaw` — the hypothesis side of E41's iff, at the shape the
re-derived driver has (`levels` fixed by the sentence and ε, `aw` the
level's own arena). -/
theorem mclass_peak_linear {setup aw kset kaw : ℕ} (levels w : ℕ)
    (hset : setup ≤ kset * (w + 1)) (haw : aw ≤ kaw * (w + 1)) :
    setup + levels * aw + 9 ≤ (kset + levels * kaw + 9) * (w + 1) := by
  have h1 : levels * aw ≤ levels * (kaw * (w + 1)) := Nat.mul_le_mul_left _ haw
  nlinarith

open Lax13Proofs.Compile Lax13Proofs.Refine.Ir Lax13Proofs.Refine.Sepref.SpaceBudget in
/-- **The M-class driver fits the E41 law.** At a weight-linear setup and
a weight-linear per-level arena, the descending skeleton's whole run
stays inside a layout at word length `w`, for every turn count — `turns`
does not occur in the hypothesis, which is the LIFO unwind's content.
This is `nested_fits_iff`'s `←` direction, consumed. -/
theorem mclass_driver_fits {setup aw kset kaw levels turns w : ℕ} (hturns : 0 < turns)
    (hset : setup ≤ kset * (w + 1)) (haw : aw ≤ kaw * (w + 1))
    (hword : (kset + levels * kaw + 9) * (w + 1) ≤ 2 ^ w) (hten : 10 ≤ 2 ^ w) :
    ∃ (B : ℕ) (L : Layout), L.scalars = probeScalars ∧ L.arrays = [heapName] ∧
        L.temps = 0 ∧ L.FitsWords B w ∧
        ∀ s' : State, Mid (nestedSkel setup aw turns levels) entryState s' → hpOf s' < B :=
  (nested_fits_iff setup aw turns levels w hturns).2
    (max_le (le_trans (mclass_peak_linear levels w hset haw) hword) hten)

open Lax13Proofs.Compile Lax13Proofs.Refine.Ir Lax13Proofs.Refine.Sepref.SpaceBudget in
/-- **…and the law bites in the other direction.** A per-level arena
that is weight-linear does not save a driver whose DEPTH grows with the
input: past `8·c ≤ levels·kaw` no word length admissible for C0's own
domain holds the peak. So "the phase is M-class in time" is not a space
argument — `levels·aw` linear stays a separate obligation of the
re-derivation road. `no_word_size_for_nested` is consumed. -/
theorem mclass_space_needs_bounded_depth {c n kaw levels turns setup : ℕ} (hc : 0 < c)
    (hturns : 0 < turns) (hcross : 8 * c ≤ levels * kaw) :
    ∃ w : ℕ,
      (∀ v ∈ probeWord n, c * ((probeWord n).length + v + 1) ≤ 2 ^ w) ∧
      ∀ (L : Layout) (B : ℕ) (s : State), Good s → hpOf s = 0 → s.vars "t" = some 0 →
        L.FitsWords B w →
        ¬ (∀ s' : State,
            Mid (nestedSkel setup (kaw * (n + 1)) turns levels) s s' → hpOf s' < B) := by
  refine no_word_size_for_nested c n setup (kaw * (n + 1)) turns levels hc hturns ?_
  have h1 : 8 * c * (n + 1) ≤ levels * kaw * (n + 1) := Nat.mul_le_mul_right _ hcross
  nlinarith

-- **The bounded-depth side is inhabited at the C0 shape**: the sentence
-- and ε fix `levels = 3`, and with a setup and a per-level arena both
-- linear in the weight the peak is inside what C0's domain already
-- grants at `c = 10⁹`, `n = 10²⁰` — no word length beyond the domain's.
#guard (10 ^ 20 + 1) + 3 * (225 * (10 ^ 20 + 1)) + 9 ≤ 10 ^ 9 * (2 * 10 ^ 20 + 4)

-- **…and the refuting side is inhabited too**: depth `10¹⁵` at a
-- per-level coefficient `1` already crosses `8·c` at `c = 10⁹`.
#guard 8 * 10 ^ 9 ≤ 10 ^ 15 * 1

/-! ### §5 The negative control: the size-blind order slot still floors

`C0Probe.level_interface_floor` is a statement about the LANDED side
conditions. Its mechanism is re-read here through the **new** arithmetic
— the M-class Σ interface of §2, with `turnCostSizeA` in the turn slot
and every other slot free — and with exactly one slot left at the landed
size-blind `RamDriverCompose.orderPhaseCost n ns W`. The floor comes
straight back: a nested level pays the whole carrier-charged order phase
on the EMPTY arena, and the root level runs `n` turns of it.

Then the bite: at the C0 numerals that same interface is
**unsatisfiable** together with §2's closed form. So the M-class
charging is what buys the budget, not the Σ re-thread. -/

/-- **The floor, re-derived through the M-class Σ shape.** Nothing about
the other phase slots is assumed: only the turn slot (at
`G2CostProbe.turnCostSizeA`, the size-reading form §2 uses), the Σ-shaped
level condition, and the ONE size-blind order slot. -/
theorem mixed_order_slot_floor {n ns W ℓ D ct : ℕ} {Ksc : ℕ → ℕ}
    {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}
    (hℓ : 2 ≤ ℓ)
    (hKs : ∀ j < ℓ, ∀ s : ℕ, turnCostSizeA ct (Ksc j) s (Kl (j + 1) s) ≤ Ks j s)
    (hKo : ∀ j w, RamDriverCompose.orderPhaseCost n ns W ≤ Ko j w)
    (hKl : ∀ j < ℓ, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ D * (w + 1) →
      Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j w) :
    n * (60 * W + 1600 * n) ≤ Kl 0 (n + ns) := by
  -- the nested level pays the size-blind order phase on the EMPTY arena
  have h10 : RamDriverCompose.orderPhaseCost n ns W ≤ Kl 1 0 := by
    have h := hKl 1 (by omega) 0 0 le_rfl (fun _ => 0) (by simp)
    simp only [Finset.range_zero, Finset.sum_empty] at h
    exact le_trans (hKo 1 0) (le_trans (Nat.le_add_right _ _) h)
  -- a turn pays its nested level (`turnCostSizeA` has `Kin` additively)
  have hks : Kl 1 0 ≤ Ks 0 0 := by
    have h := hKs 0 (by omega) 0
    simp only [Nat.zero_add, turnCostSizeA] at h
    omega
  -- the root level runs `n` turns inside an arena of weight `n + ns`
  have h0 := hKl 0 (by omega) (n + ns) n (by omega) (fun _ => 0) (by simp)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h0
  have hP : n * (Ks 0 0 + 11) ≤ Kl 0 (n + ns) := by omega
  have hop : 60 * W + 1600 * n ≤ RamDriverCompose.orderPhaseCost n ns W := by
    simp only [RamDriverCompose.orderPhaseCost]
    omega
  calc n * (60 * W + 1600 * n)
      ≤ n * (Ks 0 0 + 11) :=
        Nat.mul_le_mul_left _ (by omega)
    _ ≤ Kl 0 (n + ns) := hP

/-- **The differential, positive side.** The three clauses the negative
control below negates — the turn shape, the Σ-shaped level condition and
§2's closed form — are all satisfiable at the C0 star numerals when the
order slot is M-class. This is `g2m_exists` read at
`ℓ = 3, D = 8, Cb = 10⁴, R = 0, ct = 200, ksc = 10⁴` and the measured
`68`/`12`; it exists so the refutation that follows is a difference in
ONE slot and not a difference in the statement. -/
theorem mclass_order_slot_satisfiable (Ksc : ℕ → ℕ) (hKsc : ∀ j < 3, Ksc j ≤ 10 ^ 4) :
    ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
        (∀ j w m, m ≤ w → phaseMR 68 12 0 m ≤ Ko j w) ∧
        (∀ j < 3, ∀ s : ℕ, turnCostSizeA 200 (Ksc j) s (Kl (j + 1) s) ≤ Ks j s) ∧
        (∀ j < 3, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
          (∑ c ∈ Finset.range t, bs c) ≤ 8 * (w + 1) →
          Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
            ≤ Kl j w) ∧
        (∀ w, Kl 0 w ≤
          (3 * g2M 68 12 68 12 68 12 0 200 (10 ^ 4) 8 + 10 ^ 4) * (8 + 1) ^ 3 * (w + 1)) := by
  obtain ⟨Ko, Kc, Kd, Ks, Kl, hKo, -, -, -, -, hKs, hKl, hcl⟩ :=
    g2m_exists 3 8 (10 ^ 4) 0 68 12 68 12 68 12 200 (10 ^ 4) Ksc hKsc
  exact ⟨Ko, Kc, Kd, Ks, Kl, hKo, hKs, hKl, hcl⟩

/-- **The control bites: the M-class order slot is load-bearing.** At the
C0 star numerals (`ℓ = 3`, `D = 8`, `Cb = 10⁴`, `ct = 200`, `ksc = 10⁴`,
`n = 10⁹`, `ns = 2·(n − 1)`, phases at the measured `68`/`12`), no cost
family satisfies the M-class arithmetic's turn and level shapes with the
order slot left size-blind AND stays inside §2's closed form. The
witness of `mclass_order_slot_satisfiable` satisfies the other three
clauses at the same numerals with the order slot M-class — so the
difference between the two is exactly the member-driven charging.

`W` is universally quantified: the surviving obstruction is the
`1600·n²` carrier term, alive even at `W = 0`. (The width half of the
old floor — `chainWidth`'s `n·n`, which made it cubic — already died at
`G2CostProbe.width_step_dead`.) -/
theorem mclass_order_slot_load_bearing (W : ℕ) (Ksc : ℕ → ℕ) :
    ¬ ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
        (∀ j w, RamDriverCompose.orderPhaseCost (10 ^ 9) (2 * (10 ^ 9 - 1)) W ≤ Ko j w) ∧
        (∀ j < 3, ∀ s : ℕ, turnCostSizeA 200 (Ksc j) s (Kl (j + 1) s) ≤ Ks j s) ∧
        (∀ j < 3, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
          (∑ c ∈ Finset.range t, bs c) ≤ 8 * (w + 1) →
          Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
            ≤ Kl j w) ∧
        (∀ w, Kl 0 w ≤
          (3 * g2M 68 12 68 12 68 12 0 200 (10 ^ 4) 8 + 10 ^ 4) * (8 + 1) ^ 3 * (w + 1)) := by
  rintro ⟨Ko, Kc, Kd, Ks, Kl, hKo, hKs, hKl, hcl⟩
  have hfloor := mixed_order_slot_floor (n := 10 ^ 9) (ns := 2 * (10 ^ 9 - 1)) (W := W)
    (ℓ := 3) (D := 8) (ct := 200) (Ksc := Ksc) (by omega) hKs hKo hKl
  have hup := hcl (10 ^ 9 + 2 * (10 ^ 9 - 1))
  have hlow : 1600 * (10 ^ 9) * (10 ^ 9) ≤ 10 ^ 9 * (60 * W + 1600 * 10 ^ 9) := by nlinarith
  have hbad : 1600 * (10 ^ 9) * (10 ^ 9) ≤
      (3 * g2M 68 12 68 12 68 12 0 200 (10 ^ 4) 8 + 10 ^ 4) * (8 + 1) ^ 3 *
        (10 ^ 9 + 2 * (10 ^ 9 - 1) + 1) :=
    le_trans hlow (le_trans hfloor hup)
  exact absurd hbad (by simp only [g2M]; decide +kernel)

-- the surviving floor, against C0's own ε = 1/2 budget (`C0Probe`'s
-- second guard, at `c = 10⁶`, `n = 10⁸`): the `1600·n²` half loses even
-- there, so the control is not an artefact of §2's constants
#guard (10 ^ 6) ^ 2 * (3 * 10 ^ 8 + 4) ^ 3 < (1600 * (10 ^ 8) ^ 2) ^ 2

-- and, side by side at the ε = 1 numerals of §3: the M-class witness
-- budget is ten orders BELOW the floor the size-blind slot forces
#guard rootBudgetM 3 (10 ^ 4) 68 12 68 12 68 12 0 200 (10 ^ 4) 8 87 (10 ^ 4) *
    (10 ^ 9 + 2 * (10 ^ 9 - 1) + 1)
  < 1600 * (10 ^ 9) * (10 ^ 9)

/-! ### §6 The root term: decode, dedup, and `lwCom`'s `4`

The restated root (`Refine/DriverRootD.lean`, landed 2026-08-06) reads
its cost as `Kdec + (Kl 0 (n + dedupNs x) + Ksent)`, with `hKdec`
covering `decodeCost n ns + dedupCost n ns + 4` — the decode, the
dedup, and the live-width scalar's `lwCom`. That whole `W`-term is
weight-linear at coefficient `87`, so it disappears into the geometric
factor. -/

/-- `RamDriverDedup.dedupCost n ns = 31·n + 50·ns + 29`, cited. -/
theorem dedupCost_eq (n ns : ℕ) :
    Lax3Proofs.RamDriverDedup.dedupCost n ns = 31 * n + 50 * ns + 29 := rfl

/-- `RamDriverIO.decodeCost n ns = 45·n + 12·ns + 54`, cited. The root's
identity member list (rebase E-mem) is the `11·n + 8` of it. -/
theorem decodeCost_eq (n ns : ℕ) :
    RamDriverIO.decodeCost n ns = 45 * n + 12 * ns + 54 := by
  simp only [RamDriverIO.decodeCost]; ring

/-- **The root `W`-term is weight-linear at `87`**: the composed
decode + dedup + `lwCom` charge that `hKdec` must cover
(`Refine.DriverRootD.decodeDLCost`) fits `87·(n + ns + 1)` — this is what
makes the `87` of `rootD_close` below a real coefficient and not a
choice. Rebase E-mem: the root member list moved the coefficient from
`79` to `87`, weight-linearly — the root arena IS the carrier. -/
theorem decodeDLCost_le_weight (n ns : ℕ) :
    Lax3Proofs.Refine.DriverRootD.decodeDLCost n ns ≤ 87 * (n + ns + 1) := by
  simp only [Lax3Proofs.Refine.DriverRootD.decodeDLCost, RamDriverIO.decodeCost,
    Lax3Proofs.RamDriverDedup.dedupCost]
  omega

-- `87` is not slack: the term is `76·n + 62·ns + 87`, so `75` loses on the
-- carrier and `86` loses at the empty word — the constant is what forces `87`
#guard ¬ (Lax3Proofs.Refine.DriverRootD.decodeDLCost (10 ^ 6) 0 ≤ 75 * (10 ^ 6 + 0 + 1))
#guard ¬ (Lax3Proofs.Refine.DriverRootD.decodeDLCost 0 0 ≤ 86 * (0 + 0 + 1))

/-- **The root closes inside the budget.** The restated root's cost text
`Kdec + (Kl 0 (n + nsd) + Ksent)` — with the level budget read at the
COMPACTED count `nsd = dedupNs x ≤ ns` and the decode charge at the
input's own `ns` — sits inside `(87 + ksent + C)·(D+1)^ℓ·(n + ns + 1)`.
The compaction is consumed through `hKmono`, which the `g2m_exists`
witness supplies; `decodeDLCost_le_weight` is what an admissible `Kdec`
(one satisfying the root's own `hKdec` slot tightly) reads. -/
theorem rootD_close {Kdec Ksent : ℕ → ℕ → ℕ} {n ns nsd C D ℓ ksent : ℕ}
    {Kl : ℕ → ℕ → ℕ}
    (hns : nsd ≤ ns) (hmono : Monotone (Kl 0))
    (hdecle : Kdec n ns ≤ 87 * (n + ns + 1))
    (hsent : Ksent n ns ≤ ksent * (n + ns + 1))
    (hcl : ∀ w, Kl 0 w ≤ C * (D + 1) ^ ℓ * (w + 1)) :
    Kdec n ns + (Kl 0 (n + nsd) + Ksent n ns) ≤
      (87 + ksent + C) * (D + 1) ^ ℓ * (n + ns + 1) := by
  have hpow : 1 ≤ (D + 1) ^ ℓ := Nat.one_le_pow _ _ (by omega)
  have hKlw : Kl 0 (n + nsd) ≤ C * (D + 1) ^ ℓ * (n + ns + 1) :=
    le_trans (hmono (by omega : n + nsd ≤ n + ns)) (hcl (n + ns))
  have h1 : 87 * (n + ns + 1) ≤ 87 * (D + 1) ^ ℓ * (n + ns + 1) := by nlinarith
  have h2 : ksent * (n + ns + 1) ≤ ksent * (D + 1) ^ ℓ * (n + ns + 1) := by nlinarith
  calc Kdec n ns + (Kl 0 (n + nsd) + Ksent n ns)
      ≤ 87 * (D + 1) ^ ℓ * (n + ns + 1) +
          (C * (D + 1) ^ ℓ * (n + ns + 1) + ksent * (D + 1) ^ ℓ * (n + ns + 1)) := by
        have := le_trans hdecle h1
        have := le_trans hsent h2
        omega
    _ = (87 + ksent + C) * (D + 1) ^ ℓ * (n + ns + 1) := by ring

/-- **The two halves, composed**: the `g2m_exists` witness threaded
through the restated root's cost text gives exactly `rootBudgetM`'s
closed form at the input weight — the shape §3's `#guard`s clear and
`mclass_c0_shape` carries to `n^{1+ε}`. -/
theorem rootBudgetM_closes {Kdec Ksent : ℕ → ℕ → ℕ} {Kl : ℕ → ℕ → ℕ}
    {n ns nsd ℓ Cb ao bo ac bc ad bd R ct ksc D ksent : ℕ}
    (hns : nsd ≤ ns) (hmono : Monotone (Kl 0))
    (hdecle : Kdec n ns ≤ 87 * (n + ns + 1))
    (hsent : Ksent n ns ≤ ksent * (n + ns + 1))
    (hcl : ∀ w, Kl 0 w ≤
      (ℓ * g2M ao bo ac bc ad bd R ct ksc D + Cb) * (D + 1) ^ ℓ * (w + 1)) :
    Kdec n ns + (Kl 0 (n + nsd) + Ksent n ns) ≤
      rootBudgetM ℓ Cb ao bo ac bc ad bd R ct ksc D 87 ksent * (n + ns + 1) := by
  have h := rootD_close (Kdec := Kdec) (Ksent := Ksent) (nsd := nsd) (ksent := ksent)
    (C := ℓ * g2M ao bo ac bc ad bd R ct ksc D + Cb) hns hmono hdecle hsent hcl
  simpa only [rootBudgetM] using h

/-! ### §7 Axioms -/

#print axioms g2m_exists
#print axioms mclass_driver_fits
#print axioms mclass_space_needs_bounded_depth
#print axioms mclass_order_slot_satisfiable
#print axioms mclass_order_slot_load_bearing
#print axioms mixed_order_slot_floor
#print axioms rootBudgetM_closes
#print axioms decodeDLCost_le_weight

end Lax3Proofs.Refine.G2ExistsRevalidation
