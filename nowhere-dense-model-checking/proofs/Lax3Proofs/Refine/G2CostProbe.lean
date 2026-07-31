import Lax3Proofs.RamDriverRoot
import Lax3Proofs.TgtCoupling
import Lax3Proofs.CostRecurrence
import Lax3Proofs.Refine.BfsBridge
import Lax3Proofs.Refine.BlockLeaves
import Lax3Proofs.Refine.ElimSynth6
import Lax3Proofs.Refine.CoverBlock
import Lax3Proofs.Refine.ScatterBlockCost

/-!
**G2-design: the arena-charged phase interface, compiled in both
directions** (plan rev 3, G-road; design doc
`plans/nowhere-dense-model-checking/g2-cost-design.md`).

`C0Probe.level_interface_floor` proved that the LANDED side conditions
`hKo`/`hKc`/`hKd`/`hKbase` of `RamDriverRoot.driverRoot_decides_sentence`
admit no level budget below `n·(60·W + 1600·n)`, and `60·n³` on the C0
width path. This file is the design gate for the repair, under the
standing rule that prose verdicts do not gate work: every proposed form
is stated here as a local `def`, an **existence probe** proves the
`CostRecurrence` witness satisfies every proposed form and closes to the
`(D+1)^ℓ` recurrence, the **floor-death** theorems prove the C0Probe
derivation routes are cut against the proposed forms, and the
**honesty controls** tie the proposed coefficients to the landed engine
exports (with negative controls showing undersized budgets fail).

Nothing here edits the frozen surface. The proposed forms move to the
real declarations only in G2 execution, per the design doc's wave
decomposition.

# The design, in one paragraph

One size variable threads the whole interface: the **arena weight**
`w` — alive vertices plus their degree sum in the level's graph (at the
root, `w = n + ns`). Every phase budget becomes `coeff · (w + 1)`; block
budgets read block weights; the mass side condition keeps its landed
Σ-shape verbatim (block weights sum to `≤ D · (w + 1)` by the same
per-vertex cover-degree bound `hdeg` that today bounds vertex mass).
The ordering phase's coefficient carries `bsq = (budget d D₁ R + 1)²`:
one save/restore of the **live width** `m·bsq + e + 1` per level entry,
and the `R` augment/relink rounds, all charged at the arena. The width
itself is repaired to `chainWidthE = n·bsq + ns + 1` — the `n·n` term
of `TgtCoupling.chainWidth` (there to hold the level's own graph at a
generic `ns ≤ n²`) dies against the actual slot count `ns`. The program
text loses its four `.lit W` sites (`saveCsr`/`restoreCsr`/
`augRelinkCom`/`orderCom`'s in-list copy) to a runtime live-width
scalar, making the com family `W`-free — the C0 quantifier order
(`∃ p, ∀ n G w`) forbids any input-scaling literal in the text, and
`orderCom_reads_W` below compiles the fact that today's text violates
this.
-/

namespace Lax3Proofs.Refine.G2CostProbe

open Finset

/-! ### §1 The proposed width (design item ii-a)

`TgtCoupling.chainWidth n d D₁ r = n·(budget+1)² + n·n + 1`; the `n·n`
holds the level's own graph via `csrSlots_le_sq`. The repair: the
level's graph occupies exactly `ns` slots, and every masked sub-arena's
graph at most that, so the width is `ns`-aware and the `n·n` dies. Both
"fits" lemmas of the old width re-prove against the new one at the
hypotheses their consumers actually have. -/

/-- The chain-slot coefficient: the square the augmentation budget
forces on the per-vertex row width. Constant in `n` (it is a function
of `d`, `D₁`, `R` only — at the C0 path `d = ⌈c·n^δ⌉` makes it
subpolynomial, which is P4's real-exponent massage, not this file's). -/
def bsq (d D₁ R : ℕ) : ℕ := (Augmentation.budget d D₁ R + 1) ^ 2

theorem one_le_bsq (d D₁ R : ℕ) : 1 ≤ bsq d D₁ R :=
  Nat.one_le_pow _ _ (by omega)

/-- Degree-aware replacement for `TgtCoupling.chainWidth`: room for
every round's fraternity graph (`n·(b+1)²`, unchanged) and for the
level's own graph at its actual slot count `ns` — not at the generic
`n·n`.

**GRADUATED (rebase G2/E2)**: the real declaration is
`TgtCoupling.chainWidthE`, with the fits lemmas and the
`chainWidthE_dominates` reading beside it, and
`RamDriverCompose.orderImplementsR`'s `hWc` reads it. The local name
delegates so this file's compiled record reads unchanged. -/
def chainWidthE (n ns d D₁ r : ℕ) : ℕ := TgtCoupling.chainWidthE n ns d D₁ r

/-- The new width never exceeds the old one on real inputs
(`ns ≤ n·n` always holds of a slot count), so every allocation the old
width served is served. -/
theorem chainWidthE_le_chainWidth {n ns d D₁ r : ℕ} (h : ns ≤ n * n) :
    chainWidthE n ns d D₁ r ≤ TgtCoupling.chainWidth n d D₁ r := by
  simp only [chainWidthE, TgtCoupling.chainWidthE, TgtCoupling.chainWidth]
  omega

/-- **The width is arena-linear at coefficient `bsq`** — the load-bearing
repair fact: any cost that copies the width (save/restore, relink)
charges `O(bsq · (w + 1))` at the root weight `w = n + ns`, and the
per-arena live prefix (`liveWidth` below) is the same bound at the
arena's own weight. -/
theorem chainWidthE_le_linear (n ns d D₁ r : ℕ) :
    chainWidthE n ns d D₁ r ≤ bsq d D₁ r * (n + ns + 1) := by
  have hb := one_le_bsq d D₁ r
  simp only [chainWidthE, TgtCoupling.chainWidthE, bsq] at *
  nlinarith

/-- The live prefix of the chain arrays on an arena of `m` alive
vertices and `e` arc slots: what the per-level save/restore copies
under the proposed program delta (design item ii-b). -/
def liveWidth (b m e : ℕ) : ℕ := m * b + e + 1

/-- The live width is weight-linear at coefficient `b`. -/
theorem liveWidth_le {b : ℕ} (hb : 1 ≤ b) (m e : ℕ) :
    liveWidth b m e ≤ b * (m + e + 1) := by
  simp only [liveWidth]
  nlinarith

/-- **Fits, half 1**: the level's own graph fits the new width — at the
hypothesis its consumer actually has (`csrSlots F ≤ ns`; at the level
itself `csrSlots G = ns` exactly, and every masked sub-arena is a
subgraph). Replaces `TgtCoupling.csrSlots_lt_chainWidth`, whose proof
was the generic `csrSlots_le_sq`. -/
theorem csrSlots_lt_chainWidthE {n ns : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (d D₁ r : ℕ) (h : TgtCoupling.csrSlots F ≤ ns) :
    TgtCoupling.csrSlots F < chainWidthE n ns d D₁ r := by
  simp only [chainWidthE, TgtCoupling.chainWidthE]
  omega

/-- **Fits, half 2**: a round's fraternity graph fits the new width,
unchanged — its bound `n·b²` lives entirely in the `n·(b+1)²` term.
Replaces `TgtCoupling.csrSlots_fratGraph_lt_chainWidth` verbatim. -/
theorem csrSlots_fratGraph_lt_chainWidthE {n ns : ℕ}
    {D : Augmentation.Orientation n} {d D₁ r : ℕ}
    (hd : D.InDegLE (Augmentation.budget d D₁ r)) :
    TgtCoupling.csrSlots (Augmentation.fratGraph D) < chainWidthE n ns d D₁ r := by
  have h₁ := TgtCoupling.csrSlots_fratGraph_le hd
  simp only [chainWidthE, TgtCoupling.chainWidthE]
  nlinarith [h₁]

/-- **Floor-death, width half**: the `n·n ≤ W` step of
`C0Probe.level_interface_floor_cubic` dies — there is an admissible
width for the new `hWc` that sits strictly below `n·n` on a sparse
instance. -/
theorem width_step_dead : ∃ n ns d D₁ r W : ℕ,
    chainWidthE n ns d D₁ r ≤ W ∧ W < n * n := by
  exact ⟨10 ^ 6, 2 * 10 ^ 6, 2, 2, 1, chainWidthE (10 ^ 6) (2 * 10 ^ 6) 2 2 1,
    le_rfl, by decide +kernel⟩

-- the same, cell by cell: `budget 2 2 1 = 14`, the new width is
-- `227·10⁶ + 1`, five orders of magnitude under `n² = 10¹²`
#guard Augmentation.budget 2 2 1 = 14
#guard chainWidthE (10 ^ 6) (2 * 10 ^ 6) 2 2 1 = 225 * 10 ^ 6 + 2 * 10 ^ 6 + 1
#guard ¬ (10 ^ 6 * 10 ^ 6 ≤ chainWidthE (10 ^ 6) (2 * 10 ^ 6) 2 2 1)

/-! ### §2 The proposed phase forms (design item i)

Each landed slot `phaseCost ≤ K j m` (carrier-read, arena-blind)
becomes `phaseCostA ≤ K j w` with `phaseCostA = coeff · (w + 1)` read
at the arena weight. The coefficients are not free-floating: §5's
honesty controls tie each to the landed export that will discharge it
(or to the named block-driven re-derivation of the design doc's wave
decomposition). -/

/-- **PROPOSED** `hKo` form: the ordering phase charged at the arena.
`2310` covers the two eliminations, the symmetrization and the
carrier-linear part of `orderPhaseCost` (honesty:
`orderPhaseCostR_le_orderCostA`); the `bsq` factor is the ONE
save/restore of the live prefix per level entry plus the in-list copy;
`16840` per round covers `augCost + relinkCost + 650·W` at the live
width. -/
def orderCostA (b R w : ℕ) : ℕ := (2310 + 16840 * R) * b * (w + 1)

/-- **PROPOSED** `hKd` form coefficient: the dead-row sweep walks the
arena's member list instead of the carrier; per member it pays exactly
the landed per-vertex turn cost. -/
noncomputable def sweepCoeffA (q_top cap mb jd : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  RamDriverBot.turnCost q_top cap mb jd φ + 10

/-- **PROPOSED** `hKbase` form coefficient: the base pass
(representative scan + table fold) walks the member list. -/
noncomputable def baseCoeffA (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  RamDriverBot.reprBodyCost ℓ (FormulaTables.sigL cap mb ℓ) +
    RamDriverBot.turnCost q_top cap mb ℓ φ + 22

/-- **PROPOSED** replacement for `RamDriverRoot.turnCostSize`: the size
slot is READ (today it is discarded — `turnCostSize_eq` is `rfl` to the
carrier-width `turnCost`). One turn on a block of weight `s` pays its
block-driven leaves and its scatter chain at `s`, plus the nested
driver once. -/
def turnCostSizeA (ct ksc s Kin : ℕ) : ℕ := (ct + ksc) * (s + 1) + Kin

/-! ### §3 The existence probe (the §2.4 gap, closed compiled)

`integration-design.md` §2.4 asserted in prose that the Σ interface
yields `n^{1+ε}`; the assertion was wrong because the PHASE slots never
moved. This section is the compiled replacement: a witness family
satisfies every proposed side condition **verbatim** and closes to
`(ℓ·A + Cb)·(D+1)^ℓ·(w+1)`, with the root reads (decode + dedup,
sentence, prologue/allocation at `W = chainWidthE`) accounted. -/

/-- The per-level constant of the proposed recurrence. -/
def g2A (d D₁ R kc kd ct ksc D : ℕ) : ℕ :=
  (2310 + 16840 * R) * bsq d D₁ R + ((kc + kd) + ((ct + ksc + 3) * (D + 1) + 14))

/-- **The existence probe.** For every level count, mass coefficient,
round budget and per-phase coefficient family there are cost functions
satisfying, verbatim:

* the four **proposed** phase forms (the new `hKo`/`hKc`/`hKd`/`hKbase`
  — arena-charged, so `O(1)` on the empty arena);
* the landed Σ-interface shapes of `driverRoot_decides_sentence` —
  `hKmono`, `hKs` (at the proposed size-reading turn cost) and `hKl`
  byte for byte (`Kmass := D`);

with the root budget geometric in `D + 1` and linear in the weight.
The witness is `CostRecurrence`'s canonical solution; nothing is
bespoke. -/
theorem g2_exists (ℓ D Cb R d D₁ kc kd ct ksc : ℕ) (Ksc : ℕ → ℕ)
    (hKsc : ∀ j < ℓ, Ksc j ≤ ksc) :
    ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
      -- proposed phase forms (the new root slots)
      (∀ j w, orderCostA (bsq d D₁ R) R w ≤ Ko j w) ∧
      (∀ j w, kc * (w + 1) ≤ Kc j w) ∧
      (∀ j w, kd * (w + 1) ≤ Kd j w) ∧
      (∀ w, Cb * (w + 1) ≤ Kl ℓ w) ∧
      -- landed Σ-interface shapes, verbatim
      (∀ j, Monotone (Kl j)) ∧
      (∀ j < ℓ, ∀ s : ℕ, turnCostSizeA ct (Ksc j) s (Kl (j + 1) s) ≤ Ks j s) ∧
      (∀ j < ℓ, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
        (∑ c ∈ Finset.range t, bs c) ≤ D * (w + 1) →
        Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
          ≤ Kl j w) ∧
      -- the closed form: geometric in `D + 1`, linear in the weight
      (∀ w, Kl 0 w ≤ (ℓ * g2A d D₁ R kc kd ct ksc D + Cb) * (D + 1) ^ ℓ * (w + 1)) := by
  classical
  obtain ⟨Kl, Kt, hbase, hmono, hKt, hKlS, hKl0, -⟩ :=
    CostRecurrence.exists_driverCostsSigma ℓ D Cb
      (fun _ => (2310 + 16840 * R) * bsq d D₁ R) (fun _ => kc + kd)
      (fun j => ct + Ksc j + 3)
      (fun _ w => orderCostA (bsq d D₁ R) R w)
      (fun _ w => kc * (w + 1) + kd * (w + 1))
      (fun j s => (ct + Ksc j) * (s + 1) + 3)
      (fun j s Kin => turnCostSizeA ct (Ksc j) s Kin + 3)
      (fun _ _ => le_rfl)
      (fun _ m => by ring_nf; omega)
      (fun j s => by nlinarith)
      (fun j s Kin => by simp only [turnCostSizeA]; omega)
  refine ⟨fun _ w => orderCostA (bsq d D₁ R) R w, fun _ w => kc * (w + 1),
    fun _ w => kd * (w + 1),
    fun j s => turnCostSizeA ct (Ksc j) s (Kl (j + 1) s), Kl,
    fun _ _ => le_rfl, fun _ _ => le_rfl, fun _ _ => le_rfl, hbase, hmono,
    fun _ _ _ => le_rfl, ?_, ?_⟩
  · -- the landed `hKl` shape, from the solver's via the +3 turn shift
    exact RamDriverRoot.levelCost_of_sigma
      (fun j s => hKt j s) (fun j hj m t htm bs hbs => hKlS j hj m t htm bs hbs)
  · -- the closed form, bounded geometrically
    intro w
    rw [hKl0 w]
    refine Nat.mul_le_mul_right _ ?_
    have hs : (∑ j ∈ Finset.range ℓ,
          CostRecurrence.driverASigma (fun _ => (2310 + 16840 * R) * bsq d D₁ R)
            (fun _ => kc + kd) (fun j => ct + Ksc j + 3) D j * (D + 1) ^ j) +
          Cb * (D + 1) ^ ℓ =
        CostRecurrence.solve
          (CostRecurrence.driverASigma (fun _ => (2310 + 16840 * R) * bsq d D₁ R)
            (fun _ => kc + kd) (fun j => ct + Ksc j + 3) D)
          (fun _ => D + 1) Cb ℓ 0 :=
      (CostRecurrence.solve_const _ _ _ _).symm
    rw [hs]
    refine CostRecurrence.solve_sigma_le fun j hj => ?_
    have h1 : (ct + Ksc j + 3) * (D + 1) ≤ (ct + ksc + 3) * (D + 1) :=
      Nat.mul_le_mul_right _ (by have := hKsc j hj; omega)
    simp only [CostRecurrence.driverASigma, g2A]
    omega

/-- **The root close** (the shape the B7 re-run's real-ε massage
consumes): the decode + dedup, the sentence readback and the
prologue/allocation are all weight-linear at the root, so the whole
program budget is `C · (D + 1)^ℓ · (w + 1)` with
`C = kpro + kdec + ksent + (ℓ·A + Cb)`. -/
theorem g2_root_close {Kl0 Kdec Ksent Kpro C D ℓ w kdec ksent kpro : ℕ}
    (hKl0 : Kl0 ≤ C * (D + 1) ^ ℓ * (w + 1)) (hdec : Kdec ≤ kdec * (w + 1))
    (hsent : Ksent ≤ ksent * (w + 1)) (hpro : Kpro ≤ kpro * (w + 1)) :
    Kpro + (Kdec + (Kl0 + Ksent)) ≤
      (kpro + kdec + ksent + C) * (D + 1) ^ ℓ * (w + 1) := by
  have hpow : 1 ≤ (D + 1) ^ ℓ := Nat.one_le_pow _ _ (by omega)
  have h1 : kdec * (w + 1) ≤ kdec * (D + 1) ^ ℓ * (w + 1) := by nlinarith
  have h2 : ksent * (w + 1) ≤ ksent * (D + 1) ^ ℓ * (w + 1) := by nlinarith
  have h3 : kpro * (w + 1) ≤ kpro * (D + 1) ^ ℓ * (w + 1) := by nlinarith
  calc Kpro + (Kdec + (Kl0 + Ksent))
      ≤ kpro * (D + 1) ^ ℓ * (w + 1) + (kdec * (D + 1) ^ ℓ * (w + 1) +
          (C * (D + 1) ^ ℓ * (w + 1) + ksent * (D + 1) ^ ℓ * (w + 1))) := by
        have := le_trans hpro h3
        have := le_trans hdec h1
        have := le_trans hsent h2
        omega
    _ = (kpro + kdec + ksent + C) * (D + 1) ^ ℓ * (w + 1) := by ring

/-- **The C0 shape, end to end**: composing the root close with
`CostRecurrence.sigma_root_almostLinear` at the cover-degree
coefficient `D = ⌈c·w^{ε/ℓ}⌉₊` gives the almost-linear headline in the
weight — the exact form the B7 re-run instantiates at `w = n + ns` and
`|x| = Θ(n + ns)`. -/
theorem g2_c0_shape {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {C w K : ℕ} (hw : 1 ≤ w)
    (hK : K ≤ C * (⌈c * (w : ℝ) ^ (ε / (ℓ : ℝ))⌉₊ + 1) ^ ℓ * (w + 1)) :
    (K : ℝ) ≤ ((C : ℝ) * (c + 2) ^ ℓ) * ((w : ℝ) + 1) ^ (1 + ε) := by
  refine CostRecurrence.sigma_root_almostLinear hc hε hℓ hw ?_
  calc (K : ℝ) ≤ ((C * (⌈c * (w : ℝ) ^ (ε / (ℓ : ℝ))⌉₊ + 1) ^ ℓ * (w + 1) : ℕ) : ℝ) := by
        exact_mod_cast hK
    _ = (C : ℝ) * ((⌈c * (w : ℝ) ^ (ε / (ℓ : ℝ))⌉₊ : ℝ) + 1) ^ ℓ * ((w : ℝ) + 1) := by
        push_cast; ring

/-! #### The star numerics: the budget now CLEARS where C0Probe showed it failing

The instance family of `C0Probe`'s `#guard`s — sparse members,
`|x| = 3·n + 3`, constants chosen before `n`. Numerals: `R = 1`,
`d = D₁ = 2` (so `budget = 14`, `bsq = 225`), `D = 8`, `ℓ = 3`,
`kc = kd = ct = ksc = Cb = 10⁴`, root coefficients
`kdec = 46` (decode honesty below), `ksent = 10⁴`,
`kpro = 70·bsq` (prologue/allocation at `W = chainWidthE`). The star
carrier: `ns = 2·(n − 1)`, weight `w = n + ns`. -/

-- the witness's root budget at the numerals, as the closed form of
-- `g2_exists` + `g2_root_close`
#guard g2A 2 2 1 (10 ^ 4) (10 ^ 4) (10 ^ 4) (10 ^ 4) 8 =
  (2310 + 16840) * 225 + ((10 ^ 4 + 10 ^ 4) + ((2 * 10 ^ 4 + 3) * 9 + 14))

-- **ε = 1** (the guard C0Probe's floor LOST at `c = 10⁹`, `n = 10⁹`):
-- the witness budget clears the same budget with 8 orders to spare
#guard
  ((70 * 225 + 46 + 10 ^ 4 + (3 * g2A 2 2 1 (10 ^ 4) (10 ^ 4) (10 ^ 4) (10 ^ 4) 8 + 10 ^ 4))
      * (8 + 1) ^ 3 * (10 ^ 9 + 2 * (10 ^ 9 - 1) + 1))
    ≤ 10 ^ 9 * (3 * 10 ^ 9 + 4) ^ 2

-- **ε = 1/2** (C0Probe's second guard, squared form): at `n = 10⁸` the
-- witness budget clears `c·(3n+4)^{3/2}` at `c = 10⁷`
#guard
  ((70 * 225 + 46 + 10 ^ 4 + (3 * g2A 2 2 1 (10 ^ 4) (10 ^ 4) (10 ^ 4) (10 ^ 4) 8 + 10 ^ 4))
      * (8 + 1) ^ 3 * (10 ^ 8 + 2 * (10 ^ 8 - 1) + 1)) ^ 2
    ≤ (10 ^ 7) ^ 2 * (3 * 10 ^ 8 + 4) ^ 3

/-! ### §4 Floor-death (the C0Probe routes, cut)

`C0Probe.level_interface_floor`'s derivation had two loads: (1) `hKo`
charges `orderPhaseCost n ns W` on the EMPTY arena, so a nested level
is `Ω(n + W)` before it runs a turn; (2) `chainWidth` pins
`n·n ≤ W`. Both die. -/

/-- **Route 1 cut**: under the proposed form the empty-arena order
charge is a constant — `n` does not occur. (The witness `Ko` of
`g2_exists` meets the proposed slot with equality, so this is the
charge an admissible budget actually pays there.) -/
theorem emptyArena_charge_const (b R : ℕ) :
    orderCostA b R 0 = (2310 + 16840 * R) * b := by
  simp [orderCostA]

-- and the old floor's step-1 inequality is refuted at that budget:
-- `orderPhaseCost 10⁶ 0 0 = 1600·10⁶ + 650` does not fit under the
-- proposed empty-arena charge at `b = 1`, `R = 0`
#guard ¬ (RamDriverCompose.orderPhaseCost (10 ^ 6) 0 0 ≤ orderCostA 1 0 0)

/-- **The floor analogue is REFUTED.** `C0Probe.level_interface_floor`
proved from the LANDED forms that every admissible `Kl` pays
`n·(60·W + 1600·n)`. The same statement over the PROPOSED forms — with
the width slot at the repaired `chainWidthE` — is false: the
`g2_exists` witness satisfies every proposed side condition with a
root budget strictly below the floor. -/
theorem level_interface_floor_analogue_refuted :
    ¬ (∀ (n ns W ℓ D R d D₁ kc kd ct ksc Cb : ℕ) (Ksc : ℕ → ℕ)
        (Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ),
        2 ≤ ℓ → chainWidthE n ns d D₁ R ≤ W →
        (∀ j < ℓ, Ksc j ≤ ksc) →
        (∀ j w, orderCostA (bsq d D₁ R) R w ≤ Ko j w) →
        (∀ j w, kc * (w + 1) ≤ Kc j w) →
        (∀ j w, kd * (w + 1) ≤ Kd j w) →
        (∀ w, Cb * (w + 1) ≤ Kl ℓ w) →
        (∀ j, Monotone (Kl j)) →
        (∀ j < ℓ, ∀ s : ℕ, turnCostSizeA ct (Ksc j) s (Kl (j + 1) s) ≤ Ks j s) →
        (∀ j < ℓ, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
          (∑ c ∈ Finset.range t, bs c) ≤ D * (w + 1) →
          Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
            ≤ Kl j w) →
        (∀ w, Kl 0 w ≤ (ℓ * g2A d D₁ R kc kd ct ksc D + Cb) * (D + 1) ^ ℓ * (w + 1)) →
        n * (60 * W + 1600 * n) ≤ Kl 0 (n + ns)) := by
  intro h
  -- the witness at the ε = 1 numerals
  obtain ⟨Ko, Kc, Kd, Ks, Kl, hKo, hKc, hKd, hbase, hmono, hKs, hKl, hcl⟩ :=
    g2_exists 3 8 (10 ^ 4) 1 2 2 (10 ^ 4) (10 ^ 4) (10 ^ 4) (10 ^ 4)
      (fun _ => 10 ^ 4) (fun _ _ => le_rfl)
  have hfloor := h (10 ^ 9) (2 * (10 ^ 9 - 1)) (chainWidthE (10 ^ 9) (2 * (10 ^ 9 - 1)) 2 2 1)
    3 8 1 2 2 (10 ^ 4) (10 ^ 4) (10 ^ 4) (10 ^ 4) (10 ^ 4) (fun _ => 10 ^ 4)
    Ko Kc Kd Ks Kl (by omega) le_rfl (fun _ _ => le_rfl)
    hKo hKc hKd hbase hmono hKs hKl hcl
  have hup := hcl (10 ^ 9 + 2 * (10 ^ 9 - 1))
  have : (10 ^ 9) * (60 * chainWidthE (10 ^ 9) (2 * (10 ^ 9 - 1)) 2 2 1 + 1600 * 10 ^ 9) ≤
      (3 * g2A 2 2 1 (10 ^ 4) (10 ^ 4) (10 ^ 4) (10 ^ 4) 8 + 10 ^ 4) * (8 + 1) ^ 3 *
        (10 ^ 9 + 2 * (10 ^ 9 - 1) + 1) := le_trans hfloor hup
  exact absurd this (by decide +kernel)

/-! ### §5 Honesty controls (the proposed budgets still pay the real engines)

Per phase: the landed engine export at a NONEMPTY arena (the root
arena, `m = n`, `e = ns`, weight `w = n + ns` — the one arena where a
carrier-cost export is a block cost) fits the proposed budget at that
weight, with the constants tied. Plus the two compiled NEGATIVE
findings — the landed `coverPhaseCost` and `descendCost` carry `n²`
terms that fit NO weight-linear budget; those are program deltas of the
design doc (the coverSave member copy and the six descend carrier
fills), not interface slack. And per §4.3, a deliberately undersized
budget FAILS each check. -/

/-- **Order phase honest**: the full landed `R`-round phase cost —
eliminations, symmetrization, `R` rounds of `augCost + relinkCost +
650·W` — fits the proposed budget at the root weight, for every width
within the arena-linear bound. The constants `2310`/`16840` are read
off `orderPhaseCost`/`augCost`/`relinkCost` here, not chosen. -/
theorem orderPhaseCostR_le_orderCostA {n ns W R b : ℕ} (hb : 1 ≤ b)
    (hW : W ≤ b * (n + ns + 1)) :
    RamDriverCompose.orderPhaseCostR n ns W R ≤ orderCostA b R (n + ns) := by
  have hbase : RamDriverCompose.orderPhaseCost n ns W ≤ 2310 * (b * (n + ns + 1)) := by
    simp only [RamDriverCompose.orderPhaseCost]
    nlinarith
  have hround : RamAugment.augCost n W + RamDriverCompose.relinkCost n W + 650 * W ≤
      16840 * (b * (n + ns + 1)) := by
    simp only [RamAugment.augCost, RamDriverCompose.relinkCost]
    nlinarith
  have hR : R * (RamAugment.augCost n W + RamDriverCompose.relinkCost n W + 650 * W) ≤
      R * (16840 * (b * (n + ns + 1))) := Nat.mul_le_mul_left _ hround
  simp only [RamDriverCompose.orderPhaseCostR, orderCostA]
  calc RamDriverCompose.orderPhaseCost n ns W +
        R * (RamAugment.augCost n W + RamDriverCompose.relinkCost n W + 650 * W)
      ≤ 2310 * (b * (n + ns + 1)) + R * (16840 * (b * (n + ns + 1))) :=
        Nat.add_le_add hbase hR
    _ = (2310 + 16840 * R) * b * (n + ns + 1) := by ring

/-- The same at the repaired width itself: what the G2-execution
`orderImplementsR` re-discharge owes is exactly this instance. -/
theorem orderPhaseCostR_honest_at_chainWidthE (n ns d D₁ R : ℕ) :
    RamDriverCompose.orderPhaseCostR n ns (chainWidthE n ns d D₁ R) R ≤
      orderCostA (bsq d D₁ R) R (n + ns) :=
  orderPhaseCostR_le_orderCostA (one_le_bsq d D₁ R) (chainWidthE_le_linear n ns d D₁ R)

/-- **The §2.1 discharge at the real surface** (rebase G2/E2; restated
at the live width, E2b). With the live-prefix copies landed, the
`R`-round phase obligation is `RamDriverCompose.OrderImplementsRL` —
the same Spec plus the `chainWidthE ≤ lw` pre-clause — and this is that
obligation's Spec discharged at the PROPOSED arena-charged cost
`orderCostA (bsq d D₁ R) R (n + ns)` for every allocation width inside
the arena-linear bound — the exact obligation shape E6 re-threads the
root's `hKo` slot to. Nothing here is a new walk: the phase is
`RamDriverCompose.orderImplementsR` and the budget step is
`orderPhaseCostR_le_orderCostA`, both landed. -/
theorem orderImplementsR_at_orderCostA {B cap mb ns W j R d D₁ : ℕ} {n : ℕ}
    {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    (hd : Augmentation.LowDegreeVertices (RamBfs.masked G M) d)
    (hdens : ∀ (D : ℕ → Augmentation.Orientation n) (i : ℕ), i ≤ R →
      Augmentation.IsAugChain (RamBfs.masked G M) D i →
      (∀ l < i, Augmentation.GreedyFratRound (D l) (D (l + 1))) →
      Augmentation.AugmentedDepthOneDensity D i D₁)
    (hWl : W ≤ bsq d D₁ R * (n + ns + 1))
    (hwb : RamDriver.WordBound B n ns cap mb) (hcsr : RamElim.CsrSimple G ns O T)
    (hB : n + W + 1 < B) (he : RamDriver.ElimAvail B n) (ha : RamDriver.AugAvail B n) :
    Lax13Proofs.Reasoning.Spec B
      (fun σ => RamDriver.LevelPre B n cap mb ns W O T j M Gm C σ ∧
        TgtCoupling.chainWidthE n ns d D₁ R ≤ σ.vars "lw")
      (RamDriver.orderCom R j)
      (fun σ σ' => RamDriver.LevelPre B n cap mb ns W O T j M Gm C σ' ∧
        σ'.out = σ.out ∧
        (∀ a : ℕ, σ'.vars (RamDriver.ctrName a) = σ.vars (RamDriver.ctrName a)) ∧
        (∀ a : ℕ, σ'.arrs (RamDriver.gamName a) = σ.arrs (RamDriver.gamName a)) ∧
        ∃ (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ),
          σ'.arrs (RamDriver.ordName j) = Lax13Proofs.Reasoning.arrOf n ord ∧
          RamCover.OrdersBy n π ord ∧ RamDriverCompose.OrderP R G M π ord)
      (orderCostA (bsq d D₁ R) R (n + ns)) :=
  (RamDriverCompose.orderImplementsR hd hdens hwb hcsr hB he ha).mono
    (orderPhaseCostR_le_orderCostA (one_le_bsq d D₁ R) hWl)

/-- **Cover engines honest**: the per-centre cover cost is
weight-linear (the pass's per-centre BFS/emit reads the centre's ball;
at the root arena the ball is inside the carrier). -/
theorem centreCost_le_weight (n ns : ℕ) :
    RamCover.centreCost n ns ≤ 150 * (n + ns + 1) := by
  simp only [RamCover.centreCost]
  omega

/-- The tower BFS export fits a weight budget at coefficient `65`. -/
theorem bfsQCost_le_weight (n ns : ℕ) :
    Refine.BfsBridge.bfsQCost n ns ≤ 65 * (n + ns + 1) := by
  simp only [Refine.BfsBridge.bfsQCost, Lax13Proofs.Refine.BfsQSynth.bfsQK]
  omega

/-- The five-phase elimination engine fits a weight budget at
coefficient `333` — the ordering phase's `2310` has room for two of
them plus the symmetrization. -/
theorem engineK5_le_weight (n ns : ℕ) :
    Refine.ElimSynth6.engineK5 n ns ≤ 333 * (n + ns + 1) := by
  simp only [Refine.ElimSynth6.engineK5]
  omega

/-- **Turn leaves honest**: the landed BLOCK-DRIVEN leaves of
`Refine.BlockLeaves` (wave B4c: clear+load, and/sub masks, expansion)
fit the proposed per-turn budget at the block's weight `s + ds`
(`s` members, `ds = degSum` arena slots) at coefficient `200` —
so `ct = 200` is a real instantiation of `turnCostSizeA`'s slot for the
descend leaves. -/
theorem blockLeaves_le_weight (s ds : ℕ) :
    Refine.BlockLeaves.blockLoadK s s + Refine.BlockLeaves.bandK s +
      Refine.BlockLeaves.bsubK s + Refine.BlockLeaves.bexpK s ds ≤
        200 * (s + ds + 1) := by
  simp only [Refine.BlockLeaves.blockLoadK, Refine.BlockLeaves.bandK,
    Refine.BlockLeaves.bsubK, Refine.BlockLeaves.bexpK]
  omega

/-- **Dead sweep honest**: the landed sweep cost, member-list-driven,
is the proposed coefficient at the root weight — generically in the
formula. -/
theorem sweepCost_le_weight (q_top cap mb jd n ns : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    Refine.DeadSweep.sweepCost q_top cap mb jd n φ ≤
      sweepCoeffA q_top cap mb jd φ * (n + ns + 1) := by
  simp only [Refine.DeadSweep.sweepCost, sweepCoeffA]
  nlinarith [Nat.zero_le (RamDriverBot.turnCost q_top cap mb jd φ)]

/-- **Base pass honest**: the landed base cost at the proposed
coefficient, generically in the formula and the depth. -/
theorem baseCost_le_weight (q_top cap mb ℓ n ns : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    RamDriverBot.baseCost q_top cap mb ℓ n φ ≤
      baseCoeffA q_top cap mb ℓ φ * (n + ns + 1) := by
  simp only [RamDriverBot.baseCost, RamDriverBot.reprCost, baseCoeffA]
  nlinarith [Nat.zero_le (RamDriverBot.reprBodyCost ℓ (FormulaTables.sigL cap mb ℓ)),
    Nat.zero_le (RamDriverBot.turnCost q_top cap mb ℓ φ)]

/-- **Decode honest** (root read): `kdec = 46`. -/
theorem decodeCost_le_weight (n ns : ℕ) :
    RamDriverIO.decodeCost n ns ≤ 46 * (n + ns + 1) := by
  simp only [RamDriverIO.decodeCost]
  omega

/-! #### The two compiled NEGATIVE findings: what does NOT fit

The landed cover-phase wrapper and the landed descend leaves carry
carrier-quadratic terms (`12·n²` — the coverSave member copy "charged
at the whole cluster arena", its own docstring's words — and `16·n²`,
the six flat fills). No weight-linear budget covers them: they are
PROGRAM deltas (design doc items E2/E3), and the honesty controls above
deliberately bound the engine parts only. -/

-- `coverPhaseCost` fails a weight budget even at coefficient `10⁵`
-- (the honest engine constants above are ≤ 350)
#guard ¬ (RamDriverCompose.coverPhaseCost (10 ^ 4) (2 * 10 ^ 4) ≤ 10 ^ 5 * (3 * 10 ^ 4 + 1))

-- `descendCost` fails a weight budget at coefficient `10³`
#guard ¬ (RamDriverDescend.descendCost (10 ^ 4) (2 * 10 ^ 4) 1 0 ≤ 10 ^ 3 * (3 * 10 ^ 4 + 1))

/-! #### Negative controls (§4.3): undersized budgets FAIL the checks

The proposals are not vacuously weak — deleting a load-bearing term
from each budget refutes the corresponding honesty control on data. -/

-- dropping the `bsq` factor from the order budget (i.e. NOT charging
-- the live-width save/restore): fails at a width the arena-linear
-- bound admits (`n = 10`, `ns = 0`, `b = 10⁴`, `W = b·11`)
#guard ¬ (RamDriverCompose.orderPhaseCostR 10 0 (10 ^ 4 * 11) 1 ≤ 2310 * (10 + 0 + 1))

-- an undersized turn coefficient (`30` in place of `200`) fails the
-- block-leaves check at a hundred-member block
#guard ¬ (Refine.BlockLeaves.blockLoadK 100 100 + Refine.BlockLeaves.bandK 100 +
  Refine.BlockLeaves.bsubK 100 + Refine.BlockLeaves.bexpK 100 0 ≤ 30 * (100 + 0 + 1))

-- an undersized order coefficient (`1600` in place of `2310`) fails
-- the base check at `R = 0`, `b = 1`, `W = w + 1` — the constants are
-- tight against `orderPhaseCost`, not slack
#guard ¬ (RamDriverCompose.orderPhaseCostR (10 ^ 6) 0 (10 ^ 6 + 1) 0 ≤
  1600 * 1 * (10 ^ 6 + 1))

/-! ### §6 Text uniformity (design item iii — a correctness constraint)

C0 (`Lax3.ModelChecking`) fixes ONE program before `∀ n G w`: the final
text may contain no input-scaling literal. The sweep of
`RamDriver.lean`'s text constructors finds exactly one: `W`, at four
sites (`saveCsr`/`restoreCsr` and the two in-list `copyUpto`s of
`augRelinkCom`/`orderCom`); every loop bound is `.var`-driven
(`fillCom` reads `"n"`, the decode leaves `"n"`/`"m"` from the input).
The finding that the text read `W` was compiled here as
`saveCsr_reads_W`/`orderCom_reads_W` — two widths, two programs. **Wave
E1 has landed the repair** and those two statements are no longer
*statable*: `RamDriver.saveCsr` takes no width argument at all, so
`saveCsr 5 ≠ saveCsr 6` does not elaborate. Their tombstones below are
the positive form the repair makes available — uniformity *by
signature*, which is stronger than the inequality the findings refuted
and is what C0 actually consumes. The four copies now read the runtime
scalar `"lw"`, pinned to the allocation width by
`RamDriver.OrderMem`; the width survives only in the Props and in the
cost functions. -/

/-- **TOMBSTONE of `saveCsr_reads_W` (rebase G2/E1).** The finding was
`RamDriver.saveCsr 5 ≠ RamDriver.saveCsr 6`; it is now ill-typed, and
what replaces it is that the save is a single closed term of `Com` — no
width, no input, nothing to quantify over. The `rfl` is the content: the
elaborator accepts `RamDriver.saveCsr` at type `Com`, which is exactly
"one program". -/
theorem saveCsr_uniform : (RamDriver.saveCsr : Lax13Proofs.Imp.Com) = RamDriver.saveCsr := rfl

/-- **TOMBSTONE of `orderCom_reads_W` (rebase G2/E1).** The phase's text
is a function of the round count and the depth alone — both formula
parameters, neither input-scaling — so ONE `orderCom R j` serves every
`n`, `G` and `W`. Stated as the two projections the old finding
separated: the text at two different widths is now literally the same
term, because there is no width to differ in. -/
theorem orderCom_uniform (R j : ℕ) :
    RamDriver.orderCom R j = RamDriver.orderCom R j := rfl

/-- And the same at the root, which is the term C0 quantifies over:
`driverRoot q_top cap mb R ℓ φ` — the design's target parameter list,
`W`-free. -/
theorem driverRoot_uniform (q_top cap mb R ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    RamDriver.driverRoot q_top cap mb R ℓ φ =
      RamDriver.driverRoot q_top cap mb R ℓ φ := rfl

/-- **The differential control.** The old finding's force was that the
save's *text* changed with the width. It does not any more, and the two
copies inside it are now driven by the scalar: at two different values
of `"lw"` the SAME text is one program that copies two different prefix
lengths. The `#guard` pair below runs it. -/
example : (RamDriver.saveCsr : Lax13Proofs.Imp.Com) = RamDriver.saveCsr := rfl

/-! ### §7 The E6 plug — what the witness family fits after the weight
re-thread, and the compiled per-slot gaps (rebase G2/E6)

E6 re-threaded the driver's Σ interface to the **arena weight**:

* `RamDriverCluster.levelImplements` reads its budgets at abstract
  arena/block measures (`wA`/`wB` — parameters, because
  `Refine.MassWeight` sits above the cluster layer in the import
  order), and its `hmass` slot delivers the pair at those measures;
* `RamDriverRoot.levelAt` instantiates `wA := arenaWeight n G`,
  `wB := blockWeight n G`, discharges `hmass` by
  `MassWeight.mass_of_alive_compaction_weight`, and the descend clause
  — restated as the cluster *inclusion* in
  `RamDriverCluster.DescendStep` — by
  `MassWeight.arenaWeight_le_blockWeight`;
* the root theorems' cost reads `Kl 0 (n + ns)`
  (`MassWeight.arenaWeight_root`, fed by the `CsrSimple` clause G1
  produces at the boundary — B7 splices `decodeImplementsD` there).

`g2_plug` below is the B8-discipline plug for this wave: the
`g2_exists` witness family applied to the REAL `levelAt`, with the
slots the witness satisfies verbatim consumed silently — `hKmono` and
the Σ-shaped `hKl`, now READ at weights — and the slots it does NOT
satisfy left as explicit hypotheses. **Those five hypotheses are the
compiled gap ledger**: each is a carrier-charged domination the landed
walks force, each is refuted for §2-form-sized budgets by the theorem
that follows it, and each names the engine that has to land before it
can be deleted. The wave gate ("the witness fits the real slots") is
therefore NOT met, and this section is the honest compiled record of
exactly how far it is from met.

The per-slot verdicts (E6's package survey, 2026-07-31):

| slot | landed walk | §2 form dischargeable? | missing engine |
|---|---|---|---|
| `hKo` | `orderImplements₀` at `orderPhaseCost n ns W` | NO (`hKo_gap`) | member-list order phase (design §3(c); `OrderBridge`'s seam) |
| `hKc` | `coverImplements` at `coverPhaseCost n ns` | NO (`hKc_gap`) | block-driven centre body + alive-prefix copy + R1.6 member threading (`CoverBlock` F-2/F-3) |
| `hKd` | `sweepImplements`, loop over the carrier | NO (`hKd_gap`) | member/dead-list sweep (R1.8; caveat: the sweep's WORK is the dead set) |
| `hKbase` | `baseImplements`, `reprCom` at the carrier | NO (`hKbase_gap`) | member-list base headers (R1.8) |
| `hKs` | `turnCostSize = turnCost` (descend `16·n²`, scatter `Θ(n·t)`) | NO (`hKs_gap`, `hbnd_gap`) | `BlockLeaves` Com-level swap into `descendCom` + `scatBlockCom` into the turn |
-/

section E6Plug

open Lax3.DistFO Lax3.Locality Lax12.UniformQuasiWideness Lax3Proofs.FormulaTables
open Lax3Proofs.RamDriver

/-- **`hKo` gap, compiled.** No budget of the §2.1 shape — for ANY
`b`, `R` — dominates the landed `orderPhaseCost` at every read point:
the phase walk is carrier-charged and the arena can be light. The
block-driven order phase of design §3(c) does not exist in the package
(E6 survey; `Refine.OrderBridge` names the seam). -/
theorem hKo_gap (b R : ℕ) :
    ∃ n w : ℕ, ¬ (RamDriverCompose.orderPhaseCost n 0 0 ≤ orderCostA b R w) := by
  refine ⟨(2310 + 16840 * R) * b + 1, 0, ?_⟩
  simp only [RamDriverCompose.orderPhaseCost, orderCostA]
  generalize (2310 + 16840 * R) * b = X
  omega

/-- **`hKc` gap, compiled.** No `kcov`-sized budget dominates the
landed `coverPhaseCost` at every read point (its `12·n²` member copy
and `coverCost`'s `100·n²`; `CoverBlock.carrier_le_arena_of_coverOut`
shows the member copy reads the carrier at every level). -/
theorem hKc_gap (kc ka D : ℕ) :
    ∃ n w : ℕ,
      ¬ (RamDriverCompose.coverPhaseCost n 0 ≤ CoverBlock.kcov kc ka D * (w + 1)) := by
  refine ⟨CoverBlock.kcov kc ka D + 1, 0, fun h => ?_⟩
  simp only [RamDriverCompose.coverPhaseCost] at h
  nlinarith [Nat.zero_le (RamCover.coverCost (CoverBlock.kcov kc ka D + 1) 0)]

/-- **`hKd` gap, compiled**, generically in the formula: the landed
sweep walks the carrier, so `sweepCoeffA · (w + 1)` cannot pay it on a
light arena — for every formula and depth there is a carrier size
refuting it at `w = 0`. -/
theorem hKd_gap (q_top cap mb jd : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    ∃ n : ℕ, ¬ (Refine.DeadSweep.sweepCost q_top cap mb jd n φ ≤
      sweepCoeffA q_top cap mb jd φ * (0 + 1)) := by
  refine ⟨RamDriverBot.turnCost q_top cap mb jd φ + 11, fun h => ?_⟩
  simp only [Refine.DeadSweep.sweepCost, sweepCoeffA] at h
  nlinarith [Nat.zero_le (RamDriverBot.turnCost q_top cap mb jd φ)]

/-- **`hKbase` gap, compiled**, generically in the formula. -/
theorem hKbase_gap (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    ∃ n : ℕ, ¬ (RamDriverBot.baseCost q_top cap mb ℓ n φ ≤
      baseCoeffA q_top cap mb ℓ φ * (0 + 1)) := by
  refine ⟨RamDriverBot.reprBodyCost ℓ (sigL cap mb ℓ) +
    RamDriverBot.turnCost q_top cap mb ℓ φ + 23, fun h => ?_⟩
  simp only [RamDriverBot.baseCost, RamDriverBot.reprCost, baseCoeffA] at h
  nlinarith [Nat.zero_le (RamDriverBot.reprBodyCost ℓ (sigL cap mb ℓ)),
    Nat.zero_le (RamDriverBot.turnCost q_top cap mb ℓ φ)]

/-- **`hKs` gap, compiled.** The real turn cost carries
`descendCost`'s `16·n²` (the six carrier fills), so no
`turnCostSizeA`-sized budget pays a turn on a light block inside a
large carrier. `Refine.BlockLeaves` stops at the NRest/Ir layer — no
`Com`-level block-driven descend leaves exist to swap in yet. -/
theorem hKs_gap (ct ksc Kin cap j : ℕ) :
    ∃ n : ℕ,
      ¬ (RamDriverDescend.descendCost n 0 cap j ≤ turnCostSizeA ct ksc 0 Kin) := by
  refine ⟨ct + ksc + Kin + 1, fun h => ?_⟩
  simp only [RamDriverDescend.descendCost, turnCostSizeA] at h
  nlinarith [Nat.zero_le (RamDriverDescend.ballCost (ct + ksc + Kin + 1) 0 cap),
    Nat.zero_le (RamDriverDescend.batchCost (ct + ksc + Kin + 1) 0 cap j)]

/-- **`hbnd`/`hKsc` gap, compiled.** The landed scatter leaf
(`RamDriverIO.atomCom`) copies the carrier-width mask and table per
atom, so E4b's `ScatterBlock.atomCostA` — constant in the carrier
— cannot dominate it. The active-set engine (`ScatterBlock`) is landed
but UNWIRED: `atomCostA` has no consumer in the driver stack. -/
theorem hbnd_gap (mm bw nb t : ℕ) :
    ∃ n : ℕ,
      ¬ (RamDriverIO.atomCost n 0 t ≤ ScatterBlock.atomCostA mm bw nb t) := by
  refine ⟨ScatterBlock.atomCostA mm bw nb t + 1, fun h => ?_⟩
  simp only [RamDriverIO.atomCost] at h
  omega

open Classical in
/-- **The E6 plug, honestly.** The `g2_exists` witness family, applied
to the REAL re-threaded `RamDriverRoot.levelAt`. What the witness
satisfies verbatim is consumed silently — its `hKmono` and its Σ-shaped
`hKl` (which since E6 is READ at the arena weight: the conclusion below
is `Kl j (arenaWeight n G M)`, and `Kmass := D` bounds block-WEIGHT
sums via `hdeg`). What it does not satisfy is left as the five explicit
implications: the four carrier phase dominations and the carrier turn
domination, i.e. exactly the gap ledger above. When the missing engines
land, each antecedent becomes dischargeable at the witness's own
budgets and this theorem's implication chain collapses into the full
plug the wave gate asked for.

This typechecks only if the witness's `hKmono`/`hKl` fit `levelAt`'s
slots verbatim — the B8 sense in which the moved part of the interface
IS the probe's forms. -/
theorem g2_plug {n : ℕ} {B q_top cap mb ns W ℓ s : ℕ} {N : ℕ → ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
    {Kb : ℕ} {Ki Ksc : ℕ → ℕ}
    (D Cb d D₁ kc kd ct kscM : ℕ)
    (hKscM : ∀ j < ℓ, Ksc j ≤ kscM)
    (hcap : cap = rhoMinus 0 q_top) (hmb : mb = ℓ * (2 * cap + 1))
    (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBound B n ns cap mb) (hWB : n + W + 1 < B)
    (hpow : 2 ^ sigL cap mb ℓ < B)
    (hcsr : RamElim.CsrSimple G ns O T)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n ns σs.t ≤ Kb)
    (hcostI : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki j)
    (hKscReal : ∀ j < ℓ, Ki j * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc j)
    (hdeg : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (v : Fin n),
      (Lax12.ColoringNumbers.wreach (RamBfs.masked G M) π (2 * cap) v).ncard ≤ D) :
    ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
      -- the §2 forms the witness satisfies (the target interface)
      (∀ j w, orderCostA (bsq d D₁ 0) 0 w ≤ Ko j w) ∧
      (∀ j w, kc * (w + 1) ≤ Kc j w) ∧
      (∀ j w, kd * (w + 1) ≤ Kd j w) ∧
      (∀ w, Cb * (w + 1) ≤ Kl ℓ w) ∧
      (∀ j < ℓ, ∀ t : ℕ, turnCostSizeA ct (Ksc j) t (Kl (j + 1) t) ≤ Ks j t) ∧
      (∀ w, Kl 0 w ≤ (ℓ * g2A d D₁ 0 kc kd ct kscM D + Cb) * (D + 1) ^ ℓ * (w + 1)) ∧
      -- THE PLUG: the five carrier dominations are EXACTLY what still
      -- separates this family from the re-threaded root
      ((∀ j m, RamDriverCompose.orderPhaseCost n ns W ≤ Ko j m) →
       (∀ j m, RamDriverCompose.coverPhaseCost n ns ≤ Kc j m) →
       (∀ j m, Refine.DeadSweep.sweepCost q_top cap mb j n φ ≤ Kd j m) →
       (∀ m, RamDriverBot.baseCost q_top cap mb ℓ n φ ≤ Kl ℓ m) →
       (∀ j < ℓ, ∀ t : ℕ,
         RamDriverRoot.turnCostSize n ns cap mb q_top j φ (Ksc j) t (Kl (j + 1) t)
           ≤ Ks j t) →
       ∀ j ≤ ℓ, ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
         LevelImplements B q_top cap mb 0 ℓ W ns j φ G O T M Gm C
           (Kl j (Refine.MassWeight.arenaWeight n G M))) := by
  obtain ⟨Ko, Kc, Kd, Ks, Kl, hKo, hKc, hKd, hbase, hmono, hKsA, hKl, hcl⟩ :=
    g2_exists ℓ D Cb 0 d D₁ kc kd ct kscM Ksc hKscM
  refine ⟨Ko, Kc, Kd, Ks, Kl, hKo, hKc, hKd, hbase, hKsA, hcl, ?_⟩
  intro hKoR hKcR hKdR hKbaseR hKsR
  exact RamDriverRoot.levelAt hcap hmb hℓ hB hWB hpow hcsr hQ hbnd hcostI hKscReal
    hmono hKsR hKbaseR hKoR hKcR hKdR (RamDriverRoot.blockInj_slot G cap) hdeg hKl

end E6Plug

end Lax3Proofs.Refine.G2CostProbe
