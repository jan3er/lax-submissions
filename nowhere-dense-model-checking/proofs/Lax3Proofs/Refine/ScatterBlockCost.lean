import Lax3Proofs.Refine.BfsBlock
import Lax3Proofs.Refine.MassWeight
import Lax3Proofs.Refine.ScatterSynth

/-!
# The active-set scatter charge, and the readings it refutes

This file is the **cost side** of the active-set scatter engine, written
before the engine, in the campaign's refute-before-prove order: the
numbers are fixed here, the falsifications of the wrong readings are
compiled here, and `Refine/ScatterBlock.lean` then has to meet them. A
walk that cannot meet a constant stated here is a defect report, not a
licence to edit the constant downward after the fact.

### What is wrong with the landed charge

The landed greedy scatter charges

    RamScatter.scatterCost n ns t = pickCost n ns * t + 36 * n + 20,
    pickCost n ns                = 74 * n + 44 * ns + 60,

and the tower's whole-engine reading is `ScatterSynth.scatK n ns t =
(94 n + 40 ns + 50) t + 33 n + 4`. **Every** term is the carrier. There
are three separate reasons, and an engine that removes only one of them
is still `Θ(n)` per turn:

1. the scan walks all `n` vertices asking `tab[v] > 0`;
2. the pass clears all `n` exclusion bits before it starts;
3. each of the `t` picks runs a carrier-sized search (`51 n + 44 ns +
   30`, whose `n` is the initial fill) and then a carrier-sized marking
   sweep (`23 n + 6`, a flat pass over the distance array).

The driver multiplies this by the per-atom count and then by the turn
count, which is the `Ω(n · W)` phase-cost floor the B7 gate compiled:
`RamDriverIO.atomCost n ns t = 24 n + 14 + scatterCost n ns t`, read per
turn through `hbnd → hcostI → hKsc`.

### What the active-set charge is

The engine of `Refine/ScatterBlock.lean` replaces all three:

1. the scan walks the **member list** of `X` — `mm` entries, not `n`;
2. the clear walks the member list too, which is sound because the scan
   only ever *reads* an exclusion bit at a member;
3. a pick runs `BfsBlock.bfsBlockCom`, charged to its ball at
   `bfsBlockK bw nb = 44 bw + 80 nb + 60`, and then marks the ball by
   walking the queue the search hands back — the ball is exactly
   `q[0 .. tail)`, so marking is `O(nb)` and never touches a cell the
   search did not reach.

So the charge is `scatBlockK mm bw nb t`, and **neither `n` nor `ns`
occurs in it**. That absence is the whole deliverable; the numerals
below are chosen with slack, because a slack numeral costs an accounting
constant and a carrier term costs a theorem.

### The three gates in this file

* §2 `scatBlockK_carrier_free_vs_scatK` — at *fixed* member data the
  landed charge is unbounded and the active one is a constant. This is
  the statement "the carrier term died", in the only form that is not
  vacuous.
* §3 the **size-refutation twin**: a small active set in a huge carrier,
  compiled, where the landed form overpays by a factor no numeral
  bounds. Paired, as the probe's honesty discipline asks, with the
  refutation of the *inadmissible* reading of the new charge — that a
  ball may be charged by its size and its edges forgotten.
* §4 the **clock gate**: at the worked instance the active charge is
  strictly below the landed one, on the nose, by `decide +kernel`.
-/

namespace Lax3Proofs.Refine.ScatterBlock

open Lax3Proofs.Refine

/-! ### §1 The charge

Four numerals, read off the four things a pass does. Each is stated
separately so that a walk that misses one is a report about *that* limb
and not about the pass. -/

/-- **Marking a ball.** The queue the block search hands back is the
ball, in arrival order; marking walks it and sets one exclusion bit per
entry, then sets the source's bit unconditionally — the search writes a
dead source's distance cell but never enqueues it, so the queue alone
would miss it. Charged to the ball's size, `nb`. -/
def markBallK (nb : ℕ) : ℕ := 30 * nb + 20

/-- **One pick.** The block-driven search, the marking of its ball, and
the constant of the three tests and two assignments around them.
Carrier-free because `bfsBlockK` is. -/
def pickBlockK (bw nb : ℕ) : ℕ := BfsBlock.bfsBlockK bw nb + markBallK nb + 60

/-- **Clearing the exclusion bits at the members.** The landed pass
clears all `n`; the active pass clears the `mm` cells the scan will
read, which is every cell whose value the scan's answer depends on. -/
def clearMemK (mm : ℕ) : ℕ := 25 * mm + 12

/-- **The scan.** One turn per member of `X`, each a pair of tests and a
counter bump. -/
def scanMemK (mm : ℕ) : ℕ := 40 * mm + 12

/-- **The active-set greedy scatter pass**: `t` picks, each charged to
its ball, and two walks of the member list. **No `n`, no `ns`.** -/
def scatBlockK (mm bw nb t : ℕ) : ℕ :=
  pickBlockK bw nb * t + clearMemK mm + scanMemK mm + 6

/-- The closed form, for the arithmetic gates. -/
theorem scatBlockK_eq (mm bw nb t : ℕ) :
    scatBlockK mm bw nb t = (44 * bw + 110 * nb + 140) * t + 65 * mm + 30 := by
  simp only [scatBlockK, pickBlockK, markBallK, clearMemK, scanMemK, BfsBlock.bfsBlockK]
  ring

/-- Monotone in every argument, which is what lets a consumer pass any
superset of the ball and any bound on the member count. -/
theorem scatBlockK_mono {mm mm' bw bw' nb nb' t t' : ℕ} (hm : mm ≤ mm') (hb : bw ≤ bw')
    (hn : nb ≤ nb') (ht : t ≤ t') : scatBlockK mm bw nb t ≤ scatBlockK mm' bw' nb' t' := by
  simp only [scatBlockK_eq]
  have h₁ : (44 * bw + 110 * nb + 140) * t ≤ (44 * bw' + 110 * nb' + 140) * t' :=
    Nat.mul_le_mul (by omega) ht
  omega

/-! ### §1b The atom, and the two member-list copies

`RamDriverIO.atomCost n ns t = 24 n + 14 + RamScatter.scatterCost n ns t`
is the landed per-atom charge: two carrier-width `copyCom`s at
`12 n + 6` apiece, the pass, and the flag. The successor charges the two
copies at the **member count** — the pattern is `CoverBlock.memCopyK mm
= 12 mm + 6`, which is `RamDriverCompose.copyPrefix_spec`'s exported
cost — and the pass at `scatBlockK`.

The landed form is restated here rather than imported: `RamDriverIO` is
the driver stack, which a sibling wave is editing, and this file is
required to be readable against a moving stack. `atomCostLanded` is
definitionally the landed `atomCost`, and E6 should discharge that by
`rfl` when it re-threads. -/

/-- The landed per-atom charge, restated. -/
def atomCostLanded (n ns t : ℕ) : ℕ := 24 * n + 14 + RamScatter.scatterCost n ns t

/-- **The per-atom charge at the member reading.** Two member-list
copies, the active-set pass, the flag. -/
def atomCostA (mm bw nb t : ℕ) : ℕ :=
  (12 * mm + 6) + (12 * mm + 6) + (scatBlockK mm bw nb t + 2)

theorem atomCostA_eq (mm bw nb t : ℕ) :
    atomCostA mm bw nb t = (44 * bw + 110 * nb + 140) * t + 89 * mm + 44 := by
  simp only [atomCostA, scatBlockK_eq]; ring

theorem atomCostA_mono {mm mm' bw bw' nb nb' t t' : ℕ} (hm : mm ≤ mm') (hb : bw ≤ bw')
    (hn : nb ≤ nb') (ht : t ≤ t') : atomCostA mm bw nb t ≤ atomCostA mm' bw' nb' t' := by
  simp only [atomCostA]
  have := scatBlockK_mono hm hb hn ht
  omega

/-! ### §2 The carrier term is gone

The statement "the charge has no `n` in it" is not a theorem — `n` is
not an argument. What *is* a theorem, and what the phase re-thread
actually needs, is that at **fixed** member data the landed charge grows
without bound while the active one does not move. -/

/-- **The landed charge is unbounded in the carrier**, at any positive
threshold and any slot count. -/
theorem scatK_unbounded (ns t K : ℕ) (ht : 1 ≤ t) : ∃ n, K < ScatterSynth.scatK n ns t := by
  refine ⟨K + 1, ?_⟩
  simp only [ScatterSynth.scatK]
  have h : 94 * (K + 1) + 40 * ns + 50 ≤ (94 * (K + 1) + 40 * ns + 50) * t :=
    Nat.le_mul_of_pos_right _ ht
  omega

/-- **The two together**: no numeral bounds the landed charge in terms of
the active one. This is the honest form of "the `Θ(n)`-per-turn class
dies", and it is the one E6 quotes. -/
theorem scatBlockK_carrier_free_vs_scatK (mm bw nb t : ℕ) (ht : 1 ≤ t) (c : ℕ) :
    ∃ n ns, c * scatBlockK mm bw nb t < ScatterSynth.scatK n ns t := by
  obtain ⟨n, hn⟩ := scatK_unbounded 0 t (c * scatBlockK mm bw nb t) ht
  exact ⟨n, 0, hn⟩

/-! ### §3 The size-refutation twin

The probe's discipline is that every admissible reading is paired with a
compiled refutation of an inadmissible one. There are two here, pointing
in opposite directions.

**Downward** — the landed reading is inadmissible for a small active set
in a large carrier. A single member of `X` sitting in a carrier of four
thousand vertices is the worked shape: the pass has one member to look
at, one ball to search, and the landed charge still pays for the whole
carrier three times over.

**Upward** — the *new* reading must not be undersold either. A ball may
not be charged by its size alone: a star's centre is one vertex whose
block is arbitrarily long, and an engine that forgot the edges would be
claiming to read a row it did not pay for. This is
`BfsBlock.bfsBlockK_size_refuted`'s shape, lifted to the pass. -/

/-- A small active set in a large carrier: one member, a ball of three
vertices spanning six slots, one pick. -/
def smallActive : ℕ × ℕ × ℕ × ℕ := (1, 6, 3, 1)

/-- The carrier it sits in, and that carrier's slot count. -/
def bigCarrier : ℕ × ℕ := (4096, 8192)

/-! The two numbers, seen. -/

#guard scatBlockK 1 6 3 1 = 829
#guard ScatterSynth.scatK 4096 8192 1 = 847926

/-- **The landed charge overpays by more than a factor of a thousand**
at that instance — compiled, and by the kernel. -/
theorem landed_overpays_smallActive :
    1000 * scatBlockK 1 6 3 1 < ScatterSynth.scatK 4096 8192 1 := by
  decide +kernel

/-- **And no numeral rescues it**: for every coefficient there is a
carrier at which the landed charge exceeds that multiple of the active
one, with the member data held fixed. -/
theorem landed_overpays_unboundedly (c : ℕ) :
    ∃ n ns, c * scatBlockK 1 6 3 1 < ScatterSynth.scatK n ns 1 :=
  scatBlockK_carrier_free_vs_scatK 1 6 3 1 le_rfl c

/-- **The inadmissible reading of the new charge is refuted**: the ball's
size does not bound the pass. A star centre is one vertex with a block as
long as you like, and the pass must pay for the row it scans. -/
theorem scatBlockK_size_refuted (ct : ℕ) :
    ∃ mm bw nb t : ℕ, ¬ (scatBlockK mm bw nb t ≤ ct * (mm + nb + 1)) := by
  refine ⟨1, ct + 1, 1, 1, ?_⟩
  simp only [scatBlockK_eq]
  have h : ct * 3 ≤ 44 * (ct + 1) := by omega
  omega

/-- **The member count is not optional either.** An engine charged only
by its ball would be claiming to scan an active set it did not pay for:
at a fixed ball and a fixed threshold, the charge must still grow with
the member count. -/
theorem scatBlockK_member_refuted (ct : ℕ) :
    ∃ mm bw nb t : ℕ, ¬ (scatBlockK mm bw nb t ≤ ct * (bw + nb + t + 1)) := by
  refine ⟨ct, 0, 0, 0, ?_⟩
  simp only [scatBlockK_eq]
  omega

/-! ### §4 The honesty controls, and the clock

`G2CostProbe` §5 reads every landed engine as `k * (weight + 1)` at a
numeral `k` fixed before the input. The active pass's weight is the
ball's — `nb` members and `bw` slots, which is `MassWeight.blockSize +
blockRowSum`, which is `slotWeight n (csrW n O)` — together with the
active set's own size, and the threshold multiplies the ball part. -/

/-- **The pass is weight-linear at coefficient `140`**, against the sum
of the active set's size and the ball's weight, with the threshold as the
multiplier it genuinely is. This is the active-set replacement for
`G2CostProbe.bfsQCost_le_weight`'s `65 * (n + ns + 1)`, whose `n` and
`ns` are the carrier. -/
theorem scatBlockK_le_weight (mm bw nb t : ℕ) :
    scatBlockK mm bw nb t ≤ 140 * ((bw + nb + 1) * t + mm + 1) := by
  simp only [scatBlockK_eq]
  have h : (44 * bw + 110 * nb + 140) * t ≤ 140 * ((bw + nb + 1) * t) := by
    have : 44 * bw + 110 * nb + 140 ≤ 140 * (bw + nb + 1) := by omega
    calc (44 * bw + 110 * nb + 140) * t ≤ (140 * (bw + nb + 1)) * t :=
          Nat.mul_le_mul_right _ this
      _ = 140 * ((bw + nb + 1) * t) := by ring
  omega

/-- **The atom too**, at coefficient `140`: the two member copies are
absorbed by the member term. -/
theorem atomCostA_le_weight (mm bw nb t : ℕ) :
    atomCostA mm bw nb t ≤ 140 * ((bw + nb + 1) * t + mm + 1) := by
  simp only [atomCostA_eq]
  have h : (44 * bw + 110 * nb + 140) * t ≤ 140 * ((bw + nb + 1) * t) := by
    have : 44 * bw + 110 * nb + 140 ≤ 140 * (bw + nb + 1) := by omega
    calc (44 * bw + 110 * nb + 140) * t ≤ (140 * (bw + nb + 1)) * t :=
          Nat.mul_le_mul_right _ this
      _ = 140 * ((bw + nb + 1) * t) := by ring
  omega

/-- **A negative control, in the probe's §4.3 shape**: an undersized
coefficient fails. `140` is not slack that could have been anything. -/
theorem scatBlockK_le_weight_at_100_refuted :
    ¬ (∀ mm bw nb t : ℕ, scatBlockK mm bw nb t ≤ 100 * ((bw + nb + 1) * t + mm + 1)) := by
  intro h
  have := h 0 0 0 2
  simp only [scatBlockK_eq] at this
  omega

/-! ### §5 The clock, and where it does *not* tick

The clock instance is a carrier of sixty-four vertices whose active set
is eight of them — the shape a scatter atom actually has once the cover
has cut the arena down, and the shape the phase re-thread is about.
Balls of radius one in a bounded-degree arena: at most three vertices
spanning at most six slots, three picks. -/

#guard scatBlockK 8 6 3 3 = 2752
#guard RamScatter.scatterCost 64 128 3 = 33608
#guard ScatterSynth.scatK 64 128 3 = 35674

/-- **The clock gate**: at the clock instance the active charge is an
order of magnitude below the hand-walked engine's charge for the same
pass. -/
theorem clock_below_scatterCost : 10 * scatBlockK 8 6 3 3 < RamScatter.scatterCost 64 128 3 := by
  decide +kernel

/-- And below the tower's whole-engine charge as well. -/
theorem clock_below_scatK : 10 * scatBlockK 8 6 3 3 < ScatterSynth.scatK 64 128 3 := by
  decide +kernel

/-- **The atom's clock**, against the landed per-atom charge — the
quantity `hbnd` bounds and `hcostI`/`hKsc` multiply. -/
theorem clock_atom_below_landed : 10 * atomCostA 8 6 3 3 < atomCostLanded 64 128 3 := by
  simp only [atomCostA_eq, atomCostLanded, RamScatter.scatterCost, RamScatter.pickCost]
  decide +kernel

/-! ### §5b The crossover, stated rather than hidden

The active engine is **not** pointwise cheaper than the landed one. When
the active set is the whole carrier there is by definition nothing to
scan less of, and the numerals above carry deliberate slack — each was
chosen with room so that a walk meeting it is a walk about carrier
freedom and not about shaving a constant. At the differential's worked
instance, where the path `0—1—2—3—4` has every one of its five vertices
in the table, the two charges cross: the active pass is *dearer*, by
eleven units.

This is recorded, compiled, because a gate that only ever reports
success is not a gate. What the engine claims is that the charge has no
carrier term — §2 and §3 — and not that it wins at every instance. E6
should read the crossover as the statement that the re-thread's benefit
is a function of `mm / n`, and that an atom whose active set is the
whole arena gains nothing. -/

#guard scatBlockK 5 6 3 3 = 2557
#guard RamScatter.scatterCost 5 8 3 = 2546

/-- **At `mm = n` the active charge does not beat the landed one.** -/
theorem clock_crossover_at_full_active :
    ¬ (scatBlockK 5 6 3 3 < RamScatter.scatterCost 5 8 3) := by
  decide +kernel

/-- Against the *tower's* charge it still wins at that instance, which
locates the crossover between the two landed readings rather than beyond
both. -/
theorem clock_full_active_below_scatK : scatBlockK 5 6 3 3 < ScatterSynth.scatK 5 8 3 := by
  decide +kernel

/-! And the instance the phase re-thread actually meets: the active set
is a vanishing fraction of the carrier, and then the gap is the one §3
compiled. -/

#guard atomCostA 1 6 3 1 = 867
#guard atomCostLanded 4096 8192 1 = 909406

/-! ### §6 The bridge family the phase re-thread consumes

`RamDriverRoot`'s `clusterStepAt`, `clusterFramesAt`, `levelAt`,
`levelAt_of_sigma` and the two `driverRoot_decides_sentence` theorems
all carry the same three hypotheses, in this order:

    hbnd   : ∀ β ∈ tables, ∀ σs ∈ atoms β,
               σs.r + 1 < B ∧ σs.t < B ∧ atomCost n ns σs.t ≤ Kb
    hcostI : ∀ β ∈ tables, Kb * (atoms β).length + 1 ≤ Ki
    hKsc   : Ki * tables.length + 1 ≤ Ksc

`Ksc` then enters `turnCost` and is paid **per turn**, which is where the
`Θ(n)`-per-turn class the B7 gate compiled comes from: `atomCost n ns t`
carries `24 n + 14 + scatterCost n ns t`, so every one of those `n`s is
multiplied by the atom count, the table count and the turn count.

The shapes are restated here over abstract atom data rather than imported
from the driver stack, for the reason §1b gives — a sibling wave is
editing that stack, and a bridge that cannot be read against a moving
stack is not a bridge. An atom is modelled as its `(radius, threshold)`
pair, which is all three shapes ever look at. E6 instantiates
`atoms β := (bcAtomsOf q_top (stepFml cap mb j β)).2` and reads the
`.length`s off the same lists it reads today.

This is the `G2CostProbe` §4.1 pattern: local defs plus satisfiability
lemmas, so that the existence of a budget is a theorem and not an
assumption. -/

/-- The `hbnd` shape at the member reading. -/
def HbndA (B Kb mm bw nb : ℕ) (atoms : List (ℕ × ℕ)) : Prop :=
  ∀ a ∈ atoms, a.1 + 1 < B ∧ a.2 < B ∧ atomCostA mm bw nb a.2 ≤ Kb

/-- The `hcostI` shape: the per-block budget covers every block's atoms. -/
def HcostA (Kb Ki : ℕ) (blocks : List (List (ℕ × ℕ))) : Prop :=
  ∀ l ∈ blocks, Kb * l.length + 1 ≤ Ki

/-- The `hKsc` shape: the phase budget covers every block. -/
def HKscA (Ki Ksc nblocks : ℕ) : Prop := Ki * nblocks + 1 ≤ Ksc

/-- **The per-atom budget is satisfiable**, at the charge of the largest
threshold. Monotonicity in `t` is what makes one numeral serve every
atom. -/
theorem hbndA_sat {B mm bw nb tmax : ℕ} {atoms : List (ℕ × ℕ)}
    (hr : ∀ a ∈ atoms, a.1 + 1 < B) (ht : ∀ a ∈ atoms, a.2 < B)
    (htm : ∀ a ∈ atoms, a.2 ≤ tmax) :
    HbndA B (atomCostA mm bw nb tmax) mm bw nb atoms := fun a ha =>
  ⟨hr a ha, ht a ha, atomCostA_mono le_rfl le_rfl le_rfl (htm a ha)⟩

/-- **The per-block budget is satisfiable**, at the largest atom count. -/
theorem hcostA_sat {Kb amax : ℕ} {blocks : List (List (ℕ × ℕ))}
    (h : ∀ l ∈ blocks, l.length ≤ amax) : HcostA Kb (Kb * amax + 1) blocks := by
  intro l hl
  have h₁ : Kb * l.length ≤ Kb * amax := Nat.mul_le_mul_left _ (h l hl)
  omega

/-- **And the phase budget is satisfiable**, on the nose. -/
theorem hKscA_sat (Ki nblocks : ℕ) : HKscA Ki (Ki * nblocks + 1) nblocks := le_rfl

/-- **The scatter phase's charge at the member reading**, composed
through the three shapes: `amax` atoms per block, `nblocks` blocks. -/
def KscA (mm bw nb tmax amax nblocks : ℕ) : ℕ :=
  (atomCostA mm bw nb tmax * amax + 1) * nblocks + 1

/-- **The three shapes compose to it**, which is the statement E6 needs:
given the word bounds and the two counts, the phase budget `KscA` is
met. -/
theorem kscA_sat {B mm bw nb tmax amax nblocks : ℕ} {blocks : List (List (ℕ × ℕ))}
    (hlen : blocks.length ≤ nblocks) (hat : ∀ l ∈ blocks, l.length ≤ amax)
    (hr : ∀ l ∈ blocks, ∀ a ∈ l, a.1 + 1 < B) (ht : ∀ l ∈ blocks, ∀ a ∈ l, a.2 < B)
    (htm : ∀ l ∈ blocks, ∀ a ∈ l, a.2 ≤ tmax) :
    (∀ l ∈ blocks, HbndA B (atomCostA mm bw nb tmax) mm bw nb l) ∧
      HcostA (atomCostA mm bw nb tmax) (atomCostA mm bw nb tmax * amax + 1) blocks ∧
      HKscA (atomCostA mm bw nb tmax * amax + 1) (KscA mm bw nb tmax amax nblocks) nblocks := by
  exact ⟨fun l hl => hbndA_sat (hr l hl) (ht l hl) (htm l hl), hcostA_sat hat,
    hKscA_sat _ nblocks⟩

/-- **The phase charge is carrier-free.** `KscA` has no `n` and no `ns`
among its arguments, and the honest reading of that — as in §2 — is that
no numeral bounds the landed phase charge in terms of it. -/
theorem kscA_carrier_free (mm bw nb tmax amax nblocks c : ℕ) (ht : 1 ≤ tmax) :
    ∃ n ns, c * KscA mm bw nb tmax amax nblocks < ScatterSynth.scatK n ns tmax := by
  obtain ⟨n, hn⟩ := scatK_unbounded 0 tmax (c * KscA mm bw nb tmax amax nblocks) ht
  exact ⟨n, 0, hn⟩

/-! The phase charge at the clock instance, seen — an atom count and a
table count of four apiece, which is a formula constant. -/

#guard KscA 8 6 3 3 4 4 = 47333
#guard atomCostA 8 6 3 3 = 2958

end Lax3Proofs.Refine.ScatterBlock
