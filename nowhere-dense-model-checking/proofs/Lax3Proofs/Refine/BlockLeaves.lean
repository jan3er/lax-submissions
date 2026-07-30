import Lax3Proofs.Refine.ExpandSynth

/-!
# ND-MC rebase P0 / wave B4c — the **block-driven** carrier passes

`ClusterSynth` and `ExpandSynth` re-derived the descent's leaf passes
through the tower and, in doing so, named the floor that is left: every
one of them is a loop over the **carrier**, so a turn of the driver's
level loop costs `Θ(n)` even when the turn's cluster is a constant-size
set (2F/D-a for the fills, 2G/D-c and 2G/N-3 for the expansion). Over
the `k` centres of a level that is `Θ(n·k)`, and it is the term the
sublinear headline cannot carry.

This file removes it for the three shapes B4c owns. Each pass is
re-written to iterate the **turn's member list**

    Xmem[Xoff (cps k) .. Xoff (cps k + 1))

— the block-scan shape `ClusterSynth.scatPass` already runs (D2c) — and
each is stated at a cost in which the carrier does not occur:
`TrailRecursion`'s acceptance bar, "note what the cost function is a
function of", read one level up.

| pass | carrier form | block form here | cost |
|---|---|---|---|
| the turn's clear+load (D2a+D2b+D2c) | `OrderSynth.fillPass` at `n`, then the scan | §3 `blockLoad0` | `15·m₁ + 15·m + 30` |
| the mask passes (D3, D8, D9, C1) | `ClusterSynth.andPass`/`subPass` at `n` | §4 `bandPass`/`bsubPass` | `25·m + 4` / `29·m + 4` |
| the self-reading ones (D7d, D10) | `ClusterSynth.andSelfPass`/`subSelfPass` | §4 `bandSelfPass`/`bsubSelfPass` | ditto |
| the expansion (D6, C2, C3) | `ExpandSynth.expPass` at `n` | §5 `bexpPass` | `50·m + 30·d + 4` |

with `m` the block's size, `m₁` the **previous** turn's block size and
`d = degSum` the number of arena slots the block's members own —
`edges(block)`. **No cost function below takes `n`.**

## B4c/D-a — the write set of a turn is the previous turn's block, and
that is what makes the clear cheap

`fillCom (cluName j) 0` exists because the scan that follows it marks
only the block and the caller wants "and everything else is zero". At
the *first* turn of a level that is what a carrier fill is for; at every
later turn the only cells that are not already zero are the ones the
**previous** turn's scan marked, so zeroing the previous block restores
the same postcondition. §3 states that as an invariant which the pass
consumes and re-establishes, and §3's cost is the two blocks' sizes.

The alternative — `Iicf/IicfTrailArray`'s `treset`, which charges the
reset at the touch counter — buys the same asymptotics for a *stronger*
program (it needs no knowledge of which block was previous) at the price
of three cells per array and a `tset` per mark. It is the right device
when the write set is not known; here it *is* known, exactly, and it is
one `aget` away. §3 takes the cheaper road and §8 records the choice.

## B4c/D-b — the block-driven pass must not write off its block, and
that is the load-bearing clause

Every export below carries, next to its value clause, the **negative**
clause

    ∀ w, (∀ q ∈ [p₀, e), idx[q] ≠ w) → t.1[w]! = A₀[w]!

— the entry array survives off the block, cell for cell. That is what
makes the passes composable in a turn loop at all (the next turn's
precondition is the previous turn's postcondition), and it is what a
carrier pass can never say. §1's differential guards pin it as a
*difference*: on a carrier that is not already supported on the block,
the block-driven pass and the carrier pass **disagree**, and the guard
exhibits the cell they disagree at.

## B4c/D-c — the self-reading block passes need the block to be
injective, and the frame-reading ones do not

`ClusterSynth`'s 2F/D-c carries over, with one addition. A carrier pass
visits each cell once by construction. A block-driven pass visits the
cells `idx[p₀], …, idx[e-1]`, and nothing in the *program* stops a slot
list from naming a cell twice. For `bandPass`/`bsubPass` that is
harmless — the value written does not depend on the cell's contents, so
a repeat writes the same value again. For the **self-reading** passes it
is not: `g (g x b) b` is not `g x b`, and §1's negative control exhibits
a slot list on which the two differ. So `bandSelfPass_spec` and
`bsubSelfPass_spec` take the block's injectivity as a hypothesis. It is
free at every call site — `RamCover.CoverOut.block_inj` is exactly it —
but it is a hypothesis, and the integration wave has to thread it.

## B4c/D-d — the expansion's two currencies become "block" and
"edges(block)"

`ExpandSynth`'s outer loop is charged `E2 (iter expRowC) (iter expC)`
with the second currency's budget `off[n] - off[z]`, which telescopes
because the loop counter *is* the vertex. A block-driven loop's vertices
are `idx[p]` in whatever order the cover wrote them, so the budget
cannot be a difference of offsets: it is the sum

    degSum idx off a b = ∑_{q ∈ [a,b)} (off[idx[q]+1] - off[idx[q]])

and `Finset.sum_eq_sum_Ico_succ_bot` is what replaces the telescoping.
That sum is `edges(block)` — the arena slots the block's members own —
and it is the honest resource: over the centres of one level it sums to
the arena, exactly as the block sizes sum to the cover's write pointer.

## What is consumed rather than re-proved

`ClusterSynth.scatPass_spec` **is** the block-driven zeroing pass — at
`v := 0` rather than `1`, the same program, the same synthesis
(`ClusterSynth.scatSynth` is stated at a general `v`). `ClusterSynth`'s
`mopAget_le`/`mopAdd_le`/`mopPair_le`, `ExpandSynth`'s `expScan_le`,
`expF_le`, `hitUpto`, `expOf` and `expC`, and `ElimSynth2`'s
`while_pot_le`/`step_spec` carry everything else. Nothing here re-proves
a landed pass.

## House traps observed

`omega` is blind through `Ir.Val` and through tuple projections (`show`
first); `decide +kernel` for the numerals; never `simp [Codegen.embed]`;
junk cells are consumed in written order; loop states are assembled with
`mopPair`; `mopConstN` is the only mid-body scalar reset; compacted
loops carry their length in the invariant (B3's defect 1), which here is
the clause `e ≤ idx.length` inside every invariant rather than a side
condition.
-/

namespace Lax3Proofs.Refine.BlockLeaves

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Sepref.WordSpike
open Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax13Proofs.Refine.Codegen
open Lax13Proofs.Refine.BfsQ (Shape cu iter irWhile_exit get!_set liftACost_cu)
open Lax3Proofs.Refine.ElimSynth2 (while_pot_le step_spec)

/-! ## 1. Refute before prove

Every pass below as a computable function, run on `ClusterSynth`'s
three-block arena and on `ExpandSynth`'s path, and checked **twice**:
against the carrier pass's answer *on the block*, and against the entry
array *off* the block. The second is the wave's own novelty and every
one of its guards is a negative control — the two passes are made to
disagree, and the cell they disagree at is written out.
-/

section Twin

/-- The state of every flat pass here: the array being written and the
**slot pointer**. `ClusterSynth.FS`, so the twins compose. -/
abbrev FS : Type := List ℕ × ℕ

/-- One slot of a block-driven two-source mask pass: the member is read
out of the slot list, and both sources are read *at the member*. -/
def bmTw (g : ℕ → ℕ → ℕ) (idx a b : List ℕ) : FS → FS := fun s =>
  (s.1.set idx[s.2]! (g a[idx[s.2]!]! b[idx[s.2]!]!), s.2 + 1)

/-- …and of a *self-reading* one (B4c/D-c). -/
def bmSelfTw (g : ℕ → ℕ → ℕ) (idx b : List ℕ) : FS → FS := fun s =>
  (s.1.set idx[s.2]! (g s.1[idx[s.2]!]! b[idx[s.2]!]!), s.2 + 1)

/-- A block-driven mask pass, run from `p₀` to `e`. -/
def bmRun (p₀ e : ℕ) (g : ℕ → ℕ → ℕ) (idx a b A : List ℕ) : List ℕ :=
  (ClusterSynth.runTw (bmTw g idx a b) e (e + 1) (A, p₀)).1

/-- A self-reading one, run. -/
def bmSelfRun (p₀ e : ℕ) (g : ℕ → ℕ → ℕ) (idx b A : List ℕ) : List ℕ :=
  (ClusterSynth.runTw (bmSelfTw g idx b) e (e + 1) (A, p₀)).1

/-- **The turn's clear and load, whole**: zero the *previous* block, then
mark this one. `ClusterSynth.scatRun` at `v := 0` is the first half —
the same pass, a different stored value. -/
def refreshRun (p₁ e₁ p₀ e : ℕ) (idx A : List ℕ) : List ℕ :=
  ClusterSynth.scatRun p₀ e 1 idx (ClusterSynth.scatRun p₁ e₁ 0 idx A)

/-! ### The arena — `ClusterSynth`'s, unchanged

Six carrier vertices in three blocks: `{0, 3}`, `{5, 1, 4}`, `{2}`. The
middle block is deliberately not an identity segment, and vertex `2`
belongs to *neither* of the first two — it is the cell the block-driven
clear does not touch and the carrier fill does. -/

/-- `ClusterSynth.demoXmem`, under a short name. -/
def xm : List ℕ := ClusterSynth.demoXmem

/-- The support hypothesis, as a computable predicate on the demo
arena: the array vanishes off block `c`. -/
def demoSupported (c : ℕ) (A : List ℕ) : Bool :=
  ((List.range 6).filter (fun w => decide (w ∉ ClusterSynth.demoBlock c))).all
    (fun w => decide (A[w]! = 0))

#guard demoSupported 0 (ClusterSynth.demoClu 0) = true
#guard demoSupported 0 (List.replicate 6 9) = false

-- **The turn is the carrier load, on a supported carrier.** Entering
-- from block `0`'s indicator, the block-driven pair leaves block `1`'s —
-- the same answer `ClusterSynth.loadRun` gives, cell for cell.
#guard refreshRun 0 2 2 5 xm (ClusterSynth.demoClu 0) = ClusterSynth.demoClu 1
#guard refreshRun 0 2 2 5 xm (ClusterSynth.demoClu 0)
  = ClusterSynth.loadRun 6 2 5 xm (ClusterSynth.demoClu 0)

-- …and one turn further, block `1` to block `2`.
#guard refreshRun 2 5 5 6 xm (ClusterSynth.demoClu 1) = ClusterSynth.demoClu 2
#guard refreshRun 2 5 5 6 xm (ClusterSynth.demoClu 1)
  = ClusterSynth.loadRun 6 5 6 xm (ClusterSynth.demoClu 1)

-- …and the readings, written out, so the checks are not circular.
#guard refreshRun 0 2 2 5 xm (ClusterSynth.demoClu 0) = [0, 1, 0, 0, 1, 1]
#guard refreshRun 2 5 5 6 xm (ClusterSynth.demoClu 1) = [0, 0, 1, 0, 0, 0]

/-! ### Negative controls: the pass does not write off its two blocks -/

-- **The clear is the previous block and not the carrier.** Out of a
-- junk carrier the block-driven pair leaves the junk standing at `2` —
-- a member of neither block — where the carrier fill would zero it.
#guard refreshRun 0 2 2 5 xm (List.replicate 6 9) = [0, 1, 9, 0, 1, 1]
#guard (refreshRun 0 2 2 5 xm (List.replicate 6 9))[2]! = 9
#guard refreshRun 0 2 2 5 xm (List.replicate 6 9)
  ≠ ClusterSynth.loadRun 6 2 5 xm (List.replicate 6 9)

-- **…and they agree on the block.** The difference above is *only* off
-- the two blocks: on block `1`'s own members the two passes are equal.
#guard (ClusterSynth.demoBlock 1).all (fun w =>
  decide ((refreshRun 0 2 2 5 xm (List.replicate 6 9))[w]!
    = (ClusterSynth.loadRun 6 2 5 xm (List.replicate 6 9))[w]!)) = true

-- **An empty previous block clears nothing.** `p₁ = e₁` is the `.skip`
-- of the clear, and a pass that ran one turn anyway would be caught.
#guard refreshRun 3 3 2 5 xm (List.replicate 6 9) = [9, 1, 9, 9, 1, 1]

/-! ### The mask passes, block-driven -/

def demoAlv : List ℕ := [1, 1, 0, 1, 1, 1]

def demoBat : List ℕ := [0, 1, 0, 0, 0, 1]

-- **The block-driven and-pass is the carrier and-pass on the block.**
-- Block `1` is `{5, 1, 4}`; the two answers agree there.
#guard (ClusterSynth.demoBlock 1).all (fun w =>
  decide ((bmRun 2 5 ClusterSynth.andG xm demoAlv (ClusterSynth.demoClu 1)
      (List.replicate 6 0))[w]!
    = (ClusterSynth.binRun 6 ClusterSynth.andG demoAlv (ClusterSynth.demoClu 1)
        (List.replicate 6 0))[w]!)) = true

-- …and the reading, written out.
#guard bmRun 2 5 ClusterSynth.andG xm demoAlv (ClusterSynth.demoClu 1) (List.replicate 6 0)
  = [0, 1, 0, 0, 1, 1]

-- **The block-driven sub-pass**, likewise: the cluster with the batch
-- killed, on the block's own cells.
#guard bmRun 2 5 ClusterSynth.subG xm (ClusterSynth.demoClu 1) demoBat (List.replicate 6 0)
  = [0, 0, 0, 0, 1, 0]

-- **The two are not each other** on this data.
#guard bmRun 2 5 ClusterSynth.andG xm (ClusterSynth.demoClu 1) demoBat (List.replicate 6 0)
  ≠ bmRun 2 5 ClusterSynth.subG xm (ClusterSynth.demoClu 1) demoBat (List.replicate 6 0)

/-! ### Negative controls -/

-- **The write is indirect.** A pass storing at the pointer rather than
-- at `xm[p]` would write cells `{2, 3, 4}`; this one writes `{5, 1, 4}`.
#guard (bmRun 2 5 ClusterSynth.andG xm demoAlv (ClusterSynth.demoClu 1)
  (List.replicate 6 7))[3]! = 7
#guard (bmRun 2 5 ClusterSynth.andG xm demoAlv (ClusterSynth.demoClu 1)
  (List.replicate 6 7))[2]! = 7

-- **…so it is not the carrier pass off the block.** On a junk entry
-- array the two differ at every cell no member names — `0`, `2`, `3`.
#guard bmRun 2 5 ClusterSynth.andG xm demoAlv (ClusterSynth.demoClu 1) (List.replicate 6 7)
  ≠ ClusterSynth.binRun 6 ClusterSynth.andG demoAlv (ClusterSynth.demoClu 1)
      (List.replicate 6 7)
#guard bmRun 2 5 ClusterSynth.andG xm demoAlv (ClusterSynth.demoClu 1) (List.replicate 6 7)
  = [7, 1, 7, 7, 1, 1]

-- **An empty block writes nothing.**
#guard bmRun 3 3 ClusterSynth.andG xm demoAlv (ClusterSynth.demoClu 1) (List.replicate 6 7)
  = List.replicate 6 7

-- **The self-reading pass agrees with the frame-reading one at the
-- entry array** — 2F/D-c at a block-driven pass.
#guard bmSelfRun 2 5 ClusterSynth.andG xm demoAlv (ClusterSynth.demoClu 1)
  = bmRun 2 5 ClusterSynth.andG xm (ClusterSynth.demoClu 1) demoAlv (ClusterSynth.demoClu 1)

-- **…but only when the block is injective (B4c/D-c).** A slot list that
-- names cell `1` twice makes the self-reading pass apply `g` twice, and
-- the two answers separate; the frame-reading pass is unmoved.
#guard bmSelfRun 0 2 ClusterSynth.andG [1, 1] [0, 2, 0, 0, 0, 0] [0, 3, 0, 0, 0, 0]
  = [0, 12, 0, 0, 0, 0]
#guard bmSelfRun 0 2 ClusterSynth.andG [1, 1] [0, 2, 0, 0, 0, 0] [0, 3, 0, 0, 0, 0]
  ≠ bmRun 0 2 ClusterSynth.andG [1, 1] [0, 3, 0, 0, 0, 0] [0, 2, 0, 0, 0, 0]
      [0, 3, 0, 0, 0, 0]
#guard bmRun 0 2 ClusterSynth.andG [1, 1] [0, 3, 0, 0, 0, 0] [0, 2, 0, 0, 0, 0]
    [0, 3, 0, 0, 0, 0]
  = [0, 6, 0, 0, 0, 0]

end Twin

/-! ## 2. The turn's clear and load — the `Θ(n)` fill removed

`RamDriver.clusterLoad j` is `fillCom (cluName j) 0` then the block
scan, and 2F/D-a is that the fill is `12·n` **per cluster**. The pass
below replaces the fill by the *previous* turn's block scan at the
stored value `0`: the same program `ClusterSynth.scatPass`, the same
synthesis, one cell pinned differently — and a cost in which `n` does
not appear.

Two clauses carry it. `Supported` is what the caller owes and what the
pass gives back (B4c/D-a), and the no-write clause is what makes the
composition legal at all (B4c/D-b). -/

section Load

/-- **The array vanishes off the block** — the turn invariant's negative
half, and the precondition the swap-in needs. -/
def Supported (p₀ e : ℕ) (idx A : List ℕ) : Prop :=
  ∀ w, (∀ q, p₀ ≤ q → q < e → idx[q]! ≠ w) → A[w]! = 0

/-- **The array is the block's indicator**: every member marked, and
nothing else touched. -/
def MarksBlock (p₀ e : ℕ) (idx A : List ℕ) : Prop :=
  (∀ q, p₀ ≤ q → q < e → A[idx[q]!]! = 1) ∧ Supported p₀ e idx A

/-- **One block-driven scatter pass with its row load**: read the
block's two offsets — three IR operations, 2F/D-b — and scan it, storing
`v` at every member. At `v = 1` this is `RamDriver.clusterLoad j`
*without* its fill; at `v = 0` it is the block-driven clear the fill is
replaced by. One program, two stored values. -/
noncomputable def rowScat (v cc : ℕ) (xoff idx A₀ : List ℕ) : NRest FS ECost :=
  bindT (mopAget xoff cc) fun p₀ =>
    bindT (mopBinop .add cc 1) fun c₁ =>
      bindT (mopAget xoff c₁) fun e =>
        bindT (mopPair A₀ p₀) fun st => ClusterSynth.scatPass e v idx st

/-- Its price: the row load and the block's own slots. -/
def rowScatC (m : ℕ) : ACost String ℕ :=
  cu Currency.aget +
    (cu Currency.add +
      (cu Currency.aget +
        (cu Currency.skip + (m • iter ClusterSynth.scatC + cu Currency.«while»))))

/-- **One block-driven scatter pass, bounded.** Both halves of the
postcondition are the block's: what it writes, and what it leaves alone
(B4c/D-b). The cost's only argument is the block's size. -/
theorem rowScat_le {v cc L : ℕ} {xoff idx A₀ : List ℕ} (hA : A₀.length = L)
    (hc : cc + 1 < xoff.length) (hpe : xoff[cc]! ≤ xoff[cc + 1]!)
    (he : xoff[cc + 1]! ≤ idx.length) (hlt : ∀ q, q < xoff[cc + 1]! → idx[q]! < L) :
    rowScat v cc xoff idx A₀
      ≤ NRest.spec
          (fun t : FS => t.1.length = L ∧
            (∀ q, xoff[cc]! ≤ q → q < xoff[cc + 1]! → t.1[idx[q]!]! = v) ∧
            (∀ w, (∀ q, xoff[cc]! ≤ q → q < xoff[cc + 1]! → idx[q]! ≠ w) → t.1[w]! = A₀[w]!))
          (fun _ => liftACost (rowScatC (xoff[cc + 1]! - xoff[cc]!))) := by
  have hcl : cc < xoff.length := by omega
  rw [rowScatC, rowScat, liftACost_add]
  refine le_trans (NRest.bindT_mono (ClusterSynth.mopAget_le hcl) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro p₀ rfl
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (ClusterSynth.mopAdd_le cc 1) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro c₁ rfl
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (ClusterSynth.mopAget_le hc) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro e rfl
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (ClusterSynth.mopPair_le A₀ xoff[cc]!) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro st rfl
  exact ClusterSynth.scatPass_spec hA hpe he hlt

/-- **The turn's clear and load, abstractly**: the previous turn's block
zeroed, then this turn's marked. The carrier is never mentioned. -/
noncomputable def blockLoad0 (cp c : ℕ) (xoff idx A₀ : List ℕ) : NRest FS ECost :=
  bindT (rowScat 0 cp xoff idx A₀) fun s => rowScat 1 c xoff idx s.1

/-- **The pass's price**: the two blocks' sizes, and nothing else. -/
def blockLoadC (m₁ m : ℕ) : ACost String ℕ := rowScatC m₁ + rowScatC m

/-- **The turn's clear and load, bounded.** The postcondition is the
turn invariant at *this* block (`MarksBlock`) together with the no-write
clause of B4c/D-b, and the cost is the two blocks' own sizes — the
carrier occurs nowhere in `blockLoadC`. -/
theorem blockLoad0_le {cp c L : ℕ} {xoff idx A₀ : List ℕ} (hA : A₀.length = L)
    (hcp : cp + 1 < xoff.length) (hc : c + 1 < xoff.length)
    (hpe₁ : xoff[cp]! ≤ xoff[cp + 1]!) (he₁ : xoff[cp + 1]! ≤ idx.length)
    (hlt₁ : ∀ q, q < xoff[cp + 1]! → idx[q]! < L)
    (hpe : xoff[c]! ≤ xoff[c + 1]!) (he : xoff[c + 1]! ≤ idx.length)
    (hlt : ∀ q, q < xoff[c + 1]! → idx[q]! < L)
    (hsupp : Supported xoff[cp]! xoff[cp + 1]! idx A₀) :
    blockLoad0 cp c xoff idx A₀
      ≤ NRest.spec
          (fun t : FS => t.1.length = L ∧
            MarksBlock xoff[c]! xoff[c + 1]! idx t.1 ∧
            (∀ w, (∀ q, xoff[cp]! ≤ q → q < xoff[cp + 1]! → idx[q]! ≠ w) →
              (∀ q, xoff[c]! ≤ q → q < xoff[c + 1]! → idx[q]! ≠ w) → t.1[w]! = A₀[w]!))
          (fun _ => liftACost (blockLoadC (xoff[cp + 1]! - xoff[cp]!)
            (xoff[c + 1]! - xoff[c]!))) := by
  classical
  rw [blockLoadC, blockLoad0, liftACost_add]
  refine le_trans (NRest.bindT_mono
    (rowScat_le (v := 0) hA hcp hpe₁ he₁ hlt₁) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro s ⟨hs1, hs2, hs3⟩
  refine le_trans (rowScat_le (v := 1) (A₀ := s.1) hs1 hc hpe he hlt)
    (spec_mono ?_ (fun _ _ => le_rfl))
  rintro t ⟨t1, t2, t3⟩
  refine ⟨t1, ⟨t2, fun w hw => ?_⟩, fun w hw₁ hw => ?_⟩
  · rw [t3 w hw]
    by_cases hp : ∀ q, xoff[cp]! ≤ q → q < xoff[cp + 1]! → idx[q]! ≠ w
    · rw [hs3 w hp]; exact hsupp w hp
    · obtain ⟨q, hq1, hq2, hq3⟩ : ∃ q, xoff[cp]! ≤ q ∧ q < xoff[cp + 1]! ∧ idx[q]! = w := by
        by_contra hcon
        exact hp fun q h1 h2 h3 => hcon ⟨q, h1, h2, h3⟩
      rw [← hq3]; exact hs2 q hq1 hq2
  · rw [t3 w hw, hs3 w hw₁]

/-! ### The pass's cost, cashed -/

/-- The clear-and-load's cost in IMP+ time units: fifteen per cell of
**either block**, and thirty for the two row loads and the two loop
exits. The carrier is not an argument. -/
def blockLoadK (m₁ m : ℕ) : ℕ := 15 * m₁ + 15 * m + 30

theorem cash_rowScatC (m : ℕ) : Codegen.cash (rowScatC m) = 15 * m + 15 := by
  rw [rowScatC]
  simp only [Codegen.cash_add, BfsQSynth.cash_nsmul, ClusterSynth.cash_scatC,
    OrderSynth.cash_while, ClusterSynth.cash_aget, ClusterSynth.cash_add,
    ClusterSynth.cash_skip]
  ring

theorem cash_blockLoadC (m₁ m : ℕ) :
    Codegen.cash (blockLoadC m₁ m) = blockLoadK m₁ m := by
  rw [blockLoadC, blockLoadK, Codegen.cash_add, cash_rowScatC, cash_rowScatC]
  ring

/-! ### The pass, synthesized

`rowScat` goes through the tool at a **general** stored value `v`, so
one synthesis is both halves of `blockLoad0`: the clear is the program
below with `"sv"` pinned to `0` and the load is the same program with
`"sv"` pinned to `1`.

**B4c/D-e — a general stored value keeps the increment off `"sv"`.**
2F/D-e recorded that at `v := 1` the frame matcher hands the pointer
bump the *first* cell of the context holding `1`, which in `loadSynth`
was `"sv"` and not `"one"`. At a general `v` that cannot happen — `"sv"`
holds a variable — so the program below reads `"one"` for the bump and
`"sv"` only for the store. That is what makes it instantiable at both
values, and it is why the composed `blockLoad0` needs *two* owned
constant cells and not one. -/

set_option maxHeartbeats 1000000 in
sepref_synth rowScatSynth (v cc : ℕ) (xoff idx A₀ : List ℕ) :
  hnRefine (hnCtxt arrayAssn A₀ "clu" ∗
      hnCtxt arrayAssn xoff "xof" ∗ hnCtxt natAssn cc "cur" ∗
      hnCtxt arrayAssn idx "xmm" ∗ hnCtxt natAssn v "sv" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "p" ∗ junkCell "ct" ∗ junkCell "pend" ∗ junkCell "cw")
    _ _ ("clu", "p") (arrayAssn ×ₐ natAssn)
    (rowScat v cc xoff idx A₀)

-- **The pass, pinned**: the row load's three instructions (2F/D-b) and
-- the block scan, with `"sv"` stored and `"one"` added (B4c/D-e).
#guard rowScatSynth_impl =
  (Com.aget "p" "xof" "cur").seq
    ((Com.binop Lax13Proofs.Imp.Bop.add "ct" "cur" "one").seq
      ((Com.aget "pend" "xof" "ct").seq
        (Com.skip.seq
          (Com.while (Cond.lt (Operand.cell "p") (Operand.cell "pend"))
            ((Com.aget "cw" "xmm" "p").seq
              ((Com.aset "clu" "cw" "sv").seq
                ((Com.binop Lax13Proofs.Imp.Bop.add "p" "p" "one").seq Com.skip)))))))

-- **There is no carrier loop in it.** `RamDriver.clusterLoad`'s program
-- is this one with `ClusterSynth.loadSynth_impl`'s fill in front, and
-- the fill is the only `while` whose bound is `"cln"`; the pass below
-- has one loop and its bound is the block's own end.
#guard rowScatSynth_impl ≠ ClusterSynth.loadSynth_impl

/-- The pass's synthesis with the frame the tool computed left
existential — the form a consumer composes with. -/
theorem rowScatSynth' (v cc : ℕ) (xoff idx A₀ : List ℕ) :
    ∃ Γ', hnRefine (hnCtxt arrayAssn A₀ "clu" ∗
        hnCtxt arrayAssn xoff "xof" ∗ hnCtxt natAssn cc "cur" ∗
        hnCtxt arrayAssn idx "xmm" ∗ hnCtxt natAssn v "sv" ∗ hnCtxt natAssn 1 "one" ∗
        junkCell "p" ∗ junkCell "ct" ∗ junkCell "pend" ∗ junkCell "cw")
      rowScatSynth_impl Γ' ("clu", "p") (arrayAssn ×ₐ natAssn) (rowScat v cc xoff idx A₀) :=
  ⟨_, rowScatSynth v cc xoff idx A₀⟩

/-! ### Gate — the synthesized pass, run, and the turn composed in the
evaluator

`Ir/Semantics.lean`'s evaluator on the program above, twice: once with
`"sv"` at `0` over the previous centre and once with `"sv"` at `1` over
this one, the second starting from the first's array. That **is**
`blockLoad0`, run — and it is what the twins of §1 are checked against. -/

def rState (v cc : ℕ) (A : List ℕ) : Ir.State :=
  Ir.State.ofPairs [("cur", cc), ("sv", v), ("one", 1), ("p", 0), ("ct", 0), ("pend", 0),
      ("cw", 0)]
    [("clu", A), ("xof", ClusterSynth.demoXoff), ("xmm", xm)]

def rRun (v cc : ℕ) (A : List ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 rowScatSynth_impl (rState v cc A)).bind fun p => p.1.arrs "clu"

/-- The turn, composed in the evaluator: the clear at `cp`, then the
load at `c`. -/
def tRun (cp c : ℕ) (A : List ℕ) : Option (List ℕ) := (rRun 0 cp A).bind (rRun 1 c)

-- **The synthesized turn is the twin**, on a supported carrier and on a
-- junk one.
#guard tRun 0 1 (ClusterSynth.demoClu 0) = some (refreshRun 0 2 2 5 xm (ClusterSynth.demoClu 0))
#guard tRun 0 1 (List.replicate 6 9) = some (refreshRun 0 2 2 5 xm (List.replicate 6 9))

-- …and on a supported carrier it is the carrier load's answer.
#guard tRun 0 1 (ClusterSynth.demoClu 0) = some (ClusterSynth.demoClu 1)
#guard tRun 1 2 (ClusterSynth.demoClu 1) = some (ClusterSynth.demoClu 2)

-- **Negative control: the clear is the previous block.** Out of junk,
-- the synthesized turn leaves cell `2` at `9` where the carrier load
-- zeroes it, so the two programs are different programs.
#guard tRun 0 1 (List.replicate 6 9) = some [0, 1, 9, 0, 1, 1]
/--
error: Expression
  decide (tRun 0 1 (List.replicate 6 9) = ClusterSynth.lRun 1 (List.replicate 6 9))
did not evaluate to `true`
-/
#guard_msgs in
#guard tRun 0 1 (List.replicate 6 9) = ClusterSynth.lRun 1 (List.replicate 6 9)

-- **…and on a supported carrier they agree**, which is B4c/D-a: the
-- carrier fill is redundant exactly when the invariant holds.
#guard tRun 0 1 (ClusterSynth.demoClu 0) = ClusterSynth.lRun 1 (ClusterSynth.demoClu 0)

end Load

/-! ## 3. The block-driven mask passes

D3, D8, D9, C1 and their self-reading pair D7d, D10 — `ClusterSynth`
§§4–5 at a loop whose turns are the block's slots. The cell function is
unchanged; what changes is that the index is read out of the slot list
first and every array is then indexed **at the member**, which is one
`aget` more per turn and `n − m` turns fewer per pass.

The loop is proved once (§3.2) at an abstract body and cell function,
exactly as `ClusterSynth.binLoop_le` is, and §§3.3–3.4 supply the four
bodies. -/

section BMask

/-! ### 3.1 The passes' range conditions, guard and invariant -/

/-- What one slot of a frame-reading block-driven mask pass needs in
range: the pointer names a member, and the member is a cell of all three
arrays. -/
def bmP (idx a b : List ℕ) : FS → Prop := fun s =>
  s.2 < idx.length ∧ idx[s.2]! < a.length ∧ idx[s.2]! < b.length ∧ idx[s.2]! < s.1.length

/-- …and of a self-reading one (2F/D-c): the destination is the first
source, so there are three bounds and not four. -/
def bmSelfP (idx b : List ℕ) : FS → Prop := fun s =>
  s.2 < idx.length ∧ idx[s.2]! < b.length ∧ idx[s.2]! < s.1.length

/-- The passes' guard — the block's own end, a runtime number. -/
def bmBf (e : ℕ) : FS → Bool := fun s => decide (s.2 < e)

/-- The block-driven mask passes' invariant. The compacted loop carries
its length (`e ≤ idx.length`, B3's defect 1) and the array is read two
ways: every member already passed holds the cell function's value, and
every cell no passed member names is the caller's. -/
def bmI (p₀ e L : ℕ) (g : ℕ → ℕ → ℕ) (idx a b A₀ : List ℕ) : FS → Prop := fun s =>
  s.1.length = L ∧ p₀ ≤ s.2 ∧ s.2 ≤ e ∧ e ≤ idx.length ∧
    (∀ q, q < e → idx[q]! < L) ∧ (∀ q, q < e → idx[q]! < a.length) ∧
    (∀ q, q < e → idx[q]! < b.length) ∧
    (∀ q, p₀ ≤ q → q < s.2 → s.1[idx[q]!]! = g a[idx[q]!]! b[idx[q]!]!) ∧
    (∀ w, (∀ q, p₀ ≤ q → q < s.2 → idx[q]! ≠ w) → s.1[w]! = A₀[w]!)

theorem bmI_range {p₀ e L : ℕ} {g : ℕ → ℕ → ℕ} {idx a b A₀ : List ℕ} {s : FS}
    (hI : bmI p₀ e L g idx a b A₀ s) (hb : bmBf e s = true) : bmP idx a b s := by
  obtain ⟨h1, -, -, h4, h5, h6, h7, -, -⟩ := hI
  have hi : s.2 < e := by simpa [bmBf] using hb
  exact ⟨by omega, h6 _ hi, h7 _ hi, by rw [h1]; exact h5 _ hi⟩

theorem bmI_selfRange {p₀ e L : ℕ} {g : ℕ → ℕ → ℕ} {idx a b A₀ : List ℕ} {s : FS}
    (hI : bmI p₀ e L g idx a b A₀ s) (hb : bmBf e s = true) : bmSelfP idx b s := by
  obtain ⟨h1, -, -, h4, h5, -, h7, -, -⟩ := hI
  have hi : s.2 < e := by simpa [bmBf] using hb
  exact ⟨by omega, h7 _ hi, by rw [h1]; exact h5 _ hi⟩

theorem bmI_step {p₀ e L : ℕ} {g : ℕ → ℕ → ℕ} {idx a b A₀ : List ℕ} {s : FS}
    (hI : bmI p₀ e L g idx a b A₀ s) (hb : bmBf e s = true) :
    bmI p₀ e L g idx a b A₀ (bmTw g idx a b s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hI
  have hi : s.2 < e := by simpa [bmBf] using hb
  have hd : idx[s.2]! < s.1.length := by rw [h1]; exact h5 _ hi
  simp only [bmI, bmTw]
  refine ⟨by simpa using h1, by omega, by omega, h4, h5, h6, h7, ?_, ?_⟩
  · intro q hq hq'
    rw [get!_set _ _ _ _ hd]
    by_cases hh : idx[q]! = idx[s.2]!
    · rw [if_pos hh, hh]
    · rw [if_neg hh]
      have hlt : q < s.2 := by
        by_contra hcon
        have : q = s.2 := by omega
        subst this; exact hh rfl
      exact h8 q hq hlt
  · intro w hw
    rw [get!_set _ _ _ _ hd, if_neg (fun hcon => hw s.2 (by omega) (by omega) hcon.symm)]
    exact h9 w fun q hq hq' => hw q hq (by omega)

/-- **The self-reading step is the frame-reading step at the entry
array** — but only because the block is injective (B4c/D-c). The cell
the step is about is the member at the pointer, and injectivity is what
says no earlier slot of the block already wrote it. -/
theorem bmSelfTw_eq {p₀ e L : ℕ} {g : ℕ → ℕ → ℕ} {idx b A₀ : List ℕ} {s : FS}
    (hI : bmI p₀ e L g idx A₀ b A₀ s) (hb : bmBf e s = true)
    (hinj : ∀ q q', p₀ ≤ q → q < e → p₀ ≤ q' → q' < e → idx[q]! = idx[q']! → q = q') :
    bmSelfTw g idx b s = bmTw g idx A₀ b s := by
  obtain ⟨-, h2, -, -, -, -, -, -, h9⟩ := hI
  have hi : s.2 < e := by simpa [bmBf] using hb
  rw [bmSelfTw, bmTw, h9 idx[s.2]! ?_]
  intro q hq hq' hcon
  have := hinj q s.2 hq (by omega) (by omega) hi hcon
  omega

/-! ### 3.2 The loop, once -/

theorem bmLoop_le {p₀ e L : ℕ} {g : ℕ → ℕ → ℕ} {idx a b A₀ : List ℕ} {P : FS → Prop}
    {f : FS → NRest FS ECost} {C : ACost String ℕ}
    (hP : ∀ s, bmI p₀ e L g idx a b A₀ s → bmBf e s = true → P s)
    (hf : ∀ s, bmI p₀ e L g idx a b A₀ s → bmBf e s = true →
      f s ≤ NRest.consume (NRest.returnT (bmTw g idx a b s)) (liftACost C)) :
    ∀ (fuel : ℕ) (s : FS), bmI p₀ e L g idx a b A₀ s → e - s.2 < fuel →
      irWhileIT (fun t => bmBf e t = true → P t) (bmBf e) f s
        ≤ NRest.spec (fun t => bmI p₀ e L g idx a b A₀ t ∧ bmBf e t = false)
            (fun _ => liftACost ((e - s.2) • iter C + cu Currency.«while»)) :=
  while_pot_le (P := P) (V := fun s => e - s.2)
    (Φ := fun s => (e - s.2) • iter C) (Φ' := fun s => (e - (s.2 + 1)) • iter C)
    (C := fun _ => C) hP
    (fun s h hb => by
      have hi : s.2 < e := by simpa [bmBf] using hb
      exact step_spec (s := s) (x := bmTw g idx a b s) (C := fun _ => C)
        (Φ := fun s => (e - s.2) • iter C) (Φ' := fun s => (e - (s.2 + 1)) • iter C)
        (V := fun s => e - s.2) (hf s h hb) (bmI_step h hb)
        (by show e - (s.2 + 1) < e - s.2; omega) le_rfl)
    (fun s _ hb => by
      have hi : s.2 < e := by simpa [bmBf] using hb
      show iter C + (e - (s.2 + 1)) • iter C ≤ (e - s.2) • iter C
      rw [show e - s.2 = (e - (s.2 + 1)) + 1 by omega, succ_nsmul]
      exact le_of_eq (by ac_rfl))

/-- The exit of every export below: the pointer has reached the block's
end, so the invariant's two halves are the postcondition. -/
theorem bmI_exit {p₀ e L : ℕ} {g : ℕ → ℕ → ℕ} {idx a b A₀ : List ℕ} {t : FS}
    (hI : bmI p₀ e L g idx a b A₀ t) (hbf : bmBf e t = false) :
    t.1.length = L ∧ (∀ q, p₀ ≤ q → q < e → t.1[idx[q]!]! = g a[idx[q]!]! b[idx[q]!]!) ∧
      (∀ w, (∀ q, p₀ ≤ q → q < e → idx[q]! ≠ w) → t.1[w]! = A₀[w]!) := by
  obtain ⟨h1, -, h3, -, -, -, -, h8, h9⟩ := hI
  have hte : t.2 = e := by
    have : ¬ t.2 < e := by simpa [bmBf] using hbf
    omega
  subst hte
  exact ⟨h1, h8, h9⟩

/-! ### 3.3 The two frame-reading block-driven mask passes -/

/-- **One slot of the block-driven and-pass**: the member, the two
sources at the member, the product, the write. -/
noncomputable def bandF (idx a b : List ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAget idx s.2) fun w =>
    bindT (mopAget a w) fun x =>
      bindT (mopAget b w) fun y =>
        bindT (mopBinop .mul x y) fun z =>
          bindT (mopAset s.1 w z) fun A =>
            bindT (mopSucc s.2) fun p => mopPair A p

/-- **One slot of the block-driven sub-pass**: the complement more, its
`1` in the entry store's pinned cell (2F/D-d). -/
noncomputable def bsubF (idx a b : List ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAget idx s.2) fun w =>
    bindT (mopAget a w) fun x =>
      bindT (mopAget b w) fun y =>
        bindT (mopBinop .sub 1 y) fun cm =>
          bindT (mopBinop .mul x cm) fun z =>
            bindT (mopAset s.1 w z) fun A =>
              bindT (mopSucc s.2) fun p => mopPair A p

/-- One slot of the and-pass's price: `ClusterSynth.andC` and the member
read. -/
def bandC : ACost String ℕ :=
  cu Currency.aget + cu Currency.aget + cu Currency.aget + cu Currency.mul +
    cu Currency.aset + cu Currency.add + cu Currency.skip

/-- …and of the sub-pass's. -/
def bsubC : ACost String ℕ :=
  cu Currency.aget + cu Currency.aget + cu Currency.aget + cu Currency.sub +
    cu Currency.mul + cu Currency.aset + cu Currency.add + cu Currency.skip

theorem bandF_le (idx a b : List ℕ) (s : FS) (h : bmP idx a b s) :
    bandF idx a b s
      ≤ NRest.consume (NRest.returnT (bmTw ClusterSynth.andG idx a b s)) (liftACost bandC) := by
  refine le_of_eq ?_
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [bandF, bmTw, ClusterSynth.andG, mopAget_def, mopAset_def, mopSucc_eq, mopBinop_def,
    mopPair_def, NRest.assert_pos h0, NRest.assert_pos h1, NRest.assert_pos h2,
    NRest.assert_pos h3, NRest.returnT_bindT,
    NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, Lax13Proofs.Imp.Bop.apply_mul, binopCurrency_add,
    binopCurrency_mul, bandC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

theorem bsubF_le (idx a b : List ℕ) (s : FS) (h : bmP idx a b s) :
    bsubF idx a b s
      ≤ NRest.consume (NRest.returnT (bmTw ClusterSynth.subG idx a b s)) (liftACost bsubC) := by
  refine le_of_eq ?_
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [bsubF, bmTw, ClusterSynth.subG, mopAget_def, mopAset_def, mopSucc_eq, mopBinop_def,
    mopPair_def, NRest.assert_pos h0, NRest.assert_pos h1, NRest.assert_pos h2,
    NRest.assert_pos h3, NRest.returnT_bindT,
    NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, Lax13Proofs.Imp.Bop.apply_mul,
    Lax13Proofs.Imp.Bop.apply_sub, binopCurrency_add, binopCurrency_mul, binopCurrency_sub,
    bsubC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

/-- **The block-driven and-pass.** -/
noncomputable def bandPass (e : ℕ) (idx a b : List ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun s => bmBf e s = true → bmP idx a b s) (bmBf e) (bandF idx a b) s₀

/-- **The block-driven sub-pass.** -/
noncomputable def bsubPass (e : ℕ) (idx a b : List ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun s => bmBf e s = true → bmP idx a b s) (bmBf e) (bsubF idx a b) s₀

/-- **The block-driven and-pass's export.** The value clause is the
block's members and the negative clause is B4c/D-b; the bound is
`e - p₀`, the block's own size. -/
theorem bandPass_spec {p₀ e L : ℕ} {idx a b A₀ : List ℕ} (hA : A₀.length = L) (hp : p₀ ≤ e)
    (he : e ≤ idx.length) (hL : ∀ q, q < e → idx[q]! < L)
    (ha : ∀ q, q < e → idx[q]! < a.length) (hb : ∀ q, q < e → idx[q]! < b.length) :
    bandPass e idx a b (A₀, p₀)
      ≤ NRest.spec
          (fun t : FS => t.1.length = L ∧
            (∀ q, p₀ ≤ q → q < e → t.1[idx[q]!]! = a[idx[q]!]! * b[idx[q]!]!) ∧
            (∀ w, (∀ q, p₀ ≤ q → q < e → idx[q]! ≠ w) → t.1[w]! = A₀[w]!))
          (fun _ => liftACost ((e - p₀) • iter bandC + cu Currency.«while»)) := by
  refine le_trans (bmLoop_le (p₀ := p₀) (e := e) (L := L) (g := ClusterSynth.andG) (idx := idx)
      (a := a) (b := b) (A₀ := A₀) (P := bmP idx a b) (C := bandC)
      (fun _ h hb' => bmI_range h hb') (fun s h hb' => bandF_le idx a b s (bmI_range h hb'))
      (e + 1) (A₀, p₀)
      ⟨hA, le_rfl, hp, he, hL, ha, hb, fun q hq hq' => absurd hq' (by omega), fun w _ => rfl⟩
      (by omega))
    (spec_mono ?_ (fun _ _ => by simp))
  rintro t ⟨hI, hbf⟩
  exact bmI_exit hI hbf

/-- **The block-driven sub-pass's export.** -/
theorem bsubPass_spec {p₀ e L : ℕ} {idx a b A₀ : List ℕ} (hA : A₀.length = L) (hp : p₀ ≤ e)
    (he : e ≤ idx.length) (hL : ∀ q, q < e → idx[q]! < L)
    (ha : ∀ q, q < e → idx[q]! < a.length) (hb : ∀ q, q < e → idx[q]! < b.length) :
    bsubPass e idx a b (A₀, p₀)
      ≤ NRest.spec
          (fun t : FS => t.1.length = L ∧
            (∀ q, p₀ ≤ q → q < e → t.1[idx[q]!]! = a[idx[q]!]! * (1 - b[idx[q]!]!)) ∧
            (∀ w, (∀ q, p₀ ≤ q → q < e → idx[q]! ≠ w) → t.1[w]! = A₀[w]!))
          (fun _ => liftACost ((e - p₀) • iter bsubC + cu Currency.«while»)) := by
  refine le_trans (bmLoop_le (p₀ := p₀) (e := e) (L := L) (g := ClusterSynth.subG) (idx := idx)
      (a := a) (b := b) (A₀ := A₀) (P := bmP idx a b) (C := bsubC)
      (fun _ h hb' => bmI_range h hb') (fun s h hb' => bsubF_le idx a b s (bmI_range h hb'))
      (e + 1) (A₀, p₀)
      ⟨hA, le_rfl, hp, he, hL, ha, hb, fun q hq hq' => absurd hq' (by omega), fun w _ => rfl⟩
      (by omega))
    (spec_mono ?_ (fun _ _ => by simp))
  rintro t ⟨hI, hbf⟩
  exact bmI_exit hI hbf

/-! ### 3.4 The two self-reading block-driven mask passes -/

/-- **One slot of the self-reading block-driven and-pass.** -/
noncomputable def bandSelfF (idx b : List ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAget idx s.2) fun w =>
    bindT (mopAget s.1 w) fun x =>
      bindT (mopAget b w) fun y =>
        bindT (mopBinop .mul x y) fun z =>
          bindT (mopAset s.1 w z) fun A =>
            bindT (mopSucc s.2) fun p => mopPair A p

/-- **One slot of the self-reading block-driven sub-pass.** -/
noncomputable def bsubSelfF (idx b : List ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAget idx s.2) fun w =>
    bindT (mopAget s.1 w) fun x =>
      bindT (mopAget b w) fun y =>
        bindT (mopBinop .sub 1 y) fun cm =>
          bindT (mopBinop .mul x cm) fun z =>
            bindT (mopAset s.1 w z) fun A =>
              bindT (mopSucc s.2) fun p => mopPair A p

theorem bandSelfF_le (idx b : List ℕ) (s : FS) (h : bmSelfP idx b s) :
    bandSelfF idx b s
      ≤ NRest.consume (NRest.returnT (bmSelfTw ClusterSynth.andG idx b s))
          (liftACost bandC) := by
  refine le_of_eq ?_
  obtain ⟨h0, h2, h3⟩ := h
  simp only [bandSelfF, bmSelfTw, ClusterSynth.andG, mopAget_def, mopAset_def, mopSucc_eq,
    mopBinop_def, mopPair_def, NRest.assert_pos h0, NRest.assert_pos h2, NRest.assert_pos h3,
    NRest.returnT_bindT, NRest.bindT_consume NRest.addSupContinuousB_acost,
    NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, Lax13Proofs.Imp.Bop.apply_mul,
    binopCurrency_add, binopCurrency_mul, bandC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

theorem bsubSelfF_le (idx b : List ℕ) (s : FS) (h : bmSelfP idx b s) :
    bsubSelfF idx b s
      ≤ NRest.consume (NRest.returnT (bmSelfTw ClusterSynth.subG idx b s))
          (liftACost bsubC) := by
  refine le_of_eq ?_
  obtain ⟨h0, h2, h3⟩ := h
  simp only [bsubSelfF, bmSelfTw, ClusterSynth.subG, mopAget_def, mopAset_def, mopSucc_eq,
    mopBinop_def, mopPair_def, NRest.assert_pos h0, NRest.assert_pos h2, NRest.assert_pos h3,
    NRest.returnT_bindT, NRest.bindT_consume NRest.addSupContinuousB_acost,
    NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, Lax13Proofs.Imp.Bop.apply_mul,
    Lax13Proofs.Imp.Bop.apply_sub, binopCurrency_add, binopCurrency_mul, binopCurrency_sub,
    bsubC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

/-- **The self-reading block-driven and-pass.** -/
noncomputable def bandSelfPass (e : ℕ) (idx b : List ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun s => bmBf e s = true → bmSelfP idx b s) (bmBf e) (bandSelfF idx b) s₀

/-- **The self-reading block-driven sub-pass.** -/
noncomputable def bsubSelfPass (e : ℕ) (idx b : List ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun s => bmBf e s = true → bmSelfP idx b s) (bmBf e) (bsubSelfF idx b) s₀

/-- **The self-reading block-driven and-pass's export.** The hypothesis
`hinj` is B4c/D-c and is the wave's own finding: without it the pass
applies its cell function twice at a repeated member, and §1's negative
control exhibits the difference. At every call site it is
`RamCover.CoverOut.block_inj`. -/
theorem bandSelfPass_spec {p₀ e L : ℕ} {idx b A₀ : List ℕ} (hA : A₀.length = L) (hp : p₀ ≤ e)
    (he : e ≤ idx.length) (hL : ∀ q, q < e → idx[q]! < L)
    (hb : ∀ q, q < e → idx[q]! < b.length)
    (hinj : ∀ q q', p₀ ≤ q → q < e → p₀ ≤ q' → q' < e → idx[q]! = idx[q']! → q = q') :
    bandSelfPass e idx b (A₀, p₀)
      ≤ NRest.spec
          (fun t : FS => t.1.length = L ∧
            (∀ q, p₀ ≤ q → q < e → t.1[idx[q]!]! = A₀[idx[q]!]! * b[idx[q]!]!) ∧
            (∀ w, (∀ q, p₀ ≤ q → q < e → idx[q]! ≠ w) → t.1[w]! = A₀[w]!))
          (fun _ => liftACost ((e - p₀) • iter bandC + cu Currency.«while»)) := by
  refine le_trans (bmLoop_le (p₀ := p₀) (e := e) (L := L) (g := ClusterSynth.andG) (idx := idx)
      (a := A₀) (b := b) (A₀ := A₀) (P := bmSelfP idx b) (C := bandC)
      (fun _ h hb' => bmI_selfRange h hb')
      (fun s h hb' => by
        rw [← bmSelfTw_eq h hb' hinj]; exact bandSelfF_le idx b s (bmI_selfRange h hb'))
      (e + 1) (A₀, p₀)
      ⟨hA, le_rfl, hp, he, hL, fun q hq => by rw [hA]; exact hL q hq, hb,
        fun q hq hq' => absurd hq' (by omega), fun w _ => rfl⟩
      (by omega))
    (spec_mono ?_ (fun _ _ => by simp))
  rintro t ⟨hI, hbf⟩
  exact bmI_exit hI hbf

/-- **The self-reading block-driven sub-pass's export.** -/
theorem bsubSelfPass_spec {p₀ e L : ℕ} {idx b A₀ : List ℕ} (hA : A₀.length = L) (hp : p₀ ≤ e)
    (he : e ≤ idx.length) (hL : ∀ q, q < e → idx[q]! < L)
    (hb : ∀ q, q < e → idx[q]! < b.length)
    (hinj : ∀ q q', p₀ ≤ q → q < e → p₀ ≤ q' → q' < e → idx[q]! = idx[q']! → q = q') :
    bsubSelfPass e idx b (A₀, p₀)
      ≤ NRest.spec
          (fun t : FS => t.1.length = L ∧
            (∀ q, p₀ ≤ q → q < e → t.1[idx[q]!]! = A₀[idx[q]!]! * (1 - b[idx[q]!]!)) ∧
            (∀ w, (∀ q, p₀ ≤ q → q < e → idx[q]! ≠ w) → t.1[w]! = A₀[w]!))
          (fun _ => liftACost ((e - p₀) • iter bsubC + cu Currency.«while»)) := by
  refine le_trans (bmLoop_le (p₀ := p₀) (e := e) (L := L) (g := ClusterSynth.subG) (idx := idx)
      (a := A₀) (b := b) (A₀ := A₀) (P := bmSelfP idx b) (C := bsubC)
      (fun _ h hb' => bmI_selfRange h hb')
      (fun s h hb' => by
        rw [← bmSelfTw_eq h hb' hinj]; exact bsubSelfF_le idx b s (bmI_selfRange h hb'))
      (e + 1) (A₀, p₀)
      ⟨hA, le_rfl, hp, he, hL, fun q hq => by rw [hA]; exact hL q hq, hb,
        fun q hq hq' => absurd hq' (by omega), fun w _ => rfl⟩
      (by omega))
    (spec_mono ?_ (fun _ _ => by simp))
  rintro t ⟨hI, hbf⟩
  exact bmI_exit hI hbf

/-! ### 3.5 The block pass **is** the carrier pass, under the invariant

The differential guards of §1 as a theorem: on a carrier where the first
source and the destination are both supported on the block, the
block-driven pass's answer and `ClusterSynth.andPass`'s agree at every
cell of the carrier. Off the block both are `0` — one because it did not
write, the other because it multiplied by a zero — and that is exactly
why the `Θ(n)` pass was redundant. -/

theorem bmask_eq_carrier {p₀ e N : ℕ} {idx a b A₀ Ab Ac : List ℕ}
    (hsa : ∀ w, w < N → (∀ q, p₀ ≤ q → q < e → idx[q]! ≠ w) → a[w]! = 0)
    (hsA : Supported p₀ e idx A₀)
    (hbv : ∀ q, p₀ ≤ q → q < e → Ab[idx[q]!]! = a[idx[q]!]! * b[idx[q]!]!)
    (hbk : ∀ w, (∀ q, p₀ ≤ q → q < e → idx[q]! ≠ w) → Ab[w]! = A₀[w]!)
    (hcv : ∀ j, Ac[j]! = if j < N then a[j]! * b[j]! else A₀[j]!) :
    ∀ w, w < N → Ab[w]! = Ac[w]! := by
  classical
  intro w hw
  rw [hcv w, if_pos hw]
  by_cases hp : ∀ q, p₀ ≤ q → q < e → idx[q]! ≠ w
  · rw [hbk w hp, hsA w hp, hsa w hw hp, Nat.zero_mul]
  · obtain ⟨q, hq1, hq2, hq3⟩ : ∃ q, p₀ ≤ q ∧ q < e ∧ idx[q]! = w := by
      by_contra hcon
      exact hp fun q h1 h2 h3 => hcon ⟨q, h1, h2, h3⟩
    have := hbv q hq1 hq2
    rw [hq3] at this
    exact this

/-! ### 3.6 The four passes, synthesized -/

set_option maxHeartbeats 1000000 in
sepref_synth bandSynth (e : ℕ) (idx a b A₀ : List ℕ) (p₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, p₀) ("cld", "p") ∗
      hnCtxt arrayAssn idx "xmm" ∗ hnCtxt arrayAssn a "cla" ∗ hnCtxt arrayAssn b "clb" ∗
      hnCtxt natAssn e "pend" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "cw" ∗ junkCell "clx" ∗ junkCell "cly" ∗ junkCell "clw")
    _ _ ("cld", "p") (arrayAssn ×ₐ natAssn)
    (bandPass e idx a b (A₀, p₀))

set_option maxHeartbeats 1000000 in
sepref_synth bsubSynth (e : ℕ) (idx a b A₀ : List ℕ) (p₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, p₀) ("cld", "p") ∗
      hnCtxt arrayAssn idx "xmm" ∗ hnCtxt arrayAssn a "cla" ∗ hnCtxt arrayAssn b "clb" ∗
      hnCtxt natAssn e "pend" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "cw" ∗ junkCell "clx" ∗ junkCell "cly" ∗ junkCell "clc" ∗ junkCell "clw")
    _ _ ("cld", "p") (arrayAssn ×ₐ natAssn)
    (bsubPass e idx a b (A₀, p₀))

set_option maxHeartbeats 1000000 in
sepref_synth bandSelfSynth (e : ℕ) (idx b A₀ : List ℕ) (p₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, p₀) ("cld", "p") ∗
      hnCtxt arrayAssn idx "xmm" ∗ hnCtxt arrayAssn b "clb" ∗
      hnCtxt natAssn e "pend" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "cw" ∗ junkCell "clx" ∗ junkCell "cly" ∗ junkCell "clw")
    _ _ ("cld", "p") (arrayAssn ×ₐ natAssn)
    (bandSelfPass e idx b (A₀, p₀))

set_option maxHeartbeats 1000000 in
sepref_synth bsubSelfSynth (e : ℕ) (idx b A₀ : List ℕ) (p₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, p₀) ("cld", "p") ∗
      hnCtxt arrayAssn idx "xmm" ∗ hnCtxt arrayAssn b "clb" ∗
      hnCtxt natAssn e "pend" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "cw" ∗ junkCell "clx" ∗ junkCell "cly" ∗ junkCell "clc" ∗ junkCell "clw")
    _ _ ("cld", "p") (arrayAssn ×ₐ natAssn)
    (bsubSelfPass e idx b (A₀, p₀))

-- **The block-driven and-pass, pinned**: the member read in front, and
-- then `ClusterSynth.andSynth_impl`'s body with `"cw"` in every index
-- position where the carrier pass has its counter.
#guard bandSynth_impl =
  Com.while (Cond.lt (Operand.cell "p") (Operand.cell "pend"))
    ((Com.aget "cw" "xmm" "p").seq
      ((Com.aget "clx" "cla" "cw").seq
        ((Com.aget "cly" "clb" "cw").seq
          ((Com.binop Lax13Proofs.Imp.Bop.mul "clw" "clx" "cly").seq
            ((Com.aset "cld" "cw" "clw").seq
              ((Com.binop Lax13Proofs.Imp.Bop.add "p" "p" "one").seq Com.skip))))))

#guard bsubSynth_impl =
  Com.while (Cond.lt (Operand.cell "p") (Operand.cell "pend"))
    ((Com.aget "cw" "xmm" "p").seq
      ((Com.aget "clx" "cla" "cw").seq
        ((Com.aget "cly" "clb" "cw").seq
          ((Com.binop Lax13Proofs.Imp.Bop.sub "clc" "one" "cly").seq
            ((Com.binop Lax13Proofs.Imp.Bop.mul "clw" "clx" "clc").seq
              ((Com.aset "cld" "cw" "clw").seq
                ((Com.binop Lax13Proofs.Imp.Bop.add "p" "p" "one").seq Com.skip)))))))

-- **The self-reading pair, pinned.** The *only* difference is the array
-- the second `aget` reads — `"cld"`, the destination itself.
#guard bandSelfSynth_impl =
  Com.while (Cond.lt (Operand.cell "p") (Operand.cell "pend"))
    ((Com.aget "cw" "xmm" "p").seq
      ((Com.aget "clx" "cld" "cw").seq
        ((Com.aget "cly" "clb" "cw").seq
          ((Com.binop Lax13Proofs.Imp.Bop.mul "clw" "clx" "cly").seq
            ((Com.aset "cld" "cw" "clw").seq
              ((Com.binop Lax13Proofs.Imp.Bop.add "p" "p" "one").seq Com.skip))))))

#guard bsubSelfSynth_impl =
  Com.while (Cond.lt (Operand.cell "p") (Operand.cell "pend"))
    ((Com.aget "cw" "xmm" "p").seq
      ((Com.aget "clx" "cld" "cw").seq
        ((Com.aget "cly" "clb" "cw").seq
          ((Com.binop Lax13Proofs.Imp.Bop.sub "clc" "one" "cly").seq
            ((Com.binop Lax13Proofs.Imp.Bop.mul "clw" "clx" "clc").seq
              ((Com.aset "cld" "cw" "clw").seq
                ((Com.binop Lax13Proofs.Imp.Bop.add "p" "p" "one").seq Com.skip)))))))

/-! ### Negative controls on the pins -/

-- **The write is at the member and not at the pointer.** The
-- transposition is a different program, and §1's guards refute it on
-- the arena.
#guard bandSynth_impl ≠
  Com.while (Cond.lt (Operand.cell "p") (Operand.cell "pend"))
    ((Com.aget "cw" "xmm" "p").seq
      ((Com.aget "clx" "cla" "cw").seq
        ((Com.aget "cly" "clb" "cw").seq
          ((Com.binop Lax13Proofs.Imp.Bop.mul "clw" "clx" "cly").seq
            ((Com.aset "cld" "p" "clw").seq
              ((Com.binop Lax13Proofs.Imp.Bop.add "p" "p" "one").seq Com.skip))))))

-- **The block passes are not the carrier passes**, as programs: the
-- carrier's loop bound is the carrier's length and its cell expression
-- reads at the counter.
#guard bandSynth_impl ≠ ClusterSynth.andSynth_impl
#guard bsubSynth_impl ≠ ClusterSynth.subSynth_impl
#guard bandSelfSynth_impl ≠ ClusterSynth.andSelfSynth_impl
#guard bsubSelfSynth_impl ≠ ClusterSynth.subSelfSynth_impl

-- **The four are four programs.**
#guard bsubSynth_impl ≠ bandSynth_impl
#guard bandSelfSynth_impl ≠ bandSynth_impl
#guard bsubSelfSynth_impl ≠ bsubSynth_impl

/-! ### 3.7 Gate — the synthesized passes, run -/

def mState (a b A : List ℕ) (p₀ e : ℕ) : Ir.State :=
  Ir.State.ofPairs [("p", p₀), ("pend", e), ("one", 1), ("cw", 0), ("clx", 0), ("cly", 0),
      ("clc", 0), ("clw", 0)]
    [("cld", A), ("cla", a), ("clb", b), ("xmm", xm)]

def baRun (a b A : List ℕ) (p₀ e : ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 bandSynth_impl (mState a b A p₀ e)).bind fun p => p.1.arrs "cld"

def bsRun (a b A : List ℕ) (p₀ e : ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 bsubSynth_impl (mState a b A p₀ e)).bind fun p => p.1.arrs "cld"

def baSelfRun (b A : List ℕ) (p₀ e : ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 bandSelfSynth_impl (mState [] b A p₀ e)).bind fun p => p.1.arrs "cld"

def bsSelfRun (b A : List ℕ) (p₀ e : ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 bsubSelfSynth_impl (mState [] b A p₀ e)).bind fun p => p.1.arrs "cld"

-- **The programs are the twins**, on block `1` of §1's arena.
#guard baRun demoAlv (ClusterSynth.demoClu 1) (List.replicate 6 0) 2 5
  = some (bmRun 2 5 ClusterSynth.andG xm demoAlv (ClusterSynth.demoClu 1) (List.replicate 6 0))
#guard bsRun (ClusterSynth.demoClu 1) demoBat (List.replicate 6 0) 2 5
  = some (bmRun 2 5 ClusterSynth.subG xm (ClusterSynth.demoClu 1) demoBat (List.replicate 6 0))
#guard baSelfRun demoAlv (ClusterSynth.demoClu 1) 2 5
  = some (bmSelfRun 2 5 ClusterSynth.andG xm demoAlv (ClusterSynth.demoClu 1))
#guard bsSelfRun demoBat (ClusterSynth.demoClu 1) 2 5
  = some (bmSelfRun 2 5 ClusterSynth.subG xm demoBat (ClusterSynth.demoClu 1))

-- …and the readings, written out.
#guard baRun demoAlv (ClusterSynth.demoClu 1) (List.replicate 6 0) 2 5 = some [0, 1, 0, 0, 1, 1]
#guard bsRun (ClusterSynth.demoClu 1) demoBat (List.replicate 6 0) 2 5 = some [0, 0, 0, 0, 1, 0]

-- **The pass does not write off its block** (B4c/D-b), in the evaluator:
-- out of a junk destination, cells `0`, `2` and `3` come back untouched.
#guard baRun demoAlv (ClusterSynth.demoClu 1) (List.replicate 6 7) 2 5
  = some [7, 1, 7, 7, 1, 1]

-- **Negative control: it is therefore not the carrier pass** on a
-- carrier the invariant does not hold at.
/--
error: Expression
  decide
    (baRun demoAlv (ClusterSynth.demoClu 1) (List.replicate 6 7) 2 5 =
      ClusterSynth.aRun demoAlv (ClusterSynth.demoClu 1) (List.replicate 6 7))
did not evaluate to `true`
-/
#guard_msgs in
#guard baRun demoAlv (ClusterSynth.demoClu 1) (List.replicate 6 7) 2 5
  = ClusterSynth.aRun demoAlv (ClusterSynth.demoClu 1) (List.replicate 6 7)

-- **…and it *is* the carrier pass where the invariant holds** — the
-- first source and the destination supported on the block. This is
-- `bmask_eq_carrier`, checked.
#guard baRun demoAlv (ClusterSynth.demoClu 1) (List.replicate 6 0) 2 5
  = ClusterSynth.aRun (ClusterSynth.demoClu 1) demoAlv (List.replicate 6 0)

-- **An empty block writes nothing.**
#guard baRun demoAlv (ClusterSynth.demoClu 1) (List.replicate 6 7) 3 3
  = some (List.replicate 6 7)

end BMask

/-! ## 4. The block-driven expansion

`RamDriver.expandCom msk src dst` at a loop whose turns are the block's
members. `ExpandSynth` derived it over the carrier and named the floor
it leaves (2G/D-c, 2G/N-3): `expRowC` is paid at every vertex of the
carrier whether the mask keeps it or not, so a chain of `2·cap`
expansions costs `Θ(cap·n)` per cluster even when the ball is three
vertices. 2G/N-3 said the repair is "expand a list of marked vertices
rather than the carrier"; the list is the turn's member list, and this
is that pass.

The inner block scan is **unchanged** — `ExpandSynth.expScan` and its
`expScan_le` are consumed, not re-proved. What is new is the outer loop,
its two-currency energy (B4c/D-d) and the two clauses of B4c/D-b. -/

section BExp

open Lax3Proofs.Refine.ExpandSynth (PS SS expScan expScanI expScan_le expBf expC expCnt
  expOf expMidC expTailC expRowC expRowCn expRowCn_eq expScanTw hitUpto hitUpto_self
  mopConstN_le)
open Lax3Proofs.Refine.ClusterSynth (mopAget_le mopAdd_le mopPair_le)

/-! ### 4.1 `edges(block)` — the second currency

The carrier pass's slot budget is `off[n] - off[z]`, which telescopes
because the loop counter *is* the vertex. A block-driven loop's vertices
are `idx[p]`, in whatever order the cover wrote them, so the budget is a
**sum** and the telescoping is replaced by
`Finset.sum_eq_sum_Ico_succ_bot`. -/

/-- The number of arena slots the members `idx[a], …, idx[b-1]` own. -/
def degSum (idx off : List ℕ) (a b : ℕ) : ℕ :=
  ∑ q ∈ Finset.Ico a b, (off[idx[q]! + 1]! - off[idx[q]!]!)

theorem degSum_self (idx off : List ℕ) (a : ℕ) : degSum idx off a a = 0 := by
  simp [degSum]

theorem degSum_succ_bot (idx off : List ℕ) {a b : ℕ} (h : a < b) :
    degSum idx off a b = (off[idx[a]! + 1]! - off[idx[a]!]!) + degSum idx off (a + 1) b := by
  rw [degSum, degSum, Finset.sum_eq_sum_Ico_succ_bot h]

/-! ### 4.2 The twin -/

/-- One member of the block-driven expansion, as a function: the member
is read out of the slot list, and then it is `ExpandSynth.expRowTw`'s
body at that vertex. -/
def bexpRowTw (idx off tgt msk src : List ℕ) : PS → PS := fun s =>
  let z := idx[s.2]!
  let c := if 0 < msk[z]! then
      (expScanTw tgt msk src off[z + 1]! (off[z + 1]! - off[z]!) (0, off[z]!)).1
    else 0
  (s.1.set z (if 0 < c then 1 else src[z]!), s.2 + 1)

/-- The pass, run. -/
def bexpRunTw (e : ℕ) (idx off tgt msk src : List ℕ) : ℕ → PS → PS
  | 0, s => s
  | fuel + 1, s =>
    if s.2 < e then bexpRunTw e idx off tgt msk src fuel (bexpRowTw idx off tgt msk src s) else s

/-- One block-driven expansion step. -/
def bexpOnce (p₀ e : ℕ) (idx off tgt msk src A : List ℕ) : List ℕ :=
  (bexpRunTw e idx off tgt msk src (e + 1) (A, p₀)).1

/-! `ExpandSynth`'s arena: the path `0—1—2—3—4—5`. The block is the slot
list `[1, 2, 3]` — three members in the middle of the path, so both the
"not written before the block" and the "not written after it" ends are
observable. -/

/-- The block's slot list. -/
def bidx : List ℕ := [1, 2, 3]

-- **The block-driven pass is the reference expansion, on the block.**
-- `ExpandSynth.refExpand` is read off the edge list and not off the
-- arena.
#guard (bidx.all fun z => decide
  ((bexpOnce 0 3 bidx ExpandSynth.demoOff ExpandSynth.demoTgt ExpandSynth.demoAll
      ExpandSynth.demoSrc (List.replicate 6 0))[z]!
    = (ExpandSynth.refExpand ExpandSynth.demoAll ExpandSynth.demoSrc)[z]!)) = true

-- …and the reading, written out.
#guard bexpOnce 0 3 bidx ExpandSynth.demoOff ExpandSynth.demoTgt ExpandSynth.demoAll
    ExpandSynth.demoSrc (List.replicate 6 0)
  = [0, 1, 0, 0, 0, 0]

/-! #### Negative controls -/

-- **The pass does not write off its block** (B4c/D-b). Out of a junk
-- destination the cells `0`, `4`, `5` — no member of the block — come
-- back untouched, where the carrier pass writes all six.
#guard bexpOnce 0 3 bidx ExpandSynth.demoOff ExpandSynth.demoTgt ExpandSynth.demoAll
    ExpandSynth.demoSrc (List.replicate 6 9)
  = [9, 1, 0, 0, 9, 9]
#guard bexpOnce 0 3 bidx ExpandSynth.demoOff ExpandSynth.demoTgt ExpandSynth.demoAll
    ExpandSynth.demoSrc (List.replicate 6 9)
  ≠ ExpandSynth.expOnce 6 ExpandSynth.demoOff ExpandSynth.demoTgt ExpandSynth.demoAll
      ExpandSynth.demoSrc

-- **…and it agrees with the carrier pass on the block**, which is the
-- other half of the differential test.
#guard (bidx.all fun z => decide
  ((bexpOnce 0 3 bidx ExpandSynth.demoOff ExpandSynth.demoTgt ExpandSynth.demoAll
      ExpandSynth.demoSrc (List.replicate 6 9))[z]!
    = (ExpandSynth.expOnce 6 ExpandSynth.demoOff ExpandSynth.demoTgt ExpandSynth.demoAll
        ExpandSynth.demoSrc)[z]!)) = true

-- **The mask still cuts the arena at both ends of an edge.** With the
-- path cut at `2`, the member `1` no longer reaches it.
#guard bexpOnce 0 3 bidx ExpandSynth.demoOff ExpandSynth.demoTgt ExpandSynth.demoCut
    [0, 1, 0, 0, 0, 0] (List.replicate 6 0)
  = [0, 1, 0, 0, 0, 0]
#guard bexpOnce 0 3 bidx ExpandSynth.demoOff ExpandSynth.demoTgt ExpandSynth.demoAll
    [0, 1, 0, 0, 0, 0] (List.replicate 6 0)
  = [0, 1, 1, 0, 0, 0]

-- **The source's value rides through** at an unexpanded member, which
-- is what `expandVal_eq_or` needs and a "write the indicator" reading
-- would break.
#guard bexpOnce 0 3 bidx ExpandSynth.demoOff ExpandSynth.demoTgt ExpandSynth.demoAll
    [0, 0, 7, 0, 0, 0] (List.replicate 6 0)
  = [0, 1, 7, 1, 0, 0]

-- **An empty block expands nothing.**
#guard bexpOnce 3 3 bidx ExpandSynth.demoOff ExpandSynth.demoTgt ExpandSynth.demoAll
    ExpandSynth.demoSrc (List.replicate 6 9)
  = List.replicate 6 9

/-! ### 4.3 One member of the pass -/

/-- The pass's guard — the block's own end. -/
def bexpBf (e : ℕ) : PS → Bool := fun s => decide (s.2 < e)

/-- What one member needs in range. `n` occurs here, in the *assertion*,
because the arrays are carrier-sized; it occurs in no cost below. -/
def bexpP (n e : ℕ) (idx off tgt msk src : List ℕ) : PS → Prop := fun s =>
  Shape n off tgt msk ∧ src.length = n ∧ s.1.length = n ∧ s.2 < e ∧ e ≤ idx.length ∧
    ∀ q, q < e → idx[q]! < n

/-- **One member of the block-driven expansion.** The member read is the
one instruction the carrier pass does not have; everything after it is
`ExpandSynth.expRowF`'s body at the member instead of at the counter,
and the bump at the end is the **pointer's** and not the vertex's. -/
noncomputable def bexpRowF (idx off tgt msk src : List ℕ) : PS → NRest PS ECost := fun s =>
  bindT (mopAget idx s.2) fun z =>
    bindT (mopAget src z) fun hz =>
      bindT (mopAget msk z) fun mz =>
        bindT (mopConstN 0) fun c₀ =>
          bindT (irIf (decide (0 < mz))
              (bindT (mopAget off z) fun j0 =>
                bindT (mopBinop .add z 1) fun zp =>
                  bindT (mopAget off zp) fun jend =>
                    bindT (mopPair c₀ j0) fun z0 =>
                      bindT (expScan tgt msk src jend z0) fun r => mopKeep r.1)
              (mopKeep c₀)) fun c =>
            bindT (irIf (decide (0 < c)) (mopAset s.1 z 1) (mopAset s.1 z hz)) fun D =>
              bindT (mopSucc s.2) fun p => mopPair D p

/-- One member's account, outside the block scan: `ExpandSynth.expRowC`
and the member read. -/
def bexpRowC : ACost String ℕ := cu Currency.aget + expRowC

/-- …in the nesting the composition produces it in. -/
def bexpRowCn (m : ℕ) : ACost String ℕ := cu Currency.aget + expRowCn m

theorem bexpRowCn_eq (m : ℕ) : bexpRowCn m = bexpRowC + m • iter expC := by
  rw [bexpRowCn, expRowCn_eq, bexpRowC, ← add_assoc]

/-- **The branch that contains the loop**, at a vertex given as a value
rather than as the loop counter. `ExpandSynth`'s `expRowF_le` proves
this inline at `s.2`; the block-driven pass needs it at `idx[s.2]`, so
it is stated once here. -/
theorem bexpMid_le {n : ℕ} {off tgt msk src : List ℕ} (hsh : Shape n off tgt msk)
    (hsrc : src.length = n) {z : ℕ} (hz : z < n) :
    irIf (decide (0 < msk[z]!))
        (bindT (mopAget off z) fun j0 =>
          bindT (mopBinop .add z 1) fun zp =>
            bindT (mopAget off zp) fun jend =>
              bindT (mopPair (0 : ℕ) j0) fun z0 =>
                bindT (expScan tgt msk src jend z0) fun r => mopKeep r.1)
        (mopKeep (0 : ℕ))
      ≤ NRest.spec (fun c : ℕ => c = expCnt off tgt msk src z)
          (fun _ => liftACost (expMidC (off[z + 1]! - off[z]!))) := by
  have holen : off.length = n + 1 := hsh.1
  have h0 : z < off.length := by omega
  have h1 : z + 1 < off.length := by omega
  have hmono : off[z]! ≤ off[z + 1]! := hsh.2.2.1 _ hz
  have hrow : off[z + 1]! ≤ tgt.length := hsh.row_le hz
  by_cases hm : 0 < msk[z]!
  · have hstart : expScanI tgt msk src off[z]! off[z + 1]! (0, off[z]!) :=
      ⟨le_rfl, hmono, (hitUpto_self tgt msk src _).symm⟩
    have hscan := expScan_le hsh hsrc hrow (off[z + 1]! - off[z]! + 1) _ hstart (by omega)
    have hkeep : ∀ r : SS,
        (expScanI tgt msk src off[z]! off[z + 1]! r ∧ expBf off[z + 1]! r = false) →
          mopKeep r.1 ≤ NRest.spec (fun c : ℕ => c = expCnt off tgt msk src z)
            (fun _ => liftACost (cu Currency.add)) := by
      rintro r ⟨⟨hr1, hr2, hr3⟩, hbf⟩
      have hend : r.2 = off[z + 1]! := by
        have : ¬ r.2 < off[z + 1]! := by simpa [expBf] using hbf
        omega
      rw [mopKeep_eq, mopBinop_def, liftACost_cu]
      refine consume_returnT_le_spec ?_ le_rfl
      show Lax13Proofs.Imp.Bop.apply .add r.1 0 = _
      rw [Lax13Proofs.Imp.Bop.apply_add, expCnt, if_pos hm, hr3, hend, Nat.add_zero]
    simp only [irIf_def, decide_eq_true_eq, if_pos hm, mopAget_def, mopBinop_def,
      mopPair_def, NRest.assert_pos h0, Lax13Proofs.Imp.Bop.apply_add, NRest.assert_pos h1,
      NRest.returnT_bindT, NRest.bindT_consume NRest.addSupContinuousB_acost,
      NRest.consume_consume, binopCurrency_add, NRest.bindT_assoc_acost]
    refine le_trans (NRest.consume_mono
      (le_trans (NRest.bindT_mono hscan fun _ => le_rfl)
        (bindT_spec_le _ _ _ _ _ hkeep)) le_rfl) (le_of_eq ?_)
    rw [Sepref.consume_spec]
    refine congrArg (NRest.spec _) (funext fun _ => ?_)
    simp only [expMidC, iter, liftACost_add, liftACost_nsmul, liftACost_cu]
    ac_rfl
  · simp only [irIf_def, decide_eq_true_eq, if_neg hm, mopKeep_eq, mopBinop_def,
      NRest.consume_consume]
    refine consume_returnT_le_spec ?_ ?_
    · show Lax13Proofs.Imp.Bop.apply .add 0 0 = _
      rw [Lax13Proofs.Imp.Bop.apply_add, expCnt, if_neg hm]
    · rw [expMidC, liftACost_add, liftACost_add]
      refine le_trans (le_of_eq ?_) (cost_le_add _ _)
      simp only [binopCurrency_add, liftACost_cu]

/-- **One member of the pass, walked.** -/
theorem bexpRowF_le {n e : ℕ} {idx off tgt msk src : List ℕ} (hsh : Shape n off tgt msk)
    (hsrc : src.length = n) (he : e ≤ idx.length) (hidx : ∀ q, q < e → idx[q]! < n)
    (s : PS) (hlen : s.1.length = n) (hi : s.2 < e) :
    bexpRowF idx off tgt msk src s
      ≤ NRest.spec
          (fun t : PS => t.1.length = n ∧ t.2 = s.2 + 1 ∧
            (∀ v, v ≠ idx[s.2]! → t.1[v]! = s.1[v]!) ∧
            t.1[idx[s.2]!]! = expOf off tgt msk src idx[s.2]!)
          (fun _ => liftACost (bexpRowC
            + (off[idx[s.2]! + 1]! - off[idx[s.2]!]!) • iter expC)) := by
  have hp : s.2 < idx.length := by omega
  have hz : idx[s.2]! < n := hidx _ hi
  have hsz : idx[s.2]! < src.length := by omega
  have hmz : idx[s.2]! < msk.length := by rw [hsh.2.1]; exact hz
  have hdz : idx[s.2]! < s.1.length := by omega
  -- the branch that writes the cell, and the pointer bump
  have htail :
      NRest.bindT (irIf (decide (0 < expCnt off tgt msk src idx[s.2]!))
            (mopAset s.1 idx[s.2]! 1) (mopAset s.1 idx[s.2]! src[idx[s.2]!]!))
          (fun D => NRest.bindT (mopSucc s.2) fun p => mopPair D p)
        ≤ NRest.spec
            (fun t : PS => t.1.length = n ∧ t.2 = s.2 + 1 ∧
              (∀ v, v ≠ idx[s.2]! → t.1[v]! = s.1[v]!) ∧
              t.1[idx[s.2]!]! = expOf off tgt msk src idx[s.2]!)
            (fun _ => liftACost expTailC) := by
    by_cases hc : 0 < expCnt off tgt msk src idx[s.2]!
    · simp only [irIf_def, decide_eq_true_eq, if_pos hc]
      simp only [mopAset_def, mopSucc_eq, mopBinop_def, mopPair_def,
        NRest.assert_pos hdz, NRest.returnT_bindT,
        NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
        Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add]
      refine consume_returnT_le_spec ⟨by simp [hlen], rfl, ?_, ?_⟩ ?_
      · intro v hv
        show (s.1.set idx[s.2]! 1)[v]! = _
        rw [get!_set _ _ _ _ hdz, if_neg hv]
      · show (s.1.set idx[s.2]! 1)[idx[s.2]!]! = _
        rw [get!_set _ _ _ _ hdz, if_pos rfl, expOf, if_pos hc]
      · simp only [expTailC, liftACost_add, liftACost_cu]
        exact le_of_eq (by ac_rfl)
    · simp only [irIf_def, decide_eq_true_eq, if_neg hc]
      simp only [mopAset_def, mopSucc_eq, mopBinop_def, mopPair_def,
        NRest.assert_pos hdz, NRest.returnT_bindT,
        NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
        Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add]
      refine consume_returnT_le_spec ⟨by simp [hlen], rfl, ?_, ?_⟩ ?_
      · intro v hv
        show (s.1.set idx[s.2]! src[idx[s.2]!]!)[v]! = _
        rw [get!_set _ _ _ _ hdz, if_neg hv]
      · show (s.1.set idx[s.2]! src[idx[s.2]!]!)[idx[s.2]!]! = _
        rw [get!_set _ _ _ _ hdz, if_pos rfl, expOf, if_neg hc]
      · simp only [expTailC, liftACost_add, liftACost_cu]
        exact le_of_eq (by ac_rfl)
  -- assemble
  rw [← bexpRowCn_eq (off[idx[s.2]! + 1]! - off[idx[s.2]!]!), bexpRowCn, expRowCn, bexpRowF]
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (mopAget_le hp) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro z rfl
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (mopAget_le hsz) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro hzv rfl
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (mopAget_le hmz) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro mz rfl
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (mopConstN_le 0) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro c₀ rfl
  rw [liftACost_add]
  refine le_trans (NRest.bindT_mono (bexpMid_le hsh hsrc hz) (fun _ => le_rfl)) ?_
  refine bindT_spec_le _ _ _ _ _ ?_
  rintro c rfl
  exact htail

/-! ### 4.4 The pass -/

/-- **The block-driven expansion pass.** -/
noncomputable def bexpPass (n e : ℕ) (idx off tgt msk src : List ℕ) (s₀ : PS) :
    NRest PS ECost :=
  irWhileIT (fun s => bexpBf e s = true → bexpP n e idx off tgt msk src s) (bexpBf e)
    (bexpRowF idx off tgt msk src) s₀

/-- The pass's invariant: every member already passed holds `expOf`, and
every cell no passed member names is the caller's. -/
def bexpI (n p₀ e : ℕ) (idx off tgt msk src A₀ : List ℕ) : PS → Prop := fun s =>
  s.1.length = n ∧ p₀ ≤ s.2 ∧ s.2 ≤ e ∧
    (∀ q, p₀ ≤ q → q < s.2 → s.1[idx[q]!]! = expOf off tgt msk src idx[q]!) ∧
    (∀ w, (∀ q, p₀ ≤ q → q < s.2 → idx[q]! ≠ w) → s.1[w]! = A₀[w]!)

theorem bexpPass_le {n p₀ e : ℕ} {idx off tgt msk src A₀ : List ℕ}
    (hsh : Shape n off tgt msk) (hsrc : src.length = n) (he : e ≤ idx.length)
    (hidx : ∀ q, q < e → idx[q]! < n) :
    ∀ (fuel : ℕ) (s : PS), bexpI n p₀ e idx off tgt msk src A₀ s → e - s.2 < fuel →
      bexpPass n e idx off tgt msk src s
        ≤ NRest.spec (fun t => bexpI n p₀ e idx off tgt msk src A₀ t ∧ bexpBf e t = false)
            (fun _ => liftACost (E2 (iter bexpRowC) (iter expC) (e - s.2)
              (degSum idx off s.2 e) + cu Currency.«while»)) :=
  while_pot_le (P := bexpP n e idx off tgt msk src) (V := fun s => e - s.2)
    (Φ := fun s => E2 (iter bexpRowC) (iter expC) (e - s.2) (degSum idx off s.2 e))
    (Φ' := fun s =>
      E2 (iter bexpRowC) (iter expC) (e - (s.2 + 1)) (degSum idx off (s.2 + 1) e))
    (C := fun s => bexpRowC + (off[idx[s.2]! + 1]! - off[idx[s.2]!]!) • iter expC)
    (fun s h hb => ⟨hsh, hsrc, h.1, by simpa [bexpBf] using hb, he, hidx⟩)
    (fun s h hb => by
      have hi : s.2 < e := by simpa [bexpBf] using hb
      obtain ⟨hl, hlo, hhi, hval, hkeep⟩ := h
      refine le_trans (bexpRowF_le hsh hsrc he hidx s hl hi) (spec_mono ?_ (fun _ _ => le_rfl))
      rintro t ⟨htlen, hti, htkeep, htnew⟩
      refine ⟨⟨htlen, by omega, by omega, fun q hq hq' => ?_, fun w hw => ?_⟩, ?_, ?_⟩
      · rw [hti] at hq'
        by_cases hh : idx[q]! = idx[s.2]!
        · rw [hh]; exact htnew
        · have hne : q ≠ s.2 := fun hcon => hh (by rw [hcon])
          rw [htkeep _ hh]
          exact hval q hq (by omega)
      · rw [hti] at hw
        rw [htkeep w (fun hcon => hw s.2 (by omega) (by omega) hcon.symm)]
        exact hkeep w fun q hq hq' => hw q hq (by omega)
      · show e - t.2 < e - s.2
        rw [hti]; omega
      · show E2 (iter bexpRowC) (iter expC) (e - t.2) (degSum idx off t.2 e) ≤ _
        rw [hti])
    (fun s _ hb => by
      have hi : s.2 < e := by simpa [bexpBf] using hb
      show iter (bexpRowC + (off[idx[s.2]! + 1]! - off[idx[s.2]!]!) • iter expC)
        + E2 (iter bexpRowC) (iter expC) (e - (s.2 + 1)) (degSum idx off (s.2 + 1) e)
        ≤ E2 (iter bexpRowC) (iter expC) (e - s.2) (degSum idx off s.2 e)
      rw [show e - s.2 = (e - (s.2 + 1)) + 1 by omega,
        degSum_succ_bot idx off hi, Nat.add_comm (off[idx[s.2]! + 1]! - off[idx[s.2]!]!),
        E2_split]
      exact le_of_eq (by simp only [iter]; ac_rfl))

/-- **One block-driven expansion, discharged.** Every member of the
block holds `ExpandSynth.expOf`, no other cell is written (B4c/D-b), and
the cost is the block's size and the block's own arena slots — never the
carrier (B4c/D-d). -/
theorem bexpPass_spec {n p₀ e : ℕ} {idx off tgt msk src A₀ : List ℕ}
    (hsh : Shape n off tgt msk) (hsrc : src.length = n) (hA : A₀.length = n)
    (hp : p₀ ≤ e) (he : e ≤ idx.length) (hidx : ∀ q, q < e → idx[q]! < n) :
    bexpPass n e idx off tgt msk src (A₀, p₀)
      ≤ NRest.spec
          (fun t : PS => t.1.length = n ∧
            (∀ q, p₀ ≤ q → q < e → t.1[idx[q]!]! = expOf off tgt msk src idx[q]!) ∧
            (∀ w, (∀ q, p₀ ≤ q → q < e → idx[q]! ≠ w) → t.1[w]! = A₀[w]!))
          (fun _ => liftACost (E2 (iter bexpRowC) (iter expC) (e - p₀)
            (degSum idx off p₀ e) + cu Currency.«while»)) := by
  refine le_trans (bexpPass_le hsh hsrc he hidx (e + 1) (A₀, p₀)
    ⟨hA, le_rfl, hp, fun q hq hq' => absurd hq' (by omega), fun w _ => rfl⟩ (by omega))
    (spec_mono ?_ (fun _ _ => by simp))
  rintro t ⟨⟨t1, -, t3, t4, t5⟩, hbf⟩
  have hte : t.2 = e := by
    have : ¬ t.2 < e := by simpa [bexpBf] using hbf
    omega
  subst hte
  exact ⟨t1, t4, t5⟩

/-! ### 4.5 The synthesis -/

set_option maxHeartbeats 1000000 in
sepref_synth bexpSynth (n e : ℕ) (idx off tgt msk src dst₀ : List ℕ) (p₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (dst₀, p₀) ("dst", "p") ∗
      hnCtxt arrayAssn idx "xmm" ∗ hnCtxt arrayAssn off "off" ∗
      hnCtxt arrayAssn tgt "tgt" ∗ hnCtxt arrayAssn msk "msk" ∗
      hnCtxt arrayAssn src "src" ∗ hnCtxt natAssn e "pend" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "z" ∗ junkCell "hz" ∗ junkCell "mz" ∗ junkCell "hct" ∗ junkCell "j" ∗
      junkCell "zp" ∗ junkCell "jend" ∗ junkCell "w" ∗ junkCell "mw" ∗ junkCell "sw")
    _ _ ("dst", "p") (arrayAssn ×ₐ natAssn)
    (bexpPass n e idx off tgt msk src (dst₀, p₀))

-- **The block-driven expansion, pinned.** Instruction for instruction
-- `ExpandSynth.expSynth_impl`'s body, with two differences and no
-- others: the member read `z := xmm[p]` in front, and the loop's guard
-- and bump on the **slot pointer** `p` rather than on the vertex `z`.
-- Everything between — the count reset, the branch containing the row
-- load and the block scan, the two-armed store — is the same program.
#guard bexpSynth_impl =
  Com.while (Cond.lt (Operand.cell "p") (Operand.cell "pend"))
    ((Com.aget "z" "xmm" "p").seq
      ((Com.aget "hz" "src" "z").seq
        ((Com.aget "mz" "msk" "z").seq
          ((Com.const "hct" 0).seq
            ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "mz"))
                  ((Com.aget "j" "off" "z").seq
                    ((Com.binop Lax13Proofs.Imp.Bop.add "zp" "z" "one").seq
                      ((Com.aget "jend" "off" "zp").seq
                        (Com.skip.seq
                          ((Com.while (Cond.lt (Operand.cell "j") (Operand.cell "jend"))
                                ((Com.aget "w" "tgt" "j").seq
                                  ((Com.aget "mw" "msk" "w").seq
                                    ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "mw"))
                                          ((Com.aget "sw" "src" "w").seq
                                            (Com.ite
                                              (Cond.lt (Operand.cell "zero") (Operand.cell "sw"))
                                              (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "one")
                                              (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct"
                                                "zero")))
                                          (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct"
                                            "zero")).seq
                                      ((Com.binop Lax13Proofs.Imp.Bop.add "j" "j" "one").seq
                                        Com.skip))))).seq
                            (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero"))))))
                  (Com.binop Lax13Proofs.Imp.Bop.add "hct" "hct" "zero")).seq
              ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "hct"))
                    (Com.aset "dst" "z" "one") (Com.aset "dst" "z" "hz")).seq
                ((Com.binop Lax13Proofs.Imp.Bop.add "p" "p" "one").seq Com.skip)))))))

-- **It is not the carrier pass.** Two programs, and the difference is
-- exactly the floor 2G/N-3 named.
#guard bexpSynth_impl ≠ ExpandSynth.expSynth_impl

/-- The pass's synthesis with the tool's frame left existential. -/
theorem bexpSynth' (n e : ℕ) (idx off tgt msk src dst₀ : List ℕ) (p₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (dst₀, p₀) ("dst", "p") ∗
        hnCtxt arrayAssn idx "xmm" ∗ hnCtxt arrayAssn off "off" ∗
        hnCtxt arrayAssn tgt "tgt" ∗ hnCtxt arrayAssn msk "msk" ∗
        hnCtxt arrayAssn src "src" ∗ hnCtxt natAssn e "pend" ∗
        hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        junkCell "z" ∗ junkCell "hz" ∗ junkCell "mz" ∗ junkCell "hct" ∗ junkCell "j" ∗
        junkCell "zp" ∗ junkCell "jend" ∗ junkCell "w" ∗ junkCell "mw" ∗ junkCell "sw")
      bexpSynth_impl Γ' ("dst", "p") (arrayAssn ×ₐ natAssn)
      (bexpPass n e idx off tgt msk src (dst₀, p₀)) :=
  ⟨_, bexpSynth n e idx off tgt msk src dst₀ p₀⟩

/-! ### 4.6 Gate — the synthesized expansion, run -/

def bpState (msk src A : List ℕ) (p₀ e : ℕ) : Ir.State :=
  Ir.State.ofPairs [("p", p₀), ("pend", e), ("one", 1), ("zero", 0), ("z", 0), ("hz", 0),
      ("mz", 0), ("hct", 5), ("j", 0), ("zp", 0), ("jend", 0), ("w", 0), ("mw", 0), ("sw", 0)]
    [("dst", A), ("xmm", bidx), ("off", ExpandSynth.demoOff), ("tgt", ExpandSynth.demoTgt),
      ("msk", msk), ("src", src)]

def bpRun (msk src A : List ℕ) (p₀ e : ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 bexpSynth_impl (bpState msk src A p₀ e)).bind fun p => p.1.arrs "dst"

-- **The program is the twin**, out of a junk destination.
#guard bpRun ExpandSynth.demoAll ExpandSynth.demoSrc (List.replicate 6 9) 0 3
  = some (bexpOnce 0 3 bidx ExpandSynth.demoOff ExpandSynth.demoTgt ExpandSynth.demoAll
      ExpandSynth.demoSrc (List.replicate 6 9))
#guard bpRun ExpandSynth.demoAll ExpandSynth.demoSrc (List.replicate 6 9) 0 3
  = some [9, 1, 0, 0, 9, 9]

-- **The count is reset per member**, not per pass: the entry store pins
-- `"hct"` at `5` and the answer is unaffected.
#guard bpRun ExpandSynth.demoAll ExpandSynth.demoSrc (List.replicate 6 0) 0 3
  = some [0, 1, 0, 0, 0, 0]

-- **Negative control: the pass does not write off its block**, so it is
-- not the carrier expansion.
/--
error: Expression
  decide
    (bpRun ExpandSynth.demoAll ExpandSynth.demoSrc (List.replicate 6 9) 0 3 =
      ExpandSynth.pRun ExpandSynth.demoAll ExpandSynth.demoSrc (List.replicate 6 9))
did not evaluate to `true`
-/
#guard_msgs in
#guard bpRun ExpandSynth.demoAll ExpandSynth.demoSrc (List.replicate 6 9) 0 3
  = ExpandSynth.pRun ExpandSynth.demoAll ExpandSynth.demoSrc (List.replicate 6 9)

-- **…and it agrees with it on the block.**
#guard (bidx.all fun z => decide
  (((bpRun ExpandSynth.demoAll ExpandSynth.demoSrc (List.replicate 6 9) 0 3).getD [])[z]!
    = ((ExpandSynth.pRun ExpandSynth.demoAll ExpandSynth.demoSrc
        (List.replicate 6 9)).getD [])[z]!)) = true

-- **The mask is load-bearing in the evaluator too.**
#guard bpRun ExpandSynth.demoCut [0, 1, 0, 0, 0, 0] (List.replicate 6 0) 0 3
  = some [0, 1, 0, 0, 0, 0]
#guard bpRun ExpandSynth.demoAll [0, 1, 0, 0, 0, 0] (List.replicate 6 0) 0 3
  = some [0, 1, 1, 0, 0, 0]

/-! ### 4.7 The bridge into `RamDriverCluster`'s vocabulary

`ExpandSynth.expOf_eq_expandVal` is the whole graph mathematics and is
consumed. What comes out is the block-driven pass in
`RamDriverDescend.expandCom_spec`'s language, at a cost that is the
block's and not the carrier's. -/

section Bridge

open Lax13Proofs.Reasoning (arrOf)
open Lax3Proofs.RamBfs (CsrGraph)
open Lax3Proofs.RamDriverCluster (expandVal)

theorem bexpPass_expandVal {n ns p₀ e : ℕ} {G : SimpleGraph (Fin n)} {O T Msk Src : ℕ → ℕ}
    (hcsr : CsrGraph G ns O T) {idx A₀ : List ℕ} (hA : A₀.length = n)
    (hp : p₀ ≤ e) (he : e ≤ idx.length) (hidx : ∀ q, q < e → idx[q]! < n) :
    bexpPass n e idx (arrOf (n + 1) O) (arrOf ns T) (arrOf n Msk) (arrOf n Src) (A₀, p₀)
      ≤ NRest.spec
          (fun t : PS => t.1.length = n ∧
            (∀ q, p₀ ≤ q → q < e → t.1[idx[q]!]! = expandVal G Msk Src idx[q]!) ∧
            (∀ w, (∀ q, p₀ ≤ q → q < e → idx[q]! ≠ w) → t.1[w]! = A₀[w]!))
          (fun _ => liftACost (E2 (iter bexpRowC) (iter expC) (e - p₀)
            (degSum idx (arrOf (n + 1) O) p₀ e) + cu Currency.«while»)) := by
  refine le_trans (bexpPass_spec (ExpandSynth.shape_of_csrGraph hcsr) (by simp [arrOf]) hA
    hp he hidx) (spec_mono ?_ (fun _ _ => le_rfl))
  rintro t ⟨t1, t2, t3⟩
  exact ⟨t1, fun q hq hq' => by
    rw [t2 q hq hq']
    exact ExpandSynth.expOf_eq_expandVal hcsr (hidx q hq'), t3⟩

end Bridge

end BExp

/-! ## 5. The costs, against the carrier passes

Every number below is exact on both sides: `ClusterSynth` and
`ExpandSynth` prove the carrier passes at closed costs and §§2–4 prove
the block passes at closed costs. The comparison is therefore arithmetic
and not estimation.

| pass | carrier (tower) | block (here) | per cell |
|---|---|---|---|
| clear + load | `12·n + 15·m + 19` | `15·m₁ + 15·m + 30` | clear `+3` |
| and-pass | `22·n + 4` | `25·m + 4` | `+3` |
| sub-pass | `26·n + 4` | `29·m + 4` | `+3` |
| expansion | `47·n + 30·ns + 4` | `50·m + 30·d + 4` | `+3` |

**The per-cell excess is one `aget` at every pass and nothing else** —
the member read `z := xmm[p]` that a carrier pass does not need because
its counter already *is* the cell. That is the whole price of the
change, and it buys `n → m` in the first factor and `ns → d` in the
second: over a level with `k` centres, `Θ(n·k)` becomes `Θ(xp)` with
`xp` the cover's write pointer (the block sizes sum to it) and
`Θ(k·ns)` becomes `Θ(ns)` when the blocks are disjoint. -/

section Cash

theorem cash_bandC : Codegen.cash (iter bandC) = 25 := by decide +kernel

theorem cash_bsubC : Codegen.cash (iter bsubC) = 29 := by decide +kernel

theorem cash_bexpRowC : Codegen.cash (iter bexpRowC) = 50 := by decide +kernel

/-- The block-driven and-pass's cost in IMP+ time units. -/
def bandK (m : ℕ) : ℕ := 25 * m + 4

theorem cash_bandBudget (m : ℕ) :
    Codegen.cash (m • iter bandC + cu Currency.«while») = bandK m := by
  rw [Codegen.cash_add, BfsQSynth.cash_nsmul, cash_bandC, OrderSynth.cash_while, bandK]
  ring

/-- The block-driven sub-pass's. -/
def bsubK (m : ℕ) : ℕ := 29 * m + 4

theorem cash_bsubBudget (m : ℕ) :
    Codegen.cash (m • iter bsubC + cu Currency.«while») = bsubK m := by
  rw [Codegen.cash_add, BfsQSynth.cash_nsmul, cash_bsubC, OrderSynth.cash_while, bsubK]
  ring

/-- The block-driven expansion's: the block's members and the block's
own arena slots. **Neither argument is the carrier.** -/
def bexpK (m d : ℕ) : ℕ := 50 * m + 30 * d + 4

theorem cash_bexpBudget (m d : ℕ) :
    Codegen.cash (E2 (iter bexpRowC) (iter ExpandSynth.expC) m d + cu Currency.«while»)
      = bexpK m d := by
  rw [E2, Codegen.cash_add, Codegen.cash_add, BfsQSynth.cash_nsmul, BfsQSynth.cash_nsmul,
    cash_bexpRowC, ExpandSynth.cash_expC, ExpandSynth.cash_while, bexpK]
  ring

/-! ### The two sides, at §1's arenas and at ten times the carrier

Three blocks over six vertices, and the middle block's three members;
the path's three middle members and their six arena slots. The block
figures do not move when the carrier does. -/

-- the clear-and-load: the carrier's `12·n` is gone
#guard ClusterSynth.clusterLoadK 6 3 = 136
#guard blockLoadK 2 3 = 105
#guard ClusterSynth.clusterLoadK 60 3 = 784
#guard blockLoadK 2 3 = 105

-- the and-pass and the sub-pass
#guard bandK 3 = 79
#guard bsubK 3 = 91
#guard bandK 3 < 22 * 6 + 4
#guard bandK 3 < 22 * 60 + 4

-- the expansion: `47·n + 30·ns` against `50·m + 30·d`
#guard ExpandSynth.expK 6 10 = 586
#guard bexpK 3 6 = 334
#guard ExpandSynth.expK 60 100 = 5824
#guard bexpK 3 6 = 334

-- **the shape of the difference**: a chain of `2·cap = 4` expansions on
-- a three-member ball, at a carrier of six and of sixty
#guard 4 * ExpandSynth.expK 6 10 = 2344
#guard 4 * ExpandSynth.expK 60 100 = 23296
#guard 4 * bexpK 3 6 = 1336

end Cash

/-! ## 6. Axioms -/

section Axioms

/-- info: 'Lax3Proofs.Refine.BlockLeaves.rowScat_le' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms rowScat_le

/-- info: 'Lax3Proofs.Refine.BlockLeaves.blockLoad0_le' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms blockLoad0_le

/-- info: 'Lax3Proofs.Refine.BlockLeaves.rowScatSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms rowScatSynth

/-- info: 'Lax3Proofs.Refine.BlockLeaves.bandPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms bandPass_spec

/-- info: 'Lax3Proofs.Refine.BlockLeaves.bsubPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms bsubPass_spec

/-- info: 'Lax3Proofs.Refine.BlockLeaves.bandSelfPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms bandSelfPass_spec

/-- info: 'Lax3Proofs.Refine.BlockLeaves.bsubSelfPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms bsubSelfPass_spec

/-- info: 'Lax3Proofs.Refine.BlockLeaves.bmask_eq_carrier' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms bmask_eq_carrier

/-- info: 'Lax3Proofs.Refine.BlockLeaves.bexpPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms bexpPass_spec

/-- info: 'Lax3Proofs.Refine.BlockLeaves.bexpPass_expandVal' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms bexpPass_expandVal

/-- info: 'Lax3Proofs.Refine.BlockLeaves.bexpSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms bexpSynth

end Axioms

/-! ## 7. What a consumer can take from here, and what is owed

### The swap-points

Each leaf below replaces a named pass of `RamDriver.clusterCom` at a
stated precondition. The integration wave owns the swap; this file owns
the leaf.

* **`rowScat` at `v := 0`, then `rowScat` at `v := 1`** (`blockLoad0_le`)
  replaces `clusterLoad j` = `fillCom (cluName j) 0; Csr.loadRow; Csr.scan`
  (D2a+D2b+D2c). *Precondition*: the destination is `Supported` on the
  **previous turn's** block — `xoff[cps (k-1)] … xoff[cps (k-1) + 1]`.
  At the **first** turn of a level there is no previous block and the
  carrier fill is still needed once, which is exactly the one `O(n)`
  charge `[[touched-only-costs]]` allows (`TrailRecursion` §6.4). The
  entry store must own **two** constant cells, `"zero"` and `"one"`
  (B4c/D-e).
* **`bandPass`/`bsubPass`** (`bandPass_spec`, `bsubPass_spec`) replace
  D3, D9, C1 (`andCom`) and D8 (`subCom`). *Precondition*: the first
  source and the destination are `Supported` on the turn's block —
  `bmask_eq_carrier` is the proof that under it the answers agree at
  every carrier cell. For D3 (`andCom alv clu res`) the first source is
  the *alive* mask, which is **not** supported on the block, so the swap
  there needs the roles exchanged (`andCom` is commutative in its two
  sources at the value level; `ClusterSynth.andG` is `HMul.hMul`).
* **`bandSelfPass`/`bsubSelfPass`** replace D7d and D10. *Additional
  precondition*: the block is injective (B4c/D-c), which is
  `RamCover.CoverOut.block_inj`.
* **`bexpPass`** (`bexpPass_spec`, `bexpPass_expandVal`) replaces
  `expandCom msk src dst` inside `chainCom` (D6) and inside `pdCom`/
  `puCom` (C2, C3). *Precondition*: `dst` is `Supported` on the block
  and `msk` marks no vertex outside it — then the cells the pass does
  not write already hold `expandVal` (which is `src`'s own value at a
  dead vertex, `expandVal_of_dead`), so the carrier writes were
  redundant.

### 7.1 Debts, named

**B4c/N-1 — the composed clear+load is not synthesized.** `rowScat` is,
at a general `v`, and `blockLoad0` is its sequential composition with
`v := 0` and `v := 1`; the tool did not translate the composition inside
1 000 000 heartbeats (it timed out at ≈ 280 s), where the same shape
with a *fill* in front — `ClusterSynth.loadSynth` — translates in about
one second. The measurement is the wave's own datapoint and its reading
is 2G/M-a's: **two loops whose bounds are both computed by preceding
operations cost the tool much more than one**, at the same state width.
§2's gate composes the two halves in the *evaluator* instead, which
checks the value claim end to end but leaves the composed `Com`
unpinned. The two ways out are a higher budget and an `hnr_seq` by hand;
neither is this wave's.

**B4c/N-2 — `degSum ≤ ns` is not proved.** The expansion's second
currency is the block's own slot count, and what a level's Σ-interface
needs is that the blocks' slot counts sum to the arena. That is a
counting fact about `RamCover.CoverOut.block_inj` and `MassMath`'s
tiling, of exactly the shape `Refine.ArenaBlock.sum_blockSize_compacted_le`
already proves for the block *sizes*; it is `ArenaBlock`'s to extend and
this file's to consume. Without it `bexpK m d` is honest but not yet
summable.

**B4c/N-3 — the first turn of a level still pays a carrier fill.** The
clear is the previous block's, so the induction needs a base, and the
base is `OrderSynth.fillPass` at `n`, once per level rather than once
per centre. That turns `Θ(n·k)` into `Θ(n + xp)` and is the allowed
charge, but it is a charge, and the recurrence in `CostRecurrence` has
to carry it.

**B4c/N-4 — no `BRefine` coverage** (2F/N-5 and 2G/N-2 at these passes).
Every bound (`pend`, `jend`) is a runtime cell entering as an `ℕ`.

**B4c/N-5 — the mask passes' first source is not always block-supported.**
Named under the swap-points above; D3 is the site.

### 7.2 Telemetry

| item | number |
|---|---|
| passes derived here | 6 (`rowScat`, four mask passes, the expansion) + 1 composed |
| syntheses | 6, all at 1 000 000 heartbeats |
| `rowScatSynth` | ≈ 1 s |
| the four mask passes | ≈ 5 s together |
| `bexpSynth` (outer + inner, branch containing the loop) | ≈ 30 s |
| file wall clock, warm, `lake env lean` | 74 s |
| widest state | 2 components (every pass is `(array, pointer)`) |
| `#guard`s | 90 |
| `#guard_msgs` blocks (negative controls + axiom checks) | 15 |
| refuted authored statements | 1 (the self-reading passes at a repeated member — B4c/D-c; the hypothesis was found by running the twin, not by failing a proof) |
| sorries | 0 |
| axioms | `propext`, `Classical.choice`, `Quot.sound` only |

**B4c/M-a — the block-driven form costs the tool nothing.** Every pass
here translated at the same heartbeat budget as its carrier counterpart
and in the same order of wall clock, at the same state width, with one
instruction more in the body. The indirection — reading the loop's
subject out of an array instead of using the counter — is not a tool
event. What *is* a tool event is the composition of two computed-bound
loops (B4c/N-1). -/

end Lax3Proofs.Refine.BlockLeaves
