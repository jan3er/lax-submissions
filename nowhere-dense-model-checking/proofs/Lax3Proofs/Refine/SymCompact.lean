import Lax3Proofs.Refine.ElimCompact

/-!
# ND-MC G2/E2-sym — the compacted-arena symmetrization

The third engine family of `g2-cost-design` §6, on the template
`Refine/ElimCompact.lean` §9 wrote for it. `Refine/OrderEngineProbe.lean`
is the warrant: its coupling table's **first and fourth rows** are the
*restore-seam*, and both are `symCom`'s —

> `mcopyPass … off/tgt` (saves 1–2) | `saveCsr` | restore-seam: `symCom`
> writes `off[0..n]`/`tgt` carrier-wide, so the saved prefix must be the
> carrier's or the restore restores junk
>
> `mcopyPass` restores (6–7) | `restoreCsr` | restore-seam: after
> `symCom` the non-member cells of `off` hold the arena structure's
> offsets, not the level's

This file kills that class. `symCom`'s offset pass is
`fillUpto "off" (.add (.var "n") (.lit 1)) …` — a **carrier** fill only
because the carrier scalar says so. Run at carrier `mm` it is a
`mm+1`-cell fill: a *prefix* write of the compact view, and the level's
dead rows above the prefix come back untouched, with no save and no
restore pass at all. §2.2 compiles that against the landed pass on the
same store (which erases a sentinel the compacted composite hands back
cell for cell), and §4 proves it (`ElimCompact.tail_preserved` at the
schedule `symClen`).

## What the wave had to discover, and did not have to do

`RamDriver.symCom` is **carrier-parametric**, exactly as
`RamElim.elimCom` was: its three passes are `RamAugment.outPass` (three
`forVerts`, all `.lt (.var "i") (.var "n")`), the offset `fillUpto` at
`.add (.var "n") (.lit 1)`, and `RamAugment.forVerts symRow`. Its landed
walk `RamDriverAugment.symPass_run` is a **theorem**, not an obligation,
and it quantifies over that carrier. So "symmetrize at carrier `mm`"
needs no re-synthesis whatever: set `"n" := mm` and apply `symPass_run`
at `n := mm`. No heartbeat ceiling was spent in this file.

What stands in the way is the same *length seam* the elimination met,
and `ElimCompact` §3 closed it generically in the semantics
(`bigStepB_padArrs`, `run_of_run_cutArrs`, `tail_preserved`). This file
imports those verbatim and supplies only its own three pieces, exactly as
the template predicted: a length schedule (`symClen`), a live-prefix
entry surface (`SymPreC`), and one `elimPreW_cutArrs`-shaped lemma
(`symPreC_cutArrs`).

## The contract

`symCom` has no member-indexed output: what it produces is the compact
undirected CSR that the *next compacted elimination* reads out of
`off`/`tgt`, so there is no scatter-back in this family (§9.3 of the
template: "a sibling reuses `compactPass` and `installCom` unchanged and
supplies its own scatter-back **if its outputs are not ranks**"). Its
restated contract `SymMemPost` is therefore already carrier-free — the
subject is an `Orientation mm` and the block structure is read on the
compact prefix — and §6 proves the restatement is an **equivalence** with
the landed reading at `mm = n`, not a weakening.

## What is *not* here

One walk is isolated as a named obligation in §7: `SymPreps`, that the
three preparation passes move the compact in-lists into the pass's input
arrays and zero the counting sort's accumulator over the compact prefix.
It is refuted-before-proved on data in §2.3 and stated once. The
*carrier-setting* half — the two assignments that make `symCom`'s three
loops arena-bounded, which is where "run at carrier `mm`" actually
happens — is **walked here** (`symSetCarrier_spec`), not assumed.

Nothing in this file is `sorry`, and no theorem assumes `SymPreps` except
`symCompact_spec`, which names it as a hypothesis.
-/

namespace Lax3Proofs.Refine.SymCompact

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamDriver (copyUpto fillUpto symCom)
open Lax3Proofs.RamElim (CsrSimple InCsr)
open Lax3Proofs.Augmentation (Orientation)
open Lax3Proofs.RamDriverCluster (markSet)
open Lax3Proofs.TgtWidenProbe (PSt PRes exec execC pB pF augSt aug5doff aug5dtg)
open Lax3Proofs.Refine.ScatterBlock (MemList)
open Lax3Proofs.Refine.ElimCompact (padArrs cutArrs tailOf padArrs_arrs cutArrs_arrs
  run_of_run_cutArrs tail_preserved take_arrOf memGraph getD_padArrs)

/-! ## §1 The program

Four passes and one `Com`. Every bound is `"mm"` or the compact in-list
slot counter `"kd"`; the carrier scalar `"n"` occurs in exactly two
places — the save `"kn" := n` and the install `n := mm` — and the second
is what makes `symCom`'s own three loops arena-bounded.

The cell discipline is the wave's own prefix (`"kn"` the saved carrier,
`"kd"` the compact arc count) plus the landed pass's own names, so no
landed scalar is disturbed. -/

/-- **The compact orientation into the pass's input arrays.** The
compacted elimination (`ElimCompact`) leaves its in-lists in
`ioff`/`itg` *in the compact numbering* — that file's §5 note records
that this is deliberate, because every consumer downstream is compacted
too. This is the phase's own relink (`copyUpto "ioff" "doff"
(.add (.var "n") (.lit 1))`, `copyUpto "itg" "dtg" (.var "lw")`) with
both bounds moved to the arena: `mm + 1` offsets and `kd` slots.

`OrderEngineProbe`'s coupling table row 3 refuted the *member* form of
these two copies (the read-seam: `symCom` reads `doff` at every carrier
vertex). Here they are prefix copies and the reads are at carrier `mm`,
so there is no non-member cell to read. -/
def symRelink : Com :=
  .seq (copyUpto "ioff" "doff" (.add (.var "mm") (.lit 1)))
    (copyUpto "itg" "dtg" (.var "kd"))

/-- **The counting sort's accumulator, zeroed over the compact prefix.**
`RamAugment.outPass` — which `symCom` opens with — accumulates the
out-degrees into `ooff` and so asks for it zeroed. The landed phase
zeroes it carrier-wide (`fillUpto "ooff" (.add (.var "n") (.lit 1))`, in
`orderZeroCom` and `augRelinkCom`); here the fill is `mm + 1` cells.
This is `OrderEngineProbe` §2's zero-seam with nothing to catch: the
re-zero is arena-class, and it is a *prefix* fill rather than a member
scatter, so no cell above the prefix is left stale. -/
def symZero : Com := fillUpto "ooff" (.add (.var "mm") (.lit 1)) (.lit 0)

/-- The three preparation passes. -/
def symPrepCom : Com := .seq symRelink symZero

/-- **The carrier, moved to the arena.** The saved carrier and the
install. Two assignments, and they are the whole of "the engine runs at
carrier `mm`" — this is the pass that is *walked* below
(`symSetCarrier_spec`) rather than assumed. -/
def symSetCarrier : Com := .seq (.assign "kn" (.var "n")) (.assign "n" (.var "mm"))

/-- **The compacted symmetrization, core**: prepare, install the carrier,
run the landed pass. What comes out in `off`/`tgt` is the compact
undirected CSR of the orientation's own graph, on the prefix `[0, mm]` of
the level's offset array and the prefix `[0, 2m)` of its target array —
and nothing above either prefix moves. -/
def symCompactCore : Com := .seq symPrepCom (.seq symSetCarrier symCom)

/-- **…and with the carrier scalar put back**, for a caller that needs
`"n"` as it handed it over. There is nothing else to restore: §2.2 and
§4 are the statement that the level's own `off`/`tgt` come back above the
compact prefix by themselves. -/
def symCompactCom : Com := .seq symCompactCore (.assign "n" (.var "kn"))

/-! ### §1.1 Frames

Read off the syntax, one `simp` apiece — the `OrderSigProbeM` discipline
(pre-owned destinations only). -/

theorem notMem_symRelink_warrs {a : String} (h₁ : a ≠ "doff") (h₂ : a ≠ "dtg") :
    a ∉ symRelink.warrs := by
  simp [symRelink, copyUpto, fillUpto, Fill.put, Com.warrs, h₁, h₂]

theorem notMem_symZero_warrs {a : String} (h : a ≠ "ooff") : a ∉ symZero.warrs := by
  simp [symZero, fillUpto, Fill.put, Com.warrs, h]

theorem notMem_symPrepCom_warrs {a : String} (h₁ : a ≠ "doff") (h₂ : a ≠ "dtg")
    (h₃ : a ≠ "ooff") : a ∉ symPrepCom.warrs := by
  simp [symPrepCom, symRelink, symZero, copyUpto, fillUpto, Fill.put, Com.warrs, h₁, h₂, h₃]

theorem notMem_symPrepCom_wvars {y : String} (h : y ≠ "i") : y ∉ symPrepCom.wvars := by
  simp [symPrepCom, symRelink, symZero, copyUpto, fillUpto, Fill.put, Com.wvars, h]

theorem notMem_symSetCarrier_warrs (a : String) : a ∉ symSetCarrier.warrs := by
  simp [symSetCarrier, Com.warrs]

theorem notMem_symSetCarrier_wvars {y : String} (h₁ : y ≠ "kn") (h₂ : y ≠ "n") :
    y ∉ symSetCarrier.wvars := by
  simp [symSetCarrier, Com.wvars, h₁, h₂]

/-! ## §2 The compiled data

Refute-before-prove, on the sharpest small instance the package has:
`TgtWidenProbe`'s augmented orientation `aug5doff`/`aug5dtg` — ten arcs
on five vertices, whose `toGraph` is `K₅` — carried as the **compact**
in-lists `ioff`/`itg` of a five-member arena inside a carrier of any
size, with a **sentinel** above every compact prefix. -/

/-- The compact in-list offsets at the carrier's physical length: the
five-vertex orientation's own six offsets, then the arc count, which is
what an offset array's padding holds. -/
def symIoffL (n : ℕ) : List ℕ := aug5doff ++ List.replicate (n + 1 - 6) 10

/-- …and its targets at the width. -/
def symItgL (W : ℕ) : List ℕ := aug5dtg ++ List.replicate (W - 10) 0

/-- The store the composite runs in: `augSt`'s twenty-six arrays, with
the compact in-lists installed, and the pass's five destinations filled
with the **sentinel** `7` — so every cell the composite hands back
unchanged is visible, and every cell it writes is visible too. -/
def sSt (n W mm kd : ℕ) : PSt :=
  { augSt n W W (List.replicate (n + 1) 0) [] with
    vars := [("n", n), ("m", 0), ("lw", W), ("mm", mm), ("kd", kd)]
    arrs :=
      ("ioff", symIoffL n) :: ("itg", symItgL W) ::
      ("doff", List.replicate (n + 1) 7) :: ("dtg", List.replicate W 7) ::
      ("off", List.replicate (n + 1) 7) :: ("tgt", List.replicate W 7) ::
      ("ooff", List.replicate (n + 1) 7) :: ("otg", List.replicate W 7) ::
      ("ofl", List.replicate n 7) ::
      (augSt n W W (List.replicate (n + 1) 0) []).arrs }

/-- The composite on the five-member arena at carrier `n`. -/
def symRun (n W : ℕ) : PRes := exec pB pF symCompactCom (sSt n W 5 10)

#guard (symRun 100 64).isOk
#guard (symRun 800 64).isOk

/-! ### §2.1 The answers are the landed pass's, at the compact carrier

`TgtWidenProbe.sym5Run` records the landed pass's answer on this
orientation at carrier `5`: offsets `0 4 8 12 16 20` and the twenty
slots of `K₅`, each row its in-block then its out-block. The compacted
composite must produce exactly those, inside a carrier of any size. -/

#guard (List.range 6).map ((symRun 100 64).cell "off") = [0, 4, 8, 12, 16, 20]
#guard (List.range 20).map ((symRun 100 64).cell "tgt")
  = [1, 2, 3, 4,  0, 2, 3, 4,  1, 0, 3, 4,  1, 2, 0, 4,  1, 2, 3, 0]

-- carrier-blind, cell for cell, at a carrier eight times larger
#guard (List.range 6).map ((symRun 800 64).cell "off") = [0, 4, 8, 12, 16, 20]
#guard (List.range 20).map ((symRun 800 64).cell "tgt")
  = [1, 2, 3, 4,  0, 2, 3, 4,  1, 0, 3, 4,  1, 2, 0, 4,  1, 2, 3, 0]

-- the union is disjoint: no row names a vertex twice, none names its own
#guard ((List.range 5).map fun v =>
  ((List.range 4).map fun k => (symRun 100 64).cell "tgt" (4 * v + k)).eraseDups.length) =
    [4, 4, 4, 4, 4]
#guard ((List.range 5).map fun v =>
  ((List.range 4).map fun k => (symRun 100 64).cell "tgt" (4 * v + k)).contains v) =
    [false, false, false, false, false]

-- the carrier scalar comes back
#guard (symRun 100 64).scalar "n" = 100
#guard (symRun 800 64).scalar "n" = 800

/-! ### §2.2 The restore-seam, dead

`OrderEngineProbe` §3's refutation, and its repair, on the same store.
The sentinel `7` sits above every compact prefix; the composite must hand
every one of those cells back, because at carrier `mm` the offset fill is
`mm + 1` cells and the row copies stop at slot `2m`. That is the whole of
the restore: there is **no save and no restore pass at all**. -/

-- **the level's own offset array, above the compact prefix, untouched**
#guard (List.range 94).all fun k => (symRun 100 64).cell "off" (6 + k) == 7
-- **…and its target array above the compact slot count**
#guard (List.range 44).all fun k => (symRun 100 64).cell "tgt" (20 + k) == 7
-- the same at the larger carrier
#guard (List.range 794).all fun k => (symRun 800 64).cell "off" (6 + k) == 7

/-- The negative control's store: `doff`/`dtg` already hold the same
orientation padded to the carrier (empty rows above the arena) and `ooff`
is zeroed carrier-wide, so the landed pass runs on the same arena at the
**carrier**. -/
def symCarrierSt (n W : ℕ) : PSt :=
  { sSt n W 5 10 with
    arrs := ("doff", symIoffL n) :: ("dtg", symItgL W) ::
      ("ooff", List.replicate (n + 1) 0) :: (sSt n W 5 10).arrs }

def symCarrierRun (n W : ℕ) : PRes := exec pB pF symCom (symCarrierSt n W)

#guard (symCarrierRun 100 64).isOk
-- the same answers on the compact prefix …
#guard (List.range 6).map ((symCarrierRun 100 64).cell "off") = [0, 4, 8, 12, 16, 20]
-- … and the level's dead rows gone: the offset fill ran to the carrier
#guard ¬ ((List.range 94).all fun k => (symCarrierRun 100 64).cell "off" (6 + k) == 7)
#guard (symCarrierRun 100 64).cell "off" 50 = 20

-- **the honesty direction on the arena's own prefix**: the wave does not
-- get its frame by writing nothing — the compact prefix of `off` really
-- did change, from the sentinel to the union's offsets
#guard ¬ ((List.range 6).all fun k => (symRun 100 64).cell "off" k == 7)

/-! ### §2.3 The two preparation passes are load-bearing

Refute-before-prove on `SymPreps` (§7). Without the relink the pass
symmetrizes the sentinel; without the zero the counting sort accumulates
on top of it. Both are compiled as failures of the *answer*, so the
obligation's content is pinned from below. -/

-- the relink is what puts the orientation where the pass reads it
#guard ¬ ((List.range 6).map
  ((exec pB pF (.seq symSetCarrier symCom) (sSt 100 64 5 10)).cell "off") =
  [0, 4, 8, 12, 16, 20])

-- the zero is what the counting sort needs: relink but no re-zero, and
-- `ooff` enters holding the sentinel, so the out-offsets — hence the
-- union's — are wrong
#guard ¬ ((List.range 6).map
  ((exec pB pF (.seq symRelink (.seq symSetCarrier symCom)) (sSt 100 64 5 10)).cell "off") =
  [0, 4, 8, 12, 16, 20])

-- and the carrier install is load-bearing too: without it the pass runs
-- at the carrier and erases the level's rows, which is §2.2's control
#guard ¬ ((List.range 94).all fun k =>
  (exec pB pF (.seq symPrepCom symCom) (sSt 100 64 5 10)).cell "off" (6 + k) == 7)

/-! ## §3 The length schedule and the live-prefix entry

`ElimCompact` §3 is generic and is imported, not re-proved. What this
family owes is its own schedule and its own entry surface. -/

/-- **The length schedule of a compacted symmetrization.** Which prefix
of each of the pass's seven arrays is the compact call's own array; every
name the pass never touches is cut to nothing and restored by the tail.
`dtg`/`otg` are at the allocation width and `tgt` at the caller's
target-array width, so those three cuts are the identity — those widths
were never carrier-coupled. -/
def symClen (mm nt W : ℕ) : String → ℕ := fun a =>
  if a = "doff" ∨ a = "ooff" ∨ a = "off" then mm + 1
  else if a = "ofl" then mm
  else if a = "dtg" ∨ a = "otg" then W
  else if a = "tgt" then nt
  else 0

@[simp] theorem symClen_doff (mm nt W : ℕ) : symClen mm nt W "doff" = mm + 1 := by simp [symClen]
@[simp] theorem symClen_ooff (mm nt W : ℕ) : symClen mm nt W "ooff" = mm + 1 := by simp [symClen]
@[simp] theorem symClen_off (mm nt W : ℕ) : symClen mm nt W "off" = mm + 1 := by simp [symClen]
@[simp] theorem symClen_ofl (mm nt W : ℕ) : symClen mm nt W "ofl" = mm := by simp [symClen]
@[simp] theorem symClen_dtg (mm nt W : ℕ) : symClen mm nt W "dtg" = W := by simp [symClen]
@[simp] theorem symClen_otg (mm nt W : ℕ) : symClen mm nt W "otg" = W := by simp [symClen]
@[simp] theorem symClen_tgt (mm nt W : ℕ) : symClen mm nt W "tgt" = nt := by simp [symClen]

/-- **The pass's entry surface at a live prefix.** Clause for clause the
hypotheses of `RamDriverAugment.symPass_run`, with every physical length
at the carrier `n` and every *contract* at the compact carrier `mm`.
Note what is not here: no clause ranges over the carrier. The
counting-sort accumulator is asked zeroed over `[0, mm]` and not over
`[0, n]`, which is `OrderEngineProbe` §2's zero-seam with nothing to
catch. -/
def SymPreC (mm n nt W : ℕ) (DO DT T₀ : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = mm ∧ mm ≤ n ∧
  (∃ g, σ.arrs "doff" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = DO i) ∧
  σ.arrs "dtg" = arrOf W DT ∧
  (∃ g, σ.arrs "ooff" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = 0) ∧
  (∃ g, σ.arrs "ofl" = arrOf n g) ∧ (∃ g, σ.arrs "otg" = arrOf W g) ∧
  (∃ g, σ.arrs "off" = arrOf (n + 1) g) ∧
  σ.arrs "tgt" = arrOf nt T₀

/-- **The seam, closed at the symmetrization.** The live-prefix surface
at the carrier's physical lengths *is* the landed pass's surface at the
compact carrier, read in the view. Every clause is one `take_arrOf` and
one `arrOf_congr`; `RamDriver`/`RamDriverAugment` are not touched. -/
theorem symPreC_cutArrs {mm n nt W : ℕ} {DO DT T₀ : ℕ → ℕ} {σ : Env}
    (h : SymPreC mm n nt W DO DT T₀ σ) :
    (cutArrs σ (symClen mm nt W)).vars "n" = mm ∧
    (cutArrs σ (symClen mm nt W)).arrs "doff" = arrOf (mm + 1) DO ∧
    (cutArrs σ (symClen mm nt W)).arrs "dtg" = arrOf W DT ∧
    (∃ g, (cutArrs σ (symClen mm nt W)).arrs "ooff" = arrOf (mm + 1) g ∧
      ∀ k ≤ mm, g k = 0) ∧
    (∃ g, (cutArrs σ (symClen mm nt W)).arrs "ofl" = arrOf mm g) ∧
    (∃ g, (cutArrs σ (symClen mm nt W)).arrs "otg" = arrOf W g) ∧
    (∃ g, (cutArrs σ (symClen mm nt W)).arrs "off" = arrOf (mm + 1) g) ∧
    (cutArrs σ (symClen mm nt W)).arrs "tgt" = arrOf nt T₀ := by
  obtain ⟨hn, hmn, ⟨d, hd, hdP⟩, hdtg, ⟨o, ho, hoP⟩, ⟨f, hf⟩, ⟨t, ht⟩, ⟨e, he⟩, htgt⟩ := h
  refine ⟨hn, ?_, ?_, ⟨o, ?_, hoP⟩, ⟨f, ?_⟩, ⟨t, ?_⟩, ⟨e, ?_⟩, ?_⟩
  · rw [cutArrs_arrs, symClen_doff, hd, take_arrOf (by omega)]
    exact ElimCompact.arrOf_congr fun i hi => hdP i (by omega)
  · rw [cutArrs_arrs, symClen_dtg, hdtg, take_arrOf le_rfl]
  · rw [cutArrs_arrs, symClen_ooff, ho, take_arrOf (by omega)]
  · rw [cutArrs_arrs, symClen_ofl, hf, take_arrOf hmn]
  · rw [cutArrs_arrs, symClen_otg, ht, take_arrOf le_rfl]
  · rw [cutArrs_arrs, symClen_off, he, take_arrOf (by omega)]
  · rw [cutArrs_arrs, symClen_tgt, htgt, take_arrOf le_rfl]

/-! ## §4 The pass at the arena's carrier

The landed walk, transported. `RamDriverAugment.symPass_run` is applied
at `n := mm`; nothing is restated and nothing is re-synthesized. -/

/-- The exit state's tail is the entry state's, per array — the compiled
§2.2 claim as a theorem, at any name of the schedule. This is the
restore-seam's death: the level's own `off` above `mm + 1` and its own
`tgt` above `nt` come back because the run never reached them. -/
theorem symCompact_tail {B mm nt W : ℕ} {σ τ : Env} {K : ℕ}
    (h : Run B symCom (cutArrs σ (symClen mm nt W)) τ K) {a : String}
    (hle : symClen mm nt W a ≤ (σ.arrs a).length) :
    ((padArrs τ (tailOf σ (symClen mm nt W))).arrs a).drop (symClen mm nt W a) =
      (σ.arrs a).drop (symClen mm nt W a) :=
  tail_preserved h hle

/-- **The compacted symmetrization.** `RamDriver.symCom`, unchanged, at
the compact carrier `mm`, on a store whose arrays are the carrier's: it
runs at `RamDriverAugment.symCost mm m` — a cost in which **the carrier
does not occur** — and leaves in the compact prefix of `off`/`tgt` a
`RamElim.CsrSimple` block structure of `D.toGraph` at `m + m` slots. The
exit store is the view's answer over the tail the call entered with.

Both halves are the wave: the compact answer, and the untouched tail. -/
theorem symCompact_engine {B mm n nt W m : ℕ} {D : Orientation mm} {DO DT T₀ : ℕ → ℕ}
    {σ : Env} (hB1 : mm + 1 < B) (hB2 : m + m < B) (hmW : m ≤ W) (hfit : m + m ≤ nt)
    (hin : InCsr D m DO DT) (hpre : SymPreC mm n nt W DO DT T₀ σ) :
    ∃ (τ : Env) (K : ℕ) (O T : ℕ → ℕ),
      Run B symCom σ (padArrs τ (tailOf σ (symClen mm nt W))) K ∧
      K ≤ Lax3Proofs.RamDriverAugment.symCost mm m ∧
      τ.arrs "off" = arrOf (mm + 1) O ∧ τ.arrs "tgt" = arrOf nt T ∧
      CsrSimple D.toGraph (m + m) O T ∧
      (∀ z, m + m ≤ z → z < nt → T z = T₀ z) ∧
      (∀ a, symClen mm nt W a ≤ (σ.arrs a).length →
        ((padArrs τ (tailOf σ (symClen mm nt W))).arrs a).drop (symClen mm nt W a) =
          (σ.arrs a).drop (symClen mm nt W a)) ∧
      (∀ a, a ≠ "off" → a ≠ "tgt" → a ≠ "ooff" → a ≠ "ofl" → a ≠ "otg" →
        τ.arrs a = (cutArrs σ (symClen mm nt W)).arrs a) ∧
      (∀ y, y ≠ "i" → y ≠ "j" → y ≠ "jend" → y ≠ "u" → y ≠ "sy" → τ.vars y = σ.vars y) := by
  obtain ⟨hn, hdoff, hdtg, hooff, hofl, hotg, hoffE, htgtA⟩ := symPreC_cutArrs hpre
  obtain ⟨τ, K, O, T, hrun, hK, hoff', htgt', hcsr, htail, hfa, hfv⟩ :=
    Lax3Proofs.RamDriverAugment.symPass_run (n := mm) (B := B) (W := W) (nt := nt) (m := m)
      (D := D) (DO := DO) (DT := DT) (T₀ := T₀) hB1 hB2 hmW hfit hn hin hdoff hdtg
      hooff hofl hotg hoffE htgtA
  exact ⟨τ, K, O, T, run_of_run_cutArrs _ hrun, hK, hoff', htgt', hcsr, htail,
    fun a ha => symCompact_tail hrun ha, hfa, hfv⟩

/-! ## §5 The contract at the compacted arena

`OrderEngineProbe` §5 compiled that the *phase*'s postcondition is
carrier-sized and that no engine repair can change that. This section is
the symmetrization's own half of the move: the pass's contract, restated
so that nothing in it ranges over the carrier.

The subject is an `Orientation mm` — the compacted arena's own
orientation, or an augmentation of it — and the block structure is read
on the compact prefix of the level's offset array, `getD`-style, exactly
as `ElimCompact.ElimMemPost` reads the in-lists. There is no `∀ v < n`:
that is the whole point. -/

/-- **The symmetrization's contract, at the compacted arena.** The
compact undirected CSR of `D.toGraph`, on the prefix `[0, mm]` of the
offset array and in the target array at the caller's width, with the
target array's own tail above the slot count preserved.

This is what the *second* compacted elimination reads: `ElimCompact`'s
`ElimPreC` asks for `off` as `arrOf (n+1) g` with `∀ i ≤ mm, g i = O i`
and `tgt` as `arrOf nt T`, which is this postcondition's `O`/`T`. -/
def SymMemPost (mm nt m : ℕ) (D : Orientation mm) (T₀ : ℕ → ℕ) (σ' : Env) : Prop :=
  ∃ O T : ℕ → ℕ,
    (∀ i, i ≤ mm → (σ'.arrs "off").getD i 0 = O i) ∧
    σ'.arrs "tgt" = arrOf nt T ∧
    CsrSimple D.toGraph (m + m) O T ∧
    (∀ z, m + m ≤ z → z < nt → T z = T₀ z)

/-- **The arena reading.** When the orientation symmetrized is one of the
compacted arena itself — which is what `ElimCompact.ElimMemPost`'s
`E.toGraph = memGraph G M hml` clause delivers at `R = 0` — the compact
CSR the pass leaves is a CSR of the compacted arena, and every quantifier
of the statement ranges over `Fin mm`. -/
theorem symMemPost_memGraph {n mm nt m : ℕ} {G : SimpleGraph (Fin n)} {M Mem : ℕ → ℕ}
    {X : Set (Fin n)} {hml : MemList n mm Mem X} {D : Orientation mm} {T₀ : ℕ → ℕ}
    {σ' : Env} (h : SymMemPost mm nt m D T₀ σ') (hD : D.toGraph = memGraph G M hml) :
    ∃ O T : ℕ → ℕ, (∀ i, i ≤ mm → (σ'.arrs "off").getD i 0 = O i) ∧
      σ'.arrs "tgt" = arrOf nt T ∧ CsrSimple (memGraph G M hml) (m + m) O T := by
  obtain ⟨O, T, hoff, htgt, hcsr, -⟩ := h
  exact ⟨O, T, hoff, htgt, hD ▸ hcsr⟩

/-! ## §6 The bridge to the landed reading

The wave's contract is a restatement, so it owes the statement that it
*is* one. At `mm = n` — the all-alive arena at the identity numbering —
`SymMemPost` is the landed conclusion of `symPass_run`, clause for clause
and in **both directions**: this is an equivalence, not a weakening. -/

/-- **The bridge.** At the carrier the member reading of the offsets is
the landed `arrOf (n+1) O` reading, and conversely. So §5 weakens
nothing. -/
theorem symMemPost_iff_landed {n nt m : ℕ} {D : Orientation n} {T₀ g : ℕ → ℕ} {σ' : Env}
    (hlen : σ'.arrs "off" = arrOf (n + 1) g) :
    SymMemPost n nt m D T₀ σ' ↔
      ∃ O T : ℕ → ℕ, σ'.arrs "off" = arrOf (n + 1) O ∧ σ'.arrs "tgt" = arrOf nt T ∧
        CsrSimple D.toGraph (m + m) O T ∧ (∀ z, m + m ≤ z → z < nt → T z = T₀ z) := by
  constructor
  · rintro ⟨O, T, hoff, htgt, hcsr, htail⟩
    refine ⟨O, T, ?_, htgt, hcsr, htail⟩
    rw [hlen]
    refine ElimCompact.arrOf_congr fun i hi => ?_
    have h := hoff i (by omega)
    rwa [hlen, getD_arrOf g hi] at h
  · rintro ⟨O, T, hoff, htgt, hcsr, htail⟩
    exact ⟨O, T, fun i hi => by rw [hoff, getD_arrOf O (by omega)], htgt, hcsr, htail⟩

/-! ## §7 The composite

One named obligation (`SymPreps`, §2.3's compiled content), one walked
pass (`symSetCarrier_spec` — the carrier install, which is where "run at
carrier `mm`" happens), and §4's transported engine. -/

/-! ### §7.0 What a discharger of `SymPreps` needs

The kit is landed and the arithmetic closes, which is why this is an
obligation and not a gap: `RamDriverOrder.copyKeep_spec` and
`fillKeep_spec` — the live-prefix half of the flat-pass kit, whose
postconditions carry the *tail-kept* clause this obligation's
live-prefix reading needs — apply once per pass at
`(N, Nd) = (mm+1, n+1)`, `(kd, W)`, `(mm+1, n+1)`, with the invariant
`Q τ := τ.vars "n" = n ∧ τ.vars "mm" = mm ∧ τ.vars "kd" = kd ∧
τ.arrs "ioff" = arrOf (n+1) IOg ∧ τ.arrs "itg" = arrOf W ITg` (each pass
writes a different array and only the scalar `"i"`, so `hQfr` is
immediate). The three costs are `14·(mm+1) + 8`, `12·kd + 6` and
`13·(mm+1) + 8`, i.e. `27·mm + 12·kd + 49`, inside
`symPrepCost mm kd = 100·mm + 100·kd + 100` with room. -/

/-- **The composite's entry**: the compact in-lists as the compacted
elimination leaves them, the pass's five scratch arrays at the carrier's
physical lengths, and the level's own offset and target arrays. -/
def SymEntryC (n mm nt W kd : ℕ) (IO IT T₀ : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "mm" = mm ∧ σ.vars "kd" = kd ∧ mm ≤ n ∧ kd ≤ W ∧
  (∃ g, σ.arrs "ioff" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = IO i) ∧
  (∃ g, σ.arrs "itg" = arrOf W g ∧ ∀ j < kd, g j = IT j) ∧
  (∃ g, σ.arrs "doff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "dtg" = arrOf W g) ∧
  (∃ g, σ.arrs "ooff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "ofl" = arrOf n g) ∧
  (∃ g, σ.arrs "otg" = arrOf W g) ∧ (∃ g, σ.arrs "off" = arrOf (n + 1) g) ∧
  σ.arrs "tgt" = arrOf nt T₀

/-- The preparation budget: arena-affine, carrier-free. -/
def symPrepCost (mm kd : ℕ) : ℕ := 100 * mm + 100 * kd + 100

/-- **Obligation E2-s/1 — the preparation walk.** `symPrepCom` moves the
compact in-lists into the pass's input arrays and zeroes the counting
sort's accumulator over the compact prefix, at `symPrepCost`, leaving the
pass's live-prefix entry surface and touching no cell above the compact
prefixes.

Refutable, and refuted-before-proved on data in §2.3: without the relink
the pass symmetrizes the sentinel, and without the zero the counting sort
accumulates on top of it — both compiled as failures of the arena's own
offsets.

The four antecedents are the word bounds a *copy* needs and nothing more:
`Expr.evalB` refuses a value reaching `B` at every subterm, so a copy of a
cell holding `B` or more has no derivation at all and the obligation
without them would be false rather than merely hard.
`prep_bounds_of_inCsr` supplies the last two from the block structure
itself, at `kd = m`. -/
def SymPreps (B n mm nt W kd : ℕ) : Prop :=
  ∀ (IO IT T₀ : ℕ → ℕ) (σ : Env), mm + 1 < B → kd < B →
    (∀ i ≤ mm, IO i < B) → (∀ j < kd, IT j < B) →
    SymEntryC n mm nt W kd IO IT T₀ σ →
    ∃ (σ' : Env) (DT : ℕ → ℕ),
      Run B symPrepCom σ σ' (symPrepCost mm kd) ∧
      σ'.vars "n" = n ∧ σ'.vars "mm" = mm ∧
      σ'.arrs "dtg" = arrOf W DT ∧ (∀ j < kd, DT j = IT j) ∧
      (∃ g, σ'.arrs "doff" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = IO i) ∧
      (∃ g, σ'.arrs "ooff" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = 0) ∧
      (∃ g, σ'.arrs "ofl" = arrOf n g) ∧ (∃ g, σ'.arrs "otg" = arrOf W g) ∧
      (∃ g, σ'.arrs "off" = arrOf (n + 1) g) ∧
      σ'.arrs "tgt" = arrOf nt T₀

/-- **The two word bounds a preparation copy needs, from the block
structure itself.** An in-list offset of an `m`-slot structure is at most
`m`, and a slot target is a vertex of the compact arena — so at `kd = m`,
which is what the phase's relink copies, the caller of `SymPreps` (and of
`AugCompact.AugPreps`) has both antecedents for free. -/
theorem prep_bounds_of_inCsr {B mm m : ℕ} {D : Orientation mm} {IO IT : ℕ → ℕ}
    (h : InCsr D m IO IT) (hmB : m < B) (hmmB : mm < B) :
    (∀ i ≤ mm, IO i < B) ∧ (∀ j < m, IT j < B) := by
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · have := Lax3Proofs.RamDriverAugment.off_le_last h.mono h.last i hi
    omega
  · have := h.target_lt j hj
    omega

/-- **The carrier install, walked.** Two assignments: the carrier saved
and the arena's vertex count put in its place. This is the whole of "the
engine runs at carrier `mm`", and it is proved, not assumed — the
`SymPreC` surface it produces is `symCompact_engine`'s precondition.

The one side condition is a word bound on the two scalars, which the
caller has from `mm ≤ n < B`. -/
theorem symSetCarrier_run {B n mm : ℕ} {σ : Env} (hnB : n < B) (hmB : mm < B)
    (hn : σ.vars "n" = n) (hmm : σ.vars "mm" = mm) :
    Run B symSetCarrier σ ((σ.setVar "kn" n).setVar "n" mm) 4 := by
  have h₁ : Run B (.assign "kn" (.var "n")) σ (σ.setVar "kn" n) 2 := by
    have h := Run.assign (B := B) (σ := σ) (x := "kn") (e := .var "n")
      (evalB_var (by rw [hn]; omega))
    rw [hn] at h
    simpa using h
  have h₂ : Run B (.assign "n" (.var "mm")) (σ.setVar "kn" n)
      ((σ.setVar "kn" n).setVar "n" mm) 2 := by
    have hv : (σ.setVar "kn" n).vars "mm" = mm := by simp [hmm]
    have h := Run.assign (B := B) (σ := σ.setVar "kn" n) (x := "n") (e := .var "mm")
      (evalB_var (by rw [hv]; omega))
    rw [hv] at h
    simpa using h
  exact (h₁.seq h₂).mono (by omega)

theorem symSetCarrier_spec {B n mm nt W : ℕ} {DO DT T₀ : ℕ → ℕ} {σ : Env}
    (hnB : n < B) (hn : σ.vars "n" = n) (hmm : σ.vars "mm" = mm) (hmn : mm ≤ n)
    (hdoff : ∃ g, σ.arrs "doff" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = DO i)
    (hdtg : σ.arrs "dtg" = arrOf W DT)
    (hooff : ∃ g, σ.arrs "ooff" = arrOf (n + 1) g ∧ ∀ i ≤ mm, g i = 0)
    (hofl : ∃ g, σ.arrs "ofl" = arrOf n g) (hotg : ∃ g, σ.arrs "otg" = arrOf W g)
    (hoffE : ∃ g, σ.arrs "off" = arrOf (n + 1) g) (htgt : σ.arrs "tgt" = arrOf nt T₀) :
    ∃ σ', Run B symSetCarrier σ σ' 4 ∧ SymPreC mm n nt W DO DT T₀ σ' ∧
      σ'.vars "kn" = n ∧ σ'.vars "mm" = mm ∧ (∀ a, σ'.arrs a = σ.arrs a) := by
  refine ⟨(σ.setVar "kn" n).setVar "n" mm, symSetCarrier_run hnB (by omega) hn hmm,
    ⟨by simp, hmn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp, by simp [hmm], fun a => rfl⟩
  · simpa using hdoff
  · simpa using hdtg
  · simpa using hooff
  · simpa using hofl
  · simpa using hotg
  · simpa using hoffE
  · simpa using htgt

/-! ### §7.1 The cost: arena-affine, carrier-blind -/

/-- **The composite's cost**: the landed pass's own `symCost` at the
compact carrier, plus the preparation and the carrier install at a
generous constant. `mm` is the arena's live vertex count and `cs` its
live slot count — **the carrier `n` does not appear**. -/
def symCompactCost (mm cs : ℕ) : ℕ :=
  Lax3Proofs.RamDriverAugment.symCost mm cs + symPrepCost mm cs + 100

/-- The cost, expanded: `300·mm + 200·cs + 400`. Affine in the arena's
two numbers, and in nothing else. -/
theorem symCompactCost_eq (mm cs : ℕ) :
    symCompactCost mm cs = 300 * mm + 200 * cs + 400 := by
  simp only [symCompactCost, symPrepCost, Lax3Proofs.RamDriverAugment.symCost]; ring

#guard symCompactCost 5 10 = 300 * 5 + 200 * 10 + 400
#guard symCompactCost 5 10 = 3900
-- two-sided: the constants are not slack
#guard ¬ (symCompactCost 5 10 = 301 * 5 + 200 * 10 + 400)

/-- **The single weight**: the composite's cost is affine in the arena's
weight and in nothing else. -/
theorem symCompactCost_le_weight {mm cs w : ℕ} (h : mm + cs ≤ w) :
    symCompactCost mm cs ≤ 300 * w + 400 := by
  rw [symCompactCost_eq]
  have : 300 * mm + 300 * cs = 300 * (mm + cs) := by ring
  omega

/-- **…and the weight is the compacted arena's own.** `MassWeight`'s root
reading at the compact graph: a `CsrSimple` of a graph all of whose
vertices are alive has weight `mm + cs`. So the composite's clock is
`300 · arenaWeight + 400` at the arena the pass actually ran on, with the
carrier nowhere in sight. -/
theorem symCompactCost_le_arenaWeight {mm cs : ℕ} {H : SimpleGraph (Fin mm)} {O' T' : ℕ → ℕ}
    (hcsr : CsrSimple H cs O' T') {M' : ℕ → ℕ} (halive : ∀ v < mm, M' v ≠ 0) :
    symCompactCost mm cs ≤ 300 * MassWeight.arenaWeight mm H M' + 400 :=
  symCompactCost_le_weight (le_of_eq (MassWeight.arenaWeight_root hcsr halive).symm)

/-! ### §7.2 The clocks, compiled

The control pattern of `ElimCompact` §6.1: the same arena inside two
carriers differing by a factor of eight, and one clock — against the
landed pass on the same arena, whose clock is affine in the carrier. -/

/-- The composite's clock on the five-member arena at carrier `n`. -/
def symClock (n W : ℕ) : ℕ := (execC pB pF symCompactCom (sSt n W 5 10)).2

-- **carrier-blindness**: one arena, four carriers, one clock
#guard symClock 100 64 = 1714
#guard symClock 200 64 = 1714
#guard symClock 400 64 = 1714
#guard symClock 800 64 = 1714
-- and it fits the cost function at the arena's own two numbers
#guard symClock 800 64 ≤ symCompactCost 5 10

-- **the honesty direction, on the clock**: the pin is exact — one tick
-- less does not hold
#guard ¬ (symClock 800 64 ≤ 1713)

/-- The landed pass's clock on the same arena, padded to the carrier —
`OrderEngineProbe` §1's instrument at this family. -/
def symCarrierClock (n W : ℕ) : ℕ := (execC pB pF symCom (symCarrierSt n W)).2

-- **the class the wave kills**: the landed pass's clock is affine in the
-- CARRIER at the fixed arena — `115·n + 829` at four carriers spanning a
-- factor of eight
#guard symCarrierClock 100 64 = 115 * 100 + 829
#guard symCarrierClock 200 64 = 115 * 200 + 829
#guard symCarrierClock 400 64 = 115 * 400 + 829
#guard symCarrierClock 800 64 = 115 * 800 + 829

-- so at a large carrier the landed pass does not fit the arena-charged
-- budget and the compacted composite does, at the same arena
#guard ¬ (symCarrierClock 800 64 ≤ symCompactCost 5 10)
#guard symClock 800 64 ≤ symCompactCost 5 10
-- the gap grows with the carrier while this clock does not …
#guard symClock 800 64 * 50 ≤ symCarrierClock 800 64
-- … and the honesty direction on the comparison: the landed share does
-- NOT fit where this one does
#guard ¬ (symCarrierClock 800 64 ≤ symClock 800 64 * 50)

/-! ### §7.3 A sparser arena: the slot term is load-bearing

The honesty direction on the cost's *shape*. The same five members with a
sparser orientation — the star `K₁,₄` oriented into its centre, four arcs
instead of ten, the instance `TgtWidenProbe.sym5Zero` measures — clocks
strictly lower, so no slot-blind budget is uniform. -/

def symStarSt (n W : ℕ) : PSt :=
  { sSt n W 5 4 with
    arrs := ("ioff", [0, 4, 4, 4, 4, 4] ++ List.replicate (n + 1 - 6) 4) ::
      ("itg", [1, 2, 3, 4] ++ List.replicate (W - 4) 0) :: (sSt n W 5 4).arrs }

def symStarClock (n W : ℕ) : ℕ := (execC pB pF symCompactCom (symStarSt n W)).2

#guard (exec pB pF symCompactCom (symStarSt 100 64)).isOk
-- the star's union is eight slots where the `K₅` orientation's is twenty
#guard (List.range 6).map ((exec pB pF symCompactCom (symStarSt 100 64)).cell "off")
  = [0, 4, 5, 6, 7, 8]
#guard (List.range 8).map ((exec pB pF symCompactCom (symStarSt 100 64)).cell "tgt")
  = [1, 2, 3, 4, 0, 0, 0, 0]
-- the level's rows above the compact prefix come back here too
#guard (List.range 94).all fun k =>
  (exec pB pF symCompactCom (symStarSt 100 64)).cell "off" (6 + k) == 7
-- … the sparser arena clocks strictly lower …
#guard symStarClock 100 64 < symClock 100 64
-- … so the sparse arena's clock is NOT a bound for the dense one: a
-- budget read at the sparse arena's slot count is refuted on data
#guard ¬ (symClock 100 64 ≤ symStarClock 100 64)
#guard symStarClock 100 64 ≤ symCompactCost 5 4
-- … and it too is carrier-blind
#guard symStarClock 100 64 = symStarClock 800 64
#guard symStarClock 100 64 = 1174

/-! ### §7.4 The assembly

The one obligation, the walked carrier install, §4's transported engine,
and nothing else. -/

/-- **The compacted symmetrization implements the arena contract.** Read
the cost: `symCompactCost mm kd` — the arena's live vertex count and its
compact slot count, and **no carrier term**. And read the last clause:
the level's own offset array above the compact prefix comes back exactly,
which is `OrderEngineProbe` §3's restore-seam dead. -/
theorem symCompact_spec {B n mm nt W kd m : ℕ} {D : Orientation mm} {IO IT T₀ : ℕ → ℕ}
    {σ : Env} (h1 : SymPreps B n mm nt W kd)
    (hin : InCsr D m IO IT) (hmkd : m ≤ kd) (hkdW : kd ≤ W) (hfit : m + m ≤ nt)
    (hnB : n < B) (hB2 : m + m < B) (hmmB : mm + 1 < B) (hkdB : kd < B)
    (hIOB : ∀ i ≤ mm, IO i < B) (hITB : ∀ j < kd, IT j < B)
    (hent : SymEntryC n mm nt W kd IO IT T₀ σ) :
    ∃ σ'', Run B symCompactCore σ σ'' (symCompactCost mm kd) ∧
      SymMemPost mm nt m D T₀ σ'' ∧
      (σ''.arrs "off").drop (mm + 1) = (σ.arrs "off").drop (mm + 1) := by
  classical
  have hmn : mm ≤ n := hent.2.2.2.1
  obtain ⟨σ1, DT, r1, hn1, hmm1, hdtg1, hDT, hdoff1, hooff1, hofl1, hotg1, hoffE1, htgt1⟩ :=
    h1 IO IT T₀ σ hmmB hkdB hIOB hITB hent
  -- the block structure survives the prefix copy of the target array
  have hin' : InCsr D m IO DT :=
    Lax3Proofs.RamDriverAugment.inCsr_congr_prefix hin fun j hj => hDT j (by omega)
  -- the carrier install
  obtain ⟨σ2, r2, hpre2, -, -, harr2⟩ :=
    symSetCarrier_spec (B := B) (n := n) (mm := mm) (nt := nt) (W := W) (DO := IO) (DT := DT)
      (T₀ := T₀) hnB hn1 hmm1 hmn hdoff1 hdtg1 hooff1 hofl1 hotg1 hoffE1 htgt1
  -- the pass, at the arena's carrier
  obtain ⟨τ, K, O, T, r3, hK, hoff', htgt', hcsr, htail, htl, -⟩ :=
    symCompact_engine (m := m) (D := D) hmmB hB2 (hmkd.trans hkdW) hfit hin' hpre2
  have hs : Lax3Proofs.RamDriverAugment.symCost mm m ≤
      Lax3Proofs.RamDriverAugment.symCost mm kd := by
    simp only [Lax3Proofs.RamDriverAugment.symCost]; omega
  have hge : 200 ≤ Lax3Proofs.RamDriverAugment.symCost mm kd := by
    simp only [Lax3Proofs.RamDriverAugment.symCost]; omega
  refine ⟨padArrs τ (tailOf σ2 (symClen mm nt W)), (r1.seq (r2.seq r3)).mono ?_,
    ⟨O, T, ?_, ?_, hcsr, htail⟩, ?_⟩
  · rw [symCompactCost]; omega
  · intro i hi
    rw [getD_padArrs (by rw [hoff']; simpa [arrOf] using Nat.lt_succ_of_le hi), hoff',
      getD_arrOf O (Nat.lt_succ_of_le hi)]
  · have htlz : (σ2.arrs "tgt").drop (symClen mm nt W "tgt") = [] := by
      rw [symClen_tgt, harr2 "tgt", htgt1]
      exact List.drop_eq_nil_of_le (by simp [arrOf])
    rw [padArrs_arrs, tailOf, htlz, List.append_nil, htgt']
  · have hoffσ1 : σ1.arrs "off" = σ.arrs "off" :=
      r1.frame_arr "off" (notMem_symPrepCom_warrs (by decide) (by decide) (by decide))
    have hlen : symClen mm nt W "off" ≤ (σ2.arrs "off").length := by
      obtain ⟨g, hg⟩ := hoffE1
      rw [symClen_off, harr2 "off", hg, length_arrOf]
      omega
    have h := htl "off" hlen
    rw [symClen_off] at h
    rw [h, harr2 "off", hoffσ1]

/-! ## §8 What this family did *not* need

For the record, against the template's checklist (`ElimCompact` §9):

1. §3's semantics **imported verbatim** — `padArrs`, `cutArrs`,
   `tailOf`, `run_of_run_cutArrs`, `tail_preserved`, `take_arrOf`,
   `arrOf_congr`. Nothing about IMP+ is re-proved here.
2. **No re-synthesis.** `symCom`'s three passes are `"n"`-bounded and
   `symPass_run` is a theorem; the walk applies at `n := mm`.
3. **No scatter-back**, because the pass's output is a block structure
   and not a per-vertex answer: its consumer — the second compacted
   elimination — reads `off`/`tgt` at carrier `mm`.
4. **No save and no restore.** This is the family's own finding, and it
   is the sharpest form of the template's item 4: because every write is
   a prefix write of the compact view (§4, `symCompact_tail`), the
   level's own block structure needs no `saveCsr`/`restoreCsr` pair
   around this pass at all. `OrderEngineProbe` §3's restore-seam is not
   repaired here — it is *removed*.
5. **The mask clause is not re-authorised**, because `symCom` does not
   read `alv`: `masked_of_all_alive` is not needed in this family. The
   pass that follows it in the phase text (`fillCom "alv" (.lit 1)`)
   becomes `fillUpto "alv" (.var "mm") (.lit 1)` in the compacted design
   — arena-class, and `ElimCompact.installCom` already carries exactly
   that fill. -/

end Lax3Proofs.Refine.SymCompact
