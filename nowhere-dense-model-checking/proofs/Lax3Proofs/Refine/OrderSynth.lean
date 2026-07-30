import Lax3Proofs.Refine.ElimSynth3
import Lax3Proofs.RamCover
import Lax13Proofs.Refine.Sepref.Examples.WordAssnSpike

/-!
# ND-MC rebase P2 / satellite 2E — the ordering phase at `R = 0`,
re-derived through the refinement tower

`RamDriver.orderCom R W j` is the pass that gives a level its
elimination ordering. This file re-derives it at **`R = 0`** — the
setting the frozen target `RamDriverRoot.driverRoot_decides_sentence`
runs at, and the only one `RamDriverCompose.orderImplements₀` is stated
at. The `R > 0` phase is blocked on the `tgt` widening (`TgtCoupling`'s
K₁,₄) and is out of scope.

## 0. THE REDUCTION — what `orderCom 0 W j` actually is

`RamDriver.orderCom` is a twelve-command sequence. At `R = 0` the
augmentation fold `foldRange (fun _ => .seq RamAugment.augCom
(augRelinkCom W)) 0` is `Com.skip`, so **the round is not there at
all** — no `RamAugment.augCom`, no `augRelinkCom`, and therefore *no
counting sort anywhere in the phase*: the three counting sorts the
ordering phase is credited with (`outPass`, the prefix sums of
`fratPass` and of `asmPass`) all live inside `RamAugment` and are
reached only at `R > 0`. What remains, pass by pass, is

| # | command | shape |
|---|---|---|
| 1 | `copyUpto "off" "gof" (n+1)` | prefix copy |
| 2 | `copyUpto "tgt" "gtg" (m+m)` | prefix copy, runtime bound `ns` |
| 3 | `copyCom (alvName j) "alv"` | prefix copy at `n` |
| 4 | `RamElim.elimCom` | **the engine** |
| 5 | `copyUpto "ioff" "doff" (n+1)` | prefix copy (dead at `R = 0`) |
| 6 | `copyUpto "itg" "dtg" (.lit W)` | prefix copy (dead at `R = 0`) |
| 7 | `foldRange … 0` | **`Com.skip`** |
| 8 | `copyUpto "gof" "off" (n+1)`, `copyUpto "gtg" "tgt" (m+m)` | two prefix copies |
| 9 | `fillCom "alv" 1` | prefix fill at `1` |
| 10 | `elimRezeroCom` | two prefix fills at `0` (`elm`, `bh`) |
| 11 | `RamElim.elimCom` | **the engine, again** |
| 12 | `ordCom (ordName j)` | **the rank inversion** |
| 13 | `orderZeroCom` | eight prefix fills at `0` |

So the R = 0 ordering phase is **fifteen prefix copies and fills, two
elimination engines, and one rank inversion** — and of those, only the
rank inversion carries mathematics, because `OrderImplements`'
postcondition names no ordering in particular: it asks for *some* `π`
and `ord` with `ordName j = arrOf n ord` and `OrdersBy n π ord`. Passes
5, 6 and 8 are pure bookkeeping for a round that does not run; they are
derived anyway, because the phase pays for them.

Three abstract programs therefore cover the whole phase:

* `copyPass` — §2, fifteen… seven uses (1, 2, 3, 5, 6, 8×2);
* `fillPass` — §3, eleven uses (9, 10×2, 13×8);
* `ordPass` — §4, one use, and the only one with content.

## What is consumed rather than re-proved

`RamCover.rankPerm` / `ordersBy_rankPerm` — that an injective rank array
with its inverse *is* an ordering — is capital and is used, not
re-proved. `ElimSynth2`'s two devices (`while_pot_le`, `larr`) and
`ElimSynth3.elimLoop`/`elimSynth` are this campaign's own capital.

## Judgment calls

**2E/D-a — the elimination enters as a hypothesis, not as a leaf op.**
`RamDriver.OrderImplements` takes `ElimAvail B n` as a *hypothesis*: the
phase does not own the engine, it calls it. The tower phase is stated
the same way — `ElimAvailA` (§6) is the abstract-layer `ElimAvail`, and
`orderPhase0_le` consumes it. The reason this is the right shape and not
an evasion: satellite 2B′ synthesized the elimination's five passes
*separately* (`degScanSynth`, `buckSynth`, `offSynth`, `fillSynth`,
`elimSynth`) and never assembled them into one program, so there is no
single `Com` for the engine to wrap. §6 registers the loop that *is*
synthesized (`mopElim`) as a leaf operation by the `mopBfsE` idiom, and
§7 runs the phase's load-bearing composition — engine-then-inversion —
through the tool to show the seam is open.

**2E/D-b — the inversion loses the machine's nested store.** The
machine writes `.store dst (.get "rnk" (.var "z")) (.var "z")`, one
instruction with a read nested in the index. The IR has no nested
operand, so `ordPass` is `aget` then `aset`: one extra cell (`"rz"`) and
one extra time unit per vertex. The value is identical (§4's twin), and
the cost difference is in §8's table.

**2E/D-c — the prefix bound is a cell, not a length.** Every pass of the
phase runs to a bound (`n + 1`, `ns`, `n`, `W`) that is *smaller* than
the array it writes in at least one use (`copyUpto "itg" "dtg" (.lit W)`
copies `W` of `itg`'s `ns` cells). So neither pass can be
`BfsQ.fillLoop`, whose specification pins `D.length = n`; both take the
bound as a parameter and state what happens **above** it, which is what
the phase's frame conditions need (`OrderImplements` asks for `LevelPre`
back, and `LevelPre` speaks about every cell).

## House traps observed

`omega` is blind through `Ir.Val`, so every arithmetic obligation is
bound at `ℕ` first; `decide +kernel` for the cost numerals; never
`simp [Codegen.embed]`; junk cells are consumed in written order; loop
states are assembled with `mopPair`, never as literal tuples (P4/D-m).
-/

namespace Lax3Proofs.Refine.OrderSynth

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Sepref.WordSpike
open Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax13Proofs.Refine.Codegen
open Lax13Proofs.Refine.BfsQ (cu iter irWhile_exit get!_set liftACost_cu)
open Lax3Proofs.Refine.ElimSynth2 (larr larr_apply larr_set while_pot_le step_spec)

/-! ## 1. Refute before prove

The three passes as computable functions, run to their ends, and the
answers pinned against the phase's own arithmetic — and, in §5, against
`Ir.evalFuel`'s reading of the *synthesized* programs.

The hot spots, and where each is checked:

* **the bound is a prefix bound** — a pass that ran to the array's
  length instead of to its bound overwrites the tail the phase's frame
  conditions promise to leave alone. Every twin below is checked on an
  array strictly longer than its bound.
* **the inversion is the inverse, not the identity** — `ordCom` writes
  `ord[rnk[z]] := z`; writing `ord[z] := rnk[z]` gives the same answer
  exactly when the rank array is an involution, and the demo's second
  rank array is not one. Checked against `RamElim.Demo`'s own published
  ranks, through `ElimSynth`'s twin of the engine.
* **the inversion needs injectivity** — on a non-injective rank array
  the pass silently drops a vertex. The negative control exhibits it.
-/

section Twin

/-- The state of every pass here: the array being written and the
counter. -/
abbrev FS : Type := List ℕ × ℕ

/-- One cell of a fill. -/
def fillTw (v : ℕ) : FS → FS := fun s => (s.1.set s.2 v, s.2 + 1)

/-- One cell of a copy. -/
def copyTw (src : List ℕ) : FS → FS := fun s => (s.1.set s.2 src[s.2]!, s.2 + 1)

/-- One vertex of the rank inversion. -/
def ordTw (rnk : List ℕ) : FS → FS := fun s => (s.1.set rnk[s.2]! s.2, s.2 + 1)

/-- A pass, run to its bound. -/
def runTw (step : FS → FS) (N : ℕ) : ℕ → FS → FS
  | 0, s => s
  | fuel + 1, s => if s.2 < N then runTw step N fuel (step s) else s

/-- The fill, run. -/
def fillRun (N v : ℕ) (A : List ℕ) : List ℕ := (runTw (fillTw v) N (N + 1) (A, 0)).1

/-- The copy, run. -/
def copyRun (N : ℕ) (src A : List ℕ) : List ℕ := (runTw (copyTw src) N (N + 1) (A, 0)).1

/-- The inversion, run. -/
def ordRun (n : ℕ) (rnk A : List ℕ) : List ℕ := (runTw (ordTw rnk) n (n + 1) (A, 0)).1

-- **The bound is a prefix bound.** Three cells of a five-cell array,
-- and the tail is the caller's.
#guard fillRun 3 0 [7, 7, 7, 7, 7] = [0, 0, 0, 7, 7]
#guard copyRun 3 [1, 2, 3, 4, 5] [9, 9, 9, 9, 9] = [1, 2, 3, 9, 9]

-- **The rank inversion on `RamElim.Demo`'s own answers**, taken through
-- `ElimSynth`'s twin of the engine — which is itself pinned against the
-- *compiled machine program*'s published readings. Mask on, the ranks
-- are the identity and so is the order.
#guard (ElimSynth.demoTw 1).rnk = [0, 1, 2, 3, 4]
#guard ordRun 5 (ElimSynth.demoTw 1).rnk (List.replicate 5 0) = [0, 1, 2, 3, 4]

-- Mask off at vertex `2`: the ranks are `0 1 4 2 3` and the order is
-- their **inverse**, `0 1 3 4 2`.
#guard (ElimSynth.demoTw 0).rnk = [0, 1, 4, 2, 3]
#guard ordRun 5 (ElimSynth.demoTw 0).rnk (List.replicate 5 0) = [0, 1, 3, 4, 2]

/-! ### Negative controls -/

-- **The inversion is not the identity map on the array.** Writing
-- `ord[z] := rnk[z]` would give the rank array back; on the demo's
-- second run it does not.
#guard ordRun 5 (ElimSynth.demoTw 0).rnk (List.replicate 5 0)
  ≠ (ElimSynth.demoTw 0).rnk

-- **Composed with the ranks, the order is the identity** — which is
-- what `OrdersBy` says and what the proof of §4 delivers.
#guard (List.range 5).map
    (fun v => (ordRun 5 (ElimSynth.demoTw 0).rnk (List.replicate 5 0))[
      (ElimSynth.demoTw 0).rnk[v]!]!) = [0, 1, 2, 3, 4]

-- **Injectivity is load-bearing.** A rank array that names position `1`
-- twice loses a vertex: position `2` is never written, and the `0` the
-- pass leaves there is not a vertex it put there.
#guard ordRun 3 [1, 1, 0] [9, 9, 9] = [2, 1, 9]

-- **The fill really writes.** A pass that stopped at zero would leave
-- the array alone, and the check can tell.
#guard fillRun 3 0 [7, 7, 7, 7, 7] ≠ [7, 7, 7, 7, 7]

end Twin

/-! ## 2. The prefix copy

`RamDriver.copyUpto src dst bnd` at the abstract layer: read a cell of
the source, write it at the same index of the destination, bump the
counter. Seven of the phase's commands are this program.

The specification states the destination **cell by cell**, below the
bound and above it, because the phase's frame conditions
(`RamDriver.LevelPre` at the exit) speak about every cell of every
array the phase touches. -/

section Copy

/-- What one cell of the copy needs in range. -/
def copyP (src : List ℕ) : FS → Prop := fun s => s.2 < src.length ∧ s.2 < s.1.length

/-- The pass's guard. -/
def copyBf (N : ℕ) : FS → Bool := fun s => decide (s.2 < N)

/-- **One cell.** -/
noncomputable def copyF (src : List ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAget src s.2) fun u =>
    bindT (mopAset s.1 s.2 u) fun A =>
      bindT (mopSucc s.2) fun i => mopPair A i

/-- **The prefix copy.** -/
noncomputable def copyPass (N : ℕ) (src : List ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun s => copyBf N s = true → copyP src s) (copyBf N) (copyF src) s₀

/-- One cell's price: a read, a write, a bump, the pair. -/
def copyC : ACost String ℕ :=
  cu Currency.aget + cu Currency.aset + cu Currency.add + cu Currency.skip

theorem copyF_le (src : List ℕ) (s : FS) (h : copyP src s) :
    copyF src s ≤ NRest.consume (NRest.returnT (copyTw src s)) (liftACost copyC) := by
  refine le_of_eq ?_
  obtain ⟨h1, h2⟩ := h
  simp only [copyF, copyTw, mopAget_def, mopAset_def, mopSucc_eq, mopBinop_def,
    mopPair_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.returnT_bindT,
    NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, copyC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

/-- The copy's invariant: the lengths, the counter, and the destination
read cell by cell against the source below the counter and against its
own entry value above it. -/
def copyI (N L : ℕ) (src A₀ : List ℕ) : FS → Prop := fun s =>
  s.1.length = L ∧ N ≤ L ∧ N ≤ src.length ∧ s.2 ≤ N ∧
    ∀ j, s.1[j]! = if j < s.2 then src[j]! else A₀[j]!

theorem copyI_range {N L : ℕ} {src A₀ : List ℕ} {s : FS} (hI : copyI N L src A₀ s)
    (hb : copyBf N s = true) : copyP src s := by
  obtain ⟨h1, h2, h3, -, -⟩ := hI
  have hi : s.2 < N := by simpa [copyBf] using hb
  exact ⟨by omega, by omega⟩

theorem copyI_step {N L : ℕ} {src A₀ : List ℕ} {s : FS} (hI : copyI N L src A₀ s)
    (hb : copyBf N s = true) : copyI N L src A₀ (copyTw src s) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  have hi : s.2 < N := by simpa [copyBf] using hb
  simp only [copyI, copyTw]
  refine ⟨by simpa using h1, h2, h3, by omega, fun j => ?_⟩
  rw [get!_set _ _ _ _ (show s.2 < s.1.length by omega)]
  by_cases hj : j = s.2
  · subst hj; rw [if_pos rfl, if_pos (by omega)]
  · rw [if_neg hj, h5 j]
    by_cases hlt : j < s.2
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

theorem copyPass_le {N L : ℕ} {src A₀ : List ℕ} :
    ∀ (fuel : ℕ) (s : FS), copyI N L src A₀ s → N - s.2 < fuel →
      copyPass N src s
        ≤ NRest.spec (fun t => copyI N L src A₀ t ∧ copyBf N t = false)
            (fun _ => liftACost ((N - s.2) • iter copyC + cu Currency.«while»)) :=
  while_pot_le (P := copyP src) (V := fun s => N - s.2)
    (Φ := fun s => (N - s.2) • iter copyC) (Φ' := fun s => (N - (s.2 + 1)) • iter copyC)
    (C := fun _ => copyC) (fun _ h hb => copyI_range h hb)
    (fun s h hb => by
      have hi : s.2 < N := by simpa [copyBf] using hb
      exact step_spec (s := s) (x := copyTw src s) (C := fun _ => copyC)
        (Φ := fun s => (N - s.2) • iter copyC) (Φ' := fun s => (N - (s.2 + 1)) • iter copyC)
        (V := fun s => N - s.2) (copyF_le src s (copyI_range h hb)) (copyI_step h hb)
        (by show N - (s.2 + 1) < N - s.2; omega) le_rfl)
    (fun s _ hb => by
      have hi : s.2 < N := by simpa [copyBf] using hb
      show iter copyC + (N - (s.2 + 1)) • iter copyC ≤ (N - s.2) • iter copyC
      rw [show N - s.2 = (N - (s.2 + 1)) + 1 by omega, succ_nsmul]
      exact le_of_eq (by ac_rfl))

/-- **The prefix copy's export.** Below the bound the destination is the
source; above it, it is what the caller left there. -/
theorem copyPass_spec {N L : ℕ} {src A₀ : List ℕ} (hA : A₀.length = L) (hNL : N ≤ L)
    (hNs : N ≤ src.length) :
    copyPass N src (A₀, 0)
      ≤ NRest.spec
          (fun t : FS => t.1.length = L ∧
            ∀ j, t.1[j]! = if j < N then src[j]! else A₀[j]!)
          (fun _ => liftACost (N • iter copyC + cu Currency.«while»)) := by
  refine le_trans (copyPass_le (N := N) (L := L) (src := src) (A₀ := A₀) (N + 1) (A₀, 0)
    ⟨hA, hNL, hNs, Nat.zero_le _, fun j => by simp⟩ (by simp))
    (spec_mono ?_ (fun _ _ => by simp))
  rintro t ⟨⟨t1, -, -, t4, t5⟩, hbf⟩
  have hti : t.2 = N := by
    have : ¬ t.2 < N := by simpa [copyBf] using hbf
    omega
  exact ⟨t1, by rw [← hti]; exact t5⟩

end Copy

/-! ## 3. The prefix fill

`RamDriver.fillUpto a bnd (.lit v)` — and `fillCom a v`, which is the
same program at the array's own length. Eleven of the phase's commands
are this one: the mask set to `1` before the second elimination, the two
fills of `elimRezeroCom`, and the eight of `orderZeroCom`. -/

section Fill

/-- What one cell of the fill needs in range. -/
def fillP : FS → Prop := fun s => s.2 < s.1.length

/-- The pass's guard. -/
def fillBf (N : ℕ) : FS → Bool := fun s => decide (s.2 < N)

/-- **One cell.** The value rides in its own cell — the machine's
`.lit v` is the tower's `hnCtxt natAssn v`, since the IR's `aset` takes
three cells and no literal. -/
noncomputable def fillF (v : ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAset s.1 s.2 v) fun A =>
    bindT (mopSucc s.2) fun i => mopPair A i

/-- **The prefix fill.** -/
noncomputable def fillPass (N v : ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun s => fillBf N s = true → fillP s) (fillBf N) (fillF v) s₀

/-- One cell's price: a write, a bump, the pair. -/
def fillC : ACost String ℕ := cu Currency.aset + cu Currency.add + cu Currency.skip

theorem fillF_le (v : ℕ) (s : FS) (h : fillP s) :
    fillF v s ≤ NRest.consume (NRest.returnT (fillTw v s)) (liftACost fillC) := by
  refine le_of_eq ?_
  have h1 : s.2 < s.1.length := h
  simp only [fillF, fillTw, mopAset_def, mopSucc_eq, mopBinop_def, mopPair_def,
    NRest.assert_pos h1, NRest.returnT_bindT,
    NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, fillC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

/-- The fill's invariant. -/
def fillI (N v L : ℕ) (A₀ : List ℕ) : FS → Prop := fun s =>
  s.1.length = L ∧ N ≤ L ∧ s.2 ≤ N ∧ ∀ j, s.1[j]! = if j < s.2 then v else A₀[j]!

theorem fillI_range {N v L : ℕ} {A₀ : List ℕ} {s : FS} (hI : fillI N v L A₀ s)
    (hb : fillBf N s = true) : fillP s := by
  obtain ⟨h1, h2, -, -⟩ := hI
  have hi : s.2 < N := by simpa [fillBf] using hb
  show s.2 < s.1.length
  omega

theorem fillI_step {N v L : ℕ} {A₀ : List ℕ} {s : FS} (hI : fillI N v L A₀ s)
    (hb : fillBf N s = true) : fillI N v L A₀ (fillTw v s) := by
  obtain ⟨h1, h2, h3, h4⟩ := hI
  have hi : s.2 < N := by simpa [fillBf] using hb
  simp only [fillI, fillTw]
  refine ⟨by simpa using h1, h2, by omega, fun j => ?_⟩
  rw [get!_set _ _ _ _ (show s.2 < s.1.length by omega)]
  by_cases hj : j = s.2
  · subst hj; rw [if_pos rfl, if_pos (by omega)]
  · rw [if_neg hj, h4 j]
    by_cases hlt : j < s.2
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

theorem fillPass_le {N v L : ℕ} {A₀ : List ℕ} :
    ∀ (fuel : ℕ) (s : FS), fillI N v L A₀ s → N - s.2 < fuel →
      fillPass N v s
        ≤ NRest.spec (fun t => fillI N v L A₀ t ∧ fillBf N t = false)
            (fun _ => liftACost ((N - s.2) • iter fillC + cu Currency.«while»)) :=
  while_pot_le (P := fillP) (V := fun s => N - s.2)
    (Φ := fun s => (N - s.2) • iter fillC) (Φ' := fun s => (N - (s.2 + 1)) • iter fillC)
    (C := fun _ => fillC) (fun _ h hb => fillI_range h hb)
    (fun s h hb => by
      have hi : s.2 < N := by simpa [fillBf] using hb
      exact step_spec (s := s) (x := fillTw v s) (C := fun _ => fillC)
        (Φ := fun s => (N - s.2) • iter fillC) (Φ' := fun s => (N - (s.2 + 1)) • iter fillC)
        (V := fun s => N - s.2) (fillF_le v s (fillI_range h hb)) (fillI_step h hb)
        (by show N - (s.2 + 1) < N - s.2; omega) le_rfl)
    (fun s _ hb => by
      have hi : s.2 < N := by simpa [fillBf] using hb
      show iter fillC + (N - (s.2 + 1)) • iter fillC ≤ (N - s.2) • iter fillC
      rw [show N - s.2 = (N - (s.2 + 1)) + 1 by omega, succ_nsmul]
      exact le_of_eq (by ac_rfl))

/-- **The prefix fill's export.** -/
theorem fillPass_spec {N v L : ℕ} {A₀ : List ℕ} (hA : A₀.length = L) (hNL : N ≤ L) :
    fillPass N v (A₀, 0)
      ≤ NRest.spec
          (fun t : FS => t.1.length = L ∧ ∀ j, t.1[j]! = if j < N then v else A₀[j]!)
          (fun _ => liftACost (N • iter fillC + cu Currency.«while»)) := by
  refine le_trans (fillPass_le (N := N) (v := v) (L := L) (A₀ := A₀) (N + 1) (A₀, 0)
    ⟨hA, hNL, Nat.zero_le _, fun j => by simp⟩ (by simp))
    (spec_mono ?_ (fun _ _ => by simp))
  rintro t ⟨⟨t1, -, t3, t4⟩, hbf⟩
  have hti : t.2 = N := by
    have : ¬ t.2 < N := by simpa [fillBf] using hbf
    omega
  exact ⟨t1, by rw [← hti]; exact t4⟩

end Fill

/-! ## 4. The rank inversion — the phase's one piece of mathematics

`RamDriver.ordCom dst`: `ord[rnk[z]] := z` for every vertex. What it
computes is the inverse of the rank array, and what
`RamDriver.OrderImplements` asks for is that this inverse *is* an
ordering — `RamCover.OrdersBy n π ord` for some `π`. The bridge is
`RamCover.rankPerm`, consumed. -/

section Ord

/-- **An injection of an initial segment into itself is onto.** Restated
here rather than imported (`RamDriverOrder.exists_preimage_of_inj` is
the same statement in the machine layer's file, which this one does not
depend on). -/
theorem exists_preimage {n : ℕ} {R : ℕ → ℕ} (hR : ∀ v < n, R v < n)
    (hinj : ∀ v < n, ∀ w < n, R v = R w → v = w) {c : ℕ} (hc : c < n) : ∃ v < n, R v = c := by
  have hsub : (Finset.range n).image R ⊆ Finset.range n := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_range.2 (hR v (Finset.mem_range.1 hv))
  have hcard : ((Finset.range n).image R).card = n := by
    rw [Finset.card_image_of_injOn (fun v hv w hw h =>
      hinj v (by simpa using hv) w (by simpa using hw) h), Finset.card_range]
  have himg : (Finset.range n).image R = Finset.range n :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
  have hmem : c ∈ (Finset.range n).image R := by rw [himg]; exact Finset.mem_range.2 hc
  obtain ⟨v, hv, hvc⟩ := Finset.mem_image.1 hmem
  exact ⟨v, Finset.mem_range.1 hv, hvc⟩

/-- What one vertex of the inversion needs in range: the counter is a
vertex, and the rank it reads names a position of the order array. -/
def ordP (rnk : List ℕ) : FS → Prop := fun s => s.2 < rnk.length ∧ rnk[s.2]! < s.1.length

/-- The pass's guard. -/
def ordBf (n : ℕ) : FS → Bool := fun s => decide (s.2 < n)

/-- **One vertex.** 2E/D-b: the machine's nested store is two IR
operations. -/
noncomputable def ordF (rnk : List ℕ) : FS → NRest FS ECost := fun s =>
  bindT (mopAget rnk s.2) fun r =>
    bindT (mopAset s.1 r s.2) fun A =>
      bindT (mopSucc s.2) fun i => mopPair A i

/-- **The rank inversion.** -/
noncomputable def ordPass (n : ℕ) (rnk : List ℕ) (s₀ : FS) : NRest FS ECost :=
  irWhileIT (fun s => ordBf n s = true → ordP rnk s) (ordBf n) (ordF rnk) s₀

/-- One vertex's price — the same account as a copy's cell. -/
def ordC : ACost String ℕ :=
  cu Currency.aget + cu Currency.aset + cu Currency.add + cu Currency.skip

theorem ordF_le (rnk : List ℕ) (s : FS) (h : ordP rnk s) :
    ordF rnk s ≤ NRest.consume (NRest.returnT (ordTw rnk s)) (liftACost ordC) := by
  refine le_of_eq ?_
  obtain ⟨h1, h2⟩ := h
  simp only [ordF, ordTw, mopAget_def, mopAset_def, mopSucc_eq, mopBinop_def,
    mopPair_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.returnT_bindT,
    NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, ordC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

/-- The inversion's invariant: the vertices below the counter have been
put at their positions. -/
def ordI (n L : ℕ) (rnk : List ℕ) : FS → Prop := fun s =>
  s.1.length = L ∧ n ≤ L ∧ rnk.length = n ∧ s.2 ≤ n ∧ ∀ v < s.2, s.1[rnk[v]!]! = v

variable {n L : ℕ} {rnk : List ℕ}

theorem ordI_range (hR : ∀ v < n, rnk[v]! < n) {s : FS} (hI : ordI n L rnk s)
    (hb : ordBf n s = true) : ordP rnk s := by
  obtain ⟨h1, h2, h3, -, -⟩ := hI
  have hi : s.2 < n := by simpa [ordBf] using hb
  exact ⟨by omega, by have := hR _ hi; omega⟩

theorem ordI_step (hR : ∀ v < n, rnk[v]! < n)
    (hinj : ∀ v < n, ∀ w < n, rnk[v]! = rnk[w]! → v = w) {s : FS} (hI : ordI n L rnk s)
    (hb : ordBf n s = true) : ordI n L rnk (ordTw rnk s) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  have hi : s.2 < n := by simpa [ordBf] using hb
  have hlt : rnk[s.2]! < s.1.length := by have := hR _ hi; omega
  simp only [ordI, ordTw]
  refine ⟨by simpa using h1, h2, h3, by omega, fun v hv => ?_⟩
  rw [get!_set _ _ _ _ hlt]
  by_cases hveq : v = s.2
  · subst hveq; rw [if_pos rfl]
  · have hvlt : v < s.2 := by omega
    rw [if_neg (fun hc => hveq (hinj v (by omega) _ hi hc)), h5 v hvlt]

theorem ordPass_le (hR : ∀ v < n, rnk[v]! < n)
    (hinj : ∀ v < n, ∀ w < n, rnk[v]! = rnk[w]! → v = w) :
    ∀ (fuel : ℕ) (s : FS), ordI n L rnk s → n - s.2 < fuel →
      ordPass n rnk s
        ≤ NRest.spec (fun t => ordI n L rnk t ∧ ordBf n t = false)
            (fun _ => liftACost ((n - s.2) • iter ordC + cu Currency.«while»)) :=
  while_pot_le (P := ordP rnk) (V := fun s => n - s.2)
    (Φ := fun s => (n - s.2) • iter ordC) (Φ' := fun s => (n - (s.2 + 1)) • iter ordC)
    (C := fun _ => ordC) (fun _ h hb => ordI_range hR h hb)
    (fun s h hb => by
      have hi : s.2 < n := by simpa [ordBf] using hb
      exact step_spec (s := s) (x := ordTw rnk s) (C := fun _ => ordC)
        (Φ := fun s => (n - s.2) • iter ordC) (Φ' := fun s => (n - (s.2 + 1)) • iter ordC)
        (V := fun s => n - s.2) (ordF_le rnk s (ordI_range hR h hb))
        (ordI_step hR hinj h hb) (by show n - (s.2 + 1) < n - s.2; omega) le_rfl)
    (fun s _ hb => by
      have hi : s.2 < n := by simpa [ordBf] using hb
      show iter ordC + (n - (s.2 + 1)) • iter ordC ≤ (n - s.2) • iter ordC
      rw [show n - s.2 = (n - (s.2 + 1)) + 1 by omega, succ_nsmul]
      exact le_of_eq (by ac_rfl))

/-- **The rank inversion's export — the phase's postcondition.** From an
injective rank array bounded by the carrier, the pass leaves an array
that `RamCover.OrdersBy` some permutation: exactly the existential
`RamDriver.OrderImplements` asks for. -/
theorem ordPass_spec {A₀ : List ℕ} (hA : A₀.length = n) (hr : rnk.length = n)
    (hR : ∀ v < n, rnk[v]! < n)
    (hinj : ∀ v < n, ∀ w < n, rnk[v]! = rnk[w]! → v = w) :
    ordPass n rnk (A₀, 0)
      ≤ NRest.spec
          (fun t : FS => t.1.length = n ∧
            ∃ π : Equiv.Perm (Fin n), RamCover.OrdersBy n π (larr t.1))
          (fun _ => liftACost (n • iter ordC + cu Currency.«while»)) := by
  refine le_trans (ordPass_le (L := n) hR hinj (n + 1) (A₀, 0)
    ⟨hA, le_rfl, hr, Nat.zero_le _, fun v hv => absurd hv (by simp)⟩ (by simp))
    (spec_mono ?_ (fun _ _ => by simp))
  rintro t ⟨⟨t1, -, -, t4, t5⟩, hbf⟩
  have hti : t.2 = n := by
    have : ¬ t.2 < n := by simpa [ordBf] using hbf
    omega
  rw [hti] at t5
  refine ⟨t1, ?_⟩
  have hoR : ∀ v < n, larr t.1 (larr rnk v) = v := fun v hv => t5 v hv
  have hord : ∀ c < n, larr t.1 c < n := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := exists_preimage (R := larr rnk) hR hinj hc
    rw [hoR v hv]; exact hv
  have hRo : ∀ c < n, larr rnk (larr t.1 c) = c := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := exists_preimage (R := larr rnk) hR hinj hc
    rw [hoR v hv]
  exact ⟨RamCover.rankPerm n (larr rnk) (larr t.1) hR hord hRo hoR,
    RamCover.ordersBy_rankPerm n (larr rnk) (larr t.1) hR hord hRo hoR⟩

end Ord

/-! ## 5. The three passes, synthesized -/

section Synth

set_option maxHeartbeats 1000000 in
sepref_synth copySynth (N : ℕ) (src A₀ : List ℕ) (i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("cpd", "cpi") ∗
      hnCtxt arrayAssn src "cps" ∗ hnCtxt natAssn N "cpn" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "cpu")
    _ _ ("cpd", "cpi") (arrayAssn ×ₐ natAssn)
    (copyPass N src (A₀, i₀))

set_option maxHeartbeats 1000000 in
sepref_synth fillSynth (N v : ℕ) (A₀ : List ℕ) (i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("fla", "fli") ∗
      hnCtxt natAssn v "flv" ∗ hnCtxt natAssn N "fln" ∗ hnCtxt natAssn 1 "one")
    _ _ ("fla", "fli") (arrayAssn ×ₐ natAssn)
    (fillPass N v (A₀, i₀))

set_option maxHeartbeats 1000000 in
sepref_synth ordSynth (n : ℕ) (rnk A₀ : List ℕ) (z₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, z₀) ("ord", "z") ∗
      hnCtxt arrayAssn rnk "rnk" ∗ hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "rz")
    _ _ ("ord", "z") (arrayAssn ×ₐ natAssn)
    (ordPass n rnk (A₀, z₀))

-- **The prefix copy, pinned**: `RamDriver.copyUpto`'s body — the read,
-- the write, the bump — instruction for instruction, the machine's
-- nested `.get` inside `.store` split into `aget` + `aset` (2E/D-b).
#guard copySynth_impl =
  Com.while (Cond.lt (Operand.cell "cpi") (Operand.cell "cpn"))
    ((Com.aget "cpu" "cps" "cpi").seq
      ((Com.aset "cpd" "cpi" "cpu").seq
        ((Com.binop Lax13Proofs.Imp.Bop.add "cpi" "cpi" "one").seq Com.skip)))

-- **The prefix fill, pinned**: `RamDriver.fillUpto` at a literal, with
-- the literal in a cell (`"flv"`).
#guard fillSynth_impl =
  Com.while (Cond.lt (Operand.cell "fli") (Operand.cell "fln"))
    ((Com.aset "fla" "fli" "flv").seq
      ((Com.binop Lax13Proofs.Imp.Bop.add "fli" "fli" "one").seq Com.skip))

-- **The rank inversion, pinned**: `RamDriver.ordCom`'s loop, at the
-- machine's own cell names `"z"`, `"n"`, `"rnk"`.
#guard ordSynth_impl =
  Com.while (Cond.lt (Operand.cell "z") (Operand.cell "n"))
    ((Com.aget "rz" "rnk" "z").seq
      ((Com.aset "ord" "rz" "z").seq
        ((Com.binop Lax13Proofs.Imp.Bop.add "z" "z" "one").seq Com.skip)))

-- **Negative control on the pin.** The inversion indexes the *order*
-- array by the rank and stores the counter; the transposition — index
-- by the counter, store the rank — is the identity map on the array
-- and is a different program.
#guard ordSynth_impl ≠
  Com.while (Cond.lt (Operand.cell "z") (Operand.cell "n"))
    ((Com.aget "rz" "rnk" "z").seq
      ((Com.aset "ord" "z" "rz").seq
        ((Com.binop Lax13Proofs.Imp.Bop.add "z" "z" "one").seq Com.skip)))

/-- info: 'Lax3Proofs.Refine.OrderSynth.copySynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms copySynth

/-- info: 'Lax3Proofs.Refine.OrderSynth.fillSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms fillSynth

/-- info: 'Lax3Proofs.Refine.OrderSynth.ordSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ordSynth

/-- The prefix copy's synthesis with the frame the tool computed left
existential. -/
theorem copySynth' (N : ℕ) (src A₀ : List ℕ) (i₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("cpd", "cpi") ∗
        hnCtxt arrayAssn src "cps" ∗ hnCtxt natAssn N "cpn" ∗ hnCtxt natAssn 1 "one" ∗
        junkCell "cpu")
      copySynth_impl Γ' ("cpd", "cpi") (arrayAssn ×ₐ natAssn) (copyPass N src (A₀, i₀)) :=
  ⟨_, copySynth N src A₀ i₀⟩

/-- The prefix fill's. -/
theorem fillSynth' (N v : ℕ) (A₀ : List ℕ) (i₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("fla", "fli") ∗
        hnCtxt natAssn v "flv" ∗ hnCtxt natAssn N "fln" ∗ hnCtxt natAssn 1 "one")
      fillSynth_impl Γ' ("fla", "fli") (arrayAssn ×ₐ natAssn) (fillPass N v (A₀, i₀)) :=
  ⟨_, fillSynth N v A₀ i₀⟩

/-- The rank inversion's. -/
theorem ordSynth' (n : ℕ) (rnk A₀ : List ℕ) (z₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, z₀) ("ord", "z") ∗
        hnCtxt arrayAssn rnk "rnk" ∗ hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗
        junkCell "rz")
      ordSynth_impl Γ' ("ord", "z") (arrayAssn ×ₐ natAssn) (ordPass n rnk (A₀, z₀)) :=
  ⟨_, ordSynth n rnk A₀ z₀⟩

end Synth

/-! ## 6. Gate — the *synthesized* programs, run

`Ir/Semantics.lean`'s evaluator on the three programs of §5, at the
`RamElim.Demo` arena's own published rank arrays for the inversion and
at a five-cell array with a three-cell bound for the two bookkeeping
passes. Every answer is the twin's answer of §1, and the twin's answers
are the machine's. -/

section Gate

/-- The inversion's entry store: the demo's ranks, an empty order array,
the counter and the scratch cell at zero. -/
def oState (rnk : List ℕ) : Ir.State :=
  Ir.State.ofPairs [("z", 0), ("n", 5), ("one", 1), ("rz", 0)]
    [("ord", List.replicate 5 0), ("rnk", rnk)]

/-- The order array the synthesized inversion leaves. -/
def oRun (rnk : List ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 ordSynth_impl (oState rnk)).bind fun p => p.1.arrs "ord"

-- mask on: the ranks are the identity and so is the order
#guard oRun (ElimSynth.demoTw 1).rnk = some [0, 1, 2, 3, 4]
-- mask off at vertex `2`: the order is the ranks' **inverse**
#guard oRun (ElimSynth.demoTw 0).rnk = some [0, 1, 3, 4, 2]

/-- The copy's entry store: a three-cell bound in a five-cell array. -/
def cState : Ir.State :=
  Ir.State.ofPairs [("cpi", 0), ("cpn", 3), ("one", 1), ("cpu", 0)]
    [("cpd", [9, 9, 9, 9, 9]), ("cps", [1, 2, 3, 4, 5])]

def cRun : Option (List ℕ) :=
  (Ir.evalFuel 20000 copySynth_impl cState).bind fun p => p.1.arrs "cpd"

/-- The fill's, at the value zero. -/
def fState (v : ℕ) : Ir.State :=
  Ir.State.ofPairs [("fli", 0), ("fln", 3), ("flv", v), ("one", 1)]
    [("fla", [7, 7, 7, 7, 7])]

def fRun (v : ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 20000 fillSynth_impl (fState v)).bind fun p => p.1.arrs "fla"

-- **The bound is a prefix bound**, in the synthesized program too
#guard cRun = some [1, 2, 3, 9, 9]
#guard fRun 0 = some [0, 0, 0, 7, 7]
#guard fRun 1 = some [1, 1, 1, 7, 7]

/-! ### Negative controls -/

-- **The tail is not overwritten.** A pass that ran to the array's
-- length would report this, and it does not.
/--
error: Expression
  decide (cRun = some [1, 2, 3, 4, 5])
did not evaluate to `true`
-/
#guard_msgs in
#guard cRun = some [1, 2, 3, 4, 5]

-- **The inversion is not the rank array.** On the demo's second run the
-- two differ, so a program that stored `rnk[z]` at `z` would be caught.
/--
error: Expression
  decide (oRun (ElimSynth.demoTw 0).rnk = some [0, 1, 4, 2, 3])
did not evaluate to `true`
-/
#guard_msgs in
#guard oRun (ElimSynth.demoTw 0).rnk = some [0, 1, 4, 2, 3]

-- **The twin is the program.** Both readings of §1 are reproduced by
-- the evaluator, cell for cell.
#guard oRun (ElimSynth.demoTw 0).rnk
  = some (ordRun 5 (ElimSynth.demoTw 0).rnk (List.replicate 5 0))
#guard cRun = some (copyRun 3 [1, 2, 3, 4, 5] [9, 9, 9, 9, 9])
#guard fRun 0 = some (fillRun 3 0 [7, 7, 7, 7, 7])

end Gate

/-! ## 7. The phase, composed at `R = 0`

The twenty-one abstract programs of §0's table, in the program's own
order, with the two eliminations entering as `ElimAvailA` — the
abstract-layer `RamDriver.ElimAvail` (2E/D-a). What comes out is the
existential `RamDriver.OrderImplements` asks for. -/

section Phase

/-- **What the phase reads of an elimination.** The rank array it
inverts, the two scratch arrays it re-zeroes afterwards, and the in-list
block structure the (absent) augmentation round would have taken. At
`R = 0` the last two are copied and never read, which is why they carry
lengths and nothing else. -/
abbrev ElimOut : Type := List ℕ × List ℕ × List ℕ × List ℕ × List ℕ

/-- The elimination's postcondition, at the phase's boundary: the
lengths, and the two clauses the rank inversion needs — the ranks are
positions, and no two vertices share one. These are
`RamElim.Elim.rank_lt` and the injectivity `RamElim.Elim.cert` carries;
2B′'s debt E2 is the transport of the loop's invariant to them. -/
def ElimPost (n W : ℕ) : ElimOut → Prop := fun e =>
  e.1.length = n ∧ e.2.1.length = n ∧ e.2.2.1.length = n + 1 ∧
    e.2.2.2.1.length = n + 1 ∧ e.2.2.2.2.length = W ∧
    (∀ v < n, e.1[v]! < n) ∧ (∀ v < n, ∀ w < n, e.1[v]! = e.1[w]! → v = w)

/-- **`RamDriver.ElimAvail`, at the abstract layer.** The phase does not
own the engine: `OrderImplements` takes its availability as a
hypothesis, and so does this. -/
def ElimAvailA (n W : ℕ) (E : List ℕ → List ℕ → List ℕ → NRest ElimOut ECost)
    (EC : ACost String ℕ) : Prop :=
  ∀ off tgt alv : List ℕ,
    E off tgt alv ≤ NRest.spec (ElimPost n W) (fun _ => liftACost EC)

/-- Sequencing two bounded programs adds their prices. -/
theorem seqA_le {α β : Type} {m : NRest α ECost} {f : α → NRest β ECost} {P : α → Prop}
    {Q : β → Prop} {c d : ACost String ℕ}
    (hm : m ≤ NRest.spec P (fun _ => liftACost c))
    (hf : ∀ x, P x → f x ≤ NRest.spec Q (fun _ => liftACost d)) :
    NRest.bindT m f ≤ NRest.spec Q (fun _ => liftACost (c + d)) :=
  le_trans (le_trans (NRest.bindT_mono hm fun _ => le_rfl)
      (bindT_spec_le P (liftACost c) f Q (liftACost d) hf))
    (spec_mono (fun _ h => h) (fun _ _ => le_of_eq (liftACost_add c d).symm))

/-- The last pass of a chain, whose value the phase then reports. -/
theorem seqA_ret {α β : Type} {m : NRest α ECost} {P : α → Prop} {Q : β → Prop}
    {c : ACost String ℕ} {y : β} (hm : m ≤ NRest.spec P (fun _ => liftACost c)) (hy : Q y) :
    NRest.bindT m (fun _ => NRest.returnT y) ≤ NRest.spec Q (fun _ => liftACost c) := by
  refine le_trans (le_trans (NRest.bindT_mono hm fun _ => le_rfl)
    (bindT_spec_le P (liftACost c) _ Q 0 (fun _ _ => ?_))) (spec_mono (fun _ h => h) ?_)
  · rw [← NRest.consume_zero (NRest.returnT y)]
    exact consume_returnT_le_spec hy le_rfl
  · exact fun _ _ => le_of_eq (add_zero _)

/-- One prefix copy's price. -/
def pcC (N : ℕ) : ACost String ℕ := N • iter copyC + cu Currency.«while»

/-- One prefix fill's. -/
def pfC (N : ℕ) : ACost String ℕ := N • iter fillC + cu Currency.«while»

/-- The rank inversion's. -/
def poC (n : ℕ) : ACost String ℕ := n • iter ordC + cu Currency.«while»

/-- **The ordering phase at `R = 0`, abstractly.** `RamDriver.orderCom
0 W j`, pass for pass: the block structure saved, the depth's mask
copied in, the first elimination, the two in-list copies the round would
have read, the structure restored, the mask reopened, the elimination
scratch re-zeroed, the second elimination, the rank inversion, and the
eight fills of the re-zeroing tail. -/
noncomputable def orderPhase0 (n ns W : ℕ)
    (E : List ℕ → List ℕ → List ℕ → NRest ElimOut ECost)
    (off tgt gof gtg alvj alv doff dtg ooff noff stf sta std ste ord : List ℕ) :
    NRest (List ℕ) ECost :=
  bindT (copyPass (n + 1) off (gof, 0)) fun sv1 =>
  bindT (copyPass ns tgt (gtg, 0)) fun sv2 =>
  bindT (copyPass n alvj (alv, 0)) fun mk =>
  bindT (E off tgt mk.1) fun e1 =>
  bindT (copyPass (n + 1) e1.2.2.2.1 (doff, 0)) fun _ =>
  bindT (copyPass W e1.2.2.2.2 (dtg, 0)) fun _ =>
  bindT (copyPass (n + 1) sv1.1 (off, 0)) fun rs1 =>
  bindT (copyPass ns sv2.1 (tgt, 0)) fun rs2 =>
  bindT (fillPass n 1 (mk.1, 0)) fun mk1 =>
  bindT (fillPass n 0 (e1.2.1, 0)) fun _ =>
  bindT (fillPass (n + 1) 0 (e1.2.2.1, 0)) fun _ =>
  bindT (E rs1.1 rs2.1 mk1.1) fun e2 =>
  bindT (ordPass n e2.1 (ord, 0)) fun po =>
  bindT (fillPass n 0 (e2.2.1, 0)) fun _ =>
  bindT (fillPass (n + 1) 0 (e2.2.2.1, 0)) fun _ =>
  bindT (fillPass (n + 1) 0 (ooff, 0)) fun _ =>
  bindT (fillPass (n + 1) 0 (noff, 0)) fun _ =>
  bindT (fillPass n 0 (stf, 0)) fun _ =>
  bindT (fillPass n 0 (sta, 0)) fun _ =>
  bindT (fillPass n 0 (std, 0)) fun _ =>
  bindT (fillPass n 0 (ste, 0)) fun _ => NRest.returnT po.1

/-- **The phase's price**: the twenty-one passes' own, in the order the
program runs them. -/
noncomputable def orderPhase0C (n ns W : ℕ) (EC : ACost String ℕ) : ACost String ℕ :=
  pcC (n + 1) + (pcC ns + (pcC n + (EC + (pcC (n + 1) + (pcC W + (pcC (n + 1) + (pcC ns +
    (pfC n + (pfC n + (pfC (n + 1) + (EC + (poC n + (pfC n + (pfC (n + 1) + (pfC (n + 1) +
      (pfC (n + 1) + (pfC n + (pfC n + (pfC n + pfC n)))))))))))))))))))

/-- **The ordering phase at `R = 0`, bounded and correct.** Under the
elimination's availability the phase leaves an array of length `n` that
orders *some* permutation of the carrier — the existential
`RamDriver.OrderImplements` asks for — at the sum of its passes'
prices. -/
theorem orderPhase0_le {n ns W : ℕ}
    {E : List ℕ → List ℕ → List ℕ → NRest ElimOut ECost} {EC : ACost String ℕ}
    (hE : ElimAvailA n W E EC)
    {off tgt gof gtg alvj alv doff dtg ooff noff stf sta std ste ord : List ℕ}
    (hoff : off.length = n + 1) (htgt : tgt.length = ns) (hgof : gof.length = n + 1)
    (hgtg : gtg.length = ns) (halvj : alvj.length = n) (halv : alv.length = n)
    (hdoff : doff.length = n + 1) (hdtg : dtg.length = W) (hooff : ooff.length = n + 1)
    (hnoff : noff.length = n + 1) (hstf : stf.length = n) (hsta : sta.length = n)
    (hstd : std.length = n) (hste : ste.length = n) (hord : ord.length = n) :
    orderPhase0 n ns W E off tgt gof gtg alvj alv doff dtg ooff noff stf sta std ste ord
      ≤ NRest.spec
          (fun O : List ℕ => O.length = n ∧
            ∃ π : Equiv.Perm (Fin n), RamCover.OrdersBy n π (larr O))
          (fun _ => liftACost (orderPhase0C n ns W EC)) := by
  rw [orderPhase0, orderPhase0C]
  refine seqA_le (copyPass_spec hgof le_rfl (by omega)) fun sv1 hsv1 => ?_
  refine seqA_le (copyPass_spec hgtg le_rfl (by omega)) fun sv2 hsv2 => ?_
  refine seqA_le (copyPass_spec halv le_rfl (by omega)) fun mk hmk => ?_
  refine seqA_le (hE off tgt mk.1) fun e1 he1 => ?_
  refine seqA_le (copyPass_spec hdoff le_rfl (le_of_eq he1.2.2.2.1.symm)) fun _ _ => ?_
  refine seqA_le (copyPass_spec hdtg le_rfl (le_of_eq he1.2.2.2.2.1.symm)) fun _ _ => ?_
  refine seqA_le (copyPass_spec hoff le_rfl (le_of_eq hsv1.1.symm)) fun rs1 hrs1 => ?_
  refine seqA_le (copyPass_spec htgt le_rfl (le_of_eq hsv2.1.symm)) fun rs2 hrs2 => ?_
  refine seqA_le (fillPass_spec hmk.1 le_rfl) fun mk1 hmk1 => ?_
  refine seqA_le (fillPass_spec he1.2.1 le_rfl) fun _ _ => ?_
  refine seqA_le (fillPass_spec he1.2.2.1 le_rfl) fun _ _ => ?_
  refine seqA_le (hE rs1.1 rs2.1 mk1.1) fun e2 he2 => ?_
  refine seqA_le (ordPass_spec hord he2.1 he2.2.2.2.2.2.1 he2.2.2.2.2.2.2) fun po hpo => ?_
  refine seqA_le (fillPass_spec he2.2.1 le_rfl) fun _ _ => ?_
  refine seqA_le (fillPass_spec he2.2.2.1 le_rfl) fun _ _ => ?_
  refine seqA_le (fillPass_spec hooff le_rfl) fun _ _ => ?_
  refine seqA_le (fillPass_spec hnoff le_rfl) fun _ _ => ?_
  refine seqA_le (fillPass_spec hstf le_rfl) fun _ _ => ?_
  refine seqA_le (fillPass_spec hsta le_rfl) fun _ _ => ?_
  refine seqA_le (fillPass_spec hstd le_rfl) fun _ _ => ?_
  exact seqA_ret (fillPass_spec hste le_rfl) hpo

end Phase

/-! ## 8. The costs, cashed

The constants are **computed** from the per-iteration accounts by
`decide +kernel`, not tuned. -/

section Cash

theorem cash_copyC : Codegen.cash (iter copyC) = 15 := by decide +kernel

theorem cash_fillC : Codegen.cash (iter fillC) = 12 := by decide +kernel

theorem cash_ordC : Codegen.cash (iter ordC) = 15 := by decide +kernel

theorem cash_while : Codegen.cash (cu Currency.«while») = 4 := by decide +kernel

theorem cash_pcC (N : ℕ) : Codegen.cash (pcC N) = 15 * N + 4 := by
  rw [pcC, Codegen.cash_add, BfsQSynth.cash_nsmul, cash_copyC, cash_while, Nat.mul_comm]

theorem cash_pfC (N : ℕ) : Codegen.cash (pfC N) = 12 * N + 4 := by
  rw [pfC, Codegen.cash_add, BfsQSynth.cash_nsmul, cash_fillC, cash_while, Nat.mul_comm]

theorem cash_poC (n : ℕ) : Codegen.cash (poC n) = 15 * n + 4 := by
  rw [poC, Codegen.cash_add, BfsQSynth.cash_nsmul, cash_ordC, cash_while, Nat.mul_comm]

/-- **The ordering phase's cost at `R = 0`**, in IMP+ time units: the
seven prefix copies (`4n + 3 + 2ns + W` cells at 15), the eleven prefix
fills (`11n + 4` cells at 12), the rank inversion (`n` at 15), the
nineteen loop entries (4 each), and the two eliminations. -/
def orderPhase0K (n ns W e : ℕ) : ℕ := 207 * n + 30 * ns + 15 * W + 169 + 2 * e

theorem cash_orderPhase0C (n ns W : ℕ) (EC : ACost String ℕ) :
    Codegen.cash (orderPhase0C n ns W EC) = orderPhase0K n ns W (Codegen.cash EC) := by
  rw [orderPhase0C]
  simp only [Codegen.cash_add, cash_pcC, cash_pfC, cash_poC, orderPhase0K]
  ring

/-! ### The comparison with the hand-walked phase

`RamDriverCompose.orderPhaseCost n ns W = 1400·n + 1250·ns + 20·W + 450`
is the budget `orderImplements₀` is proved at, and it **contains the two
eliminations**: `RamElim.elimCost n ns = 600·n + 600·ns + 100` each. The
phase's own share of that budget is therefore

    1400n + 1250ns + 20W + 450 − 2·(600n + 600ns + 100)
      = 200n + 50ns + 20W + 250,

against this file's `207n + 30ns + 15W + 169`. The two are not the same
kind of number — the baseline's is a *budget*, deliberately generous
(`orderPhaseCost`'s own docstring says so), and this one is the exact
sum of twenty-one proved per-pass bounds — but per cell the comparison
is exact and is the one 2B′/F-a predicted:

| pass | hand-walked | tower | why |
|---|---|---|---|
| prefix copy | `14·N + 8` | `15·N + 4` | one `mopPair` skip per cell (F-a) |
| prefix fill | `13·N + 8` | `12·N + 4` | the IR's `aset` beats `.store` with a literal |
| rank inversion | `12·n + 6` | `15·n + 4` | the nested store is two IR ops (2E/D-b) |

So the phase is cheaper in `ns` and `W` (where the copies dominate at a
`.lit` bound the machine pays three sizes for), dearer in `n` by seven
units per vertex, and the whole difference is accounted for by the two
recorded deviations. -/

-- the two figures side by side at the demo's size, with the sign of the
-- difference recorded rather than assumed
#guard orderPhase0K 5 10 10 0 = 1654
#guard 200 * 5 + 50 * 10 + 20 * 10 + 250 = 1950

end Cash

/-! ## 9. The elimination as a leaf, and the phase's load-bearing
composition

2E/D-a says the *engine* enters `orderPhase0` as a hypothesis, because
2B′ never assembled its five passes into one program. What 2B′ *did*
synthesize is the elimination **loop**, and this section registers that
as a leaf operation by the `mopBfsE` idiom (`CoverSynth` §0) and then
asks the tool for the composition the phase turns on: the loop, and
then the rank inversion reading `rnk` off the loop's own state.

That composition is exactly the shape `ScatterSynth` §8b reported as
blocked — a loop wanting one component of a bound tuple as its own
conjunct — and that tool wave T1 fixed (`fri` bound-tuple split,
T1/D-b/D-d/D-f). This section is the ordering phase's check that the fix
holds at an **eleven**-component leaf. -/

section Leaf

/-- The elimination loop, as an operation of its own. Unlike
`CoverSynth.mopBfsE` it needs no `assert`: `ElimSynth3.elimSynth`'s rule
pins no state component at a literal — the eleven components enter at
whatever the caller holds — so the leaf has no entry condition to
discharge. -/
noncomputable def mopElim (n : ℕ) (off tgt alv : List ℕ) (e₀ : ElimSynth3.ES) :
    NRest ElimSynth3.ES ECost := ElimSynth3.elimLoop n off tgt alv e₀

theorem mopElim_eq (n : ℕ) (off tgt alv : List ℕ) (e₀ : ElimSynth3.ES) :
    mopElim n off tgt alv e₀ = ElimSynth3.elimLoop n off tgt alv e₀ := rfl

/-- Its only rule: 2B′'s synthesis, re-registered as a leaf — with the
precondition and the frame **spelled out** and not behind a name, which
is R2A/D-f's finding and the difference between a rule the matcher fires
and one it does not. -/
@[sepref_fr_rules]
theorem hnr_mop_elim (n : ℕ) (off tgt alv : List ℕ)
    (deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ : List ℕ) (sp₀ cnt₀ mind₀ kmax₀ : ℕ) :
    hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
          arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn)
        (deg₀, elm₀, rnk₀, idg₀, bh₀, bv₀, bn₀, sp₀, cnt₀, mind₀, kmax₀)
        ("deg", "elm", "rnk", "idg", "bh", "bv", "bn", "sp", "cnt", "mind", "kmax") ∗
        hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
        hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        junkCell "bhm" ∗ junkCell "w" ∗ junkCell "bnp" ∗ junkCell "ew" ∗ junkCell "dw" ∗
        junkCell "nm" ∗ junkCell "rw" ∗ junkCell "dk" ∗ junkCell "aw" ∗ junkCell "j" ∗
        junkCell "wp" ∗ junkCell "jend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗
        junkCell "dv" ∗ junkCell "du" ∗ junkCell "bhd")
      ElimSynth3.elimSynth_impl
      (hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
        hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        junkCell "bhm" ∗ junkCell "w" ∗ junkCell "bnp" ∗ junkCell "ew" ∗ junkCell "dw" ∗
        junkCell "nm" ∗ junkCell "rw" ∗ junkCell "dk" ∗ junkCell "aw" ∗ junkCell "j" ∗
        junkCell "wp" ∗ junkCell "jend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗
        junkCell "dv" ∗ junkCell "du" ∗ junkCell "bhd")
      ("deg", "elm", "rnk", "idg", "bh", "bv", "bn", "sp", "cnt", "mind", "kmax")
      (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
        arrayAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn)
      (mopElim n off tgt alv
        (deg₀, elm₀, rnk₀, idg₀, bh₀, bv₀, bn₀, sp₀, cnt₀, mind₀, kmax₀)) :=
  ElimSynth3.elimSynth n off tgt alv deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ sp₀ cnt₀ mind₀ kmax₀

attribute [irreducible] mopElim

/-- **The phase's core, abstractly**: the elimination loop, then the
inversion of the rank array it leaves. -/
noncomputable def elimThenOrd (n : ℕ) (off tgt alv : List ℕ) (e₀ : ElimSynth3.ES)
    (ord₀ : List ℕ) (z₀ : ℕ) : NRest FS ECost :=
  bindT (mopElim n off tgt alv e₀) fun e => ordPass n e.2.2.1 (ord₀, z₀)

set_option maxHeartbeats 1000000 in
sepref_synth elimOrdSynth (n : ℕ) (off tgt alv : List ℕ)
    (deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ : List ℕ) (sp₀ cnt₀ mind₀ kmax₀ : ℕ)
    (ord₀ : List ℕ) (z₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
        arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn)
      (deg₀, elm₀, rnk₀, idg₀, bh₀, bv₀, bn₀, sp₀, cnt₀, mind₀, kmax₀)
      ("deg", "elm", "rnk", "idg", "bh", "bv", "bn", "sp", "cnt", "mind", "kmax") ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
      hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "bhm" ∗ junkCell "w" ∗ junkCell "bnp" ∗ junkCell "ew" ∗ junkCell "dw" ∗
      junkCell "nm" ∗ junkCell "rw" ∗ junkCell "dk" ∗ junkCell "aw" ∗ junkCell "j" ∗
      junkCell "wp" ∗ junkCell "jend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗
      junkCell "dv" ∗ junkCell "du" ∗ junkCell "bhd" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (ord₀, z₀) ("ord", "z") ∗ junkCell "rz")
    _ _ ("ord", "z") (arrayAssn ×ₐ natAssn)
    (elimThenOrd n off tgt alv
      (deg₀, elm₀, rnk₀, idg₀, bh₀, bv₀, bn₀, sp₀, cnt₀, mind₀, kmax₀) ord₀ z₀)

-- **The composition, pinned.** The elimination loop's own program,
-- then the inversion — and the inversion's scratch cell is **`"bhm"`,
-- not `"rz"`**: 2E/D-d, below.
#guard elimOrdSynth_impl =
  ElimSynth3.elimSynth_impl.seq
    (Com.while (Cond.lt (Operand.cell "z") (Operand.cell "n"))
      ((Com.aget "bhm" "rnk" "z").seq
        ((Com.aset "ord" "bhm" "z").seq
          ((Com.binop Lax13Proofs.Imp.Bop.add "z" "z" "one").seq Com.skip))))

/-- info: 'Lax3Proofs.Refine.OrderSynth.elimOrdSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms elimOrdSynth

/-! **2E/D-d — a leaf's scratch cells are released, and the next pass
takes them.** The composed program's inversion reads into `"bhm"`, the
elimination loop's first junk cell, and never touches the `"rz"` the
precondition offers it: junk destinations are consumed from the
precondition **in written order**, and the leaf's twenty-two scratch
cells come first. Two consequences worth recording.

* The composition costs **no extra cell**. A phase built out of leaves
  re-uses the leaves' scratch, which is the opposite of the worry that
  each leaf's footprint accumulates.
* A `#guard` that pinned the composed program as `elimSynth_impl.seq
  ordSynth_impl` **fails** — the two inversions differ in one cell name.
  Pinning a composed program means re-reading the tool's report, not
  concatenating the pins of its parts. -/

end Leaf

/-! ## 10. The bounds passes (`BRefine`)

P0.2's second judgment, at the three loops. The hand-tax is the ≈ 50
lines per loop `AugmentSynth` §2.1 measured, and all three are paid
here: the phase's word obligations are exactly two, `i + 1 < B` at each
counter bump, and everything else the run hands over.

**The `BRefine` junk gap is not a gap here** (T1's memo item (b)). The
copy and the inversion both write into a scratch cell, and `BRefine`'s
loop rule takes an *arbitrary* index type `σ` — so the scratch cell's
value rides in the index as a fourth component and needs no junk rule at
all. What the memo asks for is ergonomics; what a consumer needs is
already derivable, and this section is the demonstration. -/

section Bounds

/-! ### 10.1 The prefix fill -/

/-- The fill loop's assertion: the array and the counter it mutates, the
three constants it reads. -/
def flΓ (N v : ℕ) : FS → Assn := fun t =>
  arrayAssn t.1 "fla" ∗ natAssn t.2 "fli" ∗ natAssn v "flv" ∗ natAssn N "fln" ∗
    natAssn 1 "one"

/-- The abstract invariant. One conjunct. -/
def flI (N : ℕ) : FS → Prop := fun t => t.2 ≤ N

theorem fl_guard (N v : ℕ) (t : FS) (F : Assn) (s : Ir.State) (cr : ECost)
    (r : Bool) (_ : flI N t) (hs : irSTATE (flΓ N v t ∗ F) (s, cr))
    (hev : (Cond.lt (Operand.cell "fli") (Operand.cell "fln")).eval s = some r) :
    decide (t.2 < N) = r := by
  obtain ⟨a, b, ha, hb, rfl⟩ := BfsQSynth.eval_lt_cells hev
  have hi : s.vars "fli" = some t.2 :=
    natAssn_vars (F := arrayAssn t.1 "fla" ∗ natAssn v "flv" ∗ natAssn N "fln" ∗
      natAssn 1 "one" ∗ F) (irSTATE_cong (by rw [flΓ]; ac_rfl) hs)
  have hn : s.vars "fln" = some N :=
    natAssn_vars (F := arrayAssn t.1 "fla" ∗ natAssn t.2 "fli" ∗ natAssn v "flv" ∗
      natAssn 1 "one" ∗ F) (irSTATE_cong (by rw [flΓ]; ac_rfl) hs)
  rw [hi] at ha
  rw [hn] at hb
  rw [Option.some.inj ha, Option.some.inj hb]

/-- The fill's loop body, named. -/
def flBody : Com :=
  (Com.aset "fla" "fli" "flv").seq
    ((Com.binop Lax13Proofs.Imp.Bop.add "fli" "fli" "one").seq Com.skip)

theorem fillSynth_impl_eq :
    fillSynth_impl = Com.while (Cond.lt (Operand.cell "fli") (Operand.cell "fln")) flBody :=
  rfl

theorem fl_body_brefine {B N v : ℕ} (hNB : N < B) (t : FS) (_hI : flI N t)
    (hbf : decide (t.2 < N) = true) :
    BRefine B (flΓ N v t) flBody (LoopAssn (flI N) (flΓ N v)) := by
  have hlt : t.2 < N := of_decide_eq_true hbf
  rw [flBody]
  refine BRefine.seq (Γ₁ := ⌜t.2 < t.1.length⌝ ∗ flΓ N v (t.1.set t.2 v, t.2)) ?_ ?_
  · exact BRefine.perm
      (P := (arrayAssn t.1 "fla" ∗ natAssn t.2 "fli" ∗ natAssn v "flv") ∗
        (natAssn N "fln" ∗ natAssn 1 "one"))
      (P' := (⌜t.2 < t.1.length⌝ ∗ arrayAssn (t.1.set t.2 v) "fla" ∗ natAssn t.2 "fli" ∗
        natAssn v "flv") ∗ (natAssn N "fln" ∗ natAssn 1 "one"))
      (by simp only [flΓ]; ac_rfl) (by simp only [flΓ]; ac_rfl)
      (BRefine.frame BRefine.aset)
  · refine BRefine.pre_pure fun _ => ?_
    refine BRefine.seq
      (Γ₁ := flΓ N v (t.1.set t.2 v, Lax13Proofs.Imp.Bop.apply .add t.2 1)) ?_ ?_
    · exact BRefine.perm
        (P := (natAssn t.2 "fli" ∗ natAssn 1 "one") ∗
          (arrayAssn (t.1.set t.2 v) "fla" ∗ natAssn v "flv" ∗ natAssn N "fln"))
        (P' := (natAssn (Lax13Proofs.Imp.Bop.apply .add t.2 1) "fli" ∗ natAssn 1 "one") ∗
          (arrayAssn (t.1.set t.2 v) "fla" ∗ natAssn v "flv" ∗ natAssn N "fln"))
        (by simp only [flΓ]; ac_rfl) (by simp only [flΓ]; ac_rfl)
        (BRefine.frame (BRefine.binop_self
          (by rw [Lax13Proofs.Imp.Bop.apply_add]; omega)))
    · exact BRefine.skip.cons (entails_refl _)
        (loopAssn_intro (I := flI N) (Γ := flΓ N v)
          (t := (t.1.set t.2 v, Lax13Proofs.Imp.Bop.apply .add t.2 1))
          (by simp only [flI, Lax13Proofs.Imp.Bop.apply_add]; omega))

/-- **The prefix fill's bounds pass.** -/
theorem fill_brefine {B N v : ℕ} (hNB : N < B) :
    BRefine B (LoopAssn (flI N) (flΓ N v)) fillSynth_impl (LoopAssn (flI N) (flΓ N v)) := by
  rw [fillSynth_impl_eq]
  exact BRefine.while_guard (bf := fun t => decide (t.2 < N))
    BfsQSynth.litLt_lt_cells (fl_guard N v)
    (fun t hI hbf => fl_body_brefine hNB t hI hbf)
    (fun t hI _ => loopAssn_intro hI)

/-! ### 10.2 The prefix copy

The scratch cell rides in the index: `σ` is the loop state **and** the
value `"cpu"` currently holds. -/

/-- The copy loop's assertion, indexed by the state and the scratch. -/
def cpΓ (N : ℕ) (src : List ℕ) : FS × ℕ → Assn := fun t =>
  arrayAssn t.1.1 "cpd" ∗ natAssn t.1.2 "cpi" ∗ arrayAssn src "cps" ∗
    natAssn N "cpn" ∗ natAssn 1 "one" ∗ natAssn t.2 "cpu"

def cpI (N : ℕ) : FS × ℕ → Prop := fun t => t.1.2 ≤ N

theorem cp_guard (N : ℕ) (src : List ℕ) (t : FS × ℕ) (F : Assn) (s : Ir.State) (cr : ECost)
    (r : Bool) (_ : cpI N t) (hs : irSTATE (cpΓ N src t ∗ F) (s, cr))
    (hev : (Cond.lt (Operand.cell "cpi") (Operand.cell "cpn")).eval s = some r) :
    decide (t.1.2 < N) = r := by
  obtain ⟨a, b, ha, hb, rfl⟩ := BfsQSynth.eval_lt_cells hev
  have hi : s.vars "cpi" = some t.1.2 :=
    natAssn_vars (F := arrayAssn t.1.1 "cpd" ∗ arrayAssn src "cps" ∗ natAssn N "cpn" ∗
      natAssn 1 "one" ∗ natAssn t.2 "cpu" ∗ F) (irSTATE_cong (by rw [cpΓ]; ac_rfl) hs)
  have hn : s.vars "cpn" = some N :=
    natAssn_vars (F := arrayAssn t.1.1 "cpd" ∗ natAssn t.1.2 "cpi" ∗ arrayAssn src "cps" ∗
      natAssn 1 "one" ∗ natAssn t.2 "cpu" ∗ F) (irSTATE_cong (by rw [cpΓ]; ac_rfl) hs)
  rw [hi] at ha
  rw [hn] at hb
  rw [Option.some.inj ha, Option.some.inj hb]

def cpBody : Com :=
  (Com.aget "cpu" "cps" "cpi").seq
    ((Com.aset "cpd" "cpi" "cpu").seq
      ((Com.binop Lax13Proofs.Imp.Bop.add "cpi" "cpi" "one").seq Com.skip))

theorem copySynth_impl_eq :
    copySynth_impl = Com.while (Cond.lt (Operand.cell "cpi") (Operand.cell "cpn")) cpBody :=
  rfl

theorem cp_body_brefine {B N : ℕ} {src : List ℕ} (hNB : N < B) (t : FS × ℕ) (_hI : cpI N t)
    (hbf : decide (t.1.2 < N) = true) :
    BRefine B (cpΓ N src t) cpBody (LoopAssn (cpI N) (cpΓ N src)) := by
  have hlt : t.1.2 < N := of_decide_eq_true hbf
  rw [cpBody]
  refine BRefine.seq (Γ₁ := ⌜t.1.2 < src.length⌝ ∗ cpΓ N src (t.1, src[t.1.2]!)) ?_ ?_
  · exact BRefine.perm
      (P := (natAssn t.2 "cpu" ∗ arrayAssn src "cps" ∗ natAssn t.1.2 "cpi") ∗
        (arrayAssn t.1.1 "cpd" ∗ natAssn N "cpn" ∗ natAssn 1 "one"))
      (P' := (⌜t.1.2 < src.length⌝ ∗ natAssn src[t.1.2]! "cpu" ∗ arrayAssn src "cps" ∗
        natAssn t.1.2 "cpi") ∗ (arrayAssn t.1.1 "cpd" ∗ natAssn N "cpn" ∗ natAssn 1 "one"))
      (by simp only [cpΓ]; ac_rfl) (by simp only [cpΓ]; ac_rfl)
      (BRefine.frame BRefine.aget)
  refine BRefine.pre_pure fun _ => ?_
  refine BRefine.seq
    (Γ₁ := ⌜t.1.2 < t.1.1.length⌝ ∗
      cpΓ N src ((t.1.1.set t.1.2 src[t.1.2]!, t.1.2), src[t.1.2]!)) ?_ ?_
  · exact BRefine.perm
      (P := (arrayAssn t.1.1 "cpd" ∗ natAssn t.1.2 "cpi" ∗ natAssn src[t.1.2]! "cpu") ∗
        (arrayAssn src "cps" ∗ natAssn N "cpn" ∗ natAssn 1 "one"))
      (P' := (⌜t.1.2 < t.1.1.length⌝ ∗
        arrayAssn (t.1.1.set t.1.2 src[t.1.2]!) "cpd" ∗ natAssn t.1.2 "cpi" ∗
        natAssn src[t.1.2]! "cpu") ∗
        (arrayAssn src "cps" ∗ natAssn N "cpn" ∗ natAssn 1 "one"))
      (by simp only [cpΓ]; ac_rfl) (by simp only [cpΓ]; ac_rfl)
      (BRefine.frame BRefine.aset)
  refine BRefine.pre_pure fun _ => ?_
  refine BRefine.seq
    (Γ₁ := cpΓ N src ((t.1.1.set t.1.2 src[t.1.2]!,
      Lax13Proofs.Imp.Bop.apply .add t.1.2 1), src[t.1.2]!)) ?_ ?_
  · exact BRefine.perm
      (P := (natAssn t.1.2 "cpi" ∗ natAssn 1 "one") ∗
        (arrayAssn (t.1.1.set t.1.2 src[t.1.2]!) "cpd" ∗ arrayAssn src "cps" ∗
          natAssn N "cpn" ∗ natAssn src[t.1.2]! "cpu"))
      (P' := (natAssn (Lax13Proofs.Imp.Bop.apply .add t.1.2 1) "cpi" ∗ natAssn 1 "one") ∗
        (arrayAssn (t.1.1.set t.1.2 src[t.1.2]!) "cpd" ∗ arrayAssn src "cps" ∗
          natAssn N "cpn" ∗ natAssn src[t.1.2]! "cpu"))
      (by simp only [cpΓ]; ac_rfl) (by simp only [cpΓ]; ac_rfl)
      (BRefine.frame (BRefine.binop_self (by rw [Lax13Proofs.Imp.Bop.apply_add]; omega)))
  · exact BRefine.skip.cons (entails_refl _)
      (loopAssn_intro (I := cpI N) (Γ := cpΓ N src)
        (t := ((t.1.1.set t.1.2 src[t.1.2]!, Lax13Proofs.Imp.Bop.apply .add t.1.2 1),
          src[t.1.2]!))
        (by simp only [cpI, Lax13Proofs.Imp.Bop.apply_add]; omega))

/-- **The prefix copy's bounds pass.** -/
theorem copy_brefine {B N : ℕ} {src : List ℕ} (hNB : N < B) :
    BRefine B (LoopAssn (cpI N) (cpΓ N src)) copySynth_impl
      (LoopAssn (cpI N) (cpΓ N src)) := by
  rw [copySynth_impl_eq]
  exact BRefine.while_guard (bf := fun t => decide (t.1.2 < N))
    BfsQSynth.litLt_lt_cells (cp_guard N src)
    (fun t hI hbf => cp_body_brefine hNB t hI hbf)
    (fun t hI _ => loopAssn_intro hI)

/-! ### 10.3 The rank inversion -/

/-- The inversion's assertion, indexed by the state and the scratch. -/
def orΓ (n : ℕ) (rnk : List ℕ) : FS × ℕ → Assn := fun t =>
  arrayAssn t.1.1 "ord" ∗ natAssn t.1.2 "z" ∗ arrayAssn rnk "rnk" ∗
    natAssn n "n" ∗ natAssn 1 "one" ∗ natAssn t.2 "rz"

def orI (n : ℕ) : FS × ℕ → Prop := fun t => t.1.2 ≤ n

theorem or_guard (n : ℕ) (rnk : List ℕ) (t : FS × ℕ) (F : Assn) (s : Ir.State) (cr : ECost)
    (r : Bool) (_ : orI n t) (hs : irSTATE (orΓ n rnk t ∗ F) (s, cr))
    (hev : (Cond.lt (Operand.cell "z") (Operand.cell "n")).eval s = some r) :
    decide (t.1.2 < n) = r := by
  obtain ⟨a, b, ha, hb, rfl⟩ := BfsQSynth.eval_lt_cells hev
  have hi : s.vars "z" = some t.1.2 :=
    natAssn_vars (F := arrayAssn t.1.1 "ord" ∗ arrayAssn rnk "rnk" ∗ natAssn n "n" ∗
      natAssn 1 "one" ∗ natAssn t.2 "rz" ∗ F) (irSTATE_cong (by rw [orΓ]; ac_rfl) hs)
  have hn : s.vars "n" = some n :=
    natAssn_vars (F := arrayAssn t.1.1 "ord" ∗ natAssn t.1.2 "z" ∗ arrayAssn rnk "rnk" ∗
      natAssn 1 "one" ∗ natAssn t.2 "rz" ∗ F) (irSTATE_cong (by rw [orΓ]; ac_rfl) hs)
  rw [hi] at ha
  rw [hn] at hb
  rw [Option.some.inj ha, Option.some.inj hb]

def orBody : Com :=
  (Com.aget "rz" "rnk" "z").seq
    ((Com.aset "ord" "rz" "z").seq
      ((Com.binop Lax13Proofs.Imp.Bop.add "z" "z" "one").seq Com.skip))

theorem ordSynth_impl_eq :
    ordSynth_impl = Com.while (Cond.lt (Operand.cell "z") (Operand.cell "n")) orBody :=
  rfl

theorem or_body_brefine {B n : ℕ} {rnk : List ℕ} (hnB : n < B) (t : FS × ℕ) (_hI : orI n t)
    (hbf : decide (t.1.2 < n) = true) :
    BRefine B (orΓ n rnk t) orBody (LoopAssn (orI n) (orΓ n rnk)) := by
  have hlt : t.1.2 < n := of_decide_eq_true hbf
  rw [orBody]
  refine BRefine.seq (Γ₁ := ⌜t.1.2 < rnk.length⌝ ∗ orΓ n rnk (t.1, rnk[t.1.2]!)) ?_ ?_
  · exact BRefine.perm
      (P := (natAssn t.2 "rz" ∗ arrayAssn rnk "rnk" ∗ natAssn t.1.2 "z") ∗
        (arrayAssn t.1.1 "ord" ∗ natAssn n "n" ∗ natAssn 1 "one"))
      (P' := (⌜t.1.2 < rnk.length⌝ ∗ natAssn rnk[t.1.2]! "rz" ∗ arrayAssn rnk "rnk" ∗
        natAssn t.1.2 "z") ∗ (arrayAssn t.1.1 "ord" ∗ natAssn n "n" ∗ natAssn 1 "one"))
      (by simp only [orΓ]; ac_rfl) (by simp only [orΓ]; ac_rfl)
      (BRefine.frame BRefine.aget)
  refine BRefine.pre_pure fun _ => ?_
  refine BRefine.seq
    (Γ₁ := ⌜rnk[t.1.2]! < t.1.1.length⌝ ∗
      orΓ n rnk ((t.1.1.set rnk[t.1.2]! t.1.2, t.1.2), rnk[t.1.2]!)) ?_ ?_
  · exact BRefine.perm
      (P := (arrayAssn t.1.1 "ord" ∗ natAssn rnk[t.1.2]! "rz" ∗ natAssn t.1.2 "z") ∗
        (arrayAssn rnk "rnk" ∗ natAssn n "n" ∗ natAssn 1 "one"))
      (P' := (⌜rnk[t.1.2]! < t.1.1.length⌝ ∗
        arrayAssn (t.1.1.set rnk[t.1.2]! t.1.2) "ord" ∗ natAssn rnk[t.1.2]! "rz" ∗
        natAssn t.1.2 "z") ∗ (arrayAssn rnk "rnk" ∗ natAssn n "n" ∗ natAssn 1 "one"))
      (by simp only [orΓ]; ac_rfl) (by simp only [orΓ]; ac_rfl)
      (BRefine.frame BRefine.aset)
  refine BRefine.pre_pure fun _ => ?_
  refine BRefine.seq
    (Γ₁ := orΓ n rnk ((t.1.1.set rnk[t.1.2]! t.1.2,
      Lax13Proofs.Imp.Bop.apply .add t.1.2 1), rnk[t.1.2]!)) ?_ ?_
  · exact BRefine.perm
      (P := (natAssn t.1.2 "z" ∗ natAssn 1 "one") ∗
        (arrayAssn (t.1.1.set rnk[t.1.2]! t.1.2) "ord" ∗ arrayAssn rnk "rnk" ∗
          natAssn n "n" ∗ natAssn rnk[t.1.2]! "rz"))
      (P' := (natAssn (Lax13Proofs.Imp.Bop.apply .add t.1.2 1) "z" ∗ natAssn 1 "one") ∗
        (arrayAssn (t.1.1.set rnk[t.1.2]! t.1.2) "ord" ∗ arrayAssn rnk "rnk" ∗
          natAssn n "n" ∗ natAssn rnk[t.1.2]! "rz"))
      (by simp only [orΓ]; ac_rfl) (by simp only [orΓ]; ac_rfl)
      (BRefine.frame (BRefine.binop_self (by rw [Lax13Proofs.Imp.Bop.apply_add]; omega)))
  · exact BRefine.skip.cons (entails_refl _)
      (loopAssn_intro (I := orI n) (Γ := orΓ n rnk)
        (t := ((t.1.1.set rnk[t.1.2]! t.1.2, Lax13Proofs.Imp.Bop.apply .add t.1.2 1),
          rnk[t.1.2]!))
        (by simp only [orI, Lax13Proofs.Imp.Bop.apply_add]; omega))

/-- **The rank inversion's bounds pass.** -/
theorem ord_brefine {B n : ℕ} {rnk : List ℕ} (hnB : n < B) :
    BRefine B (LoopAssn (orI n) (orΓ n rnk)) ordSynth_impl
      (LoopAssn (orI n) (orΓ n rnk)) := by
  rw [ordSynth_impl_eq]
  exact BRefine.while_guard (bf := fun t => decide (t.1.2 < n))
    BfsQSynth.litLt_lt_cells (or_guard n rnk)
    (fun t hI hbf => or_body_brefine hnB t hI hbf)
    (fun t hI _ => loopAssn_intro hI)

end Bounds

/-! ## 11. What `OrderImplements` asks for, and what is here

`RamDriver.OrderImplements`' postcondition has five clauses. Where each
one stands at this layer:

| clause | here |
|---|---|
| `∃ π ord, ordName j = arrOf n ord ∧ OrdersBy n π ord` | `orderPhase0_le`'s postcondition, verbatim |
| `LevelPre` preserved | the length half is `orderPhase0_le`'s lengths; the *value* half is structural, below |
| `σ'.out = σ.out` | **not expressible**: the abstract layer has no output stream, and no program here can write one |
| `ctrName a` unchanged | likewise: a scalar no pass names |
| `gamName a` unchanged | likewise: an array no pass is given |

The last three are the layer's own argument, the same one `ElimSynth`'s
header makes about the re-zeroing defect. Every program above is a
function of the arrays it is *handed*; `orderPhase0` takes fifteen
arrays and an engine, and its value and cost are functions of those.
There is no state for it to disturb, so the three frame clauses are not
proved here — they are *unstatable*, which is the strongest form of
"preserved" a refinement layer offers. They become statements again only
at the lowering, where `Codegen`'s `wvars`/`warrs` are what the machine
layer already reads off the emitted `Com`.

The zeroing half of `LevelPre` — `OrderMem`'s eight "this array is all
zero" clauses — is `fillPass_spec`'s `∀ j, t.1[j]! = if j < N then 0
else A₀[j]!` at the eight tail fills, at `N` the array's own length. It
is not carried through `orderPhase0_le`'s postcondition because nothing
downstream of the phase reads it *inside* this file; the eight facts are
one `seqA_le` continuation away for the consumer that needs them, and
the shape of that continuation is fixed by `fillPass_spec`.

## 12. Debts, named

**2E/E1 — the engine is an interface, not a program.** `ElimAvailA` is
discharged by assembling 2B′'s five synthesized passes and transporting
`RamElim.Elim`'s invariant to `ElimPost`'s two rank clauses — 2B′'s own
debts E1 (the amortized bound) and E2 (the correctness transport) plus
the assembly. Nothing here is `sorry`ed: the phase is stated *under* the
hypothesis, exactly as `OrderImplements` is stated under `ElimAvail`.

**2E/E2 — the phase is not one `Com`.** §9 synthesizes the composition
that carries the phase's content (the engine's loop, then the
inversion). The remaining twenty passes are `copySynth`/`fillSynth` at
twenty different cell-name sets; each is a two-second `sepref_synth`
run, and the driver-side assembly that names them is the *retained*
half of satellite 2A's tower/hand boundary decision (the name-generating
recursion stays hand-written). Emitting them is mechanical and is a
cost, not a risk.

**2E/E3 — the `Spec` bridge.** Turning `orderPhase0_le` into
`RamDriver.OrderImplements` is the P4 cost-assembly step
(`Spec`→`computesInTime`), and is not this satellite's.

## 13. Axioms -/

/-- info: 'Lax3Proofs.Refine.OrderSynth.copyPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms copyPass_spec

/-- info: 'Lax3Proofs.Refine.OrderSynth.fillPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms fillPass_spec

/-- info: 'Lax3Proofs.Refine.OrderSynth.ordPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ordPass_spec

/-- info: 'Lax3Proofs.Refine.OrderSynth.orderPhase0_le' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms orderPhase0_le

/-- info: 'Lax3Proofs.Refine.OrderSynth.fill_brefine' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms fill_brefine

/-- info: 'Lax3Proofs.Refine.OrderSynth.copy_brefine' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms copy_brefine

/-- info: 'Lax3Proofs.Refine.OrderSynth.ord_brefine' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ord_brefine

/-! ## 14. Telemetry (the wave's acceptance numbers)

* **Syntheses**: four, all first-try, all at a 1 000 000-heartbeat
  budget. `copySynth` / `fillSynth` / `ordSynth` ≈ 2 s each (flat
  two-component loops); `elimOrdSynth` — the eleven-component leaf plus
  the inversion — ≈ 7 s. The composition is *cheaper* than the leaf's
  own re-synthesis would be, because the leaf is a rule and not a
  re-derivation.
* **Costs**: `copyC` 15, `fillC` 12, `ordC` 15 per cell; `while` 4 per
  loop entry; the phase `207n + 30ns + 15W + 169` plus the two
  eliminations, against the hand-walked phase's share of its budget,
  `200n + 50ns + 20W + 250`.
* **Falsification**: twenty-six `#guard`s — ten twin readings (two of
  them `RamElim.Demo`'s own published ranks, taken through
  `ElimSynth`'s engine twin), eight readings of the *synthesized*
  programs under `Ir.evalFuel` (three of which check the twin against
  the program cell for cell), four program pins, two cost figures — and
  three `#guard_msgs`-pinned refutations, plus eleven `#print axioms`
  gates. The old ordering phase publishes **no** worked run of its own
  (`RamDriverOrder`/`RamDriverCompose` carry no `#guard`), so the
  strongest available coupling to the compiled machine program is
  through `RamElim.Demo`'s ranks, and that is the one used.
* **Bounds passes**: three, ≈ 55 lines each, no tool gap — the
  `BRefine` junk-cell item of T1's memo is an ergonomics item, not a
  blocker (§10).
-/

end Lax3Proofs.Refine.OrderSynth
