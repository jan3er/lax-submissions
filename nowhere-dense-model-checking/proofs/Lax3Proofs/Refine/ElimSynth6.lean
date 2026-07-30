import Lax3Proofs.Refine.ElimSynth5
import Lax3Proofs.Refine.OrderSynth

/-!
# P2 wave F1 — the fill pass, walked, and the engine at five phases

`ElimSynth2` §4 has the fill pass as a program (`fillPass`), its
per-iteration accounts (`fillC` at 41, `fillRowC` at 37) and its
synthesized `Com` (`fillSynth_impl`, pinned instruction for
instruction). What it does not have is the walk: the two loops' bound
and postcondition. `ElimSynth5` §7 has the engine at **four** phases
(`elimEngine_le`) and names the fifth as debt F1.

This file pays the *range and length* half of F1 and closes the
elimination's consumer:

* §1 — the fill's row scan, run to the end, at an arbitrary invariant
  (the shape `degScan_le` has, so the content walk that is still open
  can be plugged into the same lemma).
* §2 — one row, and the pass, on the two-currency energy the degree
  pass runs on: one `fillRowC` per vertex left, one `fillC` per
  adjacency slot left.
* §3 — the block starts do not overtake the block structure
  (`psum ID v ≤ off[v]!`), which is what keeps the fill pointer inside
  `itg`. This is the one piece of mathematics the walk needs, and it
  comes off `ElimAnswer`'s in-degree clause.
* §4 — the five-phase engine, `elimEngine5_le`, and its cost.
* §5 — `OrderSynth.ElimAvailA`, discharged.
* §6 — what is landed, what is left.

## The pointer argument, in one line

The fill writes at `ifl[i]`, which starts at `psum ID i ≤ off[i]!` and
advances by at most one per slot the scan passes. So the fill pointer
**never overtakes the scan pointer**: `ifl[i]! ≤ j < off[i+1]! ≤ ns ≤
W`. No `written`-set bookkeeping is needed for the range — that is a
counting-sort fact about the block structure, not about the arcs.

## House traps observed

`omega` is blind through `FS`'s projections — every arithmetic clause
needs its `show`. `decide +kernel` for the cashed constants. `ac_rfl`
only at the small accounts. Never `simp [Codegen.embed]`.
-/

namespace Lax3Proofs.Refine.ElimSynth6

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax13Proofs.Refine.Codegen
open Lax13Proofs.Refine.BfsQ (Shape cu iter irWhile_exit get!_set res_of_le liftACost_cu)
open Lax3Proofs.Refine.ElimSynth hiding mopSucc mopSucc_eq mopKeep mopKeep_eq
open Lax3Proofs.Refine.ElimSynth2
open Lax3Proofs.Refine.ElimSynth3
open Lax3Proofs.Refine.ElimSynth4
open Lax3Proofs.Refine.ElimSynth5

/-! ## 0. Refute before prove

The fill twins of `ElimSynth` §1.2 are golden data — they reproduce
`RamElim.Demo`'s published readings of the *compiled machine program*.
Every statement this file proves about the pass is read off them
first. -/

section Refute

/-- The demo's ranks, as the engine leaves them (`ElimSynth`'s
`demoTw 1`). -/
def dRnk : List ℕ := [0, 1, 2, 3, 4]

/-- The demo's block starts, as the offset pass leaves them: `ioff`
truncated to the `n` cells `ifl` has. -/
def dIfl : List ℕ := [0, 0, 1, 3, 4]

/-- The fill twin on the demo arena, from an empty `itg` of the demo's
own width. -/
def dFill : List ℕ × List ℕ × ℕ :=
  fillPassTw 5 demoOff demoTgt (demoAlv 1) dRnk 20 (List.replicate 10 0, dIfl, 0)

-- **The twin is the machine's**: the arcs `RamElim.Demo` publishes.
#guard dFill.1.take 5 = [0, 0, 1, 2, 3]

-- **The claim this file proves, read off the twin.** The in-list array
-- comes out at the width it went in at, and the pointer array at `n`.
#guard dFill.1.length = 10
#guard dFill.2.1.length = 5

-- **The pointer never overtakes the block structure**: at the end of
-- the pass every fill pointer sits at the end of its own block, and
-- every block ends inside the target array.
#guard dFill.2.1 = [0, 1, 3, 4, 5]
#guard (List.range 5).all (fun v => dFill.2.1[v]! ≤ demoOff[v + 1]!)

-- …and at the demo's own width the pointer is strictly inside `itg`
-- at every row start, which is the `fillP` clause the walk owes.
#guard (List.range 5).all (fun v => dIfl[v]! < 10)

/-! ### Negative controls -/

-- **(a) the export's length clause is not free.** A claim of the wrong
-- width is refuted by the twin.
#guard ¬ (dFill.1.length = 9)
#guard ¬ (dFill.1.length = 11)

-- **(b) the mask bites here too.** With vertex `2` masked off the fill
-- writes a different array, so a walk that ignored `alv` would be
-- refuted.
#guard (fillPassTw 5 demoOff demoTgt (demoAlv 0) [0, 1, 4, 2, 3] 20
  (List.replicate 10 0, [0, 0, 1, 1, 1], 0)).1.take 5 = [0, 3, 0, 0, 0]
#guard dFill.1 ≠ (fillPassTw 5 demoOff demoTgt (demoAlv 0) [0, 1, 4, 2, 3] 20
  (List.replicate 10 0, [0, 0, 1, 1, 1], 0)).1

-- **(c) the pass is not the identity.** A walk whose postcondition were
-- "nothing moved" would satisfy every length clause above and is
-- refuted by both arrays.
#guard dFill.2.1 ≠ dIfl
#guard dFill.1 ≠ List.replicate 10 0

end Refute

/-! ## 1. The fill's row scan, run to the end

`degScan_le`'s shape, at `fillF`/`fillStep`: an arbitrary invariant the
caller supplies, preserved by the twin step and implying `fillP` at
every slot the guard admits. Every iteration pays the same `fillC` —
the two-armed branch is priced at its dearest arm — so the row's price
is the number of slots it has. -/

section Scan

theorem fillScan_le {Inv : FS → Prop} (tgt alv rnk : List ℕ) (i ri jend : ℕ)
    (hs : ∀ t : FS, Inv t → fillBf jend t = true →
      ElimSynth2.fillP tgt alv rnk i t ∧ Inv (fillStep tgt alv rnk i ri t)) :
    ∀ (fuel : ℕ) (t : FS), Inv t → jend - t.2.2 ≤ fuel →
      fillScan tgt alv rnk i ri jend t
        ≤ NRest.spec (fun t' : FS => Inv t' ∧ jend ≤ t'.2.2)
            (fun _ => liftACost ((jend - t.2.2) • iter ElimSynth2.fillC
              + cu Currency.«while»)) := by
  have exit : ∀ t : FS, Inv t → jend ≤ t.2.2 →
      fillScan tgt alv rnk i ri jend t
        ≤ NRest.spec (fun t' : FS => Inv t' ∧ jend ≤ t'.2.2)
            (fun _ => liftACost ((jend - t.2.2) • iter ElimSynth2.fillC
              + cu Currency.«while»)) := by
    intro t hI hk
    have hb : fillBf jend t = false := by
      simp only [fillBf, decide_eq_false_iff_not]
      omega
    simp only [fillScan, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨hI, hk⟩ ?_
    rw [show jend - t.2.2 = 0 by omega]
    simp
  intro fuel
  induction fuel with
  | zero => intro t hI hf; exact exit t hI (by omega)
  | succ fuel ih =>
    intro t hI hf
    by_cases hb : t.2.2 < jend
    · have hbt : fillBf jend t = true := by simp [fillBf, hb]
      obtain ⟨hPt, hInv'⟩ := hs t hI hbt
      have hIs : fillBf jend t = true → ElimSynth2.fillP tgt alv rnk i t := fun _ => hPt
      have hk' : (fillStep tgt alv rnk i ri t).2.2 = t.2.2 + 1 := by
        simp only [fillStep]
        split <;> [split; skip] <;> rfl
      have hih := ih (fillStep tgt alv rnk i ri t) hInv' (by rw [hk']; omega)
      rw [hk'] at hih
      have hcost : irUnit Currency.«while»
          + (liftACost ElimSynth2.fillC
            + liftACost ((jend - (t.2.2 + 1)) • iter ElimSynth2.fillC + cu Currency.«while»))
          = liftACost ((jend - t.2.2) • iter ElimSynth2.fillC + cu Currency.«while») := by
        rw [show jend - t.2.2 = (jend - (t.2.2 + 1)) + 1 by omega, succ_nsmul]
        simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
        ac_rfl
      calc fillScan tgt alv rnk i ri jend t
          = NRest.consume (NRest.bindT (fillF tgt alv rnk i ri t)
              fun t' => fillScan tgt alv rnk i ri jend t') (irUnit Currency.«while») := by
            simp only [fillScan]; rw [irWhileIT_of_true hIs hbt]
        _ ≤ NRest.consume (NRest.bindT
              (NRest.consume (NRest.returnT (fillStep tgt alv rnk i ri t))
                (liftACost ElimSynth2.fillC))
              fun t' => fillScan tgt alv rnk i ri jend t') (irUnit Currency.«while») :=
            NRest.consume_mono
              (NRest.bindT_mono (fillF_le tgt alv rnk i ri t hPt) fun _ => le_rfl) le_rfl
        _ = NRest.consume (NRest.consume
              (fillScan tgt alv rnk i ri jend (fillStep tgt alv rnk i ri t))
              (liftACost ElimSynth2.fillC)) (irUnit Currency.«while») := by rw [bindT_unitT]
        _ ≤ _ := by
            rw [← hcost]
            exact NRest.consume_mono (NRest.consume_mono hih le_rfl) le_rfl |>.trans
              (le_of_eq (by rw [Sepref.consume_spec, Sepref.consume_spec]))
    · exact exit t hI (by omega)

end Scan

/-! ## 2. One row, and the pass

The row's invariant is the pointer one: `ifl[i]` starts at or below the
row's first slot and gains at most one per slot passed, so it stays
below `off[i+1]! ≤ off[n]!`. Everything else is lengths and the frame
(`ifl` is touched only at `i`). -/

section Row

variable {n W : ℕ} {off tgt alv rnk : List ℕ}

/-- The row scan's invariant: the two arrays at their lengths, the slot
index inside the row, the fill pointer at most the slot index, and the
pointer array untouched away from the row's own vertex. -/
def RowInv (n W : ℕ) (off : List ℕ) (fl₀ : List ℕ) (i : ℕ) : FS → Prop := fun z =>
  z.1.length = W ∧ z.2.1.length = n ∧ off[i]! ≤ z.2.2 ∧ z.2.2 ≤ off[i + 1]! ∧
    z.2.1[i]! ≤ z.2.2 ∧ ∀ v, v ≠ i → z.2.1[v]! = fl₀[v]!

theorem fillRowF_le (hsh : Shape n off tgt alv) (hr : rnk.length = n)
    (hW : off[n]! ≤ W) (t : FS)
    (hitg : t.1.length = W) (hfl : t.2.1.length = n) (hi : t.2.2 < n)
    (hstart : t.2.1[t.2.2]! ≤ off[t.2.2]!) :
    fillRowF n off tgt alv rnk t
      ≤ NRest.spec
          (fun t' : FS => t'.1.length = W ∧ t'.2.1.length = n ∧ t'.2.2 = t.2.2 + 1 ∧
            ∀ v, v ≠ t.2.2 → t'.2.1[v]! = t.2.1[v]!)
          (fun _ => liftACost (fillRowC + (off[t.2.2 + 1]! - off[t.2.2]!)
            • iter ElimSynth2.fillC)) := by
  have holen : off.length = n + 1 := hsh.1
  have halen : alv.length = n := hsh.2.1
  have h0 : t.2.2 < off.length := by omega
  have h1 : t.2.2 + 1 < off.length := by omega
  have hmono : off[t.2.2]! ≤ off[t.2.2 + 1]! := hsh.2.2.1 _ hi
  have htop : off[t.2.2 + 1]! ≤ off[n]! := hsh.mono' (by omega) le_rfl
  have hrow : off[t.2.2 + 1]! ≤ tgt.length := hsh.row_le hi
  have hai : t.2.2 < alv.length := by omega
  -- the scan's step keeps the invariant and gives `fillP` at every slot
  have hs : ∀ z : FS, RowInv n W off t.2.1 t.2.2 z →
      fillBf off[t.2.2 + 1]! z = true →
      ElimSynth2.fillP tgt alv rnk t.2.2 z ∧
        RowInv n W off t.2.1 t.2.2 (fillStep tgt alv rnk t.2.2 rnk[t.2.2]! z) := by
    rintro z ⟨hz1, hz2, hz3, hz4, hz5, hz6⟩ hzb
    have hzlt : z.2.2 < off[t.2.2 + 1]! := by simpa [fillBf] using hzb
    have hzt : z.2.2 < tgt.length := by omega
    have hun : tgt[z.2.2]! < n := hsh.2.2.2.2 _ hzt
    have hP : ElimSynth2.fillP tgt alv rnk t.2.2 z :=
      ⟨hzt, by omega, by omega, by omega, by omega⟩
    refine ⟨hP, ?_⟩
    by_cases hb1 : 0 < alv[tgt[z.2.2]!]!
    · by_cases hb2 : rnk[tgt[z.2.2]!]! < rnk[t.2.2]!
      · have hstep : fillStep tgt alv rnk t.2.2 rnk[t.2.2]! z
            = (z.1.set z.2.1[t.2.2]! tgt[z.2.2]!,
                z.2.1.set t.2.2 (z.2.1[t.2.2]! + 1), z.2.2 + 1) := by
          simp only [fillStep, if_pos hb1, if_pos hb2]
        rw [hstep]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · show (z.1.set z.2.1[t.2.2]! tgt[z.2.2]!).length = W
          rw [List.length_set]; exact hz1
        · show (z.2.1.set t.2.2 (z.2.1[t.2.2]! + 1)).length = n
          rw [List.length_set]; exact hz2
        · show off[t.2.2]! ≤ z.2.2 + 1
          omega
        · show z.2.2 + 1 ≤ off[t.2.2 + 1]!
          omega
        · show (z.2.1.set t.2.2 (z.2.1[t.2.2]! + 1))[t.2.2]! ≤ z.2.2 + 1
          rw [get!_set _ _ _ _ (by omega), if_pos rfl]
          omega
        · intro v hv
          show (z.2.1.set t.2.2 (z.2.1[t.2.2]! + 1))[v]! = t.2.1[v]!
          rw [get!_set _ _ _ _ (by omega), if_neg hv]
          exact hz6 v hv
      · have hstep : fillStep tgt alv rnk t.2.2 rnk[t.2.2]! z = (z.1, z.2.1, z.2.2 + 1) := by
          simp only [fillStep, if_pos hb1, if_neg hb2]
        rw [hstep]
        exact ⟨hz1, hz2, by show off[t.2.2]! ≤ z.2.2 + 1; omega,
          by show z.2.2 + 1 ≤ off[t.2.2 + 1]!; omega,
          by show z.2.1[t.2.2]! ≤ z.2.2 + 1; omega, hz6⟩
    · have hstep : fillStep tgt alv rnk t.2.2 rnk[t.2.2]! z = (z.1, z.2.1, z.2.2 + 1) := by
        simp only [fillStep, if_neg hb1]
      rw [hstep]
      exact ⟨hz1, hz2, by show off[t.2.2]! ≤ z.2.2 + 1; omega,
        by show z.2.2 + 1 ≤ off[t.2.2 + 1]!; omega,
        by show z.2.1[t.2.2]! ≤ z.2.2 + 1; omega, hz6⟩
  have hstartI : RowInv n W off t.2.1 t.2.2 (t.1, t.2.1, off[t.2.2]!) :=
    ⟨hitg, hfl, le_rfl, hmono, hstart, fun _ _ => rfl⟩
  have hscan : fillScan tgt alv rnk t.2.2 rnk[t.2.2]! off[t.2.2 + 1]!
        (t.1, t.2.1, off[t.2.2]!)
      ≤ NRest.spec
          (fun t' : FS => RowInv n W off t.2.1 t.2.2 t' ∧ off[t.2.2 + 1]! ≤ t'.2.2)
          (fun _ => liftACost ((off[t.2.2 + 1]! - off[t.2.2]!) • iter ElimSynth2.fillC
            + cu Currency.«while»)) :=
    fillScan_le (Inv := RowInv n W off t.2.1 t.2.2) tgt alv rnk t.2.2
      rnk[t.2.2]! off[t.2.2 + 1]! hs (off[t.2.2 + 1]! - off[t.2.2]!) _ hstartI (by simp)
  have hri : t.2.2 < rnk.length := by omega
  -- the row's tail: the pair the branch returns, re-assembled with the bumped index
  have hK : ∀ x : FS, (RowInv n W off t.2.1 t.2.2 x ∧ off[t.2.2 + 1]! ≤ x.2.2) →
      NRest.consume (NRest.returnT ((x.1, x.2.1, t.2.2 + 1) : FS))
          (irUnit Currency.skip
            + (irUnit Currency.add + (irUnit Currency.skip + irUnit Currency.skip)))
        ≤ NRest.spec
            (fun t' : FS => t'.1.length = W ∧ t'.2.1.length = n ∧ t'.2.2 = t.2.2 + 1 ∧
              ∀ v, v ≠ t.2.2 → t'.2.1[v]! = t.2.1[v]!)
            (fun _ => irUnit Currency.skip
              + (irUnit Currency.add + (irUnit Currency.skip + irUnit Currency.skip))) := by
    rintro x ⟨⟨hx1, hx2, -, -, -, hx6⟩, -⟩
    exact consume_returnT_le_spec ⟨hx1, hx2, rfl, hx6⟩ le_rfl
  by_cases hb : 0 < alv[t.2.2]!
  · simp only [fillRowF, pack3f, mopAget_def, mopBinop_def, mopPair_def, mopSucc_eq,
      irIf_def, NRest.assert_pos hai, NRest.assert_pos h0, NRest.assert_pos h1,
      NRest.assert_pos hri, NRest.returnT_bindT,
      NRest.bindT_consume NRest.addSupContinuousB_acost,
      NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add,
      decide_eq_true_eq, if_pos hb, NRest.bindT_assoc_acost]
    refine le_trans (NRest.consume_mono
      (le_trans (NRest.bindT_mono hscan fun _ => le_rfl)
        (bindT_spec_le _ _ _ _ _ hK)) le_rfl) (le_of_eq ?_)
    rw [Sepref.consume_spec]
    refine congrArg (NRest.spec _) (funext fun _ => ?_)
    simp only [fillRowC, iter, liftACost_add, liftACost_nsmul, liftACost_cu]
    ac_rfl
  · simp only [fillRowF, pack3f, mopAget_def, mopBinop_def, mopPair_def, mopSucc_eq,
      irIf_def, NRest.assert_pos hai, NRest.returnT_bindT,
      NRest.bindT_consume NRest.addSupContinuousB_acost,
      NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add,
      decide_eq_true_eq, if_neg hb, NRest.bindT_assoc_acost]
    refine consume_returnT_le_spec ⟨hitg, hfl, rfl, fun _ _ => rfl⟩ ?_
    have hsplit : liftACost (fillRowC
          + (off[t.2.2 + 1]! - off[t.2.2]!) • iter ElimSynth2.fillC)
        = (irUnit Currency.aget + (irUnit Currency.ite + (irUnit Currency.skip
            + (irUnit Currency.add + (irUnit Currency.skip + irUnit Currency.skip)))))
          + ((irUnit Currency.aget + irUnit Currency.aget + irUnit Currency.aget
              + irUnit Currency.add + irUnit Currency.skip + irUnit Currency.skip
              + irUnit Currency.«while»)
            + liftACost ((off[t.2.2 + 1]! - off[t.2.2]!) • iter ElimSynth2.fillC)) := by
      simp only [fillRowC, liftACost_add, liftACost_cu]
      ac_rfl
    rw [hsplit]
    exact cost_le_add _ _

/-! ### The pass

The outer loop's energy is the degree pass's: one `fillRowC` per vertex
still to visit, one `fillC` per adjacency slot still to scan. The rows
tile the target array, so the second currency is bounded by `off[n]!`
however the branch falls. -/

theorem fillPass_le (hsh : Shape n off tgt alv) (hr : rnk.length = n)
    (hW : off[n]! ≤ W) (ID : ℕ → ℕ) (hID : ∀ v ≤ n, RamElim.psum ID v ≤ off[v]!) :
    ∀ (fuel : ℕ) (t : FS), t.1.length = W → t.2.1.length = n → t.2.2 ≤ n →
      -- (the block structure's own lengths are `hsh`'s first two clauses)
      n - t.2.2 ≤ fuel → (∀ v, t.2.2 ≤ v → v < n → t.2.1[v]! = RamElim.psum ID v) →
      fillPass n off tgt alv rnk t
        ≤ NRest.spec (fun t' : FS => t'.1.length = W ∧ t'.2.1.length = n)
            (fun _ => liftACost (E2 (iter fillRowC) (iter ElimSynth2.fillC) (n - t.2.2)
              (off[n]! - off[t.2.2]!) + cu Currency.«while»)) := by
  have holen : off.length = n + 1 := hsh.1
  have halen : alv.length = n := hsh.2.1
  have exit : ∀ t : FS, t.1.length = W → t.2.1.length = n → n ≤ t.2.2 →
      fillPass n off tgt alv rnk t
        ≤ NRest.spec (fun t' : FS => t'.1.length = W ∧ t'.2.1.length = n)
            (fun _ => liftACost (E2 (iter fillRowC) (iter ElimSynth2.fillC) (n - t.2.2)
              (off[n]! - off[t.2.2]!) + cu Currency.«while»)) := by
    intro t hitg hfl hge
    have hb : fillRowBf n t = false := by
      simp only [fillRowBf, decide_eq_false_iff_not]
      omega
    simp only [fillPass, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨hitg, hfl⟩ ?_
    rw [liftACost_add, liftACost_cu, add_comm]
    exact cost_le_add _ _
  intro fuel
  induction fuel with
  | zero => intro t hitg hfl hle hf hall; exact exit t hitg hfl (by omega)
  | succ fuel ih =>
    intro t hitg hfl hle hf hall
    by_cases hb : t.2.2 < n
    · have hbt : fillRowBf n t = true := by simp [fillRowBf, hb]
      have hIs : fillRowBf n t = true → fillRowP n off alv rnk t := fun _ =>
        ⟨by omega, by omega, by omega, by omega⟩
      have hmono : off[t.2.2]! ≤ off[t.2.2 + 1]! := hsh.2.2.1 _ hb
      have htop : off[t.2.2 + 1]! ≤ off[n]! := hsh.mono' (by omega) le_rfl
      have hstart : t.2.1[t.2.2]! ≤ off[t.2.2]! := by
        rw [hall t.2.2 le_rfl hb]; exact hID t.2.2 (by omega)
      have hcont : ∀ t' : FS, (t'.1.length = W ∧ t'.2.1.length = n ∧ t'.2.2 = t.2.2 + 1 ∧
            ∀ v, v ≠ t.2.2 → t'.2.1[v]! = t.2.1[v]!) →
          fillPass n off tgt alv rnk t'
            ≤ NRest.spec (fun t'' : FS => t''.1.length = W ∧ t''.2.1.length = n)
                (fun _ => liftACost (E2 (iter fillRowC) (iter ElimSynth2.fillC)
                  (n - (t.2.2 + 1)) (off[n]! - off[t.2.2 + 1]!) + cu Currency.«while»)) := by
        rintro t' ⟨h1, h2, h3, h4⟩
        refine le_trans (ih t' h1 h2 (by omega) (by omega) ?_) (le_of_eq ?_)
        · intro v hv hvn
          rw [h3] at hv
          rw [h4 v (by omega)]
          exact hall v (by omega) hvn
        · rw [h3]
      have hcost : irUnit Currency.«while»
          + (liftACost (fillRowC + (off[t.2.2 + 1]! - off[t.2.2]!) • iter ElimSynth2.fillC)
            + liftACost (E2 (iter fillRowC) (iter ElimSynth2.fillC) (n - (t.2.2 + 1))
                (off[n]! - off[t.2.2 + 1]!) + cu Currency.«while»))
          = liftACost (E2 (iter fillRowC) (iter ElimSynth2.fillC) (n - t.2.2)
              (off[n]! - off[t.2.2]!) + cu Currency.«while») := by
        rw [show n - t.2.2 = (n - (t.2.2 + 1)) + 1 by omega,
          show off[n]! - off[t.2.2]!
            = (off[n]! - off[t.2.2 + 1]!) + (off[t.2.2 + 1]! - off[t.2.2]!) by omega,
          E2_split]
        simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
        ac_rfl
      calc fillPass n off tgt alv rnk t
            = NRest.consume (NRest.bindT (fillRowF n off tgt alv rnk t)
                fun t' => fillPass n off tgt alv rnk t') (irUnit Currency.«while») := by
              simp only [fillPass]; rw [irWhileIT_of_true hIs hbt]
          _ ≤ NRest.consume (NRest.spec _ (fun _ =>
                liftACost (fillRowC + (off[t.2.2 + 1]! - off[t.2.2]!) • iter ElimSynth2.fillC)
                + liftACost (E2 (iter fillRowC) (iter ElimSynth2.fillC) (n - (t.2.2 + 1))
                    (off[n]! - off[t.2.2 + 1]!) + cu Currency.«while»)))
                (irUnit Currency.«while») :=
              NRest.consume_mono
                (le_trans (NRest.bindT_mono
                    (fillRowF_le hsh hr hW t hitg hfl hb hstart) fun _ => le_rfl)
                  (bindT_spec_le _ _ _ _ _ hcont)) le_rfl
          _ = _ := by rw [Sepref.consume_spec, ← hcost]
    · exact exit t hitg hfl (by omega)

end Row

/-! ## 3. The block starts do not overtake the block structure

The one piece of mathematics the walk needs. `ElimAnswer` says the
recorded extraction degree of a vertex *is* the in-degree of the
elimination orientation; the in-neighbours of a vertex are a subset of
its arena neighbours, and those are counted by the live slots of its
row. So `ID v ≤ off[v+1]! − off[v]!`, and the running sum of the block
lengths never passes the running sum of the row lengths. -/

section Starts

open Lax3Proofs.Augmentation (nbrsIn mem_nbrsIn)
open Lax3Proofs.RamBfs (masked)

variable {n ns W : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}

/-- **A block is no longer than its row.** -/
theorem idg_le_rowLen (hin : EIn n ns W G off tgt alv) {e : ES}
    (hans : ElimAnswer n ns G alv e) {v : ℕ} (hv : v < n) :
    e.2.2.2.1[v]! ≤ off[v + 1]! - off[v]! := by
  have hcard := hans.2.2.2.2.1 ⟨v, hv⟩
  rw [larr_apply] at hcard
  by_cases hM : larr alv v = 0
  · rw [hcard, RamElim.inN_of_dead hv hM, Finset.card_empty]
    exact Nat.zero_le _
  · have hsub : (RamElim.ElimCert.elimOr (masked G (larr alv))
          (fun z : Fin n => larr e.2.2.1 (z : ℕ))).inN ⟨v, hv⟩
        ⊆ nbrsIn (masked G (larr alv)) Finset.univ (⟨v, hv⟩ : Fin n) := fun u hu =>
      mem_nbrsIn.2 ⟨Finset.mem_univ _, (RamElim.ElimCert.mem_elimOr.1 hu).1⟩
    rw [hcard]
    calc ((RamElim.ElimCert.elimOr (masked G (larr alv))
            (fun z : Fin n => larr e.2.2.1 (z : ℕ))).inN ⟨v, hv⟩).card
        ≤ (nbrsIn (masked G (larr alv)) Finset.univ (⟨v, hv⟩ : Fin n)).card :=
          Finset.card_le_card hsub
      _ = RamElim.adeg G (larr alv) v := (RamElim.adeg_eq hv).symm
      _ = (RamElim.liveSlots (larr off) (larr tgt) (larr alv) v).card :=
          RamElim.adeg_of_alive hin.csr hv hM
      _ ≤ (Finset.Ico (larr off v) (larr off (v + 1))).card :=
          Finset.card_filter_le _ _
      _ = off[v + 1]! - off[v]! := by rw [Nat.card_Ico, larr_apply, larr_apply]

/-- **…so the running sums never cross.** -/
theorem psum_idg_le (hin : EIn n ns W G off tgt alv) {e : ES}
    (hans : ElimAnswer n ns G alv e) :
    ∀ v ≤ n, RamElim.psum (larr e.2.2.2.1) v ≤ off[v]! := by
  have hsh : Shape n off tgt alv := by
    refine ⟨hin.offLen, hin.alvLen, fun i hi => hin.csr.csr.mono i hi, ?_, fun j hj => ?_⟩
    · rw [← larr_apply off n, hin.csr.csr.last, hin.tgtLen]
    · rw [hin.tgtLen] at hj
      exact hin.csr.csr.target_lt j hj
  intro v
  induction v with
  | zero =>
    intro _
    rw [RamElim.psum_zero, ← larr_apply off 0, hin.csr.csr.zero]
  | succ v ih =>
    intro hv
    have hmono : off[v]! ≤ off[v + 1]! := hsh.2.2.1 v (by omega)
    have h1 : RamElim.psum (larr e.2.2.2.1) v ≤ off[v]! := ih (by omega)
    have h2 : larr e.2.2.2.1 v ≤ off[v + 1]! - off[v]! :=
      idg_le_rowLen hin hans (by omega)
    rw [RamElim.psum_succ]
    omega

/-- **The fill pass, at the engine's boundary.** Handed the in-lists
the offset pass opened and a scratch array at the block structure's
width, the pass leaves both at their lengths, at the two-currency
price. -/
theorem fillPass_spec (hin : EIn n ns W G off tgt alv) {e : ES}
    (hans : ElimAnswer n ns G alv e) {itg₀ ifl : List ℕ} (hitg : itg₀.length = W)
    (hfl : ifl.length = n)
    (hfl0 : ∀ v < n, ifl[v]! = RamElim.psum (larr e.2.2.2.1) v) :
    fillPass n off tgt alv e.2.2.1 (itg₀, ifl, 0)
      ≤ NRest.spec (fun t : FS => t.1.length = W ∧ t.2.1.length = n)
          (fun _ => liftACost (E2 (iter fillRowC) (iter ElimSynth2.fillC) n ns
            + cu Currency.«while»)) := by
  have hsh : Shape n off tgt alv := by
    refine ⟨hin.offLen, hin.alvLen, fun i hi => hin.csr.csr.mono i hi, ?_, fun j hj => ?_⟩
    · rw [← larr_apply off n, hin.csr.csr.last, hin.tgtLen]
    · rw [hin.tgtLen] at hj
      exact hin.csr.csr.target_lt j hj
  have hoffn : off[n]! = ns := by rw [← larr_apply off n, hin.csr.csr.last]
  have hoff0 : off[0]! = 0 := by rw [← larr_apply off 0, hin.csr.csr.zero]
  have hwide : ns ≤ W := hin.wide
  refine le_trans (fillPass_le hsh hans.1 (by omega) (larr e.2.2.2.1)
    (psum_idg_le hin hans) n (itg₀, ifl, 0) hitg hfl (Nat.zero_le n) le_rfl
    (fun v _ hvn => hfl0 v hvn)) (spec_mono (fun _ h => h) ?_)
  intro _ _
  show liftACost (E2 (iter fillRowC) (iter ElimSynth2.fillC) (n - (0 : ℕ)) _ + _)
    ≤ liftACost (E2 (iter fillRowC) (iter ElimSynth2.fillC) n ns + cu Currency.«while»)
  rw [hoffn, hoff0, Nat.sub_zero, Nat.sub_zero]

end Starts

/-! ## 4. The engine at five phases

`elimEngine_le`'s four passes with the fill on top: the degrees, the
buckets, the elimination, the offsets, the in-lists. -/

section Engine5

open Lax13Proofs.Reasoning (arrOf)

variable {n ns W : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}

/-- **The elimination engine at five phases.** -/
noncomputable def elimEngine5 (n : ℕ) (off tgt alv : List ℕ)
    (deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀ : List ℕ) :
    NRest (ES × OS × FS) ECost :=
  bindT (elimEngine n off tgt alv deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀) fun p =>
    bindT (fillPass n off tgt alv p.1.2.2.1 (itg₀, p.2.2.1, 0)) fun f =>
      NRest.returnT (p.1, p.2, f)

/-- **What the five phases leave**: `EngineOut`, and the in-list arrays
at their lengths. -/
def EngineOut5 (n ns W : ℕ) (G : SimpleGraph (Fin n)) (alv : List ℕ)
    (q : ES × OS × FS) : Prop :=
  EngineOut n ns G alv (q.1, q.2.1) ∧ q.2.2.1.length = W ∧ q.2.2.2.1.length = n

/-- The five phases' price: the four passes' own and the fill's. -/
noncomputable def engineC5 (n ns : ℕ) : ACost String ℕ :=
  engineC n ns + (E2 (iter fillRowC) (iter ElimSynth2.fillC) n ns + cu Currency.«while»)

/-- **THE FIVE-PHASE EXPORT.** Against `RamElim.Implements`'s input
surface — a block structure, a mask and scratch at its lengths, the
in-list target array included — the five passes deliver
`RamElim.AfterLoop`'s answer, the in-list offsets `AfterOff` adds, and
the in-list array at the block structure's width, at the sum of the
five passes' derived prices. -/
theorem elimEngine5_le (hcsr : RamElim.CsrSimple G ns O T) (hW : ns ≤ W)
    {deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀ : List ℕ}
    (hdeg : deg₀.length = n) (helm : elm₀.length = n) (helm0 : ∀ v < n, elm₀[v]! = 0)
    (hrnk : rnk₀.length = n) (hidg : idg₀.length = n)
    (hbh : bh₀.length = n + 1) (hbh0 : ∀ j ≤ n, bh₀[j]! = 0)
    (hbv : bv₀.length = n + W + 1) (hbn : bn₀.length = n + W + 1)
    (hio : ioff₀.length = n + 1) (hio0 : ioff₀[0]! = 0) (hifl : ifl₀.length = n)
    (hitg : itg₀.length = W) :
    elimEngine5 n (arrOf (n + 1) O) (arrOf ns T) (arrOf n M)
        deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀
      ≤ NRest.spec (EngineOut5 n ns W G (arrOf n M))
          (fun _ => liftACost (engineC5 n ns)) := by
  have hin : EIn n ns W G (arrOf (n + 1) O) (arrOf ns T) (arrOf n M) := eIn_arrOf hcsr hW
  rw [elimEngine5, engineC5]
  refine seqA_le (elimEngine_le hcsr hW hdeg helm helm0 hrnk hidg hbh hbh0 hbv hbn
    hio hio0 hifl) fun p hp => ?_
  exact bindA_ret (fillPass_spec hin hp.1 hitg hp.2.2.1 hp.2.2.2.2) fun f hf =>
    ⟨hp, hf.1, hf.2⟩

/-- **The five phases' cost**: `333·n + 168·ns + 45` IMP+ time units,
against the hand-walked baseline's `293·n + 176·ns + 94` for the same
five phases (`RamElim.implements`'s `w1`–`w5`). The fill alone is
`37·n + 41·ns + 4` against the baseline's `32·n + 32·ns + 10`: dearer
on both coefficients, and the whole of the difference is the
state-as-resource `skip`s of a three-component loop state run twice
(F-a). At the demo's size the tower's five-phase figure is *above* the
baseline's — the first phase boundary where it is, and the number is
derived rather than chosen. -/
def fillK (n ns : ℕ) : ℕ := 37 * n + 41 * ns + 4

theorem cash_fillBudget (n ns : ℕ) :
    Codegen.cash (E2 (iter fillRowC) (iter ElimSynth2.fillC) n ns + cu Currency.«while»)
      = fillK n ns := by
  rw [E2, Codegen.cash_add, Codegen.cash_add, BfsQSynth.cash_nsmul, BfsQSynth.cash_nsmul,
    cash_fillRowC, cash_fillC,
    show Codegen.cash (cu Currency.«while») = 4 from by decide +kernel, fillK]
  ring

def engineK5 (n ns : ℕ) : ℕ := 333 * n + 168 * ns + 45

theorem cash_engine5Budget (n ns : ℕ) : Codegen.cash (engineC5 n ns) = engineK5 n ns := by
  rw [engineC5, Codegen.cash_add, cash_engineBudget, cash_fillBudget, engineK, fillK,
    engineK5]
  ring

-- the fill's two figures side by side at the demo's size…
#guard fillK 5 10 = 599
#guard 32 * 5 + 32 * 10 + 10 = 490
#guard ¬ (fillK 5 10 ≤ 32 * 5 + 32 * 10 + 10)

-- …and the five phases', with the sign of the difference recorded
-- rather than assumed.
#guard engineK5 5 10 = 3390
#guard 293 * 5 + 176 * 10 + 94 = 3319
#guard ¬ (engineK5 5 10 ≤ 293 * 5 + 176 * 10 + 94)

/-! ### Negative controls on the extension

The export is a `≤` on the cost and an `=` on the length, so what
falsifies it is a cheaper price or a wrong width. -/

-- **(a) the fill is not free.** An extension that charged nothing for
-- the fifth phase would claim the four-phase figure.
#guard ¬ (engineK5 5 10 ≤ engineK 5 10)

-- **(b) the width clause is the block structure's, not the arena's.**
-- `itg` is `W` cells wide, not `n`; the twin at the demo's `W = 10`
-- refutes the `n`-wide reading.
#guard ¬ (dFill.1.length = 5)

-- **(c) the row account really carries a whole row.** A per-row charge
-- with no slot term would price the demo's ten slots at nothing.
#guard ¬ (fillK 5 10 ≤ 37 * 5 + 4)

end Engine5

/-! ## 5. `OrderSynth.ElimAvailA`, discharged

`ElimPost`'s seven clauses at the phase's boundary: five lengths, the
rank bound and the rank injectivity. Four of the lengths and both rank
clauses come off `ElimAnswer`/`EngineOut`; the fifth — `itg.length = W`
— is the fill's, and is what §4 adds.

**2E/D-a, as the interface actually reads.** `ElimAvailA` quantifies
over *arbitrary* `off`, `tgt`, `alv`: it asks the engine to meet
`ElimPost` at arrays that need not be a block structure at all. An
engine that needs `CsrSimple` cannot meet that, and the only witness is
one that ignores its arguments — which is sound here precisely because
`ElimPost` says nothing about the mask or the graph (it is five lengths
and two rank clauses). Both forms are below: `elimPost_of_engine` is
the instantiation an integration composes, and `elimAvailA_of_engine`
is the hypothesis `orderPhase0_le` literally takes. -/

section Avail

open Lax13Proofs.Reasoning (arrOf)

variable {n ns W : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}

/-- **What the phase reads of the engine**: the ranks, the extraction
degrees and the block heads it re-zeroes, and the in-list block
structure it copies. At `R = 0` the two scratch arrays are written and
never read, which is why the offsets stand in for the second of
them. -/
def elimOutOf (q : ES × OS × FS) : OrderSynth.ElimOut :=
  (q.1.2.2.1, q.1.2.2.2.1, q.2.1.1, q.2.1.1, q.2.2.1)

/-- The engine, read into the phase's vocabulary. -/
noncomputable def elimProgram (n : ℕ) (off tgt alv : List ℕ)
    (deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀ : List ℕ) :
    NRest OrderSynth.ElimOut ECost :=
  bindT (elimEngine5 n off tgt alv deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀)
    fun q => NRest.returnT (elimOutOf q)

/-- **`ElimPost`, off the five-phase export.** -/
theorem elimPost_of_engine (hcsr : RamElim.CsrSimple G ns O T) (hW : ns ≤ W)
    {deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀ : List ℕ}
    (hdeg : deg₀.length = n) (helm : elm₀.length = n) (helm0 : ∀ v < n, elm₀[v]! = 0)
    (hrnk : rnk₀.length = n) (hidg : idg₀.length = n)
    (hbh : bh₀.length = n + 1) (hbh0 : ∀ j ≤ n, bh₀[j]! = 0)
    (hbv : bv₀.length = n + W + 1) (hbn : bn₀.length = n + W + 1)
    (hio : ioff₀.length = n + 1) (hio0 : ioff₀[0]! = 0) (hifl : ifl₀.length = n)
    (hitg : itg₀.length = W) :
    elimProgram n (arrOf (n + 1) O) (arrOf ns T) (arrOf n M)
        deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀
      ≤ NRest.spec (OrderSynth.ElimPost n W) (fun _ => liftACost (engineC5 n ns)) := by
  refine bindA_ret (elimEngine5_le hcsr hW hdeg helm helm0 hrnk hidg hbh hbh0 hbv hbn
    hio hio0 hifl hitg) fun q hq => ?_
  obtain ⟨⟨hans, hioffLen, hiflLen, -, -⟩, hitgLen, -⟩ := hq
  refine ⟨hans.1, hans.2.1, hioffLen, hioffLen, hitgLen, hans.2.2.1, fun v hv w hw hvw => ?_⟩
  have hinj := hans.2.2.2.1.inj (a₁ := (⟨v, hv⟩ : Fin n)) (a₂ := (⟨w, hw⟩ : Fin n))
  exact congrArg Fin.val (hinj (by simpa [larr_apply] using hvw))

/-- **`ElimAvailA`, discharged.** The engine at a block structure is a
witness for the phase's hypothesis at that block structure's own
arena. -/
theorem elimAvailA_of_engine (hcsr : RamElim.CsrSimple G ns O T) (hW : ns ≤ W)
    {deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀ : List ℕ}
    (hdeg : deg₀.length = n) (helm : elm₀.length = n) (helm0 : ∀ v < n, elm₀[v]! = 0)
    (hrnk : rnk₀.length = n) (hidg : idg₀.length = n)
    (hbh : bh₀.length = n + 1) (hbh0 : ∀ j ≤ n, bh₀[j]! = 0)
    (hbv : bv₀.length = n + W + 1) (hbn : bn₀.length = n + W + 1)
    (hio : ioff₀.length = n + 1) (hio0 : ioff₀[0]! = 0) (hifl : ifl₀.length = n)
    (hitg : itg₀.length = W) :
    OrderSynth.ElimAvailA n W
      (fun _ _ _ => elimProgram n (arrOf (n + 1) O) (arrOf ns T) (arrOf n M)
        deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀)
      (engineC5 n ns) := fun _ _ _ =>
  elimPost_of_engine hcsr hW hdeg helm helm0 hrnk hidg hbh hbh0 hbv hbn hio hio0 hifl hitg

end Avail

/-! ## 6. What is landed, and what is left (F1)

**F1's range and length half — paid.** `fillScan_le` runs the fill's
row scan at an arbitrary invariant; `fillRowF_le` runs one row on the
pointer invariant `ifl[i]! ≤ j`; `fillPass_le` runs the pass on the
degree pass's two-currency energy. `psum_idg_le` is the pass's one
piece of mathematics — the block starts never overtake the row starts —
and it is `ElimAnswer`'s in-degree clause plus `card_liveSlots`,
consumed, not re-proved. `elimEngine5_le` is the engine at five phases,
and `elimAvailA_of_engine` closes `OrderSynth`'s hypothesis.

**F1's content half — still open.** `RamElim.fillPass_spec`'s `InCsr`
— that block `w` holds *exactly* the in-neighbours of `w` in the
elimination orientation — is not carried here. Its mathematics
(`written`, `written_succ_of_take`, `not_mem_written`, `written_last`,
`exists_block`, `inN_of_dead`) is stated over functions `ℕ → ℕ` and is
consumed by `larr` verbatim; what is missing is `FillSt`'s content
clauses at the list layer. `fillScan_le` takes the invariant as a
parameter, so the content walk plugs into the same lemma: it is a
strengthening of `RowInv`, not a re-derivation.

**Why the range half suffices for the consumer.** `OrderSynth.ElimPost`
— and `RamDriver.OrderImplements` behind it, at `R = 0` — reads five
lengths and two rank clauses off the elimination. The in-lists are
copied into `doff`/`dtg` and never read: the augmentation round that
would read them is the `R > 0` case, and that is where the content half
becomes load-bearing.

**The cost, honestly.** The fill is the first phase boundary where the
tower is *dearer* than the hand-walked baseline on both coefficients
(`37 n + 41 ns + 4` against `32 n + 32 ns + 10`), and the five-phase
total follows it (`333 n + 168 ns + 45` against `293 n + 176 ns + 94`;
at the demo's size, 3 390 against 3 319). The whole of the gap is the
`mopPair` skips of the three-component loop state, paid on every
iteration of *both* loops — F-a's standing cost, now measured on a
nested pass. -/

/-! ## 7. Axioms -/

/-- info: 'Lax3Proofs.Refine.ElimSynth6.elimEngine5_le' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms elimEngine5_le

/-- info: 'Lax3Proofs.Refine.ElimSynth6.fillPass_le' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms fillPass_le

/-- info: 'Lax3Proofs.Refine.ElimSynth6.psum_idg_le' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms psum_idg_le

/-- info: 'Lax3Proofs.Refine.ElimSynth6.elimAvailA_of_engine' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms elimAvailA_of_engine

end Lax3Proofs.Refine.ElimSynth6
