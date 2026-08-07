import Lax3Proofs.RamScatter
import Lax3Proofs.Refine.BfsBridge
import Lax13Proofs.Refine.Examples.BfsQSynth
import Lax13Proofs.Refine.Sepref.Examples.WordAssnSpike
import Lax13Proofs.Refine.Sepref.IrOpsExtra

/-!
# ND-MC rebase P2 / satellite 2A — the scatter engine's marking sweep,
re-derived through the refinement tower

`Lax3Proofs.RamScatter` is the greedy scatter pass. Its three phases are

1. `clearExc` — zero the exclusion bits (a flat pass over the carrier);
2. `scatterLoop` — the greedy scan, whose picking branch runs **the whole
   depth-capped search** (`RamBfs.bfsCom`) and then
3. `markCom` — the marking sweep, a flat pass over the carrier applying
   `RamScatter.markVal` pointwise.

This file re-derives **all three phases** through the tower, end to end:
abstract `NRest` program → correctness → `sepref_synth` → `BRefine`
bounds → cashing → a `Reasoning.Spec` export in the baseline's own
vocabulary.

Sections 1–11 are satellite 2A: phases 1 and 3 derived, and the
architectural finding about phase 2 (§8b probes the frame-layer gap,
§9 prices the rest). Sections 12–17 are **wave 2A′**, written after tool
wave T1 closed that gap: phase 2 — the greedy scan, with the whole
depth-capped search inside its picking branch and the marking sweep
after it — derived the same way, and the three phases assembled into one
engine (§16) in `RamScatter.scatterCom`'s own shape. The marking sweep
therefore appears twice: once standalone (§1–§10, at the `mk*` cells)
and once inside the scan (§12, at the search's own scratch cells).

## What is consumed rather than re-proved

`RamScatter.markVal` and `RamScatter.markVal_eq_zero_iff` are the
baseline's own arithmetic, cited. The tower re-derives the *program*
that computes `markVal` pointwise; the meaning of `markVal` — the bit
stays clear exactly when it was clear and the search put the vertex out
of range — is landed capital and is not restated.

## Judgment calls

**R2A/D-a — `markExpr` becomes five three-address operations.** The
baseline writes the marking arithmetic as one IMP+ `Expr`
(`1 - (1 - exc[sw]) * (1 - ((r+1) - dist[sw]))`, `RamScatter.markExpr`).
The IR has no expression layer at all (`Ir/Syntax.lean` ledger D2: three
addresses, operands are cells), so the same arithmetic is **five binops
and two array reads through seven scratch cells**. That is a *cost-only*
change and the ledger entry is here rather than hidden: the baseline
charges `10 + markExpr.size = 23` IMP+ units per cell, the tower `38`,
and the exported constants differ accordingly (§10).

**R2A/D-b — the radius enters through a cell, not a literal.** The
baseline compiles the radius into the program text (`markExpr r`), so a
different radius is a different program. The IR admits literals in
conditions only, so `r + 1` is held in the cell `"mkr"` and **one**
synthesized program serves every radius. This is strictly better for the
driver, which folds the pass over a per-atom radius list.

**R2A/D-c — the sweep's own scratch cells carry no digits.** P1/B-f: a
cell name ending in a digit is the hazard the integration wave has to
re-list. Every cell this file introduces is `"mk"`-prefixed and
digit-free, so the relisting is mechanical (§10).
-/

namespace Lax3Proofs.Refine.ScatterSynth

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Sepref.WordSpike
open Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest Lax13Proofs.Refine.Codegen
open Lax13Proofs.Refine.BfsQ (cu iter irWhile_exit get!_set liftACost_cu)

/-! ## 1. The abstract programs

Both passes are flat loops over the carrier with the array and the
counter as the loop state — the shape `BfsQ.fillLoop` already has, and
the shape `sepref_synth` translates. -/

/-- The clearing pass's body: store a zero and bump. -/
noncomputable def clearF : List ℕ × ℕ → NRest (List ℕ × ℕ) ECost := fun s =>
  bindT (mopAset s.1 s.2 0) fun E => bindT (BfsQSynth.mopSucc s.2) fun w => mopPair E w

def clearBf (n : ℕ) : List ℕ × ℕ → Bool := fun s => decide (s.2 < n)

def clearP (n : ℕ) : List ℕ × ℕ → Prop := fun s => s.1.length = n

/-- **The clearing pass** (`RamScatter.clearExc`). -/
noncomputable def clearLoop (n : ℕ) (s₀ : List ℕ × ℕ) : NRest (List ℕ × ℕ) ECost :=
  irWhileIT (fun s => clearBf n s = true → clearP n s) (clearBf n) clearF s₀

/-- The marking sweep's body, at three addresses (R2A/D-a). The five
binops are `markExpr` read inside out; `rp1` is the cell holding
`r + 1` (R2A/D-b) and `1` is the constant cell every tower program
already owns. -/
noncomputable def markF (rp1 : ℕ) (D : List ℕ) :
    List ℕ × ℕ → NRest (List ℕ × ℕ) ECost := fun s =>
  bindT (mopAget s.1 s.2) fun e =>
    bindT (mopAget D s.2) fun d =>
      bindT (mopBinop .sub 1 e) fun a =>
        bindT (mopBinop .sub rp1 d) fun b =>
          bindT (mopBinop .sub 1 b) fun c =>
            bindT (mopBinop .mul a c) fun p =>
              bindT (mopBinop .sub 1 p) fun m =>
                bindT (mopAset s.1 s.2 m) fun E =>
                  bindT (BfsQSynth.mopSucc s.2) fun w => mopPair E w

def markBf (n : ℕ) : List ℕ × ℕ → Bool := fun s => decide (s.2 < n)

def markP (n : ℕ) (D : List ℕ) : List ℕ × ℕ → Prop := fun s =>
  s.1.length = n ∧ n ≤ D.length

/-- **The marking sweep** (`RamScatter.markCom`). -/
noncomputable def markLoop (n rp1 : ℕ) (D : List ℕ) (s₀ : List ℕ × ℕ) :
    NRest (List ℕ × ℕ) ECost :=
  irWhileIT (fun s => markBf n s = true → markP n D s) (markBf n) (markF rp1 D) s₀

/-! ## 2. What one cell of each pass computes and costs -/

/-- The cell function the sweep applies, at the *shifted* radius the
program actually holds. `mkVal (r+1)` is `RamScatter.markVal r`
(`mkVal_eq_markVal`), which is what ties this file to the baseline's
arithmetic rather than to a second copy of it. -/
def mkVal (rp1 e d : ℕ) : ℕ := 1 - (1 - e) * (1 - (rp1 - d))

/-- **The tower's cell function is the baseline's.** -/
theorem mkVal_eq_markVal (r e d : ℕ) : mkVal (r + 1) e d = RamScatter.markVal r e d := rfl

theorem mkVal_le_one (rp1 e d : ℕ) : mkVal rp1 e d ≤ 1 := Nat.sub_le _ _

/-- One clearing iteration. -/
def clearC : ACost String ℕ := cu Currency.aset + cu Currency.add + cu Currency.skip

/-- One marking iteration: two reads, five arithmetic steps, the store,
the bump and the tuple. -/
def markC : ACost String ℕ :=
  cu Currency.aget + cu Currency.aget + cu (binopCurrency .sub) + cu (binopCurrency .sub)
    + cu (binopCurrency .sub) + cu (binopCurrency .mul) + cu (binopCurrency .sub)
    + cu Currency.aset + cu Currency.add + cu Currency.skip

theorem clearF_le (s : List ℕ × ℕ) (h : s.2 < s.1.length) :
    clearF s ≤ NRest.consume (NRest.returnT (s.1.set s.2 0, s.2 + 1)) (liftACost clearC) := by
  refine le_of_eq ?_
  simp only [clearF, BfsQSynth.mopSucc_eq, mopAset_def, mopBinop_def, mopPair_def,
    NRest.assert_pos h, NRest.returnT_bindT, bindT_unitT, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, clearC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

theorem markF_le (rp1 : ℕ) (D : List ℕ) (s : List ℕ × ℕ) (h : s.2 < s.1.length)
    (hd : s.2 < D.length) :
    markF rp1 D s
      ≤ NRest.consume (NRest.returnT
          (s.1.set s.2 (mkVal rp1 s.1[s.2]! D[s.2]!), s.2 + 1)) (liftACost markC) := by
  refine le_of_eq ?_
  simp only [markF, BfsQSynth.mopSucc_eq, mopAget_def, mopAset_def, mopBinop_def, mopPair_def,
    NRest.assert_pos h, NRest.assert_pos hd, NRest.returnT_bindT, bindT_unitT,
    NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, Lax13Proofs.Imp.Bop.apply_sub, Lax13Proofs.Imp.Bop.apply_mul,
    binopCurrency_add, markC, liftACost_add, liftACost_cu, mkVal]
  congr 1
  ac_rfl

/-! ## 3. The two loops, bounded

Both are `BfsQ.fillLoop_le`'s induction at their own cell function. -/

theorem clearLoop_le (n : ℕ) : ∀ (fuel : ℕ) (E : List ℕ) (i : ℕ), E.length = n → n - i ≤ fuel →
    i ≤ n → (∀ j, j < i → E[j]! = 0) →
    clearLoop n (E, i)
      ≤ NRest.spec (fun p : List ℕ × ℕ =>
            p.1.length = n ∧ p.2 = n ∧ ∀ j, j < n → p.1[j]! = 0)
          (fun _ => liftACost ((n - i) • iter clearC + cu Currency.«while»)) := by
  have exit : ∀ (E : List ℕ) (i : ℕ), E.length = n → n ≤ i → i ≤ n →
      (∀ j, j < i → E[j]! = 0) →
      clearLoop n (E, i)
        ≤ NRest.spec (fun p : List ℕ × ℕ =>
              p.1.length = n ∧ p.2 = n ∧ ∀ j, j < n → p.1[j]! = 0)
            (fun _ => liftACost ((n - i) • iter clearC + cu Currency.«while»)) := by
    intro E i hlen hf hin hj
    have hb : clearBf n (E, i) = false := by simp only [clearBf, decide_eq_false_iff_not]; omega
    simp only [clearLoop, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨hlen, by omega, fun j hjn => hj j (by omega)⟩ ?_
    rw [show n - i = 0 by omega]
    simp
  intro fuel
  induction fuel with
  | zero => intro E i hlen hf hin hj; exact exit E i hlen (by omega) hin hj
  | succ fuel ih =>
    intro E i hlen hf hin hj
    by_cases hb : i < n
    · have hbt : clearBf n (E, i) = true := by simp [clearBf, hb]
      have hIs : clearBf n ((E, i) : List ℕ × ℕ) = true → clearP n (E, i) := fun _ => hlen
      have hih := ih (E.set i 0) (i + 1) (by simp [hlen]) (by omega) (by omega) (fun j hjl => by
        rw [get!_set E i 0 j (by omega)]
        by_cases hji : j = i
        · rw [if_pos hji]
        · rw [if_neg hji]; exact hj j (by omega))
      have hcost : irUnit Currency.«while»
          + (liftACost clearC + liftACost ((n - (i + 1)) • iter clearC + cu Currency.«while»))
          = liftACost ((n - i) • iter clearC + cu Currency.«while») := by
        rw [show n - i = (n - (i + 1)) + 1 by omega, succ_nsmul]
        simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
        ac_rfl
      calc clearLoop n (E, i)
          = NRest.consume (NRest.bindT (clearF (E, i)) fun s' => clearLoop n s')
              (irUnit Currency.«while») := by
            simp only [clearLoop]; rw [irWhileIT_of_true hIs hbt]
        _ ≤ NRest.consume (NRest.bindT
              (NRest.consume (NRest.returnT (E.set i 0, i + 1)) (liftACost clearC))
              fun s' => clearLoop n s') (irUnit Currency.«while») :=
            NRest.consume_mono
              (NRest.bindT_mono (clearF_le (E, i) (by simpa [hlen] using hb)) fun _ => le_rfl)
              le_rfl
        _ = NRest.consume (NRest.consume (clearLoop n (E.set i 0, i + 1)) (liftACost clearC))
              (irUnit Currency.«while») := by rw [bindT_unitT]
        _ ≤ _ := by
            rw [← hcost]
            exact NRest.consume_mono (NRest.consume_mono hih le_rfl) le_rfl |>.trans
              (le_of_eq (by rw [Sepref.consume_spec, Sepref.consume_spec]))
    · exact exit E i hlen (by omega) hin hj

theorem markLoop_le (n rp1 : ℕ) (D E₀ : List ℕ) (hn : n ≤ D.length) :
    ∀ (fuel : ℕ) (E : List ℕ) (i : ℕ), E.length = n → n - i ≤ fuel → i ≤ n →
    (∀ j, j < i → E[j]! = mkVal rp1 E₀[j]! D[j]!) →
    (∀ j, i ≤ j → j < n → E[j]! = E₀[j]!) →
    markLoop n rp1 D (E, i)
      ≤ NRest.spec (fun p : List ℕ × ℕ =>
            p.1.length = n ∧ p.2 = n ∧ ∀ j, j < n → p.1[j]! = mkVal rp1 E₀[j]! D[j]!)
          (fun _ => liftACost ((n - i) • iter markC + cu Currency.«while»)) := by
  have exit : ∀ (E : List ℕ) (i : ℕ), E.length = n → n ≤ i → i ≤ n →
      (∀ j, j < i → E[j]! = mkVal rp1 E₀[j]! D[j]!) →
      markLoop n rp1 D (E, i)
        ≤ NRest.spec (fun p : List ℕ × ℕ =>
              p.1.length = n ∧ p.2 = n ∧ ∀ j, j < n → p.1[j]! = mkVal rp1 E₀[j]! D[j]!)
            (fun _ => liftACost ((n - i) • iter markC + cu Currency.«while»)) := by
    intro E i hlen hf hin hj
    have hb : markBf n (E, i) = false := by simp only [markBf, decide_eq_false_iff_not]; omega
    simp only [markLoop, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨hlen, by omega, fun j hjn => hj j (by omega)⟩ ?_
    rw [show n - i = 0 by omega]
    simp
  intro fuel
  induction fuel with
  | zero => intro E i hlen hf hin hj hab; exact exit E i hlen (by omega) hin hj
  | succ fuel ih =>
    intro E i hlen hf hin hj hab
    by_cases hb : i < n
    · have hbt : markBf n (E, i) = true := by simp [markBf, hb]
      have hIs : markBf n ((E, i) : List ℕ × ℕ) = true → markP n D (E, i) :=
        fun _ => ⟨hlen, hn⟩
      have hEi : E[i]! = E₀[i]! := hab i le_rfl hb
      have hih := ih (E.set i (mkVal rp1 E[i]! D[i]!)) (i + 1) (by simp [hlen]) (by omega)
        (by omega)
        (fun j hjl => by
          rw [get!_set E i _ j (by omega)]
          by_cases hji : j = i
          · rw [if_pos hji, hji, hEi]
          · rw [if_neg hji]; exact hj j (by omega))
        (fun j hj₁ hj₂ => by
          rw [get!_set E i _ j (by omega), if_neg (by omega)]
          exact hab j (by omega) hj₂)
      have hcost : irUnit Currency.«while»
          + (liftACost markC + liftACost ((n - (i + 1)) • iter markC + cu Currency.«while»))
          = liftACost ((n - i) • iter markC + cu Currency.«while») := by
        rw [show n - i = (n - (i + 1)) + 1 by omega, succ_nsmul]
        simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
        ac_rfl
      calc markLoop n rp1 D (E, i)
          = NRest.consume (NRest.bindT (markF rp1 D (E, i)) fun s' => markLoop n rp1 D s')
              (irUnit Currency.«while») := by
            simp only [markLoop]; rw [irWhileIT_of_true hIs hbt]
        _ ≤ NRest.consume (NRest.bindT
              (NRest.consume (NRest.returnT (E.set i (mkVal rp1 E[i]! D[i]!), i + 1))
                (liftACost markC))
              fun s' => markLoop n rp1 D s') (irUnit Currency.«while») :=
            NRest.consume_mono
              (NRest.bindT_mono
                (markF_le rp1 D (E, i) (by simpa [hlen] using hb) (by omega)) fun _ => le_rfl)
              le_rfl
        _ = NRest.consume (NRest.consume
              (markLoop n rp1 D (E.set i (mkVal rp1 E[i]! D[i]!), i + 1)) (liftACost markC))
              (irUnit Currency.«while») := by rw [bindT_unitT]
        _ ≤ _ := by
            rw [← hcost]
            exact NRest.consume_mono (NRest.consume_mono hih le_rfl) le_rfl |>.trans
              (le_of_eq (by rw [Sepref.consume_spec, Sepref.consume_spec]))
    · exact exit E i hlen (by omega) hin hj

/-! ## 4. The synthesis -/

set_option maxHeartbeats 1000000 in
sepref_synth clearSynth (n : ℕ) (exc₀ : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (exc₀, 0) ("exc", "sw") ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "mkz")
    _ _ ("exc", "sw") (arrayAssn ×ₐ natAssn)
    (clearLoop n (exc₀, 0))

-- The synthesized clearing pass, pinned.
#guard clearSynth_impl =
  Com.while (Cond.lt (Operand.cell "sw") (Operand.cell "n"))
    ((Com.aset "exc" "sw" "mkz").seq
      ((Com.binop Lax13Proofs.Imp.Bop.add "sw" "sw" "one").seq Com.skip))

set_option maxHeartbeats 1000000 in
sepref_synth markSynth (n rp1 : ℕ) (dist exc₀ : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (exc₀, 0) ("exc", "sw") ∗
      hnCtxt arrayAssn dist "dist" ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn rp1 "mkr" ∗
      junkCell "mke" ∗ junkCell "mkd" ∗ junkCell "mka" ∗ junkCell "mkb" ∗
      junkCell "mkc" ∗ junkCell "mkp" ∗ junkCell "mkm")
    _ _ ("exc", "sw") (arrayAssn ×ₐ natAssn)
    (markLoop n rp1 dist (exc₀, 0))

-- The synthesized marking sweep, pinned. Every scratch cell landed in
-- the slot the program consumes it at (R2A/D-c), with no reordering.
#guard markSynth_impl =
  Com.while (Cond.lt (Operand.cell "sw") (Operand.cell "n"))
    ((Com.aget "mke" "exc" "sw").seq
      ((Com.aget "mkd" "dist" "sw").seq
        ((Com.binop Lax13Proofs.Imp.Bop.sub "mka" "one" "mke").seq
          ((Com.binop Lax13Proofs.Imp.Bop.sub "mkb" "mkr" "mkd").seq
            ((Com.binop Lax13Proofs.Imp.Bop.sub "mkc" "one" "mkb").seq
              ((Com.binop Lax13Proofs.Imp.Bop.mul "mkp" "mka" "mkc").seq
                ((Com.binop Lax13Proofs.Imp.Bop.sub "mkm" "one" "mkp").seq
                  ((Com.aset "exc" "sw" "mkm").seq
                    ((Com.binop Lax13Proofs.Imp.Bop.add "sw" "sw" "one").seq
                      Com.skip)))))))))

/-! ## 5. The bounds pass, via `BRefine` (P0.2's verdict)

No `Ir.State` invariant is authored anywhere below: the loop assertion
*is* the invariant, and every side condition is an arithmetic goal about
the abstract values. This is `Sepref/Examples/WordAssnSpike.lean` §4's
judgment carried to an ND-MC engine, and the telemetry is §8. -/

section Bounds

/-! ### The clearing pass -/

/-- The clearing pass's loop assertion: the two components it mutates and
the three constants it reads. -/
def clearΓ (n : ℕ) : List ℕ × ℕ → Assn := fun t =>
  arrayAssn t.1 "exc" ∗ natAssn t.2 "sw" ∗ natAssn n "n" ∗ natAssn 1 "one" ∗
    natAssn 0 "mkz"

/-- The abstract invariant. One conjunct. -/
def clearI (n : ℕ) : List ℕ × ℕ → Prop := fun t => t.2 ≤ n

theorem clear_guard (n : ℕ) (t : List ℕ × ℕ) (F : Assn) (s : Ir.State) (cr : ECost)
    (r : Bool) (_ : clearI n t) (hs : irSTATE (clearΓ n t ∗ F) (s, cr))
    (hev : (Cond.lt (Operand.cell "sw") (Operand.cell "n")).eval s = some r) :
    decide (t.2 < n) = r := by
  obtain ⟨a, b, ha, hb, rfl⟩ := BfsQSynth.eval_lt_cells hev
  have hi : s.vars "sw" = some t.2 :=
    natAssn_vars (F := arrayAssn t.1 "exc" ∗ natAssn n "n" ∗ natAssn 1 "one" ∗
      natAssn 0 "mkz" ∗ F) (irSTATE_cong (by rw [clearΓ]; ac_rfl) hs)
  have hn : s.vars "n" = some n :=
    natAssn_vars (F := arrayAssn t.1 "exc" ∗ natAssn t.2 "sw" ∗ natAssn 1 "one" ∗
      natAssn 0 "mkz" ∗ F) (irSTATE_cong (by rw [clearΓ]; ac_rfl) hs)
  rw [hi] at ha
  rw [hn] at hb
  rw [Option.some.inj ha, Option.some.inj hb]

/-- The clearing pass's loop body, named. -/
def clearBody : Com :=
  (Com.aset "exc" "sw" "mkz").seq
    ((Com.binop Lax13Proofs.Imp.Bop.add "sw" "sw" "one").seq Com.skip)

theorem clearSynth_impl_eq :
    clearSynth_impl = Com.while (Cond.lt (Operand.cell "sw") (Operand.cell "n")) clearBody :=
  rfl

theorem clear_body_brefine {B n : ℕ} (hnB : n < B) (t : List ℕ × ℕ) (_hI : clearI n t)
    (hbf : decide (t.2 < n) = true) :
    BRefine B (clearΓ n t)
      clearBody (LoopAssn (clearI n) (clearΓ n)) := by
  have hlt : t.2 < n := of_decide_eq_true hbf
  rw [clearBody]
  refine BRefine.seq (Γ₁ := ⌜t.2 < t.1.length⌝ ∗ clearΓ n (t.1.set t.2 0, t.2)) ?_ ?_
  · exact BRefine.perm
      (P := (arrayAssn t.1 "exc" ∗ natAssn t.2 "sw" ∗ natAssn 0 "mkz") ∗
        (natAssn n "n" ∗ natAssn 1 "one"))
      (P' := (⌜t.2 < t.1.length⌝ ∗ arrayAssn (t.1.set t.2 0) "exc" ∗ natAssn t.2 "sw" ∗
        natAssn 0 "mkz") ∗ (natAssn n "n" ∗ natAssn 1 "one"))
      (by simp only [clearΓ]; ac_rfl) (by simp only [clearΓ]; ac_rfl)
      (BRefine.frame BRefine.aset)
  · refine BRefine.pre_pure fun _ => ?_
    refine BRefine.seq
      (Γ₁ := clearΓ n (t.1.set t.2 0, Lax13Proofs.Imp.Bop.apply .add t.2 1)) ?_ ?_
    · exact BRefine.perm
        (P := (natAssn t.2 "sw" ∗ natAssn 1 "one") ∗
          (arrayAssn (t.1.set t.2 0) "exc" ∗ natAssn n "n" ∗ natAssn 0 "mkz"))
        (P' := (natAssn (Lax13Proofs.Imp.Bop.apply .add t.2 1) "sw" ∗ natAssn 1 "one") ∗
          (arrayAssn (t.1.set t.2 0) "exc" ∗ natAssn n "n" ∗ natAssn 0 "mkz"))
        (by simp only [clearΓ]; ac_rfl) (by simp only [clearΓ]; ac_rfl)
        (BRefine.frame (BRefine.binop_self
          (by rw [Lax13Proofs.Imp.Bop.apply_add]; omega)))
    · exact BRefine.skip.cons (entails_refl _)
        (loopAssn_intro (I := clearI n) (Γ := clearΓ n)
          (t := (t.1.set t.2 0, Lax13Proofs.Imp.Bop.apply .add t.2 1))
          (by simp only [clearI, Lax13Proofs.Imp.Bop.apply_add]; omega))

/-- **The clearing pass's bounds pass.** -/
theorem clear_brefine {B n : ℕ} (hnB : n < B) :
    BRefine B (LoopAssn (clearI n) (clearΓ n)) clearSynth_impl
      (LoopAssn (clearI n) (clearΓ n)) := by
  rw [clearSynth_impl_eq]
  exact BRefine.while_guard (bf := fun t => decide (t.2 < n))
    BfsQSynth.litLt_lt_cells (clear_guard n)
    (fun t hI hbf => clear_body_brefine hnB t hI hbf)
    (fun t hI _ => loopAssn_intro hI)

/-! ### The marking sweep

Thirteen owned conjuncts, nine operations, seven scratch cells. The
scratch cells are existential in the loop assertion — they are junk at
entry and junk again at exit — and `BRefine.pre_ex` opens them once. -/

/-- The sweep's assertion at *named* scratch values. -/
def mkΓ (n rp1 : ℕ) (D E : List ℕ) (i e d a b c p m : ℕ) : Assn :=
  arrayAssn E "exc" ∗ natAssn i "sw" ∗ arrayAssn D "dist" ∗ natAssn n "n" ∗
    natAssn 1 "one" ∗ natAssn rp1 "mkr" ∗ natAssn e "mke" ∗ natAssn d "mkd" ∗
    natAssn a "mka" ∗ natAssn b "mkb" ∗ natAssn c "mkc" ∗ natAssn p "mkp" ∗
    natAssn m "mkm"

/-- …and the loop assertion, with the scratch cells quantified. -/
def markΓ (n rp1 : ℕ) (D : List ℕ) : List ℕ × ℕ → Assn := fun t =>
  sepEx fun y : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
    mkΓ n rp1 D t.1 t.2 y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2.1
      y.2.2.2.2.2.2

theorem mkΓ_sw {n rp1 : ℕ} {D E : List ℕ} {i e d a b c p m : ℕ} {F : Assn}
    {s : Ir.State} {cr : ECost} (h : irSTATE (mkΓ n rp1 D E i e d a b c p m ∗ F) (s, cr)) :
    s.vars "sw" = some i :=
  natAssn_vars (F := (arrayAssn E "exc" ∗ arrayAssn D "dist" ∗ natAssn n "n" ∗
    natAssn 1 "one" ∗ natAssn rp1 "mkr" ∗ natAssn e "mke" ∗ natAssn d "mkd" ∗
    natAssn a "mka" ∗ natAssn b "mkb" ∗ natAssn c "mkc" ∗ natAssn p "mkp" ∗
    natAssn m "mkm") ∗ F) (irSTATE_cong (by simp only [mkΓ]; ac_rfl) h)

theorem mkΓ_n {n rp1 : ℕ} {D E : List ℕ} {i e d a b c p m : ℕ} {F : Assn}
    {s : Ir.State} {cr : ECost} (h : irSTATE (mkΓ n rp1 D E i e d a b c p m ∗ F) (s, cr)) :
    s.vars "n" = some n :=
  natAssn_vars (F := (arrayAssn E "exc" ∗ natAssn i "sw" ∗ arrayAssn D "dist" ∗
    natAssn 1 "one" ∗ natAssn rp1 "mkr" ∗ natAssn e "mke" ∗ natAssn d "mkd" ∗
    natAssn a "mka" ∗ natAssn b "mkb" ∗ natAssn c "mkc" ∗ natAssn p "mkp" ∗
    natAssn m "mkm") ∗ F) (irSTATE_cong (by simp only [mkΓ]; ac_rfl) h)

theorem mkΓ_entails_markΓ (n rp1 : ℕ) (D E : List ℕ) (i e d a b c p m : ℕ) :
    mkΓ n rp1 D E i e d a b c p m ⊢ markΓ n rp1 D (E, i) :=
  fun _ h => ⟨(e, d, a, b, c, p, m), h⟩

/-- The abstract invariant. One conjunct, as for the clearing pass. -/
def markI (n : ℕ) : List ℕ × ℕ → Prop := fun t => t.2 ≤ n

theorem mark_guard (n rp1 : ℕ) (D : List ℕ) (t : List ℕ × ℕ) (F : Assn) (s : Ir.State)
    (cr : ECost) (r : Bool) (_ : markI n t) (hs : irSTATE (markΓ n rp1 D t ∗ F) (s, cr))
    (hev : (Cond.lt (Operand.cell "sw") (Operand.cell "n")).eval s = some r) :
    decide (t.2 < n) = r := by
  obtain ⟨a, b, ha, hb, rfl⟩ := BfsQSynth.eval_lt_cells hev
  simp only [markΓ] at hs
  rw [sepEx_sepConj] at hs
  obtain ⟨y, hy⟩ := hs
  have hi : s.vars "sw" = some t.2 := mkΓ_sw hy
  have hn : s.vars "n" = some n := mkΓ_n hy
  rw [hi] at ha
  rw [hn] at hb
  rw [Option.some.inj ha, Option.some.inj hb]

/-! #### The nine operations

One lemma each. The permutation each needs is the one
`Sepref/Translate.lean`'s driver computes for the synthesis half and
which `BRefine` has no database for yet (§8, tool gap 1). -/

section Steps

variable {B n rp1 : ℕ} {D E : List ℕ} {i e d a b c p m : ℕ}

theorem step_aget_e :
    BRefine B (mkΓ n rp1 D E i e d a b c p m) (Com.aget "mke" "exc" "sw")
      (⌜i < E.length⌝ ∗ mkΓ n rp1 D E i E[i]! d a b c p m) :=
  BRefine.perm
    (P := (natAssn e "mke" ∗ arrayAssn E "exc" ∗ natAssn i "sw") ∗
      (natAssn d "mkd" ∗ natAssn a "mka" ∗ natAssn b "mkb" ∗ natAssn c "mkc" ∗
        natAssn p "mkp" ∗ natAssn m "mkm" ∗ arrayAssn D "dist" ∗ natAssn n "n" ∗
        natAssn 1 "one" ∗ natAssn rp1 "mkr"))
    (P' := (⌜i < E.length⌝ ∗ natAssn E[i]! "mke" ∗ arrayAssn E "exc" ∗ natAssn i "sw") ∗
      (natAssn d "mkd" ∗ natAssn a "mka" ∗ natAssn b "mkb" ∗ natAssn c "mkc" ∗
        natAssn p "mkp" ∗ natAssn m "mkm" ∗ arrayAssn D "dist" ∗ natAssn n "n" ∗
        natAssn 1 "one" ∗ natAssn rp1 "mkr"))
    (by simp only [mkΓ]; ac_rfl) (by simp only [mkΓ]; ac_rfl)
    (BRefine.frame BRefine.aget)

theorem step_aget_d :
    BRefine B (mkΓ n rp1 D E i e d a b c p m) (Com.aget "mkd" "dist" "sw")
      (⌜i < D.length⌝ ∗ mkΓ n rp1 D E i e D[i]! a b c p m) :=
  BRefine.perm
    (P := (natAssn d "mkd" ∗ arrayAssn D "dist" ∗ natAssn i "sw") ∗
      (natAssn e "mke" ∗ natAssn a "mka" ∗ natAssn b "mkb" ∗ natAssn c "mkc" ∗
        natAssn p "mkp" ∗ natAssn m "mkm" ∗ arrayAssn E "exc" ∗ natAssn n "n" ∗
        natAssn 1 "one" ∗ natAssn rp1 "mkr"))
    (P' := (⌜i < D.length⌝ ∗ natAssn D[i]! "mkd" ∗ arrayAssn D "dist" ∗ natAssn i "sw") ∗
      (natAssn e "mke" ∗ natAssn a "mka" ∗ natAssn b "mkb" ∗ natAssn c "mkc" ∗
        natAssn p "mkp" ∗ natAssn m "mkm" ∗ arrayAssn E "exc" ∗ natAssn n "n" ∗
        natAssn 1 "one" ∗ natAssn rp1 "mkr"))
    (by simp only [mkΓ]; ac_rfl) (by simp only [mkΓ]; ac_rfl)
    (BRefine.frame BRefine.aget)

theorem step_sub_a (hb : Lax13Proofs.Imp.Bop.apply .sub 1 e < B) :
    BRefine B (mkΓ n rp1 D E i e d a b c p m)
      (Com.binop Lax13Proofs.Imp.Bop.sub "mka" "one" "mke")
      (mkΓ n rp1 D E i e d (Lax13Proofs.Imp.Bop.apply .sub 1 e) b c p m) :=
  BRefine.perm
    (P := (natAssn a "mka" ∗ natAssn 1 "one" ∗ natAssn e "mke") ∗
      (natAssn d "mkd" ∗ natAssn b "mkb" ∗ natAssn c "mkc" ∗ natAssn p "mkp" ∗
        natAssn m "mkm" ∗ arrayAssn E "exc" ∗ arrayAssn D "dist" ∗ natAssn i "sw" ∗
        natAssn n "n" ∗ natAssn rp1 "mkr"))
    (P' := (natAssn (Lax13Proofs.Imp.Bop.apply .sub 1 e) "mka" ∗ natAssn 1 "one" ∗
        natAssn e "mke") ∗
      (natAssn d "mkd" ∗ natAssn b "mkb" ∗ natAssn c "mkc" ∗ natAssn p "mkp" ∗
        natAssn m "mkm" ∗ arrayAssn E "exc" ∗ arrayAssn D "dist" ∗ natAssn i "sw" ∗
        natAssn n "n" ∗ natAssn rp1 "mkr"))
    (by simp only [mkΓ]; ac_rfl) (by simp only [mkΓ]; ac_rfl)
    (BRefine.frame (BRefine.binop hb))

theorem step_sub_b (hbd : Lax13Proofs.Imp.Bop.apply .sub rp1 d < B) :
    BRefine B (mkΓ n rp1 D E i e d a b c p m)
      (Com.binop Lax13Proofs.Imp.Bop.sub "mkb" "mkr" "mkd")
      (mkΓ n rp1 D E i e d a (Lax13Proofs.Imp.Bop.apply .sub rp1 d) c p m) :=
  BRefine.perm
    (P := (natAssn b "mkb" ∗ natAssn rp1 "mkr" ∗ natAssn d "mkd") ∗
      (natAssn e "mke" ∗ natAssn a "mka" ∗ natAssn c "mkc" ∗ natAssn p "mkp" ∗
        natAssn m "mkm" ∗ arrayAssn E "exc" ∗ arrayAssn D "dist" ∗ natAssn i "sw" ∗
        natAssn n "n" ∗ natAssn 1 "one"))
    (P' := (natAssn (Lax13Proofs.Imp.Bop.apply .sub rp1 d) "mkb" ∗ natAssn rp1 "mkr" ∗
        natAssn d "mkd") ∗
      (natAssn e "mke" ∗ natAssn a "mka" ∗ natAssn c "mkc" ∗ natAssn p "mkp" ∗
        natAssn m "mkm" ∗ arrayAssn E "exc" ∗ arrayAssn D "dist" ∗ natAssn i "sw" ∗
        natAssn n "n" ∗ natAssn 1 "one"))
    (by simp only [mkΓ]; ac_rfl) (by simp only [mkΓ]; ac_rfl)
    (BRefine.frame (BRefine.binop hbd))

theorem step_sub_c (hbc : Lax13Proofs.Imp.Bop.apply .sub 1 b < B) :
    BRefine B (mkΓ n rp1 D E i e d a b c p m)
      (Com.binop Lax13Proofs.Imp.Bop.sub "mkc" "one" "mkb")
      (mkΓ n rp1 D E i e d a b (Lax13Proofs.Imp.Bop.apply .sub 1 b) p m) :=
  BRefine.perm
    (P := (natAssn c "mkc" ∗ natAssn 1 "one" ∗ natAssn b "mkb") ∗
      (natAssn e "mke" ∗ natAssn d "mkd" ∗ natAssn a "mka" ∗ natAssn p "mkp" ∗
        natAssn m "mkm" ∗ arrayAssn E "exc" ∗ arrayAssn D "dist" ∗ natAssn i "sw" ∗
        natAssn n "n" ∗ natAssn rp1 "mkr"))
    (P' := (natAssn (Lax13Proofs.Imp.Bop.apply .sub 1 b) "mkc" ∗ natAssn 1 "one" ∗
        natAssn b "mkb") ∗
      (natAssn e "mke" ∗ natAssn d "mkd" ∗ natAssn a "mka" ∗ natAssn p "mkp" ∗
        natAssn m "mkm" ∗ arrayAssn E "exc" ∗ arrayAssn D "dist" ∗ natAssn i "sw" ∗
        natAssn n "n" ∗ natAssn rp1 "mkr"))
    (by simp only [mkΓ]; ac_rfl) (by simp only [mkΓ]; ac_rfl)
    (BRefine.frame (BRefine.binop hbc))

theorem step_mul_p (hbp : Lax13Proofs.Imp.Bop.apply .mul a c < B) :
    BRefine B (mkΓ n rp1 D E i e d a b c p m)
      (Com.binop Lax13Proofs.Imp.Bop.mul "mkp" "mka" "mkc")
      (mkΓ n rp1 D E i e d a b c (Lax13Proofs.Imp.Bop.apply .mul a c) m) :=
  BRefine.perm
    (P := (natAssn p "mkp" ∗ natAssn a "mka" ∗ natAssn c "mkc") ∗
      (natAssn e "mke" ∗ natAssn d "mkd" ∗ natAssn b "mkb" ∗ natAssn m "mkm" ∗
        arrayAssn E "exc" ∗ arrayAssn D "dist" ∗ natAssn i "sw" ∗ natAssn n "n" ∗
        natAssn 1 "one" ∗ natAssn rp1 "mkr"))
    (P' := (natAssn (Lax13Proofs.Imp.Bop.apply .mul a c) "mkp" ∗ natAssn a "mka" ∗
        natAssn c "mkc") ∗
      (natAssn e "mke" ∗ natAssn d "mkd" ∗ natAssn b "mkb" ∗ natAssn m "mkm" ∗
        arrayAssn E "exc" ∗ arrayAssn D "dist" ∗ natAssn i "sw" ∗ natAssn n "n" ∗
        natAssn 1 "one" ∗ natAssn rp1 "mkr"))
    (by simp only [mkΓ]; ac_rfl) (by simp only [mkΓ]; ac_rfl)
    (BRefine.frame (BRefine.binop hbp))

theorem step_sub_m (hbm : Lax13Proofs.Imp.Bop.apply .sub 1 p < B) :
    BRefine B (mkΓ n rp1 D E i e d a b c p m)
      (Com.binop Lax13Proofs.Imp.Bop.sub "mkm" "one" "mkp")
      (mkΓ n rp1 D E i e d a b c p (Lax13Proofs.Imp.Bop.apply .sub 1 p)) :=
  BRefine.perm
    (P := (natAssn m "mkm" ∗ natAssn 1 "one" ∗ natAssn p "mkp") ∗
      (natAssn e "mke" ∗ natAssn d "mkd" ∗ natAssn a "mka" ∗ natAssn b "mkb" ∗
        natAssn c "mkc" ∗ arrayAssn E "exc" ∗ arrayAssn D "dist" ∗ natAssn i "sw" ∗
        natAssn n "n" ∗ natAssn rp1 "mkr"))
    (P' := (natAssn (Lax13Proofs.Imp.Bop.apply .sub 1 p) "mkm" ∗ natAssn 1 "one" ∗
        natAssn p "mkp") ∗
      (natAssn e "mke" ∗ natAssn d "mkd" ∗ natAssn a "mka" ∗ natAssn b "mkb" ∗
        natAssn c "mkc" ∗ arrayAssn E "exc" ∗ arrayAssn D "dist" ∗ natAssn i "sw" ∗
        natAssn n "n" ∗ natAssn rp1 "mkr"))
    (by simp only [mkΓ]; ac_rfl) (by simp only [mkΓ]; ac_rfl)
    (BRefine.frame (BRefine.binop hbm))

theorem step_aset :
    BRefine B (mkΓ n rp1 D E i e d a b c p m) (Com.aset "exc" "sw" "mkm")
      (⌜i < E.length⌝ ∗ mkΓ n rp1 D (E.set i m) i e d a b c p m) :=
  BRefine.perm
    (P := (arrayAssn E "exc" ∗ natAssn i "sw" ∗ natAssn m "mkm") ∗
      (natAssn e "mke" ∗ natAssn d "mkd" ∗ natAssn a "mka" ∗ natAssn b "mkb" ∗
        natAssn c "mkc" ∗ natAssn p "mkp" ∗ arrayAssn D "dist" ∗ natAssn n "n" ∗
        natAssn 1 "one" ∗ natAssn rp1 "mkr"))
    (P' := (⌜i < E.length⌝ ∗ arrayAssn (E.set i m) "exc" ∗ natAssn i "sw" ∗
        natAssn m "mkm") ∗
      (natAssn e "mke" ∗ natAssn d "mkd" ∗ natAssn a "mka" ∗ natAssn b "mkb" ∗
        natAssn c "mkc" ∗ natAssn p "mkp" ∗ arrayAssn D "dist" ∗ natAssn n "n" ∗
        natAssn 1 "one" ∗ natAssn rp1 "mkr"))
    (by simp only [mkΓ]; ac_rfl) (by simp only [mkΓ]; ac_rfl)
    (BRefine.frame BRefine.aset)

theorem step_bump (hbi : Lax13Proofs.Imp.Bop.apply .add i 1 < B) :
    BRefine B (mkΓ n rp1 D E i e d a b c p m)
      (Com.binop Lax13Proofs.Imp.Bop.add "sw" "sw" "one")
      (mkΓ n rp1 D E (Lax13Proofs.Imp.Bop.apply .add i 1) e d a b c p m) :=
  BRefine.perm
    (P := (natAssn i "sw" ∗ natAssn 1 "one") ∗
      (natAssn e "mke" ∗ natAssn d "mkd" ∗ natAssn a "mka" ∗ natAssn b "mkb" ∗
        natAssn c "mkc" ∗ natAssn p "mkp" ∗ natAssn m "mkm" ∗ arrayAssn E "exc" ∗
        arrayAssn D "dist" ∗ natAssn n "n" ∗ natAssn rp1 "mkr"))
    (P' := (natAssn (Lax13Proofs.Imp.Bop.apply .add i 1) "sw" ∗ natAssn 1 "one") ∗
      (natAssn e "mke" ∗ natAssn d "mkd" ∗ natAssn a "mka" ∗ natAssn b "mkb" ∗
        natAssn c "mkc" ∗ natAssn p "mkp" ∗ natAssn m "mkm" ∗ arrayAssn E "exc" ∗
        arrayAssn D "dist" ∗ natAssn n "n" ∗ natAssn rp1 "mkr"))
    (by simp only [mkΓ]; ac_rfl) (by simp only [mkΓ]; ac_rfl)
    (BRefine.frame (BRefine.binop_self hbi))

end Steps

/-- The sweep's loop body, named. -/
def markBody : Com :=
  (Com.aget "mke" "exc" "sw").seq
    ((Com.aget "mkd" "dist" "sw").seq
      ((Com.binop Lax13Proofs.Imp.Bop.sub "mka" "one" "mke").seq
        ((Com.binop Lax13Proofs.Imp.Bop.sub "mkb" "mkr" "mkd").seq
          ((Com.binop Lax13Proofs.Imp.Bop.sub "mkc" "one" "mkb").seq
            ((Com.binop Lax13Proofs.Imp.Bop.mul "mkp" "mka" "mkc").seq
              ((Com.binop Lax13Proofs.Imp.Bop.sub "mkm" "one" "mkp").seq
                ((Com.aset "exc" "sw" "mkm").seq
                  ((Com.binop Lax13Proofs.Imp.Bop.add "sw" "sw" "one").seq
                    Com.skip))))))))

theorem markSynth_impl_eq :
    markSynth_impl = Com.while (Cond.lt (Operand.cell "sw") (Operand.cell "n")) markBody := rfl

/-- The product of two monus-by-one values is at most one: the only side
condition of the sweep that is not an `omega`. -/
theorem mul_sub_lt {B x y : ℕ} (h1B : 1 < B) :
    Lax13Proofs.Imp.Bop.apply .mul (Lax13Proofs.Imp.Bop.apply .sub 1 x)
      (Lax13Proofs.Imp.Bop.apply .sub 1 y) < B := by
  rw [Lax13Proofs.Imp.Bop.apply_mul, Lax13Proofs.Imp.Bop.apply_sub,
    Lax13Proofs.Imp.Bop.apply_sub]
  calc (1 - x) * (1 - y) ≤ 1 * 1 := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    _ < B := by omega

/-- **The sweep's loop body.** Six arithmetic side conditions and one
index-restoration goal, every one of them about the *abstract* values:
five monus bounds, one product bound and the counter's bump. -/
theorem mark_body_brefine {B n rp1 : ℕ} {D : List ℕ} (hnB : n < B) (h1B : 1 < B)
    (hrB : rp1 < B) (t : List ℕ × ℕ) (_hI : markI n t) (hbf : decide (t.2 < n) = true) :
    BRefine B (markΓ n rp1 D t) markBody (LoopAssn (markI n) (markΓ n rp1 D)) := by
  have hlt : t.2 < n := of_decide_eq_true hbf
  simp only [markΓ]
  refine BRefine.pre_ex fun y => ?_
  rw [markBody]
  refine BRefine.seq step_aget_e (BRefine.pre_pure fun _ => ?_)
  refine BRefine.seq step_aget_d (BRefine.pre_pure fun _ => ?_)
  refine BRefine.seq (step_sub_a (by rw [Lax13Proofs.Imp.Bop.apply_sub]; omega)) ?_
  refine BRefine.seq (step_sub_b (by rw [Lax13Proofs.Imp.Bop.apply_sub]; omega)) ?_
  refine BRefine.seq (step_sub_c (by rw [Lax13Proofs.Imp.Bop.apply_sub]; omega)) ?_
  refine BRefine.seq (step_mul_p (mul_sub_lt h1B)) ?_
  refine BRefine.seq (step_sub_m (by rw [Lax13Proofs.Imp.Bop.apply_sub]; omega)) ?_
  refine BRefine.seq step_aset (BRefine.pre_pure fun _ => ?_)
  refine BRefine.seq (step_bump (by rw [Lax13Proofs.Imp.Bop.apply_add]; omega)) ?_
  refine BRefine.skip.cons (entails_refl _)
    (entails_trans (mkΓ_entails_markΓ _ _ _ _ _ _ _ _ _ _ _ _) ?_)
  refine loopAssn_intro (I := markI n) (Γ := markΓ n rp1 D) ?_
  simp only [markI, Lax13Proofs.Imp.Bop.apply_add]
  omega

/-- **The marking sweep's bounds pass.** -/
theorem mark_brefine {B n rp1 : ℕ} {D : List ℕ} (hnB : n < B) (h1B : 1 < B) (hrB : rp1 < B) :
    BRefine B (LoopAssn (markI n) (markΓ n rp1 D)) markSynth_impl
      (LoopAssn (markI n) (markΓ n rp1 D)) := by
  rw [markSynth_impl_eq]
  exact BRefine.while_guard (bf := fun t => decide (t.2 < n))
    BfsQSynth.litLt_lt_cells (mark_guard n rp1 D)
    (fun t hI hbf => mark_body_brefine hnB h1B hrB t hI hbf)
    (fun t hI _ => loopAssn_intro hI)

end Bounds

/-! ## 6. The cashing chain and the exports

`spec_of_hnRefine`, then `readout_arr`/`readout_scalar` at the result
tuple's two components. The cost constants are **computed** from the
per-iteration accounts by `decide +kernel`, not tuned. -/

section Export

open Lax13Proofs.Reasoning (arrOf length_arrOf arrOf_congr)

/-! ### The two initial stores -/

/-- The clearing pass's store: the array, the counter, and the three
constants it reads. -/
def clearState (n : ℕ) (E₀ : List ℕ) : Ir.State :=
  Ir.State.ofPairs [("sw", 0), ("n", n), ("one", 1), ("mkz", 0)] [("exc", E₀)]

/-- …and the sweep's: two arrays, the counter, three constants and the
seven scratch cells, zeroed (statement delta P7/D-bp). -/
def markState (n rp1 : ℕ) (D E₀ : List ℕ) : Ir.State :=
  Ir.State.ofPairs
    [("sw", 0), ("n", n), ("one", 1), ("mkr", rp1), ("mke", 0), ("mkd", 0), ("mka", 0),
      ("mkb", 0), ("mkc", 0), ("mkp", 0), ("mkm", 0)]
    [("exc", E₀), ("dist", D)]

/-! ### The synthesis preconditions and frames, named -/

def clearPre (n : ℕ) (E₀ : List ℕ) : Assn :=
  hnCtxt (arrayAssn ×ₐ natAssn) (E₀, 0) ("exc", "sw") ∗ hnCtxt natAssn n "n" ∗
    hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "mkz"

def clearFrame (n : ℕ) : Assn :=
  hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "mkz"

def markPre (n rp1 : ℕ) (D E₀ : List ℕ) : Assn :=
  hnCtxt (arrayAssn ×ₐ natAssn) (E₀, 0) ("exc", "sw") ∗ hnCtxt arrayAssn D "dist" ∗
    hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn rp1 "mkr" ∗
    junkCell "mke" ∗ junkCell "mkd" ∗ junkCell "mka" ∗ junkCell "mkb" ∗
    junkCell "mkc" ∗ junkCell "mkp" ∗ junkCell "mkm"

def markFrame (n rp1 : ℕ) (D : List ℕ) : Assn :=
  hnCtxt arrayAssn D "dist" ∗ hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗
    hnCtxt natAssn rp1 "mkr" ∗ junkCell "mke" ∗ junkCell "mkd" ∗ junkCell "mka" ∗
    junkCell "mkb" ∗ junkCell "mkc" ∗ junkCell "mkp" ∗ junkCell "mkm"

theorem clearSynth' (n : ℕ) (E₀ : List ℕ) :
    hnRefine (clearPre n E₀) clearSynth_impl (clearFrame n) ("exc", "sw")
      (arrayAssn ×ₐ natAssn) (clearLoop n (E₀, 0)) := clearSynth n E₀

theorem markSynth' (n rp1 : ℕ) (D E₀ : List ℕ) :
    hnRefine (markPre n rp1 D E₀) markSynth_impl (markFrame n rp1 D) ("exc", "sw")
      (arrayAssn ×ₐ natAssn) (markLoop n rp1 D (E₀, 0)) := markSynth n rp1 D E₀

/-! ### Ownership -/

def clearHole (n : ℕ) (E₀ : List ℕ) : Assn :=
  EXACT ((vcells (clearState n E₀) |>.erase "sw" |>.erase "n" |>.erase "one"
      |>.erase "mkz",
    acells (clearState n E₀) |>.erase "exc", hcells (clearState n E₀)), 0)

theorem clear_state_holds (n : ℕ) (E₀ : List ℕ) :
    irSTATE (clearPre n E₀ ∗ clearHole n E₀) (clearState n E₀, 0) := by
  show (clearPre n E₀ ∗ clearHole n E₀)
    ((vcells (clearState n E₀), acells (clearState n E₀), hcells (clearState n E₀)), 0)
  simp only [clearPre, hnCtxt, prodAssn, natAssn_def, arrayAssn_def, sepConj_assoc]
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  exact Ir.ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩

def markHole (n rp1 : ℕ) (D E₀ : List ℕ) : Assn :=
  EXACT ((vcells (markState n rp1 D E₀) |>.erase "sw" |>.erase "n" |>.erase "one"
      |>.erase "mkr" |>.erase "mke" |>.erase "mkd" |>.erase "mka" |>.erase "mkb"
      |>.erase "mkc" |>.erase "mkp" |>.erase "mkm",
    acells (markState n rp1 D E₀) |>.erase "exc" |>.erase "dist",
    hcells (markState n rp1 D E₀)), 0)

theorem mark_state_holds (n rp1 : ℕ) (D E₀ : List ℕ) :
    irSTATE (markPre n rp1 D E₀ ∗ markHole n rp1 D E₀) (markState n rp1 D E₀, 0) := by
  show (markPre n rp1 D E₀ ∗ markHole n rp1 D E₀)
    ((vcells (markState n rp1 D E₀), acells (markState n rp1 D E₀),
      hcells (markState n rp1 D E₀)), 0)
  simp only [markPre, hnCtxt, prodAssn, natAssn_def, arrayAssn_def, sepConj_assoc]
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  iterate 7
    rw [junkCell_def, sepEx_sepConj]
    refine ⟨0, Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩⟩
  rfl

/-! ### The same two stores, at the `BRefine` assertions -/

theorem clearΓ_holds (n : ℕ) (E₀ : List ℕ) :
    irSTATE (clearΓ n (E₀, 0) ∗ clearHole n E₀) (clearState n E₀, 0) := by
  show (clearΓ n (E₀, 0) ∗ clearHole n E₀)
    ((vcells (clearState n E₀), acells (clearState n E₀), hcells (clearState n E₀)), 0)
  simp only [clearΓ, natAssn_def, arrayAssn_def, sepConj_assoc]
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  exact Ir.ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩

theorem mkΓ_holds (n rp1 : ℕ) (D E₀ : List ℕ) :
    irSTATE (mkΓ n rp1 D E₀ 0 0 0 0 0 0 0 0 ∗ markHole n rp1 D E₀)
      (markState n rp1 D E₀, 0) := by
  show (mkΓ n rp1 D E₀ 0 0 0 0 0 0 0 0 ∗ markHole n rp1 D E₀)
    ((vcells (markState n rp1 D E₀), acells (markState n rp1 D E₀),
      hcells (markState n rp1 D E₀)), 0)
  simp only [mkΓ, natAssn_def, arrayAssn_def, sepConj_assoc]
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  exact Ir.ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩

/-! ### The stores are bounded -/

theorem clearState_bound {B n : ℕ} {E₀ : List ℕ} (hnB : n < B) (h1B : 1 < B)
    (hE : ∀ v ∈ E₀, v < B) : Ir.StateBound B (clearState n E₀) := by
  refine Codegen.stateBound_ofPairs ?_ ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simpa using by omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact hE

theorem markState_bound {B n rp1 : ℕ} {D E₀ : List ℕ} (hnB : n < B) (h1B : 1 < B)
    (hrB : rp1 < B) (hE : ∀ v ∈ E₀, v < B) (hD : ∀ v ∈ D, v < B) :
    Ir.StateBound B (markState n rp1 D E₀) := by
  refine Codegen.stateBound_ofPairs ?_ ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa using by omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hE
    · exact hD

/-! ### The bounds witnesses -/

theorem clear_bpre {B n : ℕ} {E₀ : List ℕ} (hnB : n < B) (h1B : 1 < B)
    (hE : ∀ v ∈ E₀, v < B) :
    Ir.bpre B clearSynth_impl (fun _ => True) (clearState n E₀) :=
  bpre_of_BRefine (F := clearHole n E₀) (clear_brefine hnB)
    (start_entailsE (clearΓ_holds n E₀)
      (sepConj_mono_left (loopAssn_intro (I := clearI n) (Γ := clearΓ n)
        (t := (E₀, 0)) (Nat.zero_le n))))
    (clearState_bound hnB h1B hE)

theorem mark_bpre {B n rp1 : ℕ} {D E₀ : List ℕ} (hnB : n < B) (h1B : 1 < B) (hrB : rp1 < B)
    (hE : ∀ v ∈ E₀, v < B) (hD : ∀ v ∈ D, v < B) :
    Ir.bpre B markSynth_impl (fun _ => True) (markState n rp1 D E₀) :=
  bpre_of_BRefine (F := markHole n rp1 D E₀) (mark_brefine hnB h1B hrB)
    (start_entailsE (mkΓ_holds n rp1 D E₀)
      (sepConj_mono_left (entails_trans (mkΓ_entails_markΓ _ _ _ _ _ _ _ _ _ _ _ _)
        (loopAssn_intro (I := markI n) (Γ := markΓ n rp1 D) (t := (E₀, 0))
          (Nat.zero_le n)))))
    (markState_bound hnB h1B hrB hE hD)

/-! ### The costs, computed -/

/-- **The clearing pass's cost**: `12·n + 4` IMP+ time units. -/
def clearK (n : ℕ) : ℕ := 12 * n + 4

/-- **The marking sweep's cost**: `38·n + 4` IMP+ time units. The
baseline's hand-tuned figure is `23·n + 6`; the difference is R2A/D-a —
one IMP+ expression walk against five IR three-address operations. -/
def markK (n : ℕ) : ℕ := 38 * n + 4

theorem ecash_clearTotal (n : ℕ) :
    ecash (liftACost (n • iter clearC + cu Currency.«while»)) = (clearK n : ℕ∞) := by
  rw [BfsQSynth.ecash_liftACost, Codegen.cash_add, BfsQSynth.cash_nsmul,
    show Codegen.cash (iter clearC) = 12 from by decide +kernel,
    show Codegen.cash (cu Currency.«while») = 4 from by decide +kernel, clearK]
  push_cast
  ring

theorem ecash_markTotal (n : ℕ) :
    ecash (liftACost (n • iter markC + cu Currency.«while»)) = (markK n : ℕ∞) := by
  rw [BfsQSynth.ecash_liftACost, Codegen.cash_add, BfsQSynth.cash_nsmul,
    show Codegen.cash (iter markC) = 38 from by decide +kernel,
    show Codegen.cash (cu Currency.«while») = 4 from by decide +kernel, markK]
  push_cast
  ring

/-! ### The cashing chain at one initial store -/

theorem clear_spec_at {B n : ℕ} (E₀ : List ℕ) (hnB : n < B) (h1B : 1 < B)
    (hE : ∀ v ∈ E₀, v < B) (hlen : E₀.length = n) :
    Lax13Proofs.Reasoning.Spec B (agree (clearState n E₀)) (embed clearSynth_impl)
      (fun _ σ' => ∃ E : List ℕ, σ'.arrs "exc" = E ∧ σ'.vars "sw" = n ∧
        E.length = n ∧ ∀ j, j < n → E[j]! = 0)
      (clearK n) := by
  have hle := clearLoop_le n n E₀ 0 hlen (by omega) (by omega)
    (fun j hj => absurd hj (Nat.not_lt_zero j))
  have hspec := spec_of_hnRefine
    (Φ := fun p : List ℕ × ℕ => p.1.length = n ∧ p.2 = n ∧ ∀ j, j < n → p.1[j]! = 0)
    (Q := fun (ra : List ℕ × ℕ) σ' => σ'.arrs "exc" = ra.1 ∧ σ'.vars "sw" = ra.2)
    (clearSynth' n E₀) hle (clear_state_holds n E₀) (clearState_bound hnB h1B hE)
    (exists_bigStepB_of_hnRefine (clearSynth' n E₀) hle (clear_state_holds n E₀)
      (clear_bpre hnB h1B hE))
    (le_of_eq (ecash_clearTotal n)) ?_
  · exact hspec.post (by
      rintro σ σ' - ⟨ra, ⟨hlen', hsw, hz⟩, hread, hvar⟩
      exact ⟨ra.1, hread, by rw [hvar, hsw], hlen', hz⟩)
  · intro ra s' cr σ' hΦ hst hag
    have he : (clearFrame n ∗ (arrayAssn ×ₐ natAssn) ra ("exc", "sw") ∗
        clearHole n E₀ ∗ GC)
        = (clearFrame n ∗ arrayAssn ra.1 "exc" ∗ (natAssn ra.2 "sw" ∗ clearHole n E₀) ∗ GC) := by
      simp only [prodAssn]; ac_rfl
    have he' : (clearFrame n ∗ (arrayAssn ×ₐ natAssn) ra ("exc", "sw") ∗
        clearHole n E₀ ∗ GC)
        = (clearFrame n ∗ natAssn ra.2 "sw" ∗ (arrayAssn ra.1 "exc" ∗ clearHole n E₀) ∗ GC) := by
      simp only [prodAssn]; ac_rfl
    exact ⟨readout_arr (he ▸ hst) hag, readout_scalar (he' ▸ hst) hag⟩

theorem mark_spec_at {B n rp1 : ℕ} (D E₀ : List ℕ) (hnB : n < B) (h1B : 1 < B)
    (hrB : rp1 < B) (hE : ∀ v ∈ E₀, v < B) (hD : ∀ v ∈ D, v < B) (hlen : E₀.length = n)
    (hdlen : n ≤ D.length) :
    Lax13Proofs.Reasoning.Spec B (agree (markState n rp1 D E₀)) (embed markSynth_impl)
      (fun _ σ' => ∃ E : List ℕ, σ'.arrs "exc" = E ∧ σ'.vars "sw" = n ∧
        E.length = n ∧ ∀ j, j < n → E[j]! = mkVal rp1 E₀[j]! D[j]!)
      (markK n) := by
  have hle := markLoop_le n rp1 D E₀ hdlen n E₀ 0 hlen (by omega) (by omega)
    (fun j hj => absurd hj (Nat.not_lt_zero j)) (fun _ _ _ => rfl)
  have hspec := spec_of_hnRefine
    (Φ := fun p : List ℕ × ℕ =>
      p.1.length = n ∧ p.2 = n ∧ ∀ j, j < n → p.1[j]! = mkVal rp1 E₀[j]! D[j]!)
    (Q := fun (ra : List ℕ × ℕ) σ' => σ'.arrs "exc" = ra.1 ∧ σ'.vars "sw" = ra.2)
    (markSynth' n rp1 D E₀) hle (mark_state_holds n rp1 D E₀)
    (markState_bound hnB h1B hrB hE hD)
    (exists_bigStepB_of_hnRefine (markSynth' n rp1 D E₀) hle (mark_state_holds n rp1 D E₀)
      (mark_bpre hnB h1B hrB hE hD))
    (le_of_eq (ecash_markTotal n)) ?_
  · exact hspec.post (by
      rintro σ σ' - ⟨ra, ⟨hlen', hsw, hz⟩, hread, hvar⟩
      exact ⟨ra.1, hread, by rw [hvar, hsw], hlen', hz⟩)
  · intro ra s' cr σ' hΦ hst hag
    have he : (markFrame n rp1 D ∗ (arrayAssn ×ₐ natAssn) ra ("exc", "sw") ∗
        markHole n rp1 D E₀ ∗ GC)
        = (markFrame n rp1 D ∗ arrayAssn ra.1 "exc" ∗
          (natAssn ra.2 "sw" ∗ markHole n rp1 D E₀) ∗ GC) := by
      simp only [prodAssn]; ac_rfl
    have he' : (markFrame n rp1 D ∗ (arrayAssn ×ₐ natAssn) ra ("exc", "sw") ∗
        markHole n rp1 D E₀ ∗ GC)
        = (markFrame n rp1 D ∗ natAssn ra.2 "sw" ∗
          (arrayAssn ra.1 "exc" ∗ markHole n rp1 D E₀) ∗ GC) := by
      simp only [prodAssn]; ac_rfl
    exact ⟨readout_arr (he ▸ hst) hag, readout_scalar (he' ▸ hst) hag⟩

/-! ### The exports

The two passes, stated from any IMP+ environment that holds the store —
the shape `RamScatter.mark_spec` is consumed in, at the tower's own list
arrays. The two statement deltas are the tower's standing ones: the
scratch arrays' entries are words state-globally (P7/D-bo) and the
scratch cells are pinned at zero (P7/D-bp). -/

/-- **The clearing pass, exported.** -/
theorem clearCom_spec {B n : ℕ} (hnB : n < B) (h1B : 1 < B) :
    Lax13Proofs.Reasoning.Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "sw" = 0 ∧ σ.vars "one" = 1 ∧ σ.vars "mkz" = 0 ∧
        (∃ E₀, σ.arrs "exc" = E₀ ∧ E₀.length = n ∧ ∀ v ∈ E₀, v < B))
      (embed clearSynth_impl)
      (fun _ σ' => ∃ E : List ℕ, σ'.arrs "exc" = E ∧ σ'.vars "sw" = n ∧
        E.length = n ∧ ∀ j, j < n → E[j]! = 0)
      (clearK n) := by
  intro σ hσ
  obtain ⟨hn, hsw, hone, hmkz, E₀, hexc, hlen, hEB⟩ := hσ
  have hag : agree (clearState n E₀) σ := by
    refine Codegen.agree_ofPairs ?_ ?_
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      assumption
  exact (clear_spec_at E₀ hnB h1B hEB hlen) σ hag

/-- **The marking sweep, exported.** -/
theorem markCom_spec {B n rp1 : ℕ} (D E₀ : List ℕ) (hnB : n < B) (h1B : 1 < B)
    (hrB : rp1 < B) (hlen : E₀.length = n) (hdlen : n ≤ D.length)
    (hEB : ∀ v ∈ E₀, v < B) (hDB : ∀ v ∈ D, v < B) :
    Lax13Proofs.Reasoning.Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "sw" = 0 ∧ σ.vars "one" = 1 ∧
        σ.vars "mkr" = rp1 ∧ σ.vars "mke" = 0 ∧ σ.vars "mkd" = 0 ∧ σ.vars "mka" = 0 ∧
        σ.vars "mkb" = 0 ∧ σ.vars "mkc" = 0 ∧ σ.vars "mkp" = 0 ∧ σ.vars "mkm" = 0 ∧
        σ.arrs "exc" = E₀ ∧ σ.arrs "dist" = D)
      (embed markSynth_impl)
      (fun _ σ' => ∃ E : List ℕ, σ'.arrs "exc" = E ∧ σ'.vars "sw" = n ∧ E.length = n ∧
        ∀ j, j < n → E[j]! = mkVal rp1 E₀[j]! D[j]!)
      (markK n) := by
  intro σ hσ
  obtain ⟨hn, hsw, hone, hmkr, e₁, e₂, e₃, e₄, e₅, e₆, e₇, hexc, hdist⟩ := hσ
  have hag : agree (markState n rp1 D E₀) σ := by
    refine Codegen.agree_ofPairs ?_ ?_
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        assumption
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> assumption
  exact (mark_spec_at D E₀ hnB h1B hrB hEB hDB hlen hdlen) σ hag

/-! ### The bridge to the baseline's function arrays

`RamScatter.mark_spec` states its pre and post at `arrOf`; the tower's
at lists. One lemma each way, and the integration wave's bridge for this
pass is these six lines and nothing else. -/

/-- In range, the `getElem!` of a function array is the function
(`Refine/BfsBridge.lean`'s `getElem!_arrOf`, restated so this file does
not depend on the search bridge). -/
theorem getElem!_arrOf {m i : ℕ} (f : ℕ → ℕ) (h : i < m) : (arrOf m f)[i]! = f i := by
  rw [getElem!_pos (arrOf m f) i (by simpa using h)]
  simp

theorem mem_arrOf_lt {m B : ℕ} {f : ℕ → ℕ} (h : ∀ z < m, f z < B) :
    ∀ w ∈ arrOf m f, w < B := by
  intro w hw
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hw
  exact h k (List.mem_range.1 hk)

/-- **The marking sweep in `RamScatter.mark_spec`'s own shape.** The
baseline's statement verbatim — the same pre vocabulary, the same
`markVal` post, the same `sw = n` — at the tower's cost and with the two
standing deltas (the scratch cells pinned, the arrays' entries words). -/
theorem markCom_spec_arrOf {B n r : ℕ} {E Dst : ℕ → ℕ} (hnB : n < B) (h1B : 1 < B)
    (hrB : r + 1 < B) (hE : ∀ i < n, E i ≤ 1) (hD : ∀ i < n, Dst i < B) :
    Lax13Proofs.Reasoning.Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "sw" = 0 ∧ σ.vars "one" = 1 ∧
        σ.vars "mkr" = r + 1 ∧ σ.vars "mke" = 0 ∧ σ.vars "mkd" = 0 ∧ σ.vars "mka" = 0 ∧
        σ.vars "mkb" = 0 ∧ σ.vars "mkc" = 0 ∧ σ.vars "mkp" = 0 ∧ σ.vars "mkm" = 0 ∧
        σ.arrs "dist" = arrOf n Dst ∧ σ.arrs "exc" = arrOf n E)
      (embed markSynth_impl)
      (fun _ σ' => σ'.arrs "exc" = arrOf n (fun j => RamScatter.markVal r (E j) (Dst j)) ∧
        σ'.vars "sw" = n)
      (markK n) := by
  intro σ hσ
  obtain ⟨hn, hsw, hone, hmkr, e₁, e₂, e₃, e₄, e₅, e₆, e₇, hdist, hexc⟩ := hσ
  obtain ⟨σ', hrun, E', hread, hswn, hElen, hEval⟩ :=
    (markCom_spec (B := B) (n := n) (rp1 := r + 1) (arrOf n Dst) (arrOf n E) hnB h1B hrB
      (length_arrOf n E) (le_of_eq (length_arrOf n Dst).symm)
      (mem_arrOf_lt fun z hz => by have := hE z hz; omega) (mem_arrOf_lt hD)) σ
      ⟨hn, hsw, hone, hmkr, e₁, e₂, e₃, e₄, e₅, e₆, e₇, hexc, hdist⟩
  refine ⟨σ', hrun, ?_, hswn⟩
  rw [hread]
  refine List.ext_getElem (by rw [length_arrOf, hElen]) fun i h₁ h₂ => ?_
  have hi : i < n := by rw [hElen] at h₁; exact h₁
  rw [Lax13Proofs.Reasoning.Lib.getElem_arrOf, ← getElem!_pos E' i h₁, hEval i hi,
    getElem!_arrOf E hi, getElem!_arrOf Dst hi, mkVal_eq_markVal]

end Export

/-! ## 7. Gate (ledger D4, refute before prove)

Both synthesized programs are *run*, by `Ir/Semantics.lean`'s own
evaluator, on `RamScatter.Demo`'s five-vertex arena, and what comes out
is `#guard`ed against `RamScatter.markVal` — the baseline's arithmetic,
not a second copy. Each positive check carries a negative control. -/

section Gate

/-- The sweep at radius `1` over the distance array of a path from
vertex `0`, nothing excluded yet. -/
def gRun (rp1 : ℕ) (D E₀ : List ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 4000 markSynth_impl (markState E₀.length rp1 D E₀)).bind
    fun p => p.1.arrs "exc"

def gClear (E₀ : List ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 4000 clearSynth_impl (clearState E₀.length E₀)).bind
    fun p => p.1.arrs "exc"

-- the synthesized sweep is `markVal` pointwise, on the baseline's own
-- radius-one reading …
#guard gRun 2 [0, 1, 2, 3, 4] [0, 0, 0, 0, 0]
  = some ((List.range 5).map fun j => RamScatter.markVal 1 0 j)
#guard gRun 2 [0, 1, 2, 3, 4] [0, 0, 0, 0, 0] = some [1, 1, 0, 0, 0]
-- … an already-excluded vertex stays excluded, whatever the distance …
#guard gRun 2 [2, 2, 2, 2, 2] [0, 1, 0, 0, 0] = some [0, 1, 0, 0, 0]
-- … and this is `RamScatter`'s own published reading of the arithmetic
#guard [RamScatter.markVal 1 0 0, RamScatter.markVal 1 0 1, RamScatter.markVal 1 0 2,
  RamScatter.markVal 1 1 2] = [1, 1, 0, 1]
-- a wider radius reaches further
#guard gRun 3 [0, 1, 2, 3, 4] [0, 0, 0, 0, 0] = some [1, 1, 1, 0, 0]

-- **The negative controls.** The radius bites, and the check can tell.
/--
error: Expression
  decide (gRun 2 [0, 1, 2, 3, 4] [0, 0, 0, 0, 0] = some [1, 1, 1, 0, 0])
did not evaluate to `true`
-/
#guard_msgs in
#guard gRun 2 [0, 1, 2, 3, 4] [0, 0, 0, 0, 0] = some [1, 1, 1, 0, 0]

-- …and the sweep does not clear an exclusion bit it found set.
/--
error: Expression
  decide (gRun 2 [2, 2, 2, 2, 2] [0, 1, 0, 0, 0] = some [0, 0, 0, 0, 0])
did not evaluate to `true`
-/
#guard_msgs in
#guard gRun 2 [2, 2, 2, 2, 2] [0, 1, 0, 0, 0] = some [0, 0, 0, 0, 0]

-- the clearing pass clears …
#guard gClear [1, 1, 1, 1, 1] = some [0, 0, 0, 0, 0]
-- … and the check can tell a pass that did not run
/--
error: Expression
  decide (gClear [1, 1, 1, 1, 1] = some [1, 1, 1, 1, 1])
did not evaluate to `true`
-/
#guard_msgs in
#guard gClear [1, 1, 1, 1, 1] = some [1, 1, 1, 1, 1]

-- The exported budgets cover real runs (`n = 5`: `markK 5 = 194`,
-- `clearK 5 = 64`), and a wrong budget is refuted.
#guard (Ir.evalFuel 4000 markSynth_impl (markState 5 2 [0, 1, 2, 3, 4] [0, 0, 0, 0, 0])).map
  (fun p => decide (Codegen.cash p.2 ≤ markK 5)) = some true
#guard ¬ ((Ir.evalFuel 4000 markSynth_impl
  (markState 5 2 [0, 1, 2, 3, 4] [0, 0, 0, 0, 0])).map
  (fun p => decide (Codegen.cash p.2 ≤ 100)) = some true)
#guard (Ir.evalFuel 4000 clearSynth_impl (clearState 5 [1, 1, 1, 1, 1])).map
  (fun p => decide (Codegen.cash p.2 ≤ clearK 5)) = some true
#guard ¬ ((Ir.evalFuel 4000 clearSynth_impl (clearState 5 [1, 1, 1, 1, 1])).map
  (fun p => decide (Codegen.cash p.2 ≤ 30)) = some true)

end Gate

/-! ## 8. Axioms -/

/-- info: 'Lax3Proofs.Refine.ScatterSynth.markCom_spec_arrOf' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms markCom_spec_arrOf

/-- info: 'Lax3Proofs.Refine.ScatterSynth.clearCom_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms clearCom_spec

/-- info: 'Lax3Proofs.Refine.ScatterSynth.markSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms markSynth

/-- info: 'Lax3Proofs.Refine.ScatterSynth.mark_brefine' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms mark_brefine

/-! ## 8b. The probe R2A/D-d asks for: the search as a leaf rule

Reported, not asserted. `mopBfs` is `BfsQSynth.bfsQS` under a name the
operator phase cannot see through (the `mopSucc` idiom, P7/D-bb), and
`hnr_mop_bfs` is its single rule — the P1 wave's own synthesis theorem,
re-registered. The probe below asks whether `sepref_synth` can then use
the whole depth-capped search as *one operation* inside a larger
program, which is what the greedy scan needs.

Whatever it reports is the finding; the `#sepref_synth` form reports and
does not throw (`Sepref/Definition.lean`'s negative-control precedent),
so this section cannot break the build.

**What the two probes report** (this is R2A/D-d's answer, measured):

1. **The search fires as a leaf. It works.** The first probe hands
   `sepref_synth` the search alone, inside a precondition with one extra
   owned cell, and it emits `BfsQSynth.bfsQSynth_impl` — the P1 wave's
   program, unchanged, with the extra cell framed off. So a synthesized
   engine *can* be re-used as one operation of a larger one, and the
   greedy scan's picking branch is not blocked at the leaf.

   **R2A/D-f — but only if the rule's precondition is spelled out.** The
   first version of `hnr_mop_bfs` stated its precondition as
   `BfsQSynth.bfsQPre …` and the tool reported *"no rule translates
   `bfsQPre … ∗ junkCell "mkz"`"*: `frameMatch` compares conjunct by
   conjunct, and a `def` that returns a `∗`-chain is one atom to it.
   This is P6/D-bc's composite-assertion opacity met at the scale of a
   whole engine's footprint. The fix costs nothing — write the
   twenty-three conjuncts — but a caller who does not know it reads the
   report as "leaf rules do not work", which is the opposite of true.

2. **The composition stalls one layer up, in `fri`.** The second probe
   is the picking branch itself — the search, then this file's marking
   sweep over the distance array the search produced. `hnr_bind` fires
   the leaf, and then `hnr_while` (the sweep) stalls with *"fri: no
   premise conjunct matches the target conjunct"*. The sweep wants
   `arrayAssn st.1 "dist"` as a conjunct of its own; after the leaf,
   `st.1` is a *component* of the bound four-tuple
   `hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn) st
   ("dist","q","head","tl")`, and the frame layer does not split a bound
   tuple in the `fri` direction. `Sepref/Frame.lean`'s `conjunctsSplit`
   does exactly this split in the *other* direction (P7/D-ba), so the
   gap is one rule, not a design problem.

So the honest statement for the integration decision is: the greedy scan
is **one frame-layer rule away** from synthesizing, not a redesign away;
and the rule is the `fri` counterpart of a split the tower already
performs. -/

section LeafProbe

/-- The abstract search, as an operation of its own. -/
noncomputable def mopBfs (n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) :
    NRest BfsQ.St ECost := BfsQSynth.bfsQS n d src off tgt alv dist₀ q₀

theorem mopBfs_eq (n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) :
    mopBfs n d src off tgt alv dist₀ q₀ = BfsQSynth.bfsQS n d src off tgt alv dist₀ q₀ := rfl

/-- Its only rule: the P1 wave's synthesis, as a leaf — with the
precondition and the frame **spelled out**, not behind the names
`bfsQPre`/`bfsQFrame`. That is the whole difference between a rule the
matcher fires and one it does not (§8b's first report). -/
@[sepref_fr_rules]
theorem hnr_mop_bfs (n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) :
    hnRefine
      (hnCtxt arrayAssn dist₀ "dist" ∗ hnCtxt arrayAssn q₀ "q" ∗
        hnCtxt natAssn 0 "i" ∗ hnCtxt natAssn 0 "head" ∗
        hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
        hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
        hnCtxt natAssn src "src" ∗ hnCtxt natAssn 1 "one" ∗
        junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
        junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
        junkCell "du")
      BfsQSynth.bfsQSynth_impl
      (junkCell "a" ∗ hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn src "src" ∗
        junkCell "i" ∗ hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
        hnCtxt natAssn n "n" ∗ hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
        hnCtxt natAssn 1 "one" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
        junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
        junkCell "du")
      ("dist", "q", "head", "tl")
      (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (mopBfs n d src off tgt alv dist₀ q₀) :=
  BfsQSynth.bfsQSynth' n d src off tgt alv dist₀ q₀

attribute [irreducible] mopBfs

set_option maxHeartbeats 400000 in
#sepref_synth (n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) :
  hnRefine
    (hnCtxt arrayAssn dist₀ "dist" ∗ hnCtxt arrayAssn q₀ "q" ∗
      hnCtxt natAssn 0 "i" ∗ hnCtxt natAssn 0 "head" ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
      hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
      hnCtxt natAssn src "src" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
      junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
      junkCell "du" ∗ hnCtxt natAssn 1 "mkz")
    _ _ ("dist", "q", "head", "tl")
    (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (mopBfs n d src off tgt alv dist₀ q₀)

-- …and the shape the greedy scan's picking branch actually is: the
-- search, then this file's marking sweep over the distance array the
-- search produced.
set_option maxHeartbeats 1000000 in
#sepref_synth (n d src rp1 : ℕ) (off tgt alv dist₀ q₀ exc₀ : List ℕ) :
  hnRefine
    (hnCtxt arrayAssn dist₀ "dist" ∗ hnCtxt arrayAssn q₀ "q" ∗
      hnCtxt natAssn 0 "i" ∗ hnCtxt natAssn 0 "head" ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
      hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
      hnCtxt natAssn src "src" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
      junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
      junkCell "du" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (exc₀, 0) ("exc", "sw") ∗
      hnCtxt natAssn rp1 "mkr" ∗
      junkCell "mke" ∗ junkCell "mkd" ∗ junkCell "mka" ∗ junkCell "mkb" ∗
      junkCell "mkc" ∗ junkCell "mkp" ∗ junkCell "mkm")
    _ _ ("exc", "sw") (arrayAssn ×ₐ natAssn)
    (NRest.bindT (mopBfs n d src off tgt alv dist₀ q₀) fun st =>
      markLoop n rp1 st.1 (exc₀, 0))

end LeafProbe

/-! ## 9. What the greedy scan would cost, and why it is not here
(R2A/D-d, R2A/D-e)

The scatter engine's middle phase is

```
sv := 0
while sv < n:
  if cnt < t and 0 < tab[sv] and exc[sv] = 0:
    cnt := cnt + 1 ; src := sv ; bfsCom r ; markCom r
  sv := sv + 1
```

— `RamScatter.scatterLoop`. Three things about it are worth stating
precisely, because together they are the satellite's architectural
report.

**R2A/D-d — the scan's picking branch is a whole other engine, and §8b
prices the gap exactly.** The body contains `RamBfs.bfsCom r`, the
depth-capped search, which the P1 wave re-derived as a *separate*
synthesis (`BfsQSynth.bfsQSynth_impl`, ≈49 s, three nested loops). At
the abstract layer the composition is routine — `bindT (bfsQS …) fun st
=> markLoop …` and `NRest.bindT_mono` against `bfsQS_correct`. At the
synthesis layer §8b's two probes settle it: the search **does** fire as
a single leaf rule (the `mopSucc` idiom of P7/D-bb, scaled to a whole
engine), provided the rule's precondition is spelled out rather than
named (R2A/D-f); and the *composition* then stalls in the frame layer,
because the sweep's read of `dist` has to be split out of the search's
bound result tuple and `fri` has no rule for that. One rule, the
counterpart of `conjunctsSplit`.

That is the item to decide on. Until it exists the scan cannot be
synthesized; once it exists the scan is an ordinary two-loop program
with two leaves.

**R2A/D-e — the scan's correctness is `RamScatter`'s own, and it is
capital.** `greedySet`/`GSel`/`selBelow` and the counting lemmas
(`ncard_selBelow_succ_of_gsel`, `selBelow_all`) are arena mathematics
with no machine in them; `Progress` and `ScatterPot` are the invariant
and the potential. A tower re-derivation *consumes* all of it — the only
new work is restating `Progress` over the abstract loop state instead of
over `Env`, which is the same shape-change the fill loop's `fillI`
already exhibits (six `Ir.State` conjuncts down to one). So the scan is
not mathematically expensive; it is *tool*-expensive, and the tool cost
is the leaf-rule gap above.

## 10. Telemetry

* **Synthesis wall clock**, warm build: the file elaborated in **≈10 s**
  at the point both syntheses had landed (the §8b probes add ≈35 s on
  top, since one of them re-runs the search's own translate). No bespoke
  tactic work, no hand-written frame clause, no `LOOP_VARIANT` (inert
  since R0/D-b). Both `Com`s came out right on the first run, with every
  scratch cell in the slot the program consumes it at — the
  junk-destination order is the precondition's listing order,
  confirmed.

* **Cost constants, computed** (`decide +kernel` from the per-iteration
  accounts, not tuned):

  | pass | tower | baseline | ratio |
  |---|---|---|---|
  | clear | `clearK n = 12·n + 4` | `11·n + 6` (`Fill.loop_spec` at `e = 0`) | 1.09 |
  | mark | `markK n = 38·n + 4` | `23·n + 6` (`RamScatter.mark_spec`) | 1.65 |

  The clear pass is within 10 %; the sweep is not, and the reason is
  R2A/D-a and nothing else — one IMP+ expression walk (`markExpr.size =
  13`, charged `10 + 13 = 23` per cell) against five IR three-address
  operations plus their two operand reads (charged `38`). This is the
  first measured instance of the IR's *no-expression-layer* choice
  (ledger D2) costing an ND-MC engine, and it is a constant factor on
  one linear pass.

* **Bounds pass via `BRefine`: 0 `Ir.State` predicates authored.** The
  side-condition traffic for the sweep — the largest straight-line body
  the tower has bounded so far — is **six arithmetic goals**: five monus
  bounds (`by rw [apply_sub]; omega`), one product bound
  (`mul_sub_lt`, the single lemma `omega` cannot do), and the counter's
  bump. Everything else is free: both `aget`s, the `aset`, every guard,
  and every index. That is the P0.2 prediction (~2 side conditions per
  loop) confirmed at ~1 per *creation site* instead, which is the honest
  unit.

* **Tool gaps met** (feeding the worklist):
  1. **no `sepref_brefine_rules` database** — every one of the nine
     operation lemmas of §5 is `BRefine.perm … (by ac_rfl) … ∘
     BRefine.frame`, i.e. the permutation the synthesis driver already
     computes, re-authored by hand. That is ≈150 of this file's lines
     and it is pure bookkeeping (`BfsQBounded.lean`'s R2/D-f item 3,
     re-met at nine operations instead of three);
  2. **no `BRefine` rule for junk cells** — `junkCell` has to be opened
     with `BRefine.pre_ex`, so the loop assertion carries the seven
     scratch values in a seven-tuple existential (`markΓ`). A
     `BRefine.junk` rule that treats a junk destination the way
     `hnr_mop_binop` does would delete `markΓ`, `mkΓ_entails_markΓ` and
     the two extraction lemmas;
  3. **`fri` cannot split a bound tuple** — §8b probe 2. A synthesized
     engine used as a leaf delivers its result as one `prodAssn`
     conjunct; a consumer that reads one component of it stalls with
     "fri: no premise conjunct matches the target conjunct".
     `Sepref/Frame.lean`'s `conjunctsSplit` does this split in the
     opposite direction already (P7/D-ba), so the fix is its `fri`
     counterpart;
  4. **`frameMatch` treats a named assertion as an atom** (R2A/D-f) — a
     rule whose precondition is written `bfsQPre …` never fires; the
     same rule with the twenty-three conjuncts written out fires
     immediately. Diagnosable only by reading the report, and the report
     says "no rule translates", which points at the wrong thing.

  Gaps 1, 2 and 4 are ergonomic. Gap 3 is the one that blocks the greedy
  scan, and it is a single rule.

* **Refuted before proved.** §7 runs both *synthesized* programs on
  `RamScatter.Demo`'s arena and checks the sweep against
  `RamScatter.markVal` — the baseline's own arithmetic — at two radii
  and at a pre-set exclusion bit, with three pinned negative controls
  and two cost-coverage refutations. The `omega`-through-`Ir.Val` trap
  did not fire (every side condition is on ℕ-typed abstract values, as
  `BfsQBounded.lean` predicted); the junk-destination misfire did not
  fire either, because the seven cells are listed in consumption order
  (R2A/D-c).

* **Axioms.** `markCom_spec_arrOf`, `clearCom_spec`, `markSynth` and
  `mark_brefine` pinned at `[propext, Classical.choice, Quot.sound]`.

## 11. Scope: where the other two named engines actually live
(R2A/D-g, R2A/D-h)

The brief this file answers named three engines — RamScatter,
FormulaTables, BotEval. Two of the three have **no machine content at
all**, and the record should say so plainly rather than leave a gap.

**R2A/D-g — `Lax3Proofs.FormulaTables` and `Lax3Proofs.BotEval` are
mathematics, not engines.** Neither file contains a `Com`, a `Spec`, a
`Run`, an `Env` or a cost. `FormulaTables.lean` says so in its own
header ("Everything here is data and lemmas about data — no program, no
arena, no run"): it is `tablesAt`, `stepFml`, `bcOf` and the rank
invariant. `BotEval.lean` is the satisfaction theory of the edgeless
arena — `sat_exL_bot`, `sat_exU_bot_of_repr`, `ncard_le_of_injOn_rowOf`,
the `k + 2 ^ L` candidate bound. There is nothing for a *program*
refinement to re-derive; both are already the abstract layer, and the
tower's job would be to consume them, which is what the machine engine
below does.

**R2A/D-h — the base-case engine is `RamDriver.baseCom`, and its program
text is a function of the formula.** What the brief's "BotEval" means as
an engine is `RamDriver.baseCom = reprCom ; (per vertex: fold botCom
over tablesAt)`, walked in `RamDriverBot.lean` and exported as
`RamDriverBot.baseCost` / `RamDriverCompose.baseImplements`. (Wave
R1.8-T4a dropped the `reprCom` half from the pass — see
`Refine.BaseShed`; the survey's verdict on the remaining half stands
verbatim, and the `reprCom` bullet below now reads as a statement about
a compiled contingency rather than about the base case.) Two of its
three parts are outside what `sepref_synth` can produce, and for the
same reason:

* `botCom jd ψ out` recurses on the **syntax of `ψ`**, and at each
  recursion step it invents its own cell names by string append
  (`out ++ "a"`, `out ++ "b"`, `out ++ "g"`, `out ++ "m"`,
  `out ++ "w"`). A `sepref_synth` invocation produces one fixed
  `Ir.Com`; here the `Com` — and the *set of cells it owns* — is a
  function of the formula. A tower derivation would have to be an
  induction over `DistFO` with the assertion parameterized by the name
  prefix, proved by hand: possible, but no part of the tool applies to
  it.
* `reprCom j L` folds `rowEqExpr` over `List.range L`, so its program
  text depends on the palette size. In the IR that fold *must* become a
  third nested loop over colours (the IR has no expression layer), which
  is an improvement — `reprCom` is the one part of the *old* base case
  (R1.8-T4a: it is now a compiled contingency, in no program) that is
  an ordinary loop program and is a genuine tower target, at three
  nested loops (`z < n`, `rw < rp`, `c < L`) and a `2 ^ L` bound on
  `rp` from `BotEval.ncard_le_of_injOn_rowOf`.

The same syntax-recursion runs one level up: `RamDriver.driverAux`
builds the driver by recursion on the depth budget and names its cells
`curName j`, `colName j c`, `tabName j i`. So the boundary the rebase
has to decide is not "which engines are hard" but **"where the tower
stops and the name-generating recursion begins"** — and that boundary
is above the leaf engines and below `driverAt`.
-/


/-! ## 12. The greedy scan — phase 2, completed (wave 2A′)

§9 priced this phase and named the one thing that blocked it: the
picking branch runs a *whole other engine* (`RamBfs.bfsCom`, the tower's
`BfsQSynth.bfsQSynth_impl`) and the frame layer could not split the
search's bound result tuple for the sweep that consumes it. Tool wave
T1 closed that (`Sepref/Frame.lean` T1/D-b, D-d, D-f), and what follows
is the phase, derived end to end: an abstract `NRest` program whose
loop state carries the exclusion bits, the search's two scratch arrays
and the two counters; its correctness against `RamScatter`'s own arena
mathematics; `sepref_synth`; the cashing chain; and the export.

### Judgment calls

**R2A/D-i — `Progress` moves into the loop state.** The baseline's
`RamScatter.Progress` is a predicate on an `Imp.Env`: it reads the count
out of a cell and the exclusion bits out of a function array. `AProg`
below is the same disjunction with the machine removed — the count and
the bit list are *components of the abstract loop state*. §9 predicted
the fill loop's six-conjuncts-to-one shrink and that is what happened:
`Progress` has no `σ.vars`, no `σ.arrs` and no `arrOf` in it, and the
scan's `irWhileIT` invariant (`scatP`) is three index facts.

**R2A/D-j — the search's entry cells become arguments of the leaf.**
`hnr_mop_bfs` (§8b) pins `i` and `head` at the abstract value `0`,
which is right for a *caller* but wrong for a *loop*: a second turn
finds `i` junk and `head` holding the queue's tail. Zeroing them inside
the program does not help, because the translate phase does not read a
bound result's value off `hnr_seq`'s `returnT a ≤ m` guard (tool gap 5
below), so the rule still does not fire. `mopBfsAt` takes the two entry
values as *arguments* and asserts them zero itself; the assertion is
discharged by the abstract program (`mopZeroI`/`mopZeroHd` return `0`)
and the rule fires. Same for `src`: the search's source cell is written
by a cell-pinned `mopSrcOf` whose result is threaded into the leaf's
`src` argument.

**R2A/D-k — the radius and the threshold enter through cells.** The
baseline compiles both into the program text (`scatterCom r t` is a
different program for every `r` and `t`). Here `d`/`sent` hold `r` and
`r + 1` and `t` holds the threshold, so **one** synthesized program
serves every radius and every threshold — the same improvement R2A/D-b
made for the sweep, now for the whole engine. The sweep inside the scan
reads its shifted radius off `sent`, so the standalone sweep's `mkr`
cell is not owned by the scan at all.

**R2A/D-l — one named debt, and it is the search's bounds pass.** See
§15.
-/

section Scan

open Lax13Proofs.Reasoning (arrOf length_arrOf arrOf_congr)
open Lax13Proofs.Refine.BfsQ (Csr St QPost Fr pack4 fillLoop fillLoop_le drainLoop_le
  popC scanC fillC bfsK bfsBudget rowSum)
open Lax13Proofs.Refine.Sepref (E2)

/-- The scan's loop state: exclusion bits, the search's two scratch
arrays, the count and the scan counter. -/
abbrev SSt : Type := List ℕ × List ℕ × List ℕ × ℕ × ℕ

/-- What a turn of the scan delivers before the counter moves. -/
abbrev PSt : Type := List ℕ × List ℕ × List ℕ × ℕ

/-! ### The three cell-pinned zeroing operations -/

noncomputable def mopZeroI : NRest ℕ ECost := mopConstN 0
theorem mopZeroI_eq : mopZeroI = mopConstN 0 := rfl

@[sepref_fr_rules]
theorem hnr_mop_zeroI : hnRefine (junkCell "i") (.const "i" 0) (□ : Assn) "i" natAssn
    mopZeroI := by rw [mopZeroI_eq]; exact hnr_mop_constN "i" 0

attribute [irreducible] mopZeroI

noncomputable def mopZeroHd : NRest ℕ ECost := mopConstN 0
theorem mopZeroHd_eq : mopZeroHd = mopConstN 0 := rfl

@[sepref_fr_rules]
theorem hnr_mop_zeroHd : hnRefine (junkCell "head") (.const "head" 0) (□ : Assn) "head"
    natAssn mopZeroHd := by rw [mopZeroHd_eq]; exact hnr_mop_constN "head" 0

attribute [irreducible] mopZeroHd

noncomputable def mopZeroSw : NRest ℕ ECost := mopConstN 0
theorem mopZeroSw_eq : mopZeroSw = mopConstN 0 := rfl

@[sepref_fr_rules]
theorem hnr_mop_zeroSw : hnRefine (junkCell "sw") (.const "sw" 0) (□ : Assn) "sw" natAssn
    mopZeroSw := by rw [mopZeroSw_eq]; exact hnr_mop_constN "sw" 0

attribute [irreducible] mopZeroSw

/-- `src := sv`, at the two cells the search and the scan own. -/
noncomputable def mopSrcOf (v : ℕ) : NRest ℕ ECost := mopCopy v
theorem mopSrcOf_eq (v : ℕ) : mopSrcOf v = mopCopy v := rfl

@[sepref_fr_rules]
theorem hnr_mop_srcOf (v : ℕ) :
    hnRefine (junkCell "src" ∗ hnCtxt natAssn v "sv") (.copy "src" "sv")
      (hnCtxt natAssn v "sv") "src" natAssn (mopSrcOf v) := by
  rw [mopSrcOf_eq]; exact hnr_mop_copy "src" "sv" v

attribute [irreducible] mopSrcOf

/-! ### The search, as a leaf that may be re-entered

`mopBfs`'s rule pins `i` and `head` at the abstract value `0`, and the
translate phase does not read a bound result's value off `hnr_seq`'s
`returnT a ≤ m` guard — so a zeroing step *inside* the program cannot
feed it. The fix is to make the two entry values **arguments** of the
operation and let the operation itself assert them zero. -/

noncomputable def mopBfsAt (n d src i₀ hd₀ : ℕ) (off tgt alv dist₀ q₀ : List ℕ) :
    NRest BfsQ.St ECost :=
  bindT (NRest.assert (i₀ = 0 ∧ hd₀ = 0)) fun _ =>
    BfsQSynth.bfsQS n d src off tgt alv dist₀ q₀

@[sepref_fr_rules]
theorem hnr_mop_bfsAt (n d src i₀ hd₀ : ℕ) (off tgt alv dist₀ q₀ : List ℕ) :
    hnRefine
      (hnCtxt arrayAssn dist₀ "dist" ∗ hnCtxt arrayAssn q₀ "q" ∗
        hnCtxt natAssn i₀ "i" ∗ hnCtxt natAssn hd₀ "head" ∗
        hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
        hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
        hnCtxt natAssn src "src" ∗ hnCtxt natAssn 1 "one" ∗
        junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
        junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
        junkCell "du")
      BfsQSynth.bfsQSynth_impl
      (junkCell "a" ∗ hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn src "src" ∗
        junkCell "i" ∗ hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
        hnCtxt natAssn n "n" ∗ hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
        hnCtxt natAssn 1 "one" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
        junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
        junkCell "du")
      ("dist", "q", "head", "tl")
      (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (mopBfsAt n d src i₀ hd₀ off tgt alv dist₀ q₀) := by
  rw [mopBfsAt]
  refine hnr_assert fun h => ?_
  obtain ⟨rfl, rfl⟩ := h
  exact BfsQSynth.bfsQSynth' n d src off tgt alv dist₀ q₀

theorem mopBfsAt_eq (n d src i₀ hd₀ : ℕ) (off tgt alv dist₀ q₀ : List ℕ) :
    mopBfsAt n d src i₀ hd₀ off tgt alv dist₀ q₀ =
      bindT (NRest.assert (i₀ = 0 ∧ hd₀ = 0)) fun _ =>
        BfsQSynth.bfsQS n d src off tgt alv dist₀ q₀ := rfl

attribute [irreducible] mopBfsAt

/-! ### Packing -/

noncomputable def pack4' (E D Q : List ℕ) (c : ℕ) : NRest PSt ECost :=
  bindT (mopPair Q c) fun p => bindT (mopPair D p) fun p' => mopPair E p'

noncomputable def pack5 (E D Q : List ℕ) (c v : ℕ) : NRest SSt ECost :=
  bindT (mopPair c v) fun p => bindT (mopPair Q p) fun p' =>
    bindT (mopPair D p') fun p'' => mopPair E p''

/-! ### The turn -/

noncomputable def pickF (n d : ℕ) (off tgt alv : List ℕ) : SSt → NRest PSt ECost := fun s =>
  bindT mopZeroI fun i₀ =>
    bindT mopZeroHd fun hd₀ =>
      bindT (mopSrcOf s.2.2.2.2) fun sv' =>
        bindT (mopBfsAt n d sv' i₀ hd₀ off tgt alv s.2.1 s.2.2.1) fun st =>
          bindT mopZeroSw fun z =>
            bindT (mopPair s.1 z) fun p =>
              bindT (markLoop n (d + 1) st.1 p) fun mr =>
                bindT (mopSucc s.2.2.2.1) fun c' => pack4' mr.1 st.1 st.2.1 c'

noncomputable def scatF (n d t : ℕ) (off tgt alv tab : List ℕ) : SSt → NRest SSt ECost :=
  fun s =>
    bindT (mopAget tab s.2.2.2.2) fun tb =>
      bindT (mopAget s.1 s.2.2.2.2) fun ex =>
        bindT (irIf (decide (s.2.2.2.1 < t))
            (irIf (decide (0 < tb))
              (irIf (decide (ex = 0)) (pickF n d off tgt alv s) (pack4' s.1 s.2.1 s.2.2.1 s.2.2.2.1))
              (pack4' s.1 s.2.1 s.2.2.1 s.2.2.2.1))
            (pack4' s.1 s.2.1 s.2.2.1 s.2.2.2.1)) fun z =>
          bindT (mopSucc s.2.2.2.2) fun v' => pack5 z.1 z.2.1 z.2.2.1 z.2.2.2 v'

def scatBf (n : ℕ) : SSt → Bool := fun s => decide (s.2.2.2.2 < n)

def scatP (n : ℕ) (tab : List ℕ) : SSt → Prop := fun s =>
  s.2.2.2.2 < n ∧ n ≤ tab.length ∧ n ≤ s.1.length

noncomputable def scatLoop (n d t : ℕ) (off tgt alv tab : List ℕ) (s₀ : SSt) :
    NRest SSt ECost :=
  irWhileIT (fun s => scatBf n s = true → scatP n tab s) (scatBf n)
    (scatF n d t off tgt alv tab) s₀

/-! ### The synthesis -/

set_option maxHeartbeats 4000000 in
sepref_synth scatSynth (n d t : ℕ) (off tgt alv tab exc₀ dist₀ q₀ : List ℕ) :
  hnRefine
    (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
        (exc₀, dist₀, q₀, 0, 0) ("exc", "dist", "q", "cnt", "sv") ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
      hnCtxt arrayAssn alv "alv" ∗ hnCtxt arrayAssn tab "tab" ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
      hnCtxt natAssn t "t" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "sctb" ∗ junkCell "scex" ∗
      junkCell "src" ∗ junkCell "i" ∗ junkCell "head" ∗ junkCell "sw" ∗
      junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
      junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
      junkCell "du")
    _ _ ("exc", "dist", "q", "cnt", "sv")
    (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (scatLoop n d t off tgt alv tab (exc₀, dist₀, q₀, 0, 0))

/-! ## The search's bound, with the queue's length kept

`BfsQSynth.bfsQS_correct` routes through `bfsQ`, whose last step
projects the result tuple onto `dist`; the queue's length — a field of
`BfsQ.Fr` all along — is lost there. A scan that re-enters the search
needs it, so the same derivation is run once more directly on `bfsQS`,
whose result *is* the drain's. -/

theorem bfsQS_correct' {n ns d : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}
    {src : ℕ} {dist₀ q₀ : List ℕ} (hc : Csr n ns G off tgt alv)
    (hsrc : src < n) (hdlen : dist₀.length = n) (hqlen : q₀.length = n) :
    BfsQSynth.bfsQS n d src off tgt alv dist₀ q₀
      ≤ NRest.spec (fun st' : St => QPost n d src G alv hsrc st'.1 ∧ st'.2.1.length = n)
          (fun _ => irUnit Currency.skip + liftACost (bfsBudget n ns)) := by
  have halv : src < alv.length := by rw [hc.shape.2.1]; exact hsrc
  have htail : ∀ p : List ℕ × ℕ, (p.1.length = n ∧ ∀ j, j < n → p.1[j]! = d + 1) →
      (NRest.bindT (mopAset p.1 src 0) fun D => NRest.bindT (mopAset q₀ 0 src) fun Q =>
        NRest.bindT (mopAget alv src) fun a =>
          NRest.bindT (irIf (decide (0 < a)) (mopConstN 1) (mopConstN 0)) fun tl =>
            NRest.bindT (pack4 D Q 0 tl) fun st =>
              BfsQSynth.drainLoop' n d (d + 1) off tgt alv st)
        ≤ NRest.spec (fun st' : St => QPost n d src G alv hsrc st'.1 ∧ st'.2.1.length = n)
            (fun _ => liftACost (n • iter popC + ns • iter scanC
              + (cu Currency.aset + cu Currency.aset + cu Currency.aget + cu Currency.ite
                + cu Currency.const + cu Currency.skip + cu Currency.skip + cu Currency.skip
                + cu Currency.«while»))) := by
    rintro p ⟨hplen, hpfill⟩
    have hseed := Fr.seed (n := n) (d := d) (G := G) (alv := alv) (s := ⟨src, hsrc⟩)
      hplen hqlen hpfill
    have hrow0 : rowSum off (q₀.set 0 src) 0 = 0 := by simp [rowSum]
    have hdrain := drainLoop_le (d := d) (s := ⟨src, hsrc⟩) hc n
      (p.1.set src 0, q₀.set 0 src, 0, if 0 < alv[src]! then 1 else 0) hseed (by simp)
    rw [hrow0, Nat.sub_zero, Nat.sub_zero] at hdrain
    have hmono : NRest.spec
        (fun z' : St => Fr n d G alv ⟨src, hsrc⟩ z'.1 z'.2.1 z'.2.2.1 z'.2.2.2 ∧
          z'.2.2.2 ≤ z'.2.2.1)
        (fun _ => liftACost (E2 (iter popC) (iter scanC) n ns + cu Currency.«while»))
        ≤ NRest.spec (fun st' : St => QPost n d src G alv hsrc st'.1 ∧ st'.2.1.length = n)
          (fun _ => liftACost (E2 (iter popC) (iter scanC) n ns + cu Currency.«while»)) := by
      refine Sepref.spec_mono ?_ (fun _ _ => le_rfl)
      rintro z' ⟨hfr, hle⟩
      rw [le_antisymm hfr.hdle hle] at hfr
      exact ⟨⟨hfr.dlen, fun v k hk => hfr.dist_le_iff v hk⟩, hfr.qlen⟩
    have hstep : ∀ tl : ℕ, tl = (if 0 < alv[src]! then 1 else 0) →
        (NRest.bindT (pack4 (p.1.set src 0) (q₀.set 0 src) 0 tl) fun st =>
          BfsQSynth.drainLoop' n d (d + 1) off tgt alv st)
          ≤ NRest.spec (fun st' : St => QPost n d src G alv hsrc st'.1 ∧ st'.2.1.length = n)
              (fun _ => (irUnit Currency.skip + irUnit Currency.skip + irUnit Currency.skip)
                + liftACost (E2 (iter popC) (iter scanC) n ns + cu Currency.«while»)) := by
      rintro tl rfl
      simp only [pack4, mopPair_def, bindT_unitT, NRest.consume_consume,
        BfsQSynth.drainLoop'_eq]
      refine le_trans (NRest.consume_mono (le_trans hdrain hmono) le_rfl) (le_of_eq ?_)
      rw [Sepref.consume_spec]
      exact congrArg (NRest.spec _) (funext fun _ => by ac_rfl)
    simp only [mopAset_def, mopAget_def, NRest.assert_pos (show src < p.1.length by omega),
      NRest.assert_pos (show 0 < q₀.length by omega), NRest.assert_pos halv,
      NRest.returnT_bindT, irIf_def, mopConstN_def,
      NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume]
    rw [show (if (decide (0 < alv[src]!)) = true
          then NRest.consume (NRest.returnT 1) (irUnit Currency.const)
          else NRest.consume (NRest.returnT 0) (irUnit Currency.const))
        = NRest.consume (NRest.returnT (if 0 < alv[src]! then 1 else 0))
            (irUnit Currency.const) from by
      by_cases hal : 0 < alv[src]!
      · rw [if_pos (by simp only [decide_eq_true_eq]; omega : (decide (0 < alv[src]!)) = true),
          if_pos hal]
      · rw [if_neg (by simp only [decide_eq_true_eq]; omega : ¬ (decide (0 < alv[src]!)) = true),
          if_neg hal],
      bindT_unitT]
    refine le_trans (NRest.consume_mono (NRest.consume_mono (hstep _ rfl) le_rfl) le_rfl)
      (le_of_eq ?_)
    rw [Sepref.consume_spec, Sepref.consume_spec]
    refine congrArg (NRest.spec _) (funext fun _ => ?_)
    simp only [E2, iter, liftACost_add, liftACost_nsmul, liftACost_cu, add_zero]
    ac_rfl
  simp only [BfsQSynth.bfsQS, mopPair_def, bindT_unitT, BfsQSynth.fillLoop'_eq]
  refine le_trans (NRest.consume_mono
    (le_trans (NRest.bindT_mono (fillLoop_le n (d + 1) n dist₀ 0 hdlen (by omega)
      (fun j hj => absurd hj (by omega))) fun _ => le_rfl)
      (Sepref.bindT_spec_le _ _ _ _ _ htail)) le_rfl) ?_
  rw [Sepref.consume_spec]
  refine Sepref.spec_mono (fun _ h => h) (fun _ _ => ?_)
  simp only [bfsBudget, bfsK, iter, liftACost_add, liftACost_nsmul, liftACost_cu, Nat.sub_zero]
  exact le_trans (cost_le_add _ (irUnit Currency.add + irUnit Currency.const))
    (le_of_eq (by ac_rfl))

/-! ## The greedy scan, priced -/

/-- What a turn pays whatever it does: the two reads, the three tests,
the branch's own re-assembly, the counter and the state's. -/
def scatC : ACost String ℕ :=
  cu Currency.aget + cu Currency.aget
    + cu Currency.ite + cu Currency.ite + cu Currency.ite
    + cu Currency.skip + cu Currency.skip + cu Currency.skip
    + cu Currency.add
    + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip

/-- …and what a turn that *picks* pays on top: the search's entry
store, the search, the sweep's entry store, the sweep, and the count. -/
def pickK : ACost String ℕ :=
  cu Currency.const + cu Currency.const + cu Currency.copy + cu Currency.skip
    + cu Currency.const + cu Currency.skip + cu Currency.«while» + cu Currency.add

def pickC (n ns : ℕ) : ACost String ℕ := bfsBudget n ns + n • iter markC + pickK

/-! ## `RamScatter.Progress`, over the abstract loop state

The baseline states its scan invariant over an `Imp.Env` — the count in
a cell, the exclusion bits in a function array. Here the same
disjunction is a statement about the loop state's own components, and
the machine has left it entirely (the six-conjuncts-to-one shrink the
fill loop showed, at an invariant with content). -/

def AProg (nn : ℕ) (G : SimpleGraph (Fin nn)) (M : ℕ → ℕ) (r t : ℕ) (X : Set (Fin nn))
    (p cnt : ℕ) (E : List ℕ) : Prop :=
  (cnt = t ∧ t ≤ (Lax3.ScatterSentences.greedySet (RamBfs.masked G M) r X).ncard) ∨
    (cnt < t ∧ cnt = (RamScatter.selBelow G M r X p).ncard ∧
      (∀ w, w < nn → E[w]! ≤ 1) ∧
      ∀ w, w < nn → (E[w]! = 0 ↔
        ∀ u, u < p → RamScatter.GSel G M r X u → ¬ RamBfs.WD G M r u w))

variable {nn ns r t : ℕ} {G : SimpleGraph (Fin nn)} {M Tab O T : ℕ → ℕ} {X : Set (Fin nn)}

theorem AProg.cnt_le {p cnt : ℕ} {E : List ℕ} (h : AProg nn G M r t X p cnt E) : cnt ≤ t := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- **A vertex the scan passes over changes nothing** —
`RamScatter.progress_succ_of_not` at the list. -/
theorem AProg_succ_of_not {p cnt : ℕ} {E : List ℕ} (hg : ¬ RamScatter.GSel G M r X p)
    (h : AProg nn G M r t X p cnt E) : AProg nn G M r t X (p + 1) cnt E := by
  rcases h with hB | ⟨h₁, h₂, hE1, hEiff⟩
  · exact Or.inl hB
  · refine Or.inr ⟨h₁, by rw [h₂, RamScatter.selBelow_succ_of_not hg], hE1, fun w hw => ?_⟩
    rw [hEiff w hw]
    refine ⟨fun hall u hu hgu => ?_, fun hall u hu hgu => hall u (by omega) hgu⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu' | rfl
    · exact hall u hu' hgu
    · exact absurd hgu hg

/-! ## The picking branch, bounded -/

theorem pickF_le (hcsr : RamBfs.CsrGraph G ns O T)
    (E D Q : List ℕ) (cnt sv : ℕ) (hsv : sv < nn)
    (hE : E.length = nn) (hD : D.length = nn) (hQ : Q.length = nn) :
    pickF nn r (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) ((E, D, Q, cnt, sv) : SSt)
      ≤ NRest.spec (fun z : PSt =>
            z.1.length = nn ∧ z.2.1.length = nn ∧ z.2.2.1.length = nn ∧ z.2.2.2 = cnt + 1 ∧
            (∀ w, w < nn → z.1[w]! = RamScatter.markVal r E[w]! z.2.1[w]!) ∧
            (∀ w, w < nn → (z.2.1[w]! ≤ r ↔ RamBfs.WD G M r sv w)))
          (fun _ => liftACost (pickC nn ns + (cu Currency.skip + cu Currency.skip
            + cu Currency.skip))) := by
  have hcsr' : Csr nn ns G (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) :=
    Lax3Proofs.Refine.BfsBridge.csr_of_csrGraph hcsr
  -- what the search leaves, and what the sweep then does with it
  have htail : ∀ st : St,
      (QPost nn r sv G (arrOf nn M) hsv st.1 ∧ st.2.1.length = nn) →
      (NRest.bindT mopZeroSw fun z => NRest.bindT (mopPair E z) fun p =>
        NRest.bindT (markLoop nn (r + 1) st.1 p) fun mr =>
          NRest.bindT (mopSucc cnt) fun c' => pack4' mr.1 st.1 st.2.1 c')
        ≤ NRest.spec (fun z : PSt =>
              z.1.length = nn ∧ z.2.1.length = nn ∧ z.2.2.1.length = nn ∧ z.2.2.2 = cnt + 1 ∧
              (∀ w, w < nn → z.1[w]! = RamScatter.markVal r E[w]! z.2.1[w]!) ∧
              (∀ w, w < nn → (z.2.1[w]! ≤ r ↔ RamBfs.WD G M r sv w)))
            (fun _ => liftACost (cu Currency.const + cu Currency.skip
              + (nn • iter markC + cu Currency.«while») + cu Currency.add
              + (cu Currency.skip + cu Currency.skip + cu Currency.skip))) := by
    rintro st ⟨⟨hdlen, hdspec⟩, hqlen⟩
    -- the distances the search decided, in the driver stack's vocabulary
    have hwd : ∀ w, w < nn → (st.1[w]! ≤ r ↔ RamBfs.WD G M r sv w) := by
      intro w hw
      rw [RamBfs.wd_iff_withinDist hsv hw]
      exact (hdspec ⟨w, hw⟩ r le_rfl).trans Lax3Proofs.Refine.BfsBridge.wd_iff_withinDist
    -- the sweep
    have hmark := markLoop_le nn (r + 1) st.1 E (le_of_eq hdlen.symm) nn E 0 hE
      (by omega) (by omega) (fun j hj => absurd hj (Nat.not_lt_zero j)) (fun _ _ _ => rfl)
    rw [Nat.sub_zero] at hmark
    have hfin : ∀ mr : List ℕ × ℕ,
        (mr.1.length = nn ∧ mr.2 = nn ∧ ∀ j, j < nn → mr.1[j]! = mkVal (r + 1) E[j]! st.1[j]!) →
        (NRest.bindT (mopSucc cnt) fun c' => pack4' mr.1 st.1 st.2.1 c')
          ≤ NRest.spec (fun z : PSt =>
              z.1.length = nn ∧ z.2.1.length = nn ∧ z.2.2.1.length = nn ∧ z.2.2.2 = cnt + 1 ∧
              (∀ w, w < nn → z.1[w]! = RamScatter.markVal r E[w]! z.2.1[w]!) ∧
              (∀ w, w < nn → (z.2.1[w]! ≤ r ↔ RamBfs.WD G M r sv w)))
            (fun _ => liftACost (cu Currency.add
              + (cu Currency.skip + cu Currency.skip + cu Currency.skip))) := by
      rintro mr ⟨hmlen, -, hmval⟩
      simp only [mopSucc_eq, mopBinop_def, Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add,
        bindT_unitT, pack4', mopPair_def, NRest.consume_consume]
      refine consume_returnT_le_spec
        ⟨hmlen, hdlen, hqlen, rfl, fun w hw => by
          rw [hmval w hw, mkVal_eq_markVal], hwd⟩ ?_
      simp only [liftACost_add, liftACost_cu]
      exact le_of_eq (by ac_rfl)
    simp only [mopZeroSw_eq, mopConstN_def, bindT_unitT, mopPair_def, NRest.consume_consume]
    refine le_trans (NRest.consume_mono
      (le_trans (NRest.bindT_mono hmark fun _ => le_rfl)
        (bindT_spec_le _ _ _ _ _ hfin)) le_rfl) (le_of_eq ?_)
    rw [Sepref.consume_spec]
    refine congrArg (NRest.spec _) (funext fun _ => ?_)
    simp only [liftACost_add, liftACost_cu]
    ac_rfl
  -- the search itself
  simp only [pickF, mopZeroI_eq, mopZeroHd_eq, mopSrcOf_eq, mopConstN_def, mopCopy_def,
    bindT_unitT, mopBfsAt_eq, NRest.assert_pos (show True ∧ True from ⟨trivial, trivial⟩),
    NRest.returnT_bindT, NRest.consume_consume]
  refine le_trans (NRest.consume_mono
    (le_trans (NRest.bindT_mono (bfsQS_correct' hcsr' hsv hD hQ) fun _ => le_rfl)
      (bindT_spec_le _ _ _ _ _ htail)) le_rfl) (le_of_eq ?_)
  rw [Sepref.consume_spec]
  refine congrArg (NRest.spec _) (funext fun _ => ?_)
  simp only [pickC, pickK, liftACost_add, liftACost_cu, liftACost_nsmul]
  ac_rfl

/-! ## The arena mathematics of one turn

`RamScatter`'s own — `GSel`/`selBelow` and the counting lemmas are
consumed, never restated. -/

theorem not_gsel_of_pass {p cnt : ℕ} {E : List ℕ} (hp : p < nn)
    (hTab : ∀ v : Fin nn, Tab (v : ℕ) ≠ 0 ↔ v ∈ X)
    (hP : AProg nn G M r t X p cnt E) (hlt : cnt < t)
    (h : Tab p = 0 ∨ E[p]! ≠ 0) : ¬ RamScatter.GSel G M r X p := by
  obtain ⟨-, -, -, hEiff⟩ : cnt < t ∧ cnt = (RamScatter.selBelow G M r X p).ncard ∧
      (∀ w, w < nn → E[w]! ≤ 1) ∧
      (∀ w, w < nn → (E[w]! = 0 ↔
        ∀ u, u < p → RamScatter.GSel G M r X u → ¬ RamBfs.WD G M r u w)) := by
    rcases hP with ⟨h', -⟩ | h'
    · omega
    · exact h'
  intro hg
  obtain ⟨hX, hfar⟩ := (RamScatter.gsel_iff hp).1 hg
  rcases h with h | h
  · exact (hTab ⟨p, hp⟩).2 hX h
  · exact h ((hEiff p hp).2 hfar)

theorem AProg_keep {p cnt : ℕ} {E : List ℕ} (hp : p < nn)
    (hTab : ∀ v : Fin nn, Tab (v : ℕ) ≠ 0 ↔ v ∈ X)
    (hP : AProg nn G M r t X p cnt E)
    (h : ¬ (cnt < t) ∨ Tab p = 0 ∨ E[p]! ≠ 0) :
    AProg nn G M r t X (p + 1) cnt E := by
  by_cases hlt : cnt < t
  · rcases h with h | h
    · exact absurd hlt h
    · exact AProg_succ_of_not (not_gsel_of_pass hp hTab hP hlt h) hP
  · rcases hP with hB | ⟨h', -⟩
    · exact Or.inl hB
    · exact absurd h' hlt

/-- **What a turn that picks establishes.** `RamScatter.step_run`'s
mathematics, at the loop state: the search decided the radius, so the
new bits are exactly the recursion's next clause. -/
theorem AProg_pick {p cnt : ℕ} {E E' D' : List ℕ} (hp : p < nn)
    (hTab : ∀ v : Fin nn, Tab (v : ℕ) ≠ 0 ↔ v ∈ X)
    (hP : AProg nn G M r t X p cnt E) (hlt : cnt < t)
    (htab : Tab p ≠ 0) (hex : E[p]! = 0)
    (hwd : ∀ w, w < nn → (D'[w]! ≤ r ↔ RamBfs.WD G M r p w))
    (hEnew : ∀ w, w < nn → E'[w]! = RamScatter.markVal r E[w]! D'[w]!) :
    AProg nn G M r t X (p + 1) (cnt + 1) E' := by
  obtain ⟨-, hcnteq, -, hEiff⟩ : cnt < t ∧ cnt = (RamScatter.selBelow G M r X p).ncard ∧
      (∀ w, w < nn → E[w]! ≤ 1) ∧
      (∀ w, w < nn → (E[w]! = 0 ↔
        ∀ u, u < p → RamScatter.GSel G M r X u → ¬ RamBfs.WD G M r u w)) := by
    rcases hP with ⟨h', -⟩ | h'
    · omega
    · exact h'
  have hgsel : RamScatter.GSel G M r X p :=
    (RamScatter.gsel_iff hp).2 ⟨(hTab ⟨p, hp⟩).1 htab, (hEiff p hp).1 hex⟩
  have hE'iff : ∀ w, w < nn → (RamScatter.markVal r E[w]! D'[w]! = 0 ↔
      ∀ u, u < p + 1 → RamScatter.GSel G M r X u → ¬ RamBfs.WD G M r u w) := by
    intro w hw
    rw [RamScatter.markVal_eq_zero_iff, hEiff w hw]
    constructor
    · rintro ⟨hall, hgt⟩ u hu hgu
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu' | rfl
      · exact hall u hu' hgu
      · exact fun hwd' => absurd ((hwd w hw).2 hwd') (by omega)
    · intro hall
      refine ⟨fun u hu hgu => hall u (by omega) hgu, ?_⟩
      by_contra hcon
      exact hall p (by omega) hgsel ((hwd w hw).1 (by omega))
  have hncard : cnt + 1 = (RamScatter.selBelow G M r X (p + 1)).ncard := by
    rw [RamScatter.ncard_selBelow_succ_of_gsel hp hgsel, hcnteq]
  have hlei : cnt + 1 ≤ (Lax3.ScatterSentences.greedySet (RamBfs.masked G M) r X).ncard := by
    rw [hncard]; exact RamScatter.ncard_selBelow_le
  rcases Nat.lt_or_ge (cnt + 1) t with h | h
  · exact Or.inr ⟨h, hncard, fun w hw => by
      rw [hEnew w hw]; exact RamScatter.markVal_le_one .., fun w hw => by
      rw [hEnew w hw]; exact hE'iff w hw⟩
  · exact Or.inl ⟨by omega, by omega⟩

/-! ## One turn of the scan, bounded -/

theorem scatF_le_keep (hTab : ∀ v : Fin nn, Tab (v : ℕ) ≠ 0 ↔ v ∈ X)
    (E D Q : List ℕ) (cnt sv : ℕ) (hsv : sv < nn)
    (hE : E.length = nn) (hD : D.length = nn) (hQ : Q.length = nn)
    (hP : AProg nn G M r t X sv cnt E)
    (hno : ¬ (cnt < t) ∨ Tab sv = 0 ∨ E[sv]! ≠ 0) :
    scatF nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
        ((E, D, Q, cnt, sv) : SSt)
      ≤ NRest.spec (fun s' : SSt => s'.1.length = nn ∧ s'.2.1.length = nn ∧
            s'.2.2.1.length = nn ∧ s'.2.2.2.2 = sv + 1 ∧ s'.2.2.2.1 = cnt ∧
            AProg nn G M r t X (sv + 1) s'.2.2.2.1 s'.1)
          (fun _ => liftACost scatC) := by
  have hpost : AProg nn G M r t X (sv + 1) cnt E := AProg_keep hsv hTab hP hno
  have htabval : (arrOf nn Tab)[sv]! = Tab sv :=
    Lax3Proofs.Refine.BfsBridge.getElem!_arrOf Tab hsv
  have hEsv : sv < E.length := by omega
  have htabsv : sv < (arrOf nn Tab).length := by rw [length_arrOf]; exact hsv
  by_cases hlt : cnt < t
  · have hg1 : decide (cnt < t) = true := by simp [hlt]
    by_cases htb : 0 < Tab sv
    · have hex : E[sv]! ≠ 0 := by
        rcases hno with h | h | h
        · exact absurd hlt h
        · omega
        · exact h
      have hg2 : decide (0 < (arrOf nn Tab)[sv]!) = true := by rw [htabval]; simp [htb]
      have hg3 : decide (E[sv]! = 0) = false := by
        simp only [decide_eq_false_iff_not]; exact hex
      simp only [scatF, mopAget_def, NRest.assert_pos htabsv, NRest.assert_pos hEsv,
        NRest.returnT_bindT, bindT_unitT, hg1, hg2, hg3, irIf_true, irIf_false,
        NRest.bindT_consume NRest.addSupContinuousB_acost, pack4', pack5, mopPair_def,
        mopSucc_eq, mopBinop_def, Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add,
        NRest.consume_consume]
      refine consume_returnT_le_spec ⟨hE, hD, hQ, rfl, rfl, hpost⟩ (le_of_eq ?_)
      simp only [scatC, liftACost_add, liftACost_cu]
      ac_rfl
    · have hg2 : decide (0 < (arrOf nn Tab)[sv]!) = false := by rw [htabval]; simp; omega
      simp only [scatF, mopAget_def, NRest.assert_pos htabsv, NRest.assert_pos hEsv,
        NRest.returnT_bindT, bindT_unitT, hg1, hg2, irIf_true, irIf_false,
        NRest.bindT_consume NRest.addSupContinuousB_acost, pack4', pack5, mopPair_def,
        mopSucc_eq, mopBinop_def, Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add,
        NRest.consume_consume]
      refine consume_returnT_le_spec ⟨hE, hD, hQ, rfl, rfl, hpost⟩
        (le_trans (cost_le_add _ (irUnit Currency.ite)) (le_of_eq ?_))
      simp only [scatC, liftACost_add, liftACost_cu]
      ac_rfl
  · have hg1 : decide (cnt < t) = false := by simp [hlt]
    simp only [scatF, mopAget_def, NRest.assert_pos htabsv, NRest.assert_pos hEsv,
      NRest.returnT_bindT, bindT_unitT, hg1, irIf_false,
      NRest.bindT_consume NRest.addSupContinuousB_acost, pack4', pack5, mopPair_def,
      mopSucc_eq, mopBinop_def, Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add,
      NRest.consume_consume]
    refine consume_returnT_le_spec ⟨hE, hD, hQ, rfl, rfl, hpost⟩
      (le_trans (cost_le_add _ (irUnit Currency.ite + irUnit Currency.ite)) (le_of_eq ?_))
    simp only [scatC, liftACost_add, liftACost_cu]
    ac_rfl

theorem scatF_le_pick (hcsr : RamBfs.CsrGraph G ns O T)
    (hTab : ∀ v : Fin nn, Tab (v : ℕ) ≠ 0 ↔ v ∈ X)
    (E D Q : List ℕ) (cnt sv : ℕ) (hsv : sv < nn)
    (hE : E.length = nn) (hD : D.length = nn) (hQ : Q.length = nn)
    (hP : AProg nn G M r t X sv cnt E)
    (hlt : cnt < t) (htb : Tab sv ≠ 0) (hex : E[sv]! = 0) :
    scatF nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
        ((E, D, Q, cnt, sv) : SSt)
      ≤ NRest.spec (fun s' : SSt => s'.1.length = nn ∧ s'.2.1.length = nn ∧
            s'.2.2.1.length = nn ∧ s'.2.2.2.2 = sv + 1 ∧ s'.2.2.2.1 = cnt + 1 ∧
            AProg nn G M r t X (sv + 1) s'.2.2.2.1 s'.1)
          (fun _ => liftACost (scatC + pickC nn ns)) := by
  have htabval : (arrOf nn Tab)[sv]! = Tab sv :=
    Lax3Proofs.Refine.BfsBridge.getElem!_arrOf Tab hsv
  have hEsv : sv < E.length := by omega
  have htabsv : sv < (arrOf nn Tab).length := by rw [length_arrOf]; exact hsv
  have hg1 : decide (cnt < t) = true := by simp [hlt]
  have hg2 : decide (0 < (arrOf nn Tab)[sv]!) = true := by rw [htabval]; simp; omega
  have hg3 : decide (E[sv]! = 0) = true := by
    simp only [decide_eq_true_eq]; exact hex
  have hcont : ∀ z : PSt,
      (z.1.length = nn ∧ z.2.1.length = nn ∧ z.2.2.1.length = nn ∧ z.2.2.2 = cnt + 1 ∧
        (∀ w, w < nn → z.1[w]! = RamScatter.markVal r E[w]! z.2.1[w]!) ∧
        (∀ w, w < nn → (z.2.1[w]! ≤ r ↔ RamBfs.WD G M r sv w))) →
      (NRest.bindT (mopSucc sv) fun v' => pack5 z.1 z.2.1 z.2.2.1 z.2.2.2 v')
        ≤ NRest.spec (fun s' : SSt => s'.1.length = nn ∧ s'.2.1.length = nn ∧
              s'.2.2.1.length = nn ∧ s'.2.2.2.2 = sv + 1 ∧ s'.2.2.2.1 = cnt + 1 ∧
              AProg nn G M r t X (sv + 1) s'.2.2.2.1 s'.1)
            (fun _ => liftACost (cu Currency.add + cu Currency.skip + cu Currency.skip
              + cu Currency.skip + cu Currency.skip)) := by
    rintro z ⟨hz1, hz2, hz3, hz4, hz5, hz6⟩
    simp only [mopSucc_eq, mopBinop_def, Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add,
      bindT_unitT, pack5, mopPair_def, NRest.consume_consume]
    refine consume_returnT_le_spec ⟨hz1, hz2, hz3, rfl, hz4, ?_⟩ (le_of_eq ?_)
    · rw [hz4]
      exact AProg_pick hsv hTab hP hlt htb hex hz6 hz5
    · simp only [liftACost_add, liftACost_cu]
      ac_rfl
  simp only [scatF, mopAget_def, NRest.assert_pos htabsv, NRest.assert_pos hEsv,
    NRest.returnT_bindT, bindT_unitT, hg1, hg2, hg3, irIf_true,
    NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume]
  refine le_trans (NRest.consume_mono
    (le_trans (NRest.bindT_mono (pickF_le hcsr E D Q cnt sv hsv hE hD hQ) fun _ => le_rfl)
      (bindT_spec_le _ _ _ _ _ hcont)) le_rfl) (le_of_eq ?_)
  rw [Sepref.consume_spec]
  refine congrArg (NRest.spec _) (funext fun _ => ?_)
  simp only [scatC, liftACost_add, liftACost_cu]
  ac_rfl

/-! ## The scan

The energy is two-currency, as the baseline's `ScatterPot` is: one
pick's worth per pick still allowed, one turn's worth per vertex not yet
reached. -/

theorem scatLoop_le (hcsr : RamBfs.CsrGraph G ns O T)
    (hTab : ∀ v : Fin nn, Tab (v : ℕ) ≠ 0 ↔ v ∈ X) :
    ∀ (fuel : ℕ) (E D Q : List ℕ) (cnt sv : ℕ), E.length = nn → D.length = nn →
      Q.length = nn → sv ≤ nn → nn - sv ≤ fuel → AProg nn G M r t X sv cnt E →
      scatLoop nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
          ((E, D, Q, cnt, sv) : SSt)
        ≤ NRest.spec (fun s' : SSt => s'.2.2.2.2 = nn ∧ AProg nn G M r t X nn s'.2.2.2.1 s'.1)
            (fun _ => liftACost ((t - cnt) • pickC nn ns + (nn - sv) • iter scatC
              + cu Currency.«while»)) := by
  have exit : ∀ (E D Q : List ℕ) (cnt sv : ℕ), sv ≤ nn → nn ≤ sv →
      AProg nn G M r t X sv cnt E →
      scatLoop nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
          ((E, D, Q, cnt, sv) : SSt)
        ≤ NRest.spec (fun s' : SSt => s'.2.2.2.2 = nn ∧ AProg nn G M r t X nn s'.2.2.2.1 s'.1)
            (fun _ => liftACost ((t - cnt) • pickC nn ns + (nn - sv) • iter scatC
              + cu Currency.«while»)) := by
    intro E D Q cnt sv hle hge hP
    have hb : scatBf nn ((E, D, Q, cnt, sv) : SSt) = false := by
      simp only [scatBf, decide_eq_false_iff_not]
      show ¬ sv < nn
      omega
    simp only [scatLoop, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨show sv = nn by omega, ?_⟩ ?_
    · exact (show sv = nn by omega) ▸ hP
    · rw [show nn - sv = 0 by omega, zero_nsmul, add_zero, liftACost_add, liftACost_cu,
        add_comm]
      exact cost_le_add _ _
  intro fuel
  induction fuel with
  | zero => intro E D Q cnt sv hE hD hQ hle hf hP; exact exit E D Q cnt sv hle (by omega) hP
  | succ fuel ih =>
    intro E D Q cnt sv hE hD hQ hle hf hP
    by_cases hb : sv < nn
    · have hbt : scatBf nn ((E, D, Q, cnt, sv) : SSt) = true := by
        simp only [scatBf, decide_eq_true_eq]; exact hb
      have hIs : scatBf nn ((E, D, Q, cnt, sv) : SSt) = true →
          scatP nn (arrOf nn Tab) ((E, D, Q, cnt, sv) : SSt) :=
        fun _ => ⟨hb, by rw [length_arrOf], show nn ≤ E.length by omega⟩
      by_cases hpick : cnt < t ∧ Tab sv ≠ 0 ∧ E[sv]! = 0
      · obtain ⟨hlt, htb, hex⟩ := hpick
        have hcont : ∀ s' : SSt, (s'.1.length = nn ∧ s'.2.1.length = nn ∧
            s'.2.2.1.length = nn ∧ s'.2.2.2.2 = sv + 1 ∧ s'.2.2.2.1 = cnt + 1 ∧
            AProg nn G M r t X (sv + 1) s'.2.2.2.1 s'.1) →
            scatLoop nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab) s'
              ≤ NRest.spec
                  (fun s'' : SSt => s''.2.2.2.2 = nn ∧ AProg nn G M r t X nn s''.2.2.2.1 s''.1)
                  (fun _ => liftACost ((t - (cnt + 1)) • pickC nn ns
                    + (nn - (sv + 1)) • iter scatC + cu Currency.«while»)) := by
          rintro ⟨E', D', Q', c', v'⟩ ⟨h1, h2, h3, h4, h5, h6⟩
          simp only at h1 h2 h3 h4 h5 h6
          subst h4; subst h5
          exact ih E' D' Q' (cnt + 1) (sv + 1) h1 h2 h3 (by omega) (by omega) h6
        have hcost : irUnit Currency.«while»
            + (liftACost (scatC + pickC nn ns)
              + liftACost ((t - (cnt + 1)) • pickC nn ns + (nn - (sv + 1)) • iter scatC
                + cu Currency.«while»))
            = liftACost ((t - cnt) • pickC nn ns + (nn - sv) • iter scatC
                + cu Currency.«while») := by
          rw [show nn - sv = (nn - (sv + 1)) + 1 by omega,
            show t - cnt = (t - (cnt + 1)) + 1 by omega, succ_nsmul, succ_nsmul]
          simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
          ac_rfl
        calc scatLoop nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
                ((E, D, Q, cnt, sv) : SSt)
            = NRest.consume (NRest.bindT
                (scatF nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
                  ((E, D, Q, cnt, sv) : SSt))
                fun s' => scatLoop nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M)
                  (arrOf nn Tab) s') (irUnit Currency.«while») := by
              simp only [scatLoop]; rw [irWhileIT_of_true hIs hbt]
          _ ≤ NRest.consume (NRest.spec _ (fun _ => liftACost (scatC + pickC nn ns)
                + liftACost ((t - (cnt + 1)) • pickC nn ns + (nn - (sv + 1)) • iter scatC
                  + cu Currency.«while»))) (irUnit Currency.«while») :=
              NRest.consume_mono (le_trans (NRest.bindT_mono
                (scatF_le_pick hcsr hTab E D Q cnt sv hb hE hD hQ hP hlt htb hex)
                fun _ => le_rfl) (bindT_spec_le _ _ _ _ _ hcont)) le_rfl
          _ = _ := by rw [Sepref.consume_spec, ← hcost]
      · have hno : ¬ (cnt < t) ∨ Tab sv = 0 ∨ E[sv]! ≠ 0 := by
          by_cases h1 : cnt < t
          · by_cases h2 : Tab sv = 0
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr fun hz => hpick ⟨h1, h2, hz⟩)
          · exact Or.inl h1
        have hcont : ∀ s' : SSt, (s'.1.length = nn ∧ s'.2.1.length = nn ∧
            s'.2.2.1.length = nn ∧ s'.2.2.2.2 = sv + 1 ∧ s'.2.2.2.1 = cnt ∧
            AProg nn G M r t X (sv + 1) s'.2.2.2.1 s'.1) →
            scatLoop nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab) s'
              ≤ NRest.spec
                  (fun s'' : SSt => s''.2.2.2.2 = nn ∧ AProg nn G M r t X nn s''.2.2.2.1 s''.1)
                  (fun _ => liftACost ((t - cnt) • pickC nn ns
                    + (nn - (sv + 1)) • iter scatC + cu Currency.«while»)) := by
          rintro ⟨E', D', Q', c', v'⟩ ⟨h1, h2, h3, h4, h5, h6⟩
          simp only at h1 h2 h3 h4 h5 h6
          subst h4
          rw [h5]
          exact ih E' D' Q' cnt (sv + 1) h1 h2 h3 (by omega) (by omega) (h5 ▸ h6)
        have hcost : irUnit Currency.«while»
            + (liftACost scatC
              + liftACost ((t - cnt) • pickC nn ns + (nn - (sv + 1)) • iter scatC
                + cu Currency.«while»))
            = liftACost ((t - cnt) • pickC nn ns + (nn - sv) • iter scatC
                + cu Currency.«while») := by
          rw [show nn - sv = (nn - (sv + 1)) + 1 by omega, succ_nsmul]
          simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
          ac_rfl
        calc scatLoop nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
                ((E, D, Q, cnt, sv) : SSt)
            = NRest.consume (NRest.bindT
                (scatF nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
                  ((E, D, Q, cnt, sv) : SSt))
                fun s' => scatLoop nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M)
                  (arrOf nn Tab) s') (irUnit Currency.«while») := by
              simp only [scatLoop]; rw [irWhileIT_of_true hIs hbt]
          _ ≤ NRest.consume (NRest.spec _ (fun _ => liftACost scatC
                + liftACost ((t - cnt) • pickC nn ns + (nn - (sv + 1)) • iter scatC
                  + cu Currency.«while»))) (irUnit Currency.«while») :=
              NRest.consume_mono (le_trans (NRest.bindT_mono
                (scatF_le_keep hTab E D Q cnt sv hb hE hD hQ hP hno)
                fun _ => le_rfl) (bindT_spec_le _ _ _ _ _ hcont)) le_rfl
          _ = _ := by rw [Sepref.consume_spec, ← hcost]
    · exact exit E D Q cnt sv hle (by omega) hP

/-! ## The exports -/

section Export

theorem AProg_final {cnt : ℕ} {E : List ℕ} (h : AProg nn G M r t X nn cnt E) :
    cnt ≤ t ∧ ((t ≤ (Lax3.ScatterSentences.greedySet (RamBfs.masked G M) r X).ncard) ↔
      ¬ cnt < t) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, -, -⟩
  · exact ⟨by omega, ⟨fun _ => by omega, fun _ => h2⟩⟩
  · rw [RamScatter.selBelow_all] at h2
    exact ⟨by omega, ⟨fun hc => by omega, fun hc => by omega⟩⟩

/-! ### The caller's store, ownership and bound -/

def scatState (n d t : ℕ) (off tgt alv tab exc₀ dist₀ q₀ : List ℕ) : Ir.State :=
  Ir.State.ofPairs
    [("cnt", 0), ("sv", 0), ("n", n), ("sent", d + 1), ("d", d), ("t", t), ("one", 1),
      ("zero", 0), ("sctb", 0), ("scex", 0), ("src", 0), ("i", 0), ("head", 0), ("sw", 0),
      ("a", 0), ("tl", 0), ("v", 0), ("dv", 0), ("dv1", 0), ("k0", 0), ("v1", 0),
      ("kend", 0), ("u", 0), ("au", 0), ("du", 0)]
    [("exc", exc₀), ("dist", dist₀), ("q", q₀), ("off", off), ("tgt", tgt), ("alv", alv),
      ("tab", tab)]

def scatPre (n d t : ℕ) (off tgt alv tab exc₀ dist₀ q₀ : List ℕ) : Assn :=
  hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (exc₀, dist₀, q₀, 0, 0) ("exc", "dist", "q", "cnt", "sv") ∗
    hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
    hnCtxt arrayAssn alv "alv" ∗ hnCtxt arrayAssn tab "tab" ∗
    hnCtxt natAssn n "n" ∗ hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
    hnCtxt natAssn t "t" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
    junkCell "sctb" ∗ junkCell "scex" ∗
    junkCell "src" ∗ junkCell "i" ∗ junkCell "head" ∗ junkCell "sw" ∗
    junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
    junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
    junkCell "du"

def scatFrame (n d t : ℕ) (off tgt alv tab : List ℕ) : Assn :=
  hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
    hnCtxt arrayAssn alv "alv" ∗ hnCtxt arrayAssn tab "tab" ∗
    hnCtxt natAssn n "n" ∗ hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
    hnCtxt natAssn t "t" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
    junkCell "sctb" ∗ junkCell "scex" ∗
    junkCell "src" ∗ junkCell "i" ∗ junkCell "head" ∗ junkCell "sw" ∗
    junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
    junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
    junkCell "du"

theorem scatSynth' (n d t : ℕ) (off tgt alv tab exc₀ dist₀ q₀ : List ℕ) :
    hnRefine (scatPre n d t off tgt alv tab exc₀ dist₀ q₀) scatSynth_impl
      (scatFrame n d t off tgt alv tab) ("exc", "dist", "q", "cnt", "sv")
      (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (scatLoop n d t off tgt alv tab (exc₀, dist₀, q₀, 0, 0)) :=
  scatSynth n d t off tgt alv tab exc₀ dist₀ q₀

def scatHole (n d t : ℕ) (off tgt alv tab exc₀ dist₀ q₀ : List ℕ) : Assn :=
  EXACT
    ((vcells (scatState n d t off tgt alv tab exc₀ dist₀ q₀)
        |>.erase "cnt" |>.erase "sv" |>.erase "n" |>.erase "sent" |>.erase "d"
        |>.erase "t" |>.erase "one" |>.erase "zero" |>.erase "sctb" |>.erase "scex"
        |>.erase "src" |>.erase "i" |>.erase "head" |>.erase "sw" |>.erase "a"
        |>.erase "tl" |>.erase "v" |>.erase "dv" |>.erase "dv1" |>.erase "k0"
        |>.erase "v1" |>.erase "kend" |>.erase "u" |>.erase "au" |>.erase "du",
      acells (scatState n d t off tgt alv tab exc₀ dist₀ q₀)
        |>.erase "exc" |>.erase "dist" |>.erase "q" |>.erase "off" |>.erase "tgt"
        |>.erase "alv" |>.erase "tab",
      hcells (scatState n d t off tgt alv tab exc₀ dist₀ q₀)), 0)

theorem scat_state_holds (n d t : ℕ) (off tgt alv tab exc₀ dist₀ q₀ : List ℕ) :
    irSTATE (scatPre n d t off tgt alv tab exc₀ dist₀ q₀
        ∗ scatHole n d t off tgt alv tab exc₀ dist₀ q₀)
      (scatState n d t off tgt alv tab exc₀ dist₀ q₀, 0) := by
  show (scatPre n d t off tgt alv tab exc₀ dist₀ q₀
      ∗ scatHole n d t off tgt alv tab exc₀ dist₀ q₀)
    ((vcells (scatState n d t off tgt alv tab exc₀ dist₀ q₀),
      acells (scatState n d t off tgt alv tab exc₀ dist₀ q₀),
      hcells (scatState n d t off tgt alv tab exc₀ dist₀ q₀)), 0)
  simp only [scatPre, hnCtxt, prodAssn, natAssn_def, arrayAssn_def, sepConj_assoc]
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  iterate 16
    rw [junkCell_def, sepEx_sepConj]
    refine ⟨0, Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩⟩
  rw [junkCell_def, sepEx_sepConj]
  exact ⟨0, Ir.ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩⟩

theorem scatState_bound {B n d t : ℕ} {off tgt alv tab exc₀ dist₀ q₀ : List ℕ}
    (hnB : n < B) (h1B : 1 < B) (hdB : d + 1 < B) (htB : t < B)
    (hexc : ∀ w ∈ exc₀, w < B) (hdist : ∀ w ∈ dist₀, w < B) (hq : ∀ w ∈ q₀, w < B)
    (hoff : ∀ w ∈ off, w < B) (htgt : ∀ w ∈ tgt, w < B) (halv : ∀ w ∈ alv, w < B)
    (htab : ∀ w ∈ tab, w < B) :
    Ir.StateBound B (scatState n d t off tgt alv tab exc₀ dist₀ q₀) := by
  refine Codegen.stateBound_ofPairs ?_ ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa using by omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-! ### The cost, computed -/

/-- **The scan's cost**: `(94·n + 40·ns + 50)·t + 33·n + 4` IMP+ time
units. -/
def scatK (n ns t : ℕ) : ℕ := (94 * n + 40 * ns + 50) * t + 33 * n + 4

theorem cash_pickC (n ns : ℕ) : Codegen.cash (pickC n ns) = 94 * n + 40 * ns + 50 := by
  rw [pickC, Codegen.cash_add, Codegen.cash_add, BfsQSynth.cash_bfsBudget, BfsQSynth.cash_nsmul,
    show Codegen.cash (iter markC) = 38 from by decide +kernel,
    show Codegen.cash pickK = 18 from by decide +kernel]
  ring

theorem ecash_scatTotal (n ns t : ℕ) :
    ecash (liftACost (t • pickC n ns + n • iter scatC + cu Currency.«while»))
      = (scatK n ns t : ℕ∞) := by
  rw [BfsQSynth.ecash_liftACost, Codegen.cash_add, Codegen.cash_add, BfsQSynth.cash_nsmul,
    BfsQSynth.cash_nsmul, cash_pickC,
    show Codegen.cash (iter scatC) = 33 from by decide +kernel,
    show Codegen.cash (cu Currency.«while») = 4 from by decide +kernel, scatK]
  push_cast
  ring

/-! ### The bounds pass: the one named debt (R2A/D-l)

Every other pass of this file carries its `BRefine` derivation. The scan
cannot: its body contains `BfsQSynth.bfsQSynth_impl` whole, and the
tower's bound for that program exists only as
`BfsQSynth.bfsQ_bpre` — an `Ir.bpre` at *one pinned store* with the
trivial postcondition. A `BRefine`-composed derivation has to pass an
*assertion* through the search (`bpre B (bfs) (bpre B (sweep) Q)`), and
`bpre` is a statement about every run, not the one `hnRefine` exhibits,
so the search's own bounds pass has to be re-run in assertion form. That
is `Examples/BfsQSynth.lean` §12 again — 560 lines — and it is a
satellite of its own, not a step of this one.

So the debt is *named*, not hidden: it is exactly the search's bounds
pass lifted to the scan's store, it is a hypothesis of every export
below, and nothing else in this file depends on it. -/

def ScanBounded (B n d t : ℕ) (off tgt alv tab exc₀ dist₀ q₀ : List ℕ) : Prop :=
  Ir.bpre B scatSynth_impl (fun _ => True) (scatState n d t off tgt alv tab exc₀ dist₀ q₀)

/-! ### The cashing chain at one initial store -/

theorem scan_spec_at {B : ℕ} (hcsr : RamBfs.CsrGraph G ns O T)
    (hTab : ∀ v : Fin nn, Tab (v : ℕ) ≠ 0 ↔ v ∈ X)
    (exc₀ dist₀ q₀ : List ℕ)
    (hnB : nn < B) (h1B : 1 < B) (hrB : r + 1 < B) (htB : t < B)
    (hexcB : ∀ w ∈ exc₀, w < B) (hdistB : ∀ w ∈ dist₀, w < B) (hqB : ∀ w ∈ q₀, w < B)
    (hoffB : ∀ z, z < nn + 1 → O z < B) (htgtB : ∀ z, z < ns → T z < B)
    (hMB : ∀ z, z < nn → M z < B) (hTabB : ∀ z, z < nn → Tab z < B)
    (hElen : exc₀.length = nn) (hDlen : dist₀.length = nn) (hQlen : q₀.length = nn)
    (hzero : ∀ j, j < nn → exc₀[j]! = 0)
    (hdebt : ScanBounded B nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M)
      (arrOf nn Tab) exc₀ dist₀ q₀) :
    Lax13Proofs.Reasoning.Spec B
      (agree (scatState nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
        exc₀ dist₀ q₀))
      (embed scatSynth_impl)
      (fun _ σ' => σ'.vars "cnt" ≤ t ∧
        ((t ≤ (Lax3.ScatterSentences.greedySet (RamBfs.masked G M) r X).ncard) ↔
          ¬ σ'.vars "cnt" < t))
      (scatK nn ns t) := by
  have hP0 : AProg nn G M r t X 0 0 exc₀ := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact Or.inl ⟨rfl, by omega⟩
    · refine Or.inr ⟨ht, by rw [RamScatter.selBelow_zero]; simp, fun w hw => by
        rw [hzero w hw]; omega, fun w hw => ⟨fun _ u hu => absurd hu (Nat.not_lt_zero u),
          fun _ => hzero w hw⟩⟩
  have hle := scatLoop_le (X := X) hcsr hTab nn exc₀ dist₀ q₀ 0 0 hElen hDlen hQlen
    (by omega) (by omega) hP0
  rw [Nat.sub_zero, Nat.sub_zero] at hle
  have hSB := scatState_bound (B := B) (n := nn) (d := r) (t := t) hnB h1B hrB htB
    hexcB hdistB hqB (Lax3Proofs.Refine.BfsBridge.mem_arrOf_lt hoffB)
    (Lax3Proofs.Refine.BfsBridge.mem_arrOf_lt htgtB)
    (Lax3Proofs.Refine.BfsBridge.mem_arrOf_lt hMB)
    (Lax3Proofs.Refine.BfsBridge.mem_arrOf_lt hTabB)
  have hspec := spec_of_hnRefine
    (Φ := fun s' : SSt => s'.2.2.2.2 = nn ∧ AProg nn G M r t X nn s'.2.2.2.1 s'.1)
    (Q := fun (ra : SSt) σ' => σ'.vars "cnt" = ra.2.2.2.1)
    (scatSynth' nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
      exc₀ dist₀ q₀) hle
    (scat_state_holds nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
      exc₀ dist₀ q₀) hSB
    (exists_bigStepB_of_hnRefine
      (scatSynth' nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
        exc₀ dist₀ q₀) hle
      (scat_state_holds nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
        exc₀ dist₀ q₀) hdebt)
    (le_of_eq (ecash_scatTotal nn ns t)) ?_
  · refine hspec.post ?_
    rintro σ σ' - ⟨ra, ⟨-, hP⟩, hcnt⟩
    obtain ⟨h1, h2⟩ := AProg_final hP
    rw [hcnt]
    exact ⟨h1, h2⟩
  · intro ra s' cr σ' hΦ hst hag
    have he : (scatFrame nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab) ∗
        (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn) ra
          ("exc", "dist", "q", "cnt", "sv") ∗
        scatHole nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
          exc₀ dist₀ q₀ ∗ GC)
        = (scatFrame nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab) ∗
          natAssn ra.2.2.2.1 "cnt" ∗
          ((arrayAssn ra.1 "exc" ∗ arrayAssn ra.2.1 "dist" ∗ arrayAssn ra.2.2.1 "q" ∗
              natAssn ra.2.2.2.2 "sv") ∗
            scatHole nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
              exc₀ dist₀ q₀) ∗ GC) := by
      simp only [prodAssn]; ac_rfl
    exact readout_scalar (he ▸ hst) hag

end Export

/-! ## Gate (ledger D4, refute before prove)

The *synthesized* scan is run by `Ir/Semantics.lean`'s own evaluator on
`RamScatter.Demo`'s arena — the path `0—1—2—3—4`, everything alive,
radius `1` — and what comes out of the count cell is `#guard`ed against
the baseline's own published readings (`RamScatter.Demo`: with vertex
`2` in the table the greedy process takes `0`, `2`, `4` and the value is
three; with it out it takes `0` and `3` and the value is two). Each
positive check carries a negative control. -/

section Gate

def gState (b2 t : ℕ) : Ir.State :=
  scatState 5 1 t [0, 1, 3, 5, 7, 8] [1, 0, 2, 1, 3, 2, 4, 3] [1, 1, 1, 1, 1]
    [1, 1, b2, 1, 1] [0, 0, 0, 0, 0] [0, 0, 0, 0, 0] [0, 0, 0, 0, 0]

def gCnt (b2 t : ℕ) : Option ℕ :=
  (Ir.evalFuel 40000 scatSynth_impl (gState b2 t)).bind fun p => p.1.vars "cnt"

def gExc (b2 t : ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 40000 scatSynth_impl (gState b2 t)).bind fun p => p.1.arrs "exc"

-- the whole table, radius one: the process takes `0`, `2`, `4` …
#guard gCnt 1 3 = some 3
-- … and stops at the threshold, which is what makes the early exit real
#guard gCnt 1 2 = some 2
#guard gCnt 1 4 = some 3
-- vertex `2` out of the table: the process takes `0` and then `3`
#guard gCnt 0 3 = some 2
#guard gCnt 0 2 = some 2
-- the exclusion bits at the end are the balls of the chosen vertices
#guard gExc 1 3 = some [1, 1, 1, 1, 1]
#guard gExc 0 3 = some [1, 1, 1, 1, 1]

-- **The negative controls.** The table bit bites, and the check can tell.
/--
error: Expression
  decide (gCnt 0 3 = some 3)
did not evaluate to `true`
-/
#guard_msgs in
#guard gCnt 0 3 = some 3

/--
error: Expression
  decide (gCnt 1 3 = some 4)
did not evaluate to `true`
-/
#guard_msgs in
#guard gCnt 1 3 = some 4

-- …and the early exit is not a no-op: at threshold two the count stops
-- at two even though three vertices are selectable.
/--
error: Expression
  decide (gCnt 1 2 = some 3)
did not evaluate to `true`
-/
#guard_msgs in
#guard gCnt 1 2 = some 3

-- The exported budget covers a real run (`n = 5`, `ns = 8`, `t = 3`:
-- `scatK 5 8 3 = 3255`), and a wrong budget is refuted.
#guard (Ir.evalFuel 40000 scatSynth_impl (gState 1 3)).map
  (fun p => decide (Codegen.cash p.2 ≤ scatK 5 8 3)) = some true
#guard ¬ ((Ir.evalFuel 40000 scatSynth_impl (gState 1 3)).map
  (fun p => decide (Codegen.cash p.2 ≤ 500)) = some true)

end Gate

/-! ## Axioms -/

/-- info: 'Lax3Proofs.Refine.ScatterSynth.scan_spec_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scan_spec_at

/-- info: 'Lax3Proofs.Refine.ScatterSynth.scatLoop_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scatLoop_le

/-- info: 'Lax3Proofs.Refine.ScatterSynth.scatSynth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scatSynth

end Scan

/-! ## 16. The whole engine, assembled (phases 1 + 2)

`clear ; scan ; report`, in `RamScatter.scatterCom`'s own shape. The
entry store the tower pins (P7/D-bp) is written by a straight-line
setup block; the marking sweep is *inside* the scan now, so phase 3
does not appear separately. -/

section Whole

open Lax13Proofs.Reasoning
open Lax13Proofs.Imp (Com Expr)

/-- The twenty-five scalars the tower's scan and clearing pass pin
beyond `n` (which the caller supplies), each written with a literal. -/
def scatSetup (r t : ℕ) : Lax13Proofs.Imp.Com :=
  .seq (.assign "mkz" (.lit 0))
      (.seq (.assign "one" (.lit 1))
      (.seq (.assign "zero" (.lit 0))
      (.seq (.assign "cnt" (.lit 0))
      (.seq (.assign "sv" (.lit 0))
      (.seq (.assign "sent" (.lit (r + 1)))
      (.seq (.assign "d" (.lit r))
      (.seq (.assign "t" (.lit t))
      (.seq (.assign "sctb" (.lit 0))
      (.seq (.assign "scex" (.lit 0))
      (.seq (.assign "src" (.lit 0))
      (.seq (.assign "i" (.lit 0))
      (.seq (.assign "head" (.lit 0))
      (.seq (.assign "sw" (.lit 0))
      (.seq (.assign "a" (.lit 0))
      (.seq (.assign "tl" (.lit 0))
      (.seq (.assign "v" (.lit 0))
      (.seq (.assign "dv" (.lit 0))
      (.seq (.assign "dv1" (.lit 0))
      (.seq (.assign "k0" (.lit 0))
      (.seq (.assign "v1" (.lit 0))
      (.seq (.assign "kend" (.lit 0))
      (.seq (.assign "u" (.lit 0))
      (.seq (.assign "au" (.lit 0))
      ((.assign "du" (.lit 0))))))))))))))))))))))))))

theorem scatSetup_wvars (r t : ℕ) : (scatSetup r t).wvars =
    ["mkz", "one", "zero", "cnt", "sv", "sent", "d", "t", "sctb", "scex", "src", "i",
      "head", "sw", "a", "tl", "v", "dv", "dv1", "k0", "v1", "kend", "u", "au", "du"] := rfl

theorem scatSetup_warrs (r t : ℕ) : (scatSetup r t).warrs = ([] : List String) := rfl

theorem scatSetup_spec {B r t : ℕ} (hrB : r + 1 < B) (htB : t < B) (h1B : 1 < B) :
    Spec B (fun _ => True) (scatSetup r t)
      (fun _ σ' => σ'.vars "mkz" = 0 ∧
        σ'.vars "one" = 1 ∧
        σ'.vars "zero" = 0 ∧
        σ'.vars "cnt" = 0 ∧
        σ'.vars "sv" = 0 ∧
        σ'.vars "sent" = (r + 1) ∧
        σ'.vars "d" = r ∧
        σ'.vars "t" = t ∧
        σ'.vars "sctb" = 0 ∧
        σ'.vars "scex" = 0 ∧
        σ'.vars "src" = 0 ∧
        σ'.vars "i" = 0 ∧
        σ'.vars "head" = 0 ∧
        σ'.vars "sw" = 0 ∧
        σ'.vars "a" = 0 ∧
        σ'.vars "tl" = 0 ∧
        σ'.vars "v" = 0 ∧
        σ'.vars "dv" = 0 ∧
        σ'.vars "dv1" = 0 ∧
        σ'.vars "k0" = 0 ∧
        σ'.vars "v1" = 0 ∧
        σ'.vars "kend" = 0 ∧
        σ'.vars "u" = 0 ∧
        σ'.vars "au" = 0 ∧
        σ'.vars "du" = 0) 50 := by
  have h0 : (0 : ℕ) < B := by omega
  have hone : (1 : ℕ) < B := h1B
  have hd : r < B := by omega
  refine Spec.of_exists fun σ _ => ?_
  refine ⟨_, _, (Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit hone)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit hrB)).seq ((Run.assign (evalB_lit hd)).seq ((Run.assign (evalB_lit htB)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq ((Run.assign (evalB_lit h0)).seq (Run.assign (evalB_lit h0))))))))))))))))))))))))),
    by simp only [size_lit]; omega, ?_⟩
  refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- **The whole pass**: the entry store, the clearing pass, the scan and
the report. -/
def scatterTowerCom (r t : ℕ) : Lax13Proofs.Imp.Com :=
  .seq (scatSetup r t)
    (.seq (Codegen.embed clearSynth_impl)
      (.seq (.assign "sw" (.lit 0))
        (.seq (Codegen.embed scatSynth_impl)
          (.ite (.lt (.var "cnt") (.lit t))
            (.assign "flag" (.lit 0)) (.assign "flag" (.lit 1))))))

/-- …and what it costs. -/
def scatterTowerK (n ns t : ℕ) : ℕ := scatK n ns t + clearK n + 58

/-- **The greedy scatter pass, re-derived through the tower.**
`RamScatter.scatter_spec`'s statement — the same precondition
vocabulary, the same `greedySet` answer in `flag` — at the tower's own
cost and with the two standing deltas (P7/D-bo: the scratch arrays'
entries are words state-globally, here for `exc` as well as `dist`/`q`;
P7/D-bp: the entry store is pinned, which `scatSetup` writes). -/
theorem scatterTowerCom_spec {B nn ns r t : ℕ} {G : SimpleGraph (Fin nn)} {M Tab O T : ℕ → ℕ}
    {X : Set (Fin nn)}
    (hcsr : RamBfs.CsrGraph G ns O T) (hnB : nn < B) (h1B : 1 < B) (hrB : r + 1 < B)
    (htB : t < B) (hOB : ∀ z, z < nn + 1 → O z < B) (hTB : ∀ z, z < ns → T z < B)
    (hMB : ∀ z, z < nn → M z < B) (hTabB : ∀ z, z < nn → Tab z < B)
    (hTab : ∀ v : Fin nn, Tab (v : ℕ) ≠ 0 ↔ v ∈ X)
    (hdebt : ∀ E D Q : List ℕ, E.length = nn → D.length = nn → Q.length = nn →
      (∀ w ∈ E, w < B) → (∀ w ∈ D, w < B) → (∀ w ∈ Q, w < B) →
      ScanBounded B nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M) (arrOf nn Tab)
        E D Q) :
    Spec B
      (fun σ => σ.vars "n" = nn ∧ σ.arrs "off" = arrOf (nn + 1) O ∧
        σ.arrs "tgt" = arrOf ns T ∧ σ.arrs "alv" = arrOf nn M ∧
        σ.arrs "tab" = arrOf nn Tab ∧ RamScatter.Words B nn "dist" σ ∧
        RamScatter.Words B nn "q" σ ∧ RamScatter.Words B nn "exc" σ)
      (scatterTowerCom r t)
      (fun _ σ' => (σ'.vars "flag" = 1 ↔
          t ≤ (Lax3.ScatterSentences.greedySet (RamBfs.masked G M) r X).ncard) ∧
        σ'.vars "flag" ≤ 1)
      (scatterTowerK nn ns t) := by
  have h0 : (0 : ℕ) < B := by omega
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hn, hoff, htgt, halv, htabA, ⟨gd, hdarr, hdB⟩, ⟨gq, hqarr, hqB⟩,
    ⟨ge, hearr, heB⟩⟩ := hσ
  -- the entry store
  obtain ⟨σ₁, run₁, hset, hfv₁, hfa₁, -, -⟩ :=
    (scatSetup_spec (r := r) (t := t) hrB htB h1B).frame.run (σ := σ) trivial
  obtain ⟨s_mkz, s_one, s_zero, s_cnt, s_sv, s_sent, s_d, s_t, s_sctb, s_scex, s_src,
    s_i, s_head, s_sw, s_a, s_tl, s_v, s_dv, s_dv1, s_k0, s_v1, s_kend, s_u, s_au,
    s_du⟩ := hset
  have harr₁ : ∀ a, σ₁.arrs a = σ.arrs a := fun a => hfa₁ a (by rw [scatSetup_warrs]; simp)
  have hn₁ : σ₁.vars "n" = nn := by
    rw [hfv₁ "n" (by rw [scatSetup_wvars]; decide)]; exact hn
  -- the clearing pass
  obtain ⟨σ₂, run₂, ⟨E, hEarr, hEsw, hElen, hEzero⟩, hfv₂, hfa₂, -, -⟩ :=
    ((clearCom_spec (B := B) (n := nn) hnB h1B).frame).run (σ := σ₁)
      ⟨hn₁, s_sw, s_one, s_mkz, arrOf nn ge, by rw [harr₁]; exact hearr,
        length_arrOf nn ge, Lax3Proofs.Refine.BfsBridge.mem_arrOf_lt heB⟩
  have hEB : ∀ w ∈ E, w < B := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hw
    rw [← getElem!_pos E k hk, hEzero k (by omega)]
    omega
  have hv₂ : ∀ y : String, y ∉ (Codegen.embed clearSynth_impl).wvars → σ₂.vars y = σ₁.vars y :=
    hfv₂
  have ha₂ : ∀ a : String, a ∉ (Codegen.embed clearSynth_impl).warrs →
      σ₂.arrs a = σ₁.arrs a := hfa₂
  -- the sweep counter, back to zero
  have run₃ : Run B (.assign "sw" (.lit 0)) σ₂ (σ₂.setVar "sw" 0) 2 :=
    (Run.assign (v := 0) (evalB_lit h0)).mono (by norm_num)
  -- the scan
  have hag : agree (scatState nn r t (arrOf (nn + 1) O) (arrOf ns T) (arrOf nn M)
      (arrOf nn Tab) E (arrOf nn gd) (arrOf nn gq)) (σ₂.setVar "sw" 0) := by
    have hsw0 : (σ₂.setVar "sw" 0).vars "sw" = 0 := by simp
    have hoth : ∀ y : String, y ≠ "sw" → (σ₂.setVar "sw" 0).vars y = σ₂.vars y := by
      intro y hy; simp [hy]
    have hothA : ∀ a : String, (σ₂.setVar "sw" 0).arrs a = σ₂.arrs a := by intro a; simp
    refine Codegen.agree_ofPairs ?_ ?_
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp only <;>
        first
          | exact hsw0
          | (rw [hoth _ (by decide), hv₂ _ (by decide)]; assumption)
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp only <;> rw [hothA] <;>
        first
          | exact hEarr
          | (rw [ha₂ _ (by decide), harr₁]; assumption)
  obtain ⟨σ₄, run₄, hcnt₄, hans₄⟩ :=
    (scan_spec_at (nn := nn) (ns := ns) (r := r) (t := t) (G := G) (M := M) (Tab := Tab)
      (O := O) (T := T) (X := X) hcsr hTab E (arrOf nn gd) (arrOf nn gq) hnB h1B hrB htB
      hEB (Lax3Proofs.Refine.BfsBridge.mem_arrOf_lt hdB)
      (Lax3Proofs.Refine.BfsBridge.mem_arrOf_lt hqB) hOB hTB hMB hTabB hElen
      (length_arrOf nn gd) (length_arrOf nn gq) hEzero
      (hdebt E (arrOf nn gd) (arrOf nn gq) hElen (length_arrOf nn gd) (length_arrOf nn gq)
        hEB (Lax3Proofs.Refine.BfsBridge.mem_arrOf_lt hdB)
        (Lax3Proofs.Refine.BfsBridge.mem_arrOf_lt hqB))).run (σ := σ₂.setVar "sw" 0) hag
  -- the report
  have hcntB : σ₄.vars "cnt" < B := by omega
  have hcv : (Lax13Proofs.Imp.Cond.lt (Expr.var "cnt") (.lit t)).evalB B σ₄
      = some (decide (σ₄.vars "cnt" < t)) := evalB_condLt (evalB_var hcntB) (evalB_lit htB)
  by_cases hlt : σ₄.vars "cnt" < t
  · refine ⟨σ₄.setVar "flag" 0, _,
      run₁.seq (run₂.seq (run₃.seq (run₄.seq (Run.ite_true (by rw [hcv]; simp [hlt])
        (Run.assign (v := 0) (evalB_lit h0)))))), ?_, ?_, ?_⟩
    · simp only [scatterTowerK, Lax13Proofs.Imp.Cond.size, Lax13Proofs.Imp.Expr.size]
      omega
    · rw [show (σ₄.setVar "flag" 0).vars "flag" = 0 from by simp]
      exact ⟨fun h => absurd h (by omega), fun hc => absurd hlt (hans₄.1 hc)⟩
    · rw [show (σ₄.setVar "flag" 0).vars "flag" = 0 from by simp]; omega
  · refine ⟨σ₄.setVar "flag" 1, _,
      run₁.seq (run₂.seq (run₃.seq (run₄.seq (Run.ite_false (by rw [hcv]; simp [hlt])
        (Run.assign (v := 1) (evalB_lit h1B)))))), ?_, ?_, ?_⟩
    · simp only [scatterTowerK, Lax13Proofs.Imp.Cond.size, Lax13Proofs.Imp.Expr.size]
      omega
    · rw [show (σ₄.setVar "flag" 1).vars "flag" = 1 from by simp]
      exact ⟨fun _ => hans₄.2 hlt, fun _ => rfl⟩
    · rw [show (σ₄.setVar "flag" 1).vars "flag" = 1 from by simp]

/-- info: 'Lax3Proofs.Refine.ScatterSynth.scatterTowerCom_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scatterTowerCom_spec

/-! ## 17. Telemetry (wave 2A′)

* **Synthesis wall clock**, warm build: the greedy scan —
  `Com.while` over a body with two array reads, three nested branches,
  the whole synthesized BFS as one leaf, a nested `while` (the sweep)
  and a five-component loop state carrying three arrays — **37 s** in
  the isolated probe module (the leaf rules, the program and one
  `#sepref_synth`), first run, no bespoke tactic work, no hand-written
  frame clause, no `LOOP_VARIANT`, no `packN`. The whole file — both
  waves, four syntheses, the two §8b probes and every gate — elaborates
  in **60 s**.

* **Cost constants, computed** (`decide +kernel` from the per-iteration
  accounts, not tuned):

  | | tower | baseline | ratio |
  |---|---|---|---|
  | one pick | `94·n + 40·ns + 50` | `74·n + 44·ns + 60` (`pickCost`) | ≈1.2 on `n` |
  | the scan | `(94n + 40ns + 50)·t + 33·n + 4` | `pickCost·t + 25·n + 6` | — |
  | the pass | `scatK + clearK n + 58` | `pickCost·t + 36·n + 20` | — |

  The per-pick gap decomposes exactly: the search is `56n + 40ns + 32`
  against the baseline's `51n + 44ns + 30` (P7/D-br, computed vs tuned),
  and the sweep is `38·n` against `23·n` — R2A/D-a, the IR's
  no-expression-layer choice, and nothing else. Everything outside those
  two is `18` units against the baseline's `24`.

* **Bounds pass.** Phases 1 and 3 carry `BRefine` derivations (§5).
  Phase 2 does not: §15's named debt, and the reason is stated there —
  the tower's bound for `bfsQSynth_impl` exists only as an `Ir.bpre` at
  one pinned store with the trivial postcondition, so no `BRefine`
  composition can pass an assertion through it. The debt is a hypothesis
  of `scan_spec_at` and of `scatterTowerCom_spec`, and of nothing else.

* **New tool gaps** (beyond §10's four):
  5. **the translate phase does not read a bound result's value.**
     `hnr_seq` hands the continuation `returnT a ≤ m`, from which
     `a = 0` follows for `m = mopConstN 0`; the translate phase keeps
     `a` opaque, so a rule whose precondition pins a *value* at a cell
     (`hnCtxt natAssn 0 "i"`) cannot be fed by a zeroing step inside the
     program. Worked around by R2A/D-j (make the entry values arguments
     and assert them in the operation), which costs one `NRest.assert`
     per pinned cell;
  6. **a named `def` returning a program is opaque to the operator
     phase** — `keepF s := pack4' …` reported "no rule translates
     `keepF s`" where the inlined `pack4' …` translates. R2A/D-f's
     `frameMatch` opacity, met one layer up, in the *operator* phase;
  7. **no `BRefine` route from a landed `Ir.bpre`** — §15. This is the
     one that costs a deliverable rather than a workaround.

* **Refuted before proved.** §14 runs the *synthesized* scan on
  `RamScatter.Demo`'s five-vertex arena at both settings of the table
  bit of vertex `2` and at three thresholds, checking the count against
  the baseline's own published readings (three and two), with three
  pinned negative controls and a cost-coverage refutation. The early
  exit is checked to be real (threshold two stops the count at two while
  three vertices are selectable) — the one behaviour a "run the whole
  scan" implementation would get wrong silently.

* **Axioms.** `scan_spec_at`, `scatLoop_le`, `scatSynth` and
  `scatterTowerCom_spec` pinned at
  `[propext, Classical.choice, Quot.sound]`.
-/

end Whole

end Lax3Proofs.Refine.ScatterSynth
