import Lax3Proofs.RamScatter
import Lax13Proofs.Refine.Examples.BfsQSynth
import Lax13Proofs.Refine.Sepref.Examples.WordAssnSpike

/-!
# ND-MC rebase P2 / satellite 2A — the scatter engine's marking sweep,
re-derived through the refinement tower

`Lax3Proofs.RamScatter` is the greedy scatter pass. Its three phases are

1. `clearExc` — zero the exclusion bits (a flat pass over the carrier);
2. `scatterLoop` — the greedy scan, whose picking branch runs **the whole
   depth-capped search** (`RamBfs.bfsCom`) and then
3. `markCom` — the marking sweep, a flat pass over the carrier applying
   `RamScatter.markVal` pointwise.

This file re-derives phases 1 and 3 through the tower, end to end:
abstract `NRest` program → correctness → `sepref_synth` → `BRefine`
bounds → cashing → a `Reasoning.Spec` export in the baseline's own
vocabulary. Phase 2 is *not* re-derived here; §8b probes the one thing
that blocks it and §9 prices the rest — the finding is architectural and
is half of the satellite's report, not an omission.

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
    acells (clearState n E₀) |>.erase "exc"), 0)

theorem clear_state_holds (n : ℕ) (E₀ : List ℕ) :
    irSTATE (clearPre n E₀ ∗ clearHole n E₀) (clearState n E₀, 0) := by
  show (clearPre n E₀ ∗ clearHole n E₀)
    ((vcells (clearState n E₀), acells (clearState n E₀)), 0)
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
    acells (markState n rp1 D E₀) |>.erase "exc" |>.erase "dist"), 0)

theorem mark_state_holds (n rp1 : ℕ) (D E₀ : List ℕ) :
    irSTATE (markPre n rp1 D E₀ ∗ markHole n rp1 D E₀) (markState n rp1 D E₀, 0) := by
  show (markPre n rp1 D E₀ ∗ markHole n rp1 D E₀)
    ((vcells (markState n rp1 D E₀), acells (markState n rp1 D E₀)), 0)
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
    ((vcells (clearState n E₀), acells (clearState n E₀)), 0)
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
    ((vcells (markState n rp1 D E₀), acells (markState n rp1 D E₀)), 0)
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
`RamDriverBot.baseCost` / `RamDriverCompose.baseImplements`. Two of its
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
  is an improvement — `reprCom` is the one part of the base case that is
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

end Lax3Proofs.Refine.ScatterSynth
