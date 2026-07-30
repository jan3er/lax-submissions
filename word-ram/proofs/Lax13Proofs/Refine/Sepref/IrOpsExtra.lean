import Lax13Proofs.Refine.Sepref.IrOps

/-!
# Shared in-place counter ops (T1/D-c; T2 additions below)

The in-place operations every engine wave has so far restated
locally — `mopSucc` (BfsQSynth, P7/D-bb), `mopAddIn` (TrailRecursion),
`mopKeep` (ElimSynth), and since T2 `mopPred` (ElimSynth3) and the
owned-destination move `mopSetIn` (2B′/D-b) — promoted to one shared
home. Each is an
irreducible alias of `mopBinop .add` with a single in-place rule, so
the operator phase cannot misroute the destination: the abstract name
*is* the routing (the `mopSucc` idiom).

The local restatements in the consumer files stay compiled — each is
keyed on its own irreducible constant, so the rules never collide; new
code imports this module instead. `mopKeep` exists because an empty
`else` branch must be an in-place `x := x + zero`, not a `mopCopy`
through a junk destination (ElimSynth's finding: the copy moves the
accumulator out of its cell and the merge junks it).

`IrOps.lean` is wave B1's and frozen; this file is the sanctioned
shared annex (same pattern as `Translate.lean` hosting `mopPair`).
-/

namespace Lax13Proofs.Refine.Sepref

open Lax13Proofs.Refine NRest Ir

/-- In-place increment: `x := x + 1`, from a cell holding `1`. -/
noncomputable def mopSucc (m : ℕ) : NRest ℕ ECost := mopBinop .add m 1

theorem mopSucc_eq (m : ℕ) : mopSucc m = mopBinop .add m 1 := rfl

@[sepref_fr_rules]
theorem hnr_mop_succ (x z : String) (m : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn 1 z) (.binop .add x x z)
      (hnCtxt natAssn 1 z) x natAssn (mopSucc m) := by
  rw [mopSucc_eq]; exact hnr_mop_binop_self .add x z m 1

attribute [irreducible] mopSucc

/-- In-place accumulate: `x := x + w`, `w` read from its own cell. -/
noncomputable def mopAddIn (m w : ℕ) : NRest ℕ ECost := mopBinop .add m w

theorem mopAddIn_eq (m w : ℕ) : mopAddIn m w = mopBinop .add m w := rfl

@[sepref_fr_rules]
theorem hnr_mop_addIn (x z : String) (m w : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn w z) (.binop .add x x z)
      (hnCtxt natAssn w z) x natAssn (mopAddIn m w) := by
  rw [mopAddIn_eq]; exact hnr_mop_binop_self .add x z m w

attribute [irreducible] mopAddIn

/-- In-place keep: `x := x + 0` — what an empty `else` branch costs. -/
noncomputable def mopKeep (m : ℕ) : NRest ℕ ECost := mopBinop .add m 0

theorem mopKeep_eq (m : ℕ) : mopKeep m = mopBinop .add m 0 := rfl

@[sepref_fr_rules]
theorem hnr_mop_keep (x z : String) (m : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn 0 z) (.binop .add x x z)
      (hnCtxt natAssn 0 z) x natAssn (mopKeep m) := by
  rw [mopKeep_eq]; exact hnr_mop_binop_self .add x z m 0

attribute [irreducible] mopKeep

/-! ## T2 additions (ND-MC rebase tool wave T2, item 5)

Two more ops every engine wave has now asked for. -/

/-- In-place decrement: `x := x - 1`, from a cell holding `1`. The
annex's fourth in-place op and its first subtractive one — restated
locally by `Lax3Proofs/Refine/ElimSynth3.lean` §1 (2B′), promoted here
with the same shape; the local restatement stays compiled on its own
irreducible constant, so the rules never collide. -/
noncomputable def mopPred (m : ℕ) : NRest ℕ ECost := mopBinop .sub m 1

theorem mopPred_eq (m : ℕ) : mopPred m = mopBinop .sub m 1 := rfl

@[sepref_fr_rules]
theorem hnr_mop_pred (x z : String) (m : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn 1 z) (.binop .sub x x z)
      (hnCtxt natAssn 1 z) x natAssn (mopPred m) := by
  rw [mopPred_eq]; exact hnr_mop_binop_self .sub x z m 1

attribute [irreducible] mopPred

/-- In-place cell-to-cell set at an **owned** destination:
`x := y + zero`. The only rule that moved one cell into another
(`hnr_mop_copy`) has a *junk* destination, so an `irIf` arm could not
assign a cell that is a component of the enclosing loop's state
(2B′/D-b's finding — ElimSynth2 had to rewrite `kmax := max kmax mind`
into branch-free arithmetic to get around it). This rule is the missing
move: the destination arrives owned at any value and leaves holding the
source's, the source and the zero cell survive. Derived from the junk
rule by weakening the destination's ownership. -/
noncomputable def mopSetIn (w : ℕ) : NRest ℕ ECost := mopBinop .add w 0

theorem mopSetIn_eq (w : ℕ) : mopSetIn w = mopBinop .add w 0 := rfl

@[sepref_fr_rules]
theorem hnr_mop_setIn (x y z : String) (m w : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn w y ∗ hnCtxt natAssn 0 z)
      (.binop .add x y z) (hnCtxt natAssn w y ∗ hnCtxt natAssn 0 z) x natAssn
      (mopSetIn w) := by
  rw [mopSetIn_eq]
  exact hnRefine_cons_pre (hnr_mop_binop .add x y z w 0)
    (sepConj_mono_left (natAssn_entails_junkCell m x))

attribute [irreducible] mopSetIn

/-! ### Gate (refute before prove, T2)

The two rules' semantics, checked by the IR's own evaluator: `pred`
really decrements in place, `setIn` really moves the *source's* value
into an owned destination — and the negative controls pin that the
destination's old value is gone, i.e. neither rule is a `keep`. -/

section Gate

/-- A four-cell store: `x = 5`, `y = 9`, `one = 1`, `zero = 0`. -/
def opState : Ir.State :=
  Ir.State.ofPairs [("x", 5), ("y", 9), ("one", 1), ("zero", 0)] []

def gPred : Option ℕ :=
  (Ir.evalFuel 8 (.binop .sub "x" "x" "one") opState).bind fun p => p.1.vars "x"

def gSetIn : Option ℕ :=
  (Ir.evalFuel 8 (.binop .add "x" "y" "zero") opState).bind fun p => p.1.vars "x"

#guard gPred = some 4
#guard gSetIn = some 9

/--
error: Expression
  decide (gPred = some 5)
did not evaluate to `true`
-/
#guard_msgs in
#guard gPred = some 5

/--
error: Expression
  decide (gSetIn = some 5)
did not evaluate to `true`
-/
#guard_msgs in
#guard gSetIn = some 5

end Gate

end Lax13Proofs.Refine.Sepref
