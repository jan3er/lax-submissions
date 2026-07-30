import Lax13Proofs.Refine.Sepref.IrOps

/-!
# Shared in-place counter ops (T1/D-c)

The three in-place operations every engine wave has so far restated
locally — `mopSucc` (BfsQSynth, P7/D-bb), `mopAddIn` (TrailRecursion),
`mopKeep` (ElimSynth) — promoted to one shared home. Each is an
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

end Lax13Proofs.Refine.Sepref
