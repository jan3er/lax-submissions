import Lax13Proofs.Refine.Sepref.Definition
import Lax13Proofs.Refine.Sepref.Signature

/-!
# Signature-driven Sepref synthesis

Tower-expansion P1.B's port of `prepare_hfref_synth_tac` from the pinned
`Sepref_Rules.thy`.  The implementation lives in `Definition.synthesize`,
where it can feed the existing command without a parallel pipeline.  This
module holds the compiled acceptance controls.

The source preparation rule changes a schematic `hfref` goal into one generic
`hn_refine` goal and introduces conceptual-type premises obtained from the
input assertions.  Lean's `hfref` is transparently the same three binders, so
the frontend introduces them directly.  Interface discovery and operation
registration are supplied by `Register.lean`; they remain orthogonal to this
proof-producing conversion.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

namespace SignaturePrepGate

structure ChainArgs where
  a : ℕ
  b : ℕ
  c : ℕ

structure ChainNames where
  a : String
  b : String
  c : String
  tmp : String
  result : String

/-- Reducible because signature preparation must expose the ownership
assertion after introducing the generic abstract and concrete arguments. -/
abbrev chainRS :
    (ChainArgs → ChainNames → Assn) × (ChainArgs → ChainNames → Assn) :=
  ((fun x n =>
      junkCell n.tmp ∗ junkCell n.result ∗
      hnCtxt natAssn x.a n.a ∗ hnCtxt natAssn x.b n.b ∗
      hnCtxt natAssn x.c n.c),
    (fun x n =>
      junkCell n.tmp ∗ hnCtxt natAssn x.c n.c ∗
      hnCtxt natAssn x.a n.a ∗ hnCtxt natAssn x.b n.b))

set_option linter.unusedVariables false in
sepref_synth chainFromSignature :
    ((fun _ : ChainNames => (_, _)),
      fun x : ChainArgs =>
        NRest.bindT (mopBinop .add x.a x.b) fun y => mopBinop .mul y x.c) ∈
      hfref (fun _ : ChainArgs => True) chainRS (fun _ _ => natAssn)

/- Signature preparation chose both the destination and the program; neither
appeared in a hand-written `hnRefine` goal. -/
#guard chainFromSignature_impl
    { a := "a", b := "b", c := "c", tmp := "t", result := "r" } =
  ("r", Com.seq (Com.binop Imp.Bop.add "t" "a" "b")
    (Com.binop Imp.Bop.mul "r" "t" "c"))

/-- The generated theorem is an ordinary signature and can immediately enter
P1.A's composition frontend. -/
theorem chainFromSignature_fcomp :
    (chainFromSignature_impl,
      fun x : ChainArgs =>
        NRest.bindT (mopBinop .add x.a x.b) fun y => mopBinop .mul y x.c) ∈
      hfref (fun _ : ChainArgs => True) chainRS (fun _ _ => natAssn) :=
  chainFromSignature

/-! ### Wide-state control

The campaign seam is array-heavy, so the exercise-scale control retains
eight independent arrays while synthesizing the same two-operation phase.
This is deliberately a signature, not an `hnRefine` transcription. -/

structure WideArgs where
  A₁ : List ℕ
  A₂ : List ℕ
  A₃ : List ℕ
  A₄ : List ℕ
  A₅ : List ℕ
  A₆ : List ℕ
  A₇ : List ℕ
  A₈ : List ℕ
  a : ℕ
  b : ℕ
  c : ℕ

abbrev wideRS :
    (WideArgs → Unit → Assn) × (WideArgs → Unit → Assn) :=
  ((fun x _ =>
      hnCtxt arrayAssn x.A₁ "A1" ∗ hnCtxt arrayAssn x.A₂ "A2" ∗
      hnCtxt arrayAssn x.A₃ "A3" ∗ hnCtxt arrayAssn x.A₄ "A4" ∗
      hnCtxt arrayAssn x.A₅ "A5" ∗ hnCtxt arrayAssn x.A₆ "A6" ∗
      hnCtxt arrayAssn x.A₇ "A7" ∗ hnCtxt arrayAssn x.A₈ "A8" ∗
      junkCell "t" ∗ junkCell "r" ∗ hnCtxt natAssn x.a "a" ∗
      hnCtxt natAssn x.b "b" ∗ hnCtxt natAssn x.c "c"),
    (fun x _ =>
      junkCell "t" ∗ hnCtxt natAssn x.c "c" ∗ hnCtxt natAssn x.a "a" ∗
      hnCtxt natAssn x.b "b" ∗ hnCtxt arrayAssn x.A₁ "A1" ∗
      hnCtxt arrayAssn x.A₂ "A2" ∗ hnCtxt arrayAssn x.A₃ "A3" ∗
      hnCtxt arrayAssn x.A₄ "A4" ∗ hnCtxt arrayAssn x.A₅ "A5" ∗
      hnCtxt arrayAssn x.A₆ "A6" ∗ hnCtxt arrayAssn x.A₇ "A7" ∗
      hnCtxt arrayAssn x.A₈ "A8"))

set_option linter.unusedVariables false in
sepref_synth widePhaseFromSignature :
    ((fun _ : Unit => (_, _)),
      fun x : WideArgs =>
        NRest.bindT (mopBinop .add x.a x.b) fun y => mopBinop .mul y x.c) ∈
      hfref (fun _ : WideArgs => True) wideRS (fun _ _ => natAssn)

#guard widePhaseFromSignature_impl () =
  ("r", Com.seq (Com.binop Imp.Bop.add "t" "a" "b")
    (Com.binop Imp.Bop.mul "r" "t" "c"))

end SignaturePrepGate

end Lax13Proofs.Refine.Sepref
