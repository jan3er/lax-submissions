import Lax13Proofs.Refine.Examples.BfsQSynth
import Lax13Proofs.Refine.Sepref.Register

/-!
# P1.B acceptance: queue BFS from an `hfref` signature

This restates the landed `BfsQSynth` synthesis boundary as data: one abstract
argument record, a fixed concrete naming scheme, and input/output assertion
functions.  There is no hand-written `hnRefine` goal.  The byte-for-byte
program equality at the end is the campaign's SIG-6 closure test.
-/

namespace Lax13Proofs.Refine.BfsQSynth

open Bfs BfsQ Sepref Ir NRest Codegen

structure BfsQArgs where
  n : ℕ
  d : ℕ
  src : ℕ
  off : List ℕ
  tgt : List ℕ
  alv : List ℕ
  dist₀ : List ℕ
  q₀ : List ℕ

/-- The signature relation is reducible so preparation exposes precisely the
same ownership boundary as `bfsQPre`/`bfsQFrame`. -/
abbrev bfsQRS :
    (BfsQArgs → Unit → Assn) × (BfsQArgs → Unit → Assn) :=
  ((fun x _ =>
      hnCtxt arrayAssn x.dist₀ "dist" ∗ hnCtxt arrayAssn x.q₀ "q" ∗
      hnCtxt natAssn 0 "i" ∗ hnCtxt natAssn 0 "head" ∗
      hnCtxt arrayAssn x.off "off" ∗ hnCtxt arrayAssn x.tgt "tgt" ∗
      hnCtxt arrayAssn x.alv "alv" ∗ hnCtxt natAssn x.n "n" ∗
      hnCtxt natAssn (x.d + 1) "sent" ∗ hnCtxt natAssn x.d "d" ∗
      hnCtxt natAssn x.src "src" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗
      junkCell "dv1" ∗ junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗
      junkCell "u" ∗ junkCell "au" ∗ junkCell "du"),
    (fun x _ =>
      junkCell "a" ∗ hnCtxt arrayAssn x.alv "alv" ∗
      hnCtxt natAssn x.src "src" ∗ junkCell "i" ∗
      hnCtxt arrayAssn x.off "off" ∗ hnCtxt arrayAssn x.tgt "tgt" ∗
      hnCtxt natAssn x.n "n" ∗ hnCtxt natAssn (x.d + 1) "sent" ∗
      hnCtxt natAssn x.d "d" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗ junkCell "k0" ∗
      junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
      junkCell "du"))

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
sepref_synth bfsQFromSignature :
    ((fun _ : Unit => (_, _)),
      fun x : BfsQArgs => bfsQS x.n x.d x.src x.off x.tgt x.alv x.dist₀ x.q₀) ∈
      hfref (fun _ : BfsQArgs => True) bfsQRS
        (fun _ _ => arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)

/- Both the selected result cells and the full command are pinned against the
existing synthesis, so this checks more than extensional refinement. -/
#guard bfsQFromSignature_impl () =
  (("dist", "q", "head", "tl"), bfsQSynth_impl)

/- info: 'Lax13Proofs.Refine.BfsQSynth.bfsQFromSignature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#print axioms bfsQFromSignature

end Lax13Proofs.Refine.BfsQSynth
