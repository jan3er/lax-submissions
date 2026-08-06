import Lax3Proofs.Refine.OrderSynth
import Lax13Proofs.Refine.Sepref.Register

/-!
# P4.6 / wave S — the ordering phase through `sepref_synth`, measured

A **tractability probe**. The question is not whether the phase's cost is
good — `OrderBlockProbe` §1/§2 already prove the landed text permits no
carrier-blind cost, and every cost synthesized here is carrier-bounded,
which is expected and is not a defect. The question is *operational*: at
fifteen array arguments and twenty-one pass instances, does whole-phase
synthesis complete, and where does the time go.

## 0. TELEMETRY

Machine: the campaign's warm `main` checkout, `lake build` of this module
alone, ND-MC proofs at 3 070 jobs for the module target (3 554 for the
package). Each row is a staged build of this file truncated after the
named synthesis, minus the previous stage, so the figure is that
synthesis' own wall clock. `ops` is `comSize` of the synthesized `Com`
(§3), pinned by `#guard` at each row.

| prefix | passes | leaf ops | ops | wall clock |
|---|---|---|---|---|
| (baseline: 3 leaf syntheses + §4) | — | — | — | 10.0 s |
| `pre5Synth` | 5 | 5 copy | 44 | 16.4 s |
| `pre9Synth` | 9 | 7 copy, 2 fill | 76 | 33.1 s |
| `pre13Synth` | 13 | 7 copy, 5 fill, 1 ord | 106 | 57.2 s |
| `pre18Synth` | 18 | 7 copy, 10 fill, 1 ord | 141 | 132.0 s |
| `pre5FromSignature` (`hfref`) | 5 | 5 copy | 44 | 27.3 s |
| `pre18FromSignature` (`hfref`) | 18 | 7 copy, 10 fill, 1 ord | 141 | ≈ 181 s |

Figures are single runs on a warm machine and carry about ±10 %; the
direct-mode column is one staging sweep, the two signature rows another.
Signature mode costs **1.4–1.7×** the written-goal form at the same
program — the `hfref` binders are unfolded at `.all` transparency and the
declared frame is re-checked against the synthesized one by
`entails_refl`. The whole module builds in 440 s.

**Against BfsQ.** `Lax13Proofs`' whole-program reference is
`bfsQFromSignature` at **49 s**, and `comSize bfsQSynth_impl = 92` (§3).
Interpolating this file's curve at 92 ops gives ≈ 46 s. The two agree to
within the measurement's own noise, and they are agreeing across a real
difference in shape: BfsQ synthesizes one deep loop nest *body and all*,
while the rows above apply a registered leaf rule per loop and pay
instead for a twenty-nine-conjunct ownership context threaded through
eighteen binds. So the cost is a function of the **program's size**, not
of whether that size is loop depth or pass count, and registering leaves
buys no asymptotic relief at this scale — it buys only the ability to
state the phase at all.

**The exponent.** 5 → 18 passes (44 → 141 ops) is 16.4 s → 132.0 s: an
exponent of 1.63 in pass count, 1.79 in op count. But it is not a single
exponent — the local exponent in pass count rises 1.20 (5→9), 1.49
(9→13), 2.57 (13→18), and the reason is that the ownership context grows
*with* the prefix (each further pass brings its own index cell and, for
the tail fills, its own array). The campaign's earlier 1.28–1.35 was
measured at fixed ownership width. At the phase's real shape the two grow
together and the curve steepens.

**Heartbeats.** `pre5Synth` needs `maxHeartbeats 1000000` (BfsQ's
figure); `pre9Synth`/`pre13Synth` need `4000000`; `pre18Synth` and both
signature-mode runs need `8000000`.

## 1. WHAT LANDED, AND WHAT STALLED

`orderPhase0` (`OrderSynth` :822–846) is twenty-one `bindT` pass
instances over fifteen arrays plus an engine argument `E`. Of the
twenty-one:

* **eighteen synthesize** — passes 1, 2, 3, 5, 6, 7, 8, 10, 11, 13, 14,
  15, 16, 17, 18, 19, 20, 21 in the §0 table's numbering. `pre18Synth`
  is exactly these, in the phase's own order, and `pre18FromSignature`
  is the same from an `hfref` signature.
* **pass 9 stalls** — `fillPass n 1 (mk.1, 0)`, the mask reopened before
  the second elimination. §4 locates it: the pass rule wants its
  destination as one `arrayAssn ×ₐ natAssn` conjunct, and after pass 3
  the mask is owned as a bare `hnCtxt arrayAssn mk.1 "alv"` with the
  index in a separate cell. `frameMatch` **splits** a product into its
  components (T1/D-b) but does not **merge** two components into a
  product. `mergeTestSplit` is the same two-pass shape with the product
  supplied whole and it synthesizes; the `example` beside it is the tool
  refusing the split form. Every other destination of the phase is
  either an input array (which can enter as a product) or an engine
  output; pass 9 is the only pass whose destination is a value an
  earlier pass produced, so it is the only one blocked.
* **passes 4 and 12 — the two engine calls — cannot be run at any
  engine instantiation that exists today.** Three routes, all closed:
  * `E := fun _ _ _ => ElimSynth6.elimProgram …`, the only witness of
    `ElimAvailA`, has **no synthesized `Com`**: 2B′ never assembled the
    engine's five passes into one program (2E/D-a, still open).
  * `E := fun o t a => mopElim n o t a s`, the only *registered* engine
    leaf (`OrderSynth` :1004), has the wrong result type (`ES`, not
    `ElimOut`) and, decisively, pins its eleven-component **entry**
    state in the rule. `orderPhase0` calls `E` twice; after the first
    call those cells hold the first call's exit state, so the second
    call cannot match. An engine leaf usable by this phase must be
    stated at an entry state the rule leaves free.
  * a spec-shaped leaf `E := fun _ _ _ => NRest.spec (ElimPost n W) …`
    would fix both — `hnRefine` is monotone upward in the abstract
    program (`Sepref/Basic.lean`'s `hnRefine_ref`), so a rule proved at
    a program transfers to any spec above it — but the program it would
    have to be proved at is `elimProgram`'s, i.e. the first route.

So the probe's answer is: **the tool scales to the phase, the phase does
not yet scale to the tool.** Eighteen of nineteen non-engine passes go
through in 132 s at a twenty-nine-conjunct ownership context; the
remaining three obstructions are one missing frame-matcher capability
(product merge) and one unpaid 2B′ debt (the engine as a program), and
neither is a cost or a semantics problem.

## 2. WHAT THIS FILE DOES *NOT* CLAIM

`pre5`/`pre9`/`pre13`/`pre18` are **new definitions of this file**. They
are `orderPhase0`'s passes in `orderPhase0`'s order, with the two engine
binds omitted and the seven engine outputs the later passes read
(`e1.2.2.2.1`, `e1.2.2.2.2`, `e1.2.1`, `e1.2.2.1`, `e2.1`, `e2.2.1`,
`e2.2.2.1`) entering as ordinary array arguments — which is what they
are once the engine is a hypothesis. No theorem here says any of them
equals `orderPhase0`, and none is a restatement of a landed cost.
`orderPhase0`, `orderPhase0_le`, `OrderBridge` and `RamDriver` are
untouched; the three leaf rules below are *new* declarations of this
namespace and no attribute is added to any landed declaration (ledger
E21).

The three leaf rules are re-syntheses at symbolic cell names, not
transports of `copySynth'`/`fillSynth'`/`ordSynth'` — those are stated at
fixed names and a name-parametric rule cannot be derived from them. §2
closes the gap the other way: each parametric rule, **instantiated at the
landed names, is the landed program**, and `mopCopy_landed` /
`mopFill_landed` / `mopOrd_landed` are `copySynth'` / `fillSynth'` /
`ordSynth'` proved from it. So the parametric rules are neither weaker
nor different.

## 3. HOUSE TRAP OBSERVED

The fills' value cell is chosen by the matcher, not by the caller: a fill
at value `0` takes *any* owned cell holding `0`, and the tool picks the
**next pass's index cell** (`aset "e1elm" "i10" "i11"`) because junk and
value cells are consumed in written order — 2E/D-d again, one layer up.
It is sound (the cell is read-only in the rule and still holds `0` when
the next pass claims it as a counter) and it is why `"zero"` is needed
only for the last fill.
-/

namespace Lax3Proofs.Refine.OrderSigProbe

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref
open Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax3Proofs.Refine.OrderSynth

/-! ## 1. The three passes as leaf operations, at symbolic cell names -/

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
sepref_synth mopCopy (d i s cnt one u : String) (N : ℕ) (src A₀ : List ℕ) (i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) (d, i) ∗
      hnCtxt arrayAssn src s ∗ hnCtxt natAssn N cnt ∗ hnCtxt natAssn 1 one ∗
      junkCell u)
    _ _ (d, i) (arrayAssn ×ₐ natAssn)
    (copyPass N src (A₀, i₀))

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
sepref_synth mopFill (a i v cnt one : String) (N w : ℕ) (A₀ : List ℕ) (i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) (a, i) ∗
      hnCtxt natAssn w v ∗ hnCtxt natAssn N cnt ∗ hnCtxt natAssn 1 one)
    _ _ (a, i) (arrayAssn ×ₐ natAssn)
    (fillPass N w (A₀, i₀))

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
sepref_synth mopOrd (a z r cnt one u : String) (N : ℕ) (rnk A₀ : List ℕ) (z₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, z₀) (a, z) ∗
      hnCtxt arrayAssn rnk r ∗ hnCtxt natAssn N cnt ∗ hnCtxt natAssn 1 one ∗
      junkCell u)
    _ _ (a, z) (arrayAssn ×ₐ natAssn)
    (ordPass N rnk (A₀, z₀))

/-! ## 2. The landed-name anchors -/

theorem mopCopy_landed (N : ℕ) (src A₀ : List ℕ) (i₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("cpd", "cpi") ∗
        hnCtxt arrayAssn src "cps" ∗ hnCtxt natAssn N "cpn" ∗ hnCtxt natAssn 1 "one" ∗
        junkCell "cpu")
      copySynth_impl Γ' ("cpd", "cpi") (arrayAssn ×ₐ natAssn) (copyPass N src (A₀, i₀)) :=
  ⟨_, mopCopy "cpd" "cpi" "cps" "cpn" "one" "cpu" N src A₀ i₀⟩

theorem mopFill_landed (N v : ℕ) (A₀ : List ℕ) (i₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) ("fla", "fli") ∗
        hnCtxt natAssn v "flv" ∗ hnCtxt natAssn N "fln" ∗ hnCtxt natAssn 1 "one")
      fillSynth_impl Γ' ("fla", "fli") (arrayAssn ×ₐ natAssn) (fillPass N v (A₀, i₀)) :=
  ⟨_, mopFill "fla" "fli" "flv" "fln" "one" N v A₀ i₀⟩

theorem mopOrd_landed (n : ℕ) (rnk A₀ : List ℕ) (z₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, z₀) ("ord", "z") ∗
        hnCtxt arrayAssn rnk "rnk" ∗ hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗
        junkCell "rz")
      ordSynth_impl Γ' ("ord", "z") (arrayAssn ×ₐ natAssn) (ordPass n rnk (A₀, z₀)) :=
  ⟨_, mopOrd "ord" "z" "rnk" "n" "one" "rz" n rnk A₀ z₀⟩

attribute [sepref_fr_rules] mopCopy mopFill mopOrd

/-! ## 3. Program size -/

/-- The number of `Com` nodes in a program. -/
def comSize : Com → ℕ
  | .skip => 1
  | .const _ _ => 1
  | .copy _ _ => 1
  | .binop _ _ _ _ => 1
  | .aget _ _ _ => 1
  | .aset _ _ _ => 1
  | .seq c d => 1 + comSize c + comSize d
  | .ite _ c d => 1 + comSize c + comSize d
  | .while _ c => 1 + comSize c

#guard comSize copySynth_impl = 8
#guard comSize fillSynth_impl = 6
#guard comSize ordSynth_impl = 8

-- the reference points of §0's table
#guard comSize Lax13Proofs.Refine.BfsQSynth.bfsQSynth_impl = 92
#guard comSize Lax3Proofs.Refine.ElimSynth3.elimSynth_impl = 205
#guard comSize elimOrdSynth_impl = 214

/-! ## 4. The merge wall -/

noncomputable def mergeTest (n : ℕ) (off gof : List ℕ) : NRest FS ECost :=
  bindT (copyPass (n + 1) off (gof, 0)) fun sv1 => copyPass (n + 1) sv1.1 (off, 0)

set_option maxHeartbeats 400000 in
set_option linter.unusedVariables false in
sepref_synth mergeTestSplit (n : ℕ) (off gof : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (gof, 0) ("gof", "i1") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (off, 0) ("off", "i7") ∗
      hnCtxt natAssn (n + 1) "bn1" ∗ hnCtxt natAssn 1 "one" ∗ junkCell "u1")
    _ _ ("off", "i7") (arrayAssn ×ₐ natAssn)
    (mergeTest n off gof)

set_option maxHeartbeats 400000 in
set_option linter.unreachableTactic false in
/-- The same program, with the destination's array and index owned as two
conjuncts rather than one product: the tool refuses. -/
example (n : ℕ) (off gof : List ℕ) : True := by
  fail_if_success
    (have : hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (gof, 0) ("gof", "i1") ∗
        hnCtxt arrayAssn off "off" ∗ hnCtxt natAssn 0 "i7" ∗
        hnCtxt natAssn (n + 1) "bn1" ∗ hnCtxt natAssn 1 "one" ∗ junkCell "u1")
      Com.skip (□ : Assn) ("off", "i7") (arrayAssn ×ₐ natAssn)
      (mergeTest n off gof) := by sepref)
  trivial

/-! ## 5. Prefixes of the phase -/

noncomputable def pre5 (n ns W : ℕ)
    (off tgt gof gtg alvj alv doff dtg d1off d1tg : List ℕ) : NRest FS ECost :=
  bindT (copyPass (n + 1) off (gof, 0)) fun _ =>
  bindT (copyPass ns tgt (gtg, 0)) fun _ =>
  bindT (copyPass n alvj (alv, 0)) fun _ =>
  bindT (copyPass (n + 1) d1off (doff, 0)) fun _ =>
  copyPass W d1tg (dtg, 0)

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
sepref_synth pre5Synth (n ns W : ℕ)
    (off tgt gof gtg alvj alv doff dtg d1off d1tg : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (gof, 0) ("gof", "i1") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (off, 0) ("off", "i7") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (gtg, 0) ("gtg", "i2") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (tgt, 0) ("tgt", "i8") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (alv, 0) ("alv", "i3") ∗
      hnCtxt arrayAssn alvj "alvj" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (doff, 0) ("doff", "i5") ∗
      hnCtxt arrayAssn d1off "d1off" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (dtg, 0) ("dtg", "i6") ∗
      hnCtxt arrayAssn d1tg "d1tg" ∗
      hnCtxt natAssn (n + 1) "bn1" ∗ hnCtxt natAssn ns "bns" ∗
      hnCtxt natAssn n "bn" ∗ hnCtxt natAssn W "bw" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗ junkCell "u1")
    _ _ ("dtg", "i6") (arrayAssn ×ₐ natAssn)
    (pre5 n ns W off tgt gof gtg alvj alv doff dtg d1off d1tg)

noncomputable def pre9 (n ns W : ℕ)
    (off tgt gof gtg alvj alv doff dtg d1off d1tg e1elm e1bh : List ℕ) : NRest FS ECost :=
  bindT (copyPass (n + 1) off (gof, 0)) fun sv1 =>
  bindT (copyPass ns tgt (gtg, 0)) fun sv2 =>
  bindT (copyPass n alvj (alv, 0)) fun _ =>
  bindT (copyPass (n + 1) d1off (doff, 0)) fun _ =>
  bindT (copyPass W d1tg (dtg, 0)) fun _ =>
  bindT (copyPass (n + 1) sv1.1 (off, 0)) fun _ =>
  bindT (copyPass ns sv2.1 (tgt, 0)) fun _ =>
  bindT (fillPass n 0 (e1elm, 0)) fun _ =>
  fillPass (n + 1) 0 (e1bh, 0)

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
sepref_synth pre9Synth (n ns W : ℕ)
    (off tgt gof gtg alvj alv doff dtg d1off d1tg e1elm e1bh : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (gof, 0) ("gof", "i1") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (off, 0) ("off", "i7") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (gtg, 0) ("gtg", "i2") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (tgt, 0) ("tgt", "i8") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (alv, 0) ("alv", "i3") ∗
      hnCtxt arrayAssn alvj "alvj" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (doff, 0) ("doff", "i5") ∗
      hnCtxt arrayAssn d1off "d1off" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (dtg, 0) ("dtg", "i6") ∗
      hnCtxt arrayAssn d1tg "d1tg" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (e1elm, 0) ("e1elm", "i10") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (e1bh, 0) ("e1bh", "i11") ∗
      hnCtxt natAssn (n + 1) "bn1" ∗ hnCtxt natAssn ns "bns" ∗
      hnCtxt natAssn n "bn" ∗ hnCtxt natAssn W "bw" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗ junkCell "u1")
    _ _ ("e1bh", "i11") (arrayAssn ×ₐ natAssn)
    (pre9 n ns W off tgt gof gtg alvj alv doff dtg d1off d1tg e1elm e1bh)

noncomputable def pre13 (n ns W : ℕ)
    (off tgt gof gtg alvj alv doff dtg ooff : List ℕ)
    (d1off d1tg e1elm e1bh e2rnk e2elm e2bh ord : List ℕ) : NRest FS ECost :=
  bindT (copyPass (n + 1) off (gof, 0)) fun sv1 =>
  bindT (copyPass ns tgt (gtg, 0)) fun sv2 =>
  bindT (copyPass n alvj (alv, 0)) fun _ =>
  bindT (copyPass (n + 1) d1off (doff, 0)) fun _ =>
  bindT (copyPass W d1tg (dtg, 0)) fun _ =>
  bindT (copyPass (n + 1) sv1.1 (off, 0)) fun _ =>
  bindT (copyPass ns sv2.1 (tgt, 0)) fun _ =>
  bindT (fillPass n 0 (e1elm, 0)) fun _ =>
  bindT (fillPass (n + 1) 0 (e1bh, 0)) fun _ =>
  bindT (ordPass n e2rnk (ord, 0)) fun _ =>
  bindT (fillPass n 0 (e2elm, 0)) fun _ =>
  bindT (fillPass (n + 1) 0 (e2bh, 0)) fun _ =>
  fillPass (n + 1) 0 (ooff, 0)

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
sepref_synth pre13Synth (n ns W : ℕ)
    (off tgt gof gtg alvj alv doff dtg ooff : List ℕ)
    (d1off d1tg e1elm e1bh e2rnk e2elm e2bh ord : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (gof, 0) ("gof", "i1") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (off, 0) ("off", "i7") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (gtg, 0) ("gtg", "i2") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (tgt, 0) ("tgt", "i8") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (alv, 0) ("alv", "i3") ∗
      hnCtxt arrayAssn alvj "alvj" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (doff, 0) ("doff", "i5") ∗
      hnCtxt arrayAssn d1off "d1off" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (dtg, 0) ("dtg", "i6") ∗
      hnCtxt arrayAssn d1tg "d1tg" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (e1elm, 0) ("e1elm", "i10") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (e1bh, 0) ("e1bh", "i11") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (ord, 0) ("ord", "i13") ∗
      hnCtxt arrayAssn e2rnk "e2rnk" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (e2elm, 0) ("e2elm", "i14") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (e2bh, 0) ("e2bh", "i15") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (ooff, 0) ("ooff", "i16") ∗
      hnCtxt natAssn (n + 1) "bn1" ∗ hnCtxt natAssn ns "bns" ∗
      hnCtxt natAssn n "bn" ∗ hnCtxt natAssn W "bw" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗ junkCell "u1")
    _ _ ("ooff", "i16") (arrayAssn ×ₐ natAssn)
    (pre13 n ns W off tgt gof gtg alvj alv doff dtg ooff
      d1off d1tg e1elm e1bh e2rnk e2elm e2bh ord)

noncomputable def pre18 (n ns W : ℕ)
    (off tgt gof gtg alvj alv doff dtg ooff noff stf sta std ste : List ℕ)
    (d1off d1tg e1elm e1bh e2rnk e2elm e2bh ord : List ℕ) : NRest FS ECost :=
  bindT (copyPass (n + 1) off (gof, 0)) fun sv1 =>
  bindT (copyPass ns tgt (gtg, 0)) fun sv2 =>
  bindT (copyPass n alvj (alv, 0)) fun _ =>
  bindT (copyPass (n + 1) d1off (doff, 0)) fun _ =>
  bindT (copyPass W d1tg (dtg, 0)) fun _ =>
  bindT (copyPass (n + 1) sv1.1 (off, 0)) fun _ =>
  bindT (copyPass ns sv2.1 (tgt, 0)) fun _ =>
  bindT (fillPass n 0 (e1elm, 0)) fun _ =>
  bindT (fillPass (n + 1) 0 (e1bh, 0)) fun _ =>
  bindT (ordPass n e2rnk (ord, 0)) fun _ =>
  bindT (fillPass n 0 (e2elm, 0)) fun _ =>
  bindT (fillPass (n + 1) 0 (e2bh, 0)) fun _ =>
  bindT (fillPass (n + 1) 0 (ooff, 0)) fun _ =>
  bindT (fillPass (n + 1) 0 (noff, 0)) fun _ =>
  bindT (fillPass n 0 (stf, 0)) fun _ =>
  bindT (fillPass n 0 (sta, 0)) fun _ =>
  bindT (fillPass n 0 (std, 0)) fun _ =>
  fillPass n 0 (ste, 0)

set_option maxHeartbeats 8000000 in
set_option linter.unusedVariables false in
sepref_synth pre18Synth (n ns W : ℕ)
    (off tgt gof gtg alvj alv doff dtg ooff noff stf sta std ste : List ℕ)
    (d1off d1tg e1elm e1bh e2rnk e2elm e2bh ord : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (gof, 0) ("gof", "i1") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (off, 0) ("off", "i7") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (gtg, 0) ("gtg", "i2") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (tgt, 0) ("tgt", "i8") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (alv, 0) ("alv", "i3") ∗
      hnCtxt arrayAssn alvj "alvj" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (doff, 0) ("doff", "i5") ∗
      hnCtxt arrayAssn d1off "d1off" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (dtg, 0) ("dtg", "i6") ∗
      hnCtxt arrayAssn d1tg "d1tg" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (e1elm, 0) ("e1elm", "i10") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (e1bh, 0) ("e1bh", "i11") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (ord, 0) ("ord", "i13") ∗
      hnCtxt arrayAssn e2rnk "e2rnk" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (e2elm, 0) ("e2elm", "i14") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (e2bh, 0) ("e2bh", "i15") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (ooff, 0) ("ooff", "i16") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (noff, 0) ("noff", "i17") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (stf, 0) ("stf", "i18") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (sta, 0) ("sta", "i19") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (std, 0) ("std", "i20") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (ste, 0) ("ste", "i21") ∗
      hnCtxt natAssn (n + 1) "bn1" ∗ hnCtxt natAssn ns "bns" ∗
      hnCtxt natAssn n "bn" ∗ hnCtxt natAssn W "bw" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗ junkCell "u1")
    _ _ ("ste", "i21") (arrayAssn ×ₐ natAssn)
    (pre18 n ns W off tgt gof gtg alvj alv doff dtg ooff noff stf sta std ste
      d1off d1tg e1elm e1bh e2rnk e2elm e2bh ord)


-- the four rows of §0's table, pinned
#guard comSize pre5Synth_impl = 44
#guard comSize pre9Synth_impl = 76
#guard comSize pre13Synth_impl = 106
#guard comSize pre18Synth_impl = 141

/-! ## 6. Signature mode

The same two prefixes again, this time as `hfref` signatures — one
abstract-argument record, the ownership boundary as data, no hand-written
`hnRefine` goal (`SignaturePrep`'s `wideRS` control at this campaign's
own scale). The `#guard`s pin the synthesized implementation record
against the direct-mode synthesis, so this checks more than extensional
agreement. -/

structure Pre5Args where
  n : ℕ
  ns : ℕ
  W : ℕ
  off : List ℕ
  tgt : List ℕ
  gof : List ℕ
  gtg : List ℕ
  alvj : List ℕ
  alv : List ℕ
  doff : List ℕ
  dtg : List ℕ
  d1off : List ℕ
  d1tg : List ℕ

/-- Reducible, so signature preparation exposes precisely the ownership
boundary `pre5Synth`'s written goal has. -/
abbrev pre5RS : (Pre5Args → Unit → Assn) × (Pre5Args → Unit → Assn) :=
  ((fun x _ =>
      hnCtxt (arrayAssn ×ₐ natAssn) (x.gof, 0) ("gof", "i1") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.off, 0) ("off", "i7") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.gtg, 0) ("gtg", "i2") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.tgt, 0) ("tgt", "i8") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.alv, 0) ("alv", "i3") ∗
      hnCtxt arrayAssn x.alvj "alvj" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.doff, 0) ("doff", "i5") ∗
      hnCtxt arrayAssn x.d1off "d1off" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.dtg, 0) ("dtg", "i6") ∗
      hnCtxt arrayAssn x.d1tg "d1tg" ∗
      hnCtxt natAssn (x.n + 1) "bn1" ∗ hnCtxt natAssn x.ns "bns" ∗
      hnCtxt natAssn x.n "bn" ∗ hnCtxt natAssn x.W "bw" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗ junkCell "u1"),
    (fun x _ =>
      junkArray "doff" ∗ junkCell "i5" ∗ junkArray "alv" ∗ junkCell "i3" ∗
      junkArray "gtg" ∗ junkCell "i2" ∗ (junkArray "gof" ∗ junkCell "i1") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.off, 0) ("off", "i7") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.tgt, 0) ("tgt", "i8") ∗
      hnCtxt arrayAssn x.alvj "alvj" ∗ hnCtxt arrayAssn x.d1off "d1off" ∗
      hnCtxt arrayAssn x.d1tg "d1tg" ∗
      hnCtxt natAssn (x.n + 1) "bn1" ∗ hnCtxt natAssn x.ns "bns" ∗
      hnCtxt natAssn x.n "bn" ∗ hnCtxt natAssn x.W "bw" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗ junkCell "u1"))

set_option maxHeartbeats 8000000 in
set_option linter.unusedVariables false in
sepref_synth pre5FromSignature :
    ((fun _ : Unit => (_, _)),
      fun x : Pre5Args =>
        pre5 x.n x.ns x.W x.off x.tgt x.gof x.gtg x.alvj x.alv x.doff x.dtg
          x.d1off x.d1tg) ∈
      hfref (fun _ : Pre5Args => True) pre5RS (fun _ _ => arrayAssn ×ₐ natAssn)

#guard pre5FromSignature_impl () = (("dtg", "i6"), pre5Synth_impl)

structure Pre18Args where
  n : ℕ
  ns : ℕ
  W : ℕ
  off : List ℕ
  tgt : List ℕ
  gof : List ℕ
  gtg : List ℕ
  alvj : List ℕ
  alv : List ℕ
  doff : List ℕ
  dtg : List ℕ
  ooff : List ℕ
  noff : List ℕ
  stf : List ℕ
  sta : List ℕ
  std : List ℕ
  ste : List ℕ
  d1off : List ℕ
  d1tg : List ℕ
  e1elm : List ℕ
  e1bh : List ℕ
  e2rnk : List ℕ
  e2elm : List ℕ
  e2bh : List ℕ
  ord : List ℕ

abbrev pre18RS : (Pre18Args → Unit → Assn) × (Pre18Args → Unit → Assn) :=
  ((fun x _ =>
      hnCtxt (arrayAssn ×ₐ natAssn) (x.gof, 0) ("gof", "i1") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.off, 0) ("off", "i7") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.gtg, 0) ("gtg", "i2") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.tgt, 0) ("tgt", "i8") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.alv, 0) ("alv", "i3") ∗
      hnCtxt arrayAssn x.alvj "alvj" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.doff, 0) ("doff", "i5") ∗
      hnCtxt arrayAssn x.d1off "d1off" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.dtg, 0) ("dtg", "i6") ∗
      hnCtxt arrayAssn x.d1tg "d1tg" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.e1elm, 0) ("e1elm", "i10") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.e1bh, 0) ("e1bh", "i11") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.ord, 0) ("ord", "i13") ∗
      hnCtxt arrayAssn x.e2rnk "e2rnk" ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.e2elm, 0) ("e2elm", "i14") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.e2bh, 0) ("e2bh", "i15") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.ooff, 0) ("ooff", "i16") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.noff, 0) ("noff", "i17") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.stf, 0) ("stf", "i18") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.sta, 0) ("sta", "i19") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.std, 0) ("std", "i20") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (x.ste, 0) ("ste", "i21") ∗
      hnCtxt natAssn (x.n + 1) "bn1" ∗ hnCtxt natAssn x.ns "bns" ∗
      hnCtxt natAssn x.n "bn" ∗ hnCtxt natAssn x.W "bw" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗ junkCell "u1"),
    (fun x _ =>
      junkArray "std" ∗ junkCell "i20" ∗ junkArray "sta" ∗ junkCell "i19" ∗
      junkArray "stf" ∗ junkCell "i18" ∗ junkArray "noff" ∗ junkCell "i17" ∗
      junkArray "ooff" ∗ junkCell "i16" ∗ junkArray "e2bh" ∗ junkCell "i15" ∗
      junkArray "e2elm" ∗ junkCell "i14" ∗ junkArray "ord" ∗ junkCell "i13" ∗
      junkArray "e1bh" ∗ junkCell "i11" ∗ junkArray "e1elm" ∗ junkCell "i10" ∗
      junkArray "tgt" ∗ junkCell "i8" ∗ junkArray "off" ∗ junkCell "i7" ∗
      junkArray "dtg" ∗ junkCell "i6" ∗ junkArray "doff" ∗ junkCell "i5" ∗
      junkArray "alv" ∗ junkCell "i3" ∗ junkArray "gtg" ∗ junkCell "i2" ∗
      (junkArray "gof" ∗ junkCell "i1") ∗
      hnCtxt arrayAssn x.alvj "alvj" ∗ hnCtxt arrayAssn x.d1off "d1off" ∗
      hnCtxt arrayAssn x.d1tg "d1tg" ∗ hnCtxt arrayAssn x.e2rnk "e2rnk" ∗
      hnCtxt natAssn (x.n + 1) "bn1" ∗ hnCtxt natAssn x.ns "bns" ∗
      hnCtxt natAssn x.n "bn" ∗ hnCtxt natAssn x.W "bw" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗ junkCell "u1"))

set_option maxHeartbeats 8000000 in
set_option linter.unusedVariables false in
sepref_synth pre18FromSignature :
    ((fun _ : Unit => (_, _)),
      fun x : Pre18Args =>
        pre18 x.n x.ns x.W x.off x.tgt x.gof x.gtg x.alvj x.alv x.doff x.dtg
          x.ooff x.noff x.stf x.sta x.std x.ste x.d1off x.d1tg x.e1elm x.e1bh
          x.e2rnk x.e2elm x.e2bh x.ord) ∈
      hfref (fun _ : Pre18Args => True) pre18RS (fun _ _ => arrayAssn ×ₐ natAssn)

#guard pre18FromSignature_impl () = (("ste", "i21"), pre18Synth_impl)

/-! ## 7. Axioms

Every principal declaration of this file, at the kernel three. -/

#print axioms mopCopy
#print axioms mopFill
#print axioms mopOrd
#print axioms mopCopy_landed
#print axioms mopFill_landed
#print axioms mopOrd_landed
#print axioms mergeTestSplit
#print axioms pre5Synth
#print axioms pre9Synth
#print axioms pre13Synth
#print axioms pre18Synth
#print axioms pre5FromSignature
#print axioms pre18FromSignature

end Lax3Proofs.Refine.OrderSigProbe
