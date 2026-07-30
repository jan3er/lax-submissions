import Lax13Proofs.Refine.Codegen.Cash
import Lax13Proofs.Refine.Examples.BfsQ

/-!
# P7 wave B — the queue BFS at the synthesis layer

Wave A (`Refine/Examples/BfsQ.lean`) proved the queue-based masked
depth-capped search correct and linear at the `NRest` layer. This file is
the second half of the gate: the same program in the form
`sepref_synth` can translate, the tower repairs that form needed, and —
where the pipeline still stalls — the exact obligation that stalls it.

**What landed.** The fill loop synthesizes mechanically (§5), which is
the first whole loop of the gate program to reach a deep `Ir.Com`. Four
pipeline defects were found and three fixed; the fourth is a
combinatorial blow-up in the translate driver, recorded in §7 with a
measurement rather than a workaround.

## Judgment calls (P7/D-b…)

**P7/D-ba — `conjunctsSplit` must not `whnf` a pair projection**
(`Sepref/Frame.lean`, fixed). Splitting `hnCtxt (A ×ₐ B) s c` produced
the *raw projection* `s.1` (`Expr.proj`), while `hnCtxt_prodAssn`'s
rewrite — the other half of `sepref_ac` — produces the *application*
`Prod.fst s`. The two terms are the same term and `isDefEq` sees that,
but `ac_rfl` compares atoms syntactically, so a permutation that needs
both spellings cannot close. This is P6's finding (3), "two `arrayAssn`
conjuncts in one `prodAssn` loop state trip `proveConjEq`", in full: the
two-array state is simply the smallest state whose match needs a
*permutation* on top of the split. One-line fix; a two-array loop state
then synthesizes and the whole package rebuilds unchanged.

**P7/D-bb — an in-place successor is its own operation.** P6/D-u
recorded that the operator phase does not backtrack across rule choice,
so `hnr_mop_binop` (junk destination) always beats `hnr_mop_binop_self`
(in place) whenever a scratch cell is free. Every counter in this
program — the fill index, the queue head, the queue tail, the scan index
— must be bumped *in place*, because it is a component of a loop state
and the loop rule fixes that state's cells; and every one of them is
bumped at a point where an inner loop's scratch cells are still junk and
therefore available. The two facts are incompatible, and no ordering of
the program repairs it. `mopSucc` is the fix that costs no tower change:
a distinct abstract operation, definitionally `mopBinop .add m 1`, with
exactly one rule, which is the in-place one. It is P6/D-u's "a
`mop_move` with a live destination", specialized to `+1`.

**P7/D-bc — the array analogue of the branch-merge rules was missing.**
`Sepref/Frame.lean` has `MERGE_natAssn_junk` and its two one-sided forms
and no `arrayAssn` counterpart, and `mergeSolve`'s pairing key did not
recognise `junkArray` at all. A branch that stores into an array and one
that does not therefore stalled with "`junkArray "dist"` has no
partner". The key is a one-line fix in `Frame.lean`; the three rules are
registered here, because `sepref_frame_merge_rules` is an extensible
database and this is what it is for.

**P7/D-bd — the drain loop's variant is left to the next wave.** `popF'`
differs from wave A's `popF` by one `pack4` (the inner loop's state has
to be *built* — `hnr_while_var` takes the state as a single conjunct,
and wave A's `popF` hands `scanLoop` a tuple literal). Its
`LOOP_VARIANT` therefore does not transfer from `drain_variant` by
rewriting, as `fill_variant'` and `scan_variant'` do; it needs
`popF_hd`'s argument re-run under one `consume`. That is bookkeeping,
not mathematics, and it is not on the critical path while §7's blocker
stands.
-/

namespace Lax13Proofs.Refine

namespace BfsQSynth

open Bfs BfsQ Sepref Ir NRest Codegen

/-! ## 1. An in-place successor (P7/D-bb) -/

/-- `x := x + 1`, as an operation of its own so that the operator phase
cannot route it through a scratch cell. -/
noncomputable def mopSucc (m : ℕ) : NRest ℕ ECost := mopBinop .add m 1

theorem mopSucc_eq (m : ℕ) : mopSucc m = mopBinop .add m 1 := rfl

/-- Its only rule, and it is the in-place one. -/
@[sepref_fr_rules]
theorem hnr_mop_succ (x z : String) (m : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn 1 z) (.binop .add x x z)
      (hnCtxt natAssn 1 z) x natAssn (mopSucc m) := by
  rw [mopSucc_eq]; exact hnr_mop_binop_self .add x z m 1

-- so that `hnr_mop_binop`'s `isDefEq` does not see through it
attribute [irreducible] mopSucc

/-! ## 2. Merging two branches that write the same array (P7/D-bc) -/

@[sepref_frame_merge_rules]
theorem MERGE_arrayAssn_junk (xs ys : List ℕ) (a : String) :
    MERGE (hnCtxt arrayAssn xs a) (hnCtxt arrayAssn ys a) (junkArray a) :=
  ⟨arrayAssn_entails_junkArray xs a, arrayAssn_entails_junkArray ys a⟩

@[sepref_frame_merge_rules]
theorem MERGE_arrayAssn_junk_left (ys : List ℕ) (a : String) :
    MERGE (junkArray a) (hnCtxt arrayAssn ys a) (junkArray a) :=
  ⟨entails_refl _, arrayAssn_entails_junkArray ys a⟩

@[sepref_frame_merge_rules]
theorem MERGE_arrayAssn_junk_right (xs : List ℕ) (a : String) :
    MERGE (hnCtxt arrayAssn xs a) (junkArray a) (junkArray a) :=
  ⟨arrayAssn_entails_junkArray xs a, entails_refl _⟩

/-! ## 3. The program, in synthesizable form

Three changes to wave A's `bfsQ`, each forced by a rule of the pipeline
and each *cost-only*: the four in-place bumps go through `mopSucc`
(P7/D-bb); the inner loop's state is built with a `pack4`, because
`hnr_while_var` reads the state off a single `hnCtxt` conjunct; and the
sentinel `d+1` and the two zero counters are written inline rather than
bound, because a `LOOP_VARIANT` annotation cannot be supplied for a
variable the enclosing `hnr_bind` has abstracted. Each loop body is
*equal* to wave A's, so wave A's value, cost and variant lemmas transfer
by rewriting. -/

noncomputable def fillF' (sent : ℕ) : List ℕ × ℕ → NRest (List ℕ × ℕ) ECost := fun s =>
  bindT (mopAset s.1 s.2 sent) fun D => bindT (mopSucc s.2) fun i => mopPair D i

theorem fillF'_eq (sent : ℕ) : fillF' sent = fillF sent := by
  funext s; rw [fillF', fillF, mopSucc_eq]

noncomputable def fillLoop' (n sent : ℕ) (s₀ : List ℕ × ℕ) : NRest (List ℕ × ℕ) ECost :=
  irWhileIT (fun s => fillBf n s = true → fillP n s) (fillBf n) (fillF' sent) s₀

theorem fillLoop'_eq (n sent : ℕ) (s₀ : List ℕ × ℕ) :
    fillLoop' n sent s₀ = fillLoop n sent s₀ := by
  rw [fillLoop', fillLoop, fillF'_eq]

noncomputable def scanF' (sent dv1 : ℕ) (tgt alv : List ℕ) : St → NRest St ECost := fun s =>
  bindT (mopAget tgt s.2.2.2) fun u =>
    bindT (mopAget alv u) fun au =>
      bindT (mopAget s.1 u) fun du =>
        bindT (irIf (decide (0 < au))
            (irIf (decide (du = sent))
              (bindT (mopAset s.1 u dv1) fun D =>
                bindT (mopAset s.2.1 s.2.2.1 u) fun Q =>
                  bindT (mopSucc s.2.2.1) fun t => pack3 D Q t)
              (pack3 s.1 s.2.1 s.2.2.1))
            (pack3 s.1 s.2.1 s.2.2.1)) fun r =>
          bindT (mopSucc s.2.2.2) fun k => pack4 r.1 r.2.1 r.2.2 k

theorem scanF'_eq (sent dv1 : ℕ) (tgt alv : List ℕ) :
    scanF' sent dv1 tgt alv = scanF sent dv1 tgt alv := by
  funext s; rw [scanF', scanF, mopSucc_eq, mopSucc_eq]

noncomputable def scanLoop' (n sent dv1 kend : ℕ) (off tgt alv : List ℕ) (s₀ : St) :
    NRest St ECost :=
  irWhileIT (fun s => scanBf kend s = true → scanP n sent kend off tgt alv s) (scanBf kend)
    (scanF' sent dv1 tgt alv) s₀

theorem scanLoop'_eq (n sent dv1 kend : ℕ) (off tgt alv : List ℕ) (s₀ : St) :
    scanLoop' n sent dv1 kend off tgt alv s₀ = scanLoop n sent dv1 kend off tgt alv s₀ := by
  rw [scanLoop', scanLoop, scanF'_eq]

/-- One pop, with the row scan's state packed for the loop rule. -/
noncomputable def popF' (n d sent : ℕ) (off tgt alv : List ℕ) : St → NRest St ECost := fun s =>
  bindT (mopAget s.2.1 s.2.2.1) fun v =>
    bindT (mopAget s.1 v) fun dv =>
      bindT (mopSucc s.2.2.1) fun hd =>
        bindT (irIf (decide (dv < d))
            (bindT (mopBinop .add dv 1) fun dv1 =>
              bindT (mopAget off v) fun k0 =>
                bindT (mopBinop .add v 1) fun v1 =>
                  bindT (mopAget off v1) fun kend =>
                    bindT (pack4 s.1 s.2.1 s.2.2.2 k0) fun z0 =>
                      bindT (scanLoop' n sent dv1 kend off tgt alv z0)
                        fun r => pack3 r.1 r.2.1 r.2.2.1)
            (pack3 s.1 s.2.1 s.2.2.2)) fun r =>
          pack4 r.1 r.2.1 hd r.2.2

noncomputable def drainLoop' (n d sent : ℕ) (off tgt alv : List ℕ) (s₀ : St) : NRest St ECost :=
  irWhileIT (fun s => popBf s = true → popP n sent off tgt alv s) popBf
    (popF' n d sent off tgt alv) s₀

/-- **The gate program**, in synthesizable form: wave A's `bfsQ` without
its final projection (the tool has no rule at `returnT`, and the
projection is not needed — the export reads `dist` off the result
tuple's first component through `readout_arr`). -/
noncomputable def bfsQS (n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) : NRest St ECost :=
  bindT (mopPair dist₀ 0) fun p₀ =>
    bindT (fillLoop' n (d + 1) p₀) fun p =>
      bindT (mopAset p.1 src 0) fun D =>
        bindT (mopAset q₀ 0 src) fun Q =>
          bindT (mopAget alv src) fun a =>
            bindT (irIf (decide (0 < a)) (mopConstN 1) (mopConstN 0)) fun tl =>
              bindT (pack4 D Q 0 tl) fun st =>
                drainLoop' n d (d + 1) off tgt alv st

/-! ## 4. The variants the synthesis takes as annotations

Two of the three transfer from wave A by one rewrite, which is what
"cost-only change" means at this layer. The third is P7/D-bd. -/

theorem fill_variant' (n sent : ℕ) :
    LOOP_VARIANT (fun s => fillBf n s = true → fillP n s) (fillBf n) (fillF' sent)
      (fun s => n - s.2) := by
  rw [fillF'_eq]; exact fill_variant n sent

theorem scan_variant' (n sent dv1 kend : ℕ) (off tgt alv : List ℕ) :
    LOOP_VARIANT (fun s => scanBf kend s = true → scanP n sent kend off tgt alv s)
      (scanBf kend) (scanF' sent dv1 tgt alv) (fun s => kend - s.2.2.2) := by
  rw [scanF'_eq]; exact scan_variant n sent dv1 kend off tgt alv

/-! ## 5. The synthesis: the fill loop

The first whole loop of the gate program at a deep `Ir.Com`, produced by
the tool with no bespoke tactic work and no hand-written frame clause.
The `+1` is in place — P7/D-bb at work: with `mopBinop` it would have
landed in whichever scratch cell the caller happened to own first. -/

sepref_synth fillSynth (n sent : ℕ) (dist₀ : List ℕ)
    (hv : LOOP_VARIANT (fun s => fillBf n s = true → fillP n s) (fillBf n) (fillF' sent)
      (fun s => n - s.2)) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (dist₀, 0) ("dist", "i") ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn sent "sent" ∗ hnCtxt natAssn 1 "one")
    _ _ ("dist", "i") (arrayAssn ×ₐ natAssn)
    (fillLoop' n sent (dist₀, 0))

-- The synthesized program, pinned.
#guard fillSynth_impl =
  Com.while (Cond.lt (Operand.cell "i") (Operand.cell "n"))
    (Com.seq (Com.aset "dist" "i" "sent")
      (Com.seq (Com.binop Imp.Bop.add "i" "i" "one") Com.skip))

/-- The fill loop's synthesis with its variant discharged, stated at wave
A's own `fillLoop` — which is what makes wave A's `fillLoop_le` the
abstract bound this `Com` inherits. -/
theorem fillSynth' (n sent : ℕ) (dist₀ : List ℕ) :
    hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (dist₀, 0) ("dist", "i") ∗
        hnCtxt natAssn n "n" ∗ hnCtxt natAssn sent "sent" ∗ hnCtxt natAssn 1 "one")
      fillSynth_impl (hnCtxt natAssn n "n" ∗ hnCtxt natAssn sent "sent" ∗
        hnCtxt natAssn 1 "one") ("dist", "i") (arrayAssn ×ₐ natAssn)
      (fillLoop n sent (dist₀, 0)) := by
  rw [← fillLoop'_eq]; exact fillSynth n sent dist₀ (fill_variant' n sent)

/-! ## 6. Axioms -/

/-- info: 'Lax13Proofs.Refine.BfsQSynth.fillSynth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fillSynth

/-- info: 'Lax13Proofs.Refine.BfsQSynth.hnr_mop_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_succ

/-! ## 7. The blocker, measured (P7/D-be)

`sepref_synth` on `scanLoop'` — the innermost loop, a three-read body
with two nested branches — does **not** terminate usefully: it explores
for 3 min 22 s and reports a stall. The full program does not finish
inside 8 000 000 heartbeats (nine minutes of wall clock). The fill loop
above, one branch-free body, is under two seconds. The cause is not any
one rule; it is `transComb`'s retry discipline.

At every `bindT` the driver tries `hnr_seq` first and `hnr_bind` second
(`Sepref/Translate.lean`, `transComb`: on a stalled premise it
`st.restore`s and moves to the next rule). `hnr_seq` succeeds exactly
when the body's postcondition is binder-free, which for a body that
reads into a scratch cell it never is — so the driver translates the
*whole remaining program* under `hnr_seq`, discovers the frame does not
close, throws it away, and translates it again under `hnr_bind`. That is
a factor of two per `bindT`, compounding: the fill body has two, the
scan body six, the drain body ten with the scan body nested inside each.
The measured times fit `2^depth` to within the noise.

Three ways out, in increasing order of invasiveness, none of them taken
here because each is a change to P4's driver and P7's authorization is
for minimal repairs at a single site:

1. **Order the database so `hnr_bind` is tried before `hnr_seq`.**
   `hnr_bind` subsumes `hnr_seq` (its extra `IMP` premise is
   `entails_refl` exactly when `hnr_seq` applies), so the synthesized
   program is unchanged and the retry disappears. `register_label_attr`
   has no priority, so this needs one.
2. **Memoize `transGoal` on the goal's type.** The retried subtree is
   literally the same goal; the driver has no cache.
3. **Fail `hnr_seq` early**, on a syntactic check of whether the
   continuation's postcondition can be binder-free, before descending.

Until one of them lands, the gate's remaining chain — bounds
(`ir_bound_vcg`), cashing (`spec_of_hnRefine`), the `bfs_spec`-shaped
export and the five-vertex demo — has no synthesized `Ir.Com` for the
whole program to attach to. Everything else the chain needs is in place:
wave A's `bfsQ_correct` is the abstract bound, `readout_arr` is the
readout at `dist`, and the export's postcondition is
`QPost n d src G alv hsrc st'.1` composed with the drain state's first
projection.

## 8. Telemetry (P7 wave B's share of the gate numbers)

* **Line counts.** This file: **346 raw**, 60 blank, 172 comment,
  **114 lines of Lean** (the same nesting-aware scan wave A reports;
  it reproduces wave A's 1,015 on wave A's file). Wave A is 1,435 raw /
  1,015 Lean, so P7 stands at **1,781 raw / 1,129 Lean** against the
  baseline `RamBfs.lean`'s 1,201 raw and its cost of `51n + 44ns + 30`.
  Where this file's 114 go: the successor operation and its rule 6, the
  three merge rules 9, the synthesizable program with its six equations
  71, the two variants 6, the synthesis, its pin and its corollary 16,
  the axiom pins 6.

* **Bounds-annotation lines: 0** — P5's separate telemetry line has
  nothing to report yet, because the bounds pass has no whole-program
  `Com` to run on (§7).

* **Hand-written frame clauses: 0**, in this file and in wave A's. No
  `fri` call, no `sepConj` rearrangement, no `ac_rfl` on an assertion.
  The three `MERGE_arrayAssn_*` rules of §2 are *entailments between
  single conjuncts* registered in a database — the same shape as
  `Sepref/Frame.lean`'s own `MERGE_natAssn_junk`, and the same shape P4's
  telemetry counts as not-a-frame-clause — and they are consumed by
  `mergeSolve`, never applied by hand.

* **Wall clock**, warm build, `lake env lean`: this file 5.4 s against a
  3.8 s import-only baseline — **1.6 s** of elaboration for everything
  above, `fillSynth` included. The two measurements that did not land
  are in §7 (3 min 22 s to a stall for `scanLoop'`; the whole program
  does not finish in nine minutes). Whole package: 3,041 jobs, 50 s.

* **Tower repairs made** (both minimal, both flagged, full package
  rebuilt green at 3,040 jobs after each): `Sepref/Frame.lean`'s
  `conjunctsSplit` — `whnf`ed projections replaced by `projOf`, which
  reduces a literal pair and otherwise leaves `Prod.fst`/`Prod.snd`
  applied (P7/D-ba); `Sepref/Frame.lean`'s `mergeSolve` pairing key —
  one line, `junkArray` added beside `junkCell` (P7/D-bc).

* **Refuted before proved.** `mopSucc`'s rule was checked to be the one
  the driver picks *before* the program was written to depend on it: the
  fill loop's pinned `Com` is `binop add "i" "i" "one"`, in place. The
  control — the *same* synthesis at wave A's `fillF`, with one extra
  `junkCell "t"` in the precondition — fails, and names the reason:
  "`hnr_mop_pair`: the rule's precondition conjuncts `hnCtxt arrayAssn ‹›
  "dist"`, `hnCtxt natAssn ‹› "i"` could not all be matched against the
  goal's `hnCtxt natAssn ‹› "t"`, …". The sum went to the scratch cell
  and the loop state can no longer be rebuilt. That is P6/D-u's finding,
  reproduced here as the reason the operation exists.
  `fillF'_eq`, `scanF'_eq` and `scanLoop'_eq` are the standing check
  that no program change in §3 is anything but cost.
-/

end BfsQSynth

end Lax13Proofs.Refine
