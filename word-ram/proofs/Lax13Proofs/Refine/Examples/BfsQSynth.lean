import Lax13Proofs.Refine.Codegen.Cash
import Lax13Proofs.Refine.Examples.BfsQ
import Lax13Proofs.Refine.NREST.FlattenCurrencies

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

**P7/D-bd is moot as of R0/D-b (ND-MC rebase P0.3).** No variant is
needed by anything: `Sepref/CombRules.lean`'s `hnr_while` reads
termination off the abstract loop's own non-failure, and it is the
`sepref_comb_rules` entry. The three `LOOP_VARIANT` hypotheses of
`bfsQSynth` below and the one of `fillSynth` are inert — kept because
those theorems are landed, not because the pipeline asks for them. Two
consequences for the next wave: the drain loop needs no re-run of
`popF_hd`'s argument at all, and the §3 distortion "the sentinel `d+1`
and the two zero counters are written inline rather than bound, because
a `LOOP_VARIANT` annotation cannot be supplied for a variable the
enclosing `hnr_bind` has abstracted" no longer has a cause — that
constraint on program shape is gone, and with it the only motive for
`Sepref/Translate.lean`'s `apply_assumption` fallback (P7/D-bh).
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

theorem popF'_eq (n d sent : ℕ) (off tgt alv : List ℕ) :
    popF' n d sent off tgt alv = popF n d sent off tgt alv := by
  funext s; simp only [popF', popF, mopSucc_eq, scanLoop'_eq]

theorem drainLoop'_eq (n d sent : ℕ) (off tgt alv : List ℕ) (s₀ : St) :
    drainLoop' n d sent off tgt alv s₀ = drainLoop n d sent off tgt alv s₀ := by
  rw [drainLoop', drainLoop, popF'_eq]

/-- …and so does the drain's (P7/D-bd, closed: wave A's `popF` now
builds the row scan's state itself, so the two bodies are the same
program and `popC` carries the three tuple steps). -/
theorem drain_variant' (n d : ℕ) (off tgt alv : List ℕ) :
    LOOP_VARIANT (fun s => popBf s = true → popP n (d + 1) off tgt alv s) popBf
      (popF' n d (d + 1) off tgt alv) (fun s => n - s.2.2.1) := by
  rw [popF'_eq]; exact drain_variant n d off tgt alv

/-! ## 5. The synthesis: the fill loop

The first whole loop of the gate program at a deep `Ir.Com`, produced by
the tool with no bespoke tactic work and no hand-written frame clause.
The `+1` is in place — P7/D-bb at work: with `mopBinop` it would have
landed in whichever scratch cell the caller happened to own first. -/

-- The variant annotation below is inert since R0/D-b: no rule in
-- `sepref_comb_rules` reads a `LOOP_VARIANT` any more. The signature
-- is kept because this synthesis theorem is landed capital.
set_option linter.unusedVariables false in
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

/-! ## 6. The synthesis: the whole program

Three nested loops, two nested branches inside the innermost one, a
tuple state carrying two arrays at every level. The tool produces the
`Ir.Com` with no bespoke tactic work, no hand-written frame clause and
three `LOOP_VARIANT` annotations — the three the abstract proof already
had. -/

set_option maxHeartbeats 1000000 in
-- The variant annotation below is inert since R0/D-b: no rule in
-- `sepref_comb_rules` reads a `LOOP_VARIANT` any more. The signature
-- is kept because this synthesis theorem is landed capital.
set_option linter.unusedVariables false in
sepref_synth bfsQSynth (n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ)
    (hf : LOOP_VARIANT (fun s => fillBf n s = true → fillP n s) (fillBf n) (fillF' (d + 1))
      (fun s => n - s.2))
    (hs : ∀ dv1 kend : ℕ, LOOP_VARIANT
      (fun s => scanBf kend s = true → scanP n (d + 1) kend off tgt alv s) (scanBf kend)
      (scanF' (d + 1) dv1 tgt alv) (fun s => kend - s.2.2.2))
    (hp : LOOP_VARIANT (fun s => popBf s = true → popP n (d + 1) off tgt alv s) popBf
      (popF' n d (d + 1) off tgt alv) (fun s => n - s.2.2.1)) :
  hnRefine (hnCtxt arrayAssn dist₀ "dist" ∗ hnCtxt arrayAssn q₀ "q" ∗
      hnCtxt natAssn 0 "i" ∗ hnCtxt natAssn 0 "head" ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗ hnCtxt arrayAssn alv "alv" ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
      hnCtxt natAssn src "src" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
      junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
      junkCell "du")
    _ _ ("dist", "q", "head", "tl")
    (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (bfsQS n d src off tgt alv dist₀ q₀)

-- The synthesized program, pinned.
#guard bfsQSynth_impl =
  Com.skip.seq
    ((Com.while (Cond.lt (Operand.cell "i") (Operand.cell "n"))
          ((Com.aset "dist" "i" "sent").seq ((Com.binop Imp.Bop.add "i" "i" "one").seq Com.skip))).seq
      ((Com.aset "dist" "src" "head").seq
        ((Com.aset "q" "head" "src").seq
          ((Com.aget "a" "alv" "src").seq
            ((Com.ite (Cond.lt (Operand.cell "head") (Operand.cell "a")) (Com.const "tl" 1) (Com.const "tl" 0)).seq
              ((Com.skip.seq (Com.skip.seq Com.skip)).seq
                (Com.while (Cond.lt (Operand.cell "head") (Operand.cell "tl"))
                  ((Com.aget "v" "q" "head").seq
                    ((Com.aget "dv" "dist" "v").seq
                      ((Com.binop Imp.Bop.add "head" "head" "one").seq
                        ((Com.ite (Cond.lt (Operand.cell "dv") (Operand.cell "d"))
                              ((Com.binop Imp.Bop.add "dv1" "dv" "one").seq
                                ((Com.aget "k0" "off" "v").seq
                                  ((Com.binop Imp.Bop.add "v1" "v" "one").seq
                                    ((Com.aget "kend" "off" "v1").seq
                                      ((Com.skip.seq (Com.skip.seq Com.skip)).seq
                                        ((Com.while (Cond.lt (Operand.cell "k0") (Operand.cell "kend"))
                                              ((Com.aget "u" "tgt" "k0").seq
                                                ((Com.aget "au" "alv" "u").seq
                                                  ((Com.aget "du" "dist" "u").seq
                                                    ((Com.ite (Cond.lt (Operand.lit 0) (Operand.cell "au"))
                                                          (Com.ite (Cond.eq (Operand.cell "du") (Operand.cell "sent"))
                                                            ((Com.aset "dist" "u" "dv1").seq
                                                              ((Com.aset "q" "tl" "u").seq
                                                                ((Com.binop Imp.Bop.add "tl" "tl" "one").seq
                                                                  (Com.skip.seq Com.skip))))
                                                            (Com.skip.seq Com.skip))
                                                          (Com.skip.seq Com.skip)).seq
                                                      ((Com.binop Imp.Bop.add "k0" "k0" "one").seq
                                                        (Com.skip.seq (Com.skip.seq Com.skip)))))))).seq
                                          (Com.skip.seq Com.skip)))))))
                              (Com.skip.seq Com.skip)).seq
                          (Com.skip.seq (Com.skip.seq Com.skip)))))))))))))

/-- The caller's ownership: the two scratch arrays, the CSR block
structure, the mask, the constants the operations read, and the eleven
scratch cells in the order the program consumes them. -/
def bfsQPre (n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) : Assn :=
  hnCtxt arrayAssn dist₀ "dist" ∗ hnCtxt arrayAssn q₀ "q" ∗
    hnCtxt natAssn 0 "i" ∗ hnCtxt natAssn 0 "head" ∗
    hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗ hnCtxt arrayAssn alv "alv" ∗
    hnCtxt natAssn n "n" ∗ hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
    hnCtxt natAssn src "src" ∗ hnCtxt natAssn 1 "one" ∗
    junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
    junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
    junkCell "du"

/-- …and what it still owns afterwards: everything but the four cells of
the result tuple, with every scratch cell dead again — the fill index
among them, which the drain does not use. -/
def bfsQFrame (n d src : ℕ) (off tgt alv : List ℕ) : Assn :=
  junkCell "a" ∗ hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn src "src" ∗ junkCell "i" ∗
    hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗ hnCtxt natAssn n "n" ∗
    hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗ hnCtxt natAssn 1 "one" ∗
    junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗ junkCell "k0" ∗ junkCell "v1" ∗
    junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "du"

/-- **The gate's synthesis theorem**: the deep `Ir.Com` above refines the
whole queue BFS, with every variant discharged and no hypothesis left. -/
theorem bfsQSynth' (n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) :
    hnRefine (bfsQPre n d src off tgt alv dist₀ q₀) bfsQSynth_impl
      (bfsQFrame n d src off tgt alv) ("dist", "q", "head", "tl")
      (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (bfsQS n d src off tgt alv dist₀ q₀) :=
  bfsQSynth n d src off tgt alv dist₀ q₀ (fill_variant' n (d + 1))
    (fun dv1 kend => scan_variant' n (d + 1) dv1 kend off tgt alv)
    (drain_variant' n d off tgt alv)


/-! ## 7. The abstract bound, transferred to `bfsQS`

`bfsQ_correct` is wave A's; `bfsQS` differs from `bfsQ` by three
cost-only steps (§3) and by not performing the final projection, which
the synthesized program has no rule for and does not need — the export
reads `dist` off the result tuple. `le_spec_of_bindT_returnT` (P7/T-c)
is what turns the second difference into a composition. -/

/-- The two programs, normalized: everything but the constants agrees. -/
theorem bfsQS_le_bfsQ (n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) :
    NRest.bindT (bfsQS n d src off tgt alv dist₀ q₀) (fun st' => NRest.returnT st'.1)
      ≤ NRest.consume (bfsQ n d src off tgt alv dist₀ q₀) (irUnit Currency.skip) := by
  simp only [bfsQS, bfsQ, fillLoop'_eq, drainLoop'_eq, mopPair_def, mopBinop_def, mopConstN_def,
    Imp.Bop.apply_add, binopCurrency_add, NRest.returnT_bindT, NRest.bindT_assoc_acost,
    NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume]
  exact NRest.consume_mono le_rfl (cost_le_add _ _)

/-- **The gate program's abstract bound.** The synthesized program's
abstract counterpart decides every masked-distance threshold up to the
cap, at `n` fill iterations, `n` pops, `ns` scanned slots and a
constant. -/
theorem bfsQS_correct {n ns d : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}
    {src : ℕ} {dist₀ q₀ : List ℕ} (hc : Csr n ns G off tgt alv)
    (hsrc : src < n) (hdlen : dist₀.length = n) (hqlen : q₀.length = n) :
    bfsQS n d src off tgt alv dist₀ q₀
      ≤ NRest.spec (fun st' : St => QPost n d src G alv hsrc st'.1)
          (fun _ => irUnit Currency.skip + liftACost (bfsBudget n ns)) := by
  refine le_spec_of_bindT_returnT (le_trans (bfsQS_le_bfsQ n d src off tgt alv dist₀ q₀) ?_)
  rw [← Sepref.consume_spec]
  exact NRest.consume_mono (bfsQ_correct hc hsrc hdlen hqlen) le_rfl

/-- **The arena, pinned beside the bound (design note P7/S-1).** The
graph the exported postcondition measures distance in is `G` with the
mask's dead vertices isolated: an edge survives exactly when it is an
edge of `G` and both endpoints are alive, "alive" being a nonzero entry
of the `alv` array. That is the shape-match with `RamBfs.bfs_spec`'s
`masked G M`, made inspectable rather than asserted. -/
theorem masked_maskOf_adj {n : ℕ} {G : SimpleGraph (Fin n)} {alv : List ℕ} {u v : Fin n} :
    (Bfs.masked G (maskOf n alv)).Adj u v
      ↔ G.Adj u v ∧ 0 < alv[(u : ℕ)]! ∧ 0 < alv[(v : ℕ)]! := by
  simp [Bfs.masked_adj, maskOf]

/-! ## 8. The demo: `RamBfs`'s five-vertex arena, run on the synthesized
program (ledger D4)

The path `0—1—2—3` with an isolated vertex `4`, six adjacency slots —
`Refine/Examples/BfsQ.lean` §1's arena, which is `RamBfs`'s own. The
`Com` below is the one `sepref_synth` produced, evaluated by
`Ir/Semantics.lean`'s own evaluator; what comes out of the `dist` array
is `#guard`ed against wave A's computable twin `bfsTw`, which §1 of that
file already checked against `RamBfs`'s four published readings and
against P1's independent level-based twin. So these are runs of the
*synthesized machine program* checked against the *abstract* one. -/

/-- The caller's initial store: the two scratch arrays are junk (all
zero), the constants are the ones `bfsQPre` owns. -/
def demoState (dcap src : ℕ) (a2 : ℕ) : Ir.State :=
  Ir.State.ofPairs
    [("i", 0), ("head", 0), ("n", 5), ("sent", dcap + 1), ("d", dcap), ("src", src),
      ("one", 1), ("a", 0), ("tl", 0), ("v", 0), ("dv", 0), ("dv1", 0), ("k0", 0),
      ("v1", 0), ("kend", 0), ("u", 0), ("au", 0), ("du", 0)]
    [("dist", [0, 0, 0, 0, 0]), ("q", [0, 0, 0, 0, 0]), ("off", demoOff),
      ("tgt", demoTgt), ("alv", demoAlv a2)]

/-- The `dist` array the synthesized program leaves. -/
def demoRun (dcap src a2 : ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 4000 bfsQSynth_impl (demoState dcap src a2)).bind fun p => p.1.arrs "dist"

-- mask on: every vertex of the path is reached
#guard demoRun 3 0 1 = some (bfsTw 5 3 0 demoOff demoTgt (demoAlv 1))
#guard demoRun 3 0 1 = some [0, 1, 2, 3, 4]
-- mask off at vertex 2: the path is cut there
#guard demoRun 3 0 0 = some (bfsTw 5 3 0 demoOff demoTgt (demoAlv 0))
#guard demoRun 3 0 0 = some [0, 1, 4, 4, 4]
-- the cap bites
#guard demoRun 1 0 1 = some (bfsTw 5 1 0 demoOff demoTgt (demoAlv 1))
#guard demoRun 0 0 1 = some (bfsTw 5 0 0 demoOff demoTgt (demoAlv 1))
-- and from a different source
#guard demoRun 3 2 1 = some (bfsTw 5 3 2 demoOff demoTgt (demoAlv 1))

-- **The negative control**: the masked run is not the unmasked one, and
-- the check can tell.
/--
error: Expression
  decide (demoRun 3 0 0 = some [0, 1, 2, 3, 4])
did not evaluate to `true`
-/
#guard_msgs in
#guard demoRun 3 0 0 = some [0, 1, 2, 3, 4]

/-! ## 9. Axioms -/

/-- info: 'Lax13Proofs.Refine.BfsQSynth.bfsQSynth'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bfsQSynth'

/-- info: 'Lax13Proofs.Refine.BfsQSynth.fillSynth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fillSynth

/-- info: 'Lax13Proofs.Refine.BfsQSynth.drain_variant'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms drain_variant'

/-- info: 'Lax13Proofs.Refine.BfsQSynth.bfsQS_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bfsQS_correct

/-- info: 'Lax13Proofs.Refine.BfsQSynth.hnr_mop_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_succ

/-! ## 10. What the blocker was, and what it cost (P7/D-be … P7/D-bh)

The first pass of this wave could not synthesize the row scan at all: it
explored for 3 min 22 s and stalled, and the whole program did not
finish inside 8 000 000 heartbeats. Three separate defects were behind
that, and they are worth separating because only one of them is the
`2^depth` story the first diagnosis told.

**P7/D-bf — `hnr_seq` before `hnr_bind`.** `hnr_bind` subsumes
`hnr_seq`: its extra premise is `∀ a, Γ₂ a ⊢ Γ'`, which `abstractPost`
closes by `entails_refl` exactly when the body's postcondition is
binder-free — which is exactly when `hnr_seq` applies. Whichever is
tried first, the program that comes out is the same `Com.seq c₁ c₂`;
but `hnr_seq` first translates the whole continuation, discovers the
frame mentions the bound value, throws it away, and `hnr_bind` does it
again. Two per `bindT`, compounding through a nested program. Fixed by
a *stable partition* in `transComb` (`combLast`): every rule keeps its
database order except `hnr_seq`, which moves to the back.

**P7/D-bg — the frame matcher admitted constant relators.** This was
the real stall, and `hnr_seq`-first had merely been hiding it behind a
long search. `hnCtxt R a c` unfolds to `R a c`, so `isDefEq` on a whole
conjunct can solve a metavariable *relator* by a constant function:
`hnCtxt ?A D ?c` matches `hnCtxt natAssn 1 "one"` at
`?A := fun _ => natAssn 1`, `?c := "one"`. `hnr_mop_pair` has an open
relator in both components, so the row scan's final tuple bound its
`dist` component to whichever cell the goal happened to list first —
here the constant `1` — and the branch merge then junked the array that
was supposed to be the result. The source pairs by the abstract term
before anything else (`prepare_fi_conv`'s `Termtab` key) and
`Frame.lean`'s own `mergeSolve` already did; `frameMatch` did not.
`absAgree` is that check, and it is one first-order `isDefEq`.

**P7/D-bh — `assumption` cannot instantiate a quantifier.** An *inner*
loop's `LOOP_VARIANT` is quantified: `scanLoop`'s offered distance and
row end are read from arrays, so the enclosing `hnr_bind` has abstracted
them and the caller can only supply `∀ dv1 kend, LOOP_VARIANT …`.
P4/D-cv's vehicle — "a hypothesis in the local context, and `assumption`
unifies `?V` with the caller's choice" — therefore had no nested-loop
instance at all. `apply_assumption` added to `fallbackTac`, after
`omega` (so the cheap closers still go first) and before `simp_all`
(which was grinding on the quantified goal instead of failing).

**The result.** Row scan: 3 min 22 s to a stall → **13 s** to a `Com`.
Whole program: did not finish in nine minutes → **50 s**. All three
changes are *output-preserving*: the full package rebuilds at 3,041
jobs with every pinned `#guard`/`#guard_msgs` synthesis across P4's
acceptance, P6's nine exercises and this file byte-identical. The one
pinned text that did change is P4's *legibility demo*
(`Sepref/Examples/Acceptance.lean` §5), where the two stalled-rule
reports now appear in the new order — `hnr_bind` before `hnr_seq`,
same two paragraphs, swapped. That is the intended effect of P7/D-bf
and it is re-pinned rather than suppressed.

## 11. The bounds obligation, diagnosed (P7/D-bj, P7/D-bk)

`bfsQSynth'` is the synthesized program and `bfsQS_correct` is its
abstract bound. What stands between them and a `bfs_spec`-shaped export
is one hypothesis of `Cash.lean`'s `spec_of_hnRefine`:

```
hbd : ∃ s' κ, Ir.BigStepB B bfsQSynth_impl s₀ s' κ
```

Everything after it is one application each (`spec_of_hnRefine`, then
`readout_arr` at `"dist"`). This section is what that hypothesis
actually costs, because the answer is not P5's.

### P7/D-bj — why it is not P5's ten lines

`Codegen/BigStepB.lean`'s `aset` rule carries `hk : k < xs.length`: a
store only steps when its index is in range. On P5's two toys every
store's index was the loop counter and the guard bounded it, so the
obligation was free, and P5's telemetry concluded "the annotation proper
is ~10 lines per program". Here the row scan performs `q[tl] := u`, and
`tl` is bounded by *nothing in the control flow*: `tl < n` holds because
the queue never receives more vertices than there are undiscovered live
ones — wave A's `room`/`undisc` counting argument (P7/D-d). A
`ir_bound_vcg` pass in the `Runs` direction has to re-prove it.

### P7/D-bk — the route taken, and the one not taken

The authorized preference was route 2: derive `BigStepB B` *along* an
existing `BigStep`, so that the run's own side conditions are given
rather than re-proved. The premise is real and worth recording, because
it retires exactly the expensive half:

* `BigStep`'s `aset` already carries `hk : k < xs.length` and its `aget`
  carries `hv : xs[k]? = some v`. **Following a derivation therefore
  hands over every in-range fact for free — the whole `room`/`undisc`
  counting of P7/D-bj disappears.**
* Comparing the two inductive definitions constructor by constructor,
  `BigStepB` differs from `BigStep` in exactly three places:
  `const` adds `n < B`, `binop` adds `op.apply m n < B`, and the four
  control constructors ask for `Cond.evalB B` where `BigStep` asks for
  `Cond.eval`. `skip`, `copy`, `aget`, `aset` and `seq` are identical.

So the residual is three `< B` facts and nothing else. What it is *not*
is state-local, and that is why the general lemma cannot be stated the
way the brief hoped. A hypothesis of the form "at any bounded operands
the result is bounded" is false for the only arithmetic this program
does: `x := y + 1` at `y = B - 1` leaves `B`. The bound on a `binop`
result is available only relative to where the run has got to — for
`head := head + one` it is `head < tl ≤ n < B`, and `tl ≤ n` is
maintained by the *previous* iteration's successful `q[tl] := u`. That
is an invariant, and an invariant threaded through a derivation is a
verification-condition generator: route 2's general lemma *is* route 1,
with the in-range obligations deleted.

**The recommendation, therefore, is a third shape** —
`BigStep.bigStepB_of_inv` in `Codegen/BigStepB.lean`, beside
`BigStep.bigStepB_of_eq`: an induction over an existing `BigStep` that
threads a caller-supplied `Inv : State → Prop` and asks only for the
three `< B` facts at the sites that create values. It is strictly
cheaper than `ir_bound_vcg` (no in-range goals, no `Runs` construction,
no termination), it is reusable by every synthesized program, and it is
the honest form of the brief's route 2. Per the brief's own instruction
— honesty over elegance — it is *not* forced into the state-local shape.

### The residual, per site, for this program

Written out so the next wave can price it. The invariant needs: `dist`
entries `≤ d + 1`, `q` entries `< n`, `off` entries `≤ ns`, `tl ≤ n`,
and the constants. Then:

| site | what bounds the result |
|---|---|
| `i := i + one` (fill) | the guard `i < n`, and `n < B` |
| `head := head + one` | the guard `head < tl` and `tl ≤ n` |
| `dv1 := dv + one` | `dv = dist[v] ≤ d + 1`, and `d + 1 < B` |
| `v1 := v + one` | `v = q[head] < n` |
| `tl := tl + one` | the *same iteration's* `q[tl] := u`, whose `hk` gives `tl < n` — the store fact doing the work |
| `k0 := k0 + one` | the guard `k0 < kend` and `kend = off[v1] ≤ ns` |
| `tl := 1`, `tl := 0` | literals, `1 < B` |
| `Cond.lt (.lit 0) (.cell "au")` | `0 < B` and `au = alv[u] < B` |

`tl ≤ n` is the interesting row: it is inductive, and the step that
maintains it is the store's own in-range side condition, not a counting
argument. That is P7/D-bj's cost, retired — but only along a derivation.
-/

/-! ## 12. The bounds pass, executed (P7/D-bn)

§11's recommendation, carried out. The general lemma is
`BigStep.bigStepB_of_inv` (`Codegen/BigStepB.lean`, judgment call
P7/D-bl); what is here is this program's annotation.

**P7/D-bn — the invariant is smaller than §11's table, because
`StateBound` does most of it.** §11 priced the pass over an invariant
carrying `dist ≤ d+1`, `q < n`, `off ≤ ns` and `tl ≤ n`. Three of those
four rows turn out to be unnecessary once the pass carries
`Ir.StateBound B` itself as a conjunct: `BigStepB`'s own state invariant
already says that every cell and every array entry is below the bound,
which is all a guard needs and all a *read* value needs. What is left is
the four facts arithmetic needs and a bound alone cannot give —

* `one` really holds `1` (otherwise `x := x + one` is not `x + 1`);
* `tl ≤ n`, which bounds `head + 1` through the loop guard `head < tl`;
* the queue's entries *below the tail* are vertices, which bounds
  `v + 1`;
* the target array's entries are vertices, which is what keeps the
  queue's entries vertices when `q[tl] := u` writes one.

`off ≤ ns` and `dist ≤ d+1` disappear entirely: `k0 + 1 ≤ kend < B`
comes from the guard and `StateBound`, and `dv + 1 ≤ d < B` likewise.
The one place a *store's* side condition does the work is still the one
§11 identified — `tl + 1 ≤ n` is read off `q[tl] := u`'s own
`hk : tl < q.length`. -/

section Bounds

/-- The caller's store as an `Ir.State`: the two scratch arrays, the
block structure, the mask, the five constants `bfsQPre` owns, and the
eleven scratch cells zeroed. `demoState` is its five-vertex instance. -/
def bfsQState (n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) : Ir.State :=
  Ir.State.ofPairs
    [("i", 0), ("head", 0), ("n", n), ("sent", d + 1), ("d", d), ("src", src),
      ("one", 1), ("a", 0), ("tl", 0), ("v", 0), ("dv", 0), ("dv1", 0), ("k0", 0),
      ("v1", 0), ("kend", 0), ("u", 0), ("au", 0), ("du", 0)]
    [("dist", dist₀), ("q", q₀), ("off", off), ("tgt", tgt), ("alv", alv)]

/-! ### Reading a guard

Three inversions of `Ir.Cond.eval`, one per guard shape the program
uses. -/

theorem eval_lt_cells {s : Ir.State} {x y : String} {r : Bool}
    (h : (Ir.Cond.lt (.cell x) (.cell y)).eval s = some r) :
    ∃ a b : ℕ, s.vars x = some a ∧ s.vars y = some b ∧ r = decide (a < b) := by
  rw [Ir.Cond.eval_lt, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rfl⟩ := h
  exact ⟨a, b, by simpa using ha, by simpa using hb, rfl⟩

theorem eval_lt_lit {s : Ir.State} {c : ℕ} {y : String} {r : Bool}
    (h : (Ir.Cond.lt (.lit c) (.cell y)).eval s = some r) :
    ∃ b : ℕ, s.vars y = some b ∧ r = decide (c < b) := by
  rw [Ir.Cond.eval_lt, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rfl⟩ := h
  rw [Ir.Operand.eval_lit] at ha
  cases ha
  exact ⟨b, by simpa using hb, rfl⟩

theorem eval_eq_cells {s : Ir.State} {x y : String} {r : Bool}
    (h : (Ir.Cond.eq (.cell x) (.cell y)).eval s = some r) :
    ∃ a b : ℕ, s.vars x = some a ∧ s.vars y = some b := by
  rw [Ir.Cond.eval_eq, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨b, hb, -⟩ := h
  exact ⟨a, b, by simpa using ha, by simpa using hb⟩

/-! ### The two invariants -/

/-- The fill loop's invariant: the bound, the constant, the head still
at zero, and the three facts the seed and the drain inherit. -/
def FInv (n B : ℕ) (s : Ir.State) : Prop :=
  Ir.StateBound B s ∧ s.vars "one" = some 1 ∧ s.vars "head" = some 0 ∧
    (∀ w, s.vars "src" = some w → w < n) ∧
    (∀ Q, s.arrs "q" = some Q → Q.length ≤ n) ∧
    (∀ T, s.arrs "tgt" = some T → ∀ w ∈ T, w < n)

/-- The invariant the drain and its row scan share: the bound, the
constant, the tail with the queue prefix it has filled, and the target
array. -/
def DInv (n B : ℕ) (s : Ir.State) : Prop :=
  Ir.StateBound B s ∧ s.vars "one" = some 1 ∧
    (∃ t, s.vars "tl" = some t ∧ t ≤ n ∧
      ∀ Q, s.arrs "q" = some Q → Q.length ≤ n ∧
        ∀ j, j < t → ∀ w, Q[j]? = some w → w < n) ∧
    (∀ T, s.arrs "tgt" = some T → ∀ w ∈ T, w < n)

theorem FInv.setVar {n B : ℕ} {s : Ir.State} (h : FInv n B s) {x : String} {v : ℕ}
    (h1 : x ≠ "one") (h2 : x ≠ "head") (h3 : x ≠ "src") (hv : v < B) :
    FInv n B (s.setVar x v) := by
  obtain ⟨hb, e1, e2, e3, e4, e5⟩ := h
  refine ⟨hb.setVar hv, ?_, ?_, ?_, e4, e5⟩
  · rw [Ir.State.vars_setVar, if_neg (Ne.symm h1)]; exact e1
  · rw [Ir.State.vars_setVar, if_neg (Ne.symm h2)]; exact e2
  · intro w hw
    rw [Ir.State.vars_setVar, if_neg (Ne.symm h3)] at hw
    exact e3 w hw

theorem FInv.setArr {n B : ℕ} {s : Ir.State} (h : FInv n B s) {a : String} {xs : List ℕ}
    (ha : s.arrs a = some xs) {k m : ℕ} (hm : m < B) (hne : a ≠ "tgt") :
    FInv n B (s.setArr a (xs.set k m)) := by
  obtain ⟨hb, e1, e2, e3, e4, e5⟩ := h
  refine ⟨hb.setArr ha hm, e1, e2, e3, ?_, ?_⟩
  · intro Q hQ
    rw [Ir.State.arrs_setArr] at hQ
    by_cases hq : "q" = a
    · rw [if_pos hq] at hQ
      cases hQ
      rw [List.length_set]
      exact e4 xs (hq ▸ ha)
    · rw [if_neg hq] at hQ; exact e4 Q hQ
  · intro T hT
    rw [Ir.State.arrs_setArr, if_neg (fun hc => hne hc.symm)] at hT
    exact e5 T hT

theorem DInv.setVar {n B : ℕ} {s : Ir.State} (h : DInv n B s) {x : String} {v : ℕ}
    (h1 : x ≠ "one") (h2 : x ≠ "tl") (hv : v < B) : DInv n B (s.setVar x v) := by
  obtain ⟨hb, e1, ⟨t, ht, htn, hq⟩, e3⟩ := h
  refine ⟨hb.setVar hv, ?_, ⟨t, ?_, htn, hq⟩, e3⟩
  · rw [Ir.State.vars_setVar, if_neg (Ne.symm h1)]; exact e1
  · rw [Ir.State.vars_setVar, if_neg (Ne.symm h2)]; exact ht

/-- A store into `dist` touches nothing the invariant mentions but the
bound. -/
theorem DInv.setArrDist {n B : ℕ} {s : Ir.State} (h : DInv n B s) {xs : List ℕ}
    (hxs : s.arrs "dist" = some xs) {k m : ℕ} (hm : m < B) :
    DInv n B (s.setArr "dist" (xs.set k m)) := by
  obtain ⟨hb, e1, ⟨t, ht, htn, hq⟩, e3⟩ := h
  refine ⟨hb.setArr hxs hm, e1, ⟨t, ht, htn, ?_⟩, ?_⟩
  · intro Q hQ
    rw [Ir.State.arrs_setArr, if_neg (by decide)] at hQ
    exact hq Q hQ
  · intro T hT
    rw [Ir.State.arrs_setArr, if_neg (by decide)] at hT
    exact e3 T hT

/-- …and a store of a vertex into the queue keeps the prefix a prefix of
vertices, whatever index it lands at. -/
theorem DInv.setArrQ {n B : ℕ} {s : Ir.State} (h : DInv n B s) {Qs : List ℕ}
    (hQs : s.arrs "q" = some Qs) {k m : ℕ} (hm : m < B) (hmn : m < n) :
    DInv n B (s.setArr "q" (Qs.set k m)) := by
  obtain ⟨hb, e1, ⟨t, ht, htn, hq⟩, e3⟩ := h
  obtain ⟨hlen, hpre⟩ := hq Qs hQs
  refine ⟨hb.setArr hQs hm, e1, ⟨t, ht, htn, ?_⟩, ?_⟩
  · intro Q hQ
    rw [Ir.State.arrs_setArr, if_pos rfl] at hQ
    cases hQ
    refine ⟨by rw [List.length_set]; exact hlen, ?_⟩
    intro j hj w hw
    rcases eq_or_ne k j with rfl | hne
    · rw [List.getElem?_set, if_pos rfl] at hw
      split at hw
      · cases hw; exact hmn
      · exact absurd hw (by simp)
    · rw [List.getElem?_set_ne hne] at hw
      exact hpre j hj w hw
  · intro T hT
    rw [Ir.State.arrs_setArr, if_neg (by decide)] at hT
    exact e3 T hT

/-- After a vertex is stored at the tail, the tail may advance: the
entry the extended prefix gains is the one just stored. -/
theorem DInv.bumpTl {n B : ℕ} {s : Ir.State} (h : DInv n B s) {tv : ℕ}
    (ht : s.vars "tl" = some tv) (htn1 : tv + 1 ≤ n) (hB1 : tv + 1 < B)
    (hcov : ∀ Q, s.arrs "q" = some Q → ∀ w, Q[tv]? = some w → w < n) :
    DInv n B (s.setVar "tl" (tv + 1)) := by
  obtain ⟨hb, e1, ⟨t, ht', htn, hq⟩, e3⟩ := h
  obtain rfl : tv = t := by rw [ht] at ht'; exact Option.some.inj ht'
  refine ⟨hb.setVar hB1, ?_, ⟨tv + 1, by simp, htn1, ?_⟩, ?_⟩
  · rw [Ir.State.vars_setVar, if_neg (by decide)]; exact e1
  · intro Q hQ
    rw [Ir.State.arrs_setVar] at hQ
    refine ⟨(hq Q hQ).1, ?_⟩
    intro j hj w hw
    rcases eq_or_ne j tv with rfl | hne
    · exact hcov Q hQ w hw
    · exact (hq Q hQ).2 j (lt_of_le_of_ne (Nat.le_of_lt_succ hj) hne) w hw
  · intro T hT
    rw [Ir.State.arrs_setVar] at hT
    exact e3 T hT

/-! ### The bound and the initial store -/

/-- What the bound owes the structure: the three linear facts. Everything
else (`1 < B`, `0 < B`, `d < B`) follows. -/
structure BfsBounds (n ns d B : ℕ) : Prop where
  /-- The vertex count. -/
  hn : n < B
  /-- The slot count. -/
  hns : ns < B
  /-- The sentinel. -/
  hd : d + 1 < B

/-- Entries of the target array are vertices, in membership form. -/
theorem tgt_mem_lt {n : ℕ} {off tgt alv : List ℕ} (hsh : Shape n off tgt alv) :
    ∀ w ∈ tgt, w < n := by
  intro w hw
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hw
  have := hsh.2.2.2.2 j hj
  rwa [getElem!_pos tgt j hj] at this

/-- Entries of the offset array sit below the **last offset** — the
slot count, not the physical width of the target array (Fa/D-x). The
old reading `w ≤ tgt.length` is this one composed with `Shape`'s
`off[n]! ≤ tgt.length`, and it is the one that pinned the width. -/
theorem off_mem_le {n : ℕ} {off tgt alv : List ℕ} (hsh : Shape n off tgt alv) :
    ∀ w ∈ off, w ≤ off[n]! := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
  have hlen : off.length = n + 1 := hsh.1
  have h1 : off[i]! ≤ off[n]! := Shape.mono' hsh (by omega) le_rfl
  rw [getElem!_pos off i hi] at h1
  omega

/-- The initial store is bounded. The offsets are bounded through the
last one (`hoff`), so the target array's width plays no part: at the
pinned width `hoff` is `Shape`'s `off[n]! ≤ tgt.length ≤ ns`, at the
widened one it is `Csr.last` (Fa/D-x). -/
theorem bfsQ_stateBound {n ns d B src : ℕ} {off tgt alv dist₀ q₀ : List ℕ}
    (hB : BfsBounds n ns d B) (hsh : Shape n off tgt alv) (hoff : off[n]! ≤ ns)
    (hsrc : src < n)
    (halv : ∀ w ∈ alv, w < B) (hd0 : ∀ w ∈ dist₀, w < B) (hq0 : ∀ w ∈ q₀, w < B) :
    Ir.StateBound B (bfsQState n d src off tgt alv dist₀ q₀) := by
  have h1 := hB.hn; have h2 := hB.hns; have h3 := hB.hd
  refine stateBound_ofPairs ?_ ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact hd0
    · exact hq0
    · intro w hw
      have h4 : w ≤ off[n]! := off_mem_le hsh w hw
      omega
    · intro w hw
      have h4 : w < n := tgt_mem_lt hsh w hw
      omega
    · exact halv

/-! ### The walk

One lemma per loop body, one for the shared tail of the scan's three
branch paths, and the assembly. Every in-range fact below arrives as a
hypothesis of a `bpre` clause — none is proved. Identifications are by
`Option.some.inj`, never `omega`, and the `< B` arithmetic is term-mode,
because the clause binders are at `Ir.Val` and `omega` is blind through
that abbrev (the P5 trap, hit again here). -/

/-- Guard literal facts, at concrete conditions (keeps the implicit
condition determined at elaboration). -/
theorem litLt_lt_cells {B : ℕ} {x y : String} :
    (Cond.lt (Operand.cell x) (Operand.cell y)).LitLt B := ⟨trivial, trivial⟩

theorem litLt_eq_cells {B : ℕ} {x y : String} :
    (Cond.eq (Operand.cell x) (Operand.cell y)).LitLt B := ⟨trivial, trivial⟩

theorem litLt_lit0 {B : ℕ} (h0 : 0 < B) {y : String} :
    (Cond.lt (Operand.lit 0) (Operand.cell y)).LitLt B := ⟨h0, trivial⟩

/-- The tail every scan path shares: the slot counter bump. -/
theorem scan_tail_bpre {n B : ℕ} {t' : Ir.State} (hI : DInv n B t')
    {k₀v kev : ℕ} (hk₀ : t'.vars "k0" = some k₀v) (hke : t'.vars "kend" = some kev)
    (hlt : k₀v < kev) :
    bpre B ((Com.binop Imp.Bop.add "k0" "k0" "one").seq
      (Com.skip.seq (Com.skip.seq Com.skip))) (DInv n B) t' := by
  intro m₁ m₂ hm₁ hm₂
  obtain rfl : k₀v = m₁ := by rw [hk₀] at hm₁; exact Option.some.inj hm₁
  obtain rfl : m₂ = 1 := by rw [hI.2.1] at hm₂; exact (Option.some.inj hm₂).symm
  have hkeB : kev < B := hI.1.var hke
  simp only [Imp.Bop.apply_add]
  exact ⟨lt_of_le_of_lt (Nat.succ_le_of_lt hlt) hkeB,
    hI.setVar (x := "k0") (by decide) (by decide)
      (lt_of_le_of_lt (Nat.succ_le_of_lt hlt) hkeB)⟩

/-- One slot of the row scan preserves the drain invariant. The
interesting step is the queue store: its own in-range hypothesis is what
bounds the tail bump two lines later. -/
theorem scan_body_bpre {n B : ℕ} (hn : n < B) {t : Ir.State} (hI : DInv n B t)
    (hg : (Cond.lt (Operand.cell "k0") (Operand.cell "kend")).eval t = some true) :
    bpre B
      ((Com.aget "u" "tgt" "k0").seq
        ((Com.aget "au" "alv" "u").seq
          ((Com.aget "du" "dist" "u").seq
            ((Com.ite (Cond.lt (Operand.lit 0) (Operand.cell "au"))
                (Com.ite (Cond.eq (Operand.cell "du") (Operand.cell "sent"))
                  ((Com.aset "dist" "u" "dv1").seq
                    ((Com.aset "q" "tl" "u").seq
                      ((Com.binop Imp.Bop.add "tl" "tl" "one").seq
                        (Com.skip.seq Com.skip))))
                  (Com.skip.seq Com.skip))
                (Com.skip.seq Com.skip)).seq
              ((Com.binop Imp.Bop.add "k0" "k0" "one").seq
                (Com.skip.seq (Com.skip.seq Com.skip))))))) (DInv n B) t := by
  have hI' := hI
  obtain ⟨hsb, hone, ⟨tv, htv, htn, hq⟩, htgtc⟩ := hI
  obtain ⟨k₀v, kev, hk₀, hke, hr⟩ := eval_lt_cells hg
  have hlt : k₀v < kev := of_decide_eq_true hr.symm
  have h0B : 0 < B := lt_of_le_of_lt (Nat.zero_le n) hn
  -- the slot's target is a vertex
  intro ku xsT u₀ hku hxsT hu₀
  have hu₀n : u₀ < n := htgtc xsT hxsT u₀ (List.mem_of_getElem? hu₀)
  have hu₀B : u₀ < B := lt_trans hu₀n hn
  intro ka ysA a₀ hka hysA ha₀
  have hysA' : t.arrs "alv" = some ysA := by simpa using hysA
  have ha₀B : a₀ < B := hsb.getElem hysA' ha₀
  intro kd zsD d₀ hkd hzsD hd₀
  have hzsD' : t.arrs "dist" = some zsD := by simpa using hzsD
  have hd₀B : d₀ < B := hsb.getElem hzsD' hd₀
  have hI₃ : DInv n B (((t.setVar "u" u₀).setVar "au" a₀).setVar "du" d₀) :=
    ((hI'.setVar (x := "u") (by decide) (by decide) hu₀B).setVar (x := "au")
      (by decide) (by decide) ha₀B).setVar (x := "du") (by decide) (by decide) hd₀B
  have hk₀₃ : (((t.setVar "u" u₀).setVar "au" a₀).setVar "du" d₀).vars "k0"
      = some k₀v := by simpa using hk₀
  have hke₃ : (((t.setVar "u" u₀).setVar "au" a₀).setVar "du" d₀).vars "kend"
      = some kev := by simpa using hke
  refine ⟨fun r h => Cond.evalB_of_stateBound hI₃.1 (litLt_lit0 h0B) h, ?_, ?_⟩
  · -- the mask says alive
    intro _
    refine ⟨fun r h => Cond.evalB_of_stateBound hI₃.1 litLt_eq_cells h, ?_, ?_⟩
    · -- undiscovered: the slot relaxes
      intro _
      intro k₄ m₄ ws hk₄ hm₄ hws hlen₄
      obtain rfl : u₀ = k₄ := by
        have h' : some u₀ = some k₄ := by simpa using hk₄
        exact Option.some.inj h'
      have hm₄B : m₄ < B := hI₃.1.var hm₄
      have hI₄ : DInv n B ((((t.setVar "u" u₀).setVar "au" a₀).setVar "du" d₀).setArr
          "dist" (ws.set u₀ m₄)) := hI₃.setArrDist hws hm₄B
      intro k₅ m₅ qs hk₅ hm₅ hqs hlen₅
      obtain rfl : u₀ = m₅ := by
        have h' : some u₀ = some m₅ := by simpa using hm₅
        exact Option.some.inj h'
      obtain rfl : tv = k₅ := by
        have h' : t.vars "tl" = some k₅ := by simpa using hk₅
        rw [htv] at h'
        exact Option.some.inj h'
      have hqs' : t.arrs "q" = some qs := by simpa using hqs
      obtain ⟨hqlen', hpre'⟩ := hq qs hqs'
      have htvn : tv + 1 ≤ n := le_trans (Nat.succ_le_of_lt hlen₅) hqlen'
      have htvB : tv + 1 < B := lt_of_le_of_lt htvn hn
      have hI₅ : DInv n B (((((t.setVar "u" u₀).setVar "au" a₀).setVar "du" d₀).setArr
          "dist" (ws.set u₀ m₄)).setArr "q" (qs.set tv u₀)) :=
        hI₄.setArrQ hqs hu₀B hu₀n
      -- the queue store: its in-range hypothesis `hlen₅` bounds the bump
      intro m₆ m₇ hm₆ hm₇
      obtain rfl : tv = m₆ := by
        have h' : t.vars "tl" = some m₆ := by simpa using hm₆
        rw [htv] at h'
        exact Option.some.inj h'
      obtain rfl : m₇ = 1 := by
        have h' : t.vars "one" = some m₇ := by simpa using hm₇
        rw [hone] at h'
        exact (Option.some.inj h').symm
      simp only [Imp.Bop.apply_add]
      refine ⟨htvB, ?_⟩
      -- the entry the extended prefix gains is the one just stored
      have hcov : ∀ Q, (((((t.setVar "u" u₀).setVar "au" a₀).setVar "du" d₀).setArr
          "dist" (ws.set u₀ m₄)).setArr "q" (qs.set tv u₀)).arrs "q" = some Q →
          ∀ w, Q[tv]? = some w → w < n := by
        intro Q hQ w hw
        have hQ' : Q = qs.set tv u₀ := by
          have h' : some (qs.set tv u₀) = some Q := by simpa using hQ
          exact (Option.some.inj h').symm
        subst hQ'
        rw [List.getElem?_set_self hlen₅] at hw
        cases hw
        exact hu₀n
      have hI₆ := hI₅.bumpTl (by simpa using htv) htvn htvB hcov
      exact scan_tail_bpre hI₆ (by simpa using hk₀) (by simpa using hke) hlt
    · -- already discovered: nothing to do
      intro _
      exact scan_tail_bpre hI₃ hk₀₃ hke₃ hlt
  · -- dead: nothing to do
    intro _
    exact scan_tail_bpre hI₃ hk₀₃ hke₃ hlt

/-- One pop preserves the drain invariant; the row scan rides inside. -/
theorem drain_body_bpre {n B : ℕ} (hn : n < B) {t : Ir.State} (hI : DInv n B t)
    (hg : (Cond.lt (Operand.cell "head") (Operand.cell "tl")).eval t = some true) :
    bpre B
      ((Com.aget "v" "q" "head").seq
        ((Com.aget "dv" "dist" "v").seq
          ((Com.binop Imp.Bop.add "head" "head" "one").seq
            ((Com.ite (Cond.lt (Operand.cell "dv") (Operand.cell "d"))
                ((Com.binop Imp.Bop.add "dv1" "dv" "one").seq
                  ((Com.aget "k0" "off" "v").seq
                    ((Com.binop Imp.Bop.add "v1" "v" "one").seq
                      ((Com.aget "kend" "off" "v1").seq
                        ((Com.skip.seq (Com.skip.seq Com.skip)).seq
                          ((Com.while (Cond.lt (Operand.cell "k0") (Operand.cell "kend"))
                              ((Com.aget "u" "tgt" "k0").seq
                                ((Com.aget "au" "alv" "u").seq
                                  ((Com.aget "du" "dist" "u").seq
                                    ((Com.ite (Cond.lt (Operand.lit 0) (Operand.cell "au"))
                                          (Com.ite (Cond.eq (Operand.cell "du")
                                              (Operand.cell "sent"))
                                            ((Com.aset "dist" "u" "dv1").seq
                                              ((Com.aset "q" "tl" "u").seq
                                                ((Com.binop Imp.Bop.add "tl" "tl" "one").seq
                                                  (Com.skip.seq Com.skip))))
                                            (Com.skip.seq Com.skip))
                                          (Com.skip.seq Com.skip)).seq
                                      ((Com.binop Imp.Bop.add "k0" "k0" "one").seq
                                        (Com.skip.seq (Com.skip.seq Com.skip)))))))).seq
                            (Com.skip.seq Com.skip)))))))
                (Com.skip.seq Com.skip)).seq
              (Com.skip.seq (Com.skip.seq Com.skip)))))) (DInv n B) t := by
  have hI' := hI
  obtain ⟨hsb, hone, ⟨tv, htv, htn, hq⟩, htgtc⟩ := hI
  obtain ⟨hd, tv', hhd, htl', hr⟩ := eval_lt_cells hg
  obtain rfl : tv = tv' := by rw [htv] at htl'; exact Option.some.inj htl'
  have hlt : hd < tv := of_decide_eq_true hr.symm
  -- the popped entry is a vertex: it sits below the tail
  intro kh qs v₀ hkh hqs hv₀
  obtain rfl : hd = kh := by rw [hhd] at hkh; exact Option.some.inj hkh
  have hv₀n : v₀ < n := (hq qs hqs).2 hd hlt v₀ hv₀
  have hv₀B : v₀ < B := lt_trans hv₀n hn
  intro kv zs d₀ hkv hzs hd₀
  have hzs' : t.arrs "dist" = some zs := by simpa using hzs
  have hd₀B : d₀ < B := hsb.getElem hzs' hd₀
  intro m₁ m₂ hm₁ hm₂
  obtain rfl : hd = m₁ := by
    have h' : t.vars "head" = some m₁ := by simpa using hm₁
    rw [hhd] at h'
    exact Option.some.inj h'
  obtain rfl : m₂ = 1 := by
    have h' : t.vars "one" = some m₂ := by simpa using hm₂
    rw [hone] at h'
    exact (Option.some.inj h').symm
  simp only [Imp.Bop.apply_add]
  have hhdB : hd + 1 < B := lt_of_le_of_lt (le_trans (Nat.succ_le_of_lt hlt) htn) hn
  have hI₃ : DInv n B (((t.setVar "v" v₀).setVar "dv" d₀).setVar "head" (hd + 1)) :=
    ((hI'.setVar (x := "v") (by decide) (by decide) hv₀B).setVar (x := "dv")
      (by decide) (by decide) hd₀B).setVar (x := "head") (by decide) (by decide) hhdB
  refine ⟨hhdB, fun r h => Cond.evalB_of_stateBound hI₃.1 litLt_lt_cells h, ?_, ?_⟩
  · -- below the cap: the row is scanned
    intro hgd
    obtain ⟨dvv, dcv, hdvv, hdcv, hrd⟩ := eval_lt_cells hgd
    obtain rfl : d₀ = dvv := by
      have h' : some d₀ = some dvv := by simpa using hdvv
      exact Option.some.inj h'
    have hcap : d₀ < dcv := of_decide_eq_true hrd.symm
    have hdcB : dcv < B := hI₃.1.var hdcv
    have hd₀B' : d₀ + 1 < B := lt_of_le_of_lt (Nat.succ_le_of_lt hcap) hdcB
    intro m₃ m₄ hm₃ hm₄
    obtain rfl : d₀ = m₃ := by
      have h' : some d₀ = some m₃ := by simpa using hm₃
      exact Option.some.inj h'
    obtain rfl : m₄ = 1 := by
      have h' : t.vars "one" = some m₄ := by simpa using hm₄
      rw [hone] at h'
      exact (Option.some.inj h').symm
    simp only [Imp.Bop.apply_add]
    refine ⟨hd₀B', ?_⟩
    intro k₆ os o₀ hk₆ hos ho₀
    have hos' : t.arrs "off" = some os := by simpa using hos
    have ho₀B : o₀ < B := hsb.getElem hos' ho₀
    intro m₅ m₆ hm₅ hm₆
    obtain rfl : v₀ = m₅ := by
      have h' : some v₀ = some m₅ := by simpa using hm₅
      exact Option.some.inj h'
    obtain rfl : m₆ = 1 := by
      have h' : t.vars "one" = some m₆ := by simpa using hm₆
      rw [hone] at h'
      exact (Option.some.inj h').symm
    simp only [Imp.Bop.apply_add]
    have hv₁B : v₀ + 1 < B := lt_of_le_of_lt (Nat.succ_le_of_lt hv₀n) hn
    refine ⟨hv₁B, ?_⟩
    intro k₇ os₂ o₁ hk₇ hos₂ ho₁
    have hos₂' : t.arrs "off" = some os₂ := by simpa using hos₂
    have ho₁B : o₁ < B := hsb.getElem hos₂' ho₁
    -- the invariant at the row loop's entry
    have hI₄ : DInv n B ((((t.setVar "v" v₀).setVar "dv" d₀).setVar "head"
        (hd + 1)).setVar "dv1" (d₀ + 1)) :=
      hI₃.setVar (x := "dv1") (by decide) (by decide) hd₀B'
    have hI₅ : DInv n B (((((t.setVar "v" v₀).setVar "dv" d₀).setVar "head"
        (hd + 1)).setVar "dv1" (d₀ + 1)).setVar "k0" o₀) :=
      hI₄.setVar (x := "k0") (by decide) (by decide) ho₀B
    have hI₆ : DInv n B ((((((t.setVar "v" v₀).setVar "dv" d₀).setVar "head"
        (hd + 1)).setVar "dv1" (d₀ + 1)).setVar "k0" o₀).setVar "v1" (v₀ + 1)) :=
      hI₅.setVar (x := "v1") (by decide) (by decide) hv₁B
    have hI₇ : DInv n B (((((((t.setVar "v" v₀).setVar "dv" d₀).setVar "head"
        (hd + 1)).setVar "dv1" (d₀ + 1)).setVar "k0" o₀).setVar "v1"
        (v₀ + 1)).setVar "kend" o₁) :=
      hI₆.setVar (x := "kend") (by decide) (by decide) ho₁B
    refine ⟨DInv n B, hI₇, ?_, ?_, ?_⟩
    · exact fun t' r hJ h => Cond.evalB_of_stateBound hJ.1 litLt_lt_cells h
    · exact fun t' hJ hg' => scan_body_bpre hn hJ hg'
    · exact fun t' hJ _ => hJ
  · -- at the cap: nothing is scanned
    intro _
    exact hI₃

/-- The fill body preserves its invariant. -/
theorem fill_body_bpre {n B : ℕ} {t : Ir.State} (hI : FInv n B t)
    (hg : (Cond.lt (Operand.cell "i") (Operand.cell "n")).eval t = some true) :
    bpre B ((Com.aset "dist" "i" "sent").seq
      ((Com.binop Imp.Bop.add "i" "i" "one").seq Com.skip)) (FInv n B) t := by
  obtain ⟨iv, nv, hiv, hnv, hr⟩ := eval_lt_cells hg
  have hlt : iv < nv := of_decide_eq_true hr.symm
  have hnvB : nv < B := hI.1.var hnv
  intro k m xs hk hm hxs hklen
  have hmB : m < B := hI.1.var hm
  have hI₁ : FInv n B (t.setArr "dist" (xs.set k m)) := hI.setArr hxs hmB (by decide)
  intro m₁ m₂ hm₁ hm₂
  obtain rfl : iv = m₁ := by
    have h' : t.vars "i" = some m₁ := by simpa using hm₁
    rw [hiv] at h'
    exact Option.some.inj h'
  obtain rfl : m₂ = 1 := by
    have h' : t.vars "one" = some m₂ := by simpa using hm₂
    rw [hI.2.1] at h'
    exact (Option.some.inj h').symm
  simp only [Imp.Bop.apply_add]
  exact ⟨lt_of_le_of_lt (Nat.succ_le_of_lt hlt) hnvB,
    hI₁.setVar (x := "i") (by decide) (by decide) (by decide)
      (lt_of_le_of_lt (Nat.succ_le_of_lt hlt) hnvB)⟩

/-- **The bounds pass for the synthesized program.** Every index-in-range
fact of §11's table has disappeared into the run; what is discharged
here is the three `< B` families and the two invariants. -/
theorem bfsQ_bpre {n ns d B src : ℕ} {off tgt alv dist₀ q₀ : List ℕ}
    (hB : BfsBounds n ns d B) (hsh : Shape n off tgt alv) (hoff : off[n]! ≤ ns)
    (hsrc : src < n)
    (halv : ∀ w ∈ alv, w < B) (hd0 : ∀ w ∈ dist₀, w < B) (hq0 : ∀ w ∈ q₀, w < B)
    (hdlen : dist₀.length = n) (hqlen : q₀.length = n) :
    bpre B bfsQSynth_impl (fun _ => True)
      (bfsQState n d src off tgt alv dist₀ q₀) := by
  have hn : n < B := hB.hn
  have h1B : 1 < B := by have := hB.hd; omega
  have h0B : 0 < B := by omega
  have hSB : Ir.StateBound B (bfsQState n d src off tgt alv dist₀ q₀) :=
    bfsQ_stateBound hB hsh hoff hsrc halv hd0 hq0
  -- the fill loop
  refine ⟨FInv n B, ?_, ?_, fun t hI hg => fill_body_bpre hI hg, ?_⟩
  · -- the invariant, at the initial store
    refine ⟨hSB, rfl, rfl, ?_, ?_, ?_⟩
    · intro w hw
      obtain rfl : w = src := (Option.some.inj hw).symm
      exact hsrc
    · intro Q hQ
      obtain rfl : Q = q₀ := (Option.some.inj hQ).symm
      exact le_of_eq hqlen
    · intro T hT
      obtain rfl : T = tgt := (Option.some.inj hT).symm
      exact tgt_mem_lt hsh
  · exact fun t' r hJ h => Cond.evalB_of_stateBound hJ.1 litLt_lt_cells h
  -- the seed
  intro t hI hgf
  have hIt := hI
  obtain ⟨hsb, hone, hhead, hsrcn, hqlenI, htgtI⟩ := hI
  intro k m xs hk hm hxs hklen
  obtain rfl : m = 0 := by rw [hhead] at hm; exact (Option.some.inj hm).symm
  have hkn : k < n := hsrcn k hk
  have hI₁ : FInv n B (t.setArr "dist" (xs.set k 0)) := hIt.setArr hxs h0B (by decide)
  intro k₂ m₂ qs hk₂ hm₂ hqs hklen₂
  obtain rfl : k₂ = 0 := by
    have h' : t.vars "head" = some k₂ := by simpa using hk₂
    rw [hhead] at h'
    exact (Option.some.inj h').symm
  obtain rfl : k = m₂ := by
    have h' : t.vars "src" = some m₂ := by simpa using hm₂
    rw [hk] at h'
    exact Option.some.inj h'
  have hkB : k < B := lt_trans hkn hn
  have hI₂ : FInv n B ((t.setArr "dist" (xs.set k 0)).setArr "q" (qs.set 0 k)) :=
    hI₁.setArr hqs hkB (by decide)
  intro k₃ ys a₀ hk₃ hys ha₀
  have hys' : t.arrs "alv" = some ys := by simpa using hys
  have ha₀B : a₀ < B := hsb.getElem hys' ha₀
  have hI₃ : FInv n B (((t.setArr "dist" (xs.set k 0)).setArr "q"
      (qs.set 0 k)).setVar "a" a₀) :=
    hI₂.setVar (x := "a") (by decide) (by decide) (by decide) ha₀B
  have hqs' : t.arrs "q" = some qs := by simpa using hqs
  have hqsn : qs.length ≤ n := hqlenI qs hqs'
  -- the queue after the seed: its head entry is the source
  have hqseed : ∀ Q', Q' = qs.set 0 k →
      Q'.length ≤ n ∧ ∀ j, j < 1 → ∀ w, Q'[j]? = some w → w < n := by
    rintro Q' rfl
    refine ⟨by simpa [List.length_set] using hqsn, ?_⟩
    intro j hj w hw
    obtain rfl : j = 0 := by omega
    rw [List.getElem?_set_self hklen₂] at hw
    cases hw
    exact hkn
  have honeS : (((t.setArr "dist" (xs.set k 0)).setArr "q"
      (qs.set 0 k)).setVar "a" a₀).vars "one" = some 1 := by simpa using hone
  have htgtS : ∀ T, (((t.setArr "dist" (xs.set k 0)).setArr "q"
      (qs.set 0 k)).setVar "a" a₀).arrs "tgt" = some T → ∀ w ∈ T, w < n := by
    intro T hT
    exact htgtI T (by simpa using hT)
  have h1n : 1 ≤ n := lt_of_le_of_lt (Nat.zero_le k) hkn
  refine ⟨fun r h => Cond.evalB_of_stateBound hI₃.1 litLt_lt_cells h, ?_, ?_⟩
  · -- the source is alive: it enters the queue
    intro _
    refine ⟨h1B, ?_⟩
    refine ⟨DInv n B, ?_, ?_, fun t' hJ hg' => drain_body_bpre hn hJ hg',
      fun _ _ _ => trivial⟩
    · refine ⟨hI₃.1.setVar h1B, by simpa using honeS, ⟨1, by simp, h1n, ?_⟩, ?_⟩
      · intro Q' hQ'
        refine hqseed Q' ?_
        have h' : some (qs.set 0 k) = some Q' := by simpa using hQ'
        exact (Option.some.inj h').symm
      · intro T hT
        exact htgtS T (by simpa using hT)
    · exact fun t' r hJ h => Cond.evalB_of_stateBound hJ.1 litLt_lt_cells h
  · -- the source is dead: the queue stays empty
    intro _
    refine ⟨h0B, ?_⟩
    refine ⟨DInv n B, ?_, ?_, fun t' hJ hg' => drain_body_bpre hn hJ hg',
      fun _ _ _ => trivial⟩
    · refine ⟨hI₃.1.setVar h0B, by simpa using honeS, ⟨0, by simp, Nat.zero_le n, ?_⟩, ?_⟩
      · intro Q' hQ'
        refine ⟨(hqseed Q' ?_).1, ?_⟩
        · have h' : some (qs.set 0 k) = some Q' := by simpa using hQ'
          exact (Option.some.inj h').symm
        · intro j hj
          exact absurd hj (Nat.not_lt_zero j)
      · intro T hT
        exact htgtS T (by simpa using hT)
    · exact fun t' r hJ h => Cond.evalB_of_stateBound hJ.1 litLt_lt_cells h

/-! ### The state, held; the run, bounded -/

/-- Everything the initial store owns beyond `bfsQPre`: nothing. The
erase chain is in the precondition's peel order, so the ownership proof
ends in `rfl`. -/
def bfsQHole (n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) : Assn :=
  EXACT
    ((vcells (bfsQState n d src off tgt alv dist₀ q₀) |>.erase "i" |>.erase "head"
        |>.erase "n" |>.erase "sent" |>.erase "d" |>.erase "src" |>.erase "one"
        |>.erase "a" |>.erase "tl" |>.erase "v" |>.erase "dv" |>.erase "dv1"
        |>.erase "k0" |>.erase "v1" |>.erase "kend" |>.erase "u" |>.erase "au"
        |>.erase "du",
      acells (bfsQState n d src off tgt alv dist₀ q₀) |>.erase "dist" |>.erase "q"
        |>.erase "off" |>.erase "tgt" |>.erase "alv",
      hcells (bfsQState n d src off tgt alv dist₀ q₀)), 0)

theorem bfsQ_state_holds (n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) :
    irSTATE (bfsQPre n d src off tgt alv dist₀ q₀
        ∗ bfsQHole n d src off tgt alv dist₀ q₀)
      (bfsQState n d src off tgt alv dist₀ q₀, 0) := by
  show (bfsQPre n d src off tgt alv dist₀ q₀ ∗ bfsQHole n d src off tgt alv dist₀ q₀)
    ((vcells (bfsQState n d src off tgt alv dist₀ q₀),
      acells (bfsQState n d src off tgt alv dist₀ q₀),
      hcells (bfsQState n d src off tgt alv dist₀ q₀)), 0)
  simp only [bfsQPre, hnCtxt, natAssn_def, arrayAssn_def, sepConj_assoc]
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  iterate 11
    rw [junkCell_def, sepEx_sepConj]
    refine ⟨0, Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩⟩
  rfl

/-- **The bounds witness, from the run the tower already has.** No
`Runs` construction, no variants, no counting — `hnRefine` supplies the
`BigStep`, `bfsQ_bpre` bounds it along its own derivation. -/
theorem bfsQ_runs {n ns d B src : ℕ} {G : SimpleGraph (Fin n)}
    {off tgt alv dist₀ q₀ : List ℕ}
    (hc : Csr n ns G off tgt alv) (hsrc : src < n) (hB : BfsBounds n ns d B)
    (halv : ∀ w ∈ alv, w < B) (hd0 : ∀ w ∈ dist₀, w < B) (hq0 : ∀ w ∈ q₀, w < B)
    (hdlen : dist₀.length = n) (hqlen : q₀.length = n) :
    ∃ s' κ', Ir.BigStepB B bfsQSynth_impl
      (bfsQState n d src off tgt alv dist₀ q₀) s' κ' :=
  exists_bigStepB_of_hnRefine (bfsQSynth' n d src off tgt alv dist₀ q₀)
    (bfsQS_correct hc hsrc hdlen hqlen)
    (bfsQ_state_holds n d src off tgt alv dist₀ q₀)
    (bfsQ_bpre hB hc.shape (le_of_eq hc.last) hsrc halv hd0 hq0 hdlen hqlen)

end Bounds

/-! ## 13. The export (design note P7/S-1)

The cashing chain, closed. `bfsQK` is what `spec_of_hnRefine` prices
the abstract budget at; the export's precondition and postcondition are
`bfs_spec`'s shape at this package's own vocabulary — every meaningful
cell and array listed, the threshold post at `WD`/`maskOf`, the cost an
explicit linear polynomial. -/

section Export

/-- `ecash` of a lifted account is `cash` of the account (the lift is
`Cash.lean`'s own, restated at `liftACost`). -/
theorem ecash_liftACost (κ : ACost String ℕ) : ecash (liftACost κ) = (Codegen.cash κ : ℕ∞) := by
  simp only [ecash, Codegen.cash, liftACost, Nat.cast_list_sum, List.map_map]
  congr 1

theorem cash_nsmul (k : ℕ) (κ : Ir.Cost) : Codegen.cash (k • κ) = k * Codegen.cash κ := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, cash_add, ih]; ring

theorem cash_cost_units (c : String) (k : ℕ) :
    Codegen.cash (ACost.cost c k) = k * Codegen.cash (ACost.cost c 1) := by
  have hcost : k • (ACost.cost c (1 : ℕ) : Ir.Cost) = ACost.cost c k := by
    ext d
    simp [ACost.toFun_nsmul, ACost.toFun_cost]
  rw [← hcost, cash_nsmul]

/-- The complete BFS account, priced from its proved coordinates rather than
by kernel evaluation of four opaque subaccounts. -/
theorem cash_bfsQTotal (n ns : ℕ) :
    Codegen.cash (bfsQTotal n ns) = 56 * n + 40 * ns + 33 := by
  rw [bfsQTotal_normal]
  simp only [cash_add]
  rw [cash_cost_units Currency.skip (9 * n + 5 * ns + 4),
    cash_cost_units Currency.const 2,
    cash_cost_units Currency.aget (4 * n + 3 * ns + 1),
    cash_cost_units Currency.aset (n + 2 * ns + 2),
    cash_cost_units Currency.ite (n + 2 * ns + 1),
    cash_cost_units Currency.«while» (3 * n + ns + 2),
    cash_cost_units Currency.add (4 * n + 2 * ns + 1)]
  simp only [Codegen.cash_cost_skip,
    Codegen.cash_cost_const, Codegen.cash_cost_aget, Codegen.cash_cost_aset,
    Codegen.cash_cost_ite, Codegen.cash_cost_while,
    show Codegen.cash (ACost.cost Currency.add 1) = 4 from Codegen.cash_cost_binop .add]
  ring

/-- At the synthesis layer, the BFS account crosses the code-generation
boundary exactly once: exchange every IR currency to the sole cash currency,
then erase the `Unit` index. The scalar is `56n + 40ns + 33`. -/
theorem flatCost_cash_bfsQTotal (n ns : ℕ) :
    NRest.flatCost
        (timerefineA NRest.cashExchangeRate (liftACost (bfsQTotal n ns))) =
      ((56 * n + 40 * ns + 33 : ℕ) : ℕ∞) := by
  rw [NRest.flatCost_timerefineA_cashExchangeRate, bfsQTotal_normal]
  simp only [liftACost_add, liftACost_cost, Codegen.ecash_add]
  rw [Codegen.ecash_cost (n := Currency.skip) (by simp [Currency.all]),
    Codegen.ecash_cost (n := Currency.const) (by simp [Currency.all]),
    Codegen.ecash_cost (n := Currency.aget) (by simp [Currency.all]),
    Codegen.ecash_cost (n := Currency.aset) (by simp [Currency.all]),
    Codegen.ecash_cost (n := Currency.ite) (by simp [Currency.all]),
    Codegen.ecash_cost (n := Currency.«while») (by simp [Currency.all]),
    Codegen.ecash_cost (n := Currency.add) (by simp [Currency.all])]
  simp only [Codegen.weight_skip, Codegen.weight_const, Codegen.weight_aget,
    Codegen.weight_aset, Codegen.weight_ite, Codegen.weight_while,
    show Codegen.weight Currency.add = 4 from Codegen.weight_binopCurrency .add]
  push_cast
  ring

/-- info: 'Lax13Proofs.Refine.BfsQSynth.flatCost_cash_bfsQTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flatCost_cash_bfsQTotal

/-- The historical budget name remains available; it is now a corollary of
the total-vector theorem, not a second calculation. -/
theorem cash_bfsBudget (n ns : ℕ) : Codegen.cash (bfsBudget n ns) = 56 * n + 40 * ns + 32 := by
  have h := cash_bfsQTotal n ns
  rw [bfsQTotal, cash_add] at h
  have hskip : Codegen.cash (cu Currency.skip) = 1 := by
    simp [Codegen.cash, Currency.all, Codegen.weight, cu, Currency.skip,
      Currency.const, Currency.copy, Currency.aget, Currency.aset, Currency.ite,
      Currency.«while», Currency.add, Currency.sub, Currency.mul, Currency.div,
      Currency.and, Currency.or, Currency.xor, Currency.shiftl, Currency.shiftr]
  omega

/-- **The exported cost**: `56·n + 40·ns + 33` IMP+ time units (the
baseline's hand-tuned figure is `51·n + 44·ns + 30`; this one is
computed, not tuned — P7/D-br). -/
def bfsQK (n ns : ℕ) : ℕ := 56 * n + 40 * ns + 33

theorem ecash_bfsQTotal (n ns : ℕ) :
    ecash (irUnit Currency.skip + liftACost (bfsBudget n ns)) = (bfsQK n ns : ℕ∞) := by
  rw [← liftACost_cu Currency.skip, ← liftACost_add, ← bfsQTotal,
    ecash_liftACost, cash_bfsQTotal, bfsQK]

/-- The cashing chain at one initial store. -/
theorem bfsQ_spec_at {n ns d B : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}
    {src : ℕ} (dist₀ q₀ : List ℕ) (hc : Csr n ns G off tgt alv) (hsrc : src < n)
    (hB : BfsBounds n ns d B) (halv : ∀ w ∈ alv, w < B) (hd0 : ∀ w ∈ dist₀, w < B)
    (hq0 : ∀ w ∈ q₀, w < B) (hdlen : dist₀.length = n) (hqlen : q₀.length = n) :
    Reasoning.Spec B (agree (bfsQState n d src off tgt alv dist₀ q₀))
      (embed bfsQSynth_impl)
      (fun _ σ' => ∃ D : List ℕ, σ'.arrs "dist" = D ∧ QPost n d src G alv hsrc D)
      (bfsQK n ns) := by
  have hspec := spec_of_hnRefine
    (Φ := fun st' : St => QPost n d src G alv hsrc st'.1)
    (Q := fun (ra : St) σ' => σ'.arrs "dist" = ra.1)
    (bfsQSynth' n d src off tgt alv dist₀ q₀)
    (bfsQS_correct hc hsrc hdlen hqlen)
    (bfsQ_state_holds n d src off tgt alv dist₀ q₀)
    (bfsQ_stateBound hB hc.shape (le_of_eq hc.last) hsrc halv hd0 hq0)
    (bfsQ_runs hc hsrc hB halv hd0 hq0 hdlen hqlen)
    (le_of_eq (ecash_bfsQTotal n ns))
    ?_
  · exact hspec.post (by rintro σ σ' - ⟨ra, hΦ, hread⟩; exact ⟨ra.1, hread, hΦ⟩)
  · intro ra s' cr σ' hΦ hst hag
    have he : (bfsQFrame n d src off tgt alv ∗
        (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn) ra ("dist", "q", "head", "tl") ∗
        bfsQHole n d src off tgt alv dist₀ q₀ ∗ GC)
        = (bfsQFrame n d src off tgt alv ∗ arrayAssn ra.1 "dist" ∗
          ((arrayAssn ra.2.1 "q" ∗ natAssn ra.2.2.1 "head" ∗ natAssn ra.2.2.2 "tl") ∗
            bfsQHole n d src off tgt alv dist₀ q₀) ∗ GC) := by
      simp only [prodAssn]
      ac_rfl
    rw [he] at hst
    exact readout_arr hst hag

/-- **The gate's export.** The synthesized queue BFS, embedded into
IMP+, decides every masked-distance threshold up to the cap from any
environment holding the block structure, the mask, the parameters, and
two scratch arrays — within `56·n + 40·ns + 33` time units, every value
below the bound. The statement is `RamBfs.bfs_spec`'s, at this package's
own `WD`/`maskOf` (adjacency characterization: `masked_maskOf_adj`);
the two deltas are P7/D-bo (the scratch arrays' initial entries sit
below the bound — `Ir.StateBound` is state-global where the baseline's
`BigStepB` bounds only what the run evaluates) and P7/D-bp (the scratch
cells appear, pinned at zero, because assertion-level ownership makes
them part of the footprint; the machine's memory starts zeroed, so the
instantiation is the natural one). -/
theorem bfsQ_spec {n ns d B src : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}
    (hc : Csr n ns G off tgt alv) (hsrc : src < n) (hB : BfsBounds n ns d B)
    (halv : ∀ w ∈ alv, w < B) :
    Reasoning.Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = src ∧ σ.vars "sent" = d + 1 ∧
        σ.vars "d" = d ∧ σ.vars "one" = 1 ∧ σ.vars "i" = 0 ∧ σ.vars "head" = 0 ∧
        σ.vars "a" = 0 ∧ σ.vars "tl" = 0 ∧ σ.vars "v" = 0 ∧ σ.vars "dv" = 0 ∧
        σ.vars "dv1" = 0 ∧ σ.vars "k0" = 0 ∧ σ.vars "v1" = 0 ∧ σ.vars "kend" = 0 ∧
        σ.vars "u" = 0 ∧ σ.vars "au" = 0 ∧ σ.vars "du" = 0 ∧
        σ.arrs "off" = off ∧ σ.arrs "tgt" = tgt ∧ σ.arrs "alv" = alv ∧
        (∃ dist₀, σ.arrs "dist" = dist₀ ∧ dist₀.length = n ∧ ∀ w ∈ dist₀, w < B) ∧
        (∃ q₀, σ.arrs "q" = q₀ ∧ q₀.length = n ∧ ∀ w ∈ q₀, w < B))
      (embed bfsQSynth_impl)
      (fun _ σ' => ∃ D : List ℕ, σ'.arrs "dist" = D ∧ D.length = n ∧
        ∀ v : Fin n, ∀ k, k ≤ d →
          (D[(v : ℕ)]! ≤ k ↔ Bfs.WD G (maskOf n alv) k ⟨src, hsrc⟩ v))
      (bfsQK n ns) := by
  intro σ hσ
  obtain ⟨hn', hsrc', hsent, hd', hone, hi, hhead, ha, htl', hv, hdv, hdv1, hk0, hv1,
    hkend, hu, hau, hdu, hoff, htgt', halv', ⟨dist₀, hdist₀, hdlen, hdb⟩,
    ⟨q₀, hq₀', hqlen, hqb⟩⟩ := hσ
  have hag : agree (bfsQState n d src off tgt alv dist₀ q₀) σ := by
    refine agree_ofPairs ?_ ?_
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> assumption
  obtain ⟨σ', hrun, D, hread, hQ⟩ :=
    (bfsQ_spec_at dist₀ q₀ hc hsrc hB halv hdb hqb hdlen hqlen) σ hag
  exact ⟨σ', hrun, D, hread, hQ.1, hQ.2⟩

/-! ## 14. The reached list, exported (R2D/D-c)

`bfsQS_correct` routes through `bfsQ`, whose last step projects the
distance array out of the result tuple, so its postcondition can only
speak of that array. The gate program itself returns the whole state,
queue included, and `BfsQ.Fr.qReached` reads the reached list off the
queue invariant at drain exit. This is the same assembly as
`BfsQ.bfsQ_correct`, run on `bfsQS` without the projection and against
`drainLoop_le'`, which carries the seed's `q[0] := src` through the
drain. -/

section Reached

open BfsQ (St QPost QReached Csr Fr bfsBudget bfsK popC scanC fillC iter cu rowSum
  fillLoop_le drainLoop_le' get!_set)

/-- **The gate program's reached list.** The synthesized search leaves,
beside the distance array it already specified, a queue whose first
`max tl 1` slots enumerate exactly the vertices it put within the
cap. -/
theorem bfsQS_reached {n ns d : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}
    {src : ℕ} {dist₀ q₀ : List ℕ} (hc : Csr n ns G off tgt alv)
    (hsrc : src < n) (hdlen : dist₀.length = n) (hqlen : q₀.length = n) :
    bfsQS n d src off tgt alv dist₀ q₀
      ≤ NRest.spec
          (fun st' : St => QPost n d src G alv hsrc st'.1 ∧
            QReached n d st'.1 st'.2.1 st'.2.2.2 ∧ st'.2.1.length = n)
          (fun _ => irUnit Currency.skip + liftACost (bfsBudget n ns)) := by
  have halv : src < alv.length := by rw [hc.shape.2.1]; exact hsrc
  have hq0 : (q₀.set 0 src)[0]! = src := by
    rw [get!_set q₀ 0 src 0 (by omega), if_pos rfl]
  -- the seed and the drain, from a filled distance array
  have htail : ∀ p : List ℕ × ℕ, (p.1.length = n ∧ ∀ j, j < n → p.1[j]! = d + 1) →
      (NRest.bindT (mopAset p.1 src 0) fun D =>
        NRest.bindT (mopAset q₀ 0 src) fun Q =>
          NRest.bindT (mopAget alv src) fun a =>
            NRest.bindT (irIf (decide (0 < a)) (mopConstN 1) (mopConstN 0)) fun tl =>
              NRest.bindT (BfsQ.pack4 D Q 0 tl) fun st =>
                BfsQ.drainLoop n d (d + 1) off tgt alv st)
        ≤ NRest.spec
            (fun st' : St => QPost n d src G alv hsrc st'.1 ∧
              QReached n d st'.1 st'.2.1 st'.2.2.2 ∧ st'.2.1.length = n)
            (fun _ => liftACost (n • iter popC + ns • iter scanC
              + (cu Currency.aset + cu Currency.aset + cu Currency.aget + cu Currency.ite
                + cu Currency.const + cu Currency.skip + cu Currency.skip + cu Currency.skip
                + cu Currency.«while»))) := by
    rintro p ⟨hplen, hpfill⟩
    have hseed := Fr.seed (n := n) (d := d) (G := G) (alv := alv) (s := ⟨src, hsrc⟩)
      hplen hqlen hpfill
    have hrow0 : rowSum off (q₀.set 0 src) 0 = 0 := by simp [rowSum]
    have hdrain := drainLoop_le' (d := d) (s := ⟨src, hsrc⟩) hc src n
      (p.1.set src 0, q₀.set 0 src, 0, if 0 < alv[src]! then 1 else 0) hseed hq0 (by simp)
    rw [hrow0, Nat.sub_zero, Nat.sub_zero] at hdrain
    have hpost : ∀ z' : St, ((Fr n d G alv ⟨src, hsrc⟩ z'.1 z'.2.1 z'.2.2.1 z'.2.2.2 ∧
        z'.2.2.2 ≤ z'.2.2.1) ∧ z'.2.1[0]! = src) →
          QPost n d src G alv hsrc z'.1 ∧ QReached n d z'.1 z'.2.1 z'.2.2.2 ∧
            z'.2.1.length = n := by
      rintro z' ⟨⟨hfr, hle⟩, hz0⟩
      rw [le_antisymm hfr.hdle hle] at hfr
      exact ⟨⟨hfr.dlen, fun v k hk => hfr.dist_le_iff v hk⟩, hfr.qReached hz0, hfr.qlen⟩
    have hstep : ∀ tl : ℕ, tl = (if 0 < alv[src]! then 1 else 0) →
        (NRest.bindT (BfsQ.pack4 (p.1.set src 0) (q₀.set 0 src) 0 tl) fun st =>
          BfsQ.drainLoop n d (d + 1) off tgt alv st)
          ≤ NRest.spec
              (fun st' : St => QPost n d src G alv hsrc st'.1 ∧
                QReached n d st'.1 st'.2.1 st'.2.2.2 ∧ st'.2.1.length = n)
              (fun _ => (irUnit Currency.skip + irUnit Currency.skip + irUnit Currency.skip)
                + liftACost (E2 (iter popC) (iter scanC) n ns + cu Currency.«while»)) := by
      rintro tl rfl
      simp only [BfsQ.pack4, mopPair_def, bindT_unitT, NRest.consume_consume]
      refine le_trans (NRest.consume_mono
        (le_trans hdrain (spec_mono hpost fun _ _ => le_rfl)) le_rfl) (le_of_eq ?_)
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
    simp only [E2, iter, liftACost_add, liftACost_nsmul, liftACost_cu]
    ac_rfl
  simp only [bfsQS, fillLoop'_eq, drainLoop'_eq, mopPair_def, bindT_unitT]
  refine le_trans (NRest.consume_mono
    (le_trans (NRest.bindT_mono (fillLoop_le n (d + 1) n dist₀ 0 hdlen (by omega)
      (fun j hj => absurd hj (by omega))) fun _ => le_rfl)
      (bindT_spec_le _ _ _ _ _ htail)) le_rfl) ?_
  rw [Sepref.consume_spec]
  refine spec_mono (fun _ h => h) fun _ _ => ?_
  have hsplit : irUnit Currency.skip + liftACost (bfsBudget n ns)
      = (irUnit Currency.skip
          + (liftACost ((n - (0 : ℕ)) • iter fillC + cu Currency.«while»)
            + liftACost (n • iter popC + ns • iter scanC
              + (cu Currency.aset + cu Currency.aset + cu Currency.aget + cu Currency.ite
                + cu Currency.const + cu Currency.skip + cu Currency.skip + cu Currency.skip
                + cu Currency.«while»))))
        + (irUnit Currency.add + irUnit Currency.const) := by
    simp only [bfsBudget, bfsK, iter, liftACost_add, liftACost_nsmul, liftACost_cu,
      Nat.sub_zero]
    ac_rfl
  rw [hsplit]
  exact cost_le_add _ _

end Reached

end Export

-- The demo run's cost is covered by the exported budget (`n = 5`,
-- `ns = 6`: `bfsQK 5 6 = 553`), and the check can tell a wrong budget.
#guard (Ir.evalFuel 4000 bfsQSynth_impl (demoState 3 0 1)).map
  (fun p => decide (Codegen.cash p.2 ≤ bfsQK 5 6)) = some true
#guard ¬ ((Ir.evalFuel 4000 bfsQSynth_impl (demoState 3 0 1)).map
  (fun p => decide (Codegen.cash p.2 ≤ 100)) = some true)

/-- info: 'Lax13Proofs.Refine.BfsQSynth.bfsQ_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bfsQ_spec

/-! ## 14. Telemetry (the plan's P7 gate numbers, final)

* **Line counts** (a nesting-aware scan; it reproduces wave A's own
  1,015 on wave A's file before this wave's retrofit).
  - baseline `RamBfs.lean`: **1,201 raw**, cost `51n + 44ns + 30`;
  - wave A `BfsQ.lean`: **1,448 raw / 1,023 Lean**;
  - wave B, this file: **1,509 raw / 899 Lean**, of which **108 are the
    pinned `Com`** (the tool's output, not authored reasoning), 24 the
    demo of §8, **560 Lean the bounds pass of §12** (the two invariants,
    their preservation lemmas, the three walk lemmas, the ownership
    peel and the bound of the initial store) and 86 Lean the export
    assembly of §13;
  - **P7 total: 2,957 raw / 1,922 Lean, or 1,814 Lean net of the
    pinned tool output.** Tower additions made along the way and
    excluded per the design note's counting rule (disclosed):
    `Codegen/BigStepB.lean` +204 raw (`bpre`,
    `BigStep.bigStepB_of_inv` — reusable by every synthesized
    program), `Codegen/Cash.lean` +37 raw (the run projection),
    `Sepref/IrLoop.lean` +188 raw (wave A's tower gap),
    the five driver repairs.
  Against the 400-line gate that is a **miss by roughly 4.5×**, and
  the miss decomposes: wave A's queue invariant (`Fr`, `SInv`, the
  tiling — the fourteen clauses `RamBfs.Frontier` also carries) is a
  third of wave A; the bounds pass is 560 lines where the baseline
  pays for the same facts inside its `Run` derivation; synthesis
  annotations proper (the goal statement, three `LOOP_VARIANT`s,
  `mopSucc`) are small. What the tower removed entirely is the machine
  half: no `Run`, no `Env`, no `wvars`/`warrs` bookkeeping, no
  hand-written frame anywhere in either file.

* **Hand-written frame clauses: 0**, across both files. No `fri` call,
  no `sepConj` rearrangement, and the two `ac_rfl`s outside rule
  wrappers are on cost sums (`ECost`) and on the §13 readout equality
  `he` — an assertion *equation* handed to `rw`, the shape
  `spec_of_hnRefine`'s P5 consumer also uses; strictly counted that is
  1 frame-shaped step in the export assembly, not in any derivation.
  *Caveat, stated rather than hidden:* the three `MERGE_arrayAssn_*`
  rules of §2 are entailments registered in a database and consumed by
  `mergeSolve`, never applied by hand — the same shape as
  `Sepref/Frame.lean`'s own `MERGE_natAssn_junk`, which P4's telemetry
  counts as not-a-frame-clause. Read the other way the count is 3.

* **Synthesis wall clock**, warm build: whole-program `bfsQSynth` —
  three nested loops, two nested branches, a four-tuple state carrying
  two arrays at every level — **≈49 s**; `fillSynth` ≈1.5 s. Before
  §10's repairs the same synthesis did not finish in nine minutes.

* **Bounds-annotation lines: 560** (§12, measured; the number §11
  priced). The route is the one §11 recommended — along the run,
  `BigStep.bigStepB_of_inv` — so there are **no in-range goals and no
  `room`/`undisc` counting anywhere**: `q[tl] := u`'s own side
  condition is what makes `tl ≤ n` inductive. What the 560 lines
  actually are: the two invariants and their preservation lemmas
  (≈150), the three loop-body walks (≈250), the ownership peel and
  initial bound (≈100), glue (≈60). P5's "≈10 lines per program" is
  confirmed **not** to transfer to a program whose write indices are
  invariant-bounded; this is the honest figure the P8 verdict should
  use, and it prices the alternative too — a `wordAssn`-style
  refactor would move these lines into synthesis side conditions, not
  delete them.

* **Cost constants: `bfsQK n ns = 56·n + 40·ns + 33`** IMP+ time
  units, from `ecash_bfsQTotal` (computed by `decide +kernel` from the
  per-iteration accounts, not tuned), against the baseline's
  hand-tuned `51n + 44ns + 30`. Same shape, coefficients within 10 %
  either way (`56 > 51` on vertices, `40 < 44` on slots). The §13
  demo `#guard` checks coverage on a real run (`cash ≤ bfsQK 5 6 =
  553`) and refutes a wrong budget (100).

* **Axioms.** `bfsQSynth'`, `fillSynth`, `drain_variant'`,
  `bfsQS_correct`, `hnr_mop_succ` (§9) and **`bfsQ_spec` (§13)** all
  pinned at `[propext, Classical.choice, Quot.sound]`.

* **Refuted before proved.** §8 runs the *synthesized* program on
  `RamBfs`'s own five-vertex arena — mask on, mask off at vertex 2, two
  cap settings and a second source — against wave A's computable twin,
  with one pinned negative control; the twin is itself already checked
  against `RamBfs`'s four published readings and against P1's
  independent level-based twin. `mopSucc`'s rule was checked to be the
  one the driver picks before the program was written to depend on it
  (§5's pinned failure). The `subst`-direction and `omega`-through-
  `Ir.Val` traps both fired during §12 and are recorded in its header.
-/

end BfsQSynth

end Lax13Proofs.Refine
