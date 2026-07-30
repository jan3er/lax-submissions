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

## 11. What is left of the gate chain, and what it actually costs
(P7/D-bj)

`bfsQSynth'` is the synthesized program and `bfsQS_correct` is its
abstract bound; the two gaps §10 of the previous revision named are
closed (`popF'_eq`, wave A's own `popF` now builds the row scan's
state; `le_spec_of_bindT_returnT`, P7/T-c). What remains between here
and a `bfs_spec`-shaped export is:

```
hbd : ∃ s' κ, Ir.BigStepB B bfsQSynth_impl s₀ s' κ     -- ir_bound_vcg
    ▸ spec_of_hnRefine (bfsQSynth') (bfsQS_correct) …  -- Cash.lean
    ▸ readout_arr at "dist"                            -- Cash.lean
```

The middle two steps are one application each. The first is **not** the
ten-line annotation P5's telemetry measured on its toys, and the reason
is worth recording because it changes what the bounds pass costs on a
real program.

`Codegen/BigStepB.lean`'s `aset` rule carries `hk : k < xs.length`: a
store only steps when its index is in range. On P5's toys every store's
index was the loop counter and the guard bounded it, so the obligation
was free. Here the drain's inner scan performs `q[tl] := u`, and `tl`
is bounded by *nothing in the program's control flow* — it is bounded
because the queue never receives more vertices than there are
undiscovered live ones, which is wave A's `room`/`undisc` counting
argument (P7/D-d). So the bounds pass for this program has to re-run
that argument over `Ir.State`, or be handed it.

Two honest routes, for whoever takes this next:

1. **Re-run `room` at the IR.** The drain's bounds invariant carries
   `tl + |undisc| ≤ n` exactly as `popP` does, and the scan's carries it
   too; the counting steps are `Finset.card_erase_of_mem` in both
   places, as in wave A's `scanP_step`. Straightforward, and perhaps
   sixty lines, but it is a *second* proof of a fact already proved.
2. **Export the fact from the abstract side.** `hnRefine` already knows
   the program does not fail, and `mopAset`'s own `assert` is exactly
   `k < xs.length`; what is missing is a lemma turning a plain `BigStep`
   (which `hnRefineD` produces) plus a `StateBound` invariant into a
   `BigStepB`. That lemma is the right fix — it would retire the whole
   per-program bounds obligation, not just this one — and it belongs in
   `Codegen/BigStepB.lean` beside `BigStep.bigStepB_of_eq`.

Route 2 is the recommendation: P5's `hbd` hypothesis exists only to
supply the value bound, and the run it re-derives is the run
`spec_of_hnRefine` already has in hand.

## 12. Telemetry (the plan's P7 gate numbers)

* **Line counts** (a nesting-aware scan; it reproduces wave A's own
  1,015 on wave A's file before this wave's retrofit).
  - baseline `RamBfs.lean`: **1,201 raw**, cost `51n + 44ns + 30`;
  - wave A `BfsQ.lean`: **1,448 raw / 1,023 Lean** (was 1,435/1,015;
    this wave added `pack4_bindT`, the `pack4` inside `popF`, three
    summands to `popC` and three to one slack term);
  - wave B, this file: **646 raw / 247 Lean**, of which **108 are the
    pinned `Com`** (`#guard bfsQSynth_impl = …`, the tool's output, not
    authored reasoning) and 24 the demo of §8;
  - **P7 total: 2,094 raw / 1,270 Lean, or 1,162 Lean net of the pinned
    tool output.**
  Against the 400-line gate that is a miss by roughly a factor of
  three, and §12 of wave A's file says where the lines are: the queue
  invariant (`Fr`, `SInv`, the tiling) is a third of wave A and it is
  the part a tower cannot shrink — it is the fourteen clauses
  `RamBfs.Frontier` carries, for the same reasons. What the tower did
  remove is the *machine* half: there is no `Run`, no `Env`, no
  `wvars`/`warrs` bookkeeping and no hand-written frame anywhere in
  either file.

* **Hand-written frame clauses: 0**, across both files. No `fri` call,
  no `sepConj` rearrangement, no `ac_rfl` on an assertion; the `ac_rfl`s
  are on cost sums (`ECost`, an `AddCommMonoid`). *Caveat, stated
  rather than hidden:* the three `MERGE_arrayAssn_*` rules of §2 are
  entailments between single conjuncts registered in a database and
  consumed by `mergeSolve`, never applied by hand — the same shape as
  `Sepref/Frame.lean`'s own `MERGE_natAssn_junk`, which P4's telemetry
  counts as not-a-frame-clause. Read the other way the count for this
  file is 3, not 0.

* **Synthesis wall clock**, warm build, `lake env lean` on this file
  against a 3.8 s import-only baseline: whole file **55 s**, of which
  `bfsQSynth` — three nested loops, two nested branches, a four-tuple
  state carrying two arrays at every level — is **about 49 s** and
  `fillSynth` about 1.5 s. Before §10's three repairs the same
  synthesis did not finish in nine minutes. Whole package: 3,041 jobs.

* **Bounds-annotation lines: 0**, and §11 says why that number is not
  the good news it looks like: the pass is not written, because on this
  program it is not the ten-line annotation P5 measured.

* **Cost constants vs the baseline's `51n + 44ns + 30`: not available.**
  The comparison is a `cash`/`ecash` evaluation of `bfsBudget n ns` and
  it is downstream of the bounds pass. What *is* fixed is the abstract
  budget `bfsQS_correct` carries: `n • iter fillC + n • iter popC +
  ns • iter scanC + bfsK + ir.skip`, linear in `n` and `ns` with
  explicit small constants at the IR's own currencies, `fillC` three
  units, `popC` seventeen, `scanC` fourteen.

* **Axioms.** `bfsQSynth'`, `fillSynth`, `drain_variant'`,
  `bfsQS_correct` and `hnr_mop_succ` are pinned in §9 at `[propext,
  Classical.choice, Quot.sound]` and nothing else.

* **Refuted before proved.** §8 runs the *synthesized* program on
  `RamBfs`'s own five-vertex arena — mask on, mask off at vertex 2, two
  cap settings and a second source — against wave A's computable twin,
  with one pinned negative control; the twin is itself already checked
  against `RamBfs`'s four published readings and against P1's
  independent level-based twin. `mopSucc`'s rule was checked to be the
  one the driver picks *before* the program was written to depend on
  it: the control — the same fill loop at wave A's `fillF`, with one
  extra `junkCell "t"` — fails, and names the reason (`hnr_mop_pair`
  cannot match `hnCtxt natAssn ‹› "i"` against the goal's
  `hnCtxt natAssn ‹› "t"`: the sum went to the scratch cell and the loop
  state can no longer be rebuilt). `fillF'_eq`, `scanF'_eq`,
  `scanLoop'_eq` and `popF'_eq` are the standing check that no program
  change in §3 is anything but cost.
-/

end BfsQSynth

end Lax13Proofs.Refine
