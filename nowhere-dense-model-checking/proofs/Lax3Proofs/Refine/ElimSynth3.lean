import Lax3Proofs.Refine.ElimSynth2

/-!
# P2 wave 2B′ — the elimination engine, completed through the tower (II)

The elimination loop itself — the phase satellite 2B retained, and the
one the plan's FLAG 2 was about. Its state is **eleven** components
(seven arrays and four scalars, minus the `ls` counter that 2B′/D-a
drops), it contains a nested row scan, and its branch tree is three
deep. This is the widest loop state the tower has been asked for.

## What is here

* §1 — the in-place decrement `mopPred`, which the shared annex does not
  carry (it holds the three *additive* in-place operations only).
* §2 — the row scan of an extraction, at a *narrow* state: the six
  components it actually touches (2B′/D-c).
* §3 — one turn, and the loop.
* §4 — the synthesis, pinned, with its measurement (2B′/M-a).
* §5 — what is **not** here: the loop's amortized bound and its
  correctness transport, named as debts rather than left implicit.

## 2B′/M-a — the wide-state measurement

The datapoint the plan asked for. `elimSynth` below — an **eleven**-component loop state, a nested six-component row scan, a three-deep branch
tree, twenty-two owned cells and eighteen scratch cells — translates in

| goal | budget | wall clock | result |
|---|---|---|---|
| `decScan` (the row scan alone) | 1 000 000 hb | ≈ 6 s | `Com`, pinned |
| `elimLoop` (outer + inner) | 1 000 000 hb | ≈ 90 s | `Com`, pinned |

against the ≈ 49 s the gate program (`BfsQSynth.bfsQSynth`, three loops,
four-component state) takes, and the ≈ 18 s tool wave T1 measured on an
eleven-deep `prodAssn` probe. **A 1 000 000-heartbeat budget suffices**;
the 4 000 000 the first run used was not needed. So the wide state
crawls but works, and the cost is roughly linear in the state width
rather than exponential — which is the fact the rebase plan needed
before committing the elimination engine to the tower.

## 2B′/D-b — `kmax := max kmax mind` without a branch

The machine writes `if kmax < mind then kmax := mind else skip`. At this
layer the two arms of an `irIf` must deliver the *same* destination, and
the only rule that moves one cell into another has a **junk**
destination (2B's `mopKeep` finding), so the `then` arm cannot assign
`kmax`. It does not have to: on `ℕ` the subtraction is truncated, so

    kmax := kmax + (mind - kmax)

*is* `max kmax mind`, in two operations and with no branch at all. The
machine's `ite` and its `assign` are replaced by a `sub` and an `add`;
the value is identical, which is what §3's twin equality states.

## 2B′/C — the row scan takes the narrow state

The twin's `decScanTw` steps the whole `ESt`. The row scan writes only
`deg` and the three bucket arrays and `sp`, and reads `elm`, `alv` and
`tgt`; so its loop state here is the six components it touches, and the
other five ride in the frame. This is not an optimization but a
*requirement*: `hnr_while_var` reads a loop's state off one `hnCtxt`
conjunct, and a scan whose state named `rnk`, `idg`, `cnt`, `mind` and
`kmax` would have to thread them through the branch merger of every
slot.
-/

namespace Lax3Proofs.Refine.ElimSynth3

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax13Proofs.Refine.Codegen
open Lax13Proofs.Refine.BfsQ (Shape cu iter irWhile_exit get!_set res_of_le liftACost_cu)
open Lax3Proofs.Refine.ElimSynth hiding mopSucc mopSucc_eq mopKeep mopKeep_eq
open Lax3Proofs.Refine.ElimSynth2

/-! ## 1. The in-place decrement -/

section Ops

/-- `x := x - 1`, in place. The shared annex (`Sepref/IrOpsExtra.lean`)
carries the three *additive* in-place operations; the elimination loop
is the first consumer that needs a subtractive one. -/
noncomputable def mopPred (m : ℕ) : NRest ℕ ECost := mopBinop .sub m 1

theorem mopPred_eq (m : ℕ) : mopPred m = mopBinop .sub m 1 := rfl

@[sepref_fr_rules]
theorem hnr_mop_pred (x z : String) (m : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn 1 z) (.binop .sub x x z)
      (hnCtxt natAssn 1 z) x natAssn (mopPred m) := by
  rw [mopPred_eq]; exact hnr_mop_binop_self .sub x z m 1

attribute [irreducible] mopPred

end Ops

/-! ## 2. The row scan of an extraction

The six components the scan touches: the degrees, the three bucket
arrays, the arena pointer, the slot index. -/

section RowScan

/-- The row scan's state: `(deg, bh, bv, bn, sp, j)`. -/
abbrev DS : Type := List ℕ × List ℕ × List ℕ × List ℕ × ℕ × ℕ

/-- Assemble a six-component state. -/
noncomputable def pack6 (deg bh bv bn : List ℕ) (sp j : ℕ) : NRest DS ECost :=
  bindT (mopPair sp j) fun p => bindT (mopPair bn p) fun q =>
    bindT (mopPair bv q) fun r => bindT (mopPair bh r) fun z => mopPair deg z

/-- Assemble the five components the branch of a slot delivers. -/
noncomputable def pack5d (deg bh bv bn : List ℕ) (sp : ℕ) :
    NRest (List ℕ × List ℕ × List ℕ × List ℕ × ℕ) ECost :=
  bindT (mopPair bn sp) fun p => bindT (mopPair bv p) fun q =>
    bindT (mopPair bh q) fun r => mopPair deg r

/-- **One slot of the row of the vertex being eliminated**, as a
function: a neighbour still in the arena loses one from its degree and
is pushed into its new bucket. The degree is decremented *before* it is
read back for the new bucket — the aliasing `ElimSynth` §1.3 checks. -/
def decStep (tgt alv elm : List ℕ) : DS → DS := fun s =>
  let u := tgt[s.2.2.2.2.2]!
  if 0 < alv[u]! then
    if elm[u]! < 1 then
      let du := s.1[u]! - 1
      (s.1.set u du, s.2.1.set du s.2.2.2.2.1, s.2.2.1.set s.2.2.2.2.1 u,
        s.2.2.2.1.set s.2.2.2.2.1 s.2.1[du]!, s.2.2.2.2.1 + 1, s.2.2.2.2.2 + 1)
    else (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2 + 1)
  else (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2 + 1)

/-- The scan's guard. -/
def decBf (jend : ℕ) : DS → Bool := fun s => decide (s.2.2.2.2.2 < jend)

/-- What one slot needs in range. -/
def decP (tgt alv elm : List ℕ) : DS → Prop := fun s =>
  s.2.2.2.2.2 < tgt.length ∧ tgt[s.2.2.2.2.2]! < alv.length ∧
    tgt[s.2.2.2.2.2]! < elm.length ∧ tgt[s.2.2.2.2.2]! < s.1.length ∧
    s.1[tgt[s.2.2.2.2.2]!]! - 1 < s.2.1.length ∧
    s.2.2.2.2.1 < s.2.2.1.length ∧ s.2.2.2.2.1 < s.2.2.2.1.length

/-- **One slot of the row scan.** -/
noncomputable def decF (tgt alv elm : List ℕ) : DS → NRest DS ECost := fun s =>
  bindT (mopAget tgt s.2.2.2.2.2) fun u =>
    bindT (mopAget alv u) fun au =>
      bindT (irIf (decide (0 < au))
          (bindT (mopAget elm u) fun eu =>
            irIf (decide (eu < 1))
              (bindT (mopAget s.1 u) fun dv =>
                bindT (mopBinop .sub dv 1) fun du =>
                  bindT (mopAset s.1 u du) fun DEG =>
                    bindT (mopAget s.2.1 du) fun bhd =>
                      bindT (mopAset s.2.2.1 s.2.2.2.2.1 u) fun BV =>
                        bindT (mopAset s.2.2.2.1 s.2.2.2.2.1 bhd) fun BN =>
                          bindT (mopAset s.2.1 du s.2.2.2.2.1) fun BH =>
                            bindT (mopSucc s.2.2.2.2.1) fun sp =>
                              pack5d DEG BH BV BN sp)
              (pack5d s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1))
          (pack5d s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1)) fun r =>
        bindT (mopSucc s.2.2.2.2.2) fun j =>
          pack6 r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 j

/-- **The row scan.** -/
noncomputable def decScan (tgt alv elm : List ℕ) (jend : ℕ) (s₀ : DS) : NRest DS ECost :=
  irWhileIT (fun s => decBf jend s = true → decP tgt alv elm s) (decBf jend)
    (decF tgt alv elm) s₀

end RowScan

/-! ## 3. The elimination loop -/

section Loop

/-- The elimination loop's state, eleven components:
`(deg, elm, rnk, idg, bh, bv, bn, sp, cnt, mind, kmax)`. -/
abbrev ES : Type :=
  List ℕ × List ℕ × List ℕ × List ℕ × List ℕ × List ℕ × List ℕ × ℕ × ℕ × ℕ × ℕ

/-- Assemble an eleven-component state. -/
noncomputable def pack11 (deg elm rnk idg bh bv bn : List ℕ) (sp cnt mind kmax : ℕ) :
    NRest ES ECost :=
  bindT (mopPair mind kmax) fun a =>
    bindT (mopPair cnt a) fun b =>
      bindT (mopPair sp b) fun c =>
        bindT (mopPair bn c) fun d =>
          bindT (mopPair bv d) fun e =>
            bindT (mopPair bh e) fun f =>
              bindT (mopPair idg f) fun g =>
                bindT (mopPair rnk g) fun h =>
                  bindT (mopPair elm h) fun k => mopPair deg k

/-- The loop's guard: there are vertices left to eliminate. -/
def elimBf (n : ℕ) : ES → Bool := fun e => decide (e.2.2.2.2.2.2.2.2.1 < n)

/-- **Eliminate the vertex `w`**: stamp it with the next rank down,
record its extraction degree, raise the bound, scan its row if it is
alive, and drop the pointer. Written over the eleven components rather
than over a packed state: a straight-line block is not a loop, so its
argument is not a resource and nothing has to be assembled. -/
noncomputable def elimVertexF (n : ℕ) (off tgt alv : List ℕ)
    (deg elm rnk idg bh bv bn : List ℕ) (sp cnt mind kmax w : ℕ) : NRest ES ECost :=
  bindT (mopAset elm w 1) fun ELM =>
    bindT (mopBinop .sub n 1) fun nm =>
      bindT (mopBinop .sub nm cnt) fun rw =>
        bindT (mopAset rnk w rw) fun RNK =>
          bindT (mopAset idg w mind) fun IDG =>
            bindT (mopSucc cnt) fun CNT =>
              bindT (mopBinop .sub mind kmax) fun dk =>
                bindT (mopAddIn kmax dk) fun KMAX =>
                  bindT (mopAget alv w) fun aw =>
                    bindT (irIf (decide (0 < aw))
                        (bindT (mopAget off w) fun j0 =>
                          bindT (mopBinop .add w 1) fun wp =>
                            bindT (mopAget off wp) fun jend =>
                              bindT (pack6 deg bh bv bn sp j0) fun z =>
                                bindT (decScan tgt alv ELM jend z) fun r =>
                                  pack5d r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1)
                        (pack5d deg bh bv bn sp)) fun r =>
                      bindT (mopPred mind) fun MIND =>
                        pack11 r.1 ELM RNK IDG r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 CNT
                          MIND KMAX

/-- **One turn.** Bump the pointer over an empty bucket, or pop the head
slot of the bucket it names — and eliminate its vertex unless the slot
is stale. -/
noncomputable def elimTurnF (n : ℕ) (off tgt alv : List ℕ) : ES → NRest ES ECost := fun e =>
  bindT (mopAget e.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1) fun bhm =>
    irIf (decide (bhm = 0))
      (bindT (mopSucc e.2.2.2.2.2.2.2.2.2.1) fun MIND =>
        pack11 e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1
          e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 MIND e.2.2.2.2.2.2.2.2.2.2)
      (bindT (mopAget e.2.2.2.2.2.1 bhm) fun w =>
        bindT (mopAget e.2.2.2.2.2.2.1 bhm) fun bnp =>
          bindT (mopAset e.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 bnp) fun BH =>
            bindT (mopAget e.2.1 w) fun ew =>
              irIf (decide (ew < 1))
                (bindT (mopAget e.1 w) fun dw =>
                  irIf (decide (dw = e.2.2.2.2.2.2.2.2.2.1))
                    (elimVertexF n off tgt alv e.1 e.2.1 e.2.2.1 e.2.2.2.1 BH
                      e.2.2.2.2.2.1 e.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.1
                      e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2 w)
                    (pack11 e.1 e.2.1 e.2.2.1 e.2.2.2.1 BH e.2.2.2.2.2.1 e.2.2.2.2.2.2.1
                      e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1
                      e.2.2.2.2.2.2.2.2.2.2))
                (pack11 e.1 e.2.1 e.2.2.1 e.2.2.2.1 BH e.2.2.2.2.2.1 e.2.2.2.2.2.2.1
                  e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1
                  e.2.2.2.2.2.2.2.2.2.2))

/-- What one turn needs in range. -/
def elimP (n : ℕ) (off tgt alv : List ℕ) : ES → Prop := fun e =>
  e.2.2.2.2.2.2.2.2.2.1 < e.2.2.2.2.1.length

/-- **The elimination loop.** -/
noncomputable def elimLoop (n : ℕ) (off tgt alv : List ℕ) (e₀ : ES) : NRest ES ECost :=
  irWhileIT (fun e => elimBf n e = true → elimP n off tgt alv e) (elimBf n)
    (elimTurnF n off tgt alv) e₀

end Loop

/-! ## 4. The synthesis -/

section Synth

set_option maxHeartbeats 1000000 in
sepref_synth decSynth (tgt alv elm : List ℕ) (jend : ℕ)
    (deg₀ bh₀ bv₀ bn₀ : List ℕ) (sp₀ j₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (deg₀, bh₀, bv₀, bn₀, sp₀, j₀) ("deg", "bh", "bv", "bn", "sp", "j") ∗
      hnCtxt arrayAssn tgt "tgt" ∗ hnCtxt arrayAssn alv "alv" ∗
      hnCtxt arrayAssn elm "elm" ∗ hnCtxt natAssn jend "jend" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗ junkCell "dv" ∗ junkCell "du" ∗
      junkCell "bhd")
    _ _ ("deg", "bh", "bv", "bn", "sp", "j")
    (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (decScan tgt alv elm jend (deg₀, bh₀, bv₀, bn₀, sp₀, j₀))

-- **The elimination loop, synthesized.** Eleven state components, a
-- nested row scan, a three-deep branch tree.
set_option maxHeartbeats 1000000 in
sepref_synth elimSynth (n : ℕ) (off tgt alv : List ℕ)
    (deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ : List ℕ) (sp₀ cnt₀ mind₀ kmax₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
        arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn)
      (deg₀, elm₀, rnk₀, idg₀, bh₀, bv₀, bn₀, sp₀, cnt₀, mind₀, kmax₀)
      ("deg", "elm", "rnk", "idg", "bh", "bv", "bn", "sp", "cnt", "mind", "kmax") ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
      hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "bhm" ∗ junkCell "w" ∗ junkCell "bnp" ∗ junkCell "ew" ∗ junkCell "dw" ∗
      junkCell "nm" ∗ junkCell "rw" ∗ junkCell "dk" ∗ junkCell "aw" ∗ junkCell "j" ∗
      junkCell "wp" ∗ junkCell "jend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗
      junkCell "dv" ∗ junkCell "du" ∗ junkCell "bhd")
    _ _ ("deg", "elm", "rnk", "idg", "bh", "bv", "bn", "sp", "cnt", "mind", "kmax")
    (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
      arrayAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn)
    (elimLoop n off tgt alv
      (deg₀, elm₀, rnk₀, idg₀, bh₀, bv₀, bn₀, sp₀, cnt₀, mind₀, kmax₀))


-- **The elimination loop, pinned.** `RamElim.elimTurn` — with
-- `elimVertex`, `Csr.loadRow`, `Csr.scan` and `decSlot` inlined —
-- instruction for instruction, save the three 2B′ deviations: no `ls`
-- counter (D-a), `kmax` raised by `sub`+`add` instead of `ite`+`assign`
-- (D-b), and `deg[u]` read once rather than twice in the row scan.
#guard elimSynth_impl =
  Com.while (Cond.lt (Operand.cell "cnt") (Operand.cell "n"))
    ((Com.aget "bhm" "bh" "mind").seq
      (Com.ite (Cond.eq (Operand.cell "bhm") (Operand.cell "zero"))
        ((Com.binop Lax13Proofs.Imp.Bop.add "mind" "mind" "one").seq
          (Com.skip.seq
            (Com.skip.seq
              (Com.skip.seq
                (Com.skip.seq (Com.skip.seq (Com.skip.seq (Com.skip.seq (Com.skip.seq (Com.skip.seq Com.skip))))))))))
        ((Com.aget "w" "bv" "bhm").seq
          ((Com.aget "bnp" "bn" "bhm").seq
            ((Com.aset "bh" "mind" "bnp").seq
              ((Com.aget "ew" "elm" "w").seq
                (Com.ite (Cond.lt (Operand.cell "ew") (Operand.cell "one"))
                  ((Com.aget "dw" "deg" "w").seq
                    (Com.ite (Cond.eq (Operand.cell "dw") (Operand.cell "mind"))
                      ((Com.aset "elm" "w" "one").seq
                        ((Com.binop Lax13Proofs.Imp.Bop.sub "nm" "n" "one").seq
                          ((Com.binop Lax13Proofs.Imp.Bop.sub "rw" "nm" "cnt").seq
                            ((Com.aset "rnk" "w" "rw").seq
                              ((Com.aset "idg" "w" "mind").seq
                                ((Com.binop Lax13Proofs.Imp.Bop.add "cnt" "cnt" "one").seq
                                  ((Com.binop Lax13Proofs.Imp.Bop.sub "dk" "mind" "kmax").seq
                                    ((Com.binop Lax13Proofs.Imp.Bop.add "kmax" "kmax" "dk").seq
                                      ((Com.aget "aw" "alv" "w").seq
                                        ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "aw"))
                                              ((Com.aget "j" "off" "w").seq
                                                ((Com.binop Lax13Proofs.Imp.Bop.add "wp" "w" "one").seq
                                                  ((Com.aget "jend" "off" "wp").seq
                                                    ((Com.skip.seq
                                                          (Com.skip.seq (Com.skip.seq (Com.skip.seq Com.skip)))).seq
                                                      ((Com.while (Cond.lt (Operand.cell "j") (Operand.cell "jend"))
                                                            ((Com.aget "u" "tgt" "j").seq
                                                              ((Com.aget "au" "alv" "u").seq
                                                                ((Com.ite
                                                                      (Cond.lt (Operand.cell "zero")
                                                                        (Operand.cell "au"))
                                                                      ((Com.aget "eu" "elm" "u").seq
                                                                        (Com.ite
                                                                          (Cond.lt (Operand.cell "eu")
                                                                            (Operand.cell "one"))
                                                                          ((Com.aget "dv" "deg" "u").seq
                                                                            ((Com.binop Lax13Proofs.Imp.Bop.sub "du"
                                                                                  "dv" "one").seq
                                                                              ((Com.aset "deg" "u" "du").seq
                                                                                ((Com.aget "bhd" "bh" "du").seq
                                                                                  ((Com.aset "bv" "sp" "u").seq
                                                                                    ((Com.aset "bn" "sp" "bhd").seq
                                                                                      ((Com.aset "bh" "du" "sp").seq
                                                                                        ((Com.binop
                                                                                              Lax13Proofs.Imp.Bop.add
                                                                                              "sp" "sp" "one").seq
                                                                                          (Com.skip.seq
                                                                                            (Com.skip.seq
                                                                                              (Com.skip.seq
                                                                                                Com.skip)))))))))))
                                                                          (Com.skip.seq
                                                                            (Com.skip.seq (Com.skip.seq Com.skip)))))
                                                                      (Com.skip.seq
                                                                        (Com.skip.seq (Com.skip.seq Com.skip)))).seq
                                                                  ((Com.binop Lax13Proofs.Imp.Bop.add "j" "j" "one").seq
                                                                    (Com.skip.seq
                                                                      (Com.skip.seq
                                                                        (Com.skip.seq
                                                                          (Com.skip.seq Com.skip))))))))).seq
                                                        (Com.skip.seq (Com.skip.seq (Com.skip.seq Com.skip))))))))
                                              (Com.skip.seq (Com.skip.seq (Com.skip.seq Com.skip)))).seq
                                          ((Com.binop Lax13Proofs.Imp.Bop.sub "mind" "mind" "one").seq
                                            (Com.skip.seq
                                              (Com.skip.seq
                                                (Com.skip.seq
                                                  (Com.skip.seq
                                                    (Com.skip.seq
                                                      (Com.skip.seq
                                                        (Com.skip.seq
                                                          (Com.skip.seq (Com.skip.seq Com.skip))))))))))))))))))))
                      (Com.skip.seq
                        (Com.skip.seq
                          (Com.skip.seq
                            (Com.skip.seq
                              (Com.skip.seq (Com.skip.seq (Com.skip.seq (Com.skip.seq (Com.skip.seq Com.skip)))))))))))
                  (Com.skip.seq
                    (Com.skip.seq
                      (Com.skip.seq
                        (Com.skip.seq
                          (Com.skip.seq (Com.skip.seq (Com.skip.seq (Com.skip.seq (Com.skip.seq Com.skip))))))))))))))))

/-- **The elimination loop's synthesis**, with the frame the tool
computed left existential — naming it costs a page and buys nothing,
`elimSynth` itself being the named statement. -/
theorem elimSynth' (n : ℕ) (off tgt alv : List ℕ)
    (deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ : List ℕ) (sp₀ cnt₀ mind₀ kmax₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
          arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn)
        (deg₀, elm₀, rnk₀, idg₀, bh₀, bv₀, bn₀, sp₀, cnt₀, mind₀, kmax₀)
        ("deg", "elm", "rnk", "idg", "bh", "bv", "bn", "sp", "cnt", "mind", "kmax") ∗
        hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
        hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        junkCell "bhm" ∗ junkCell "w" ∗ junkCell "bnp" ∗ junkCell "ew" ∗ junkCell "dw" ∗
        junkCell "nm" ∗ junkCell "rw" ∗ junkCell "dk" ∗ junkCell "aw" ∗ junkCell "j" ∗
        junkCell "wp" ∗ junkCell "jend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗
        junkCell "dv" ∗ junkCell "du" ∗ junkCell "bhd")
      elimSynth_impl Γ'
      ("deg", "elm", "rnk", "idg", "bh", "bv", "bn", "sp", "cnt", "mind", "kmax")
      (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
        arrayAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn)
      (elimLoop n off tgt alv
        (deg₀, elm₀, rnk₀, idg₀, bh₀, bv₀, bn₀, sp₀, cnt₀, mind₀, kmax₀)) :=
  ⟨_, elimSynth n off tgt alv deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ sp₀ cnt₀ mind₀ kmax₀⟩

/-- info: 'Lax3Proofs.Refine.ElimSynth3.elimSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms elimSynth

end Synth

/-! ## 5. What is not here (2B′ debts)

The elimination loop is **derived and synthesized**; two things about it
are not proved in this wave, and both are named so that the next one
does not have to rediscover them.

**Debt E1 — the amortized bound.** `RamElim`'s own walk pays the loop
out of the potential

    40 · (n + 1 − mind) + 40 · ls + 100 · (ns − sc) + 80 · (n − cnt),

with `ls` the number of slots the buckets hold and `sc` the number of
slots scanned. At this layer `ls` is not a state component (2B′/D-a) but
a *function* of the state — `Buck.ls_eq` reads it off the bucket arrays
as `∑ d ≤ n, |chain bn (bh d)|` — and `sc` likewise (`RamElim.scanned`).
So the potential is expressible as `Φ : ES → ACost` and
`ElimSynth2.while_pot_le` is the lemma that consumes it: what is missing
is the four case analyses (`elimBump_run`, `elimStale_run`,
`elimTake_run`, `elimTakeDead_run` in `RamElim`) transported to the list
layer, plus the row scan's own bound. Nothing about the shape of the
obligation is open.

**Debt E2 — the correctness transport.** `RamElim.Elim` is the loop
invariant and it is stated over functions `ℕ → ℕ`, so
`ElimSynth2.larr`/`larr_set` carry it to the list layer verbatim, and
`Elim.init`, `Elim.bump`, `Elim.extract` and `Elim.cert` — the whole
mathematics — are *consumed*. What is missing is the symbolic execution
of `elimTurnF` against them: the same four cases as E1. The **rank
bound** `∀ v < n, R v < n` is `Elim.rank_lt`, a clause of that same
invariant, and it is what the export must carry (the old `ElimMem`
dropped it and `RamDriverCompose.elimRank_spec` had to re-run all five
phase walks to get it back).

**Debt E3 — `BRefine`.** No bounds pass is written for either loop.
`Sepref/WordSpike.lean`'s `BRefine` has no nested-`while` rule
(`BRefine.while_guard` takes a body, not a body containing a loop), so
the elimination loop and the fill pass both need one before their word
bounds can be discharged; the three flat passes (`buckSynth`,
`offSynth`, and 2B's `degScanSynth`) are each a `BRefine.while_guard`
away, at the ≈ 50 lines per loop `AugmentSynth` §2.1 and §4b measure.
This is a *tool* gap, not a proof gap.

**What is not a debt.** The re-zeroing defect class that chartered this
satellite is dead at the *layer*, as `ElimSynth`'s header argues: the
programs above are functions of `n`, `ns`, `W`, `off`, `tgt`, `alv` and
their scratch, every scratch array enters its loop as a value the caller
supplies and no clause of any precondition here says what any scratch
array *contains* — only how long it is. `RamDriver.elimRezeroCom` has
nothing to re-zero at this layer and the `n = 1` counterexample is not
expressible. That argument does not depend on the loop having been
synthesized, and the loop has now been synthesized anyway. -/

end Lax3Proofs.Refine.ElimSynth3
