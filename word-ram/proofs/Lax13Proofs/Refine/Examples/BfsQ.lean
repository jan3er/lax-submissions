import Lax13Proofs.Refine.Examples.Bfs
import Lax13Proofs.Refine.NREST.Automation
import Lax13Proofs.Refine.Sepref.IrLoop
import Lax13Proofs.Refine.Sepref.Definition

/-!
# P7 wave A — the queue-based masked depth-capped search

The gate program, at the IR's own operations and combinators
(`Sepref/IrOps.lean`), with its correctness and its **linear** cost
bound proved at the `NRest` layer:

```
bfsQ n d src off tgt alv dist₀ q₀
  ≤ SPEC (dist decides masked distance at every threshold ≤ d)
         (n • fill + n • pop + ns • scan + K)
```

All data is first-order — `dist`, the queue and the CSR arrays are
`List ℕ`, the indices are `ℕ` — which is the shape wave B synthesizes.
The graph appears only in the *specification* and in the proof: the
program never mentions it.

## Judgment calls (P7/D-a …)

**P7/D-a — the direct queue invariant, not a data refinement off
`bfsAlg`.** P1's abstract BFS is level-synchronous: one iteration per
level, with the frontier as a list. The queue program's drain loop pops
*one* vertex per iteration, so an abstract iteration is a whole run of
concrete ones and the refinement would be a nested-loop simulation. The
direct route re-proves the frontier invariant in queue form (`Fr`, §4)
and is the cheaper of the two. What is reused from `Bfs.lean` is the
*graph theory*, which is where the mathematics is: `masked`, `WD` and
its five decomposition lemmas, plus the two `wfR2` gap lemmas — see the
telemetry.

**P7/D-b — three loops, three fuel inductions; the VCG's loop rule is
available but not consumed.** The three loops all have a state-bounded
iteration count (`n - i`, `kend - k`, `n - head`), so each is bounded by
an induction on that measure — and the same induction delivers the
`LOOP_VARIANT` annotation wave B needs (§7), which a `While`
application does not. The general bridge from the translator's
`irWhileIT` to the VCG's `whileIET` is proved anyway
(`Sepref/IrLoop.lean`, P7/T-a): it is a real gap in the tower, found
here, and it is what a loop *without* a state-bounded measure would need.

**P7/D-c — the relaxation test is `dist[u] = d + 1`, and `qcap` is its
price.** `RamBfs`'s test is `dist[v] + 1 < dist[u]`, which makes the
`exp` clause free and the "not already queued" step need `qcap`. Ours
makes "not already queued" free (a queued vertex reads `≤ d`) and `exp`
need `qcap`. Both invariants carry `qmono`/`qcap`; the choice is the
brief's, and it is the one a cap-`d` implementation actually writes.

**P7/D-d — `room` replaces the counting argument inside the program.**
The queue write `q[tail] := u` must be in range. `RamBfs` gets that from
a `Finset` cardinality argument over the queue's injectivity, which
mentions the graph. The clause `tail + |undiscovered live| ≤ n` says the
same thing at the *list* level, so the program's own assertion
(`popP`, `scanP`) stays graph-free — which is what lets `bfsQ` be a
program over lists and its variants be provable from its own
assertions.

**P7/D-e — every loop's assertion is guarded by that loop's
condition.** `irWhileIT` asserts before testing the guard, so an
assertion that can fail at the exit state makes the program strictly
larger than the `whileIET` the VCG knows (P7/T-a). Writing every `I` as
`bf s = true → P s` is the discipline that closes the gap, and it costs
nothing: the body is the only consumer.

**P7/D-f — the branches of the row scan are balanced with `pack3`.**
Both arms of both conditionals deliver the same triple through the same
tuple operation (P4/D-ee's rule for in-place merges), so the three paths
differ only by the two `aset`s and the one `add` the relaxing path
spends, and `scanC` is the maximum. The projection that drops the scan
index at the end of the row (`pack3 r.1 r.2.1 r.2.2.1`) is free here;
wave B junks the cell, as `rvLoop_array` does (P4/D-ec).

**Fa/D-x — the target array's physical width is a number of its own
(ND-MC rebase wave F-a, 2026-07-30).** `Csr` used to carry
`tlen : tgt.length = ns` beside `last : off[n]! = ns`, pinning the
array's length at the slot count. Nothing in the search wants that: the
scan of row `v` runs over `off[v] … off[v+1] − 1`, and `Csr.row_le_ns`
bounds that by `off[n]! = ns`, so no read of the program ever reaches a
slot at or above `ns`. The pin was inherited from `RamBfs.CsrGraph`,
where the array is *built* at exactly its slot count; the ND-MC cover
pass materializes it at a caller-chosen width `W ≥ ns` and so could not
present the relation at all (finding F-a of rebase wave B5 — the same
severing the consumer package did for the reasoning kit's relation in
`Lax3Proofs/CsrWide.lean`, at the same rationale).

The field is therefore weakened to `tlen : ns ≤ tgt.length`, which
`shape` and `last` already imply — it is kept as a field so that the
relation still reads its width discipline off its own statement, and so
that the four-field anonymous constructor every caller writes keeps its
arity. Consequences, in full:

* Every export over `Csr` — `bfsQ_correct`, `drainLoop_le'`,
  `BfsQSynth.bfsQS_correct`, `bfsQ_spec_at`, `bfsQ_spec`,
  `bfsQS_reached`, and `BfsQTrail`'s `drainLoop_touched`,
  `searchQ_touched`, `turnQ_touched`, `turnQ_bounded`, `turnsQ_touched`
  — is **statement-identical** and strictly more general: `Csr` is a
  hypothesis of each, and it got weaker. No primed form is needed, and
  the pinned callers reach the relation through `Csr.of_tlen_eq` (or
  through the four-field constructor, unchanged).
* Three internal bounds helpers change statement, because they were the
  only places the old field was consumed: `BfsQSynth.off_mem_le` now
  reads offsets against `off[n]!` rather than `tgt.length` (strictly
  stronger, and width-free), and `bfsQ_stateBound` / `bfsQ_bpre` take
  `off[n]! ≤ ns` where they took `tgt.length ≤ ns`. All three are
  `Shape`-level lemmas with no consumer outside `BfsQSynth.lean`.
* `Csr.widen` is the constructive half: the relation survives appending
  any padding whose entries are vertices.

**What the widening does *not* cover.** `Shape`'s range clause is still
`∀ j < tgt.length, tgt[j]! < n` — over the *whole* array, not the
occupied prefix — because it is consumed at full width by
`bfsQ_stateBound` (the machine's `Ir.StateBound` is state-global: every
entry of every array in the store must be a word) and by four ND-MC
passes over the same relation (`ElimSynth`'s degree pass, `ElimSynth6`'s
fill, `ExpandSynth`, `BlockLeaves`). So a widened caller must pad with
in-range values — `Csr.widen` is stated at exactly that. That is no
extra burden at the machine layer — the store bound demands `< B` of
the padding anyway — but it is a real difference from `CsrWide`'s
`∀ p < ns, tgt p < V`, and it is the residual of finding F-a.
-/

namespace Lax13Proofs.Refine

namespace BfsQ

open Bfs Sepref Ir NRest

/-! ## 1. Refute before prove

The abstract program's three loops are `noncomputable`; their *steps*
are not, and §3 proves each abstract body equal to the step function
below. So the runs checked here are runs of `bfsQ`. -/

/-- The state of both inner loops: distances, queue, a queue index, a
scan index. -/
abbrev St : Type := List ℕ × List ℕ × ℕ × ℕ

/-- One slot of a row scan: read the target, and if it is alive and
undiscovered give it the offered distance and put it on the queue. -/
def scanStep (tgt alv : List ℕ) (sent dv1 : ℕ) : St → St
  | (D, Q, tl, k) =>
    if 0 < alv[tgt[k]!]! then
      if D[tgt[k]!]! = sent then (D.set tgt[k]! dv1, Q.set tl tgt[k]!, tl + 1, k + 1)
      else (D, Q, tl, k + 1)
    else (D, Q, tl, k + 1)

/-- The row scan, run to the end of the row. -/
def scanTw (tgt alv : List ℕ) (sent dv1 kend : ℕ) : ℕ → St → St
  | 0, s => s
  | fuel + 1, s =>
    if s.2.2.2 < kend then scanTw tgt alv sent dv1 kend fuel (scanStep tgt alv sent dv1 s) else s

/-- One pop: expand the head of the queue, unless the cap stops it. -/
def popStep (off tgt alv : List ℕ) (d : ℕ) : St → St
  | (D, Q, hd, tl) =>
    if D[Q[hd]!]! < d then
      let r := scanTw tgt alv (d + 1) (D[Q[hd]!]! + 1) off[Q[hd]! + 1]!
        (off[Q[hd]! + 1]! - off[Q[hd]!]!) (D, Q, tl, off[Q[hd]!]!)
      (r.1, r.2.1, hd + 1, r.2.2.1)
    else (D, Q, hd + 1, tl)

/-- The drain, run until the queue is empty. -/
def drainTw (off tgt alv : List ℕ) (d : ℕ) : ℕ → St → St
  | 0, s => s
  | fuel + 1, s =>
    if s.2.2.1 < s.2.2.2 then drainTw off tgt alv d fuel (popStep off tgt alv d s) else s

/-- The whole search: fill, seed, drain, read the distances off. -/
def bfsTw (n d src : ℕ) (off tgt alv : List ℕ) : List ℕ :=
  (drainTw off tgt alv d n
    (((List.replicate n (d + 1)).set src 0), (List.replicate n 0).set 0 src, 0,
      if 0 < alv[src]! then 1 else 0)).1

/-! ### The baseline's arena

`RamBfs`'s own demo: the path `0—1—2—3` with an isolated vertex `4`,
six adjacency slots, the mask of vertex `2` left open. -/

def demoOff : List ℕ := [0, 1, 3, 5, 6, 6]
def demoTgt : List ℕ := [1, 0, 2, 1, 3, 2]
def demoAlv (a2 : ℕ) : List ℕ := [1, 1, a2, 1, 1]

-- the baseline's four `#guard`s, its own numbers (`RamBfs.lean` §Demo)
#guard bfsTw 5 3 0 demoOff demoTgt (demoAlv 1) = [0, 1, 2, 3, 4]
#guard bfsTw 5 3 0 demoOff demoTgt (demoAlv 0) = [0, 1, 4, 4, 4]
#guard bfsTw 5 1 0 demoOff demoTgt (demoAlv 1) = [0, 1, 2, 2, 2]
#guard bfsTw 5 0 0 demoOff demoTgt (demoAlv 1) = [0, 1, 1, 1, 1]

-- …and against P1's own twin of the *level-based* abstract program,
-- which shares no code with this one
#guard bfsTw 5 4 0 demoOff demoTgt (demoAlv 1) = List.ofFn (Sanity.bfsRun Sanity.pathG Sanity.fullM 0 4)
#guard bfsTw 5 4 0 demoOff demoTgt (demoAlv 0) = List.ofFn (Sanity.bfsRun Sanity.pathG Sanity.cutM 0 4)
#guard bfsTw 5 4 2 demoOff demoTgt (demoAlv 1) = List.ofFn (Sanity.bfsRun Sanity.pathG Sanity.fullM 2 4)
#guard bfsTw 5 1 0 demoOff demoTgt (demoAlv 1) = List.ofFn (Sanity.bfsRun Sanity.pathG Sanity.fullM 0 1)

-- **Negative control.** A wrong reading fails, and says so.
/--
error: Expression
  decide (bfsTw 5 3 0 demoOff demoTgt (demoAlv 0) = [0, 1, 2, 3, 4])
did not evaluate to `true`
-/
#guard_msgs in
#guard bfsTw 5 3 0 demoOff demoTgt (demoAlv 0) = [0, 1, 2, 3, 4]

/-! ## 2. The program

Every operation is a `mop` of `Sepref/IrOps.lean`, every branch an
`irIf`, every loop an `irWhileIT` — the shape `sepref_synth` translates,
at the IR's own currencies (P7/D-a).

The three loops assert what their operations need, and nothing else
(P4/D-ed). Each assertion is *guarded by the loop's own condition*,
which is what `irWhileIT_eq_whileIET` asks for and what makes the
assertion vacuous at the exit state. `Shape` collects the static facts
about the arrays; the rest is state.

`room` is the clause that makes the queue write in range without a
counting argument inside the program: the queue and the still
undiscovered live vertices together fit in `n`, so as long as one
undiscovered live vertex is left there is a slot for it. -/

/-- The still-undiscovered live vertices. -/
def undisc (n sent : ℕ) (alv D : List ℕ) : Finset ℕ :=
  (Finset.range n).filter fun w => 0 < alv[w]! ∧ D[w]! = sent

/-- **Room for one more**: the queue plus what may still join it fits. -/
def room (n sent : ℕ) (alv D : List ℕ) (tl : ℕ) : Prop :=
  tl + (undisc n sent alv D).card ≤ n

/-- The static facts about the block structure that keep every read in
range. -/
def Shape (n : ℕ) (off tgt alv : List ℕ) : Prop :=
  off.length = n + 1 ∧ alv.length = n ∧ (∀ i < n, off[i]! ≤ off[i + 1]!) ∧
    off[n]! ≤ tgt.length ∧ ∀ j < tgt.length, tgt[j]! < n

/-- Assemble a four-component state, at the IR's tuple operation. -/
noncomputable def pack4 (D Q : List ℕ) (a b : ℕ) : NRest St ECost :=
  bindT (mopPair a b) fun p => bindT (mopPair Q p) fun p' => mopPair D p'

/-- …and a three-component one, the shape each branch of a scan
delivers (P4/D-ee: the branches write the same destinations). -/
noncomputable def pack3 (D Q : List ℕ) (a : ℕ) : NRest (List ℕ × List ℕ × ℕ) ECost :=
  bindT (mopPair Q a) fun p => mopPair D p

/-- Binding a four-component state is charging its three tuple steps
(P7/D-bi). `hnr_while_var` reads a loop's state off a *single* `hnCtxt`
conjunct, so a loop entered in the middle of a block has to have its
state built — the row scan is, and `popF` below builds it. -/
theorem pack4_bindT {β : Type} (D Q : List ℕ) (a b : ℕ) (f : St → NRest β ECost) :
    bindT (pack4 D Q a b) f
      = NRest.consume (f (D, Q, a, b))
          (irUnit Currency.skip + (irUnit Currency.skip + irUnit Currency.skip)) := by
  simp only [pack4, mopPair_def, bindT_unitT, NRest.consume_consume]

/-! ### The fill -/

def fillBf (n : ℕ) : List ℕ × ℕ → Bool := fun s => decide (s.2 < n)

def fillP (n : ℕ) : List ℕ × ℕ → Prop := fun s => s.1.length = n

noncomputable def fillF (sent : ℕ) : List ℕ × ℕ → NRest (List ℕ × ℕ) ECost := fun s =>
  bindT (mopAset s.1 s.2 sent) fun D => bindT (mopBinop .add s.2 1) fun i => mopPair D i

noncomputable def fillLoop (n sent : ℕ) (s₀ : List ℕ × ℕ) : NRest (List ℕ × ℕ) ECost :=
  irWhileIT (fun s => fillBf n s = true → fillP n s) (fillBf n) (fillF sent) s₀

/-! ### The row scan -/

def scanBf (kend : ℕ) : St → Bool := fun s => decide (s.2.2.2 < kend)

def scanP (n sent kend : ℕ) (off tgt alv : List ℕ) : St → Prop := fun s =>
  Shape n off tgt alv ∧ s.1.length = n ∧ s.2.1.length = n ∧ kend ≤ tgt.length ∧
    room n sent alv s.1 s.2.2.1

noncomputable def scanF (sent dv1 : ℕ) (tgt alv : List ℕ) : St → NRest St ECost := fun s =>
  bindT (mopAget tgt s.2.2.2) fun u =>
    bindT (mopAget alv u) fun au =>
      bindT (mopAget s.1 u) fun du =>
        bindT (irIf (decide (0 < au))
            (irIf (decide (du = sent))
              (bindT (mopAset s.1 u dv1) fun D =>
                bindT (mopAset s.2.1 s.2.2.1 u) fun Q =>
                  bindT (mopBinop .add s.2.2.1 1) fun t => pack3 D Q t)
              (pack3 s.1 s.2.1 s.2.2.1))
            (pack3 s.1 s.2.1 s.2.2.1)) fun r =>
          bindT (mopBinop .add s.2.2.2 1) fun k => pack4 r.1 r.2.1 r.2.2 k

noncomputable def scanLoop (n sent dv1 kend : ℕ) (off tgt alv : List ℕ) (s₀ : St) :
    NRest St ECost :=
  irWhileIT (fun s => scanBf kend s = true → scanP n sent kend off tgt alv s) (scanBf kend)
    (scanF sent dv1 tgt alv) s₀

/-! ### The drain -/

def popBf : St → Bool := fun s => decide (s.2.2.1 < s.2.2.2)

def popP (n sent : ℕ) (off tgt alv : List ℕ) : St → Prop := fun s =>
  Shape n off tgt alv ∧ s.1.length = n ∧ s.2.1.length = n ∧
    (∀ i < s.2.2.2, s.2.1[i]! < n) ∧ room n sent alv s.1 s.2.2.2

noncomputable def popF (n d sent : ℕ) (off tgt alv : List ℕ) : St → NRest St ECost := fun s =>
  bindT (mopAget s.2.1 s.2.2.1) fun v =>
    bindT (mopAget s.1 v) fun dv =>
      bindT (mopBinop .add s.2.2.1 1) fun hd =>
        bindT (irIf (decide (dv < d))
            (bindT (mopBinop .add dv 1) fun dv1 =>
              bindT (mopAget off v) fun k0 =>
                bindT (mopBinop .add v 1) fun v1 =>
                  bindT (mopAget off v1) fun kend =>
                    bindT (pack4 s.1 s.2.1 s.2.2.2 k0) fun z0 =>
                      bindT (scanLoop n sent dv1 kend off tgt alv z0)
                        fun r => pack3 r.1 r.2.1 r.2.2.1)
            (pack3 s.1 s.2.1 s.2.2.2)) fun r =>
          pack4 r.1 r.2.1 hd r.2.2

noncomputable def drainLoop (n d sent : ℕ) (off tgt alv : List ℕ) (s₀ : St) : NRest St ECost :=
  irWhileIT (fun s => popBf s = true → popP n sent off tgt alv s) popBf
    (popF n d sent off tgt alv) s₀

/-! ### The whole search -/

/-- **The program.** `dist₀` and `q₀` are the caller's two scratch
arrays, of length `n`; the result is the distance array. -/
noncomputable def bfsQ (n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) : NRest (List ℕ) ECost :=
  bindT (mopBinop .add d 1) fun sent =>
    bindT (mopConstN 0) fun z =>
      bindT (fillLoop n sent (dist₀, z)) fun p =>
        bindT (mopAset p.1 src 0) fun D =>
          bindT (mopAset q₀ 0 src) fun Q =>
            bindT (mopAget alv src) fun a =>
              bindT (irIf (decide (0 < a)) (mopConstN 1) (mopConstN 0)) fun tl =>
                bindT (pack4 D Q z tl) fun st =>
                  bindT (drainLoop n d sent off tgt alv st) fun st' => returnT st'.1

/-! ## 3. What each body costs, and what each counted loop does

Every body is bounded *above* by "return the step, pay the price": an
inequality is all a `≤ SPEC` proof ever needs, and it is what lets the
three branches of a row scan share one price. -/

/-- One unit of one currency, at `ℕ`. -/
def cu (c : String) : ACost String ℕ := ACost.cost c 1

@[simp] theorem liftACost_cu (c : String) : liftACost (cu c) = irUnit c := by
  rw [cu, liftACost_cost]; norm_num

/-- One fill iteration. -/
def fillC : ACost String ℕ := cu Currency.aset + cu Currency.add + cu Currency.skip

/-- What every slot of a row scan pays. -/
def scanC0 : ACost String ℕ := cu Currency.aget + cu Currency.aget + cu Currency.aget
  + cu Currency.ite + cu Currency.ite + cu Currency.skip + cu Currency.skip
  + cu Currency.add + cu Currency.skip + cu Currency.skip + cu Currency.skip

/-- …and what the slot that relaxes pays on top. -/
def scanC : ACost String ℕ := scanC0 + (cu Currency.aset + cu Currency.aset + cu Currency.add)

/-- One pop, everything outside the row: the two reads, the head bump,
the cap test, the row bounds, the tuple, and the row loop's entry
test. -/
def popC : ACost String ℕ := cu Currency.aget + cu Currency.aget + cu Currency.add
  + cu Currency.ite + cu Currency.add + cu Currency.aget + cu Currency.add + cu Currency.aget
  + cu Currency.«while» + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip

/-- An iteration is a body plus the guard test that let it run. -/
def iter (C : ACost String ℕ) : ACost String ℕ := C + cu Currency.«while»

/-- The length of a row. -/
def rowLen (off : List ℕ) (v : ℕ) : ℕ := off[v + 1]! - off[v]!

theorem fillF_le (sent : ℕ) (s : List ℕ × ℕ) (h : s.2 < s.1.length) :
    fillF sent s ≤ NRest.consume (NRest.returnT (s.1.set s.2 sent, s.2 + 1)) (liftACost fillC) := by
  refine le_of_eq ?_
  simp only [fillF, mopAset_def, mopBinop_def, mopPair_def, NRest.assert_pos h,
    NRest.returnT_bindT, bindT_unitT, NRest.consume_consume, Imp.Bop.apply_add,
    binopCurrency_add, fillC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

theorem scanF_le (sent dv1 : ℕ) (tgt alv : List ℕ) (s : St)
    (h1 : s.2.2.2 < tgt.length) (h2 : tgt[s.2.2.2]! < alv.length)
    (h3 : tgt[s.2.2.2]! < s.1.length)
    (h4 : 0 < alv[tgt[s.2.2.2]!]! → s.1[tgt[s.2.2.2]!]! = sent → s.2.2.1 < s.2.1.length) :
    scanF sent dv1 tgt alv s
      ≤ NRest.consume (NRest.returnT (scanStep tgt alv sent dv1 s)) (liftACost scanC) := by
  have base : liftACost scanC0 ≤ liftACost scanC := by
    rw [scanC, liftACost_add]; exact cost_le_add _ _
  by_cases hb1 : 0 < alv[tgt[s.2.2.2]!]!
  · by_cases hb2 : s.1[tgt[s.2.2.2]!]! = sent
    · have h5 : s.2.2.1 < s.2.1.length := h4 hb1 hb2
      refine le_of_eq ?_
      simp only [scanF, scanStep, mopAget_def, mopAset_def, mopBinop_def, mopPair_def, pack3,
        pack4, irIf_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h3,
        NRest.assert_pos h5, NRest.returnT_bindT,
        NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
        Imp.Bop.apply_add, binopCurrency_add, decide_eq_true_eq, if_pos hb1, if_pos hb2,
        scanC, scanC0, liftACost_add, liftACost_cu]
      congr 1
      ac_rfl
    · simp only [scanF, scanStep, mopAget_def, mopBinop_def, mopPair_def, pack3, pack4, irIf_def,
        NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h3, NRest.returnT_bindT,
        NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
        Imp.Bop.apply_add, binopCurrency_add, decide_eq_true_eq, if_pos hb1, if_neg hb2]
      refine NRest.consume_mono le_rfl (le_trans (le_of_eq ?_) base)
      simp only [scanC0, liftACost_add, liftACost_cu]
      ac_rfl
  · simp only [scanF, scanStep, mopAget_def, mopBinop_def, mopPair_def, pack3, pack4, irIf_def,
      NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h3, NRest.returnT_bindT,
      NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
      Imp.Bop.apply_add, binopCurrency_add, decide_eq_true_eq, if_neg hb1]
    refine NRest.consume_mono le_rfl (le_trans (cost_le_add _ (irUnit Currency.ite))
      (le_trans (le_of_eq ?_) base))
    simp only [scanC0, liftACost_add, liftACost_cu]
    ac_rfl

/-! ### The two counted loops, run to the end

Both are bounded by a specification of their result together with the
number of iterations they can still make. The induction is on a fuel the
guard's own measure bounds — the same measure the synthesis needs as a
variant (§6). -/

/-- Reading a written array. -/
theorem get!_set (xs : List ℕ) (i v j : ℕ) (hi : i < xs.length) :
    (xs.set i v)[j]! = if j = i then v else xs[j]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = i
  · subst h; simp [hi]
  · simp [h, Ne.symm h]

/-- The exit of an `irWhileIT` at a guarded invariant: no assertion can
stand in the way. -/
theorem irWhile_exit {σ : Type} {P : σ → Prop} {bf : σ → Bool} {f : σ → NRest σ ECost} {s : σ}
    (hb : bf s = false) :
    irWhileIT (fun y => bf y = true → P y) bf f s
      = NRest.consume (NRest.returnT s) (irUnit Currency.«while») :=
  irWhileIT_of_false (fun h => absurd h (by rw [hb]; simp)) hb

theorem fillLoop_le (n sent : ℕ) : ∀ (fuel : ℕ) (D : List ℕ) (i : ℕ), D.length = n → n - i ≤ fuel →
    (∀ j, j < i → D[j]! = sent) →
    fillLoop n sent (D, i)
      ≤ NRest.spec (fun p : List ℕ × ℕ => p.1.length = n ∧ ∀ j, j < n → p.1[j]! = sent)
          (fun _ => liftACost ((n - i) • iter fillC + cu Currency.«while»)) := by
  have exit : ∀ (D : List ℕ) (i : ℕ), D.length = n → n ≤ i → (∀ j, j < i → D[j]! = sent) →
      fillLoop n sent (D, i)
        ≤ NRest.spec (fun p : List ℕ × ℕ => p.1.length = n ∧ ∀ j, j < n → p.1[j]! = sent)
            (fun _ => liftACost ((n - i) • iter fillC + cu Currency.«while»)) := by
    intro D i hlen hf hj
    have hb : fillBf n (D, i) = false := by simp only [fillBf, decide_eq_false_iff_not]; omega
    simp only [fillLoop, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨hlen, fun j hjn => hj j (by omega)⟩ ?_
    rw [show n - i = 0 by omega]
    simp
  intro fuel
  induction fuel with
  | zero => intro D i hlen hf hj; exact exit D i hlen (by omega) hj
  | succ fuel ih =>
    intro D i hlen hf hj
    by_cases hb : i < n
    · have hbt : fillBf n (D, i) = true := by simp [fillBf, hb]
      have hIs : fillBf n ((D, i) : List ℕ × ℕ) = true → fillP n (D, i) := fun _ => hlen
      have hih := ih (D.set i sent) (i + 1) (by simp [hlen]) (by omega) (fun j hjl => by
        rw [get!_set D i sent j (by omega)]
        by_cases hji : j = i
        · rw [if_pos hji]
        · rw [if_neg hji]; exact hj j (by omega))
      have hcost : irUnit Currency.«while»
          + (liftACost fillC + liftACost ((n - (i + 1)) • iter fillC + cu Currency.«while»))
          = liftACost ((n - i) • iter fillC + cu Currency.«while») := by
        rw [show n - i = (n - (i + 1)) + 1 by omega, succ_nsmul]
        simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
        ac_rfl
      calc fillLoop n sent (D, i)
          = NRest.consume (NRest.bindT (fillF sent (D, i)) fun s' => fillLoop n sent s')
              (irUnit Currency.«while») := by
            simp only [fillLoop]; rw [irWhileIT_of_true hIs hbt]
        _ ≤ NRest.consume (NRest.bindT
              (NRest.consume (NRest.returnT (D.set i sent, i + 1)) (liftACost fillC))
              fun s' => fillLoop n sent s') (irUnit Currency.«while») :=
            NRest.consume_mono
              (NRest.bindT_mono (fillF_le sent (D, i) (by simpa [hlen] using hb)) fun _ => le_rfl)
              le_rfl
        _ = NRest.consume (NRest.consume (fillLoop n sent (D.set i sent, i + 1)) (liftACost fillC))
              (irUnit Currency.«while») := by rw [bindT_unitT]
        _ ≤ _ := by
            rw [← hcost]
            exact NRest.consume_mono (NRest.consume_mono hih le_rfl) le_rfl |>.trans
              (le_of_eq (by rw [consume_spec, consume_spec]))
    · exact exit D i hlen (by omega) hj

theorem scanP_bounds {n sent kend : ℕ} {off tgt alv : List ℕ} {s : St}
    (hP : scanP n sent kend off tgt alv s) (hb : scanBf kend s = true) :
    s.2.2.2 < tgt.length ∧ tgt[s.2.2.2]! < alv.length ∧ tgt[s.2.2.2]! < s.1.length ∧
      (0 < alv[tgt[s.2.2.2]!]! → s.1[tgt[s.2.2.2]!]! = sent → s.2.2.1 < s.2.1.length) := by
  obtain ⟨⟨-, halen, -, -, htlt⟩, hD, hQ, hkt, hroom⟩ := hP
  have hk : s.2.2.2 < tgt.length := lt_of_lt_of_le (by simpa [scanBf] using hb) hkt
  have hu : tgt[s.2.2.2]! < n := htlt _ hk
  refine ⟨hk, by omega, by omega, fun ha hd => ?_⟩
  have hmem : tgt[s.2.2.2]! ∈ undisc n sent alv s.1 := by
    simp only [undisc, Finset.mem_filter, Finset.mem_range]
    exact ⟨hu, ha, hd⟩
  have hpos : 0 < (undisc n sent alv s.1).card := Finset.card_pos.mpr ⟨_, hmem⟩
  rw [hQ]
  simp only [room] at hroom
  omega

theorem scanLoop_le {Inv : St → Prop} (n sent dv1 kend : ℕ) (off tgt alv : List ℕ)
    (hs : ∀ t : St, Inv t → scanBf kend t = true →
      scanP n sent kend off tgt alv t ∧ Inv (scanStep tgt alv sent dv1 t)) :
    ∀ (fuel : ℕ) (s : St), Inv s → kend - s.2.2.2 ≤ fuel →
      scanLoop n sent dv1 kend off tgt alv s
        ≤ NRest.spec (fun t : St => Inv t ∧ kend ≤ t.2.2.2)
            (fun _ => liftACost ((kend - s.2.2.2) • iter scanC + cu Currency.«while»)) := by
  have exit : ∀ s : St, Inv s → kend ≤ s.2.2.2 →
      scanLoop n sent dv1 kend off tgt alv s
        ≤ NRest.spec (fun t : St => Inv t ∧ kend ≤ t.2.2.2)
            (fun _ => liftACost ((kend - s.2.2.2) • iter scanC + cu Currency.«while»)) := by
    intro s hI hk
    have hb : scanBf kend s = false := by simp only [scanBf, decide_eq_false_iff_not]; omega
    simp only [scanLoop, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨hI, hk⟩ ?_
    rw [show kend - s.2.2.2 = 0 by omega]
    simp
  intro fuel
  induction fuel with
  | zero => intro s hI hf; exact exit s hI (by omega)
  | succ fuel ih =>
    intro s hI hf
    by_cases hb : s.2.2.2 < kend
    · have hbt : scanBf kend s = true := by simp [scanBf, hb]
      obtain ⟨hPs, hInv'⟩ := hs s hI hbt
      obtain ⟨h1, h2, h3, h4⟩ := scanP_bounds hPs hbt
      have hIs : scanBf kend s = true → scanP n sent kend off tgt alv s := fun _ => hPs
      have hk' : (scanStep tgt alv sent dv1 s).2.2.2 = s.2.2.2 + 1 := by
        simp only [scanStep]; split_ifs <;> rfl
      have hih := ih (scanStep tgt alv sent dv1 s) hInv' (by rw [hk']; omega)
      rw [hk'] at hih
      have hcost : irUnit Currency.«while»
          + (liftACost scanC + liftACost ((kend - (s.2.2.2 + 1)) • iter scanC + cu Currency.«while»))
          = liftACost ((kend - s.2.2.2) • iter scanC + cu Currency.«while») := by
        rw [show kend - s.2.2.2 = (kend - (s.2.2.2 + 1)) + 1 by omega, succ_nsmul]
        simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
        ac_rfl
      calc scanLoop n sent dv1 kend off tgt alv s
          = NRest.consume (NRest.bindT (scanF sent dv1 tgt alv s)
              fun s' => scanLoop n sent dv1 kend off tgt alv s') (irUnit Currency.«while») := by
            simp only [scanLoop]; rw [irWhileIT_of_true hIs hbt]
        _ ≤ NRest.consume (NRest.bindT
              (NRest.consume (NRest.returnT (scanStep tgt alv sent dv1 s)) (liftACost scanC))
              fun s' => scanLoop n sent dv1 kend off tgt alv s') (irUnit Currency.«while») :=
            NRest.consume_mono
              (NRest.bindT_mono (scanF_le sent dv1 tgt alv s h1 h2 h3 h4) fun _ => le_rfl) le_rfl
        _ = NRest.consume (NRest.consume
              (scanLoop n sent dv1 kend off tgt alv (scanStep tgt alv sent dv1 s))
              (liftACost scanC)) (irUnit Currency.«while») := by rw [bindT_unitT]
        _ ≤ _ := by
            rw [← hcost]
            exact NRest.consume_mono (NRest.consume_mono hih le_rfl) le_rfl |>.trans
              (le_of_eq (by rw [consume_spec, consume_spec]))
    · exact exit s hI (by omega)

/-! ## 4. The queue invariant

P1's `Refine/Examples/Bfs.lean` supplies the graph theory whole —
`masked`, `WD` and its five decomposition lemmas — so what is left here
is the *queue* discipline, which the level-based program of P1 does not
have. Every clause below is here because a step asks for it; `qmono`
and `qcap` are the two a textbook leaves implicit, and they are what
makes the relaxation test `dist[u] = d + 1` sound (`RamBfs.lean` states
the same two, for the same reason). -/

/-- The mask the program reads out of `alv`. -/
def maskOf (n : ℕ) (alv : List ℕ) : Fin n → Bool := fun v => decide (0 < alv[(v : ℕ)]!)

@[simp] theorem maskOf_iff {n : ℕ} {alv : List ℕ} {v : Fin n} :
    maskOf n alv v = true ↔ 0 < alv[(v : ℕ)]! := by simp [maskOf]

/-- The block structure, as a view of the graph: `RamBfs`'s `CsrGraph`
with the arrays spelled as lists (design note P7/S-1 — nothing is
imported from that package).

`ns` is the **slot count** — the last offset — and `tgt.length` is the
array's **physical width**; the two are separate numbers (Fa/D-x), with
`tlen` the only thing that relates them. -/
structure Csr (n ns : ℕ) (G : SimpleGraph (Fin n)) (off tgt alv : List ℕ) : Prop where
  shape : Shape n off tgt alv
  /-- The slot count is a *lower bound* of the physical width: the
  target array may be materialized wider than the structure occupies
  (Fa/D-x). Redundant given `shape` and `last`, and kept as a field so
  that the relation still reads off its own statement. -/
  tlen : ns ≤ tgt.length
  last : off[n]! = ns
  adj : ∀ u v : Fin n, G.Adj u v ↔
    ∃ j, off[(u : ℕ)]! ≤ j ∧ j < off[(u : ℕ) + 1]! ∧ tgt[j]! = (v : ℕ)

/-- The offsets do not decrease, all the way up. -/
theorem Shape.mono' {n : ℕ} {off tgt alv : List ℕ} (h : Shape n off tgt alv) :
    ∀ {i k}, i ≤ k → k ≤ n → off[i]! ≤ off[k]! := by
  intro i k hik hk
  induction k with
  | zero => rw [show i = 0 by omega]
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with hlt | hge
    · exact le_trans (ih (by omega) (by omega)) (h.2.2.1 k (by omega))
    · rw [show i = k + 1 by omega]

/-- A row ends inside the target array. -/
theorem Shape.row_le {n : ℕ} {off tgt alv : List ℕ} (h : Shape n off tgt alv) {v : ℕ}
    (hv : v < n) : off[v + 1]! ≤ tgt.length := le_trans (h.mono' hv le_rfl) h.2.2.2.1

theorem Csr.mono' {n ns : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}
    (h : Csr n ns G off tgt alv) : ∀ {i k}, i ≤ k → k ≤ n → off[i]! ≤ off[k]! :=
  h.shape.mono'

/-! ### The width reading (Fa/D-x)

`ns` counts the slots the structure occupies; `tgt.length` is the
array the caller materialized. The search reads only slots below
`off[n]! = ns`, so every read the pinned relation justified the
decoupled one justifies too — `row_le_ns` is the whole of that
argument, `of_tlen_eq` is the pinned relation as an instance, and
`widen` is the caller's side of it. -/

/-- Reading below a list's own length does not see what was appended
after it. -/
theorem getElem!_append_left {l₁ l₂ : List ℕ} {j : ℕ} (hj : j < l₁.length) :
    (l₁ ++ l₂)[j]! = l₁[j]! := by
  rw [getElem!_pos (l₁ ++ l₂) j (by simp only [List.length_append]; omega),
    getElem!_pos l₁ j hj, List.getElem_append_left hj]

namespace Csr

variable {n ns : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}

/-- **The pinned relation is the equal-width instance.** A caller who
still holds the old coupling gets the relation by one `le_of_eq`. -/
theorem of_tlen_eq (hs : Shape n off tgt alv) (ht : tgt.length = ns) (hl : off[n]! = ns)
    (ha : ∀ u v : Fin n, G.Adj u v ↔
      ∃ j, off[(u : ℕ)]! ≤ j ∧ j < off[(u : ℕ) + 1]! ∧ tgt[j]! = (v : ℕ)) :
    Csr n ns G off tgt alv :=
  ⟨hs, le_of_eq ht.symm, hl, ha⟩

/-- Every offset sits inside the occupied prefix. -/
theorem le_ns (hc : Csr n ns G off tgt alv) {i : ℕ} (hi : i ≤ n) : off[i]! ≤ ns :=
  hc.last ▸ hc.mono' hi le_rfl

/-- **A row ends inside the occupied prefix** — not merely inside the
array. This is the clause the widening turns on: the scan of any row
stays below `ns`, whatever the physical width is. -/
theorem row_le_ns (hc : Csr n ns G off tgt alv) (v : Fin n) : off[(v : ℕ) + 1]! ≤ ns :=
  hc.le_ns v.isLt

/-- Reading below the occupied prefix does not see the padding. -/
theorem getElem!_append_left {l₁ l₂ : List ℕ} {j : ℕ} (hj : j < l₁.length) :
    (l₁ ++ l₂)[j]! = l₁[j]! := by
  rw [getElem!_pos (l₁ ++ l₂) j (by simp only [List.length_append]; omega),
    getElem!_pos l₁ j hj, List.getElem_append_left hj]

/-- **Padding the target array is free** — the constructive half of the
decoupling (Fa/D-x). The relation survives materializing the array at
any greater width, provided the padding holds vertices (`Shape`'s
range clause is over the whole array; the *adjacency* clause and every
read stay below `off[n]! = ns`). This is what a widened caller
supplies, and it is why the widening is a hypothesis generalization
and not a re-proof. -/
theorem widen (hc : Csr n ns G off tgt alv) {pad : List ℕ} (hpad : ∀ w ∈ pad, w < n) :
    Csr n ns G off (tgt ++ pad) alv := by
  have hlast : off[n]! ≤ tgt.length := hc.shape.2.2.2.1
  have hread : ∀ j, j < off[n]! → (tgt ++ pad)[j]! = tgt[j]! :=
    fun j hj => getElem!_append_left (by omega)
  refine ⟨⟨hc.shape.1, hc.shape.2.1, hc.shape.2.2.1, by simp only [List.length_append]; omega,
    fun j hj => ?_⟩, by rw [List.length_append]; have := hc.tlen; omega, hc.last, fun u v => ?_⟩
  · rcases Nat.lt_or_ge j tgt.length with h | h
    · rw [getElem!_append_left h]; exact hc.shape.2.2.2.2 j h
    · rw [List.length_append] at hj
      rw [getElem!_pos _ j (by simp only [List.length_append]; omega),
        List.getElem_append_right h]
      exact hpad _ (List.getElem_mem _)
  · have hrow : off[(u : ℕ) + 1]! ≤ off[n]! := hc.mono' u.isLt le_rfl
    rw [hc.adj u v]
    exact ⟨fun ⟨j, h₁, h₂, h₃⟩ => ⟨j, h₁, h₂, by rw [hread j (by omega)]; exact h₃⟩,
      fun ⟨j, h₁, h₂, h₃⟩ => ⟨j, h₁, h₂, by rwa [hread j (by omega)] at h₃⟩⟩

end Csr

/-! ### Refute before prove: the decoupling (Fa/D-x)

The wave's one authored delta is the severed width coupling, so the
refutable readings are the coupling it removes and the coupling it
keeps. The arena is §1's, its target array materialized three slots
wide of its six occupied ones. -/

section WidthFalsification

/-- §1's target array, materialized at width `9` for a structure that
occupies `6` slots. The padding names vertices — `Shape`'s range clause
is over the whole array — but no offset reaches it. -/
def demoTgtPad : List ℕ := demoTgt ++ [4, 4, 4]

/-- The same padded array with an `off` that *claims* the padding:
vertex `3`'s row is stretched to the end. A different arena — the point
of the differential below. -/
def demoOffWide : List ℕ := [0, 1, 3, 5, 9, 9]

-- the widened array is a legal shape, and the decoupled width clause
-- holds of it …
example : Shape 5 demoOff demoTgtPad (demoAlv 1) := by
  refine ⟨rfl, rfl, ?_, by decide, ?_⟩
  · intro i hi; interval_cases i <;> decide
  · intro j hj
    rw [show demoTgtPad.length = 9 from rfl] at hj
    interval_cases j <;> decide

example : 6 ≤ demoTgtPad.length := by decide

-- … **refuted**: the pinned reading does not. `tgt.length = ns` is
-- simply false at the widened width, which is why the old field
-- blocked every widened caller.
example : ¬ demoTgtPad.length = 6 := by decide

-- **refuted**: the width may not be *smaller* than the slot count —
-- the decoupling is one-sided. A short array has no relation at all,
-- whatever the graph.
example (G : SimpleGraph (Fin 5)) : ¬ Csr 5 6 G demoOff (demoTgt.take 4) (demoAlv 1) := by
  intro h
  have := h.tlen
  simp only [List.length_take, List.length_cons, List.length_nil] at this
  omega

-- **refuted**: nothing above the last offset is read, so nothing above
-- it is owned. "Every slot of the array has an owner" is true at the
-- pinned width and false at the widened one — slot `6` lies above
-- `off[5]! = 6`.
example : ¬ ∀ j < demoTgtPad.length,
    ∃ u : Fin 5, demoOff[(u : ℕ)]! ≤ j ∧ j < demoOff[(u : ℕ) + 1]! := by
  intro h
  obtain ⟨u, h₁, h₂⟩ := h 6 (by decide)
  fin_cases u <;> simp_all [demoOff]

/-! #### The differential: the widened search is the exact-width search

Same arena, same masks, same caps — the padded array answers exactly
what the six-slot array answers, at every one of §1's samples. -/

#guard bfsTw 5 3 0 demoOff demoTgtPad (demoAlv 1) = bfsTw 5 3 0 demoOff demoTgt (demoAlv 1)
#guard bfsTw 5 3 0 demoOff demoTgtPad (demoAlv 0) = bfsTw 5 3 0 demoOff demoTgt (demoAlv 0)
#guard bfsTw 5 1 0 demoOff demoTgtPad (demoAlv 1) = bfsTw 5 1 0 demoOff demoTgt (demoAlv 1)
#guard bfsTw 5 0 0 demoOff demoTgtPad (demoAlv 1) = bfsTw 5 0 0 demoOff demoTgt (demoAlv 1)
#guard bfsTw 5 4 0 demoOff demoTgtPad (demoAlv 1) = bfsTw 5 4 0 demoOff demoTgt (demoAlv 1)
#guard bfsTw 5 4 2 demoOff demoTgtPad (demoAlv 1) = bfsTw 5 4 2 demoOff demoTgt (demoAlv 1)

-- **Negative control.** The padding is live data, not slots that could
-- not matter: hand the same array an `off` that claims them and the
-- answer changes (vertex `4` becomes reachable from `3`). So the six
-- equalities above are the search declining to read what it was not
-- told to read.
#guard bfsTw 5 4 0 demoOffWide demoTgtPad (demoAlv 1)
  ≠ bfsTw 5 4 0 demoOff demoTgtPad (demoAlv 1)

-- …and the wrong reading fails, and says so.
/--
error: Expression
  decide (bfsTw 5 4 0 demoOffWide demoTgtPad (demoAlv 1) = bfsTw 5 4 0 demoOff demoTgt (demoAlv 1))
did not evaluate to `true`
-/
#guard_msgs in
#guard bfsTw 5 4 0 demoOffWide demoTgtPad (demoAlv 1) = bfsTw 5 4 0 demoOff demoTgt (demoAlv 1)

end WidthFalsification

/-- **The queue invariant.** -/
structure Fr (n d : ℕ) (G : SimpleGraph (Fin n)) (alv : List ℕ) (s : Fin n)
    (D Q : List ℕ) (hd tl : ℕ) : Prop where
  dlen : D.length = n
  qlen : Q.length = n
  cap : ∀ w < n, D[w]! ≤ d + 1
  src0 : D[(s : ℕ)]! = 0
  sound : ∀ v : Fin n, D[(v : ℕ)]! ≤ d → Bfs.WD G (maskOf n alv) D[(v : ℕ)]! s v
  hdle : hd ≤ tl
  room : tl + (undisc n (d + 1) alv D).card ≤ n
  qlt : ∀ i < tl, Q[i]! < n
  qmem : ∀ i < tl, D[Q[i]!]! ≤ d ∧ 0 < alv[Q[i]!]!
  qall : ∀ w < n, 0 < alv[w]! → D[w]! ≤ d → ∃ i < tl, Q[i]! = w
  qinj : ∀ i < tl, ∀ j < tl, Q[i]! = Q[j]! → i = j
  qmono : ∀ i j, i ≤ j → j < tl → D[Q[i]!]! ≤ D[Q[j]!]!
  qcap : ∀ i < tl, ∀ j, hd ≤ j → j < tl → D[Q[i]!]! ≤ D[Q[j]!]! + 1
  exp : ∀ i < hd, ∀ u w : Fin n, (u : ℕ) = Q[i]! → (masked G (maskOf n alv)).Adj u w →
    D[(w : ℕ)]! ≤ D[(u : ℕ)]! + 1

namespace Fr

variable {n d : ℕ} {G : SimpleGraph (Fin n)} {alv : List ℕ} {s : Fin n} {D Q : List ℕ}
  {hd tl : ℕ}

theorem tl_le (h : Fr n d G alv s D Q hd tl) : tl ≤ n := by
  have := h.room; omega

/-- **The exit argument.** Once the queue is empty every threshold below
the cap is decided, by induction on the threshold: the last edge of a
walk runs from a vertex the induction hypothesis settles, which is alive
because an edge of the arena has two live ends, hence on the queue,
hence — the queue being empty — expanded. -/
theorem complete (h : Fr n d G alv s D Q tl tl) :
    ∀ k ≤ d, ∀ w : Fin n, Bfs.WD G (maskOf n alv) k s w → D[(w : ℕ)]! ≤ k := by
  intro k
  induction k with
  | zero => intro _ w hw; rw [← hw.eq_of_zero]; exact le_of_eq h.src0
  | succ k ih =>
    intro hk w hw
    rcases hw.tail with hshort | ⟨c, hc, hcw⟩
    · have := ih (by omega) w hshort; omega
    · have hcd : D[(c : ℕ)]! ≤ k := ih (by omega) c hc
      have hca : 0 < alv[(c : ℕ)]! := maskOf_iff.mp (Bfs.masked_adj.mp hcw).2.1
      obtain ⟨i, hi, hQi⟩ := h.qall (c : ℕ) c.isLt hca (by omega)
      have := h.exp i hi c w hQi.symm hcw
      omega

/-- **What the search computes**, threshold by threshold. -/
theorem dist_le_iff (h : Fr n d G alv s D Q tl tl) (w : Fin n) {k : ℕ} (hk : k ≤ d) :
    D[(w : ℕ)]! ≤ k ↔ Bfs.WD G (maskOf n alv) k s w :=
  ⟨fun hle => (h.sound w (by omega)).mono hle, h.complete k hk w⟩

/-- **The one change the arrays undergo.** The head of the queue offers
its neighbour `w` one more than its own distance; `w` still reads the
sentinel, so it takes the offer and goes on the back of the queue.
`room` is why there is a slot for it, and `qcap` is why `w` was not on
the queue already. -/
theorem relax (h : Fr n d G alv s D Q hd tl) (hht : hd < tl) (v w : Fin n)
    (hv : (v : ℕ) = Q[hd]!) (hadj : (masked G (maskOf n alv)).Adj v w)
    (hdw : D[(w : ℕ)]! = d + 1) (hlt : D[(v : ℕ)]! < d) :
    Fr n d G alv s (D.set (w : ℕ) (D[(v : ℕ)]! + 1)) (Q.set tl (w : ℕ)) hd (tl + 1) := by
  obtain ⟨-, hva, hwa⟩ := Bfs.masked_adj.mp hadj
  rw [maskOf_iff] at hva hwa
  have hmemw : (w : ℕ) ∈ undisc n (d + 1) alv D := by
    simp only [undisc, Finset.mem_filter, Finset.mem_range]; exact ⟨w.isLt, hwa, hdw⟩
  have hcard : 0 < (undisc n (d + 1) alv D).card := Finset.card_pos.mpr ⟨_, hmemw⟩
  have hroom := h.room
  have htn : tl < n := by omega
  have hnq : ∀ i < tl, Q[i]! ≠ (w : ℕ) := fun i hi hqi => by
    have := (h.qmem i hi).1; rw [hqi, hdw] at this; omega
  have hwv : (w : ℕ) ≠ (v : ℕ) := fun hc => by rw [hc] at hdw; omega
  have hsw : (s : ℕ) ≠ (w : ℕ) := fun hc => by
    have h0 := h.src0; rw [hc, hdw] at h0; omega
  have hD' : ∀ j, (D.set (w : ℕ) (D[(v : ℕ)]! + 1))[j]!
      = if j = (w : ℕ) then D[(v : ℕ)]! + 1 else D[j]! :=
    fun j => get!_set D _ _ j (by rw [h.dlen]; exact w.isLt)
  have hQ' : ∀ j, (Q.set tl (w : ℕ))[j]! = if j = tl then (w : ℕ) else Q[j]! :=
    fun j => get!_set Q tl _ j (by rw [h.qlen]; exact htn)
  have dw' : (D.set (w : ℕ) (D[(v : ℕ)]! + 1))[(w : ℕ)]! = D[(v : ℕ)]! + 1 := by
    rw [hD', if_pos rfl]
  have dq' : ∀ i, i < tl → (D.set (w : ℕ) (D[(v : ℕ)]! + 1))[Q[i]!]! = D[Q[i]!]! :=
    fun i hi => by rw [hD', if_neg (hnq i hi)]
  have hund : undisc n (d + 1) alv (D.set (w : ℕ) (D[(v : ℕ)]! + 1))
      = (undisc n (d + 1) alv D).erase (w : ℕ) := by
    ext z
    simp only [undisc, Finset.mem_erase, Finset.mem_filter, Finset.mem_range, hD']
    by_cases hz : z = (w : ℕ)
    · subst hz
      simp only [if_true]
      exact ⟨fun hc => absurd hc.2.2 (by omega), fun hc => absurd rfl hc.1⟩
    · simp only [if_neg hz]
      exact ⟨fun hc => ⟨hz, hc⟩, fun hc => hc.2⟩
  refine ⟨by simp [h.dlen], by simp [h.qlen], fun z hz => ?_, ?_, fun z hz => ?_, by omega, ?_,
    fun i hi => ?_, fun i hi => ?_, fun z hz hza hzd => ?_, fun i hi j hj hij => ?_,
    fun i j hij hj => ?_, fun i hi j hj₁ hj₂ => ?_, fun i hi u w' hu hadj' => ?_⟩
  · rw [hD']; split_ifs <;> [omega; exact h.cap z hz]
  · rw [hD', if_neg hsw]; exact h.src0
  · rw [hD'] at hz ⊢
    by_cases hzw : (z : ℕ) = (w : ℕ)
    · obtain rfl : z = w := Fin.val_injective hzw
      rw [if_pos rfl]
      exact (h.sound v (by omega)).step hadj
    · rw [if_neg hzw] at hz ⊢; exact h.sound z hz
  · rw [hund, Finset.card_erase_of_mem hmemw]; omega
  · rw [hQ']; split_ifs with hit
    · exact w.isLt
    · exact h.qlt i (by omega)
  · rw [hQ']; split_ifs with hit
    · rw [hD', if_pos rfl]; exact ⟨by omega, hwa⟩
    · have hi' : i < tl := by omega
      rw [hD', if_neg (hnq i hi')]; exact h.qmem i hi'
  · rw [hD'] at hzd
    by_cases hzw : z = (w : ℕ)
    · exact ⟨tl, by omega, by rw [hQ', if_pos rfl, hzw]⟩
    · rw [if_neg hzw] at hzd
      obtain ⟨i, hi, hqi⟩ := h.qall z hz hza hzd
      exact ⟨i, by omega, by rw [hQ', if_neg (by omega), hqi]⟩
  · simp only [hQ'] at hij
    by_cases hit : i = tl <;> by_cases hjt : j = tl
    · omega
    · rw [if_pos hit, if_neg hjt] at hij; exact absurd hij.symm (hnq j (by omega))
    · rw [if_neg hit, if_pos hjt] at hij; exact absurd hij (hnq i (by omega))
    · rw [if_neg hit, if_neg hjt] at hij; exact h.qinj i (by omega) j (by omega) hij
  · have e2 : (Q.set tl (w : ℕ))[j]! = if j = tl then (w : ℕ) else Q[j]! := hQ' j
    have e1 : (Q.set tl (w : ℕ))[i]! = if i = tl then (w : ℕ) else Q[i]! := hQ' i
    by_cases hjt : j = tl <;> by_cases hit : i = tl
    · rw [e1, e2, if_pos hit, if_pos hjt]
    · rw [e1, e2, if_neg hit, if_pos hjt, dw', dq' i (by omega)]
      have := h.qcap i (by omega) hd le_rfl hht
      rw [← hv] at this; omega
    · omega
    · rw [e1, e2, if_neg hit, if_neg hjt, dq' i (by omega), dq' j (by omega)]
      exact h.qmono i j hij (by omega)
  · have e2 : (Q.set tl (w : ℕ))[j]! = if j = tl then (w : ℕ) else Q[j]! := hQ' j
    have e1 : (Q.set tl (w : ℕ))[i]! = if i = tl then (w : ℕ) else Q[i]! := hQ' i
    by_cases hjt : j = tl <;> by_cases hit : i = tl
    · rw [e1, e2, if_pos hit, if_pos hjt]; omega
    · rw [e1, e2, if_neg hit, if_pos hjt, dw', dq' i (by omega)]
      have := h.qcap i (by omega) hd le_rfl hht
      rw [← hv] at this; omega
    · have hdvj : D[(v : ℕ)]! ≤ D[Q[j]!]! := by
        have := h.qmono hd j hj₁ (by omega); rw [← hv] at this; exact this
      rw [e1, e2, if_pos hit, if_neg hjt, dw', dq' j (by omega)]; omega
    · rw [e1, e2, if_neg hit, if_neg hjt, dq' i (by omega), dq' j (by omega)]
      exact h.qcap i (by omega) j hj₁ (by omega)
  · have hit : i ≠ tl := by omega
    rw [hQ', if_neg hit] at hu
    rw [hD' (u : ℕ), if_neg (by rw [hu]; exact hnq i (by omega))]
    by_cases hzw : (w' : ℕ) = (w : ℕ)
    · exfalso
      have h₁ := h.exp i hi u w' hu hadj'
      have h₂ := h.qmono i hd (by omega) hht
      rw [← hv, ← hu] at h₂
      rw [hzw, hdw] at h₁
      omega
    · rw [hD' (w' : ℕ), if_neg hzw]; exact h.exp i hi u w' hu hadj'

end Fr



/-! ### One row, one slot at a time -/

/-- The invariant of the scan of `v`'s row, popped from index `hd`: the
queue invariant with `hd` *not yet* advanced, plus what the slots
already looked at have achieved. -/
structure SInv (n d : ℕ) (G : SimpleGraph (Fin n)) (off tgt alv : List ℕ) (s : Fin n)
    (hd : ℕ) (v : Fin n) (dv : ℕ) (t : St) : Prop where
  fr : Fr n d G alv s t.1 t.2.1 hd t.2.2.1
  hdlt : hd < t.2.2.1
  vq : (v : ℕ) = t.2.1[hd]!
  dvv : t.1[(v : ℕ)]! = dv
  lo : off[(v : ℕ)]! ≤ t.2.2.2
  hi : t.2.2.2 ≤ off[(v : ℕ) + 1]!
  scanned : ∀ j, off[(v : ℕ)]! ≤ j → j < t.2.2.2 → 0 < alv[tgt[j]!]! → t.1[tgt[j]!]! ≤ dv + 1

variable {n ns d : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ} {s v : Fin n}
  {hd tl dv : ℕ} {D Q : List ℕ} {t : St}

/-- The row of a vertex ends inside the target array. -/
theorem Csr.row_le (hc : Csr n ns G off tgt alv) (v : Fin n) : off[(v : ℕ) + 1]! ≤ tgt.length :=
  hc.shape.row_le v.isLt

/-- **One slot.** The three things the slot's operations need, and the
invariant again. The relaxing case is `Fr.relax`; the other two rest on
`qcap`, which bounds an already discovered neighbour by one more than
the popped vertex's own distance. -/
theorem SInv_step (hc : Csr n ns G off tgt alv) (hdv : dv < d)
    (hI : SInv n d G off tgt alv s hd v dv t) (hb : scanBf off[(v : ℕ) + 1]! t = true) :
    scanP n (d + 1) off[(v : ℕ) + 1]! off tgt alv t ∧
      SInv n d G off tgt alv s hd v dv (scanStep tgt alv (d + 1) (dv + 1) t) := by
  have hkend : off[(v : ℕ) + 1]! ≤ tgt.length := hc.row_le v
  have hk : t.2.2.2 < off[(v : ℕ) + 1]! := by simpa [scanBf] using hb
  have hun : tgt[t.2.2.2]! < n := hc.shape.2.2.2.2 _ (by omega)
  have hva : 0 < alv[(v : ℕ)]! := by
    have := (hI.fr.qmem hd hI.hdlt).2; rwa [← hI.vq] at this
  refine ⟨⟨hc.shape, hI.fr.dlen, hI.fr.qlen, hkend, hI.fr.room⟩, ?_⟩
  -- the slot that does not relax leaves an already discovered neighbour, and `qcap` bounds it
  have hskip : (0 < alv[tgt[t.2.2.2]!]! → t.1[tgt[t.2.2.2]!]! ≤ dv + 1) →
      scanStep tgt alv (d + 1) (dv + 1) t = (t.1, t.2.1, t.2.2.1, t.2.2.2 + 1) →
      SInv n d G off tgt alv s hd v dv (scanStep tgt alv (d + 1) (dv + 1) t) := by
    intro hlast heq
    have hlo := hI.lo
    rw [heq]
    refine ⟨hI.fr, hI.hdlt, hI.vq, hI.dvv, show off[(v : ℕ)]! ≤ t.2.2.2 + 1 by omega,
      show t.2.2.2 + 1 ≤ off[(v : ℕ) + 1]! by omega, ?_⟩
    show ∀ j, off[(v : ℕ)]! ≤ j → j < t.2.2.2 + 1 → 0 < alv[tgt[j]!]! → t.1[tgt[j]!]! ≤ dv + 1
    intro j hj1 hj2 hja
    rcases Nat.lt_or_ge j t.2.2.2 with hlt | hge
    · exact hI.scanned j hj1 hlt hja
    · rw [show j = t.2.2.2 by omega] at hja ⊢; exact hlast hja
  by_cases ha : 0 < alv[tgt[t.2.2.2]!]!
  · by_cases hu : t.1[tgt[t.2.2.2]!]! = d + 1
    · -- the slot relaxes
      have hmemw : tgt[t.2.2.2]! ∈ undisc n (d + 1) alv t.1 := by
        simp only [undisc, Finset.mem_filter, Finset.mem_range]; exact ⟨hun, ha, hu⟩
      have hcard := Finset.card_pos.mpr ⟨_, hmemw⟩
      have hroom := hI.fr.room
      have htn : t.2.2.1 < n := by omega
      have hadj : (masked G (maskOf n alv)).Adj v ⟨_, hun⟩ :=
        Bfs.masked_adj.mpr ⟨(hc.adj v ⟨_, hun⟩).mpr ⟨t.2.2.2, hI.lo, hk, rfl⟩,
          maskOf_iff.mpr hva, maskOf_iff.mpr ha⟩
      have hfr := hI.fr.relax hI.hdlt v ⟨_, hun⟩ hI.vq hadj hu (by rw [hI.dvv]; exact hdv)
      rw [hI.dvv] at hfr
      have hD' : ∀ j, (t.1.set tgt[t.2.2.2]! (dv + 1))[j]!
          = if j = tgt[t.2.2.2]! then dv + 1 else t.1[j]! :=
        fun j => get!_set _ _ _ j (by rw [hI.fr.dlen]; exact hun)
      have hQ' : ∀ j, (t.2.1.set t.2.2.1 tgt[t.2.2.2]!)[j]!
          = if j = t.2.2.1 then tgt[t.2.2.2]! else t.2.1[j]! :=
        fun j => get!_set _ _ _ j (by rw [hI.fr.qlen]; exact htn)
      have hvne : (v : ℕ) ≠ tgt[t.2.2.2]! := fun hcc => by rw [← hcc, hI.dvv] at hu; omega
      rw [show scanStep tgt alv (d + 1) (dv + 1) t
          = (t.1.set tgt[t.2.2.2]! (dv + 1), t.2.1.set t.2.2.1 tgt[t.2.2.2]!,
              t.2.2.1 + 1, t.2.2.2 + 1) by simp only [scanStep, if_pos ha, if_pos hu]]
      have hlo := hI.lo
      have hhd := hI.hdlt
      refine ⟨hfr, show hd < t.2.2.1 + 1 by omega, ?_, ?_,
        show off[(v : ℕ)]! ≤ t.2.2.2 + 1 by omega,
        show t.2.2.2 + 1 ≤ off[(v : ℕ) + 1]! by omega, ?_⟩
      · show (v : ℕ) = (t.2.1.set t.2.2.1 tgt[t.2.2.2]!)[hd]!
        rw [hQ', if_neg (by omega)]; exact hI.vq
      · show (t.1.set tgt[t.2.2.2]! (dv + 1))[(v : ℕ)]! = _
        rw [hD', if_neg hvne]; exact hI.dvv
      · show ∀ j, off[(v : ℕ)]! ≤ j → j < t.2.2.2 + 1 → 0 < alv[tgt[j]!]! →
          (t.1.set tgt[t.2.2.2]! (dv + 1))[tgt[j]!]! ≤ dv + 1
        intro j hj1 hj2 hja
        rw [hD']
        by_cases hjt : tgt[j]! = tgt[t.2.2.2]!
        · rw [if_pos hjt]
        · rw [if_neg hjt]
          rcases Nat.lt_or_ge j t.2.2.2 with hlt | hge
          · exact hI.scanned j hj1 hlt hja
          · exact absurd (show tgt[j]! = tgt[t.2.2.2]! by rw [show j = t.2.2.2 by omega]) hjt
    · refine hskip (fun _ => ?_) (by simp only [scanStep, if_pos ha, if_neg hu])
      have hcapu := hI.fr.cap _ hun
      obtain ⟨i, hi, hqi⟩ := hI.fr.qall _ hun ha (by omega)
      have hq := hI.fr.qcap i hi hd le_rfl hI.hdlt
      rw [hqi, ← hI.vq, hI.dvv] at hq
      exact hq
  · exact hskip (fun hcc => absurd hcc ha) (by simp only [scanStep, if_neg ha])

/-- **The row is done.** Every neighbour of the popped vertex has been
offered a distance, so the head may advance. -/
theorem SInv.pop (hc : Csr n ns G off tgt alv) (hI : SInv n d G off tgt alv s hd v dv t)
    (hdone : off[(v : ℕ) + 1]! ≤ t.2.2.2) :
    Fr n d G alv s t.1 t.2.1 (hd + 1) t.2.2.1 := by
  have h := hI.fr
  refine ⟨h.dlen, h.qlen, h.cap, h.src0, h.sound, by have := hI.hdlt; omega, h.room, h.qlt,
    h.qmem, h.qall, h.qinj, h.qmono, fun i hi j hj₁ hj₂ => h.qcap i hi j (by omega) hj₂, ?_⟩
  intro i hi u w' hu hadj
  rcases Nat.lt_or_ge i hd with hlt | hge
  · exact h.exp i hlt u w' hu hadj
  · obtain rfl : i = hd := by omega
    obtain rfl : u = v := Fin.val_injective (hu.trans hI.vq.symm)
    obtain ⟨hg, -, hwa⟩ := Bfs.masked_adj.mp hadj
    obtain ⟨j, hj₁, hj₂, hj₃⟩ := (hc.adj u w').mp hg
    rw [hI.dvv, ← hj₃]
    exact hI.scanned j hj₁ (by omega) (by rw [hj₃]; exact maskOf_iff.mp hwa)

/-- …and so it may when the cap stops the row from being scanned at
all: the sentinel already bounds every neighbour. -/
theorem Fr.popSkip (h : Fr n d G alv s D Q hd tl) (hht : hd < tl) (hdv : ¬ D[Q[hd]!]! < d) :
    Fr n d G alv s D Q (hd + 1) tl := by
  refine ⟨h.dlen, h.qlen, h.cap, h.src0, h.sound, by omega, h.room, h.qlt, h.qmem, h.qall,
    h.qinj, h.qmono, fun i hi j hj₁ hj₂ => h.qcap i hi j (by omega) hj₂, ?_⟩
  intro i hi u w' hu hadj
  rcases Nat.lt_or_ge i hd with hlt | hge
  · exact h.exp i hlt u w' hu hadj
  · rw [show i = hd from by omega] at hu
    have hcapw := h.cap _ w'.isLt
    have hqm := (h.qmem hd hht).1
    rw [← hu] at hdv hqm
    omega

/-- **The seed.** The source is written at distance zero whether or not
it is alive; only the queue notices the difference. -/
theorem Fr.seed (hDlen : D.length = n) (hQlen : Q.length = n)
    (hfill : ∀ j, j < n → D[j]! = d + 1) :
    Fr n d G alv s (D.set (s : ℕ) 0) (Q.set 0 (s : ℕ)) 0
      (if 0 < alv[(s : ℕ)]! then 1 else 0) := by
  have hsn : (s : ℕ) < n := s.isLt
  have hD' : ∀ j, (D.set (s : ℕ) 0)[j]! = if j = (s : ℕ) then 0 else D[j]! :=
    fun j => get!_set _ _ _ j (by rw [hDlen]; exact hsn)
  have hQ' : ∀ j, (Q.set 0 (s : ℕ))[j]! = if j = 0 then (s : ℕ) else Q[j]! :=
    fun j => get!_set _ _ _ j (by rw [hQlen]; omega)
  have htl : (if 0 < alv[(s : ℕ)]! then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have hsub : undisc n (d + 1) alv (D.set (s : ℕ) 0) ⊆ (Finset.range n).erase (s : ℕ) := by
    intro z hz
    simp only [undisc, Finset.mem_filter, Finset.mem_range] at hz
    refine Finset.mem_erase.mpr ⟨fun hc => ?_, Finset.mem_range.mpr hz.1⟩
    rw [hc, hD', if_pos rfl] at hz; omega
  have hcard : (undisc n (d + 1) alv (D.set (s : ℕ) 0)).card ≤ n - 1 := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem (Finset.mem_range.mpr hsn), Finset.card_range] at this
  have hzero : ∀ z, z < n → (D.set (s : ℕ) 0)[z]! ≤ d → z = (s : ℕ) := by
    intro z hz hzd
    by_contra hc
    rw [hD', if_neg hc, hfill z hz] at hzd; omega
  refine ⟨by simp [hDlen], by simp [hQlen], fun z hz => ?_, by rw [hD', if_pos rfl],
    fun z hz => ?_, by omega, by omega, fun i hi => ?_, fun i hi => ?_,
    fun z hz hza hzd => ?_, fun i hi j hj hij => by omega, fun i j hij hj => by
      rw [show i = 0 by omega, show j = 0 by omega], fun i hi j hj₁ hj₂ => by
      rw [show i = 0 by omega, show j = 0 by omega]; omega, fun i hi => absurd hi (by omega)⟩
  · rw [hD']; split_ifs with hc
    · omega
    · rw [hfill z hz]
  · obtain rfl : z = s := Fin.val_injective (hzero _ z.isLt hz)
    rw [hD', if_pos rfl]
    exact Bfs.WD.refl G (maskOf n alv) 0 z
  · rw [hQ', if_pos (by omega)]; exact hsn
  · have hal : 0 < alv[(s : ℕ)]! := by by_contra hc; rw [if_neg hc] at hi; omega
    rw [hQ', if_pos (by omega), hD', if_pos rfl]
    exact ⟨by omega, hal⟩
  · obtain rfl : z = (s : ℕ) := hzero z hz hzd
    exact ⟨0, by rw [if_pos hza]; omega, by rw [hQ', if_pos rfl]⟩

/-! ### The rows of the queue tile the target array -/

/-- The blocks of the first `k` vertices tile the array up to the
`k`-th offset. -/
theorem Csr.tele (hc : Csr n ns G off tgt alv) :
    ∀ k, k ≤ n → ∑ v ∈ Finset.range k, rowLen off v = off[k]! - off[0]! := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : off[0]! ≤ off[k]! := hc.mono' (Nat.zero_le _) (by omega)
    have h2 : off[k]! ≤ off[k + 1]! := hc.shape.2.2.1 k (by omega)
    rw [Finset.sum_range_succ, ih (by omega)]
    simp only [rowLen]; omega

/-- **The cost bound of the whole search**: the rows of the vertices the
queue has already expanded fit inside the target array, the queue's
injectivity standing in for distinctness. -/
theorem Csr.rowSum_le (hc : Csr n ns G off tgt alv) {Q : List ℕ} {k tl : ℕ}
    (hqlt : ∀ i < tl, Q[i]! < n) (hqinj : ∀ i < tl, ∀ j < tl, Q[i]! = Q[j]! → i = j)
    (hk : k ≤ tl) : ∑ i ∈ Finset.range k, rowLen off Q[i]! ≤ ns := by
  have himg : ∑ v ∈ (Finset.range k).image (fun i => Q[i]!), rowLen off v
      = ∑ i ∈ Finset.range k, rowLen off Q[i]! :=
    Finset.sum_image fun i hi j hj hq =>
      hqinj i (by have := Finset.mem_range.mp hi; omega) j
        (by have := Finset.mem_range.mp hj; omega) hq
  have hsub : (Finset.range k).image (fun i => Q[i]!) ⊆ Finset.range n := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_range.mpr (hqlt i (by have := Finset.mem_range.mp hi; omega))
  rw [← himg]
  calc ∑ v ∈ (Finset.range k).image (fun i => Q[i]!), rowLen off v
      ≤ ∑ v ∈ Finset.range n, rowLen off v := Finset.sum_le_sum_of_subset hsub
    _ = off[n]! - off[0]! := hc.tele n le_rfl
    _ ≤ ns := by rw [hc.last]; omega

/-! ## 5. The drain

The one loop whose iteration count is not a state measure: it runs once
per *popped* vertex, and its price is paid out of a two-currency energy
— one `popC` per vertex still to pop, one `scanC` per adjacency slot
still to scan (`Csr.rowSum_le` is why the second is bounded by `ns`). -/

/-- The slots the queue's expanded prefix has already consumed. -/
def rowSum (off Q : List ℕ) (h : ℕ) : ℕ := ∑ i ∈ Finset.range h, rowLen off Q[i]!

/-- **One pop.** The head is expanded, or the cap stops it; either way
the head advances by one, the queue's expanded prefix is untouched, and
the price is one `popC` plus one `scanC` per slot of the row. -/
theorem popF_le (hc : Csr n ns G off tgt alv)
    (h : Fr n d G alv s t.1 t.2.1 t.2.2.1 t.2.2.2) (hb : popBf t = true) :
    popF n d (d + 1) off tgt alv t
      ≤ NRest.spec
          (fun t' : St => Fr n d G alv s t'.1 t'.2.1 t'.2.2.1 t'.2.2.2 ∧
            t'.2.2.1 = t.2.2.1 + 1 ∧ ∀ i, i < t.2.2.1 + 1 → t'.2.1[i]! = t.2.1[i]!)
          (fun _ => liftACost (popC + rowLen off t.2.1[t.2.2.1]! • iter scanC)) := by
  have hht : t.2.2.1 < t.2.2.2 := by simpa [popBf] using hb
  have hqh : t.2.2.1 < t.2.1.length := by rw [h.qlen]; have := h.tl_le; omega
  have hvn : t.2.1[t.2.2.1]! < n := h.qlt _ hht
  have hvd : t.2.1[t.2.2.1]! < t.1.length := by rw [h.dlen]; exact hvn
  have hoff1 : t.2.1[t.2.2.1]! + 1 < off.length := by rw [hc.shape.1]; omega
  have hoff0 : t.2.1[t.2.2.1]! < off.length := by omega
  simp only [popF, mopAget_def, NRest.assert_pos hqh, NRest.assert_pos hvd,
    NRest.returnT_bindT, mopBinop_def, Imp.Bop.apply_add, binopCurrency_add,
    irIf_def, NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume]
  by_cases hcap : t.1[t.2.1[t.2.2.1]!]! < d
  · -- the row is scanned
    set v : Fin n := ⟨t.2.1[t.2.2.1]!, hvn⟩ with hvdef
    set dv := t.1[t.2.1[t.2.2.1]!]! with hdvdef
    have hkend := hc.row_le v
    have hlo : off[(v : ℕ)]! ≤ off[(v : ℕ) + 1]! := hc.shape.2.2.1 _ hvn
    have hstart : SInv n d G off tgt alv s t.2.2.1 v dv (t.1, t.2.1, t.2.2.2, off[(v : ℕ)]!) ∧
        ∀ i, i < t.2.2.1 + 1 → (t.1, t.2.1, t.2.2.2, off[(v : ℕ)]!).2.1[i]! = t.2.1[i]! := by
      refine ⟨⟨h, hht, rfl, rfl, le_rfl, hlo, ?_⟩, fun _ _ => rfl⟩
      intro j hj1 hj2 _
      exact absurd hj2 (Nat.not_lt.mpr hj1)
    have hs : ∀ z : St,
        (SInv n d G off tgt alv s t.2.2.1 v dv z ∧
          ∀ i, i < t.2.2.1 + 1 → z.2.1[i]! = t.2.1[i]!) →
        scanBf off[(v : ℕ) + 1]! z = true →
        scanP n (d + 1) off[(v : ℕ) + 1]! off tgt alv z ∧
          (SInv n d G off tgt alv s t.2.2.1 v dv (scanStep tgt alv (d + 1) (dv + 1) z) ∧
            ∀ i, i < t.2.2.1 + 1 → (scanStep tgt alv (d + 1) (dv + 1) z).2.1[i]! = t.2.1[i]!) := by
      intro z hz hzb
      obtain ⟨hP, hI'⟩ := SInv_step hc hcap hz.1 hzb
      have hz1 := hz.1
      have hkt : z.2.2.2 < tgt.length := lt_of_lt_of_le (by simpa [scanBf] using hzb) hkend
      have hun : tgt[z.2.2.2]! < n := hc.shape.2.2.2.2 _ hkt
      refine ⟨hP, hI', fun i hi => ?_⟩
      rw [show (scanStep tgt alv (d + 1) (dv + 1) z).2.1
          = if 0 < alv[tgt[z.2.2.2]!]! ∧ z.1[tgt[z.2.2.2]!]! = d + 1
            then z.2.1.set z.2.2.1 tgt[z.2.2.2]! else z.2.1 by
        simp only [scanStep]; split_ifs <;> simp_all]
      split_ifs with hcc
      · have hmemw : tgt[z.2.2.2]! ∈ undisc n (d + 1) alv z.1 := by
          simp only [undisc, Finset.mem_filter, Finset.mem_range]
          exact ⟨hun, hcc.1, hcc.2⟩
        have hcp := Finset.card_pos.mpr ⟨_, hmemw⟩
        have hrm := hz1.fr.room
        have hhl := hz1.hdlt
        rw [get!_set z.2.1 z.2.2.1 tgt[z.2.2.2]! i (by rw [hz1.fr.qlen]; omega),
          if_neg (by omega)]
        exact hz.2 i hi
      · exact hz.2 i hi
    have hscan := scanLoop_le (Inv := fun z : St =>
        SInv n d G off tgt alv s t.2.2.1 v dv z ∧ ∀ i, i < t.2.2.1 + 1 → z.2.1[i]! = t.2.1[i]!)
      n (d + 1) (dv + 1) off[(v : ℕ) + 1]! off tgt alv hs
      (off[(v : ℕ) + 1]! - off[(v : ℕ)]!) _ hstart (by simp)
    have hK : ∀ z : St, ((SInv n d G off tgt alv s t.2.2.1 v dv z ∧
          ∀ i, i < t.2.2.1 + 1 → z.2.1[i]! = t.2.1[i]!) ∧ off[(v : ℕ) + 1]! ≤ z.2.2.2) →
        NRest.bindT (pack3 z.1 z.2.1 z.2.2.1) (fun r => pack4 r.1 r.2.1 (t.2.2.1 + 1) r.2.2)
          ≤ NRest.spec (fun t' : St => Fr n d G alv s t'.1 t'.2.1 t'.2.2.1 t'.2.2.2 ∧
              t'.2.2.1 = t.2.2.1 + 1 ∧ ∀ i, i < t.2.2.1 + 1 → t'.2.1[i]! = t.2.1[i]!)
            (fun _ => irUnit Currency.skip + irUnit Currency.skip + irUnit Currency.skip
              + irUnit Currency.skip + irUnit Currency.skip) := by
      rintro z ⟨⟨hzI, hzq⟩, hdone⟩
      simp only [pack3, pack4, mopPair_def, bindT_unitT, NRest.consume_consume]
      exact consume_returnT_le_spec ⟨hzI.pop hc hdone, rfl, hzq⟩ (le_of_eq (by ac_rfl))
    rw [if_pos (by simp [hcap] : (decide (dv < d)) = true)]
    simp only [NRest.assert_pos hoff0, NRest.assert_pos hoff1, NRest.returnT_bindT,
      NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
      NRest.bindT_assoc_acost, pack4_bindT]
    refine le_trans (NRest.consume_mono
      (le_trans (NRest.bindT_mono hscan fun _ => le_rfl) (bindT_spec_le _ _ _ _ _ hK)) le_rfl)
      (le_of_eq ?_)
    rw [consume_spec]
    refine congrArg (NRest.spec _) (funext fun _ => ?_)
    simp only [popC, iter, rowLen, liftACost_add, liftACost_nsmul, liftACost_cu, hvdef]
    ac_rfl
  · rw [if_neg (by simp only [decide_eq_true_eq]; exact hcap)]
    simp only [pack3, pack4, mopPair_def, bindT_unitT, NRest.consume_consume]
    refine consume_returnT_le_spec ⟨h.popSkip hht hcap, rfl, fun _ _ => rfl⟩ ?_
    refine le_trans (cost_le_add _ (irUnit Currency.add + irUnit Currency.aget
      + irUnit Currency.add + irUnit Currency.aget + irUnit Currency.«while»
      + irUnit Currency.skip + irUnit Currency.skip + irUnit Currency.skip
      + rowLen off t.2.1[t.2.2.1]! • liftACost (iter scanC))) (le_of_eq ?_)
    simp only [popC, iter, liftACost_add, liftACost_nsmul, liftACost_cu]
    ac_rfl

/-- **The drain.** Its energy is two-currency: one `popC` for every
vertex still to pop, one `scanC` for every adjacency slot still to
scan. The second is bounded because the rows of the queue's distinct
vertices tile the target array (`Csr.rowSum_le`). -/
theorem drainLoop_le (hc : Csr n ns G off tgt alv) :
    ∀ (fuel : ℕ) (z : St), Fr n d G alv s z.1 z.2.1 z.2.2.1 z.2.2.2 → n - z.2.2.1 ≤ fuel →
      drainLoop n d (d + 1) off tgt alv z
        ≤ NRest.spec
            (fun z' : St => Fr n d G alv s z'.1 z'.2.1 z'.2.2.1 z'.2.2.2 ∧ z'.2.2.2 ≤ z'.2.2.1)
            (fun _ => liftACost (E2 (iter popC) (iter scanC) (n - z.2.2.1)
              (ns - rowSum off z.2.1 z.2.2.1) + cu Currency.«while»)) := by
  have exit : ∀ z : St, Fr n d G alv s z.1 z.2.1 z.2.2.1 z.2.2.2 → z.2.2.2 ≤ z.2.2.1 →
      drainLoop n d (d + 1) off tgt alv z
        ≤ NRest.spec
            (fun z' : St => Fr n d G alv s z'.1 z'.2.1 z'.2.2.1 z'.2.2.2 ∧ z'.2.2.2 ≤ z'.2.2.1)
            (fun _ => liftACost (E2 (iter popC) (iter scanC) (n - z.2.2.1)
              (ns - rowSum off z.2.1 z.2.2.1) + cu Currency.«while»)) := by
    intro z hz hle
    have hb : popBf z = false := by simp only [popBf, decide_eq_false_iff_not]; omega
    simp only [drainLoop, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨hz, hle⟩ ?_
    rw [liftACost_add, liftACost_cu, add_comm]
    exact cost_le_add _ _
  intro fuel
  induction fuel with
  | zero => intro z hz hf; exact exit z hz (by have := hz.hdle; have := hz.tl_le; omega)
  | succ fuel ih =>
    intro z hz hf
    by_cases hb : z.2.2.1 < z.2.2.2
    · have hbt : popBf z = true := by simp [popBf, hb]
      have hIs : popBf z = true → popP n (d + 1) off tgt alv z :=
        fun _ => ⟨hc.shape, hz.dlen, hz.qlen, hz.qlt, hz.room⟩
      have hS' : rowSum off z.2.1 (z.2.2.1 + 1)
          = rowSum off z.2.1 z.2.2.1 + rowLen off z.2.1[z.2.2.1]! := Finset.sum_range_succ _ _
      have hSle : rowSum off z.2.1 (z.2.2.1 + 1) ≤ ns := by
        rw [rowSum]; exact hc.rowSum_le (tl := z.2.2.2) hz.qlt hz.qinj (by omega)
      have hzn : z.2.2.1 < n := lt_of_lt_of_le hb hz.tl_le
      have hcont : ∀ z' : St, (Fr n d G alv s z'.1 z'.2.1 z'.2.2.1 z'.2.2.2 ∧
            z'.2.2.1 = z.2.2.1 + 1 ∧ ∀ i, i < z.2.2.1 + 1 → z'.2.1[i]! = z.2.1[i]!) →
          drainLoop n d (d + 1) off tgt alv z'
            ≤ NRest.spec
                (fun z'' : St => Fr n d G alv s z''.1 z''.2.1 z''.2.2.1 z''.2.2.2 ∧
                  z''.2.2.2 ≤ z''.2.2.1)
                (fun _ => liftACost (E2 (iter popC) (iter scanC) (n - (z.2.2.1 + 1))
                  (ns - rowSum off z.2.1 (z.2.2.1 + 1)) + cu Currency.«while»)) := by
        rintro z' ⟨hfr', hhd', hq'⟩
        refine le_trans (ih z' hfr' (by omega))
          (spec_mono (fun _ hx => hx) fun _ _ => le_of_eq ?_)
        have hrs : rowSum off z'.2.1 (z.2.2.1 + 1) = rowSum off z.2.1 (z.2.2.1 + 1) := by
          rw [rowSum, rowSum]
          exact Finset.sum_congr rfl fun i hi => by
            rw [hq' i (by have := Finset.mem_range.mp hi; omega)]
        rw [hhd', hrs]
      have hcost : irUnit Currency.«while»
          + (liftACost (popC + rowLen off z.2.1[z.2.2.1]! • iter scanC)
            + liftACost (E2 (iter popC) (iter scanC) (n - (z.2.2.1 + 1))
                (ns - rowSum off z.2.1 (z.2.2.1 + 1)) + cu Currency.«while»))
          = liftACost (E2 (iter popC) (iter scanC) (n - z.2.2.1)
              (ns - rowSum off z.2.1 z.2.2.1) + cu Currency.«while») := by
        rw [show n - z.2.2.1 = (n - (z.2.2.1 + 1)) + 1 by omega,
          show ns - rowSum off z.2.1 z.2.2.1
            = (ns - rowSum off z.2.1 (z.2.2.1 + 1)) + rowLen off z.2.1[z.2.2.1]! by omega,
          E2_split]
        simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
        ac_rfl
      calc drainLoop n d (d + 1) off tgt alv z
            = NRest.consume (NRest.bindT (popF n d (d + 1) off tgt alv z)
                fun z' => drainLoop n d (d + 1) off tgt alv z') (irUnit Currency.«while») := by
              simp only [drainLoop]; rw [irWhileIT_of_true hIs hbt]
          _ ≤ NRest.consume (NRest.spec _ (fun _ => liftACost (popC + rowLen off z.2.1[z.2.2.1]! •
                iter scanC) + liftACost (E2 (iter popC) (iter scanC) (n - (z.2.2.1 + 1))
                  (ns - rowSum off z.2.1 (z.2.2.1 + 1)) + cu Currency.«while»)))
                (irUnit Currency.«while») :=
              NRest.consume_mono (le_trans (NRest.bindT_mono (popF_le hc hz hbt) fun _ => le_rfl)
                (bindT_spec_le _ _ _ _ _ hcont)) le_rfl
          _ = _ := by rw [consume_spec, ← hcost]
    · exact exit z hz (by omega)

/-! ## 6. The export -/

/-- **The exported postcondition**, in the shape of `RamBfs.bfs_spec`'s
(design note P7/S-1): the array decides, at every threshold up to the
cap, the distance bound of the arena — `G` with the mask's dead vertices
isolated, which is exactly `Bfs.masked G (maskOf n alv)`. -/
def QPost (n d src : ℕ) (G : SimpleGraph (Fin n)) (alv : List ℕ) (hsrc : src < n)
    (D : List ℕ) : Prop :=
  D.length = n ∧ ∀ v : Fin n, ∀ k, k ≤ d →
    (D[(v : ℕ)]! ≤ k ↔ Bfs.WD G (maskOf n alv) k ⟨src, hsrc⟩ v)

/-- The prefix and the seed: everything the two loops do not pay for. -/
def bfsK : ACost String ℕ := cu Currency.add + cu Currency.const + cu Currency.«while»
  + cu Currency.aset + cu Currency.aset + cu Currency.aget + cu Currency.ite + cu Currency.const
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.«while»

/-- **The advertised budget**: linear in the number of vertices and in
the number of adjacency slots, at the IR's own currencies. -/
def bfsBudget (n ns : ℕ) : ACost String ℕ :=
  n • iter fillC + n • iter popC + ns • iter scanC + bfsK

/-- The complete account paid by the synthesized BFS export: its extra
leading `skip`, followed by the abstract BFS budget. -/
def bfsQTotal (n ns : ℕ) : ACost String ℕ :=
  cu Currency.skip + bfsBudget n ns

/-- The canonical vector form of the complete BFS account.  Both inequalities
are organized by the P3.A source-shaped cost solver; only the resulting scalar
natural-number obligations are handed to arithmetic normalization. -/
theorem bfsQTotal_normal (n ns : ℕ) :
    bfsQTotal n ns =
      ACost.cost Currency.skip (9 * n + 5 * ns + 4) +
      ACost.cost Currency.const 2 +
      ACost.cost Currency.aget (4 * n + 3 * ns + 1) +
      ACost.cost Currency.aset (n + 2 * ns + 2) +
      ACost.cost Currency.ite (n + 2 * ns + 1) +
      ACost.cost Currency.«while» (3 * n + ns + 2) +
      ACost.cost Currency.add (4 * n + 2 * ns + 1) := by
  apply le_antisymm
  · rw [← liftACost_le_iff]
    simp only [bfsQTotal, bfsBudget, bfsK, iter, fillC, popC, scanC, scanC0, cu,
      norm_cost]
    sc_solve
    simp only [true_and, zero_add, nsmul_eq_mul]
    repeat' apply And.intro
    all_goals first | trivial | (apply le_of_eq; push_cast; ring)
  · rw [← liftACost_le_iff]
    simp only [bfsQTotal, bfsBudget, bfsK, iter, fillC, popC, scanC, scanC0, cu,
      norm_cost]
    sc_solve
    simp only [true_and, zero_add, nsmul_eq_mul]
    repeat' apply And.intro
    all_goals first | trivial | (apply le_of_eq; push_cast; ring)

/-! The source-shaped account is inspected structurally, before any exchange
rate is applied.  These seven coordinates are the complete support. -/

@[simp] theorem bfsQTotal_skip (n ns : ℕ) :
    (bfsQTotal n ns).toFun Currency.skip = 9 * n + 5 * ns + 4 := by
  simp [bfsQTotal, bfsBudget, bfsK, iter, fillC, popC, scanC, scanC0, cu,
    Currency.skip, Currency.const, Currency.aget, Currency.aset, Currency.ite,
    Currency.«while», Currency.add]
  ring

@[simp] theorem bfsQTotal_const (n ns : ℕ) :
    (bfsQTotal n ns).toFun Currency.const = 2 := by
  simp [bfsQTotal, bfsBudget, bfsK, iter, fillC, popC, scanC, scanC0, cu,
    Currency.skip, Currency.const, Currency.aget, Currency.aset, Currency.ite,
    Currency.«while», Currency.add]

@[simp] theorem bfsQTotal_aget (n ns : ℕ) :
    (bfsQTotal n ns).toFun Currency.aget = 4 * n + 3 * ns + 1 := by
  simp [bfsQTotal, bfsBudget, bfsK, iter, fillC, popC, scanC, scanC0, cu,
    Currency.skip, Currency.const, Currency.aget, Currency.aset, Currency.ite,
    Currency.«while», Currency.add]
  ring

@[simp] theorem bfsQTotal_aset (n ns : ℕ) :
    (bfsQTotal n ns).toFun Currency.aset = n + 2 * ns + 2 := by
  simp [bfsQTotal, bfsBudget, bfsK, iter, fillC, popC, scanC, scanC0, cu,
    Currency.skip, Currency.const, Currency.aget, Currency.aset, Currency.ite,
    Currency.«while», Currency.add]
  ring

@[simp] theorem bfsQTotal_ite (n ns : ℕ) :
    (bfsQTotal n ns).toFun Currency.ite = n + 2 * ns + 1 := by
  simp [bfsQTotal, bfsBudget, bfsK, iter, fillC, popC, scanC, scanC0, cu,
    Currency.skip, Currency.const, Currency.aget, Currency.aset, Currency.ite,
    Currency.«while», Currency.add]
  ring

@[simp] theorem bfsQTotal_while (n ns : ℕ) :
    (bfsQTotal n ns).toFun Currency.«while» = 3 * n + ns + 2 := by
  simp [bfsQTotal, bfsBudget, bfsK, iter, fillC, popC, scanC, scanC0, cu,
    Currency.skip, Currency.const, Currency.aget, Currency.aset, Currency.ite,
    Currency.«while», Currency.add]
  ring

@[simp] theorem bfsQTotal_add (n ns : ℕ) :
    (bfsQTotal n ns).toFun Currency.add = 4 * n + 2 * ns + 1 := by
  simp [bfsQTotal, bfsBudget, bfsK, iter, fillC, popC, scanC, scanC0, cu,
    Currency.skip, Currency.const, Currency.aget, Currency.aset, Currency.ite,
    Currency.«while», Currency.add]
  ring

theorem bfsQTotal_other (n ns : ℕ) {c : String}
    (hskip : c ≠ Currency.skip) (hconst : c ≠ Currency.const)
    (haget : c ≠ Currency.aget) (haset : c ≠ Currency.aset)
    (hite : c ≠ Currency.ite) (hwhile : c ≠ Currency.«while»)
    (hadd : c ≠ Currency.add) :
    (bfsQTotal n ns).toFun c = 0 := by
  simp [bfsQTotal, bfsBudget, bfsK, iter, fillC, popC, scanC, scanC0, cu,
    ACost.toFun_cost_ne, hskip, hconst, haget, haset, hite, hwhile, hadd]

/-- **P7's export.** The queue-based masked depth-capped search delivers
an array deciding every masked-distance threshold up to the cap, for
`n` fill iterations, `n` pops, `ns` scanned slots and a constant. -/
theorem bfsQ_correct {src : ℕ} {dist₀ q₀ : List ℕ} (hc : Csr n ns G off tgt alv)
    (hsrc : src < n) (hdlen : dist₀.length = n) (hqlen : q₀.length = n) :
    bfsQ n d src off tgt alv dist₀ q₀
      ≤ NRest.spec (QPost n d src G alv hsrc) (fun _ => liftACost (bfsBudget n ns)) := by
  have halv : src < alv.length := by rw [hc.shape.2.1]; exact hsrc
  -- the seed and the drain, from a filled distance array
  have htail : ∀ p : List ℕ × ℕ, (p.1.length = n ∧ ∀ j, j < n → p.1[j]! = d + 1) →
      (NRest.bindT (mopAset p.1 src 0) fun D => NRest.bindT (mopAset q₀ 0 src) fun Q =>
        NRest.bindT (mopAget alv src) fun a =>
          NRest.bindT (irIf (decide (0 < a)) (mopConstN 1) (mopConstN 0)) fun tl =>
            NRest.bindT (pack4 D Q 0 tl) fun st =>
              NRest.bindT (drainLoop n d (d + 1) off tgt alv st) fun st' => NRest.returnT st'.1)
        ≤ NRest.spec (QPost n d src G alv hsrc)
            (fun _ => liftACost (n • iter popC + ns • iter scanC
              + (cu Currency.aset + cu Currency.aset + cu Currency.aget + cu Currency.ite
                + cu Currency.const + cu Currency.skip + cu Currency.skip + cu Currency.skip
                + cu Currency.«while»))) := by
    rintro p ⟨hplen, hpfill⟩
    have hseed := Fr.seed (n := n) (d := d) (G := G) (alv := alv) (s := ⟨src, hsrc⟩)
      hplen hqlen hpfill
    have hrow0 : rowSum off (q₀.set 0 src) 0 = 0 := by simp [rowSum]
    have hdrain := drainLoop_le (d := d) (s := ⟨src, hsrc⟩) hc n
      (p.1.set src 0, q₀.set 0 src, 0, if 0 < alv[src]! then 1 else 0) hseed (by simp)
    rw [hrow0, Nat.sub_zero, Nat.sub_zero] at hdrain
    have hpost : ∀ z' : St, (Fr n d G alv ⟨src, hsrc⟩ z'.1 z'.2.1 z'.2.2.1 z'.2.2.2 ∧
        z'.2.2.2 ≤ z'.2.2.1) → NRest.returnT z'.1
          ≤ NRest.spec (QPost n d src G alv hsrc) (fun _ => (0 : ECost)) := by
      rintro z' ⟨hfr, hle⟩
      rw [le_antisymm hfr.hdle hle] at hfr
      rw [← NRest.consume_zero (NRest.returnT z'.1)]
      exact consume_returnT_le_spec ⟨hfr.dlen, fun v k hk => hfr.dist_le_iff v hk⟩ le_rfl
    have hstep : ∀ tl : ℕ, tl = (if 0 < alv[src]! then 1 else 0) →
        (NRest.bindT (pack4 (p.1.set src 0) (q₀.set 0 src) 0 tl) fun st =>
          NRest.bindT (drainLoop n d (d + 1) off tgt alv st) fun st' => NRest.returnT st'.1)
          ≤ NRest.spec (QPost n d src G alv hsrc)
              (fun _ => (irUnit Currency.skip + irUnit Currency.skip + irUnit Currency.skip)
                + (liftACost (E2 (iter popC) (iter scanC) n ns + cu Currency.«while») + 0)) := by
      rintro tl rfl
      simp only [pack4, mopPair_def, bindT_unitT, NRest.consume_consume]
      refine le_trans (NRest.consume_mono (le_trans (NRest.bindT_mono hdrain fun _ => le_rfl)
        (bindT_spec_le _ _ _ _ _ hpost)) le_rfl) (le_of_eq ?_)
      rw [consume_spec]
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
    rw [consume_spec, consume_spec]
    refine congrArg (NRest.spec _) (funext fun _ => ?_)
    simp only [E2, iter, liftACost_add, liftACost_nsmul, liftACost_cu, add_zero]
    ac_rfl
  simp only [bfsQ, mopBinop_def, mopConstN_def, Imp.Bop.apply_add, binopCurrency_add,
    bindT_unitT]
  refine le_trans (NRest.consume_mono (NRest.consume_mono
    (le_trans (NRest.bindT_mono (fillLoop_le n (d + 1) n dist₀ 0 hdlen (by omega)
      (fun j hj => absurd hj (by omega))) fun _ => le_rfl)
      (bindT_spec_le _ _ _ _ _ htail)) le_rfl) le_rfl) (le_of_eq ?_)
  rw [consume_spec, consume_spec]
  refine congrArg (NRest.spec _) (funext fun _ => ?_)
  simp only [bfsBudget, bfsK, iter, liftACost_add, liftACost_nsmul, liftACost_cu, Nat.sub_zero]
  ac_rfl

/-! ## 7. The variants the synthesis will need (P7/D-b)

`sepref_synth`'s loop rule takes the termination measure as an
annotation (`LOOP_VARIANT`, P4/D-cv). Each is the measure the
corresponding fuel induction above already runs on, and each rests on
the body's *value*, which the body bounds pin: a one-result upper bound
makes every possible outcome that one result. -/

/-- Any outcome of a body bounded by "return the step" is that step. -/
theorem res_of_le {α : Type} {m : NRest α ECost} {x s' : α} {c : ECost}
    (hm : m ≤ NRest.consume (NRest.returnT x) c)
    (hle : (NRest.returnT s' : NRest α ECost) ≤ m) : s' = x := by
  by_contra hne
  rw [NRest.consume_returnT] at hm
  have h := le_trans hle hm
  rw [returnT_le_rest_iff, NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at h
  exact WithBot.coe_ne_bot h

theorem fill_variant (n sent : ℕ) :
    LOOP_VARIANT (fun s => fillBf n s = true → fillP n s) (fillBf n) (fillF sent)
      (fun s => n - s.2) := by
  intro s s' hI hb hle
  have hlt : s.2 < n := by simpa [fillBf] using hb
  have hlen : s.1.length = n := hI hb
  rw [res_of_le (fillF_le sent s (by omega)) hle]
  show n - (s.2 + 1) < n - s.2
  omega

theorem scan_variant (n sent dv1 kend : ℕ) (off tgt alv : List ℕ) :
    LOOP_VARIANT (fun s => scanBf kend s = true → scanP n sent kend off tgt alv s)
      (scanBf kend) (scanF sent dv1 tgt alv) (fun s => kend - s.2.2.2) := by
  intro s s' hI hb hle
  obtain ⟨h1, h2, h3, h4⟩ := scanP_bounds (hI hb) hb
  rw [res_of_le (scanF_le sent dv1 tgt alv s h1 h2 h3 h4) hle]
  have hk : s.2.2.2 < kend := by simpa [scanBf] using hb
  have : (scanStep tgt alv sent dv1 s).2.2.2 = s.2.2.2 + 1 := by
    simp only [scanStep]; split_ifs <;> rfl
  show kend - (scanStep tgt alv sent dv1 s).2.2.2 < kend - s.2.2.2
  rw [this]
  omega

/-- The row scan keeps the *list-level* invariant on its own — no graph
in sight — which is what lets the drain's variant be stated at the
program's own guarded assertion. -/
theorem scanP_step {sent dv1 kend : ℕ} {z : St} (hne : dv1 ≠ sent)
    (hP : scanP n sent kend off tgt alv z) (hb : scanBf kend z = true) :
    scanP n sent kend off tgt alv (scanStep tgt alv sent dv1 z) := by
  obtain ⟨hsh, hD, hQ, hkt, hroom⟩ := hP
  obtain ⟨h1, h2, h3, h4⟩ := scanP_bounds ⟨hsh, hD, hQ, hkt, hroom⟩ hb
  simp only [room] at hroom
  by_cases ha : 0 < alv[tgt[z.2.2.2]!]!
  · by_cases hu : z.1[tgt[z.2.2.2]!]! = sent
    · have hun : tgt[z.2.2.2]! < n := by rw [← hD]; exact h3
      have hmemw : tgt[z.2.2.2]! ∈ undisc n sent alv z.1 := by
        simp only [undisc, Finset.mem_filter, Finset.mem_range]; exact ⟨hun, ha, hu⟩
      have hcp := Finset.card_pos.mpr ⟨_, hmemw⟩
      have hD' : ∀ j, (z.1.set tgt[z.2.2.2]! dv1)[j]!
          = if j = tgt[z.2.2.2]! then dv1 else z.1[j]! := fun j => get!_set _ _ _ j h3
      have hund : undisc n sent alv (z.1.set tgt[z.2.2.2]! dv1)
          = (undisc n sent alv z.1).erase tgt[z.2.2.2]! := by
        ext y
        simp only [undisc, Finset.mem_erase, Finset.mem_filter, Finset.mem_range, hD']
        by_cases hy : y = tgt[z.2.2.2]!
        · subst hy
          simp only [if_true]
          exact ⟨fun hcc => absurd hcc.2.2 hne, fun hcc => absurd rfl hcc.1⟩
        · simp only [if_neg hy]; exact ⟨fun hcc => ⟨hy, hcc⟩, fun hcc => hcc.2⟩
      rw [show scanStep tgt alv sent dv1 z = (z.1.set tgt[z.2.2.2]! dv1,
          z.2.1.set z.2.2.1 tgt[z.2.2.2]!, z.2.2.1 + 1, z.2.2.2 + 1) by
        simp only [scanStep, if_pos ha, if_pos hu]]
      refine ⟨hsh, by simpa using hD, by simpa using hQ, hkt, ?_⟩
      show z.2.2.1 + 1 + (undisc n sent alv (z.1.set tgt[z.2.2.2]! dv1)).card ≤ n
      rw [hund, Finset.card_erase_of_mem hmemw]
      omega
    · rw [show scanStep tgt alv sent dv1 z = (z.1, z.2.1, z.2.2.1, z.2.2.2 + 1) by
        simp only [scanStep, if_pos ha, if_neg hu]]
      exact ⟨hsh, hD, hQ, hkt, hroom⟩
  · rw [show scanStep tgt alv sent dv1 z = (z.1, z.2.1, z.2.2.1, z.2.2.2 + 1) by
      simp only [scanStep, if_neg ha]]
    exact ⟨hsh, hD, hQ, hkt, hroom⟩

/-- The drain's body never fails under the program's own assertion, and
every outcome has advanced the head by one — which is the whole content
of the drain's variant. -/
theorem popF_hd {z : St} (hP : popP n (d + 1) off tgt alv z) (hb : popBf z = true) :
    popF n d (d + 1) off tgt alv z
      ≤ NRest.spec (fun t' : St => t'.2.2.1 = z.2.2.1 + 1) (fun _ => (⊤ : ECost)) := by
  obtain ⟨hsh, hDl, hQl, hqlt, hroom⟩ := hP
  have hht : z.2.2.1 < z.2.2.2 := by simpa [popBf] using hb
  have hroomN : z.2.2.2 + (undisc n (d + 1) alv z.1).card ≤ n := hroom
  have hqh : z.2.2.1 < z.2.1.length := by omega
  have hvn : z.2.1[z.2.2.1]! < n := hqlt _ hht
  have hvd : z.2.1[z.2.2.1]! < z.1.length := by omega
  have hoff1 : z.2.1[z.2.2.1]! + 1 < off.length := by rw [hsh.1]; omega
  have hoff0 : z.2.1[z.2.2.1]! < off.length := by omega
  have hK : ∀ y : St, (scanP n (d + 1) off[z.2.1[z.2.2.1]! + 1]! off tgt alv y ∧
        off[z.2.1[z.2.2.1]! + 1]! ≤ y.2.2.2) →
      NRest.bindT (pack3 y.1 y.2.1 y.2.2.1) (fun r => pack4 r.1 r.2.1 (z.2.2.1 + 1) r.2.2)
        ≤ NRest.spec (fun t' : St => t'.2.2.1 = z.2.2.1 + 1) (fun _ => (⊤ : ECost)) := by
    intro y _
    simp only [pack3, pack4, mopPair_def, bindT_unitT, NRest.consume_consume]
    exact consume_returnT_le_spec rfl le_top
  simp only [popF, mopAget_def, NRest.assert_pos hqh, NRest.assert_pos hvd,
    NRest.returnT_bindT, mopBinop_def, Imp.Bop.apply_add, binopCurrency_add,
    irIf_def, NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume]
  by_cases hcap : z.1[z.2.1[z.2.2.1]!]! < d
  · rw [if_pos (by simp only [decide_eq_true_eq]; exact hcap)]
    simp only [NRest.assert_pos hoff0, NRest.assert_pos hoff1, NRest.returnT_bindT,
      NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
      NRest.bindT_assoc_acost, pack4_bindT]
    have hscan := scanLoop_le (Inv := scanP n (d + 1) off[z.2.1[z.2.2.1]! + 1]! off tgt alv)
      n (d + 1) (z.1[z.2.1[z.2.2.1]!]! + 1) off[z.2.1[z.2.2.1]! + 1]! off tgt alv
      (fun y hy hyb => ⟨hy, scanP_step (by omega) hy hyb⟩)
      (off[z.2.1[z.2.2.1]! + 1]! - off[z.2.1[z.2.2.1]!]!)
      (z.1, z.2.1, z.2.2.2, off[z.2.1[z.2.2.1]!]!)
      ⟨hsh, hDl, hQl, hsh.row_le hvn, hroom⟩ (by simp)
    refine le_trans (NRest.consume_mono
      (le_trans (NRest.bindT_mono hscan fun _ => le_rfl) (bindT_spec_le _ _ _ _ _ hK)) le_rfl)
      ?_
    rw [consume_spec]
    exact spec_mono (fun _ hx => hx) fun _ _ => le_top
  · rw [if_neg (by simp only [decide_eq_true_eq]; exact hcap)]
    simp only [pack3, pack4, mopPair_def, bindT_unitT, NRest.consume_consume]
    exact consume_returnT_le_spec rfl le_top

theorem drain_variant (n d : ℕ) (off tgt alv : List ℕ) :
    LOOP_VARIANT (fun s => popBf s = true → popP n (d + 1) off tgt alv s) popBf
      (popF n d (d + 1) off tgt alv) (fun s => n - s.2.2.1) := by
  intro z s' hI hb hle
  have hP := hI hb
  have hht : z.2.2.1 < z.2.2.2 := by simpa [popBf] using hb
  have hroom := hP.2.2.2.2
  simp only [room] at hroom
  have h := le_trans hle (popF_hd hP hb)
  rw [NRest.spec, returnT_le_rest_iff] at h
  have hs' : s'.2.2.1 = z.2.2.1 + 1 := by
    by_contra hne
    rw [if_neg hne, le_bot_iff, ← WithBot.coe_zero] at h
    exact WithBot.coe_ne_bot h
  show n - s'.2.2.1 < n - z.2.2.1
  omega

/-! ## 8. The reached list (R2D/D-c)

`bfsQ_correct` specifies the *distance array* and says nothing about
the queue. A consumer that wants to scan the vertices the search
actually reached — rather than test `D[z] ≤ d` at all `n` of them —
needs one more clause: the first `max tl 1` slots of the queue list
exactly the vertices the search put within the cap, each once.

It is `Fr` at drain exit, read three times over, plus one graph fact:
a masked walk ends at a *live* vertex unless it is trivial. The
`max tl 1` is the dead-source case: the seed writes `q[0] := src`
before the drain starts, the drain never runs, and the single slot is
right. -/

section Reached

variable {D Q : List ℕ} {hd tl : ℕ}

/-- **A masked walk ends alive unless it is trivial.** Every edge of
`masked G M` has two live ends, so the last one gives the endpoint's
mask bit; a walk with no edges gives the source back. -/
theorem wd_alive_or_eq {M : Fin n → Bool} :
    ∀ (k : ℕ) (w : Fin n), Bfs.WD G M k s w → s = w ∨ M w = true := by
  intro k
  induction k with
  | zero => intro w hw; exact Or.inl hw.eq_of_zero
  | succ k ih =>
    intro w hw
    rcases hw.tail with hshort | ⟨c, -, hcw⟩
    · exact ih w hshort
    · exact Or.inr (Bfs.masked_adj.mp hcw).2.2

/-- **The glue.** A vertex the search put within the cap is alive, or
it is the source. -/
theorem Fr.alive_or_src (h : Fr n d G alv s D Q hd tl) (w : Fin n)
    (hw : D[(w : ℕ)]! ≤ d) : 0 < alv[(w : ℕ)]! ∨ w = s := by
  rcases wd_alive_or_eq (G := G) (s := s) _ w (h.sound w hw) with heq | hal
  · exact Or.inr heq.symm
  · exact Or.inl (maskOf_iff.mp hal)

/-- **The clause the cover pass asks for**, at the list layer: the
first `max tl 1` slots of the queue name vertices, name them once, and
name exactly the vertices the distance array puts within the cap. -/
def QReached (n d : ℕ) (D Q : List ℕ) (tl : ℕ) : Prop :=
  (∀ k < max tl 1, Q[k]! < n) ∧
    (∀ k < max tl 1, ∀ k' < max tl 1, Q[k]! = Q[k']! → k = k') ∧
    (∀ w < n, D[w]! ≤ d ↔ ∃ k < max tl 1, Q[k]! = w)

/-- **A dead source reaches nothing, and its queue is empty.** If the
source's mask bit is clear then no live vertex can be on the queue —
the queue's own soundness would make it the source. -/
theorem Fr.tl_eq_zero_of_dead (h : Fr n d G alv s D Q tl tl)
    (hdead : ¬ 0 < alv[(s : ℕ)]!) : tl = 0 := by
  by_contra hne
  have h0 : (0 : ℕ) < tl := by omega
  obtain ⟨hd0, hal0⟩ := h.qmem 0 h0
  have hq0n : Q[0]! < n := h.qlt 0 h0
  have hsq : s = (⟨Q[0]!, hq0n⟩ : Fin n) :=
    (Bfs.WD.of_dead (G := G) (M := maskOf n alv) (s := s)
      (by simpa [maskOf] using hdead)).mp (h.sound ⟨Q[0]!, hq0n⟩ hd0)
  rw [show (s : ℕ) = Q[0]! from congrArg Fin.val hsq] at hdead
  exact hdead hal0

/-- **The reached list, off the queue invariant at drain exit.** The
one thing `Fr` does not know is the seed's `q[0] := src`, which is
what the dead-source branch runs on. -/
theorem Fr.qReached (h : Fr n d G alv s D Q tl tl) (hq0 : Q[0]! = (s : ℕ)) :
    QReached n d D Q tl := by
  by_cases hal : 0 < alv[(s : ℕ)]!
  · -- the source is alive, so it is on the queue and `max tl 1 = tl`
    obtain ⟨i, hi, -⟩ := h.qall (s : ℕ) s.isLt hal (by rw [h.src0]; omega)
    have htl : max tl 1 = tl := by omega
    simp only [QReached, htl]
    refine ⟨h.qlt, h.qinj, fun w hw => ⟨fun hd => ?_, fun ⟨k, hk, hkw⟩ => ?_⟩⟩
    · have halw : 0 < alv[w]! := by
        rcases h.alive_or_src ⟨w, hw⟩ hd with hx | hx
        · exact hx
        · rw [show w = (s : ℕ) from congrArg Fin.val hx]; exact hal
      exact h.qall w hw halw hd
    · rw [← hkw]; exact (h.qmem k hk).1
  · -- the source is dead: the queue never grew, and slot `0` is the seed
    have htl0 : tl = 0 := h.tl_eq_zero_of_dead hal
    subst htl0
    have hmax : max (0 : ℕ) 1 = 1 := by omega
    simp only [QReached, hmax]
    refine ⟨fun k hk => ?_, fun k hk k' hk' _ => by omega, fun w hw => ⟨fun hd => ?_, ?_⟩⟩
    · rw [show k = 0 by omega, hq0]; exact s.isLt
    · have hsw : s = (⟨w, hw⟩ : Fin n) :=
        (Bfs.WD.of_dead (G := G) (M := maskOf n alv) (s := s)
          (by simpa [maskOf] using hal)).mp (h.sound ⟨w, hw⟩ hd)
      exact ⟨0, by omega, by rw [hq0, show (s : ℕ) = w from congrArg Fin.val hsw]⟩
    · rintro ⟨k, hk, hkw⟩
      rw [show k = 0 by omega, hq0] at hkw
      rw [← hkw, h.src0]
      omega

/-- **The drain, with the seed's slot `0` carried through.** A pop
never writes below its own head, and the head never passes `0`; the
`popF_le` clause that says so is what this induction reads. Otherwise
this is `drainLoop_le`, with one conjunct added to the postcondition. -/
theorem drainLoop_le' (hc : Csr n ns G off tgt alv) (q0 : ℕ) :
    ∀ (fuel : ℕ) (z : St), Fr n d G alv s z.1 z.2.1 z.2.2.1 z.2.2.2 → z.2.1[0]! = q0 →
      n - z.2.2.1 ≤ fuel →
      drainLoop n d (d + 1) off tgt alv z
        ≤ NRest.spec
            (fun z' : St => (Fr n d G alv s z'.1 z'.2.1 z'.2.2.1 z'.2.2.2 ∧
                z'.2.2.2 ≤ z'.2.2.1) ∧ z'.2.1[0]! = q0)
            (fun _ => liftACost (E2 (iter popC) (iter scanC) (n - z.2.2.1)
              (ns - rowSum off z.2.1 z.2.2.1) + cu Currency.«while»)) := by
  have exit : ∀ z : St, Fr n d G alv s z.1 z.2.1 z.2.2.1 z.2.2.2 → z.2.1[0]! = q0 →
      z.2.2.2 ≤ z.2.2.1 →
      drainLoop n d (d + 1) off tgt alv z
        ≤ NRest.spec
            (fun z' : St => (Fr n d G alv s z'.1 z'.2.1 z'.2.2.1 z'.2.2.2 ∧
                z'.2.2.2 ≤ z'.2.2.1) ∧ z'.2.1[0]! = q0)
            (fun _ => liftACost (E2 (iter popC) (iter scanC) (n - z.2.2.1)
              (ns - rowSum off z.2.1 z.2.2.1) + cu Currency.«while»)) := by
    intro z hz hq hle
    have hb : popBf z = false := by simp only [popBf, decide_eq_false_iff_not]; omega
    simp only [drainLoop, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨⟨hz, hle⟩, hq⟩ ?_
    rw [liftACost_add, liftACost_cu, add_comm]
    exact cost_le_add _ _
  intro fuel
  induction fuel with
  | zero => intro z hz hq hf; exact exit z hz hq (by have := hz.hdle; have := hz.tl_le; omega)
  | succ fuel ih =>
    intro z hz hq hf
    by_cases hb : z.2.2.1 < z.2.2.2
    · have hbt : popBf z = true := by simp [popBf, hb]
      have hIs : popBf z = true → popP n (d + 1) off tgt alv z :=
        fun _ => ⟨hc.shape, hz.dlen, hz.qlen, hz.qlt, hz.room⟩
      have hS' : rowSum off z.2.1 (z.2.2.1 + 1)
          = rowSum off z.2.1 z.2.2.1 + rowLen off z.2.1[z.2.2.1]! := Finset.sum_range_succ _ _
      have hSle : rowSum off z.2.1 (z.2.2.1 + 1) ≤ ns := by
        rw [rowSum]; exact hc.rowSum_le (tl := z.2.2.2) hz.qlt hz.qinj (by omega)
      have hzn : z.2.2.1 < n := lt_of_lt_of_le hb hz.tl_le
      have hcont : ∀ z' : St, (Fr n d G alv s z'.1 z'.2.1 z'.2.2.1 z'.2.2.2 ∧
            z'.2.2.1 = z.2.2.1 + 1 ∧ ∀ i, i < z.2.2.1 + 1 → z'.2.1[i]! = z.2.1[i]!) →
          drainLoop n d (d + 1) off tgt alv z'
            ≤ NRest.spec
                (fun z'' : St => (Fr n d G alv s z''.1 z''.2.1 z''.2.2.1 z''.2.2.2 ∧
                  z''.2.2.2 ≤ z''.2.2.1) ∧ z''.2.1[0]! = q0)
                (fun _ => liftACost (E2 (iter popC) (iter scanC) (n - (z.2.2.1 + 1))
                  (ns - rowSum off z.2.1 (z.2.2.1 + 1)) + cu Currency.«while»)) := by
        rintro z' ⟨hfr', hhd', hq'⟩
        refine le_trans (ih z' hfr' (by rw [hq' 0 (by omega)]; exact hq) (by omega))
          (spec_mono (fun _ hx => hx) fun _ _ => le_of_eq ?_)
        have hrs : rowSum off z'.2.1 (z.2.2.1 + 1) = rowSum off z.2.1 (z.2.2.1 + 1) := by
          rw [rowSum, rowSum]
          exact Finset.sum_congr rfl fun i hi => by
            rw [hq' i (by have := Finset.mem_range.mp hi; omega)]
        rw [hhd', hrs]
      have hcost : irUnit Currency.«while»
          + (liftACost (popC + rowLen off z.2.1[z.2.2.1]! • iter scanC)
            + liftACost (E2 (iter popC) (iter scanC) (n - (z.2.2.1 + 1))
                (ns - rowSum off z.2.1 (z.2.2.1 + 1)) + cu Currency.«while»))
          = liftACost (E2 (iter popC) (iter scanC) (n - z.2.2.1)
              (ns - rowSum off z.2.1 z.2.2.1) + cu Currency.«while») := by
        rw [show n - z.2.2.1 = (n - (z.2.2.1 + 1)) + 1 by omega,
          show ns - rowSum off z.2.1 z.2.2.1
            = (ns - rowSum off z.2.1 (z.2.2.1 + 1)) + rowLen off z.2.1[z.2.2.1]! by omega,
          E2_split]
        simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
        ac_rfl
      calc drainLoop n d (d + 1) off tgt alv z
            = NRest.consume (NRest.bindT (popF n d (d + 1) off tgt alv z)
                fun z' => drainLoop n d (d + 1) off tgt alv z') (irUnit Currency.«while») := by
              simp only [drainLoop]; rw [irWhileIT_of_true hIs hbt]
          _ ≤ NRest.consume (NRest.spec _ (fun _ => liftACost (popC + rowLen off z.2.1[z.2.2.1]! •
                iter scanC) + liftACost (E2 (iter popC) (iter scanC) (n - (z.2.2.1 + 1))
                  (ns - rowSum off z.2.1 (z.2.2.1 + 1)) + cu Currency.«while»)))
                (irUnit Currency.«while») :=
              NRest.consume_mono (le_trans (NRest.bindT_mono (popF_le hc hz hbt) fun _ => le_rfl)
                (bindT_spec_le _ _ _ _ _ hcont)) le_rfl
          _ = _ := by rw [consume_spec, ← hcost]
    · exact exit z hz hq (by omega)

end Reached

/-! ## 9. Axioms -/

/-- info: 'Lax13Proofs.Refine.BfsQ.bfsQTotal_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bfsQTotal_normal

/-- info: 'Lax13Proofs.Refine.BfsQ.bfsQ_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bfsQ_correct

/-- info: 'Lax13Proofs.Refine.BfsQ.drain_variant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms drain_variant

/-- info: 'Lax13Proofs.Refine.BfsQ.scan_variant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scan_variant

/-- info: 'Lax13Proofs.Refine.BfsQ.fill_variant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fill_variant

/-! ## 9. Telemetry (the plan's P7 gate numbers, wave A's share)

* **Raw `wc -l`: 1,435** for this file — the counting rule of the P7
  design note, comments included. A nesting-aware scan classifies 108
  lines as blank and 312 as comment, leaving **1,015 lines of Lean**.
  The gate is 400 for the whole of P7 against `RamBfs.lean`'s 1,201, so
  **wave A alone misses it**, and by a factor of about three; P8 records
  the verdict with the breakdown below.

* **Where the lines go** (Lean lines per section, measured):
  §1 the twin and the demo, 39; §2 the program — three bodies, three
  loops, two tuple operations, four assertions and `bfsQ` — 67;
  §3 the cost constants, the three body bounds and the two counted
  loops' fuel inductions, 188; §4 the queue invariant with `relax`,
  `complete`, `pop`, `popSkip`, `seed`, the scan invariant and the
  tiling, **340**; §5 the drain, 162; §6 the export, 82; §7 the three
  variants, 121; §8 axioms, 8. The queue invariant is a third of the
  file and it is the part a *tower* cannot shrink: it is the fourteen
  clauses `RamBfs.Frontier` carries, for the same reasons.

* **What was reused from `Refine/Examples/Bfs.lean`** (P1's acceptance
  artifact, 1,051 lines, reported separately per the design note):
  `masked` and `masked_adj`; `WD` with `WD.refl`, `WD.mono`, `WD.step`,
  `WD.eq_of_zero` and `WD.tail` — the whole graph-theoretic core of the
  exit argument; and `wfR2_zero`/`wfR2_add`/`progress_consume` were
  *not* needed, because P7/D-b's route does not go through the VCG's
  loop rule. Nothing else. The level-based `Inv`, `NextLevel`,
  `inv_step` and the potential argument were **not** reusable: they are
  about a frontier list, not a queue (P7/D-a).

* **What was added to the tower** (`Sepref/IrLoop.lean`, 188 raw / 100
  Lean lines, excluded from the count as library):
  `irWhileIT_eq_whileIET` (P7/T-a, the translator-to-VCG bridge),
  `bindT_consume_right`, `bindT_unitT`, `cost_le_add`,
  `consume_returnT_le_spec`, `consume_spec`, `spec_mono`,
  `bindT_spec_le`, and the two-currency energy algebra `E2`/`E2_sub`/
  `E2_mono`/`E2_split`/`liftACost_nsmul`/`wfR2_nsmul` (P7/T-b). All are
  program-independent; `E2_sub`, `E2_mono` and `wfR2_nsmul` are what a
  `While`-rule route would consume and are unused here.

* **Hand-written frame clauses: 0.** No separation-logic connective
  appears in this file at all — wave A is entirely at the `NRest` layer.
  The `ac_rfl`s are on **cost sums** (`ECost`, an `AddCommMonoid`),
  never on `∗`.

* **Axioms.** `#print axioms` is pinned in §8 for `bfsQ_correct` and the
  three variants: `[propext, Classical.choice, Quot.sound]` and nothing
  else.

* **Refuted before proved.** §1 runs a computable twin of the very step
  functions §3 proves the abstract bodies equal to, on `RamBfs`'s own
  five-vertex arena, against the baseline's four published readings, and
  against P1's independent level-based twin on four more; one negative
  control is pinned as an error. Nothing was refuted — but three
  assumptions were corrected *before* any proof, by the shape of the
  program rather than by a failed guard: the relaxation test needs
  `qcap` (P7/D-c), the queue write needs `room` (P7/D-d), and the
  assertion must be guard-shaped or the VCG cannot see the loop
  (P7/D-e).

* **Backlog for wave B.** (i) The `else` arms of the row scan write no
  array, so the tool's `MERGE` sees `hnCtxt`-for-`hnCtxt` on the state
  but nothing to reconcile for `dist`/`q`; if that stalls, the arms need
  a write-back `aset`, which is a cost-only change here. (ii) The
  projection at the end of a row drops the scan index; wave B junks the
  cell (`hnRefine_cons_res`, P4/D-ec). (iii) `bfsQ`'s two scratch arrays
  are parameters, so the export's precondition is `bfs_spec`'s
  `∃ g, arrs "dist" = arrOf n g` verbatim. -/

end BfsQ

end Lax13Proofs.Refine
