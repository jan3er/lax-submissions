import Lax3Proofs.Refine.CoverSynth

/-!
# P2 wave F1 — the reached list, supplied (debt R2D/D-c)

`CoverSynth` §8 states `ReachedList` and takes it as a hypothesis
everywhere it is used: the tower's BFS export specified the *distance
array* and said nothing about the queue, and reading the reached list
off `q` needs exactly that missing clause.

The clause is now proved, in the BFS where it belongs
(`Lax13Proofs.Refine.BfsQ`'s `Fr.qReached`, off the queue invariant at
drain exit) and exported through the gate program
(`BfsQSynth.bfsQS_reached`). This file is the two-line bridge: the
tower's `QReached` *is* `CoverSynth.ReachedList`, and the search
program's own bound supplies it.

## What the proof turned on

Three of the clauses are `Fr` fields read at `hd = tl`: `qlt` is
"every slot names a vertex", `qinj` is "each once", and `qmem`/`qall`
are the two directions of "the queue is the fibre". `qall` needs its
vertex *alive*, and the distance array alone does not say so — the
glue is `BfsQ.Fr.alive_or_src`: a vertex within the cap is alive or is
the source, because a masked walk ends at a live vertex unless it is
trivial (`BfsQ.wd_alive_or_eq`).

The `max tl 1` is the dead-centre branch. A dead source has an *empty*
queue — `BfsQ.Fr.tl_eq_zero_of_dead`, since a live vertex on the queue
would have to be the source by `Bfs.WD.of_dead` — and its one reached
vertex is itself, sitting in the `q[0] := src` slot the seed writes
before the drain starts. Carrying that slot through the drain is
`BfsQ.drainLoop_le'`, `drainLoop_le` with the `popF_le` clause "a pop
never writes below its own head" read at index `0`.
-/

namespace Lax3Proofs.Refine.ReachedBridge

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax13Proofs.Refine.BfsQ (St QPost QReached Csr bfsBudget)

/-! ## 0. Refute before prove

`ReachedList` is an authored claim about a program's queue, and so is
the glue "a vertex within the cap is alive or is the source". Both are
read off `BfsQ`'s computable twin — the one already checked against
`RamBfs`'s four published readings and against P1's independent
level-based twin — before either is proved. -/

section Refute

open Lax13Proofs.Refine.BfsQ (drainTw demoOff demoTgt demoAlv)

/-- The twin's whole state, queue included: `BfsQ.bfsTw` without its
final projection. -/
def stTw (n d src : ℕ) (off tgt alv : List ℕ) : St :=
  drainTw off tgt alv d n
    ((List.replicate n (d + 1)).set src 0, (List.replicate n 0).set 0 src, 0,
      if 0 < alv[src]! then 1 else 0)

/-- `ReachedList`'s three clauses, decided at a run. -/
def reachedCheck (n d : ℕ) (st : St) : Bool :=
  let m := max st.2.2.2 1
  ((List.range m).all fun k => decide (st.2.1[k]! < n)) &&
    ((List.range m).all fun k => (List.range m).all fun k' =>
      decide (st.2.1[k]! = st.2.1[k']!) == decide (k = k')) &&
    ((List.range n).all fun w =>
      decide (st.1[w]! ≤ d) == ((List.range m).any fun k => decide (st.2.1[k]! = w)))

/-- The same three clauses over the *bare* `tl` slots — the reading
without the dead-centre repair. -/
def reachedCheckTl (n d : ℕ) (st : St) : Bool :=
  let m := st.2.2.2
  ((List.range m).all fun k => decide (st.2.1[k]! < n)) &&
    ((List.range m).all fun k => (List.range m).all fun k' =>
      decide (st.2.1[k]! = st.2.1[k']!) == decide (k = k')) &&
    ((List.range n).all fun w =>
      decide (st.1[w]! ≤ d) == ((List.range m).any fun k => decide (st.2.1[k]! = w)))

-- **The claim, read off the twin** at the four settings `BfsQ`'s own
-- `#guard`s use, plus the dead-centre run the cover pass needs.
#guard reachedCheck 5 3 (stTw 5 3 0 demoOff demoTgt (demoAlv 1))
#guard reachedCheck 5 3 (stTw 5 3 0 demoOff demoTgt (demoAlv 0))
#guard reachedCheck 5 1 (stTw 5 1 0 demoOff demoTgt (demoAlv 1))
#guard reachedCheck 5 3 (stTw 5 3 2 demoOff demoTgt (demoAlv 0))

-- **The dead centre, pinned.** Its queue never grows, and the seed's
-- slot `0` is the centre itself — which is why the reading is over
-- `max tl 1` slots and not `tl`.
#guard (stTw 5 3 2 demoOff demoTgt (demoAlv 0)).2.2.2 = 0
#guard (stTw 5 3 2 demoOff demoTgt (demoAlv 0)).2.1[0]! = 2

-- **The glue's edge case, pinned.** A masked-off vertex is *not* within
-- the cap: it keeps the sentinel, because no masked walk reaches it.
#guard (stTw 5 3 0 demoOff demoTgt (demoAlv 0)).1[2]! = 4
#guard ¬ ((stTw 5 3 0 demoOff demoTgt (demoAlv 0)).1[2]! ≤ 3)

/-! ### Negative controls -/

-- **(a) `max tl 1` is load-bearing.** The bare-`tl` reading agrees with
-- the repaired one on a live centre and is *false* on a dead one.
#guard reachedCheckTl 5 3 (stTw 5 3 0 demoOff demoTgt (demoAlv 1))
#guard ¬ reachedCheckTl 5 3 (stTw 5 3 2 demoOff demoTgt (demoAlv 0))

-- **(b) the check can tell.** A queue that listed the same vertex twice,
-- or missed one, is refuted by the same predicate.
#guard ¬ reachedCheck 5 3 ((stTw 5 3 0 demoOff demoTgt (demoAlv 1)).1,
  [0, 0, 2, 3, 4], 5, 5)
#guard ¬ reachedCheck 5 3 ((stTw 5 3 0 demoOff demoTgt (demoAlv 1)).1,
  [0, 1, 2, 3, 4], 3, 3)

end Refute

/-! ## 1. The two predicates are one -/

/-- **The bridge.** `BfsQ.QReached` and `CoverSynth.ReachedList` are the
same three clauses; neither package could state the other's name, which
is the whole of the gap R2D/D-c recorded. -/
theorem reachedList_of_qReached {n d : ℕ} {D reach : List ℕ} {tl : ℕ}
    (h : QReached n d D reach tl) : CoverSynth.ReachedList n d D reach tl := h

theorem qReached_of_reachedList {n d : ℕ} {D reach : List ℕ} {tl : ℕ}
    (h : CoverSynth.ReachedList n d D reach tl) : QReached n d D reach tl := h

/-! ## 2. The search supplies it

The gate program's own bound, with `CoverSynth`'s hypothesis in the
postcondition: the distance array as before, the queue's first
`max tl 1` slots enumerating the reached set, and the queue at its
length. -/

variable {n ns d : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}
  {src : ℕ} {dist₀ q₀ : List ℕ}

/-- **`ReachedList`, supplied by the search.** -/
theorem bfsQS_reachedList (hc : Csr n ns G off tgt alv) (hsrc : src < n)
    (hdlen : dist₀.length = n) (hqlen : q₀.length = n) :
    BfsQSynth.bfsQS n d src off tgt alv dist₀ q₀
      ≤ NRest.spec
          (fun st' : St => QPost n d src G alv hsrc st'.1 ∧
            CoverSynth.ReachedList n d st'.1 st'.2.1 st'.2.2.2 ∧ st'.2.1.length = n)
          (fun _ => irUnit Currency.skip + liftACost (bfsBudget n ns)) :=
  le_trans (BfsQSynth.bfsQS_reached hc hsrc hdlen hqlen)
    (spec_mono (fun _ h => ⟨h.1, reachedList_of_qReached h.2.1, h.2.2⟩) fun _ _ => le_rfl)

/-- **…and through the cover pass's own leaf.** `ScatterSynth.mopBfsAt`
is the search as one registered operation, with its two entry
conditions turned into `assert`s (R2D/D-b); this is the form the turn
loop of `CoverSynth` binds. -/
theorem mopBfsAt_reachedList {i₀ hd₀ : ℕ} (hc : Csr n ns G off tgt alv) (hsrc : src < n)
    (hi : i₀ = 0) (hh : hd₀ = 0) (hdlen : dist₀.length = n) (hqlen : q₀.length = n) :
    ScatterSynth.mopBfsAt n d src i₀ hd₀ off tgt alv dist₀ q₀
      ≤ NRest.spec
          (fun st' : St => QPost n d src G alv hsrc st'.1 ∧
            CoverSynth.ReachedList n d st'.1 st'.2.1 st'.2.2.2 ∧ st'.2.1.length = n)
          (fun _ => irUnit Currency.skip + liftACost (bfsBudget n ns)) := by
  rw [ScatterSynth.mopBfsAt_eq, NRest.assert_pos (show i₀ = 0 ∧ hd₀ = 0 from ⟨hi, hh⟩),
    NRest.returnT_bindT]
  exact bfsQS_reachedList hc hsrc hdlen hqlen

/-! ## 3. What this closes, and what it does not

**Closed.** `CoverSynth`'s `emitRun_block` and `emitRun_hasg` — and
every other consumer of `ReachedList` in that file — now have a
supplier. Nothing in `CoverSynth` changes: its exports keep their
hypothesis form, and the integration wave discharges it with
`mopBfsAt_reachedList` at the turn's own search call.

**Not closed.** The turn's *cost* assembly (`emitLoopCost` plus
`bfsBudget` through a `≤ NRest.spec` composition rather than an
equality) is the other named item of `CoverSynth` §8's "what is still
owed", and it is untouched here. -/

/-! ## 4. Axioms -/

/-- info: 'Lax3Proofs.Refine.ReachedBridge.bfsQS_reachedList' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms bfsQS_reachedList

/-- info: 'Lax3Proofs.Refine.ReachedBridge.mopBfsAt_reachedList' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms mopBfsAt_reachedList

end Lax3Proofs.Refine.ReachedBridge
