import Lax13Proofs.Refine.Examples.BfsQSynth
import Lax13Proofs.Refine.Iicf.IicfTrailArray

/-!
# The re-entrant queue BFS — a turn whose price is the touched set (wave B4b)

`Refine/Examples/BfsQSynth.lean` exports `bfsQ_spec`: the queue BFS,
synthesized, at `56·n + 40·ns + 33` IMP+ time units. Both linear terms
are *carrier-wide*: the fill loop zeroes all `n` slots of `dist`, and the
drain's budget charges `n` pops and `ns` scanned slots because that is
the only bound the queue invariant offers up front. Run once per cluster
turn, that is `#turns · Θ(n)` and the sublinear headline is gone
(memory `touched-only-costs.md`).

This file re-cashes the same search as a **turn**: one invocation from a
trail-clean store, whose price is a function of the *reached set* and the
adjacency slots it scans, and which hands the store back trail-clean so
the next turn may start. The carrier size does not occur in the turn's
cost — `turnCost` does not take `n` as an argument, which is
`Iicf/IicfTrailArray.lean`'s "note what it is a function of" and
`Examples/TrailRecursion.lean`'s `clusterCost` one level up.

## Finding 1 — the invocation protocol, and why no trail array is needed

The obvious route is to make `dist` an `Iicf/IicfTrailArray.lean` trail
array: writes go through `mop_tset` (write + push), and `mop_treset`
pops. It is not needed here, and the reason is a *theorem the engine of
record already proves*:

> **the queue is the trail of `dist`.**

`BfsQ.QReached` — proved in `BfsQ.Fr.qReached`, consumed by
`BfsQSynth.bfsQS_reached` — says that for every `w < n`,
`D[w]! ≤ d ↔ ∃ k < max tl 1, Q[k]! = w`; and `BfsQ.Fr.cap` says every
entry is `≤ d + 1`. Together: **a slot of `dist` differs from the
sentinel exactly when its index appears in the queue's prefix
`Q[0 … max tl 1)`**, and `Fr.qinj` says it appears once. That is
literally `TrailWf`'s `off_trail` and `mem_lt` clauses with `Q` as the
trail array and `max tl 1` as the top of trail. So the search *already*
maintains a trail, in an array it already owns, at no extra cost — no
`tset`, no push, no second scratch array, and no change to the search
program at all.

Consequently the protocol is:

```
                        ── one turn ──
  dist = replicate n (d+1)        (trail-clean, the loop-carried pre)
  q, out : any length-n arrays    (junk; the turn overwrites what it uses)
      │
      │  seed + drain              ← BfsQSynth's search, verbatim, no fill
      ▼
  dist[v] = distance for v reached, q[0 … max tl 1) = the reached list
      │
      │  harvest-and-clean         ← one pass over the queue prefix:
      │                              out[j] := dist[q[j]]; dist[q[j]] := d+1
      ▼
  out[0 … max tl 1) = the answers, dist = replicate n (d+1) again
```

and the consumer reads its answers off `q`/`out` **by the prefix**, never
by a carrier-wide scan. The reset is inside the turn, after the readout,
which is what makes the post equal to the pre — so `k` successive turns
compose (§7) and the one `O(n)` charge the discipline allows, the initial
fill, is paid once outside the loop.

The harvest is fused into the clean because `Fr.qinj` makes the prefix
repeat-free: each slot is read exactly once before it is restored, so one
pass does both. Note the contrast with `IicfTrailArray`'s R0/D-g — that
trail charges per *write* because its push is unconditional; here the
push is the relaxation itself, which the `du = sent` test already makes
at most once per vertex, so this trail charges per *distinct* cell. The
price of that is not free: it is `Fr.qinj`, and `Fr` is landed capital.

## Judgment calls

**B4b/D-a — the cost is a function of the *result*, not of a bound.**
`NRest.spec`'s cost argument is `α → ECost` and every consumer in the
tower instantiates it at `fun _ => c`. The sharp turn bound cannot: the
number of pops is the reached count and the number of scanned slots is
`rowSum off Q tl`, and both are read off the state the search leaves.
So §5's export is stated at a genuine `fun r => …`, and §6 weakens it to
the constant form `fun _ => turnCost T S` for caller-supplied bounds
`T`, `S` by one `spec_mono`. The tower needed one new lemma for this,
`bindT_spec_le'` (§3), which is `Sepref/IrLoop.lean`'s `bindT_spec_le`
with the continuation's cost allowed to depend on its result; the proof
is the same four lines.

**B4b/D-b — the drain is re-derived at a *difference* cost, not at an
energy.** `BfsQ.drainLoop_le'` prices the drain by the two-currency
energy `E2 … (n - hd) (ns - rowSum …)`: the potential is what is *left*,
and both slacks are carrier-wide because nothing bounds the queue's final
length except `n`. The touched-only statement needs the opposite reading
— what was *spent* — so `drainLoop_touched` (§4) carries
`(hd' - hd) • iter popC + (rowSum off Q' hd' - rowSum off Q hd) • iter scanC`.
The induction is `drainLoop_le'`'s with two clauses added to the
postcondition (`hd` is monotone, and the queue's prefix below `hd` is
stable), which is what makes both truncated subtractions honest and the
telescoping exact. `popF_le`, `Fr`, `SInv` and the whole graph-theoretic
core are consumed unchanged.

**B4b/D-c — no `max` in the program: slot `0` is harvested outside the
loop.** The prefix has length `max tl 1`, not `tl`: a *dead* source is
still at `q[0]` with `dist[src] = 0` (the seed writes unconditionally),
and `QReached` is stated at `max tl 1` for exactly that reason. Computing
`max tl 1` in the program would cost a branch and a constant; harvesting
slot `0` unconditionally and running the loop from `j = 1` to `tl` covers
the same `max tl 1` slots — `hcRun_max` (§2) is that identity — and it
also makes the guard count come out at `max tl 1` on the nose, so the
turn's price is `(max tl 1) • iter hcC` with no correction term.

**B4b/D-d — `out` is a third array, and it needs no reset.** The turn's
answers have to leave the turn somewhere, and `dist` cannot hold them (it
is restored). `out` is written only at indices below `max tl 1`, and the
next turn overwrites the ones it uses, so its precondition is "any list
of length `n`" — it is junk in, junk out, and no `O(n)` charge attaches
to it. The same is true of `q`: the turn's precondition asks nothing of
its contents.
-/

namespace Lax13Proofs.Refine

namespace BfsQTrail

open Bfs BfsQ Sepref Ir NRest Codegen

/-! ## 1. Refute before prove

Everything below is *run* before anything is proved. The twins are not an
independent specification — `searchTw` is `BfsQ.drainTw` from the seed
`BfsQSynth.bfsQS` builds, and `hcStep` is exactly what §5's value lemma
proves the abstract harvest body equal to — so a `#guard` here is a
`#guard` about the abstract program. The differential partner is
`BfsQ.bfsTw`, which `Refine/Examples/BfsQ.lean` §1 already checked
against `RamBfs`'s four published readings and against P1's independent
level-based twin. -/

/-- The harvest-and-clean state: the distance array, the answer array,
and the prefix index. -/
abbrev HSt : Type := List ℕ × List ℕ × ℕ

/-- The seed `bfsQS` builds, as a function: the source at distance zero,
the source at the head of the queue, and a tail that is `1` exactly when
the source is alive. -/
def seedSt (src : ℕ) (alv D Q : List ℕ) : St :=
  (D.set src 0, Q.set 0 src, 0, if 0 < alv[src]! then 1 else 0)

/-- **The search, without the fill**: seed, then drain. `BfsQ.bfsTw`
is this at the two arrays the fill would have produced. -/
def searchTw (n d src : ℕ) (off tgt alv D Q : List ℕ) : St :=
  drainTw off tgt alv d n (seedSt src alv D Q)

/-- **One slot of the harvest-and-clean pass**: read the vertex the
prefix names, copy its distance to the answer array, restore the
sentinel, advance. -/
def hcStep (sent : ℕ) (Q : List ℕ) (s : HSt) : HSt :=
  (s.1.set Q[s.2.2]! sent, s.2.1.set s.2.2 s.1[Q[s.2.2]!]!, s.2.2 + 1)

/-- `m` slots of it. -/
def hcRun (sent : ℕ) (Q : List ℕ) : ℕ → HSt → HSt
  | 0, s => s
  | m + 1, s => hcRun sent Q m (hcStep sent Q s)

/-- **One whole turn**: the search, then the harvest-and-clean pass over
the queue's prefix — slot `0` unconditionally and then `j = 1 … tl`
(B4b/D-c). The result carries the answer arrays *and* the queue with its
tail, because that pair is what the turn's price is a function of. -/
def turnTw (n d src : ℕ) (off tgt alv D Q O : List ℕ) : HSt × List ℕ × ℕ :=
  let r := searchTw n d src off tgt alv D Q
  (hcRun (d + 1) r.2.1 (r.2.2.2 - 1) (hcStep (d + 1) r.2.1 (r.1, O, 0)), r.2.1, r.2.2.2)

/-! ### The arena

`RamBfs`'s own five-vertex demo, through `BfsQ`'s `demoOff`/`demoTgt`/
`demoAlv`: the path `0—1—2—3` with an isolated vertex `4`. -/

/-- A trail-clean distance array of capacity `n`: every slot the
sentinel. -/
def cleanD (n d : ℕ) : List ℕ := List.replicate n (d + 1)

/-- Junk scratch: the turn asks nothing of `q` or `out` but their
length. -/
def junkA (n : ℕ) : List ℕ := List.replicate n 0

/-- The turn's answers, read off the prefix: the pairs
`(q[j], out[j])` for `j < max tl 1`. -/
def readPrefix (r : HSt × List ℕ × ℕ) : List (ℕ × ℕ) :=
  (List.range (max r.2.2 1)).map fun j => (r.2.1[j]!, r.1.2.1[j]!)

/-- …and the same pairs read the *old* way, off a carrier-wide distance
array: every vertex the search put within the cap, with its distance.
This is the differential partner. -/
def readCarrier (n d : ℕ) (D : List ℕ) : List (ℕ × ℕ) :=
  (List.range n).filterMap fun v => if D[v]! ≤ d then some (v, D[v]!) else none

/-- The demo turn: carrier `5`, cap `d`, source `src`, mask bit `a2`. -/
def demoTurn (d src a2 : ℕ) : HSt × List ℕ × ℕ :=
  turnTw 5 d src demoOff demoTgt (demoAlv a2) (cleanD 5 d) (junkA 5) (junkA 5)

/-! ### The differential test: same answers as the engine of record -/

-- Mask on: every vertex of the path is reached, and the turn's
-- prefix readout is the engine's carrier readout, up to order.
#guard (demoTurn 3 0 1 |> readPrefix).mergeSort (fun a b => a.1 ≤ b.1)
  = readCarrier 5 3 (bfsTw 5 3 0 demoOff demoTgt (demoAlv 1))
-- Mask off at vertex 2: the path is cut there.
#guard (demoTurn 3 0 0 |> readPrefix).mergeSort (fun a b => a.1 ≤ b.1)
  = readCarrier 5 3 (bfsTw 5 3 0 demoOff demoTgt (demoAlv 0))
-- The cap bites.
#guard (demoTurn 1 0 1 |> readPrefix).mergeSort (fun a b => a.1 ≤ b.1)
  = readCarrier 5 1 (bfsTw 5 1 0 demoOff demoTgt (demoAlv 1))
#guard (demoTurn 0 0 1 |> readPrefix).mergeSort (fun a b => a.1 ≤ b.1)
  = readCarrier 5 0 (bfsTw 5 0 0 demoOff demoTgt (demoAlv 1))
-- …and from a different source.
#guard (demoTurn 3 2 1 |> readPrefix).mergeSort (fun a b => a.1 ≤ b.1)
  = readCarrier 5 3 (bfsTw 5 3 2 demoOff demoTgt (demoAlv 1))

-- The readouts in full, pinned: BFS order on the left, carrier order on
-- the right.
#guard readPrefix (demoTurn 3 0 1) = [(0, 0), (1, 1), (2, 2), (3, 3)]
#guard readCarrier 5 3 (bfsTw 5 3 0 demoOff demoTgt (demoAlv 1)) = [(0, 0), (1, 1), (2, 2), (3, 3)]
-- With vertex 2 masked out only `0` and `1` are reached — and the
-- prefix has exactly two entries, which is the point: the turn never
-- looks at the other three slots.
#guard readPrefix (demoTurn 3 0 0) = [(0, 0), (1, 1)]
#guard (demoTurn 3 0 0).2.2 = 2

-- **The queue is the trail**: the search's own distance array differs
-- from the sentinel exactly at the prefix's entries.
#guard (searchTw 5 3 0 demoOff demoTgt (demoAlv 0) (cleanD 5 3) (junkA 5)).1 = [0, 1, 4, 4, 4]
#guard (searchTw 5 3 0 demoOff demoTgt (demoAlv 0) (cleanD 5 3) (junkA 5)).2.1[0]! = 0
#guard (searchTw 5 3 0 demoOff demoTgt (demoAlv 0) (cleanD 5 3) (junkA 5)).2.1[1]! = 1

/-! ### The reset, pinned: the store comes back clean -/

-- After the turn the distance array is the sentinel everywhere again,
-- whatever the search wrote.
#guard (demoTurn 3 0 1).1.1 = cleanD 5 3
#guard (demoTurn 3 0 0).1.1 = cleanD 5 3
#guard (demoTurn 0 0 1).1.1 = cleanD 5 0
#guard (demoTurn 3 2 1).1.1 = cleanD 5 3

-- **A second invocation from the restored store is a fresh
-- invocation.** This is the re-entrancy claim, run: turn from `0`, then
-- turn from `2` on what the first turn handed back, and the second
-- turn's answers are the ones a *fresh* turn from `2` gives.
def demoTurn2 (d : ℕ) : HSt × List ℕ × ℕ :=
  let r1 := demoTurn d 0 1
  turnTw 5 d 2 demoOff demoTgt (demoAlv 1) r1.1.1 r1.2.1 r1.1.2.1

#guard readPrefix (demoTurn2 3) = readPrefix (demoTurn 3 2 1)
#guard (demoTurn2 3).1.1 = cleanD 5 3

-- **Negative control 1.** Without the reset the second turn is wrong:
-- the search would read a stale `dist` and find nothing new. Here is the
-- store the first turn *would* have left with the clean pass deleted…
#guard (searchTw 5 3 0 demoOff demoTgt (demoAlv 1) (cleanD 5 3) (junkA 5)).1 = [0, 1, 2, 3, 4]
-- …and a search from `2` on it reaches only `2` itself, because every
-- other slot already reads below the sentinel.
#guard (searchTw 5 3 2 demoOff demoTgt (demoAlv 1)
  (searchTw 5 3 0 demoOff demoTgt (demoAlv 1) (cleanD 5 3) (junkA 5)).1 (junkA 5)).2.2.2 = 1
/--
error: Expression
  decide
    ((searchTw 5 3 2 demoOff demoTgt (demoAlv 1) (searchTw 5 3 0 demoOff demoTgt (demoAlv 1) (cleanD 5 3) (junkA 5)).1
              (junkA 5)).2.2.2 =
      (demoTurn2 3).2.2)
did not evaluate to `true`
-/
#guard_msgs in
#guard (searchTw 5 3 2 demoOff demoTgt (demoAlv 1)
  (searchTw 5 3 0 demoOff demoTgt (demoAlv 1) (cleanD 5 3) (junkA 5)).1 (junkA 5)).2.2.2
  = (demoTurn2 3).2.2

-- **Negative control 2.** A clean pass one slot short leaves the array
-- dirty — the pass is not vacuously correct.
/--
error: Expression
  decide
    ((hcRun 4 (searchTw 5 3 0 demoOff demoTgt (demoAlv 1) (cleanD 5 3) (junkA 5)).2.1 2
          ((searchTw 5 3 0 demoOff demoTgt (demoAlv 1) (cleanD 5 3) (junkA 5)).1, junkA 5, 0)).1 =
      cleanD 5 3)
did not evaluate to `true`
-/
#guard_msgs in
#guard (hcRun 4 (searchTw 5 3 0 demoOff demoTgt (demoAlv 1) (cleanD 5 3) (junkA 5)).2.1 2
  ((searchTw 5 3 0 demoOff demoTgt (demoAlv 1) (cleanD 5 3) (junkA 5)).1, junkA 5, 0)).1
  = cleanD 5 3

-- **The dead source.** The mask is clear at the source, the queue never
-- grows — and the prefix is still one slot long, holding the source,
-- because the seed wrote `dist[src] := 0` and the clean pass has to undo
-- it. This is B4b/D-c's whole content.
#guard (turnTw 5 3 2 demoOff demoTgt [1, 1, 0, 1, 1] (cleanD 5 3) (junkA 5) (junkA 5)).2.2 = 0
#guard readPrefix (turnTw 5 3 2 demoOff demoTgt [1, 1, 0, 1, 1] (cleanD 5 3) (junkA 5) (junkA 5))
  = [(2, 0)]
#guard (turnTw 5 3 2 demoOff demoTgt [1, 1, 0, 1, 1] (cleanD 5 3) (junkA 5) (junkA 5)).1.1
  = cleanD 5 3

/-! ## 2. The harvest-and-clean pass, as a function

The mathematics the trail discipline needs, before any program: `m`
slots of the prefix, and what the two arrays look like afterwards. -/

/-- Slot `0` outside the loop and `m - 1` inside it are the prefix's
`max m 1` slots (B4b/D-c). -/
theorem hcRun_max (sent : ℕ) (Q : List ℕ) (m : ℕ) (s : HSt) :
    hcRun sent Q (m - 1) (hcStep sent Q s) = hcRun sent Q (max m 1) s := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  · rw [show max m 1 = m by omega, show m = (m - 1) + 1 by omega]
    simp [hcRun]

theorem hcRun_index (sent : ℕ) (Q : List ℕ) :
    ∀ (m : ℕ) (s : HSt), (hcRun sent Q m s).2.2 = s.2.2 + m := by
  intro m
  induction m with
  | zero => intro s; simp [hcRun]
  | succ m ih => intro s; rw [hcRun, ih]; show s.2.2 + 1 + m = s.2.2 + (m + 1); omega

theorem hcRun_len (sent : ℕ) (Q : List ℕ) :
    ∀ (m : ℕ) (s : HSt), (hcRun sent Q m s).1.length = s.1.length ∧
      (hcRun sent Q m s).2.1.length = s.2.1.length := by
  intro m
  induction m with
  | zero => intro s; exact ⟨rfl, rfl⟩
  | succ m ih =>
    intro s
    obtain ⟨h1, h2⟩ := ih (hcStep sent Q s)
    rw [hcRun]
    exact ⟨by rw [h1]; show (s.1.set _ _).length = _; simp,
      by rw [h2]; show (s.2.1.set _ _).length = _; simp⟩

open scoped Classical in
/-- **What the pass does.** Reading the prefix restores every slot it
names to the sentinel and copies the distance it found into the answer
array; nothing else moves. The injectivity hypothesis is `Fr.qinj` — it
is what makes the *read* at slot `k` see the array as it was, although
earlier slots have already been restored. -/
theorem hcRun_spec (sent : ℕ) (Q : List ℕ) (n : ℕ) :
    ∀ (m : ℕ) (s : HSt), s.1.length = n → s.2.1.length = n → s.2.2 + m ≤ n →
      (∀ k, k < s.2.2 + m → Q[k]! < n) →
      (∀ k, k < s.2.2 + m → ∀ k', k' < s.2.2 + m → Q[k]! = Q[k']! → k = k') →
      (∀ k, s.2.2 ≤ k → k < s.2.2 + m → (hcRun sent Q m s).2.1[k]! = s.1[Q[k]!]!) ∧
      (∀ k, k < s.2.2 → (hcRun sent Q m s).2.1[k]! = s.2.1[k]!) ∧
      (∀ w, w < n → (hcRun sent Q m s).1[w]!
        = if ∃ k, s.2.2 ≤ k ∧ k < s.2.2 + m ∧ Q[k]! = w then sent else s.1[w]!) := by
  intro m
  induction m with
  | zero =>
    intro s _ _ _ _ _
    refine ⟨fun k _ hk => absurd hk (by omega), fun _ _ => rfl, fun w _ => ?_⟩
    rw [if_neg (by rintro ⟨k, hk1, hk2, -⟩; omega)]
    rfl
  | succ m ih =>
    intro s hd hOu hn hlt hinj
    have hjn : s.2.2 < n := by omega
    have hqj : Q[s.2.2]! < n := hlt s.2.2 (by omega)
    have hqjd : Q[s.2.2]! < s.1.length := by rw [hd]; exact hqj
    have hjo : s.2.2 < s.2.1.length := by rw [hOu]; exact hjn
    set s' : HSt := hcStep sent Q s with hs'
    have hs'1 : s'.1 = s.1.set Q[s.2.2]! sent := rfl
    have hs'2 : s'.2.1 = s.2.1.set s.2.2 s.1[Q[s.2.2]!]! := rfl
    have hs'3 : s'.2.2 = s.2.2 + 1 := rfl
    have hd' : s'.1.length = n := by rw [hs'1, List.length_set]; exact hd
    have hOu' : s'.2.1.length = n := by rw [hs'2, List.length_set]; exact hOu
    have hlt' : ∀ k, k < s'.2.2 + m → Q[k]! < n := by
      intro k hk; exact hlt k (by rw [hs'3] at hk; omega)
    have hinj' : ∀ k, k < s'.2.2 + m → ∀ k', k' < s'.2.2 + m → Q[k]! = Q[k']! → k = k' := by
      intro k hk k' hk'; rw [hs'3] at hk hk'; exact hinj k (by omega) k' (by omega)
    obtain ⟨ih1, ih2, ih3⟩ := ih s' hd' hOu' (by rw [hs'3]; omega) hlt' hinj'
    rw [hcRun]
    refine ⟨fun k hk1 hk2 => ?_, fun k hk => ?_, fun w hw => ?_⟩
    · rcases eq_or_lt_of_le hk1 with rfl | hk1'
      · rw [ih2 _ (by rw [hs'3]; omega), hs'2, get!_set _ _ _ _ hjo, if_pos rfl]
      · have hk1'' : s'.2.2 ≤ k := by rw [hs'3]; omega
        rw [ih1 k hk1'' (by rw [hs'3]; omega), hs'1, get!_set _ _ _ _ hqjd,
          if_neg (fun hc => absurd (hinj k (by omega) s.2.2 (by omega) hc) (by omega))]
    · rw [ih2 k (by rw [hs'3]; omega), hs'2, get!_set _ _ _ _ hjo, if_neg (by omega)]
    · rw [ih3 w hw, hs'1, get!_set _ _ _ _ hqjd, hs'3]
      by_cases hex : ∃ k, s.2.2 + 1 ≤ k ∧ k < s.2.2 + 1 + m ∧ Q[k]! = w
      · obtain ⟨k, hk1, hk2, hk3⟩ := hex
        rw [if_pos ⟨k, hk1, hk2, hk3⟩, if_pos ⟨k, by omega, by omega, hk3⟩]
      · rw [if_neg hex]
        by_cases hw0 : w = Q[s.2.2]!
        · rw [if_pos hw0, if_pos ⟨s.2.2, le_rfl, by omega, hw0.symm⟩]
        · rw [if_neg hw0, if_neg ?_]
          rintro ⟨k, hk1, hk2, hk3⟩
          rcases eq_or_lt_of_le hk1 with rfl | hk1'
          · exact hw0 hk3.symm
          · exact hex ⟨k, by omega, by omega, hk3⟩

/-! ## 3. The abstract program

Three pieces: the search without its fill, one harvest-and-clean slot,
and the loop over the rest of the prefix. Nothing here mentions an
assertion, a cell, a `Com` or a carrier size. -/

/-- **The search, without the fill.** `BfsQSynth.bfsQS` without its
leading `fillLoop'` — the caller supplies a distance array that is
already all-sentinel, which is what a *turn* starts from. -/
noncomputable def searchQ (n d src : ℕ) (off tgt alv D Q : List ℕ) : NRest St ECost :=
  bindT (mopAset D src 0) fun D' =>
    bindT (mopAset Q 0 src) fun Q' =>
      bindT (mopAget alv src) fun a =>
        bindT (irIf (decide (0 < a)) (mopConstN 1) (mopConstN 0)) fun tl =>
          bindT (pack4 D' Q' 0 tl) fun st =>
            drainLoop n d (d + 1) off tgt alv st

/-- **One slot of the harvest-and-clean pass.** Read the vertex, read
its distance, write the answer, restore the sentinel, advance. -/
noncomputable def hcF (sent : ℕ) (Q : List ℕ) : HSt → NRest HSt ECost := fun s =>
  bindT (mopAget Q s.2.2) fun v =>
    bindT (mopAget s.1 v) fun w =>
      bindT (mopAset s.2.1 s.2.2 w) fun O =>
        bindT (mopAset s.1 v sent) fun D =>
          bindT (BfsQSynth.mopSucc s.2.2) fun j =>
            bindT (mopPair O j) fun p => mopPair D p

def hcBf (tl : ℕ) : HSt → Bool := fun s => decide (s.2.2 < tl)

/-- The pass's assertion: what the reads and the writes need, and
nothing else (P4/D-ed). -/
def hcP (n tl : ℕ) (Q : List ℕ) : HSt → Prop := fun s =>
  s.1.length = n ∧ s.2.1.length = n ∧ Q.length = n ∧ tl ≤ n ∧ ∀ k, k < tl → Q[k]! < n

noncomputable def hcLoop (n sent tl : ℕ) (Q : List ℕ) (s₀ : HSt) : NRest HSt ECost :=
  irWhileIT (fun s => hcBf tl s = true → hcP n tl Q s) (hcBf tl) (hcF sent Q) s₀

/-- **The turn.** Search, harvest slot `0`, run the pass over the rest of
the prefix, and hand back the answers together with the queue and its
tail — the pair the turn's price is a function of (B4b/D-a). -/
noncomputable def turnQ (n d src : ℕ) (off tgt alv D Q O : List ℕ) :
    NRest (HSt × List ℕ × ℕ) ECost :=
  bindT (searchQ n d src off tgt alv D Q) fun st =>
    bindT (hcF (d + 1) st.2.1 (st.1, O, 0)) fun s1 =>
      bindT (hcLoop n (d + 1) st.2.2.2 st.2.1 s1) fun s2 =>
        bindT (mopPair st.2.1 st.2.2.2) fun p => mopPair s2 p

/-! ## 4. What one slot costs, and what the pass costs -/

/-- One harvest-and-clean slot: the two reads, the two writes, the
advance, and the two tuple steps. -/
def hcC : ACost String ℕ := cu Currency.aget + cu Currency.aget + cu Currency.aset
  + cu Currency.aset + cu Currency.add + cu Currency.skip + cu Currency.skip

theorem hcF_eq (sent : ℕ) (Q : List ℕ) (s : HSt) (h1 : s.2.2 < Q.length)
    (h2 : Q[s.2.2]! < s.1.length) (h3 : s.2.2 < s.2.1.length) :
    hcF sent Q s = NRest.consume (NRest.returnT (hcStep sent Q s)) (liftACost hcC) := by
  show NRest.bindT (mopAget Q s.2.2) _ = _
  simp only [mopAget_def, mopAset_def, mopPair_def, BfsQSynth.mopSucc_eq, mopBinop_def,
    NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h3, NRest.returnT_bindT,
    bindT_unitT, NRest.consume_consume, hcStep, hcC, liftACost_add, liftACost_cu,
    Imp.Bop.apply_add, binopCurrency_add]
  congr 1
  ac_rfl

/-- The pass's price: one slot and one guard per slot, plus the exit's
guard. **`n` does not occur.** -/
def hcLoopCost (m : ℕ) : ACost String ℕ := m • iter hcC + cu Currency.«while»

/-- **The pass, run to the end of the prefix.** -/
theorem hcLoop_value (n sent tl : ℕ) (Q : List ℕ) (hQ : Q.length = n) (htn : tl ≤ n)
    (hqlt : ∀ k, k < tl → Q[k]! < n) :
    ∀ (fuel : ℕ) (s : HSt), s.1.length = n → s.2.1.length = n → tl - s.2.2 ≤ fuel →
      hcLoop n sent tl Q s
        = NRest.consume (NRest.returnT (hcRun sent Q (tl - s.2.2) s))
            (liftACost (hcLoopCost (tl - s.2.2))) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hd hOu hf
    have hb : hcBf tl s = false := by simp only [hcBf, decide_eq_false_iff_not]; omega
    show irWhileIT _ (hcBf tl) (hcF sent Q) s = _
    rw [irWhile_exit hb, show tl - s.2.2 = 0 by omega]
    congr 1
    simp [hcLoopCost, liftACost_cu]
  | succ fuel ih =>
    intro s hd hOu hf
    by_cases hb : s.2.2 < tl
    · have hbt : hcBf tl s = true := by simp [hcBf, hb]
      have hI : hcBf tl s = true → hcP n tl Q s := fun _ => ⟨hd, hOu, hQ, htn, hqlt⟩
      have h1 : s.2.2 < Q.length := by rw [hQ]; omega
      have h2 : Q[s.2.2]! < s.1.length := by rw [hd]; exact hqlt _ hb
      have h3 : s.2.2 < s.2.1.length := by rw [hOu]; omega
      have hstep : tl - s.2.2 = (tl - (s.2.2 + 1)) + 1 := by omega
      have hidx : (hcStep sent Q s).2.2 = s.2.2 + 1 := rfl
      show irWhileIT _ (hcBf tl) (hcF sent Q) s = _
      rw [irWhileIT_of_true hI hbt, hcF_eq sent Q s h1 h2 h3, bindT_unitT]
      show NRest.consume (NRest.consume (hcLoop n sent tl Q (hcStep sent Q s)) _) _ = _
      rw [ih (hcStep sent Q s) (by show (s.1.set _ _).length = n; simpa using hd)
          (by show (s.2.1.set _ _).length = n; simpa using hOu)
          (by show tl - (s.2.2 + 1) ≤ fuel; omega),
        hidx, hstep, hcRun, NRest.consume_consume, NRest.consume_consume]
      congr 1
      simp only [hcLoopCost, iter, succ_nsmul, liftACost_add, liftACost_nsmul, liftACost_cu]
      abel
    · have hbf : hcBf tl s = false := by simp only [hcBf, decide_eq_false_iff_not]; omega
      show irWhileIT _ (hcBf tl) (hcF sent Q) s = _
      rw [irWhile_exit hbf, show tl - s.2.2 = 0 by omega]
      congr 1
      simp [hcLoopCost, liftACost_cu]

/-! ## 5. The drain, re-cashed as what it *spent* (B4b/D-b)

`BfsQ.drainLoop_le'` prices the drain by the energy still available:
`E2 … (n - hd) (ns - rowSum …)`. Both slacks are carrier-wide, and no
weakening of them is: the queue invariant bounds the tail by `n` and
nothing sharper. The touched-only reading is the complementary one — the
*difference* between the state the drain leaves and the state it was
handed — and it needs no bound at all, because it is the increment the
loop actually pays.

Everything mathematical is reused: `popF_le` (one pop, priced at
`popC` plus one `scanC` per slot of the row), `Fr` with `relax`,
`complete`, `pop`, `popSkip`, `qReached`, and the whole scan tiling.
Only the induction's bookkeeping is new. -/

/-- `Sepref/IrLoop.lean`'s `bindT_spec_le`, with the continuation's cost
allowed to depend on its own result (B4b/D-a). Same proof; stated here
rather than in the tower because it is the only consumer so far. -/
theorem bindT_spec_le' {α β : Type} (P : α → Prop) (c : ECost) (g : α → NRest β ECost)
    (P' : β → Prop) (c' : β → ECost)
    (h : ∀ x, P x → g x ≤ NRest.spec P' c') :
    NRest.bindT (NRest.spec P (fun _ => c)) g ≤ NRest.spec P' (fun y => c + c' y) := by
  rw [NRest.spec, NRest.bindT_rest_eq_iSup]
  refine iSup_le fun x => ?_
  by_cases hx : P x
  · rw [if_pos hx, NRest.consumeB_coe]
    refine le_trans (NRest.consume_mono (h x hx) le_rfl) ?_
    rw [Sepref.consume_spec]
  · rw [if_neg hx, NRest.consumeB_bot]
    exact bot_le

/-- The expanded prefix only grows. -/
theorem rowSum_mono (off Q : List ℕ) {a b : ℕ} (h : a ≤ b) :
    rowSum off Q a ≤ rowSum off Q b :=
  Finset.sum_le_sum_of_subset fun _ hi =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) h)

section Drain

variable {n ns d : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ} {s : Fin n}

/-- **The drain, at a difference cost.** One `iter popC` per pop the
loop *made* and one `iter scanC` per adjacency slot it *scanned*, plus
the exit's guard — and no `n`, no `ns`, no potential. The two extra
postcondition clauses (`hd` only grows; the expanded prefix of the queue
never moves) are what makes both truncated subtractions exact. -/
theorem drainLoop_touched (hc : Csr n ns G off tgt alv) (q0 : ℕ) :
    ∀ (fuel : ℕ) (z : St), Fr n d G alv s z.1 z.2.1 z.2.2.1 z.2.2.2 → z.2.1[0]! = q0 →
      n - z.2.2.1 ≤ fuel →
      drainLoop n d (d + 1) off tgt alv z
        ≤ NRest.spec
            (fun z' : St => ((Fr n d G alv s z'.1 z'.2.1 z'.2.2.1 z'.2.2.2 ∧
                  z'.2.2.2 ≤ z'.2.2.1) ∧ z'.2.1[0]! = q0) ∧
              z.2.2.1 ≤ z'.2.2.1 ∧ ∀ i, i < z.2.2.1 → z'.2.1[i]! = z.2.1[i]!)
            (fun z' => liftACost (E2 (iter popC) (iter scanC) (z'.2.2.1 - z.2.2.1)
              (rowSum off z'.2.1 z'.2.2.1 - rowSum off z.2.1 z.2.2.1) + cu Currency.«while»)) := by
  have exit : ∀ z : St, Fr n d G alv s z.1 z.2.1 z.2.2.1 z.2.2.2 → z.2.1[0]! = q0 →
      z.2.2.2 ≤ z.2.2.1 →
      drainLoop n d (d + 1) off tgt alv z
        ≤ NRest.spec
            (fun z' : St => ((Fr n d G alv s z'.1 z'.2.1 z'.2.2.1 z'.2.2.2 ∧
                  z'.2.2.2 ≤ z'.2.2.1) ∧ z'.2.1[0]! = q0) ∧
              z.2.2.1 ≤ z'.2.2.1 ∧ ∀ i, i < z.2.2.1 → z'.2.1[i]! = z.2.1[i]!)
            (fun z' => liftACost (E2 (iter popC) (iter scanC) (z'.2.2.1 - z.2.2.1)
              (rowSum off z'.2.1 z'.2.2.1 - rowSum off z.2.1 z.2.2.1)
                + cu Currency.«while»)) := by
    intro z hz hq hle
    have hb : popBf z = false := by simp only [popBf, decide_eq_false_iff_not]; omega
    simp only [drainLoop, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨⟨⟨hz, hle⟩, hq⟩, le_rfl, fun _ _ => rfl⟩ (le_of_eq ?_)
    rw [Nat.sub_self, Nat.sub_self]
    simp [E2, liftACost_cu]
  intro fuel
  induction fuel with
  | zero => intro z hz hq hf; exact exit z hz hq (by have := hz.hdle; have := hz.tl_le; omega)
  | succ fuel ih =>
    intro z hz hq hf
    by_cases hb : z.2.2.1 < z.2.2.2
    · have hbt : popBf z = true := by simp [popBf, hb]
      have hIs : popBf z = true → popP n (d + 1) off tgt alv z :=
        fun _ => ⟨hc.shape, hz.dlen, hz.qlen, hz.qlt, hz.room⟩
      have hzn : z.2.2.1 < n := lt_of_lt_of_le hb hz.tl_le
      set r : ℕ := rowLen off z.2.1[z.2.2.1]! with hrdef
      have hrow1 : rowSum off z.2.1 (z.2.2.1 + 1) = rowSum off z.2.1 z.2.2.1 + r :=
        Finset.sum_range_succ _ _
      -- the continuation, at a cost expressed in the *outer* state's data
      have hcont : ∀ z' : St, (Fr n d G alv s z'.1 z'.2.1 z'.2.2.1 z'.2.2.2 ∧
            z'.2.2.1 = z.2.2.1 + 1 ∧ ∀ i, i < z.2.2.1 + 1 → z'.2.1[i]! = z.2.1[i]!) →
          drainLoop n d (d + 1) off tgt alv z'
            ≤ NRest.spec
                (fun z'' : St => ((Fr n d G alv s z''.1 z''.2.1 z''.2.2.1 z''.2.2.2 ∧
                      z''.2.2.2 ≤ z''.2.2.1) ∧ z''.2.1[0]! = q0) ∧
                  z.2.2.1 + 1 ≤ z''.2.2.1 ∧
                    ∀ i, i < z.2.2.1 + 1 → z''.2.1[i]! = z.2.1[i]!)
                (fun z'' => liftACost (E2 (iter popC) (iter scanC)
                  (z''.2.2.1 - (z.2.2.1 + 1))
                  (rowSum off z''.2.1 z''.2.2.1 - (rowSum off z.2.1 z.2.2.1 + r))
                    + cu Currency.«while»)) := by
        rintro z' ⟨hfr', hhd', hq'⟩
        refine le_trans (ih z' hfr' (by rw [hq' 0 (by omega)]; exact hq) (by omega))
          (spec_mono (fun z'' hx => ?_) fun z'' hx => le_of_eq ?_)
        · obtain ⟨hx1, hx2, hx3⟩ := hx
          refine ⟨hx1, by omega, fun i hi => ?_⟩
          rw [hx3 i (by omega), hq' i (by omega)]
        · have hrs' : rowSum off z'.2.1 (z.2.2.1 + 1) = rowSum off z.2.1 z.2.2.1 + r := by
            rw [← hrow1, rowSum, rowSum]
            exact Finset.sum_congr rfl fun i hi => by
              rw [hq' i (by have := Finset.mem_range.mp hi; omega)]
          rw [hhd', hrs']
      have hcost : ∀ z'' : St, z.2.2.1 + 1 ≤ z''.2.2.1 →
          rowSum off z.2.1 z.2.2.1 + r ≤ rowSum off z''.2.1 z''.2.2.1 →
          irUnit Currency.«while»
            + (liftACost (popC + r • iter scanC)
              + liftACost (E2 (iter popC) (iter scanC) (z''.2.2.1 - (z.2.2.1 + 1))
                  (rowSum off z''.2.1 z''.2.2.1 - (rowSum off z.2.1 z.2.2.1 + r))
                    + cu Currency.«while»))
            = liftACost (E2 (iter popC) (iter scanC) (z''.2.2.1 - z.2.2.1)
                (rowSum off z''.2.1 z''.2.2.1 - rowSum off z.2.1 z.2.2.1)
                  + cu Currency.«while») := by
        intro z'' hpop hscan
        rw [show z''.2.2.1 - z.2.2.1 = (z''.2.2.1 - (z.2.2.1 + 1)) + 1 by omega,
          show rowSum off z''.2.1 z''.2.2.1 - rowSum off z.2.1 z.2.2.1
            = (rowSum off z''.2.1 z''.2.2.1 - (rowSum off z.2.1 z.2.2.1 + r)) + r by omega,
          E2_split]
        simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
        ac_rfl
      calc drainLoop n d (d + 1) off tgt alv z
            = NRest.consume (NRest.bindT (popF n d (d + 1) off tgt alv z)
                fun z' => drainLoop n d (d + 1) off tgt alv z') (irUnit Currency.«while») := by
              simp only [drainLoop]; rw [irWhileIT_of_true hIs hbt]
          _ ≤ NRest.consume (NRest.spec _ (fun z'' => liftACost (popC + r • iter scanC)
                + liftACost (E2 (iter popC) (iter scanC) (z''.2.2.1 - (z.2.2.1 + 1))
                    (rowSum off z''.2.1 z''.2.2.1 - (rowSum off z.2.1 z.2.2.1 + r))
                      + cu Currency.«while»))) (irUnit Currency.«while») :=
              NRest.consume_mono (le_trans (NRest.bindT_mono (popF_le hc hz hbt) fun _ => le_rfl)
                (bindT_spec_le' _ _ _ _ _ hcont)) le_rfl
          _ ≤ _ := by
              rw [Sepref.consume_spec]
              refine spec_mono (fun z'' hx => ⟨hx.1, by omega, fun i hi => hx.2.2 i (by omega)⟩)
                fun z'' hx => le_of_eq (hcost z'' hx.2.1 ?_)
              have hstab : rowSum off z''.2.1 (z.2.2.1 + 1) = rowSum off z.2.1 (z.2.2.1 + 1) := by
                rw [rowSum, rowSum]
                exact Finset.sum_congr rfl fun i hi => by
                  rw [hx.2.2 i (by have := Finset.mem_range.mp hi; omega)]
              calc rowSum off z.2.1 z.2.2.1 + r
                  = rowSum off z''.2.1 (z.2.2.1 + 1) := by rw [hstab, hrow1]
                _ ≤ rowSum off z''.2.1 z''.2.2.1 := rowSum_mono _ _ hx.2.1
    · exact exit z hz hq (by omega)

/-! ### The search, from a trail-clean store

`BfsQSynth.bfsQS_reached`'s `htail`, re-run against `drainLoop_touched`:
what the seed and the drain do, with no fill in front of them. -/

/-- The seed and the tuple steps: everything the drain does not pay
for, and the *only* constant in the turn's budget. -/
def searchK : ACost String ℕ :=
  cu Currency.aset + cu Currency.aset + cu Currency.aget + cu Currency.ite + cu Currency.const
    + cu Currency.skip + cu Currency.skip + cu Currency.skip

/-- **The search, priced at what it touched.** From a distance array
that is all-sentinel, the seed and the drain leave the queue invariant at
`hd = tl`, with the source at slot `0`, for one `iter popC` per queue
entry, one `iter scanC` per adjacency slot the pops scanned, and a
constant. `n` and `ns` occur nowhere in the price. -/
theorem searchQ_touched {n ns d : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}
    {src : ℕ} {D Q : List ℕ} (hc : Csr n ns G off tgt alv) (hsrc : src < n)
    (hDlen : D.length = n) (hQlen : Q.length = n) (hfill : ∀ j, j < n → D[j]! = d + 1) :
    searchQ n d src off tgt alv D Q
      ≤ NRest.spec
          (fun z' : St => (Fr n d G alv ⟨src, hsrc⟩ z'.1 z'.2.1 z'.2.2.1 z'.2.2.2 ∧
              z'.2.2.2 ≤ z'.2.2.1) ∧ z'.2.1[0]! = src)
          (fun z' => liftACost (E2 (iter popC) (iter scanC) z'.2.2.1
            (rowSum off z'.2.1 z'.2.2.1) + cu Currency.«while» + searchK)) := by
  have halv : src < alv.length := by rw [hc.shape.2.1]; exact hsrc
  have hq0 : (Q.set 0 src)[0]! = src := by
    rw [get!_set Q 0 src 0 (by omega), if_pos rfl]
  have hseed := Fr.seed (n := n) (d := d) (G := G) (alv := alv) (s := ⟨src, hsrc⟩)
    hDlen hQlen hfill
  have hdrain := drainLoop_touched (d := d) (s := ⟨src, hsrc⟩) hc src n
    (D.set src 0, Q.set 0 src, 0, if 0 < alv[src]! then 1 else 0) hseed hq0 (by simp)
  have hrow0 : rowSum off (Q.set 0 src) 0 = 0 := by simp [rowSum]
  -- the branch that sets the tail, and the tuple that builds the state
  have hstep : ∀ tl : ℕ, tl = (if 0 < alv[src]! then 1 else 0) →
      (NRest.bindT (pack4 (D.set src 0) (Q.set 0 src) 0 tl) fun st =>
        drainLoop n d (d + 1) off tgt alv st)
        ≤ NRest.spec
            (fun z' : St => (Fr n d G alv ⟨src, hsrc⟩ z'.1 z'.2.1 z'.2.2.1 z'.2.2.2 ∧
                z'.2.2.2 ≤ z'.2.2.1) ∧ z'.2.1[0]! = src)
            (fun z' => (irUnit Currency.skip + (irUnit Currency.skip + irUnit Currency.skip))
              + liftACost (E2 (iter popC) (iter scanC) z'.2.2.1
                (rowSum off z'.2.1 z'.2.2.1) + cu Currency.«while»)) := by
    rintro tl rfl
    rw [pack4_bindT]
    refine le_trans (NRest.consume_mono (le_trans hdrain (spec_mono (fun z' hx => hx.1)
      fun z' hx => le_of_eq ?_)) le_rfl) (le_of_eq (Sepref.consume_spec _ _ _))
    rw [Nat.sub_zero, hrow0, Nat.sub_zero]
  show NRest.bindT (mopAset D src 0) _ ≤ _
  simp only [mopAset_def, mopAget_def, NRest.assert_pos (show src < D.length by omega),
    NRest.assert_pos (show 0 < Q.length by omega), NRest.assert_pos halv,
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
  simp only [searchK, liftACost_add, liftACost_cu]
  ac_rfl

/-! ## 6. The turn

The deliverable: one invocation from a trail-clean store, its answers,
its store handed back clean, and a price with no carrier in it. -/

/-- Composing a specification with a *deterministic* continuation whose
value and price the caller knows at every result the specification
admits. The turn's tail is of that shape — three `consume (returnT …)`
steps — so the whole assembly is one application. -/
theorem bindT_spec_le_fn {α β : Type} (P : α → Prop) (T : α → ECost) (g : α → NRest β ECost)
    (f : α → β) (c : α → ECost) (P' : β → Prop) (Tot : β → ECost)
    (hg : ∀ x, P x → g x = NRest.consume (NRest.returnT (f x)) (c x))
    (hP : ∀ x, P x → P' (f x)) (hc : ∀ x, P x → T x + c x ≤ Tot (f x)) :
    NRest.bindT (NRest.spec P T) g ≤ NRest.spec P' Tot := by
  rw [NRest.spec, NRest.bindT_rest_eq_iSup]
  refine iSup_le fun x => ?_
  by_cases hx : P x
  · rw [if_pos hx, NRest.consumeB_coe, hg x hx, NRest.consume_consume]
    exact consume_returnT_le_spec (hP x hx) (hc x hx)
  · rw [if_neg hx, NRest.consumeB_bot]
    exact bot_le

/-- **What a turn delivers.** The store is trail-clean again; the
queue's prefix enumerates, once each, exactly the vertices the search put
within the cap (`BfsQ.QReached`); and the answer array holds their
distances in the *engine of record's* own postcondition vocabulary
(`BfsQ.QPost`), the distance array itself having been given back to the
sentinel. Nothing in this statement mentions a cluster, a cover or any
other consumer's vocabulary. -/
def TurnPost (n d src : ℕ) (G : SimpleGraph (Fin n)) (alv : List ℕ) (hsrc : src < n)
    (r : HSt × List ℕ × ℕ) : Prop :=
  r.1.1 = List.replicate n (d + 1) ∧ r.1.2.1.length = n ∧ r.2.1.length = n ∧ r.2.2 ≤ n ∧
    ∃ D : List ℕ, QPost n d src G alv hsrc D ∧ QReached n d D r.2.1 r.2.2 ∧
      ∀ k, k < max r.2.2 1 → r.1.2.1[k]! = D[r.2.1[k]!]!

/-- Everything the turn pays outside its three counted quantities. -/
def turnK : ACost String ℕ :=
  cu Currency.«while» + searchK + cu Currency.skip + cu Currency.skip

/-- **The turn's price.** `T` queue entries, `S` scanned adjacency
slots, `max T 1` harvested slots, and a constant. **It does not take
`n`** — the carrier-freedom is a reading of the signature, exactly as it
is for `Iicf.resetCost` and `TrailRecursion.clusterCost`. -/
def turnCost (T S : ℕ) : ACost String ℕ :=
  T • iter popC + S • iter scanC + (max T 1) • iter hcC + turnK

/-- The tail's value at a search result. -/
def turnVal (d : ℕ) (O : List ℕ) (x : St) : HSt × List ℕ × ℕ :=
  (hcRun (d + 1) x.2.1 (max x.2.2.2 1) (x.1, O, 0), x.2.1, x.2.2.2)

/-- …and the tail's price. -/
def turnTailCost (m : ℕ) : ACost String ℕ :=
  hcC + hcLoopCost (m - 1) + cu Currency.skip + cu Currency.skip

theorem turnTailCost_eq (m : ℕ) :
    turnTailCost m + (cu Currency.«while» + searchK) = (max m 1) • iter hcC + turnK := by
  rw [show max m 1 = (m - 1) + 1 by omega]
  simp only [turnTailCost, hcLoopCost, turnK, iter, succ_nsmul]
  abel

/-- The turn's whole price, assembled: the search's, plus the tail's, is
`turnCost` at the two counted quantities. -/
theorem turn_cost_split (m S : ℕ) :
    E2 (iter popC) (iter scanC) m S + cu Currency.«while» + searchK + turnTailCost m
      = turnCost m S := by
  rw [show turnCost m S = m • iter popC + S • iter scanC
      + ((max m 1) • iter hcC + turnK) from by rw [turnCost]; abel,
    ← turnTailCost_eq]
  simp only [E2]
  abel

section Turn

variable {n ns d : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ} {src : ℕ}

/-- **The turn, priced at the touched set.** From a trail-clean distance
array and two arrays of the right length holding anything at all, the
turn reads the masked distances of everything within the cap, leaves them
in `out` indexed by the queue's prefix, and hands the distance array back
all-sentinel — for `tl` pops, `rowSum off q tl` scanned slots,
`max tl 1` harvested slots, and a constant. Both counted quantities are
read off the result; the carrier size occurs nowhere. -/
theorem turnQ_touched {D Q O : List ℕ} (hc : Csr n ns G off tgt alv) (hsrc : src < n)
    (hD : D = List.replicate n (d + 1)) (hQlen : Q.length = n) (hOlen : O.length = n) :
    turnQ n d src off tgt alv D Q O
      ≤ NRest.spec (TurnPost n d src G alv hsrc)
          (fun r => liftACost (turnCost r.2.2 (rowSum off r.2.1 r.2.2))) := by
  have hDlen : D.length = n := by rw [hD]; simp
  have hfill : ∀ j, j < n → D[j]! = d + 1 := by
    intro j hj
    rw [hD, getElem!_pos _ j (by simpa using hj)]
    simp
  have hn0 : 0 < n := by omega
  -- what the tail does at a search result, and what it costs
  have htail : ∀ x : St,
      ((Fr n d G alv ⟨src, hsrc⟩ x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ x.2.2.2 ≤ x.2.2.1) ∧
        x.2.1[0]! = src) →
      (NRest.bindT (hcF (d + 1) x.2.1 (x.1, O, 0)) fun s1 =>
        NRest.bindT (hcLoop n (d + 1) x.2.2.2 x.2.1 s1) fun s2 =>
          NRest.bindT (mopPair x.2.1 x.2.2.2) fun p => mopPair s2 p)
        = NRest.consume (NRest.returnT (turnVal d O x))
            (liftACost (turnTailCost x.2.2.2)) := by
    rintro x ⟨⟨hfr, hle⟩, hq0⟩
    have hhd : x.2.2.1 = x.2.2.2 := le_antisymm hfr.hdle hle
    have htn : x.2.2.2 ≤ n := hfr.tl_le
    have hqlt : ∀ k, k < x.2.2.2 → x.2.1[k]! < n := fun k hk => hfr.qlt k hk
    have h1 : (0 : ℕ) < x.2.1.length := by rw [hfr.qlen]; omega
    have h2 : x.2.1[(0 : ℕ)]! < x.1.length := by rw [hfr.dlen, hq0]; exact hsrc
    have h3 : (0 : ℕ) < O.length := by rw [hOlen]; omega
    have hs1 : (hcStep (d + 1) x.2.1 (x.1, O, 0)).1.length = n := by
      show (x.1.set _ _).length = n; simpa using hfr.dlen
    have hs2 : (hcStep (d + 1) x.2.1 (x.1, O, 0)).2.1.length = n := by
      show (O.set _ _).length = n; simpa using hOlen
    rw [hcF_eq (d + 1) x.2.1 (x.1, O, 0) h1 h2 h3, bindT_unitT,
      hcLoop_value n (d + 1) x.2.2.2 x.2.1 hfr.qlen htn hqlt n
        (hcStep (d + 1) x.2.1 (x.1, O, 0)) hs1 hs2 (by omega),
      bindT_unitT, mopPair_def, bindT_unitT, mopPair_def,
      show (hcStep (d + 1) x.2.1 (x.1, O, 0)).2.2 = 1 from rfl,
      hcRun_max, NRest.consume_consume, NRest.consume_consume, NRest.consume_consume]
    congr 1
    simp only [turnTailCost, liftACost_add, liftACost_cu]
  -- the postcondition, and the price
  have hpost : ∀ x : St,
      ((Fr n d G alv ⟨src, hsrc⟩ x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ x.2.2.2 ≤ x.2.2.1) ∧
        x.2.1[0]! = src) → TurnPost n d src G alv hsrc (turnVal d O x) := by
    rintro x ⟨⟨hfr, hle⟩, hq0⟩
    have hhd : x.2.2.1 = x.2.2.2 := le_antisymm hfr.hdle hle
    rw [hhd] at hfr
    have hqr : QReached n d x.1 x.2.1 x.2.2.2 := hfr.qReached hq0
    obtain ⟨hqlt, hqinj, hqiff⟩ := hqr
    have htn : x.2.2.2 ≤ n := hfr.tl_le
    have hmax : max x.2.2.2 1 ≤ n := by omega
    obtain ⟨hh1, hh2, hh3⟩ := hcRun_spec (d + 1) x.2.1 n (max x.2.2.2 1) (x.1, O, 0)
      hfr.dlen hOlen (by simpa using hmax) (by simpa using hqlt) (by simpa using hqinj)
    obtain ⟨hl1, hl2⟩ := hcRun_len (d + 1) x.2.1 (max x.2.2.2 1) (x.1, O, 0)
    simp only [TurnPost, turnVal]
    refine ⟨?_, by rw [hl2]; exact hOlen, hfr.qlen, htn, x.1, ⟨hfr.dlen, fun v k hk =>
      hfr.dist_le_iff v hk⟩, ⟨hqlt, hqinj, hqiff⟩, fun k hk => hh1 k (Nat.zero_le k) (by simpa using hk)⟩
    refine Sepref.Iicf.eq_replicate_of_forall (by rw [hl1]; exact hfr.dlen) fun w hw => ?_
    rw [hh3 w hw]
    by_cases hex : ∃ k, 0 ≤ k ∧ k < 0 + max x.2.2.2 1 ∧ x.2.1[k]! = w
    · rw [if_pos hex]
    · rw [if_neg hex]
      have hnd : ¬ x.1[w]! ≤ d := fun hcon => hex (by
        obtain ⟨k, hk, hkw⟩ := (hqiff w hw).mp hcon
        exact ⟨k, Nat.zero_le k, by simpa using hk, hkw⟩)
      have := hfr.cap w hw
      show x.1[w]! = d + 1
      omega
  show NRest.bindT (searchQ n d src off tgt alv D Q) _ ≤ _
  refine le_trans (NRest.bindT_mono (searchQ_touched hc hsrc hDlen hQlen hfill) fun _ => le_rfl)
    (bindT_spec_le_fn _ _ _ (turnVal d O) (fun x => liftACost (turnTailCost x.2.2.2)) _ _
      htail hpost fun x hx => le_of_eq ?_)
  show liftACost (E2 (iter popC) (iter scanC) x.2.2.1
      (rowSum off x.2.1 x.2.2.1) + cu Currency.«while» + searchK)
        + liftACost (turnTailCost x.2.2.2)
      = liftACost (turnCost x.2.2.2 (rowSum off x.2.1 x.2.2.2))
  have hhd : x.2.2.1 = x.2.2.2 := le_antisymm hx.1.1.hdle hx.1.2
  rw [hhd, ← liftACost_add, turn_cost_split]

/-! ### The turn at a constant budget

`turnQ_touched`'s price is a function of the result, which is the sharp
statement but not the one a caller composes with. A caller who knows how
much one turn can touch — for ND-MC's cover that is the cluster's own
combinatorics — supplies the two bounds and gets a constant. -/

/-- Two bounds on what one turn touches: the length of the queue it
leaves, and the adjacency slots its pops scanned. -/
def TouchBound (n d src : ℕ) (G : SimpleGraph (Fin n)) (alv off : List ℕ) (hsrc : src < n)
    (T S : ℕ) : Prop :=
  ∀ r : HSt × List ℕ × ℕ, TurnPost n d src G alv hsrc r →
    r.2.2 ≤ T ∧ rowSum off r.2.1 r.2.2 ≤ S

theorem turnCost_mono {T T' S S' : ℕ} (hT : T ≤ T') (hS : S ≤ S') :
    turnCost T S ≤ turnCost T' S' := by
  refine ACost.le_def.mpr fun k => ?_
  have hmax : max T 1 ≤ max T' 1 := by omega
  simp only [turnCost, ACost.toFun_add, ACost.toFun_nsmul, smul_eq_mul]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ hT)
    (Nat.mul_le_mul_right _ hS)) (Nat.mul_le_mul_right _ hmax)) le_rfl

theorem liftACost_mono {κ : Type} {a b : ACost κ ℕ} (h : a ≤ b) : liftACost a ≤ liftACost b :=
  ACost.le_def.mpr fun k => by
    simp only [toFun_liftACost]
    exact_mod_cast ACost.le_def.mp h k

/-- **The turn, at a constant budget.** -/
theorem turnQ_bounded {D Q O : List ℕ} {T S : ℕ} (hc : Csr n ns G off tgt alv) (hsrc : src < n)
    (hD : D = List.replicate n (d + 1)) (hQlen : Q.length = n) (hOlen : O.length = n)
    (hb : TouchBound n d src G alv off hsrc T S) :
    turnQ n d src off tgt alv D Q O
      ≤ NRest.spec (TurnPost n d src G alv hsrc) (fun _ => liftACost (turnCost T S)) :=
  le_trans (turnQ_touched hc hsrc hD hQlen hOlen)
    (spec_mono (fun _ hx => hx) fun r hr =>
      liftACost_mono (turnCost_mono (hb r hr).1 (hb r hr).2))

end Turn

/-! ## 7. Re-entrancy: `k` turns from one store, `Σ` prices, one init

The turn's postcondition contains its precondition — the distance array
is all-sentinel at both ends — so turns chain, and the `O(n)` fill that
`BfsQSynth.bfsQS` pays *per invocation* is paid **once**, outside the
chain. This is the shape the ND-MC cover turn consumes.

`use` is the consumer's readout of one turn's answers: it reads `out`
and the queue prefix and folds them into whatever it is accumulating.
It is free at this layer because it is not part of *this* program — the
bridge wave supplies a real emission pass over the prefix and pays for
it there, and the point of the statement is that the pass is over the
prefix and not over the carrier. -/

section Reentrant

variable {n ns d : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}

/-- The store the turns thread: distance array, queue, answer array.
The answer array of one turn becomes the scratch of the next — junk in,
junk out (B4b/D-d). -/
abbrev Store : Type := List ℕ × List ℕ × List ℕ

/-- **The loop-carried precondition**, which is also the
postcondition. -/
def StoreClean (n d : ℕ) (st : Store) : Prop :=
  st.1 = List.replicate n (d + 1) ∧ st.2.1.length = n ∧ st.2.2.length = n

/-- **`k` turns, one per source.** -/
noncomputable def turnsQ {γ : Type} (n d : ℕ) (off tgt alv : List ℕ)
    (use : γ → ℕ → (HSt × List ℕ × ℕ) → γ) :
    List ℕ → Store × γ → NRest (Store × γ) ECost
  | [], z => NRest.returnT z
  | src :: more, z =>
      bindT (turnQ n d src off tgt alv z.1.1 z.1.2.1 z.1.2.2) fun r =>
        turnsQ n d off tgt alv use more (((r.1.1, r.2.1, r.1.2.1) : Store), use z.2 src r)

theorem returnT_le_spec {α : Type} {x : α} {P : α → Prop} {T : α → ECost} (hP : P x)
    (h0 : (0 : ECost) ≤ T x) : NRest.returnT x ≤ NRest.spec P T := by
  rw [← NRest.consume_zero (NRest.returnT x)]
  exact consume_returnT_le_spec hP h0

/-- **The Σ-form.** `k` successive turns from one trail-clean store cost
`Σ_k turnCost T_k S_k`, hand the store back trail-clean, and carry the
consumer's fold invariant. Neither `turnCost` nor the sum takes the
carrier size; the only `O(n)` charge in a driver built on this is the
one fill that establishes `StoreClean` before the first turn. -/
theorem turnsQ_touched {γ : Type} {use : γ → ℕ → (HSt × List ℕ × ℕ) → γ}
    (hc : Csr n ns G off tgt alv) (Inv : γ → Prop) (T S : ℕ → ℕ)
    (hstep : ∀ g src r, Inv g → (∀ hsrc : src < n, TurnPost n d src G alv hsrc r) →
      Inv (use g src r)) :
    ∀ (srcs : List ℕ), (∀ v ∈ srcs, v < n) →
      (∀ v ∈ srcs, ∀ hv : v < n, TouchBound n d v G alv off hv (T v) (S v)) →
      ∀ z : Store × γ, StoreClean n d z.1 → Inv z.2 →
        turnsQ n d off tgt alv use srcs z
          ≤ NRest.spec (fun z' => StoreClean n d z'.1 ∧ Inv z'.2)
              (fun _ => liftACost ((srcs.map fun v => turnCost (T v) (S v)).sum)) := by
  intro srcs
  induction srcs with
  | nil =>
    intro _ _ z hz hg
    exact returnT_le_spec ⟨hz, hg⟩ (by simp)
  | cons src more ih =>
    intro hlt hbd z hz hg
    have hsrc : src < n := hlt src (by simp)
    obtain ⟨hD, hQ, hO⟩ := hz
    have hb := hbd src (by simp) hsrc
    show NRest.bindT (turnQ n d src off tgt alv z.1.1 z.1.2.1 z.1.2.2) _ ≤ _
    refine le_trans (NRest.bindT_mono (turnQ_bounded hc hsrc hD hQ hO hb) fun _ => le_rfl)
      (le_trans (bindT_spec_le (TurnPost n d src G alv hsrc)
        (liftACost (turnCost (T src) (S src))) _
        (fun z' : Store × γ => StoreClean n d z'.1 ∧ Inv z'.2)
        (liftACost ((more.map fun v => turnCost (T v) (S v)).sum)) fun r hr => ?_)
        (le_of_eq ?_))
    · refine ih (fun v hv => hlt v (by simp [hv])) (fun v hv => hbd v (by simp [hv]))
        ((r.1.1, r.2.1, r.1.2.1), use z.2 src r) ⟨hr.1, hr.2.2.1, hr.2.1⟩
        (hstep z.2 src r hg fun _ => hr)
    · refine congrArg (NRest.spec _) (funext fun _ => ?_)
      simp only [List.map_cons, List.sum_cons, liftACost_add]

end Reentrant

end Drain

/-! ## 8. The acceptance criterion — the price is the touched set

`turnCost` takes two arguments and neither is the carrier, so "the same
search costs the same at every carrier size" is a reading of the
signature rather than a theorem — exactly as it is for
`Iicf.resetCost k` (`treset_cost_touched_only`) and for
`TrailRecursion.clusterCost`. What *is* checked below is the arithmetic
and the two runs. -/

/-- The turn's price in IMP+ time units: `44` per queue entry, `40` per
scanned adjacency slot, `22` per harvested slot, and `24`. Computed from
the per-iteration accounts by `decide +kernel`, not tuned. -/
theorem cash_turnCost (T S : ℕ) :
    Codegen.cash (turnCost T S) = 44 * T + 40 * S + 22 * (max T 1) + 24 := by
  rw [turnCost, Codegen.cash_add, Codegen.cash_add, Codegen.cash_add,
    BfsQSynth.cash_nsmul, BfsQSynth.cash_nsmul, BfsQSynth.cash_nsmul,
    show Codegen.cash (iter popC) = 44 from by decide +kernel,
    show Codegen.cash (iter scanC) = 40 from by decide +kernel,
    show Codegen.cash (iter hcC) = 22 from by decide +kernel,
    show Codegen.cash turnK = 24 from by decide +kernel]
  ring

/-- The number the turn is priced at, on a run: its queue length and the
slots its pops scanned. -/
def turnCash (off : List ℕ) (r : HSt × List ℕ × ℕ) : ℕ :=
  Codegen.cash (turnCost r.2.2 (rowSum off r.2.1 r.2.2))

/-! ### The same search at two carrier sizes

The five-vertex arena, and then the *same four-vertex path* sitting
inside a carrier of six thousand: 5 995 extra isolated vertices, the same
six adjacency slots, the same source, the same cap. -/

def bigN : ℕ := 6000
def bigOff : List ℕ := [0, 1, 3, 5, 6] ++ List.replicate (bigN - 4) 6
def bigAlv : List ℕ := List.replicate bigN 1

def bigTurn (d src : ℕ) : HSt × List ℕ × ℕ :=
  turnTw bigN d src bigOff demoTgt bigAlv (cleanD bigN d) (junkA bigN) (junkA bigN)

-- Same answers…
#guard readPrefix (bigTurn 3 0) = readPrefix (demoTurn 3 0 1)
#guard readPrefix (bigTurn 3 0) = [(0, 0), (1, 1), (2, 2), (3, 3)]
-- …same two counted quantities…
#guard (bigTurn 3 0).2.2 = (demoTurn 3 0 1).2.2
#guard rowSum bigOff (bigTurn 3 0).2.1 (bigTurn 3 0).2.2
  = rowSum demoOff (demoTurn 3 0 1).2.1 (demoTurn 3 0 1).2.2
-- …and therefore the same price, at a carrier 1 200 times larger.
#guard turnCash bigOff (bigTurn 3 0) = turnCash demoOff (demoTurn 3 0 1)
#guard turnCash demoOff (demoTurn 3 0 1) = 528

-- **What the engine of record charges for the same two runs.** Its
-- budget is `56·n + 40·ns + 33`, so it is a *thousandfold* worse at the
-- larger carrier for exactly the same search.
#guard BfsQSynth.bfsQK 5 6 = 553
#guard BfsQSynth.bfsQK 6000 6 = 336273
#guard BfsQSynth.bfsQK 5 6 - turnCash demoOff (demoTurn 3 0 1) = 25
#guard 600 * turnCash bigOff (bigTurn 3 0) < BfsQSynth.bfsQK 6000 6

-- **Negative control 1.** The turn's price is not covered by a budget
-- one pop short, and the check can tell.
/--
error: Expression
  decide (turnCash demoOff (demoTurn 3 0 1) ≤ 100)
did not evaluate to `true`
-/
#guard_msgs in
#guard turnCash demoOff (demoTurn 3 0 1) ≤ 100

-- **Negative control 2.** The price does *not* track the carrier: the
-- two runs above are the same search, and asserting that the larger one
-- costs more is false.
/--
error: Expression
  decide (turnCash demoOff (demoTurn 3 0 1) < turnCash bigOff (bigTurn 3 0))
did not evaluate to `true`
-/
#guard_msgs in
#guard turnCash demoOff (demoTurn 3 0 1) < turnCash bigOff (bigTurn 3 0)

/-! ### The charge is per *reached vertex*, not per offer

`IicfTrailArray`'s R0/D-g records that its trail charges once per
*write*, because its push is unconditional, so a repeated index inside
one arena is charged twice. This trail does not: the push is the
relaxation, and the `du = sent` test makes it at most once per vertex —
which is `Fr.qinj`. The demo arena exhibits the difference. Vertex `1`
is offered by `0` and again by `2`; vertex `2` by `1` and by `3`. The
scan therefore visits **six** slots and the harvest **four**. -/

#guard rowSum demoOff (demoTurn 3 0 1).2.1 (demoTurn 3 0 1).2.2 = 6
#guard max (demoTurn 3 0 1).2.2 1 = 4
#guard (readPrefix (demoTurn 3 0 1)).map (fun p => p.1) = [0, 1, 2, 3]
-- …so the harvested slots are strictly fewer than the offers, and the
-- prefix names each vertex once.
#guard (readPrefix (demoTurn 3 0 1)).length
  < rowSum demoOff (demoTurn 3 0 1).2.1 (demoTurn 3 0 1).2.2
#guard ((readPrefix (demoTurn 3 0 1)).map (fun p => p.1)).eraseDups
  = (readPrefix (demoTurn 3 0 1)).map (fun p => p.1)

-- **Negative control 3.** The prefix is not the whole carrier: with the
-- mask cutting the path at vertex 2, it is two slots, not five.
/--
error: Expression
  decide ((readPrefix (demoTurn 3 0 0)).length = 5)
did not evaluate to `true`
-/
#guard_msgs in
#guard (readPrefix (demoTurn 3 0 0)).length = 5

/-! ## 9. The new loop, synthesized

The search half of a turn is `BfsQSynth.bfsQSynth_impl` verbatim minus
its fill — landed capital, not re-derived here. The one *new* program is
the harvest-and-clean pass, and it goes through `sepref_synth`
mechanically: one command, no bespoke tactic work, no hand-written frame
clause, and the two-array loop state that P7/D-ba fixed. -/

set_option maxHeartbeats 1000000 in
sepref_synth hcSynth (n sent tl : ℕ) (Q : List ℕ) (s₀ : HSt) :
  hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ natAssn) s₀ ("dist", "out", "j") ∗
      hnCtxt arrayAssn Q "q" ∗ hnCtxt natAssn tl "tl" ∗ hnCtxt natAssn sent "sent" ∗
      hnCtxt natAssn 1 "one" ∗ junkCell "v" ∗ junkCell "w")
    _ _ ("dist", "out", "j") (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
    (hcLoop n sent tl Q s₀)

-- The synthesized program, pinned. Read the vertex, read its distance,
-- write the answer, restore the sentinel, advance.
#guard hcSynth_impl =
  Com.while (Cond.lt (Operand.cell "j") (Operand.cell "tl"))
    ((Com.aget "v" "q" "j").seq
      ((Com.aget "w" "dist" "v").seq
        ((Com.aset "out" "j" "w").seq
          ((Com.aset "dist" "v" "sent").seq
            ((Com.binop Imp.Bop.add "j" "j" "one").seq (Com.skip.seq Com.skip))))))

/-- The pass's synthesis at its own value and price: `hcLoop_value`
composed with the `Com` above. What the machine program leaves is
`hcRun`'s answer array and its restored distance array, for
`hcLoopCost` — a function of the prefix alone. -/
theorem hcSynth' (n sent tl : ℕ) (Q : List ℕ) (s : HSt) (hQ : Q.length = n) (htn : tl ≤ n)
    (hqlt : ∀ k, k < tl → Q[k]! < n) (hd : s.1.length = n) (hOu : s.2.1.length = n)
    (hfuel : tl - s.2.2 ≤ n) :
    ∃ Γ' : Assn,
      hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ natAssn) s ("dist", "out", "j") ∗
          hnCtxt arrayAssn Q "q" ∗ hnCtxt natAssn tl "tl" ∗ hnCtxt natAssn sent "sent" ∗
          hnCtxt natAssn 1 "one" ∗ junkCell "v" ∗ junkCell "w")
        hcSynth_impl Γ' ("dist", "out", "j") (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
        (NRest.consume (NRest.returnT (hcRun sent Q (tl - s.2.2) s))
          (liftACost (hcLoopCost (tl - s.2.2)))) := by
  have h := hcSynth n sent tl Q s
  rw [hcLoop_value n sent tl Q hQ htn hqlt n s hd hOu hfuel] at h
  exact ⟨_, h⟩

/-! ## 10. Axioms -/

/-- info: 'Lax13Proofs.Refine.BfsQTrail.drainLoop_touched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms drainLoop_touched

/-- info: 'Lax13Proofs.Refine.BfsQTrail.hcRun_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hcRun_spec

/-- info: 'Lax13Proofs.Refine.BfsQTrail.searchQ_touched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms searchQ_touched

/-- info: 'Lax13Proofs.Refine.BfsQTrail.turnQ_touched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms turnQ_touched

/-- info: 'Lax13Proofs.Refine.BfsQTrail.turnQ_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms turnQ_bounded

/-- info: 'Lax13Proofs.Refine.BfsQTrail.turnsQ_touched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms turnsQ_touched

/-- info: 'Lax13Proofs.Refine.BfsQTrail.cash_turnCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cash_turnCost

/-! ## 11. Telemetry, and the cut

**What was reused, and what was re-derived.** Reused verbatim, not
restated: `BfsQ`'s whole graph-theoretic core — `Fr` with its fourteen
clauses, `relax`, `complete`, `dist_le_iff`, `pop`, `popSkip`, `seed`,
`qReached`, `tl_eq_zero_of_dead`, the scan invariant `SInv` and its
tiling, `popF_le`, `Csr`/`Shape`, `QPost`, `QReached`, the cost accounts
`popC`/`scanC`/`iter`/`rowSum`; and `BfsQSynth`'s `mopSucc` with its
rule. Re-derived, and only because the trail substitution forces it:
the drain's *cost* induction (`drainLoop_touched`, ≈90 lines — the same
induction as `drainLoop_le'` with a difference cost and two extra
postcondition clauses) and the seed's assembly (`searchQ_touched`,
≈45 lines, `bfsQS_reached`'s `htail` against the new drain). New
mathematics: the harvest-and-clean pass (`hcRun_spec`, ≈50 lines) and
the cost algebra (≈40).

**Cost constants.** `turnCost T S = T • iter popC + S • iter scanC +
(max T 1) • iter hcC + turnK`, cashing to `44·T + 40·S + 22·max(T,1) +
24` IMP+ time units (`cash_turnCost`, `decide +kernel`). The engine of
record's `bfsQK n ns = 56·n + 40·ns + 33`. On §8's two runs of the
*same* four-vertex search: this turn 528 at both carriers, the engine
553 at `n = 5` and 336 273 at `n = 6000`.

**Hand-written frame clauses: 0.** The two `ac_rfl`s (in `hcF_eq` and
in the drain's `hcost`) are on cost sums (`ECost`, an `AddCommMonoid`),
under a `congr 1`, never on `∗`. §9's synthesis is one `sepref_synth`
command with no frame clause and no bespoke tactic.

**Tower additions: 3 lemmas**, all in this file rather than in
`Sepref/IrLoop.lean` because they have one consumer so far —
`bindT_spec_le'` (the continuation's cost may depend on its result),
`bindT_spec_le_fn` (composing with a deterministic continuation) and
`returnT_le_spec`. Each is four to six lines and program-independent.

**The cut, stated precisely.** The abstract layer is complete: program,
correctness in `bfsQ_spec`'s own postcondition vocabulary
(`QPost` + `QReached`, both landed), carrier-free cost, and the
re-entrant Σ-form. At the *machine* layer, §9 synthesizes the one new
loop and pins its `Com`; the search half is `bfsQSynth_impl` minus its
leading `while`, which exists. What is **not** in this wave is the
whole-turn `sepref_synth` and the `Reasoning.Spec` export that
`BfsQSynth` §12–§13 build for `bfsQ_spec` — the bounds pass
(`BigStep.bigStepB_of_inv` annotation, 560 lines for the engine of
record) and the cashing chain. Those are mechanical against this file's
abstract bound but they are a wave of their own.

**What the ND-MC bridge wave needs.**
1. `turnQ_bounded` is the consumable form: supply `TouchBound n d src G
   alv off hsrc T S` from the cluster's own combinatorics — `T` bounds
   the reached count, `S` the adjacency slots those reached vertices
   own — and one turn costs `turnCost T S`.
2. `turnsQ_touched` is the driver form: one `StoreClean` established by
   a single `Iicf.tinitProg`-style fill before the loop, then `Σ_k
   turnCost (T src_k) (S src_k)`; the fold invariant `Inv` is where the
   cover's emission accumulates.
3. Two small pieces are left for the bridge because they belong to the
   consumer's vocabulary, not to this file's: (a) `T` and `S` in terms
   of `Bfs.WD` — `max tl 1` is *exactly* the number of vertices within
   the cap (`TurnPost`'s `QReached` plus `QPost` give the bijection, the
   counting argument is ≈30 lines); (b) the emission pass over
   `q[0 … max tl 1)` and `out[0 … max tl 1)`, which is what `use`
   stands for in `turnsQ` and which the bridge must pay for itself.
4. If the whole-turn `Com` is wanted, `turnQ`'s harvest-and-clean state
   is currently applied to a *literal tuple* `(st.1, O, 0)`; the loop
   itself is fine (§9), and the composition is `BfsQSynth`'s own
   `pack4`/`pack3` idiom, a cost-only change of two `ir.skip`.

**B4b/D-e — the whole-turn synthesis was attempted and it stalls; the
measurement, not a workaround.** One `sepref_synth` on `turnQ` with the
23-cell precondition `bfsQSynth` uses plus `"out"`, at
`maxHeartbeats 4000000`: **21 min 33 s to a deterministic `isDefEq`
timeout**, no `Com`. That is the shape of P7/D-bg — a frame match with
an open relator — not a heartbeat shortage, and item 4 above is the
suspect: `hcF` applied to a literal tuple gives the operator phase three
destinations to solve at once where `pack3` would fix them. The
harvest-and-clean loop *alone* synthesizes in **≈8 s** (§9), and
`bfsQSynth` itself takes ≈49 s, so the stall is in the composition and
not in either half. Recorded here rather than papered over, per the
design note's honesty rule; the bridge wave should try the `pack3` first
and re-measure. -/

end BfsQTrail

end Lax13Proofs.Refine
