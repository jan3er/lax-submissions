# Vertex cover, rung B (1.4656^k) — plan, rev 1

Date: 2026-07-28, ~03:00. Rung A (fib) is fully discharged
(`Lax15Proofs.VCMain.exists_fibTime_program_vertexCover`, c = 90300,
commit 12fddcc), well inside VF7's margin, so this second campaign in
the **same submission Lax15** proceeds per `vc-fib-plan.md` VF7: a
*second* theorem concept with a named recurrence. Everything in
`vc-fib-night-brief.md` still governs sessions; rung A's files
(`Residual/Config/Program/Phases/Loop/Main.lean` and the rung-A
concept) are **frozen — import, never edit**. New proof files use the
namespace `Lax15Proofs.VC3`; the concept file lands only at B6, so the
endorsement surface stays exactly rung A until the moment rung B is
proved. If the night ends mid-campaign, whatever is committed is
green, invisible to the surface, and logged.

## The statement (concept surface, fixed; file lands at B6)

New concept `concepts/Lax15/VertexCoverBranch.lean` (name may be
polished at B6):

```lean
/-- Leaf count of the search tree that branches, at budget `b ≥ 3`,
into budgets `b − 1` and `b − 3`: the take-the-vertex child and the
take-its-three-plus-neighbours child. Grows as `β^k` for the real
root `β ≈ 1.4656` of `x³ = x² + 1`. -/
def branchCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | (b + 3) => branchCount (b + 2) + branchCount b

open Classical in
axiom exists_branchTime_program_vertexCover :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k w : ℕ),
      ComputesInTime w p
        {x | EncodesParamInstance x n G k ∧ c * (x.length + k + 1) ≤ 2 ^ w}
        (fun _ => if G.vertexCoverNum ≤ (k : ℕ∞) then [1] else [0])
        (fun x => c * branchCount k * (x.length + 1))
```

Same admissible set, same `EncodesParamInstance` (Lax11's), same
output. `branchCount k ≤ fib (k+2)` (values 1,2,3,4,6,9,13,19,28 vs
1,2,3,5,8,13,21,34), so this strictly sharpens rung A from k = 3 on.
The def is the one new surface object; its docstring carries the
reading, the notes justify the initials (the exact leaf counts at
budgets 0,1,2 under the algorithm below).

## The algorithm (delta from rung A; fixed)

Same read phase, same arrays/stacks/trail, same push/flip/pop blocks —
B3 must **reuse rung A's `flipFrame`, `popFrame`, and read-phase `Com`
defs verbatim** so S4's `rowLoop_run`/`unwind_run`/`flipFrame_eq`/
`popFrame_eq` apply unchanged. New arrays: `vis` (extent `n`), `q`
(queue, extent `n`), scalars `head`, `tl`, `s`, `tog`, `t2` plus rung
A's. Two changed/new blocks:

- **descend scan (deg-3 test)**: same CSR pass, per-owner registers
  now `seen ∈ {0,1,2}`, `t1`, `t2`, `cnted` dropped (no `ro`). On
  unmarked owner `u`, unmarked slot target `w`: if `seen = 0`:
  `t1 := w, seen := 1`; else if `w = t1`: skip; else if `seen = 1`:
  `t2 := w, seen := 2`; else if `w = t2`: skip; else (third distinct
  target): `found := 1, v := u` (first such owner; keep scanning is
  NOT needed here — no `ro` — but exiting early needs the VC3
  counter-forcing idiom; either is acceptable, pick what proves
  cleanest and document it).
- **solver block** (descend, ¬found — every unmarked vertex has ≤ 2
  distinct unmarked neighbours): clear `vis` (one pass `0..n−1`);
  `s := 0`; sweep roots `r = 0..n−1`: if `mark[r] = 0 ∧ vis[r] = 0`:
  `vis[r] := 1`, enqueue, `tog := 0`, drain: dequeue `u`, scan its
  row with the same `seen/t1/t2` dedup; for each *distinct* unmarked
  target `w`: edge-count once via `u < w` — toggle-halving: if
  `tog = 0` then `s := s + 1, tog := 1` else `tog := 0` (after `e`
  edges of the component, `s` grew by `⌈e/2⌉`); BFS: if `vis[w] = 0`:
  `vis[w] := 1`, enqueue. (A third distinct target during the solver
  cannot occur — ¬found; code skips it, the Run proof shows the
  branch unreachable.) Then: `s ≤ bud` → `ans := 1; mode := 2`; else
  `mode := 1`.
- **push** requires found (now: three distinct unmarked targets, so
  `3 ≤ resDeg`); found ∧ `bud = 0` → backtrack, as before.

Everything else is rung A verbatim. Still no multiplication; queue
and vis costs are `≤ numeral·(n + 2m + 1)` per solver call (each
vertex enqueued once — `vis` set before enqueue — and each row
scanned once per call).

## The mathematics (fixed; stress-tested on paper)

**Potential.** `g 0 = 1, g 1 = 2, g 2 = 3, g (b+3) = g (b+2) + g b`
(= the concept's `branchCount`); `f₃ b := 4 * g b − 3`, so
`f₃ = 1, 5, 9, 13, 21, 33, …`, monotone, ≥ 1, and
`f₃ (b+3) = f₃ (b+2) + f₃ b + 3`. `P₃` as in rung A with stored
phase-0 frames worth `f₃ (b_i − 3) + 2` (ℕ-sub). Drops, each ≥ 1:
- push at `b ≥ 3`: exact 1 by the recurrence;
- push at `b = 1`: `f₃ 1 − f₃ 0 − (f₃ 0 + 2) = 5 − 4 = 1`;
  at `b = 2`: `f₃ 2 − f₃ 1 − (f₃ 0 + 2) = 9 − 8 = 1`;
- feasible flip (`d ≤ b_i`, `d ≥ 3`): `f₃ (b_i − d) ≤ f₃ (b_i − 3)`,
  drop ≥ 1; infeasible flip: drop ≥ 2; pop/exits/leaves as rung A.
- init `P₃ = f₃ k + 1 ≤ 4 * g k`, so the concept shape
  `c * branchCount k * (|x|+1)` is exact.

**Invariant.** `J₃ := J ∧ (every phase-0 frame has
3 ≤ resDeg (P_i) v_i)`. Rung A's `J` and `Healthy` are *reused as
stated* (a deg-≥3 push satisfies the deg-≥2 health clause); the extra
clause is what feeds `d ≥ 3` to the flip drop, and is trivially
preserved (push creates it, flip discharges it, nothing else touches
frames). Transition lemmas: reuse the `J`-halves of S2's `step_*`
(project with `.1` / restate thinly), prove fresh `pot₃` drops; T1/T2
(solver leaves) take semantic guards `Ok G (marked) bud` /
`¬ Ok G (marked) bud` — `step_yes` is reusable verbatim, the solver
NO needs a plain-`¬Ok` variant.

**The solver lemma (the campaign's one genuinely new theorem).** For
the residual graph `R` (unmarked vertices, `G`-edges with both
endpoints unmarked — as a `SimpleGraph (Fin n)`:
`R.Adj a b := G.Adj a b ∧ a ∉ M ∧ b ∉ M`), with every unmarked vertex
of residual degree ≤ 2, and
`compCost := Σ_{C : R.ConnectedComponent} ⌈e_C / 2⌉` (`e_C` = number
of `R`-edges inside `C`; `⌈e/2⌉ = (e + 1) / 2` in ℕ):

    Ok G M b  ↔  compCost ≤ b

- **Lower bound** (→, contrapositive `b < compCost → ¬Ok`): a cover
  `S ⊇ M` meets every `R`-edge in `S \ M`; within one component each
  such vertex covers ≤ `resDeg ≤ 2` of its edges, so
  `e_C ≤ 2 · |(S \ M) ∩ C|`, hence `⌈e_C/2⌉ ≤ |(S \ M) ∩ C|`; sum
  over components (they partition the vertices, so the intersections
  are disjoint).
- **Upper bound** (←): **PROVED at B1 (`ok_of_compCost_le` in
  `Solver.lean`), with a corrected induction rule.** The rev-1 rule
  "delete any degree-2 vertex" is *false*: `⌈e₁/2⌉ + ⌈e₂/2⌉ + 1 ≤
  ⌈e_C/2⌉` fails at `e₁ = e₂ = 1` — deleting P₅'s middle vertex buys
  nothing. The proved rule: isolate the *neighbour of a degree-1
  vertex* if one exists; otherwise every degree in an edge-bearing
  component is 2 (per-component handshake `sum_degree_comp`, via
  `restrictComp` and mathlib's `sum_degrees_eq_twice_card_edges`)
  and any endpoint of an edge works. Deletion is edge-isolation
  (`isolate`: vertex kept, edges dropped, no `Fin n` re-indexing),
  so components compare through `liftComp`/`fiber`;
  `compCost'_isolate_succ_le` and `split_bound` carry the
  bookkeeping.
- **Scan transport** (extends S1's): three-distinct-slots ↔
  `3 ≤ resDeg` (per-vertex witness form, like
  `two_le_resDeg_of_slots`), and ¬found ↔ all unmarked resDeg ≤ 2
  (the `thinBlocks_iff` analogue at threshold 3).
- **Sweep transport**: machine `s` = `compCost` — the BFS invariant:
  processed roots' components are exactly the visited set; per
  component the dedup'd `u < w` count enumerates `e_C` once each;
  toggle-halving turns the enumeration into `⌈e_C/2⌉`. House pattern:
  the CC campaign (`CCSearch`/`CCSweep`) proved BFS component
  labelling on the same queue idiom — imitate its invariant shape.

## Milestones

- **B1 — the solver lemma, pure side** (`Lax15Proofs/Solver.lean`):
  `R`, `compCost`, lower bound, upper bound, scan-transport at
  threshold 3. **Two-session budget; this is the abort valve** — if
  the upper-bound induction is genuinely not landing by the end of
  session two, rung B is abandoned (log precisely; rung A ships).
- **B2 — potential and transitions** (`Lax15Proofs/Config3.lean`):
  `g`≡`branchCount` (proofs-side copy until B6 lands the concept;
  B6 swaps the def for the concept's and proves them equal or just
  uses the concept's), `f₃`, `P₃`/`stackPot₃`/`potN₃` + crossing,
  `J₃`, the eight transition wrappers (S2 `J`-halves + fresh drops).
- **B3 — program + smoke** (`Lax15Proofs/Program3.lean`): `vcf3Com`
  reusing rung A's blocks; smoke with `#guard` on: K₄ (k=2 no, 3
  yes), K₅ (k=3 no, 4 yes — exercises d=4), star K₁,₄ (k=1 yes), C₇
  (k=3 no, 4 yes — pure solver, odd cycle), C₄+C₆ disjoint (k=4 no,
  5 yes), triangle+P₃+C₄ (compCost 2+1+2: k=4 no, 5 yes), P₄ (k=1
  no — solver on paths), 2K₂ doubled-slots regression (linear
  steps), the `Repeats.lean` word, bull graph (triangle abc +
  pendants at a and b: cover {a, b}, so k=1 no, 2 yes — and every
  expected answer in this list must be re-derived by hand in a
  comment before it becomes a `#guard`), edgeless k=0,
  malformed non-crash. Step counts to the log; expect K-family
  counts to beat rung A's.
- **B4 — the two scan Run lemmas** (`Lax15Proofs/Phases3.lean`):
  `descendScan3_run` (found/¬found verdict at threshold 3) and
  `solve_run` (vis/queue/toggle BFS ⇒ `s = compCost`, cost ≤
  numeral·(n+2m+1)). `solve_run` is CC-sweep-sized: if it needs its
  own session, split here (B4a scan / B4b solver).
- **B5 — outer body** (`Lax15Proofs/Loop3.lean`): `outerBody3_run`,
  same shape and discipline as S5 (whose Lean traps are in the
  NIGHTLOG; reread them).
- **B6 — concept + loop + endgame** (`concepts/Lax15/
  VertexCoverBranch.lean` + `Lax15Proofs/Main3.lean`): the concept
  file verbatim from this plan (+ prose in the rung-A concept's
  register, cross-referencing it), concepts root import, loop
  `while_pot` over `P₃`, assembly (read phase reused), endgame with
  explicit constant, `example := rfl` identity check, `lean_verify`,
  both packages green.
- **B7 — wrap-up**: abstract/notes/README second-rung updates,
  `lax build`, NIGHTLOG morning block. No submit (VF8 stands).

## Watch items

- All rung-A watch items and S5's Lean traps apply verbatim.
- **Hard cutoff 06:00 local**: no new session after it; whatever is
  in flight finishes; if B6 has not landed, the surface stays rung-A
  and the log states exactly which B-milestones are green.
- The `seen/t1/t2` dedup must be identical in the deg-3 scan and the
  solver row scan — factor the row-scan `Com` into one def used
  twice if that keeps `Run` lemmas single-sourced.
- `⌈e/2⌉` in ℕ is `(e + 1) / 2` — Nat division by the literal 2 in
  *proofs* is fine (mathlib API), but never in the program (VF5: the
  machine has no division; that is what the toggle is for).
- `branchCount`'s B2 proofs-side copy and the B6 concept def must be
  definitionally identical (same equation shapes) so the endgame's
  `rfl` identity check survives.
