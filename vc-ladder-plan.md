# Vertex cover ladder — plan, rev 1

Goal: discharge `Lax11.VertexCover.exists_fptTime_program_vertexCover`
(the `2^k` bounded search tree) on the existing Lax11 tower, building
the branching idioms so that later rungs (`φ^k`, `1.4656^k`, …) are
reduction rules plus recurrence bookkeeping. Phase 1 (this document's
executable part) is the `2^k` discharge. Phases 2–3 are sketched at the
end and are **not** to be started without Jan: rung 2 changes the
concept surface.

The statement to prove, verbatim from
`concepts/Lax11/VertexCover.lean` (frozen — never edit concepts):

```lean
∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ),
  ComputesInTime p {x | EncodesInstance x n G k}
    (fun _ => if G.vertexCoverNum ≤ (k : ℕ∞) then [1] else [0])
    (fun x => c * 2 ^ k * (x.length + 1))
```

## Decision record

- **VC1 — no kit change.** `Run.while_pot` already takes `Φ : Env → ℕ`
  (full environment, arrays included) and is amortized with a drop-form
  conclusion. The branching argument is a *potential pattern* (VC4),
  not a new rule. Do not add rules to `Reasoning.lean` unless a proof
  forces it; harvest reusable stack lemmas into the kit only when rung
  2 confirms the shape.
- **VC2 — budget is depth.** In the `2^k` tree both children run at
  `b − 1`, so the budget needs no storage: invariant `bud + depth = k`,
  with `bud` a scalar and `depth` the stack pointer. Frames store only
  `(u, v, phase)`. (Dies at rung 2 — noted in Phase 2.)
- **VC3 — break by forcing counters.** IMP+ `Cond` is a single
  comparison, so loops exit early by assigning their counters to their
  bounds (`j := 2m; u := n`) when the scan finds an uncovered edge.
  House-compatible; the invariant carries the found-flag.
- **VC4 — the tree potential** (stress-tested by hand; the naive
  `4 * 2 ^ b` version fails — a push gains a unit and a phase flip
  drops nothing. Use exactly this). `f b := 4 * 2 ^ b − 3`, so
  `f 0 = 1`, `f ≥ 1`, and `f b = 2 * f (b−1) + 3`. Pending work of a
  configuration (see V4 for the config):

      P := (mode = descend ? f bud : 0)
         + Σ_{frames i with phase_i = 0} (f (k − 1 − i) + 2)
         + Σ_{frames i with phase_i = 1} 1
         + (mode ≠ done ? 1 : 0)

  Transition drops (each ≥ 1): push turns `f bud` into
  `f (bud−1) + (f (bud−1) + 2) = f bud − 1`; descend→backtrack at
  `bud = 0` drops `f 0 = 1`; a phase flip turns a frame's `f + 2` into
  active `f` plus a phase-1 unit, dropping 1; a pop drops its phase-1
  unit; the two exits drop the mode unit. Loop potential
  `Φ σ := U * (x.length + 1) * P (decode σ)` where `decode` reads the
  config *totally* off the arrays (garbage off-invariant is fine — only
  invariant states are ever compared) and `U` is a numeral ≥ the
  outer-loop body cost per `(x.length + 1)`, condition size included.
  Initial value `P = f k + 1 ≤ 4 * 2 ^ k`, so
  `Φ ≤ 4U * 2^k * (x.length + 1)` and the concept constant is
  `L.const * (4U + read/write slack)` — the `2^k` shape is exact, no
  base inflation. Take slack in every inequality (`≤`, `.mono`), but
  the `−3` in `f` is load-bearing: do not "simplify" it away.
- **VC5 — machine model frozen.** No multiplication, no word RAM. A
  word-RAM variant, if ever needed (hashing, bit-parallel DP), enters
  as a *sibling* machine concept with a bridge, never as an edit to
  `Ram.lean`. Recorded here so no session "improves" the machine.
- **VC6 — one statement, recurrence bound later.** The ladder keeps a
  single vertex cover theorem-concept. At the first improvement the
  bound moves from `2 ^ k` to a concept-level recurrence
  (`branchCount`), replacing the statement while in draft. That is a
  concept-surface change: **Jan gate**, not a relay decision.

## The algorithm (fixed; sessions implement, don't redesign)

After the read phase (`n`, `m`, offsets, targets as in CC, then one
more `read` for `k` — the tape has exactly `3 + n + 2m + 1` entries by
`EncodesInstance` + `EncodesGraph.length_eq`):

State: arrays `off`, `tgt` (the graph), `mark` (0/1 per vertex),
`stkU`, `stkV`, `stkP` (the frames); scalars `top`, `bud`, `mode`
(0 = descend, 1 = backtrack, 2 = done), `ans`.

Outer loop `while mode < 2`:

- **descend**: scan for an uncovered edge — one pass `j` over
  `[0, 2m)` maintaining the block owner `u` (inner `while off[u+1] ≤ j`
  advances `u`; amortized ≤ `n` over the scan); uncovered means
  `mark[u] = 0` and `mark[tgt[j]] = 0`; on found, record `eu, ev`, set
  the found flag, force `j := 2m` (VC3).
  - no uncovered edge: `ans := 1; mode := 2`.
  - found, `bud = 0`: `mode := 1`.
  - found, `bud > 0`: push `(eu, ev, 0)`; `mark[eu] := 1`;
    `bud := bud − 1` (stay in descend).
- **backtrack**: if `top = 0`: `ans := 0; mode := 2`. Else look at the
  top frame `(u, v, p)`:
  - `p = 0`: `mark[u] := 0; mark[v] := 1; stkP[top−1] := 1;
    mode := 0` (`bud` unchanged: siblings share `b − 1`).
  - `p = 1`: `mark[v] := 0; bud := bud + 1; top := top − 1`.

Then `write ans`. Per outer iteration the body costs
≤ `B * (x.length + 1)` for a numeral `B` (scan ≤ `2m + n` steps plus
constants; pushes/pops constant).

## The mathematics (fixed)

Pure side, all in `VCSpec.lean`, no `Env` anywhere:

- `Ok (M : Finset (Fin n)) (b : ℕ) : Prop :=`
  `∃ S : Finset (Fin n), IsVertexCover G ↑S ∧ M ⊆ S ∧ (S \ M).card ≤ b`.
- **Bridge**: `Ok ∅ k ↔ G.vertexCoverNum ≤ (k : ℕ∞)`. Via
  `vertexCoverNum_exists` (attainment) one way,
  `IsVertexCover.vertexCoverNum_le` the other;
  `Set.encard_coe_eq_coe_finsetCard` converts cardinalities. This is
  the only ℕ∞ contact — quarantine it in one lemma.
- **Cover-on-exhaustion**: if every CSR pair `(u, tgt j)` has a marked
  endpoint then the marked set is a vertex cover — transport through
  `EncodesGraph.adj_iff` once, in the style of `CCGraph.lean`.
- **Branch**: for `G.Adj u v`, `u ∉ M`, `v ∉ M`:
  `Ok M b ↔ 0 < b ∧ (Ok (insert u M) (b−1) ∨ Ok (insert v M) (b−1))`,
  plus `¬ Ok M 0` when an uncovered edge exists.
- **Pure config and invariant**: config `C = (frames, mode, bud, ans)`
  with `frames : List (Fin n × Fin n × Bool)`; marking `M C` = the
  chosen endpoints (`u` if phase 0, `v` if phase 1), pairwise distinct
  (part of the invariant, needed for undo); `bud = k − |frames|`.
  Writing `P_i` for the chosen set of frames `< i` and
  `A := ⋁_{phase-0 frames i} Ok (insert v_i (P_i)) (k − 1 − i)`:

      J(C) :=  mode = descend  →  (Ok ∅ k ↔ Ok (M C) bud ∨ A)
             ∧ mode = backtrack →  (Ok ∅ k ↔ A)
             ∧ mode = done     →  (ans = 1 ↔ Ok ∅ k)

  plus the **frame-health clause**: the chosen vertices are pairwise
  distinct, the mark array is exactly the indicator of `M C`, and for
  every phase-0 frame `v_i ∉ insert u_i (P_i)` — this is what makes
  the unmark-on-flip and unmark-on-pop sound (each frame's mark is
  present exactly once) and it holds at push time because both
  endpoints of the found edge were unmarked.

  Each machine transition preserves `J` by exactly one of the lemmas
  above; the flip case is where the stored alternative becomes the
  active branch (`M` becomes `insert v_i (P_i)` and `bud = k − 1 − i`
  on the nose — the VC2 bookkeeping makes this a `rfl`-grade check).
  At `done`, the bridge turns `ans` into the concept's `if`.

## Phase 1 milestones (relay-sized)

- **V1 — `VCSpec.lean`, pure model.** `Ok`, bridge, branch,
  cover-on-exhaustion, config, `J`, preservation lemmas, the `P`/`f`
  arithmetic of VC4 (`pure` statements about configs, no `Env`).
  Green, no `sorry`, committed. May split into two sessions
  (graph lemmas | config lemmas).
- **V2 — the program and its smoke test.** `vcCom : Com`, `vcCom_ok`,
  `#eval` the *compiled machine program* on: triangle (`k = 1` no,
  `k = 2` yes), star `K_{1,3}` (`k = 1` yes), path `P₄` (`k = 1` no,
  `k = 2` yes), edgeless (`k = 0` yes), plus a malformed-input
  non-crash sanity run. House discipline: run programs before proving
  them.
- **V3 — the scan lemma.** `Run` lemma for the scan in the CCPhases
  style: arrays represent config + marks, conclusion "found *an*
  uncovered CSR position / there is none" (any one, not the least —
  the invariant never needs which), cost ≤ numeral ·
  `(x.length + 1)`. Not `while_count`: one `j`-iteration's cost is not
  constant (the owner-advance inner loop can take many steps), so use
  `Run.while_pot` with potential `a·(2m − j) + b·(n − u)` for
  numerals `a`, `b` — the same amortization CC's scan used.
- **V4 — the outer loop.** One-transition lemma (body: env-level,
  case split on mode/found/bud, each case ≤ constant + scan cost,
  preserves "arrays represent `C` ∧ `J C`" and drops `P` by ≥ 1), then
  `Run.while_pot` with `Φ` of VC4. The expected hard part; budget two
  sessions before escalating.
- **V5 — assembly and audit.** Read phase (CC's `readLoop` pattern +
  one `read` for `k`), `write ans`, `computesInTime_of_run`,
  the conclusion-frontmatter theorem discharging
  `Lax11.VertexCover.exists_fptTime_program_vertexCover` with an
  explicit numeral `c`. `lake build` green; `lean_verify`: only the
  three background axioms. Commit.
- **V6 — wrap-up (Jan-visible).** Update `abstract.md`'s final
  paragraph (the statement is no longer open) and `notes.md`;
  build-output refresh; log the achieved constant. Do **not** touch
  concepts. Flag for Jan's morning review.

## Phase 2 sketch (φ^k — needs Jan's gate on VC6/concept bound)

Branch on a vertex of degree ≥ 2 (`v` vs `N(v)`), reduction rules for
degree ≤ 1; recurrence `T(k−1) + T(k−2)`; concept bound becomes
`branchCount` with `branchCount k = branchCount (k−1) +
branchCount (k−2) + slack`. Deltas: frames store a *list* of marked
vertices and an explicit budget (VC2 dies); the potential's `f`
becomes the recurrence solution (Fibonacci-style, still elementary);
reduction-rule dominance lemmas (a degree-1 vertex has an optimal
cover through its neighbor) enter `VCSpec`.

## Phase 3 sketch (1.4656^k)

Branch only on degree ≥ 3 (`T(k−1) + T(k−3)`); polynomial exact
solver for max-degree-2 graphs (paths/cycles — reuses the CC sweep);
concept recurrence changes again. Beyond this: folding/struction
(graph surgery, new CSR-with-undo machinery), then Chen–Kanj–Xia as a
separate campaign with its own plan.

## Watch items

- `lean-lsp` serves stale diagnostics after an external `lake build`
  (known from the CC relay) — rebuild via `lean_build` or trust
  `lake build` output.
- Never `simp` with concept definitions written by pattern matching
  (splitter leakage); restate as `rfl` lemmas in `Lax11Proofs`.
- `omega` cannot see structure fields; `have := hS.field` first.
- The `EncodesInstance` existential: destructure `⟨g, rfl, hg⟩` and
  work with `g ++ [k]`; `x.length = 3 + n + 2*m + 1` follows from
  `EncodesGraph.length_eq`.
- `bud`, `top`, `mode`, `ans` are the only scalars the potential and
  invariant may not read from arrays — everything else lives in the
  pure config; keep `Φ` and `J` defined on the *pure* config and
  lifted, never directly on `Env` internals.
