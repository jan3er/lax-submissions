# P3.C-D worker brief — two-dimensional composition and normalization

## 1. Identity and goal (required)

You own P3.C-D of the tower-expansion campaign. Create
`Lax13Proofs/Refine/Asymptotics/TwoDimensionalComposition.lean` in namespace
`Lax13Proofs.Refine.Asymptotics2D`. Port all 12 live public declarations from
pinned `Asymptotics_2D.thy` lines 272–463, 563–636, and 671–672, in source
order: two-coordinate O/Ω/Θ composition and its linear wrappers, the partial
`polylog2` comparison predicate and three comparison results, the two named
normalization declarations, and the nonconstant-polylog growth lemma. Record
`landau_util_2d.ML` at line 674 as a substrate exclusion. Carry an in-file
source→Lean table with 12 live rows plus that exclusion. Done means the exact
scheduled family is classified, source premises and directions are preserved,
the module builds green, principal exports have kernel-three guards, and there
is zero `sorry`/`admit`/`native_decide`.

Expected fully-qualified API stems are:

- `bigO2ComposeBoth`, `bigOmega2ComposeBoth`, `bigTheta2ComposeBoth`,
  `bigTheta2ComposeBothLinear`, and `bigTheta2ComposeBothPolylogLinear`;
- `Polylog2StrictlyBelow` (source `cas1`), `polylog2Compare`,
  `polylog2CompareFstStrict`, and `polylog2CompareSndStrict`;
- a named theorem bundle rendering source `landau_norms2`, a function-level
  multiplication wrapper rendering `landau_norms2'`, and `polylogLittleOmegaOne`.

Exact source stems stay in doc comments. If Lean spelling or a theorem-bundle
split differs, record it in the source table; do not silently fuse or omit
declarations. Do not extend the source's partial comparison into a total
normalizer.

## 2. State of the world (required — kills the orientation tax)

- Worktree: `/home/jan/git/lax-submissions` (`main`; direct-main work is
  explicitly authorized by the active campaign and Jan). Package:
  `/home/jan/git/lax-submissions/word-ram/proofs`. Namespace above. Green
  commit: `e6d2f96` (`Complete tower expansion P3.C-C`). Supervisor replay:
  focused P3.C-C 1,988 jobs, concepts 505, full proofs 3,074 jobs, and
  `lax build --only proofs word-ram` green. Seed state:
  `word-ram/proofs/lake-manifest.json` SHA-256
  `d02fbf582ffd91e228a6c62ee800e457f2e28147d33a5e68c1894681eaf94a71`.
  If absent or different, stop and report; do not seed.
- Pinned source is `/tmp/Asymptotics_2D.thy`, SHA-256
  `edeea514189e817190e354a257fe938acedbf1bae5c1a44fb4b57488b7469c20`,
  from `bzhan/Imperative_HOL_Time@09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec`.
  Live anchors are 272, 342, 412, 432, 453, 563, 566, 602, 612, 624, 634,
  and 671. `ML_file "landau_util_2d.ML"` at 674 is an explicit substrate
  exclusion: named Lean theorems and representative checks are the rendering,
  not a text port of the head-keyed ML reducer.
- Load-bearing landed API is in
  `Lax13Proofs/Refine/Asymptotics/TwoDimensional.lean`: literal
  `productAtTop := atTop ×ˢ atTop`, the four 2D Landau aliases, `polylog2`,
  `StableBigO2`, `EventuallyMonoNorm2`, O/Ω extractors, and coordinate/product
  lifting. The 1D imports below it supply `fsmallEventually`, 1D O/Ω/Θ
  extraction/composition, `polylogCompare`, and named normalization algebra.
  Import `TwoDimensional` and reuse this capital; do not restate it.
- Source growth premise `f ∈ ω(1)` is represented by
  `(fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n => (f n : ℝ)`, as in the landed
  1D layer. Isabelle Ω remains reverse mathlib big-O. Source `event_mono2` is
  `EventuallyMonoNorm2`, not global `Monotone`.
- FROZEN: every existing file, including all three landed asymptotics leaves
  and the root; plans/ledger, concepts, pins, machine model, and all consumers.
  You own only the new leaf. No recurrence, ND-MC, BFS, introsort, or codegen
  import is allowed.
- Traps: each composition theorem has independent growth premises for both
  inner coordinates. O and Ω use opposite Landau directions but identical
  product-filter semantics. Preserve natural-valued composition before real
  coercion. The comparison predicate requires one coordinate strictly smaller
  and the other weakly smaller; incomparable exponent pairs remain
  incomparable. The ML reducer is partial and head-keyed. Avoid new automation
  or a global simp set. Kernel guards permit only `propext`,
  `Classical.choice`, and `Quot.sound`.

Predecessor final report (verbatim):

> Root integration is green.
>
> - Added the import at `word-ram/proofs/Lax13Proofs.lean:103`.
> - Full `lake build` passed: 3,074 jobs.
> - No other files changed; nothing staged or committed.

Trust this report; do not re-verify modules it declares green.

## 3. File ownership (required for parallel waves)

- Create and own
  `word-ram/proofs/Lax13Proofs/Refine/Asymptotics/TwoDimensionalComposition.lean`
  and ONLY it; import
  `Lax13Proofs.Refine.Asymptotics.TwoDimensional` and no consumer modules.
- You MUST NOT edit any existing file; sibling agents own their leaves; the
  supervisor delegates root wiring separately.
- Build ONLY your module:
  `lake build Lax13Proofs.Refine.Asymptotics.TwoDimensionalComposition` from
  the proofs directory. On a Lake lock conflict, wait briefly and retry.
- Do not commit; do not stage. The supervisor commits per wave.

## 4. Lightweight sanity checks (Jan-approved exception)

This direct source-shaped port does not require a compiled falsification or
negative-control suite. Do not formalize counterexamples merely to satisfy the
brief. Source review must still check O/Ω orientation, both independent inner
coordinates, strict-versus-weak comparison inequalities, and the absence of a
total comparison claim. Representative positive checks should exercise one Θ
composition, both strict-coordinate comparison branches, and concrete
`polylog2` multiplication normalization. Escalate only if a source statement
looks false or a substantive adaptation is needed.

## 5. Working method

- Iterate at the LSP (`lean_goal`, `lean_multi_attempt`, diagnostics). Use the
  leaf `lake build` only as a completion gate. Never `lean_build`, `lake
  update`, or an unseeded build.
- Read the exact source ranges and landed 1D/2D APIs before writing. Create only
  the owned leaf. Reuse the source-shaped extractors, growth consequences, and
  mathlib Landau transitivity rather than duplicating filter algebra.
- Batch remote searches. Keep source order and declaration correspondence
  visible so the Isabelle theory remains a usable manual.

## 6. Budget and stop rule (required — kills 3-agent chains)

Estimated scope: 12 live declarations plus one exclusion, roughly 450–750 Lean
lines. If the honest remainder exceeds one agent-session, stop at the last
green source-section boundary and report the exact remaining range. If one
lemma resists after 4 distinct approaches, record its goal and attempts,
revert that section to the last green state, and move on. Never leave a
half-proof.

## 7. Report format (required)

End with:

- **Done** — declarations, `file:line`, source-table count, and leaf build.
- **Frozen/untouched** — explicitly confirm no existing file changed.
- **Defects found** — source/substrate mismatch, with evidence.
- **Remaining + next action** — exact source range and first command.
- **Traps** — Lean gotchas in NIGHTLOG-ready form.
- Honesty over completeness: reverted work with a repair plan is acceptable;
  hidden `sorry` is not.
