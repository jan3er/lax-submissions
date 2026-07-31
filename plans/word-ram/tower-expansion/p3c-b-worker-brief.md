# P3.C-B worker brief — one-dimensional operations and normalization

## 1. Identity and goal (required)

You own P3.C-B of the tower-expansion campaign. Create
`Lax13Proofs/Refine/Asymptotics/OneDimensionalOperations.lean` in namespace
`Lax13Proofs.Refine.Asymptotics1D`. Port every live public declaration from
pinned `Asymptotics_1D.thy` lines 386–854, in source order: O/Ω/Θ composition,
natural division and subtraction, ceiling/log results, Θ addition, and the
named normalization/algebra rules that feed `landau_util.ML`. Carry an in-file
source→Lean table that also records the dead/substrate exclusions. Done means
the complete remaining 1D family is present or explicitly classified, the
module builds green, principal exports have kernel-three guards, and there is
zero `sorry`/`admit`.

Expected fully-qualified API stems are:

- `bigOmegaCompose`, `bigOCompose`, `bigThetaCompose`,
  `bigThetaComposeLinear`, and the source's polylog-linear wrapper;
- `asymBoundDiv`, `asymBoundDivLinear`, `asymBoundDiff`;
- `ceilingTheta`, `eventNonnegLogPlus`, `log2Asym`, its source helper,
  `abcdLog`, and `log2Nonnegative`;
- `thetaAdd`, its function-addition wrapper, the six `landauNorms*` rules,
  `plusAbsorbLeft`, `plusAbsorbRight`, `plusAbsorbSame`, `bigThetaAdd`,
  `landauNormLinear`, `landauNormConst`, `landauNormTimes`,
  `bigThetaConst`, `bigThetaLinear`, and `bigThetaMul`.

Exact source stems stay in doc comments. If Lean requires a different spelling
or a theorem-bundle split, record it in the source table; do not silently fuse
or omit declarations.

## 2. State of the world (required — kills the orientation tax)

- Worktree: `/home/jan/git/lax-submissions` (`main`; direct-main work is
  explicitly authorized by the active campaign and Jan). Package:
  `/home/jan/git/lax-submissions/word-ram/proofs`. Namespace above. Green
  commit: `1fa093e` (`Complete tower expansion P3.C-A`). Supervisor replay:
  focused P3.C-A 1,986 jobs, concepts 505, full proofs 3,072 jobs, and
  `lax build --only proofs word-ram` green. Seed state:
  `word-ram/proofs/lake-manifest.json` SHA-256
  `d02fbf582ffd91e228a6c62ee800e457f2e28147d33a5e68c1894681eaf94a71`.
  If absent or different, stop and report; do not seed.
- Pinned source is `/tmp/Asymptotics_1D.thy`, SHA-256
  `83334111a75605f6b25576b1b96b068793104f6e19cc8b28737e030efd39b56a`,
  from `bzhan/Imperative_HOL_Time@09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec`.
  Scheduled anchors: 386, 430, 474, 500, 515, 527, 589, 594, 642–643,
  689, 693, 699, 703, 725, 730–735, 781–786, 796–803, 805, 808, 811,
  814, 830, 833, 836, 840, 844, and 848. Source
  `polylog_power_compose` at 489–498 ends in `oops`: classify it as dead source
  and do not prove it. `ML_file landau_util.ML`, `attribute_setup asym_bound`,
  and `method_setup master_theorem2` at 855–862 are substrate exclusions:
  named Lean rules and gates are the scheduled rendering, not a tactic port.
- Load-bearing landed API in
  `Lax13Proofs/Refine/Asymptotics/OneDimensional.lean`:
  `StableBigO f := ∀ d : ℕ, 0 < d → (fun x => f (d*x)) =O[atTop] f`
  (`:71–73`); `EventuallyMonoNorm f := ∀ᶠ x₁ in atTop, ∀ x₂ ≥ x₁,
  ‖f x₁‖ ≤ ‖f x₂‖` (`:75–77`); `IsBigOmega l f g := g =O[l] f`
  (`:79–82`); `polylog` (`:67–69`); `polylogCompare` (`:174–216`);
  stability/monotonicity families (`:220–350`); O/Ω extractors and growth
  consequences (`:354–433`). Import and reuse these; do not restate them.
- Mathlib substrate pin is
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Relevant capital:
  `Asymptotics` composition/transitivity in `Defs.lean:431–532`, algebra in
  `Defs.lean:984–1024,1309–1339`, Θ algebra/absorption in
  `Theta.lean:44–110,179–280`, ceiling equivalence in
  `SpecificAsymptotics.lean:212–218`, and log infrastructure in
  `SpecialFunctions/Log/{Basic,Base}.lean`. Reuse mathlib's Akra–Bazzi later;
  this file must not define a master-theorem API.
- FROZEN: every existing file, including the landed P3.C-A leaf and root;
  plans/ledger, concepts, pins, machine model, and all consumers. You own only
  the new leaf. It imports P3.C-A plus mathlib. No ND-MC, BFS, introsort, or
  codegen import is allowed.
- Traps: Ω is reverse big-O. `event_mono` is eventual norm monotonicity, not
  global `Monotone`. Preserve Nat truncation before casting in division and
  subtraction. Θ addition needs nonnegative premises because cancellation is
  real. An O-only upper bound never justifies Θ. The source ML reducer is
  partial and head-keyed; named theorems do not license a total simplifier.
  Avoid `native_decide`; kernel guards permit only `propext`,
  `Classical.choice`, and `Quot.sound`.

Predecessor final report (verbatim):

> - **Done** — Created `word-ram/proofs/Lax13Proofs/Refine/Asymptotics/OneDimensional.lean` only.
>   - Source table: 38 entries, comprising 5 definitions and 33 public theorems (`file:13–53`).
>   - Definitions: `EventuallyNonnegative`, `polylog`, `StableBigO`, `EventuallyMonoNorm`, `IsBigOmega` (`file:64–82`).
>   - Compiled falsification controls for reversed lexicographic comparison, zero scaling, and sum monotonicity without nonnegativity (`file:90–137`).
>   - Eventual-nonnegativity and complete `polylog` family (`file:142–216`).
>   - Complete stability family (`file:221–286`).
>   - Complete eventual norm-monotonicity family (`file:292–350`).
>   - O/Ω introduction/extraction and all four growth consequences (`file:355–433`).
>   - Required positive gates (`file:437–470`).
>   - Thirteen exact kernel-three axiom guards (`file:474–524`).
>   - Focused build passed: `lake build Lax13Proofs.Refine.Asymptotics.OneDimensional`, 1,986 jobs.
>   - Zero `sorry`/`admit`.
>
> - **Frozen/untouched** — No existing file changed. Only the new leaf is untracked; nothing staged or committed. Root imports, plans, concepts, and sibling modules remain untouched.
>
> - **Defects found** — None. The expected substrate gaps were handled explicitly:
>   - Isabelle Ω is reverse mathlib big-O.
>   - Mathlib has no `Norm ℕ`, so Nat-valued asymptotic boundaries use explicit real casts.
>   - The negative controls confirm strict comparison orientation, positive scaling, and sum nonnegativity are genuinely necessary.
>
> - **Remaining + next action** — No source lines remain unported from scheduled range 7–384. Supervisor should wire the root and replay focused/full gates; first command after wiring:
>   `lake build Lax13Proofs.Refine.Asymptotics.OneDimensional`
>
> - **Traps** —
>   - Render `f ∈ Ω(g)` as `g =O[...] f`; reversing this silently corrupts extractors.
>   - Cast Nat-valued functions to `ℝ` at O/Ω and little-o boundaries.
>   - `polylog` must be `noncomputable` because it contains `Real.log`.
>   - Zero rescaling is invalid even for a positively stable function.
>   - Eventual norm-monotonicity of sums needs eventual nonnegativity; product closure does not.
>   - Nat big-O extraction needs `Nat.ceil` of the real witness constant.

Trust this report; do not re-verify modules it declares green.

## 3. File ownership (required for parallel waves)

- Create and own
  `word-ram/proofs/Lax13Proofs/Refine/Asymptotics/OneDimensionalOperations.lean`
  and ONLY it; import
  `Lax13Proofs.Refine.Asymptotics.OneDimensional` and the minimum mathlib
  log/asymptotics substrate.
- You MUST NOT edit any existing file; sibling agents own their leaves; the
  supervisor delegates root wiring separately.
- Build ONLY your module:
  `lake build Lax13Proofs.Refine.Asymptotics.OneDimensionalOperations` from the
  proofs directory. On a Lake lock conflict, wait briefly and retry.
- Do not commit; do not stage. The supervisor commits per wave.

## 4. Falsification gate (required for authored obligations)

Before proofs, compile negative controls showing: divisor zero is rejected;
an O-only premise cannot produce Θ; cancellation invalidates Θ-addition when
the source nonnegative premises are removed; and the aborted
`polylog_power_compose` is an exclusion rather than a theorem target. Positive
gates must exercise a nontrivial Θ-linear inner composition, Nat division and
truncated subtraction, ceiling-of-log Θ, Θ addition, and named normalization
of a concrete polynomial/log expression. If a statement is refuted, report
the counterexample and stop on that obligation; do not repair the surface
without supervisor authority.

## 5. Working method

- Iterate at the LSP (`lean_goal`, `lean_multi_attempt`, diagnostics). Use the
  leaf `lake build` only as a completion gate. Never `lean_build`, `lake
  update`, or an unseeded build.
- Read source and mathlib before writing. Create only the owned leaf. Reuse the
  landed P3.C-A API and mathlib capital rather than re-proving generic filter
  algebra.
- Batch remote searches. Keep source sections and declaration order visible so
  the Isabelle theory remains a usable manual.

## 6. Budget and stop rule (required — kills 3-agent chains)

Estimated scope: about 30 source-facing declarations/wrappers plus explicit
exclusion rows, roughly 550–850 Lean lines. If the honest remainder exceeds
one agent-session, stop at the last green source section boundary and report
the exact remaining line range. If one lemma resists after 4 distinct
approaches, record its goal and attempts, revert that section to the last green
state, and move on. Never leave a half-proof.

## 7. Report format (required)

End with:

- **Done** — declarations, `file:line`, source-table count, and leaf build.
- **Frozen/untouched** — explicitly confirm no existing file changed.
- **Defects found** — source/substrate mismatch or refutation, with evidence.
- **Remaining + next action** — exact source range and first command.
- **Traps** — Lean gotchas in NIGHTLOG-ready form.
- Honesty over completeness: reverted work with a repair plan is acceptable;
  hidden `sorry` is not.
