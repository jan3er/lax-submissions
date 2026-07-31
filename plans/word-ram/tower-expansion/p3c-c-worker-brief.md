# P3.C-C worker brief — two-dimensional foundations and lifting

## 1. Identity and goal (required)

You own P3.C-C of the tower-expansion campaign. Create
`Lax13Proofs/Refine/Asymptotics/TwoDimensional.lean` in namespace
`Lax13Proofs.Refine.Asymptotics2D`. Port every live public declaration in
pinned `Asymptotics_2D.thy` lines 5–270, 467–559, and 638–669, in source
order: the four 2D Landau faces over the genuine product filter,
`polylog2` and eventual nonnegativity, `StableBigO2` and its introduction,
product, extraction, addition, and polylog results, `EventuallyMonoNorm2` and
its product, polylog, and addition results, the O/Ω extractors,
`multBivariateI`, `oO_o`, `Oo_o`, `multThetaBivariate`, and its three
polylog/coordinate lifting wrappers. Carry an in-file source→Lean table.
Done means every declaration in those disjoint ranges is present or explicitly
classified, at least one positive gate genuinely depends on
`atTop ×ˢ atTop`, the module builds green, principal exports have kernel-three
guards, and there is zero `sorry`/`admit`.

Expected fully-qualified API stems are:

- `productAtTop`, `IsBigO2`, `IsLittleO2`, `IsTheta2`, and `IsBigOmega2`
  (the source abbreviations may be rendered as type-correct Lean aliases);
- `polylog2`, `eventNonnegPolylog2`;
- `StableBigO2`, `stableBigO2I`, `stableBigO2Mul`, `stableBigO2Extract`,
  `stableBigO2ExtractPair`, `stableBigO2Add`, `stablePolylog2`;
- `EventuallyMonoNorm2`, `eventMono2Mul`, `eventMono2Polylog2`,
  `eventMono2Add`;
- `bigO2E`, `bigOmega2E`, `multBivariateI`, `oO_o`, `Oo_o`,
  `multThetaBivariate`, `multThetaBivariatePolylog`,
  `multThetaBivariateFst`, and `multThetaBivariateSnd`.

Exact source stems stay in doc comments. If Lean spelling or the abbreviation
rendering differs, record the correspondence in the source table; do not
silently fuse or omit declarations. Composition/comparison/normalization
declarations outside these ranges belong to P3.C-D and must not be pulled in.

## 2. State of the world (required — kills the orientation tax)

- Worktree: `/home/jan/git/lax-submissions` (`main`; direct-main work is
  explicitly authorized by the active campaign and Jan). Package:
  `/home/jan/git/lax-submissions/word-ram/proofs`. Namespace above. Green
  commit: `3094e6e` (`Complete tower expansion P3.C-B`). Supervisor replay:
  focused P3.C-B 1,987 jobs, concepts 505, full proofs 3,073 jobs, and
  `lax build --only proofs word-ram` green. Seed state:
  `word-ram/proofs/lake-manifest.json` SHA-256
  `d02fbf582ffd91e228a6c62ee800e457f2e28147d33a5e68c1894681eaf94a71`.
  If absent or different, stop and report; do not seed.
- Pinned source is `/tmp/Asymptotics_2D.thy`, SHA-256
  `edeea514189e817190e354a257fe938acedbf1bae5c1a44fb4b57488b7469c20`,
  from `bzhan/Imperative_HOL_Time@09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec`.
  Owned declaration anchors are 5–8, 12, 15, 23, 26, 34, 71, 84, 97, 133,
  142, 145, 173, 180, 214, 226, 240, 467, 490, 515, 638, 649, and 660.
  Lines 272–463, 563–636, and 671 onward belong to P3.C-D or substrate and
  are frozen even though the source interleaves them with this wave.
- Load-bearing landed API is in
  `Lax13Proofs/Refine/Asymptotics/OneDimensional.lean` and
  `OneDimensionalOperations.lean`: `polylog`, `StableBigO`,
  `EventuallyMonoNorm`, reverse-O `IsBigOmega`, the eventual nonnegativity,
  stability, and monotonicity families, O/Ω extractors, and Θ algebra. Import
  `OneDimensionalOperations` and reuse it; do not restate the 1D layer.
- Mathlib substrate pin is
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Product-filter capital:
  `Order/Filter/AtTopBot/Prod.lean:24` (`prod_atTop_atTop_eq`) and its eventual
  threshold lemmas at `:92–106`; Landau coordinate lifts in
  `Analysis/Asymptotics/Defs.lean:884–915` (`comp_fst`, `comp_snd`) and Θ lifts
  in `Analysis/Asymptotics/Theta.lean:295–317`. Use `atTop ×ˢ atTop` on
  `ℕ × ℕ`; a diagonal map or nested limit is not an equivalent carrier.
- FROZEN: every existing file, including both landed 1D leaves and the root;
  plans/ledger, concepts, pins, machine model, and all consumers. You own only
  the new leaf. No ND-MC, BFS, introsort, recurrence, or codegen import is
  allowed.
- Traps: Ω is reverse big-O. Product-filter eventuality means independent
  lower bounds on both coordinates; diagonal truth is insufficient.
  `event_mono2` is eventual norm monotonicity in the product order, not global
  `Monotone`. Addition retains eventual nonnegativity. Nat multiplication and
  casts in the bivariate lifting theorems must match the source. Do not invent
  a total order on `polylog2`; comparison belongs to P3.C-D and is partial.
  Avoid `native_decide`; kernel guards permit only `propext`,
  `Classical.choice`, and `Quot.sound`.

Predecessor final report (verbatim):

> Root integration is green.
>
> - Added the import at `word-ram/proofs/Lax13Proofs.lean:102`.
> - Full `lake build` passed: 3,073/3,073 jobs.
> - Nothing staged or committed.
> - No other files modified.

Trust this report; do not re-verify modules it declares green.

## 3. File ownership (required for parallel waves)

- Create and own
  `word-ram/proofs/Lax13Proofs/Refine/Asymptotics/TwoDimensional.lean` and ONLY
  it; import
  `Lax13Proofs.Refine.Asymptotics.OneDimensionalOperations` and the minimum
  mathlib product-filter/asymptotics substrate.
- You MUST NOT edit any existing file; sibling agents own their leaves; the
  supervisor delegates root wiring separately.
- Build ONLY your module:
  `lake build Lax13Proofs.Refine.Asymptotics.TwoDimensional` from the proofs
  directory. On a Lake lock conflict, wait briefly and retry.
- Do not commit; do not stage. The supervisor commits per wave.

## 4. Lightweight sanity checks (Jan-approved exception)

This is a direct source-shaped port, so Jan has explicitly waived a compiled
falsification/negative-control suite. Do not spend time formalizing diagonal,
zero-scaling, or cancellation counterexamples. Source review must still confirm
that the carrier is literally `atTop ×ˢ atTop` and that both coordinates occur
where the source requires them. Representative positive checks should exercise
independent product thresholds, coordinate lifting, O/Ω extraction, and Θ
multiplication. Escalate only if a source statement itself looks false or a
substantive adaptation is needed; do not repair the surface without supervisor
authority.

## 5. Working method

- Iterate at the LSP (`lean_goal`, `lean_multi_attempt`, diagnostics). Use the
  leaf `lake build` only as a completion gate. Never `lean_build`, `lake
  update`, or an unseeded build.
- Read the exact disjoint source ranges and mathlib product-filter API before
  writing. Create only the owned leaf. Reuse landed 1D results and mathlib
  coordinate lifts rather than rebuilding filter algebra.
- Batch remote searches. Keep source sections and declaration order visible so
  the Isabelle theory remains a usable manual.

## 6. Budget and stop rule (required — kills 3-agent chains)

Estimated scope: 26 source declarations/abbreviations plus gates and source
table, roughly 500–800 Lean lines. If the honest remainder exceeds one
agent-session, stop at the last green source-section boundary and report the
exact remaining range. If one lemma resists after 4 distinct approaches,
record its goal and attempts, revert that section to the last green state, and
move on. Never leave a half-proof.

## 7. Report format (required)

End with:

- **Done** — declarations, `file:line`, source-table count, and leaf build.
- **Frozen/untouched** — explicitly confirm no existing file changed.
- **Defects found** — source/substrate mismatch or refutation, with evidence.
- **Remaining + next action** — exact source range and first command.
- **Traps** — Lean gotchas in NIGHTLOG-ready form.
- Honesty over completeness: reverted work with a repair plan is acceptable;
  hidden `sorry` is not.
