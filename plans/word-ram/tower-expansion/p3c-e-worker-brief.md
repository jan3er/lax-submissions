# P3.C-E worker brief — linear and bivariate recurrences

## 1. Identity and goal (required)

You own P3.C-E of the tower-expansion campaign. Create
`Lax13Proofs/Refine/Asymptotics/Recurrences.lean` in namespace
`Lax13Proofs.Refine.AsymptoticsRecurrences`. Port all 18 scheduled rows from
pinned `Asymptotics_Recurrences.thy` through line 585: 12 generic public
declarations and six source validation-example rows. Carry an in-file
source→Lean table distinguishing generic API, definitions/helpers, and the two
unnamed private validation theorems. Done means every row is implemented and
classified, recurrence premises/directions are source-faithful, genuine
product-filter bivariate results are present, the module builds green,
principal exports have kernel-three guards, and there is zero
`sorry`/`admit`/`native_decide`.

Expected source map and Lean stems:

- 7 `K` → `selfLeMulMul`;
- 11 `bigO_linear_recurrence` → `bigOLinearRecurrence`;
- 60 `bigO_linear_recurrence'` → `bigOLinearRecurrenceGeneral`;
- 139 `bigOmega_linear_recurrence` → `bigOmegaLinearRecurrence`;
- 220 `bigOmega_linear_recurrence'` → `bigOmegaLinearRecurrenceGeneral`;
- 313 `chara_ln` → `succMulLogLe`;
- 353/371/387 Θ wrappers → `bigThetaLinearRecurrenceConst`,
  `bigThetaLinearRecurrenceLog`, and `bigThetaLinearRecurrence`;
- 403 `bla_time` → `Examples.blaTime`; 407 `bla_time_nneg` →
  `Examples.blaTimeNonnegative`; unnamed line-410 lemma → private
  `blaTimeThetaQuadraticGate`;
- 416/496/559 → `bivariateBigO`, `bivariateBigOmega`, `bivariateTheta`;
- 579 `ex` → `Examples.bivariateTime`; 583 `ex_pos` →
  `@[simp] Examples.bivariateTimeNonnegative`; unnamed line-585 lemma →
  private `bivariateTimeThetaProductGate`.

Each source `fun` is one row; generated equations and induction principles are
compiler artifacts, not extra rows. Keep exact source stems in doc comments.
The unnamed lemmas remain private gates rather than invented public API.

## 2. State of the world (required — kills the orientation tax)

- Worktree: `/home/jan/git/lax-submissions` (`main`; direct-main work is
  explicitly authorized by the active campaign and Jan). Package:
  `/home/jan/git/lax-submissions/word-ram/proofs`. Namespace above. Green
  commit: `f1e1356` (`Complete tower expansion P3.C-D`). Supervisor replay:
  focused P3.C-D 1,989 jobs, concepts 505, full proofs 3,075 jobs, and
  `lax build --only proofs word-ram` green. Seed state:
  `word-ram/proofs/lake-manifest.json` SHA-256
  `d02fbf582ffd91e228a6c62ee800e457f2e28147d33a5e68c1894681eaf94a71`.
  If absent or different, stop and report; do not seed.
- Pinned source is `/tmp/Asymptotics_Recurrences.thy`, SHA-256
  `75cfb80c9d7abc92a5b0208f94a41500495bfe002d7e9be65f583fb239a473f7`,
  from `bzhan/Imperative_HOL_Time@09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec`.
  Exact anchors are 7, 11, 60, 139, 220, 313, 353, 371, 387, 403, 407, 410,
  416, 496, 559, 579, 583, and 585. There are no source exclusions.
- Import `Lax13Proofs.Refine.Asymptotics.TwoDimensionalComposition`. Landed
  capital includes `bigOE`, `bigOmegaE`, `bigO2E`, `bigOmega2E`,
  `productAtTop`, reverse-O aliases, product thresholds, polylog/log facts, and
  the complete 1D/2D composition and normalization layer. Reuse these rather
  than restating Landau extraction.
- Akra–Bazzi disposition: these are successor recurrences with recursive
  argument `n-1`, whose asymptotic ratio is 1. They do not satisfy mathlib's
  fixed-shrink `0 < bᵢ < 1` shape in
  `Mathlib/Computability/AkraBazzi/SumTransform.lean:60`. Prove them directly
  by tail induction. Document, but do not duplicate, mathlib's existing
  endpoints: `AkraBazziRecurrence.asympBound` (`SumTransform.lean:565`),
  `isBigO_asympBound` (`AkraBazzi.lean:655`), reverse-O
  `isBigO_symm_asympBound` (`:667`), and `isTheta_asympBound` (`:679`). A
  compact comment or `#check` block is sufficient; define no recurrence object
  or master-theorem API.
- FROZEN: every existing file, root imports, plans/ledger, concepts, pins,
  machine model, and consumers. You own only the new leaf. No ND-MC, BFS,
  introsort, codegen, or tactic framework import is allowed.
- Traps: O is forward big-O; Ω is reverse big-O. The generalized O result
  retains raw tail monotonicity and strict tail positivity of `G`. The
  generalized Ω result additionally retains global nonnegativity of `f` and
  `g`, strict tail positivity, `0 ≤ C`, and exactly the source increment bound
  `((n+1 : ℕ) : ℝ) * G (n+1) ≤ (n : ℝ) * G n + C * G n`. Do not weaken Ω
  nonnegativity to eventual. Bivariate recurrence advances only the first
  coordinate but concludes over literal `productAtTop`; its base premise is
  `n ≤ N → f (n,m) ≤ C`, not an absolute-value bound. Preserve unused source
  premises in `bivariateBigOmega`, including the redundant binder in
  `gpos : ∀ n _m : ℕ, 0 ≤ g n`. Bivariate targets cast natural multiplication
  after `n*m`; `blaTime` uses real multiplication.

Predecessor final report (verbatim):

> Root integration is green.
>
> - Added the import at `word-ram/proofs/Lax13Proofs.lean:104`.
> - Full `lake build` passed: 3,075 jobs.
> - No other files changed; nothing staged or committed.

Trust this report; do not re-verify modules it declares green.

## 3. File ownership (required for parallel waves)

- Create and own
  `word-ram/proofs/Lax13Proofs/Refine/Asymptotics/Recurrences.lean` and ONLY it;
  import `Lax13Proofs.Refine.Asymptotics.TwoDimensionalComposition` plus only
  the minimal mathlib log/Akra–Bazzi documentation substrate actually used.
- You MUST NOT edit any existing file; sibling agents own their leaves; the
  supervisor delegates root wiring separately.
- Build ONLY your module:
  `lake build Lax13Proofs.Refine.Asymptotics.Recurrences` from the proofs
  directory. On a Lake lock conflict, wait briefly and retry.
- Do not commit; do not stage. The supervisor commits per wave.

## 4. Lightweight sanity checks (Jan-approved exception)

Do not create a broad compiled falsification suite. Source review and direct
typechecking are sufficient for routine recurrence rows. The two source example
theorems are required validation gates: `blaTime` must exercise the quadratic
Θ wrapper; `bivariateTime` must exercise Θ over literal `productAtTop` with
`((n*m : ℕ) : ℝ)`. Add compact abstract checks for reverse-O orientation and
the generalized O/Ω pair without inventing new claims. Escalate if a source
statement appears false or a substantive premise change is needed.

## 5. Working method

- Iterate at the LSP (`lean_goal`, `lean_multi_attempt`, diagnostics). Use the
  leaf `lake build` only as a completion gate. Never `lean_build`, `lake
  update`, or an unseeded build.
- Read the exact source ranges and landed APIs before writing. Create only the
  owned leaf. Use tail induction and landed extractors; do not force these
  successor recurrences through Akra–Bazzi.
- Batch remote searches. Keep source order and declaration correspondence
  visible so the Isabelle theory remains a usable manual.

## 6. Budget and stop rule (required — kills 3-agent chains)

Estimated scope: 18 source rows, roughly 700–1,100 Lean lines. If the honest
remainder exceeds one agent-session, stop at the last green boundary (1D
generic family, 1D examples, 2D generic family, or 2D examples) and report the
exact remaining range. If one lemma resists after 4 distinct approaches,
record its goal and attempts, revert that section to the last green state, and
move on. Never leave a half-proof.

## 7. Report format (required)

End with:

- **Done** — declarations, `file:line`, source-table count, and leaf build.
- **Frozen/untouched** — explicitly confirm no existing file changed.
- **Defects found** — source/substrate mismatch, with evidence.
- **Remaining + next action** — exact source range and first command.
- **Traps** — Lean gotchas in NIGHTLOG-ready form.
- Honesty over completeness: reverted work with a repair plan is acceptable;
  hidden `sorry` is not.
