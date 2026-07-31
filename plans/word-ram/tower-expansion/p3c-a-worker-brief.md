# P3.C-A worker brief — one-dimensional asymptotic foundations

## 1. Identity and goal (required)

You own P3.C-A of the tower-expansion campaign. Create
`Lax13Proofs/Refine/Asymptotics/OneDimensional.lean` in namespace
`Lax13Proofs.Refine.Asymptotics1D`. Port the complete ordered public family of
pinned `Asymptotics_1D.thy` lines 7–384: eventual nonnegativity, `polylog`,
stable big-O, eventual norm-monotonicity, O/Ω introduction and extraction, and
the four eventual-growth consequences. Preserve source declaration stems in
idiomatic Lean spelling and carry an in-file source→Lean table. Done means
every scheduled declaration is present or classified as mathlib-supplied with
a local source-shaped wrapper/gate, the module build is green, principal
exports have kernel-three axiom guards, and there is zero `sorry`/`admit`.

Expected fully-qualified API stems are:

- definitions `EventuallyNonnegative`, `polylog`, `StableBigO`,
  `EventuallyMonoNorm`, and the source-facing Ω rendering `IsBigOmega`;
- the `eventNonneg*`, `stableBigO*`, and `eventMono*` families corresponding in
  order to source lines 7–229;
- `bigOmegaI`, `bigOmegaE`, `bigOE`, `bigOENat`, `bigOmegaENat`, `fsmallReal`,
  `fsmallEventually`, `fsmall`, and `fbig`, corresponding to lines 239–384.

If a better Lean spelling is materially necessary, keep the source stem in the
doc comment and report the rename; do not silently omit or fuse declarations.

## 2. State of the world (required — kills the orientation tax)

- Worktree: `/home/jan/git/lax-submissions` (`main`; direct-main work is
  explicitly authorized by the active campaign and Jan). Package:
  `/home/jan/git/lax-submissions/word-ram/proofs`. Namespace above. Green
  commit: `5e23c90` (`Complete tower expansion P3.B`). Supervisor replay:
  concepts 505 jobs, focused P3.B 2,985 jobs, full proofs 3,066 jobs, and
  `lax build --only proofs word-ram` green. Seed state:
  `word-ram/proofs/lake-manifest.json` exists with SHA-256
  `d02fbf582ffd91e228a6c62ee800e457f2e28147d33a5e68c1894681eaf94a71`.
  If that manifest is missing or differs, stop and report; do not seed.
- Pinned source is already fetched at `/tmp/Asymptotics_1D.thy`, SHA-256
  `83334111a75605f6b25576b1b96b068793104f6e19cc8b28737e030efd39b56a`.
  Authoritative pin and raw path:
  `bzhan/Imperative_HOL_Time@09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec`,
  `Asymptotics/Asymptotics_1D.thy`. The exact scheduled line anchors are
  7, 10, 14, 17, 21, 27, 30, 37, 43, 46, 50, 59, 62, 65, 68, 71, 107,
  117, 127, 164, 167, 170, 174, 178, 182–185, 211–212, 229, 239, 253,
  265, 277, 295, 320, 334, 350, and 363.
- The Lean substrate is mathlib pin
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Load-bearing shapes:
  `Asymptotics.IsBigO l f g` is notation `f =O[l] g`
  (`Analysis/Asymptotics/Defs.lean:103`);
  `Asymptotics.IsTheta l f g := IsBigO l f g ∧ IsBigO l g f`
  (`Defs.lean:170`); `isBigO_iff'` extracts a positive constant and eventual
  norm bound (`Defs.lean:118`); `IsBigO.of_bound` installs an eventual bound
  (`Defs.lean:150`); mathlib has no separate big-Ω judgment, so the faithful
  Lean rendering is reverse big-O behind the named `IsBigOmega` surface.
  Addition/multiplication support is in `Defs.lean:984–1017,1309–1339` and Θ
  algebra in `Theta.lean:44–110,179–219`.
- FROZEN: every existing Lean file, `Lax13Proofs.lean`, all plan/ledger files,
  concept surfaces, toolchain/mathlib pins, machine model, and every consumer
  module. You own only the new leaf named above. You may import mathlib
  asymptotics/log/power modules; do not import an ND-MC module or any BFS/
  introsort example.
- Traps: Isabelle Ω is reverse big-O in mathlib; do not accidentally reverse
  source hypotheses or conclusions. Use the actual `atTop` filter. Keep
  natural casts explicit at theorem boundaries. Do not recreate mathlib's
  generic asymptotics API. Split source multi-conclusion declarations into
  named Lean lemmas only when the in-file table records the split. Avoid
  `native_decide`; principal exports must remain within `propext`,
  `Classical.choice`, and `Quot.sound`. Root `lax` catches splitters that a leaf
  build does not, so do not introduce root namespace commands.

## 3. File ownership (required for parallel waves)

- Create and own
  `word-ram/proofs/Lax13Proofs/Refine/Asymptotics/OneDimensional.lean` and ONLY
  it; imports are mathlib-only and limited to the asymptotics/log/power
  substrate needed by the source family.
- You MUST NOT edit any existing file; sibling agents own their leaves; the
  supervisor wires roots.
- Build ONLY your module:
  `lake build Lax13Proofs.Refine.Asymptotics.OneDimensional` from the proofs
  directory. On a Lake lock conflict, wait briefly and retry.
- Do not commit; do not stage. The supervisor commits per wave.

## 4. Falsification gate (required for authored obligations)

Refute before prove. Before proving authored adaptations, compile negative
controls for: the reversed strict lexicographic `polylog` comparison; stability
at zero scaling; and eventual monotonicity of a sum with the source nonnegative
premise removed (use the concrete eventual counterexample pattern
`f(n)=n`, `g(n)=-(n+n%2)`: both norms are monotone while the sum norm
oscillates). Positive gates must include `polylog 1 0` versus linear
growth, strict polylog comparison, sum/product stability, sum/product eventual
norm-monotonicity, and both O and Ω extractors. If a proposed statement is
refuted, record the smallest counterexample and stop on it unless the exact
source statement resolves the mismatch; do not redesign the surface silently.

## 5. Working method

- Iterate at the LSP: `lean_goal` / `lean_multi_attempt` /
  `lean_diagnostic_messages` at the stuck position. `lake build` is a gate
  when you believe you are done, never the inner loop. Never `lean_build`,
  `lake update`, or an unseeded build.
- Read source and mathlib before writing. The new leaf may be created normally;
  do not modify other files. Differential/numerical checks are for
  falsification, not file surgery.
- Remote search is rate-limited; batch queries. Landed mathlib proofs are
  capital: wrap and compose them instead of reproving generic filter algebra.

## 6. Budget and stop rule (required — kills 3-agent chains)

Estimated scope: 5 definitions, about 34 source-facing lemmas/wrappers, and
roughly 450–700 Lean lines. If the honest remainder exceeds one agent-session,
stop at the last green source section boundary and report the exact unported
line range; do not start a section you cannot finish. If one lemma resists
after 4 distinct approaches, record its goal state and attempts, revert that
section to the last green state, and move on. Never leave a half-proved lemma.

## 7. Report format (required)

End with:

- **Done** — declarations landed, with `file:line`, and the source-table count.
- **Frozen/untouched** — explicitly confirm no existing file changed.
- **Defects found** — source/substrate mismatch or refuted statement, with
  evidence; this outranks progress.
- **Remaining + next action** — exact line range and first command.
- **Traps** — Lean gotchas in NIGHTLOG-ready form.
- Honesty over completeness: a reverted proof with a repair plan is a good
  outcome; a hidden `sorry` is the only bad one.
