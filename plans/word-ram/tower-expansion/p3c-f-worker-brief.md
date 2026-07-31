# P3.C-F worker brief — asymptotic consumer demonstrations

## 1. Identity and goal (required)

You own P3.C-F of the tower-expansion campaign. Create
`Lax13Proofs/Refine/Examples/AsymptoticConsumers.lean` in namespace
`Lax13Proofs.Refine.AsymptoticConsumers`. Add exactly two bounded consumer
demonstrations over the landed P3.C API:

1. project the exact seven-coordinate BfsQ account to unit cash, prove its
   exact polynomial, and export only O(n + ns) over the genuine product filter;
2. wrap the exact introsort cash boundary, define its scalar polynomial, and
   export only O(n log n).

Carry a two-row consumer-provenance table. Done means both exact wrappers and
both O theorems build, the O exports have kernel-three guards, there is no Θ
strengthening or ND-MC dependency, and there is zero
`sorry`/`admit`/`native_decide`.

Expected API stems:

- `bfsQCash`, `bfsQCash_eq`, and `bfsQCash_isBigO`;
- `introsortCash`, an exact wrapper such as `introsortBudget_cash_eq`, and
  `introsortCash_isBigO`.

The exact theorem statements are:

```lean
theorem bfsQCash_isBigO :
    (fun p : ℕ × ℕ => (bfsQCash p.1 p.2 : ℝ)) =O[productAtTop]
      fun p => (p.1 : ℝ) + (p.2 : ℝ)

theorem introsortCash_isBigO :
    (fun n => (introsortCash n : ℝ)) =O[atTop]
      fun n => (n : ℝ) * Real.log (n : ℝ)
```

Do not claim Θ or lower bounds.

## 2. State of the world (required — kills the orientation tax)

- Worktree: `/home/jan/git/lax-submissions` (`main`; direct-main work is
  explicitly authorized by the active campaign and Jan). Package:
  `/home/jan/git/lax-submissions/word-ram/proofs`. Namespace above. Green
  commit: `ba0bb45` (`Complete tower expansion P3.C-E`). Supervisor replay:
  focused P3.C-E 2,248 jobs, concepts 505, full proofs 3,243 jobs, and
  `lax build --only proofs word-ram` green. Seed state:
  `word-ram/proofs/lake-manifest.json` SHA-256
  `d02fbf582ffd91e228a6c62ee800e457f2e28147d33a5e68c1894681eaf94a71`.
  If absent or different, stop and report; do not seed.
- The final A–E reconciliation is green: 131 normalized source rows, 126 live
  and five exclusions. By theory: 1D 74/70/4, 2D 39/38/1, recurrences 18/18/0.
  Do not edit or restate those source tables. This leaf has a two-row consumer
  map, not new source-port rows.
- Imports are exactly the necessary subset of:
  `Lax13Proofs.Refine.Asymptotics.Recurrences`,
  `Lax13Proofs.Refine.Examples.BfsQ`, and
  `Lax13Proofs.Refine.Examples.IntrosortBudget`. They have no ND-MC dependency.
- BfsQ capital in `Examples/BfsQ.lean`: `BfsQ.bfsQTotal` at `:1354`, exact
  vector `BfsQ.bfsQTotal_normal` at `:1360`, seven coordinate theorems at
  `:1388–1434`, and complete-support theorem `bfsQTotal_other` at `:1436`.
  Define `bfsQCash n ns` as the sum of exactly those seven coordinates and
  prove `bfsQCash n ns = 22 * n + 15 * ns + 13`. The O result must use literal
  `productAtTop`, not a diagonal limit.
- Introsort capital in `Examples/IntrosortBudget.lean`: `ilog n := Nat.log 2 n`
  at `:50`, `operationBudget` at `:98`, `introsortBudget_normal` at `:147`, and
  scalar boundary `introsortBudget_cash` at `:370–375`. Define
  `introsortCash n := 4693 + 5 * ilog n + 231 * n + 455 * (n * ilog n)` and
  add an exact wrapper re-expressing `introsortBudget_cash` with this name.
- Log bridge: mathlib `Real.natLog_le_logb` in
  `Analysis/SpecialFunctions/Log/Base.lean:421`, then landed `log2Asym 0` in
  `OneDimensionalOperations.lean:349`. Use big-O addition/multiplication and
  landed polylog comparison/absorption facts to absorb constants, `log n`, and
  `n` into `n * log n` eventually. Do not derive a lower bound from the exact
  syntactic polynomial.
- FROZEN: every existing file, root imports, A–E leaves/tables, plans/ledger,
  concepts, pins, machine model, and consumer implementations. You own only
  the new leaf. No ND-MC import or edit is allowed.
- Traps: the seven BfsQ coordinates sum to `22*n + 15*ns + 13`; omitting the
  constant coordinate corrupts the projection. The BfsQ filter has independent
  coordinate thresholds. `Nat.log` needs a one-sided bridge to real log; an O
  proof may ignore small `n`, but must handle positivity of `Real.log n` on the
  chosen tail. Exact cost equalities do not themselves justify Θ. Kernel guards
  permit only `propext`, `Classical.choice`, and `Quot.sound`.

Predecessor final report (verbatim):

> Root integration is green.
>
> - Added `import Lax13Proofs.Refine.Asymptotics.Recurrences` at `Lax13Proofs.lean:105`.
> - Full `lake build` passed: 3,243 jobs.
> - No other files changed; nothing staged or committed.

Trust this report; do not re-verify modules it declares green.

## 3. File ownership (required for parallel waves)

- Create and own
  `word-ram/proofs/Lax13Proofs/Refine/Examples/AsymptoticConsumers.lean` and ONLY
  it; use only the three frozen imports listed above.
- You MUST NOT edit any existing file; sibling agents own their leaves; the
  supervisor delegates root wiring separately.
- Build ONLY your module:
  `lake build Lax13Proofs.Refine.Examples.AsymptoticConsumers` from the proofs
  directory. On a Lake lock conflict, wait briefly and retry.
- Do not commit; do not stage. The supervisor commits per wave.

## 4. Lightweight sanity checks (Jan-approved exception)

No compiled falsification suite is required. The exact BfsQ polynomial and
exact introsort boundary wrapper are the sanity checks. Add direct positive
checks that the BfsQ theorem uses `productAtTop` and that both exported results
are O, not Θ. Escalate if either advertised exact equality fails; do not alter
the frozen producer theorem or strengthen/weaken the requested surfaces.

## 5. Working method

- Iterate at the LSP (`lean_goal`, `lean_multi_attempt`, diagnostics). Use the
  leaf `lake build` only as a completion gate. Never `lean_build`, `lake
  update`, or an unseeded build.
- Read producer statements before writing. Create only the owned leaf. Reuse
  exact producer theorems and landed asymptotic algebra rather than re-expanding
  BFS or introsort implementations.
- Batch remote searches. Keep the two consumer rows visibly separate.

## 6. Budget and stop rule (required — kills 3-agent chains)

Estimated scope: two consumer rows, roughly 180–350 Lean lines. If the honest
remainder exceeds one agent-session, stop at the last green boundary (BfsQ or
introsort) and report the remaining theorem. If one theorem resists after four
distinct approaches, record its goal and attempts, revert to the last green
state, and move on. Never leave a half-proof.

## 7. Report format (required)

End with:

- **Done** — declarations, `file:line`, two-row map, and leaf build.
- **Frozen/untouched** — explicitly confirm no existing file changed and no
  ND-MC dependency.
- **Defects found** — producer/API mismatch, with evidence.
- **Remaining + next action** — exact theorem and first command.
- **Traps** — Lean gotchas in NIGHTLOG-ready form.
- Honesty over completeness: reverted work with a repair plan is acceptable;
  hidden `sorry` is not.
