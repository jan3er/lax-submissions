# P4.A1 worker brief — generic vector amortization

## 1. Identity and goal (required)

You own P4.A1 of the tower-expansion campaign. Create
`word-ram/proofs/Lax13Proofs/Refine/Sepref/Amortization.lean` and use namespaces
`Lax13Proofs.Refine.NRest`, `Lax13Proofs.Refine.ACost`, and
`Lax13Proofs.Refine.Sepref` for the declarations below. Port the generic
amortization calculus from pinned `Dynamic_Array.thy:202–458`, while carrying
the complete in-file source-accounting table from `p4-design.md` for the
selected SLTC support ranges and `Dynamic_Array.thy:6–458`. Done means the
module builds green, all rows are classified, the authored vector-reclaim seam
passes its focused differential checks, principal exports have kernel-three
guards, and there is zero `sorry`/`admit`/`native_decide`.

Expected fully-qualified public API stems:

- `Lax13Proofs.Refine.NRest.reclaim`, `reclaim_fail`,
  `nofailT_reclaim`, `reclaim_spec`, `reclaim_spec_le`, and
  `timerefine_reclaim`;
- `Lax13Proofs.Refine.ACost.FiniteCost`, `finiteCost_apply`,
  `finiteCost_liftACost`, and `exists_liftACost_eq`;
- `Lax13Proofs.Refine.Sepref.augmentAmorAssn`,
  `invalidAssn_augmentAmorAssn`, `wpTimeFrame`, `hnRefineI2`,
  `hnRefine_paydayReverse`, `hnRefine_reclaim`, and
  `hnRefine_amortization`.

These stems correspond respectively to source lines 205–291, 310–333,
295–305, 343–360, 364–370, 372–388, 392–440, and 443–458. Preserve the exact
source stem in each doc comment. Helper lemmas from `Dynamic_Array.thy:6–200`
may be public only when an A1 theorem or a later A2/B2 theorem needs them;
otherwise reuse existing capital or keep them private and record their row.
If a materially different type or name is necessary, stop and request surface
authority rather than silently changing the API.

## 2. State of the world (required — kills the orientation tax)

- Worktree: `/home/jan/git/lax-submissions` (the campaign's authorized
  main-tree workspace). Package directory:
  `/home/jan/git/lax-submissions/word-ram/proofs`. Namespace and owned file are
  above. Green commit: `b6008c66fee3886456093dd13c761fb9f3e6c084`
  (`Complete tower expansion P3.C`); supervisor baseline: recurrence leaf
  2,248 jobs, concepts 505 jobs, full proofs 3,244 jobs, and proofs-only lax
  green. Seed state:
  `/home/jan/git/lax-submissions/word-ram/proofs/lake-manifest.json`, SHA-256
  `d02fbf582ffd91e228a6c62ee800e457f2e28147d33a5e68c1894681eaf94a71`.
  The supervisor owns
  seeding. If the exact manifest placeholder is unfilled, missing, or differs,
  wait and report; do not launch a second seed or an unseeded build.
- Exact primary source:
  `/tmp/claude-1000/-home-jan-git-lax-submissions/527e946f-f29f-4b59-9e6e-34554f43b878/scratchpad/illvm_time/thys/examples/dynarray/Dynamic_Array.thy`,
  from
  `lammich/isabelle_llvm_time@42dd7f59998d76047bb4b6bce76d8f67b53a08b6`,
  git blob `036faf5c16bb15d6da9fd46af305aeb62ebd0e13`, SHA-256
  `17c1905e7c2c713a6d580c9fc86d2e4d25ef82cfd79b48d3d37983242c61565e`.
  The supervisor must verify this path and checksum immediately before launch.
  Active ranges are 6–458, with new declarations concentrated at 202–458.
- Exact SLTC support sources are
  `/tmp/iht-p3c/SepLogicTime/SLTC.thy` (blob
  `cd10016003c23cd79a6f798fa20d1553a24f43d9`, SHA-256
  `70ddbb9ceb01901391d9e596de7119ed0f9da78a906ae23f94ce855c4dfc780e`)
  and `SLTC_More.thy` (blob `c92a653662d3ba1e96123bb50672147f2874f47e`, SHA-256
  `5861751b256c3fc196ea459f8298dbb3b796483b57026d6cb815fccbed539511`),
  at `bzhan/Imperative_HOL_Time@09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec`.
  Use the range table below; `SLTC_Automation.thy` is architecture-only/X7.
- Load-bearing definitions, quoted:
  - `ECost := ACost String ℕ∞`; `ACost` is a total function, not `Finsupp`
    (`Cost/ACost.lean:28–37,315`). `ResSub.resSub`, written `-ᵣ`, has
    `∞ -ᵣ ∞ = ∞` (`Cost/ACost.lean:77–118`).
  - `credits (c : ECost) : Assn := SND (EXACT c)` and
    `credits_add (c c' : ECost) : ¤(c+c') = ¤c ∗ ¤c'`
    (`Ir/Assn.lean:782–834`).
  - `NRest.consume m t` adds `t` on the left of each result cost
    (`NREST/Basic.lean:378–389`).
  - `liftACost (c : ACost κ ℕ) : ACost κ ℕ∞` and its add/subtraction laws
    (`NREST/BackwardsReasoning.lean:528–570`).
  - `timerefine`, `nofailT_timerefine`, `timerefineA_mono`, and
    `timerefine_consume` are at
    `NREST/TimeRefinement.lean:279–305,423–447,644–667`.
  - `invalidAssn R a c := ⌜purePart (R a c)⌝`
    (`Sepref/Basic.lean:168–174`).
  - `hnRefine Γ c Γ' d R m` is the cost-carrying refinement judgment
    (`Sepref/Basic.lean:411–424`); consequence rules are `:541–574`.
- Source table to reproduce in the new module header:

  | source | exact range | required disposition |
  |---|---:|---|
  | `SLTC.thy` | 53–302 | existing generic assertion/credit algebra; cite `Ir/Assn.lean` |
  | `SLTC.thy` | 304–350 | existing entailment/GC credit weakening; add only missing A1 support |
  | `SLTC.thy` | 352–484 | existing Wp/frame/consequence |
  | `SLTC.thy` | 486–573 | existing primitive triples |
  | `SLTC_More.thy` | 7–161,186–260,262–345,610–631 | existing normalization, GC-entailment, `sepOr`, consequence |
  | `SLTC_More.thy` | 165–184 | excluded D2/X13 address heap relation |
  | `SLTC_More.thy` | 347–606 | outside selected credit slice; conjunction/precision/auto2 classifier not A1 API |
  | `Dynamic_Array.thy` | 6–200 | existing cost/time-refinement support or named private helper |
  | `Dynamic_Array.thy` | 202–291 | new `reclaim` family |
  | `Dynamic_Array.thy` | 293–305 | new potential assertion family |
  | `Dynamic_Array.thy` | 308–333 | new finite-cost/extraction family |
  | `Dynamic_Array.thy` | 336–458 | new Wp/`hnRefine` amortization family |

- FROZEN: every existing file, root imports, plans/ledger, concepts, pins,
  machine model, A2/B1/B2 leaves, and consumers. Own only the new A1 leaf.
  Do not add allocation, arrays, a dynamic-list interface, union-find, arena
  credits, or an automation framework.
- Known traps: use `-ᵣ`, not `-`; `ECost` order is pointwise over infinitely
  many `String` currencies; finite cost means pointwise non-top, not finite
  support. Keep vector costs primary. Do not collapse to cash. `GC` absorbs
  credits only, never cells. `invalidAssn` is pure bookkeeping, not
  deallocation. Use `set` before `simp only` when unfolding a higher-order cost
  expression would trigger a large `whnf`. `fri`/`refine_vcg` remain the solver
  carriers; do not port auto2.

There is no predecessor worker report for this first P4 wave.

## 3. File ownership (required for parallel waves)

- Create and own
  `word-ram/proofs/Lax13Proofs/Refine/Sepref/Amortization.lean` and ONLY it;
  imports are the frozen `Lax13Proofs.Refine.Sepref.Basic`,
  `Lax13Proofs.Refine.NREST.BackwardsReasoning`, and
  `Lax13Proofs.Refine.NREST.TimeRefinement` layers, reduced if a smaller
  non-cyclic import set suffices.
- You MUST NOT edit any existing file; sibling agents own their leaves; the
  supervisor wires roots.
- Build ONLY your module:
  `lake build Lax13Proofs.Refine.Sepref.Amortization` from the proofs dir. On a
  lake lock conflict, wait briefly and retry.
- Do not commit; do not stage. The supervisor commits per wave.

## 4. Falsification gate (required for authored obligations)

Routine source-shaped SLTC and amortization statements use source review,
typechecking, kernel guards, and the leaf build only. Do not create compiled
negative controls for those direct ports.

The vector-valued `reclaim` rendering is genuinely authored at the currency
seam and must be refuted before proved. Build a private executable finite
two-currency mirror and compare it to the pointwise `ECost` result on:

1. exact residual: `(5,7)` reclaimed by `(2,3)` gives `(3,4)`;
2. insufficient potential: a coordinate demanding more than the result cost
   makes that result unavailable/no-fail fail in the source-prescribed way;
3. currency isolation: surplus in currency A cannot pay a deficit in B;
4. top behavior: the implementation uses `-ᵣ`, preserving `⊤ -ᵣ ⊤ = ⊤`.

Keep the executable mirror private and small; it is a falsification oracle,
not a second API. If any check refutes the proposed definition or direction,
record the counterexample and stop on that obligation. Do not repair the
surface without supervisor authority.

## 5. Working method

- Iterate at the LSP: `lean_goal` / `lean_multi_attempt` /
  `lean_diagnostic_messages` at the stuck position. `lake build` is a gate you
  run when you believe you are done, never the inner loop. Never `lean_build`
  (MCP), `lake update`, or a bare unseeded `lake build`.
- Read the exact source ranges and landed declarations before writing. Preserve
  the source order in the new leaf and keep the source→Lean table current as
  each family lands. Use existing `liftACost`, time-refinement, Wp, credit, and
  consequence lemmas instead of re-proving them.
- Remote search is rate-limited; batch queries. Files are edited normally;
  Python/heredoc work is only for the private differential oracle, not file
  surgery.
- Files: read before writing; use Edit for changes. A full-file rewrite is
  allowed only for the new file created in this session. Do not use Python for
  file surgery.
- Principal exports get kernel-three `#print axioms` guards permitting only
  `propext`, `Classical.choice`, and `Quot.sound`. Root wiring and full-build
  replay belong to the supervisor.

## 6. Budget and stop rule (required — kills 3-agent chains)

Estimated scope: about 17 public declarations plus private support/table/gates,
roughly 350–600 Lean lines. If mid-task the honest estimate of the remainder
exceeds one agent-session, stop at the current green boundary (`reclaim`,
finite-cost, assertion augmentation, or `hnRefine` family) and report; do not
start a piece you cannot finish. If one lemma resists after 4 distinct
approaches, record the exact goal state and attempts, revert that section to
the last green state, and move on. Never leave a half-proved lemma: revert to
the last green state and file the attempt.

## 7. Report format (required)

End with a report the next agent can resume from cold:

- **Done** — declarations landed, with `file:line`, source-table count,
  differential checks, kernel guards, and leaf build.
- **Frozen/untouched** — explicitly confirm every existing file and sibling
  leaf remained unchanged.
- **Defects found** — source/substrate mismatch or refuted statement, with
  exact evidence; this outranks progress.
- **Remaining + next action** — exact source range and the first command to run.
- **Traps** — Lean gotchas in NIGHTLOG-ready form.
- Honesty over completeness: a reverted proof with a repair plan is a good
  outcome; a hidden `sorry` is the only bad one.
