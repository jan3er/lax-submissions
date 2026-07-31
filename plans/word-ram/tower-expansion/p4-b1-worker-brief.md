# P4.B1 worker brief — pure union-find theory

## 1. Identity and goal (required)

You own P4.B1 of the tower-expansion campaign. Create
`word-ram/proofs/Lax13Proofs/Refine/Iicf/UnionFindAbstract.lean` in namespace
`Lax13Proofs.Refine.Iicf.UnionFind`. Port the complete pure union-find family
from AFP `Partial_Equivalence_Relation.thy:11–75`, pinned Sepreftime
`UnionFind.thy:8–59`, and `Union_Find_Time.thy:20–649,813–828`. Use explicit
bounded-fuel totalizations for the source's partial `rep_of` and `height_of`,
and prove their source equations under `ufaInvar`; off-invariant behavior is
not public semantics. Done means all source rows are mapped or landed, PER/list
abstraction and union/compression correctness are green, the exponential and
logarithmic height bounds are green, the module builds, principal exports have
kernel-three guards, and there is zero `sorry`/`admit`/`native_decide`.

Expected fully-qualified public API stems under
`Lax13Proofs.Refine.Iicf.UnionFind`:

- PER dependency and wrapper family: `Per`, `PartEquiv`, `perInit`,
  `perCompare`, `perInitNat`, `perUnion`, `perSupsetRel`, and source-shaped
  lemmas `partEquivRefl`, `partEquivSymm`, `partEquivTrans`,
  `perUnionPartEquiv`, `perUnionCompare`, `perUnionSame`, `perUnionComm`,
  `perUnionDomain`, `perInitOfNatRange`, `perInitPartEquiv`, `perInitSelf`,
  `perUnionImpl`, `perUnionRelated`, `perSupsetRelDomain`,
  `perSupsetCompare`, and `perSupsetUnion`;
- representative/abstraction family: private `repOfFuel`, public `repOf`,
  `ufaInvar`, `ufaInvarD`, `repOfRefl`, `repOfStep`, `repOfInduct`,
  `repOfRoot`, `repOfBound`, `repOfIdem`, `repOfRootUpdate`, `repOfIndex`,
  `ufaAlpha`, `ufaAlphaPartEquiv`, `ufaAlphaLength`, `ufaAlphaDomain`,
  `ufaAlphaRefl`, and `ufaAlphaLengthEq`;
- operation family: `ufaInitInvar`, `ufaInitCorrect`, `ufaFindCorrect`,
  `ufaUnion`, `ufaUnionInvar`, `ufaUnionRep`, `ufaUnionCorrect`,
  `ufaCompress`, `ufaCompressInvar`, and `ufaCompressCorrect`;
- height/rank family: private `heightOfFuel`, public `heightOf`, `heightOfStep`,
  `hOf`, `rankInvar`, `rankAtRootLeLength`, `heightOfRoot`,
  `ufaCompressHeight`, `ufaUnionPathSucc`, `ufaUnionOffPath`,
  `ufaUnionHeight`, `hOfCompress`, `hOfUnionUntouched`, `hOfUnionSame`,
  `hOfUnionTouched`, `heightOfLeHOf`, and `heightOfPowTwoLeLength`;
- logarithmic wrapper family: `heightUb`, `heightUbThetaLog`, and
  `heightOfLeHeightUb`.

Source helper rows `hel`, `MAXIMUM_mono`, `MAXIMUM_eq`, `Suc_h_of`,
`MAXIMUM_Un`, and the unnamed max-monotonicity lemma at lines 512–564 may be
private wrappers around mathlib. Record every one in the source table. Preserve
source stems in doc comments. If the stated totalization cannot prove the
source equations without changing `ufaInvar`, stop and request surface
authority rather than weakening the invariant.

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
  wait and report; do not seed or run an unseeded build.
- Exact Sepreftime sources at
  `maxhaslbeck/Sepreftime@c1c987b45ec886d289ba215768182ac87b82f20d`:
  - `Examples/Kruskal/UnionFind.thy`, blob
    `f5562a98227c3b96f2ee972a62632baac89d51b6`, SHA-256
    `a372eae3503f478d6fede5c5f1e72be2b9a3a6541cabd671ac2747f966753464`,
    active range 8–59; local path
    `/tmp/lax-p4-sources/sepreftime/UnionFind.thy`;
  - `Examples/Kruskal/Union_Find_Time.thy`, blob
    `f07981b49870fc063eeacf9aa7a839f603af973d`, SHA-256
    `9b0ce7306623ce70a1552eb151f539fcaa25846006af5966d8f04253c1d52d34`,
    active ranges 20–649 and 813–828; local path
    `/tmp/lax-p4-sources/sepreftime/Union_Find_Time.thy`.
  Both files were materialized from the exact pinned raw blobs and their
  SHA-256 values were replayed immediately before launch.
- AFP dependency: Isabelle2025-2, official stable archive extract
  `afp-2026-07-21`,
  `Collections/Lib/Partial_Equivalence_Relation.thy:11–75`; the P0 survey used
  mirror commit `400ee45cf836394b0b35dde6d20ab5ecd2012ee3`, blob
  `3735a0e259bafbbaffe374c3cea9caa60ebbd0a9`, SHA-256
  `1475d988f7cd9ad679de5001c4932db599f3f7cb8f60f8325b99314440934ce6`.
  Exact official extract path:
  `/tmp/lax-p4-sources/afp/afp-2026-07-21/thys/Collections/Lib/Partial_Equivalence_Relation.thy`.
  Its SHA-256 is byte-identical to the surveyed mirror source.
  Its definitions are
  `part_equiv R ≡ sym R ∧ trans R` and
  `per_union R a b ≡ R ∪ {(x,y). (x,a)∈R ∧ (y,b)∈R}
  ∪ {(y,x). (x,a)∈R ∧ (y,b)∈R}` (`:11,43–44`).
- Exact source table to reproduce in the module header:

  | source | range | declarations/disposition |
  |---|---:|---|
  | `Partial_Equivalence_Relation.thy` | 11–31 | `part_equiv` and reflexive/symmetric/transitive consequences |
  | same | 33–39 | `symcl` helper family; private unless needed by a public proof |
  | same | 41–75 | `per_union` and its part-equivalence/compare/same/commute/domain/class lemmas |
  | `UnionFind.thy` | 8–40 | `per`, init/compare, init and union lemmas |
  | same | 42–59 | `per_supset_rel` domain/compare/union family |
  | `Union_Find_Time.thy` | 20–116 | `rep_of`, invariant, source equations, induction, root/bound/idempotence/update/index |
  | same | 117–147 | `ufa_alpha` PER abstraction/domain/length family |
  | same | 148–331 | init/find/union/compression invariant and correctness family |
  | same | 333–389 | `height_of`, domain equivalence, `h_of`, rank invariant, root-size bound |
  | same | 394–510 | compression and union effects on path height |
  | same | 512–564 | Max helpers; private mathlib wrappers, individually accounted |
  | same | 568–647 | `h_of` union cases and `2^height ≤ length` theorem |
  | same | 813–828 | `height_ub`, Θ(log n), and height upper bound |

- Load-bearing local substrate:
  - Lists use `List.get!`/proved index bounds or an equivalent option-safe
    interface; never rely on silent out-of-range semantics in a public theorem.
  - P3.C one-dimensional asymptotic capital is under
    `Lax13Proofs.Refine.Asymptotics1D` and
    `Asymptotics1DOperations`; reuse its Θ/log wrappers rather than creating a
    second Landau API.
  - The future concrete assertion convention is caller-owned capacity:
    `junkArrayOfLen n a := ∃ᵃ xs, ⌜xs.length=n⌝ ∗ arrayAssn xs a`
    (`Iicf/Basic.lean:114`). B1 is pure and must not import Sepref or define an
    assertion.
  - The future executable language has only loops and no recursion/allocation
    (`Ir/Syntax.lean:33–43,130–155`). B1 proves pure facts only; B2 owns that
    rendering.
- FROZEN: every existing file, root imports, plans/ledger, A1/A2/B2 leaves,
  concepts, pins, machine model, and consumers. Own only the new B1 leaf. Do
  not define MOPs, assertions, IR programs, costs, HNR rules, Kruskal, or an
  inverse-Ackermann theorem.
- Known traps: the source's `part_equiv` is symmetry plus transitivity, not a
  globally reflexive equivalence relation. Its domain is the relation domain.
  `rep_of` and `height_of` are partial off-invariant; the bounded totalization
  is observable only under `ufaInvar`. Preserve source update direction:
  `ufa_union l x y` links `rep_of l x` to `rep_of l y`. The rank invariant
  stores size only at roots and its sum equals list length. The final source
  claim is worst-case Θ(log n), not alpha(n). Keep casts and log base explicit;
  do not claim Θ at zero without the source's wrapper conventions. Use `set`
  before simplification when repeated `repOf` unfolding causes `whnf` growth.

There is no predecessor worker report; B1 runs independently beside A1.

## 3. File ownership (required for parallel waves)

- Create and own
  `word-ram/proofs/Lax13Proofs/Refine/Iicf/UnionFindAbstract.lean` and ONLY it;
  imports are mathlib list/set/finite-set relation support plus the frozen
  `Lax13Proofs.Refine.Asymptotics.OneDimensionalOperations` module needed for
  `heightUbThetaLog`. Do not import Sepref, IR, or another IICF implementation.
- You MUST NOT edit any existing file; sibling agents own their leaves; the
  supervisor wires roots.
- Build ONLY your module:
  `lake build Lax13Proofs.Refine.Iicf.UnionFindAbstract` from the proofs dir.
  On a lake lock conflict, wait briefly and retry.
- Do not commit; do not stage. The supervisor commits per wave.

## 4. Falsification gate (required for authored obligations)

This is a routine direct source port. Source review, direct typechecking,
source-equation gates, kernel guards, and the leaf build are sufficient; do not
create a broad compiled falsification suite.

The only authored representation choice is bounded-fuel totalization. Before
depending on it, attempt counterexamples on singleton, one-edge, multi-edge,
compression, and both directions of a union, without creating a focused
compiled differential suite. Then prove that under `ufaInvar` its
`repOfRefl`/`repOfStep` and `heightOfStep` equations are exactly the source
equations. Also prove/publicly document that all public correctness theorems
assume `ufaInvar`; off-invariant output is deliberately unspecified. If a
source statement is refuted or needs a changed premise, record the
counterexample and stop; do not redesign it yourself.

## 5. Working method

- Iterate at the LSP: `lean_goal` / `lean_multi_attempt` /
  `lean_diagnostic_messages` at the stuck position. `lake build` is a gate you
  run when you believe you're done, never the inner loop. Never `lean_build`,
  `lake update`, or a bare unseeded build.
- Work in source order: PER dependency; representatives/abstraction;
  init/union/compression; height/rank; logarithmic wrapper. Keep the in-file
  table updated. Read source and landed mathlib/P3.C APIs before proving.
- Use existing finite-set Max/sum and asymptotic capital. Do not re-prove a
  generic relation, maximum, logarithm, or Landau library when a wrapper
  suffices. Batch remote searches.
- Files: read before writing; use Edit for changes. A full-file rewrite is
  allowed only for the new file created in this session. Python/heredocs are
  not file-surgery tools.
- Principal exports receive kernel-three `#print axioms` guards allowing only
  `propext`, `Classical.choice`, and `Quot.sound`. Root wiring and full replay
  belong to the supervisor.

## 6. Budget and stop rule (required — kills 3-agent chains)

Estimated scope: roughly 55 source rows/declarations plus private totalization
helpers, about 700–1,100 Lean lines. If mid-task the honest estimate of the
remainder exceeds one agent-session, stop at the current green source boundary
(PER, representatives/abstraction, operations, height/rank, or logarithmic
wrapper) and report; do not start a section you cannot finish. If one lemma
resists after 4 distinct approaches, record the exact goal state and attempts,
revert that section to the last green state, and move on. Never leave a
half-proved lemma: revert to the last green state and file the attempt.

## 7. Report format (required)

End with a report the next agent can resume from cold:

- **Done** — declarations landed, with `file:line`, source-table count,
  computation/source-equation gates, kernel guards, and leaf build.
- **Frozen/untouched** — explicitly confirm no existing file or sibling leaf
  changed.
- **Defects found** — source/substrate mismatch or refuted statement, with
  evidence; this outranks progress.
- **Remaining + next action** — exact source range and the first command to run.
- **Traps** — Lean gotchas in NIGHTLOG-ready form.
- Honesty over completeness: a reverted proof with a repair plan is a good
  outcome; a hidden `sorry` is the only bad one.
