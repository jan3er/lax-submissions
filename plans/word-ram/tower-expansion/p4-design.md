# Tower expansion P4 — credits and amortization design

Status: **ACTIVE 2026-08-01; A1, A2, and B1 complete; B2 comparison green.**
A2 is root-green. B2 has its MOP/assertion surface, no-allocation two-array
initialization, and height-sensitive measured root-search and path-compression
loops, plus bounds-checked same-set comparison; union-by-size is next. This record
instantiates P4 of `tower-expansion-plan.md`. It is source-first: every selected
source range receives a Lean owner, an existing-capital mapping, or an explicit
exclusion. The machine model remains frozen.

## 1. Supervisor decision and dependency graph

The four worker-sized waves are:

```text
P4.A1 generic amortization ───────▶ P4.A2 bounded dynamic array
             │
             └──────────────┐
P4.B1 pure union-find ──────┴────▶ P4.B2 timed loop-form union-find
```

- **P4.A1 — complete** creates `Sepref/Amortization.lean`: generic
  vector-credit reclaim, potential assertions, and the amortized `hnRefine`
  bridge.
- **P4.A2 — complete** creates `Iicf/IicfDynamicArray.lean`: the source-faithful abstract
  dynamic-list/potential development plus a bounded executable adapter over
  caller-owned, preallocated storage. Capacity and buffer ownership are explicit.
- **P4.B1 — complete** creates
  `Iicf/UnionFindAbstract.lean`: PER/list semantics, representation invariants,
  union/compression correctness, and logarithmic height theory are green.
- **P4.B2** creates `Iicf/UnionFindTime.lean`: the MOP/HNR interface and timed
  loop-form implementation over caller-owned parent and size arrays.

A1 and B1 may run in parallel. A2 waits for A1. B2 waits for both A1 and B1;
it does not wait for A2.

**P4-DYN-1 — accepted substrate deviation.** The supervisor rejects a
machine-model allocation extension. `Ir.Com` has no allocation/free
(`Ir/Syntax.lean:33–43`), writes require existing cells
(`Ir/Semantics.lean:54–65`), and IICF construction already consumes
`junkArrayOfLen` (`Iicf/Basic.lean:52–73`). The source-faithful generic and
abstract amortization theorem lands unchanged, but the executable A2 face is a
bounded caller-owned adapter. It must expose capacity/buffer ownership and must
not claim unbounded allocation or an executable implementation of the source's
undefined allocator. P5 may consume only that honest bounded surface.

**P4-UF-1 — planned substrate adaptation.** The source's `rep_of` and
`uf_compress` are recursive; the executable IR is loop-only (D6). B1 may
totalize the pure partial functions with explicit bounded fuel while proving
the source equations under `ufaInvar`. B2 renders find and path compression as
one root-search loop plus a second compression pass. Source scalar constants
are not copied to the authored loop program; B2 derives vector costs from the
synthesized operations and then proves O(log n).

## 2. Exact source ledger

| source | exact pin | blob / SHA-256 | selected ranges |
|---|---|---|---|
| `SepLogicTime/SLTC.thy` | `bzhan/Imperative_HOL_Time@09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec` | git blob `cd10016003c23cd79a6f798fa20d1553a24f43d9`; SHA-256 `70ddbb9ceb01901391d9e596de7119ed0f9da78a906ae23f94ce855c4dfc780e` | 53–350 credit/assertion/entailment discipline; 352–573 accounted as existing Hoare/atomic capital |
| `SepLogicTime/SLTC_More.thy` | same | blob `c92a653662d3ba1e96123bb50672147f2874f47e`; SHA-256 `5861751b256c3fc196ea459f8298dbb3b796483b57026d6cb815fccbed539511` | 7–260 normalization and garbage entailment; 262–345 disjunction accounting; 610–631 consequence accounting |
| `SepLogicTime/SLTC_Automation.thy` | same | blob `06e008b3aec869933aef200a5fd3631bab6bf99b`; SHA-256 `bd405bea52431e2efa70fd7a6d2d5d0f363d86eb98707e8bc69b0754cdfb6a50` | architecture only: 31–80 frame/rotate, 83–225 simplifier/matcher, 228–248 timeframe, 249–1060 entailment/`sep_auto`; excluded X7 |
| `thys/examples/dynarray/Dynamic_Array.thy` | `lammich/isabelle_llvm_time@42dd7f59998d76047bb4b6bce76d8f67b53a08b6` | blob `036faf5c16bb15d6da9fd46af305aeb62ebd0e13`; SHA-256 `17c1905e7c2c713a6d580c9fc86d2e4d25ef82cfd79b48d3d37983242c61565e` | A1: 6–200 and 202–458; A2: 464–1005 and 1028–1091 |
| `Examples/IHT_Dynamic_Array.thy` | IHT pin above | blob `9e8d6b36c405017edafe262391bf55bc37a0eeeb`; SHA-256 `932a3077de97436c0bcb58061597f329d75c4ee4bb796b1a4e7e49ebc3742a59` | A2: 5–186 potential/raw rules and 188–203 functional push |
| `Examples/IHT_Dynamic_Array_More.thy` | IHT pin above | blob `24d4b79f21f57a9d686a87508b73dce28dcbf4e6`; SHA-256 `0aa441497be63a58e96c2bf3ddfe8136ab5844257d56dd469315a44c7fcbae13` | A2: 5–147 second potential and public O(1) push interface |
| `Examples/Kruskal/UnionFind.thy` | `maxhaslbeck/Sepreftime@c1c987b45ec886d289ba215768182ac87b82f20d` | blob `f5562a98227c3b96f2ee972a62632baac89d51b6`; SHA-256 `a372eae3503f478d6fede5c5f1e72be2b9a3a6541cabd671ac2747f966753464` | B1: 8–59 |
| `Examples/Kruskal/UnionFind_Impl.thy` | same | blob `ab8ee190712ed90cbcd1d58a253f4b40097a42d6`; SHA-256 `3cf8f65c0bbb2a5b6b6245f9afdf4365e61d19df47435c07e4450b53b219aa52` | B2: 7–86 |
| `Examples/Kruskal/Union_Find_Time.thy` | same | blob `f07981b49870fc063eeacf9aa7a839f603af973d`; SHA-256 `9b0ce7306623ce70a1552eb151f539fcaa25846006af5966d8f04253c1d52d34` | B1: 20–649 and pure bounds 813–828; B2: 651–811 and 832–1204 |
| `Collections/Lib/Partial_Equivalence_Relation.thy` | AFP Isabelle2025-2; surveyed mirror `400ee45cf836394b0b35dde6d20ab5ecd2012ee3`; official stable archive extract `afp-2026-07-21` | surveyed blob `3735a0e259bafbbaffe374c3cea9caa60ebbd0a9`; SHA-256 `1475d988f7cd9ad679de5001c4932db599f3f7cb8f60f8325b99314440934ce6`; the official extract is byte-identical | B1 dependency: 11–75 (`part_equiv`, `symcl`, `per_union` family) |

Locally verified IHT extracts are under `/tmp/iht-p3c/`; the primary artifact
extract was verified against the `42dd7f5` tree. The three Sepreftime files are
materialized under `/tmp/lax-p4-sources/sepreftime/` and match the exact pinned
blob hashes above. The official AFP stable extract is under
`/tmp/lax-p4-sources/afp/afp-2026-07-21/` and is byte-identical to the surveyed
source at the recorded SHA-256.

## 3. Source-accounting law and wave tables

Every module header must contain a table with one row per source declaration or
coherent helper family. A row has exactly one disposition: **existing Lean
capital**, **landed here**, **private proof helper**, or **excluded with the
exact reason and range**. A worker may split one source declaration into
several named Lean lemmas, but must record the split. It may not silently omit,
fuse, weaken, or strengthen a source statement. Adaptation glue is visually
separate from source-derived content, as required by ledger E6.

### A1 — generic amortization

| source range | disposition |
|---|---|
| `SLTC.thy:53–302` | map assertion carrier, `emp`, star, existential, pure, credits and credit addition to `Ir/Assn.lean:739–856` and generic separation laws at `:242–434`; do not duplicate |
| `SLTC.thy:304–350` | map entailment and credit garbage collection to `Ir/Assn.lean:286`, `:795–834` and solver rules; add only a source-shaped lemma required by the amortization proof |
| `SLTC.thy:352–484` | map Hoare/frame/consequence to `Ir/Wp.lean:98–167` and `Sepref/Basic.lean:416–574`; do not duplicate |
| `SLTC.thy:486–573` | map atomic heap rules to `Ir/Triples.lean`; no new primitive rule |
| `SLTC_More.thy:7–161,186–260,262–345,610–631` | account as landed normalization, `GC`-entailment composition, `sepOr`, and consequence; add no unrelated assertion API |
| `SLTC_More.thy:165–184` | address/heap relation is superseded by named-cell state, D2/X13 |
| `SLTC_More.thy:347–606` | `ureturn`, assertion conjunction/precision, and auto2 pure classifier are outside the selected credit-discipline slice; no A1 consumer and X7 applies to automation |
| `Dynamic_Array.thy:6–200` | map cost arithmetic/time-refinement helpers to `Cost/ACost.lean`, `NREST/BackwardsReasoning.lean`, and `NREST/TimeRefinement.lean`; add only missing direct support lemmas |
| `Dynamic_Array.thy:202–291` | land `reclaim`, no-failure/specification laws, and time-refinement bridge |
| `Dynamic_Array.thy:293–305` | land potential-augmented assertion and invalidation preservation |
| `Dynamic_Array.thy:308–333` | land finite-cost predicate and extraction through existing `liftACost` |
| `Dynamic_Array.thy:336–458` | land time-frame helper and `hnRefine` payday/reclaim/amortization family |

### A2 — dynamic array (brief deferred)

`Dynamic_Array.thy:464–1005,1028–1091` and the two IHT ranges above are
active. Source `:627–628`, `:717–742`, `:1094–1157`, and `:1162–1313` is
unfinished/obsolete/undefined and excluded. In particular, `:1097–1107`
defines the concrete push/empty implementation and exchange rate as
`undefined` and leaves the interpretation proof unfinished. The A2 adapter is
therefore authored, bounded, and explicit about capacity. IHT More `:152–221`
(swap/filter) is a derived consumer outside the selected dynamic-array core.

### B1 — pure union-find

Port `Partial_Equivalence_Relation.thy:11–75`, `UnionFind.thy:8–59`, and
`Union_Find_Time.thy:20–649,813–828`. The source partial-function domain
package is rendered by total bounded-fuel definitions plus source equations
under `ufaInvar`; off-invariant behavior is not API. Keep helper Max lemmas
private where Lean/mathlib already supplies them, but account for source
lines 512–564 individually in the table.

### B2 — timed union-find (brief deferred)

Port `UnionFind_Impl.thy:7–86` and `Union_Find_Time.thy:651–811,832–1204`.
Initialization consumes two caller-owned `junkArrayOfLen n` buffers. Find and
compression are loop-form. Preserve functional results and invariant/logarithmic
bounds, but synthesize honest vector costs. The source proves worst-case
Theta(log n), not inverse-Ackermann amortization; no alpha(n) claim is allowed.

## 4. Validation policy and acceptance

Routine direct ports use source review, Lean typechecking, principal
kernel-three guards, the focused module build, the full proofs build, and
`lax build --only proofs word-ram`. They do **not** receive a ceremonial
compiled falsification suite.

Focused compiled differential tests are reserved for genuinely authored seams:

1. A1 vector `reclaim`: two-currency exact residual, insufficient potential,
   and currency isolation; use `-ᵣ`, never mathlib subtraction.
2. A2 bounded adapter: no-resize/resize boundary, full-capacity failure, and
   functional/cost agreement over push sequences.
3. B2 recursion-to-loop adaptation: small valid forests, both union-by-size
   branches, path compression, and exact vector-cost probes.

Each wave additionally requires zero `sorry`/`admit`/`native_decide`, a complete
in-file source table, no ND-MC import, no auto2, no P9 arena/touched-reset work,
no P5 Kruskal work, no machine-model changes, and no edits to sibling leaves.
The supervisor alone wires `Lax13Proofs.lean` after leaf acceptance.

## 5. Risks and exclusions

- `ECost` is a total function (`Cost/ACost.lean:34–37`), not `Finsupp`.
  Finite-cost extraction is pointwise and must not invent a finite-support
  premise.
- Resource subtraction is `-ᵣ`; `top - top` deliberately differs from
  mathlib subtraction (`Cost/ACost.lean:77–118`).
- The source dynamic-array concrete face is unfinished, and the local IR cannot
  allocate. P4-DYN-1 is the only authorized executable adaptation.
- The source union-find code is recursive and scalar-costed. Only B2 owns the
  loop/vector adaptation.
- Exclusions X1, X7, X10, X11, X13, X15, and X16 remain binding. Arena/reset is
  P9; Kruskal is P5 post-freeze; Edmonds–Karp and extra amortized structures are
  not idle-margin work.
