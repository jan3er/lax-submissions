# RAM stack plan (rev 3 — C0 written, awaiting the freeze review)

Status (2026-07-26): id **Lax11** provisioned via `lax init
ram-linear-time`; scaffold in place. Jan delegated the P-layer design
choices (D9–D12, settled below). The C0 surface decisions D1–D7 are
my recommendations and get their review at the step-1 freeze boundary
as planned.

**Steps 1–2 are drafted: the four C0 concept modules are written and
`lax build ram-linear-time` is OK** (manifest, abstract, both packages
green, no spec violations). The surface is *not* frozen — it is now a
concrete artifact to review rather than a sketch, which is exactly the
step-1 review object. Deltas from the sketch below are recorded as
D13–D15; three smoke tests validate it (see "Surface as written").

Goal: a reusable stack for honest algorithmic statements in Lax. The
concept surface talks about a **textbook RAM** — cost intrinsic to the
machine semantics, nothing annotation-based is trusted. The proof
package builds a tower of verified transpilation + reasoning layers
(P1–P3) so that algorithms are *written and verified once, shallowly*,
and compile down to RAM programs with cost bounds. Driver theorem:
**connected components in linear time**. Everything lands in a single
test submission (`ram-linear-time/`, id Lax11); we split
infrastructure from headline later.

Companion: the Courcelle discussion (chat, 2026-07-26). Courcelle is
the eventual consumer: phase-2 automaton run = one tree-fold `Prog` at
P3. This submission de-risks the entire stack first.

## C0 — concept surface

### RAM (definition-concept `Ram`)

Accumulator RAM, AHU §1.2 minus MULT/DIV (Cook–Reckhow honesty cut).
Values are unrestricted `ℕ`; with only `+`, monus and comparisons the
unit-cost model is standard and safe (D2).

```lean
/-- An operand: literal, direct address, or indirect address. -/
inductive Op | lit (n : ℕ) | mem (a : ℕ) | ind (a : ℕ)

/-- Instructions of the RAM. `sub` is truncated subtraction. -/
inductive Instr
  | load (o : Op) | store (a : ℕ) | storeInd (a : ℕ)
  | add (o : Op) | sub (o : Op)
  | jump (l : ℕ) | jzero (l : ℕ) | jgtz (l : ℕ)
  | halt

abbrev Program := List Instr

/-- Machine state: program counter, accumulator, memory. -/
structure State where
  pc : ℕ
  acc : ℕ
  mem : ℕ → ℕ

/-- One step; `none` iff halted (halt instruction or pc past the
program). Total, deterministic, ~25 lines. -/
def step (p : Program) (s : State) : Option State := ...

/-- `RunsTo p x y t`: started on input `x`, the machine halts after
exactly `t` steps with output `y` (I/O convention D3). -/
def RunsTo (p : Program) (x y : List ℕ) (t : ℕ) : Prop := ...
```

- Unit cost: time = number of `step`s to halt. No space measure (D6).
- I/O (D3): initial memory `mem 0 = x.length`, `mem (i+1) = x[i]`,
  zero elsewhere; on halt symmetrically `mem 0 = y.length`,
  `mem (i+1) = y[i]`. Memory-resident, no tapes, no heads.
- The interpreter `step` is the whole trusted semantics: one page,
  auditable against AHU §1.2 line by line.

### Computes / InTime (definition-concept `RamComputes`)

```lean
/-- `p` computes `f` on the set `D` of valid inputs. -/
def Computes (p : Program) (D : Set (List ℕ)) (f : List ℕ → List ℕ) : Prop :=
  ∀ x ∈ D, ∃ t, RunsTo p x (f x) t

/-- ... within `T x` steps. -/
def ComputesInTime (p : Program) (D : Set (List ℕ))
    (f : List ℕ → List ℕ) (T : List ℕ → ℕ) : Prop :=
  ∀ x ∈ D, ∃ t ≤ T x, RunsTo p x (f x) t

/-- Linear time on `D`. -/
def ComputesLinear (p : Program) (D : Set (List ℕ))
    (f : List ℕ → List ℕ) : Prop :=
  ∃ c, ComputesInTime p D f (fun x => c * (x.length + 1))
```

Linear bounds stated elementarily, `∃ c` (D4): `IsBigO` over families
of encoded inputs is filter noise with no reviewability gain; keep
`IsBigO` for genuinely asymptotic exponents later (FPT statements can
still use plain `∃ f : Params → ℕ`).

### Graph encoding (definition-concept `GraphEncoding`)

CSR adjacency (D5): `x = n :: m :: offsets(n+1) :: targets(2m)`;
validity predicate `EncodesGraph x n G` says offsets are monotone with
the right endpoints and, for all `u v : Fin n`, `G.Adj u v` iff `v`
occurs in `u`'s target segment. Dumb and canonical — the honesty
argument in the formalization notes must say why nothing is
precomputed (the encoding is exactly what every textbook hands the
algorithm). No sortedness, no multiplicity constraint beyond the iff.

### ConnectedComponents (theorem-concept, the driver)

Output convention (D7): the label array `ℓ` with
`ℓ v = min {u | G.Reachable u v}` (least vertex of the component) —
canonical, so the computed object is a *function* of the graph and
`Computes` applies unchanged.

```lean
/-- Connected components of a graph, as least-vertex labels. -/
noncomputable def ccLabels (n : ℕ) (G : SimpleGraph (Fin n)) : List ℕ := ...

/-- Connected components in linear time on the unit-cost RAM. -/
axiom ccLabels_computable_linear :
    ∃ p : Program, ∀ n G x, EncodesGraph x n G →
      -- packaged via ComputesLinear over D := valid encodings
      ...
```

(Exact packaging — one `ComputesLinear` over the sigma of encodings vs
the inlined form — is a step-1 decision; keep whichever reads more
like the textbook sentence.)

Surface size: four small files. The RAM interpreter is the only
nontrivial audit object.

## Surface as written (2026-07-26)

Four concepts, all green:

- `Lax11/Ram.lean` — `Op`, `Instr`, `Program`, `State`, `Op.value`,
  `write`, `step`, `run`, `cells`, `initState`, `RunsTo`. The I/O
  convention is carried by one function, `cells x` ("cell 0 holds the
  length, cell `i+1` the `i`-th entry, everything else 0"), used on
  both sides: the input pins *every* cell, the output only the first
  `|y|+1` (the rest is scratch).
- `Lax11/RamComputes.lean` — `ComputesInTime p D f T` only (D13).
- `Lax11/GraphEncoding.lean` — `vertexCount`, `edgeCount`, `offset`,
  `target`, and `EncodesGraph` as a seven-field `Prop`-structure
  (D14).
- `Lax11/ConnectedComponents.lean` — `label`, `ccLabels`, and the
  axiom `exists_linearTime_program_ccLabels` (D15).

Smoke tests in `proofs/` (helpers, no `conclusion:` frontmatter — they
exist to keep the surface from being quietly wrong):

- `RamSanity`: a five-instruction program is run end-to-end,
  `RunsTo lengthProgram x [x.length] 4`, plus its `ComputesInTime`
  packaging. The machine demonstrably halts, produces output, and the
  step count is the instruction count.
- `EncodingSanity`: `EncodesGraph [2,1,0,1,2,1,0] 2 ⊤` — the encoding
  is satisfiable and the header/offset/target index arithmetic lines
  up. Without this the headline theorem could be vacuously true.
- `Labels`: `label_eq` (the least-vertex characterization later work
  will use) and the computations `ccLabels ⊤ = [0,0]`,
  `ccLabels ⊥ = [0,1]` on `Fin 2`.

Watch item for the review: the concept package generates no auxiliary
declarations of its own, but `simp [cells]` *in the proof package*
emits `Lax11.Ram.cells.match_1.splitter`, which the namespace rule
rejects. Proof-side lemmas about `cells` must therefore be stated and
proved without `simp`-unfolding it (`rfl` and explicit equation lemmas
are fine). This will recur throughout P1–P3.

## Proof-package tower

All of P1–P3 lives in `ram-linear-time/proofs/` for now (D8); the
split into a standalone package happens when a second consumer exists.

### P1 — IMP+ and verified compilation to RAM

Structured while-language, the compilation target of P3 and the level
where the RAM's flatness is dealt with once:

- Syntax: scalar variables and array names (both `String`), `Expr`
  over `+`/monus/literals/vars/array-reads, commands
  `skip / assign / arrStore / seq / if / while`, and a program header
  declaring each array's extent (D11).
- Environment (D10): `vars : String → ℕ`, `arrs : String → List ℕ`.
  Expression evaluation is `Option`-valued; an out-of-bounds array
  access has **no big-step derivation** (stuck, not
  default-to-zero) — this is what makes the layout simulation
  provable, since a defaulting semantics would diverge from what the
  flat RAM memory returns. Cost = 1 + syntactic size of the
  expressions used, per executed construct. Distinct names are
  disjoint *by construction* — aliasing dies here, permanently;
  nothing above P1 reasons about memory overlap (this is the move
  that replaces separation logic).
- Extents (D11): the header declares each array's length as an `Expr`
  over literals and reads of the reserved input array only (CC needs
  extents `n`, `n+1`, `2m` — all input cells or sums thereof).
  Reserved names `INPUT`/`OUTPUT` carry the I/O convention into IMP+.
- Compiler `compileCom : ImpProg → Program`: prologue evaluates the
  extent Exprs (input cells sit at known RAM addresses), accumulates
  base addresses by additions into reserved cells, then the body
  lowers control flow to jumps and array indexing to base+index
  indirect addressing.
- Simulation theorem, the P1 deliverable:
  `⟨c, σ_init(x)⟩ ⇓[t] σ' → ∃ t' ≤ C_c * (t + 1), RunsTo (compileCom c) x (out σ') t'`
  with `C_c` program-dependent, input-independent. O()-sloppy
  constants throughout; nothing is tight, ever.

Precedent: Concrete Semantics ch. 8 plus a cost index
(Nipkow–Haslbeck, *Hoare Logics for Time Bounds*). No research risk;
the grind is the layout invariant.

### P2 — thin Hoare-with-time kit over IMP+

`{P} c {Q | t}` as a semantic definition + derived rules (seq/if/
while-with-invariant-variant-and-cost-potential). Deliberately thin:
P2 exists to prove the P1/P3 compilers and as the fallback for ad-hoc
programs. End users live at P3; if P3 works, P2 never grows a VCG.

### P3 — the catch: write once, shallowly

Design (D9): a **deep first-order combinator DSL with a shallow
denotation**, not lockstep refinement of hand-written IMP+.

```lean
/-- First-order imperative programs over named scalars/arrays.
Deep enough to compile, denoted shallowly for reasoning. -/
inductive Prog
  | assign (v : String) (e : Expr)
  | arrStore (a : String) (i e : Expr)
  | seq (p q : Prog)
  | ite (c : Cond) (p q : Prog)
  | while (c : Cond) (body : Prog)
  | skip
```

with three artifacts (D12 — rev 2 correction: rev 1 sketched a
fuel-free `M α := Env → Option (α × Env × ℕ)` denotation, which is
not definable for `while` in Lean without well-founded plumbing; the
settled design makes fuel explicit but invisible):

1. `run : Prog → Env → ℕ → Option (Env × ℕ)` — an executable
   **fuel interpreter** (fuel bounds steps; returns the final
   environment and the cost incurred, charging exactly the IMP+ cost
   model so the compiler correctness proof stays structural).
   Monotonicity in fuel is proved once. Termination and cost merge:
   `RunsWithin p env k env' := ∃ f, run p env f = some (env', k')`
   with `k' ≤ k`.
2. A **combinator rule library** proved once by induction on fuel:
   seq/ite congruence rules and the workhorse while-rule
   (invariant + ℕ-variant + cost potential ⇒ `RunsWithin` with the
   summed bound). **Per-algorithm proofs never mention fuel** — they
   instantiate invariants and variants against a pure Lean model
   function, with `run`'s executability available for `simp`/`decide`
   on straight-line fragments.
3. `compileProg : Prog → ImpCom` — structural, near-identity (Prog is
   IMP+-shaped by design; the DSL's value is the *reasoning layer*,
   not syntax distance) — plus adequacy in one direction:
   `run p env f = some (env', k)` implies the compiled command
   big-steps to the matching state with cost `≤ C_p * (k + 1)`.

So the workflow per algorithm is: write `Prog`; prove
`RunsWithin prog (load x) (c * size x) (store (model x))` via the
rule library against the pure model; get the RAM program and its
linear bound by composing adequacy + P1 simulation. Tick-monad
ergonomics, but the counts are *theorems about compiled code*, not
trusted annotations.

`Cond` stays minimal: `Expr = Expr` and `Expr < Expr` (other
comparisons via monus tricks or branch swaps at the `Prog` level).

P4 (schema library — verified fold/map/BFS-loop patterns over `Prog`)
is explicitly out of scope for this submission; it emerges from
whatever lemmas the driver forces, and gets named when Courcelle
needs it.

### Driver — connected components at P3

- Pure model: `ccPure : CSR → List ℕ` via BFS over the CSR arrays;
  prove `ccPure = ccLabels` using mathlib `SimpleGraph.Reachable` /
  `ConnectedComponent` (small; reachability API exists).
- `Prog`: standard BFS/CC — visited array, queue array with head/tail
  indices, label array; outer loop over vertices, inner BFS loop.
  Cost: each vertex enqueued once, each CSR slot scanned once —
  the invariant is "cost so far ≤ c₁·(processed queue entries) +
  c₂·(scanned slots) + c₃"; no amortization subtleties.
- Assemble: adequacy + P1 simulation discharge the concept axiom;
  `#print axioms` audit to standard axioms only.

## Steps

1. **Statement design** — ✅ drafted, ⏸ *not frozen*. C0 is written out
   (RAM instruction list, `step`, I/O, `ComputesInTime`, CSR validity,
   `ccLabels`, axiom packaging), against the pinned mathlib (toolchain
   v4.30.0, same rev as Lax5), with D13–D15 recorded above. →
   **awaiting Jan review; then D-record updated and surface frozen.**
   Open questions I would put to that review: (a) is dropping
   `Computes`/`ComputesLinear` from the surface right, or is the named
   "linear time" vocabulary worth an unused definition? (b) `edgeCount`
   as declared length rather than the true edge count — keep, or add
   the no-repetition field? (c) is the `Prop`-structure the right shape
   for `EncodesGraph`, against a plain conjunction?
2. **Concepts package** — ✅ four modules, manifest (title, author,
   AHU + Cook–Reckhow bib entries), abstract; `lax build` OK, no
   violations; three smoke tests in the proof package.
3. **P1**: IMP+ semantics, compiler, simulation theorem. Smoke test:
   a five-line IMP+ program ("sum the input") taken end-to-end to a
   RAM `ComputesLinear` by hand, *before* P3 exists — validates the
   chain early. → **checkpoint: report constants/pain level.**
4. **P2**: the thin Hoare kit, as needed by 3/5.
5. **P3**: `Prog`, `run`, rule library, `compileProg`, adequacy.
   Re-run the smoke test at P3 (should shrink to a few lines of
   rule-library reasoning). → **checkpoint: this is the make-or-break ergonomics
   review; if the while-rule at denotation level is unpleasant,
   fallback is P2-style lockstep refinement before the driver.**
6. **Driver**: `ccPure` + mathlib proof, BFS `Prog`, cost invariant,
   assembly, axiom discharge, audit.
7. **Wrap-up**: formalization notes (honesty ledger: D2 no-MULT
   rationale, D5 encoding dumbness, D7 label convention, D4 bound
   form), abstract, build-output, commit.

Feasibility judgment: P1/P2 are textbook-plus-cost-index (the
Isabelle precedents solved strictly harder problems — separation
logic, nondeterministic refinement, real extraction, tight constants
— all deliberately absent here). P3 is the one novel design; it is
first-order, closure-free, and has a bounded fallback. The driver's
math side is small. No step has research-grade risk; step 5 has
ergonomics risk, contained by the step-3 smoke test and the fallback.

## Decision record (rev 2 — D8–D12 settled by Jan's delegation
2026-07-26; D1–D7 are recommendations reviewed at the step-1 surface
freeze)

- **D1** RAM flavor: accumulator machine, AHU §1.2 instruction set
  minus MULT/DIV, lit/direct/indirect operands, `halt` instruction,
  unit cost, deterministic `step` interpreter as the semantics.
- **D2** No MULT/DIV/bit-ops: unit-cost honesty (Cook–Reckhow).
  Constant-factor multiplications are unrolled additions; nothing we
  target needs more. Extending the instruction set later is a *new*
  concept, argued then.
- **D3** I/O memory-resident: `mem 0` = length, `mem (i+1)` = words;
  same convention for output on halt. No tapes.
- **D4** Time bounds on the surface are elementary (`∃ c, ≤ c·(|x|+1)`),
  not `IsBigO` over input filters.
- **D5** Graph encoding: CSR with an iff-validity predicate; dumbness
  argued in formalization notes.
- **D6** Time only; no space measure in this submission.
- **D7** CC output: least-vertex labels (canonical function).
- **D8** (settled) Single test submission holds C0 + P1–P3 + driver;
  split infra/headline later. Id **Lax11**, dir `ram-linear-time/`,
  provisioned via `lax init` 2026-07-26.
- **D9** (settled) P3 = deep first-order `Prog` DSL + executable
  denotation + compiler + adequacy; reasoning at the denotation,
  never on compiled artifacts. Fallback: lockstep refinement at P2.
- **D10** (settled) IMP+ env `vars : String → ℕ`,
  `arrs : String → List ℕ`; out-of-bounds access is stuck (no
  big-step derivation), never default-valued — required for the
  layout simulation. `Option`-valued expression eval; cost = 1 +
  expression size per executed construct.
- **D11** (settled) Array extents: header Exprs over literals and
  reads of the reserved `INPUT` array only; compiler prologue
  computes cumulative bases by additions. Reserved `INPUT`/`OUTPUT`
  names carry the I/O convention.
- **D13** (mine, review at the freeze) The `Computes*` concept declares
  **only** `ComputesInTime p D f T`. `Computes` (untimed) and
  `ComputesLinear` were dropped: nothing in the submission uses them,
  and unused declarations are review surface spent for nothing. The
  linear bound therefore appears literally as `c * (x.length + 1)` at
  the point of use, which is also more transparent than an indirection.
  The reason `ComputesLinear` *cannot* be used for the driver is
  quantifier order — it hides `∃ c` inside, and the constant must be
  chosen before the graph, not after it.
- **D14** (mine) `EncodesGraph x n G` is a `Prop`-structure with seven
  named fields (`vertexCount_eq`, `length_eq`, `offset_zero`,
  `offset_last`, `offset_mono`, `target_lt`, `adj_iff`), so each
  condition is a separately checkable obligation. Cells are read with
  `List.getD` (default 0), which `length_eq` makes unreachable at every
  constrained position; this keeps the encoding proof-obligation-free
  in the concept. `edgeCount x` is only the *declared* half-length of
  the target array: with repetitions permitted it is ≥ the number of
  edges, and equal exactly when no block repeats a neighbor. Both
  dumbnesses (no sortedness, repetitions allowed) weaken the hypothesis
  and hence strengthen the theorem.
- **D15** (mine) Driver packaging: the inlined form loses, the
  `ComputesInTime` form wins —
  `∃ p c, ∀ n G, ComputesInTime p {x | EncodesGraph x n G}
  (fun _ => ccLabels G) (fun x => c * (x.length + 1))`. One program and
  one constant, quantified ahead of the graph; the domain is the
  encodings *of that graph*, so the function is constant on it and no
  choice function is needed to turn "the graph encoded by `x`" into a
  `List ℕ → List ℕ`. `label` is `sInf (Fin.val '' {u | G.Reachable u v})`
  — the least *number* of a reachable vertex — and `ccLabels` is
  `List.ofFn (label G)`.
- **D12** (settled) P3 denotation is a fuel interpreter
  `run : Prog → Env → ℕ → Option (Env × ℕ)` with fuel-monotonicity
  and a once-proved combinator rule library (seq/ite rules,
  while-rule with invariant + variant + cost potential); fuel never
  appears in per-algorithm proofs. Adequacy proved in the
  run-success → big-step direction only. (Rev 2 correction: rev 1's
  fuel-free `Option` state monad is not definable for `while`.)
