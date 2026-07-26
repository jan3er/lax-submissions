# RAM stack plan (rev 5 — C0 frozen, P1 done, P3 next)

Status (2026-07-26): id **Lax11** provisioned via `lax init
ram-linear-time`; scaffold in place. Jan delegated the P-layer design
choices (D9–D12, settled below) and, in the session of 2026-07-26 (2),
the answers to the three step-1 review questions ("follow your
recommendations").

**Steps 1–3 are done.** The surface is frozen at the recommended
answers: `ComputesInTime` only (D13 kept), `edgeCount` = declared
half-length with repetitions permitted (D14 kept), `EncodesGraph` a
`Prop`-structure (D14 kept). Writing the compiler then forced one
*substantive* correction to the frozen shape — the memory-resident I/O
convention D3 makes a one-accumulator machine unable to address its
scratch space, so I/O moved to the input and output tapes of the cited
source (**D16**), which is the model AHU §1.2 actually defines. With
tapes, IMP+ does its own I/O (**D17**) and the array-extent header
(D11) evaporates. **P1 is finished and green**: compiler, simulation
theorem, and the step-3 smoke test taken all the way to a
`ComputesInTime` statement about a concrete machine program. The
step-3 checkpoint report is below.

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
  | read (a : ℕ) | write (o : Op)
  | load (o : Op) | store (a : ℕ) | storeInd (a : ℕ)
  | add (o : Op) | sub (o : Op)
  | jump (l : ℕ) | jzero (l : ℕ) | jgtz (l : ℕ)
  | halt

abbrev Program := List Instr

/-- Machine state: program counter, accumulator, memory, the input not
yet read, the output written so far. -/
structure State where
  pc : ℕ
  acc : ℕ
  mem : ℕ → ℕ
  inp : List ℕ
  out : List ℕ

/-- The instruction semantics; `none` iff the machine halts (`halt`, or
a read from an exhausted tape). -/
def Instr.effect : Instr → State → Option State := ...

/-- One step: fetch, then execute; `none` also when pc ran past the
program. -/
def step (p : Program) (s : State) : Option State :=
  p[s.pc]?.bind fun i => i.effect s

/-- `RunsTo p x y t`: started on input tape `x`, the machine halts
after exactly `t` steps with output tape `y` (I/O convention D16). -/
def RunsTo (p : Program) (x y : List ℕ) (t : ℕ) : Prop := ...
```

- Unit cost: time = number of `step`s to halt. No space measure (D6).
- I/O (D16): read-only input tape, write-only output tape, all memory
  cells initially zero. `RunsTo` constrains the output tape and nothing
  else.
- The interpreter `Instr.effect`/`step` is the whole trusted semantics:
  one page, auditable against AHU §1.2 line by line.

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

## Surface as written (2026-07-26, frozen)

Four concepts, all green:

- `Lax11/Ram.lean` — `Op`, `Instr`, `Program`, `State`, `Op.value`,
  `setCell`, `Instr.effect`, `step`, `run`, `initState`, `RunsTo`. The
  I/O convention is the tapes (D16): `initState x` has all cells zero,
  `inp = x`, `out = []`, and `RunsTo p x y t` says the machine halts
  after exactly `t` steps with `out = y`.
- `Lax11/RamComputes.lean` — `ComputesInTime p D f T` only (D13).
- `Lax11/GraphEncoding.lean` — `vertexCount`, `edgeCount`, `offset`,
  `target`, and `EncodesGraph` as a seven-field `Prop`-structure
  (D14).
- `Lax11/ConnectedComponents.lean` — `label`, `ccLabels`, and the
  axiom `exists_linearTime_program_ccLabels` (D15).

Smoke tests in `proofs/` (helpers, no `conclusion:` frontmatter — they
exist to keep the surface from being quietly wrong):

- `RamSanity`: a six-instruction program is run end-to-end,
  `RunsTo sumProgram (a :: b :: x) [a + b] 6` (by `⟨_, rfl, rfl, rfl⟩`
  — the semantics computes), plus its `ComputesInTime` packaging. The
  machine demonstrably reads its tape, halts, writes an output, and the
  step count is the instruction count.
- `EncodingSanity`: `EncodesGraph [2,1,0,1,2,1,0] 2 ⊤` — the encoding
  is satisfiable and the header/offset/target index arithmetic lines
  up. Without this the headline theorem could be vacuously true.
- `Labels`: `label_eq` (the least-vertex characterization later work
  will use) and the computations `ccLabels ⊤ = [0,0]`,
  `ccLabels ⊥ = [0,1]` on `Fin 2`.

Watch item, still live: the concept package generates no auxiliary
declarations of its own, but `simp`-unfolding a concept definition that
was written by pattern matching emits e.g.
`Lax11.Ram.Instr.effect.match_1.splitter` *from the proof package*,
which the namespace rule rejects (only `Lax11Proofs`-prefixed names may
be declared there). The discipline throughout P1–P3: state the equation
lemmas you want in `Lax11Proofs`, prove them by `rfl`, and simp with
those. Never `simp [Instr.effect]`.

## Proof-package tower

All of P1–P3 lives in `ram-linear-time/proofs/` for now (D8); the
split into a standalone package happens when a second consumer exists.

### P1 — IMP+ and verified compilation to RAM

Structured while-language, the compilation target of P3 and the level
where the RAM's flatness is dealt with once:

- Syntax: scalar variables and array names (both `String`), `Expr`
  over `+`/monus/literals/vars/array-reads, commands
  `skip / assign / store / seq / if / while / read / write`. No
  program header, no array extents: since the machine's memory starts
  zeroed and is unbounded, an array of any length costs nothing to
  have, so the array lengths live in the *initial environment* the
  user of the simulation theorem picks (D17).
- Environment (D10): `vars : String → ℕ`, `arrs : String → List ℕ`,
  plus `inp`/`out` for the tapes.
  Expression evaluation is `Option`-valued; an out-of-bounds array
  access has **no big-step derivation** (stuck, not
  default-to-zero) — this is what makes the layout simulation
  provable, since a defaulting semantics would diverge from what the
  flat RAM memory returns. Cost = 1 + syntactic size of the
  expressions used, per executed construct. Distinct names are
  disjoint *by construction* — aliasing dies here, permanently;
  nothing above P1 reasons about memory overlap (this is the move
  that replaces separation logic).
- I/O is by the commands `read x` (scalar) and `write e` (D17), which
  compile to one and two instructions; the tapes are in the
  environment. So I/O cost is *in* the IMP+ cost of the run and the
  simulation bound stays the clean `C_c · (k + 1)` — no prologue, no
  epilogue, no reserved `INPUT`/`OUTPUT` names.
- Compiler `compile : Layout → Com → ℕ → Program` (the `ℕ` is the
  address the block is laid at, because machine jumps are absolute);
  control flow lowers to jumps, array indexing to indirect addressing.
- Simulation theorem, the P1 deliverable:
  `BigStep c (initEnv ext x) σ' k → ∃ t ≤ C_c * k, RunsTo (compileProgram c) x σ'.out t`
  with `C_c` program-dependent, input-independent. O()-sloppy
  constants throughout; nothing is tight, ever.

Precedent: Concrete Semantics ch. 8 plus a cost index
(Nipkow–Haslbeck, *Hoare Logics for Time Bounds*). No research risk;
the grind is the layout invariant.

#### Why the I/O convention had to change (D16)

Kept here because it is the one argument in this plan that a reader
will want to check. The compiler needs a constant number of scratch
cells at addresses it knows statically. With the input laid out in
memory from cell 1 (the old D3), free memory begins at cell `|x|+1`,
an address known only at run time, so scratch must be reached through
a pointer cell. There is exactly one statically-known cell to hold
that pointer (cell 0, the length), the machine has one accumulator,
and moving the pointer destroys it — so a memory-to-memory move is
impossible, and *no* compiler exists for that convention unless the
concept surface itself reserves an arbitrary constant number of cells.
Tapes remove the problem at the root: memory starts empty, so every
address is static. They are also what the cited source defines. The
price is that the machine cannot random-access its input without
copying it, one instruction per number, which no linear-time algorithm
minds.

**Layout (D18).** Temporaries in cells `0 … T-1`, the `i`-th scalar in
cell `T + i`, entry `i` of the `j`-th array in cell `T + p + j + q·i`
(`p` scalars, `q` arrays). Arrays are *interleaved*, not blocked:
lengths are unbounded, so blocks would need run-time bases again,
while striding by `q` keeps every address a static affine function of
the index for `q` additions per access. Address space is free (D6).

#### Status (rev 5, 2026-07-26): P1 is done

Five modules in `proofs/Lax11Proofs/`, all green, axiom audit clean
(`propext`, `Classical.choice`, `Quot.sound`):

- `Imp.lean` — `Expr` / `Cond` / `Com` (incl. `read`/`write`), `Env`
  with the two tapes, `Option`-valued evaluation, the cost-indexed
  `BigStep`, `BigStep.unique`, `initEnv`.
- `Machine.lean` — the concept's equations restated as `rfl` lemmas in
  this package's namespace, `run_add`/`run_trans`/`run_one`, and
  `Fits` (block placement) with its append/singleton lemmas.
- `Compile.lean` — `Layout`, the address functions, `compileExpr`,
  `condExpr`/`compileCond`, `compile`, `compileProgram`, the `Ok`
  predicates, `size`/`esize`/`bsize` with `compile_length`, and the
  injectivity of the layout (`index_inj` and friends).
- `Simulation.lean` — `Represents`, `Reaches`, `compileExpr_correct`,
  `compileCond_correct`, `compile_correct` (the induction on the
  derivation) and `compileProgram_runsTo`.
- `SumSmoke.lean` — the step-3 end-to-end test.

The deliverable:

```lean
theorem compileProgram_runsTo (hok : Com.Ok L c)
    (hbs : BigStep c (initEnv ext x) σ' k) :
    ∃ t ≤ L.const * k, RunsTo (compileProgram L c) x σ'.out t
```

`L.const = 3 * L.idxLen + 13`, and `L.idxLen = (#arrays - 1) + 3` is
the cost of one array access. So the constant depends on the layout
only, never on the program or the input.

Design points that survived contact (see D16–D18 for the decisions):

- **Conditions compile through the expression compiler.** `condExpr`
  turns a condition into an expression that is zero exactly when the
  condition holds — `(e-f)+(f-e)` for equality, `1-(f-e)` for order —
  which truncated subtraction makes sound. Both are then followed by
  the same `jzero`. This deleted an entire second instruction chain
  from the proof; it was the single biggest simplification.
- **`Reaches` is the right abstraction for straight-line code.** It
  bundles fall-through, step count, accumulator, untouched tapes, and
  the frame condition "writes only temporaries from `d` upwards". The
  frame clause is what lets the two operands of a binary operator be
  compiled at consecutive depths with the first result surviving.
- **Array lengths never reach the machine.** They only decide which
  IMP+ programs have a derivation, so the all-zero memory of a
  starting machine represents an initial environment with zero-filled
  arrays of *any* declared lengths. `initEnv` takes the lengths as a
  parameter and they cost nothing.
- The compiler was checked by **evaluation** (`#eval` on the fuel-free
  `run`) before any proving: successor, array store/read, a summing
  while-loop, both branches of an equality test. Two real bugs would
  have cost hours of proof debugging otherwise. Do this again at P3.

#### Step-3 checkpoint: constants and pain level

**Constants.** For the smoke test's layout (four scalars, no arrays,
two temporaries) `L.const = 22`, the IMP+ derivation costs `21` per
input number, so the concept-level bound is `462 * (|x| + 1)` where
the compiled program actually takes about `19 * |x|` steps. Loose by
roughly 30×, and deliberately: no step of the tower attempts a tight
constant, and the driver's statement only needs *some* constant.

**Pain level, honestly.** The simulation proof itself was a grind but
never in doubt: about 700 lines, of which the genuinely fiddly part is
`Fits` bookkeeping (splitting a block's placement hypothesis and
matching program-counter arithmetic across `++`). The pattern that
worked is: right-associate the code with a `show ... from by simp
[List.append_assoc]`, `rw [fits_append, …]`, then `Fits.congr (by
omega)` whenever an address does not match syntactically.

What the smoke test *actually* measured is the cost of using P1
directly, and this is the number that matters for the P3 decision: a
five-line program needed ~60 lines of proof, of which ~25 are the loop
lemma. The loop is proved by induction on the input that is left (its
variant) with the invariant inlined into the statement, and the cost
bound is carried as a `≤` alongside. Two frictions dominate:

1. **Environment bookkeeping.** Every `setVar` is a function update, so
   reading a variable back is a chain of `if`-reductions
   (`simp [Env.setVar]` handles it, but it is in every step).
2. **Cost arithmetic on the nose.** The `BigStep` constructors produce
   costs like `1 + b.size + k + k'` which are *not* definitionally
   `13 + k`, so the existential's witness has to be left as `_` and
   bounded afterwards by `omega`.

Both are exactly what P3's rule library is meant to absorb: the
while-rule takes an invariant, a variant and a cost potential and the
per-algorithm proof never sees a derivation. The measurement says P3 is
worth building; it also says the fallback (P2-style lockstep
refinement) would be unpleasant, since it would keep friction 1.

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

1. **Statement design** — ✅ done, **frozen** 2026-07-26. C0 is written
   out (RAM instruction list, `Instr.effect`, tape I/O, `ComputesInTime`,
   CSR validity, `ccLabels`, axiom packaging), against the pinned
   mathlib (toolchain v4.30.0, same rev as Lax5). The three review
   questions were answered by Jan's delegation with "follow the
   recommendation": (a) `Computes`/`ComputesLinear` stay dropped,
   (b) `edgeCount` stays the declared half-length with repetitions
   permitted, (c) `EncodesGraph` stays a `Prop`-structure. D13–D15 are
   therefore settled; the one later change is D16, which is not a
   review answer but a correction forced by the compiler.
2. **Concepts package** — ✅ four modules, manifest (title, author,
   AHU + Cook–Reckhow bib entries), abstract; `lax build` OK, no
   violations; three smoke tests in the proof package.
3. **P1** — ✅ done. IMP+ semantics, compiler, simulation theorem, and
   the smoke test: `sumProgram_computesInTime` is a `ComputesInTime`
   statement of the concept surface about a concrete machine program,
   proved through the tower. → **checkpoint reported above.**
4. **P2**: the thin Hoare kit — *skipped for now*. P1 needed nothing
   from it and P3 is the ergonomic answer; it stays available as the
   fallback if step 5 disappoints.
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

## Decision record (rev 4 — D8–D12 settled by Jan's delegation
2026-07-26; D1–D7 and D13–D15 frozen at the step-1 review, which
answered "follow the recommendation"; D16–D18 are mine, taken while
writing the compiler)

- **D1** RAM flavor: accumulator machine, AHU §1.2 instruction set
  minus MULT/DIV, lit/direct/indirect operands, `halt` instruction,
  unit cost, deterministic `step` interpreter as the semantics.
- **D2** No MULT/DIV/bit-ops: unit-cost honesty (Cook–Reckhow).
  Constant-factor multiplications are unrolled additions; nothing we
  target needs more. Extending the instruction set later is a *new*
  concept, argued then.
- **D3** (superseded by D16) I/O memory-resident: `mem 0` = length,
  `mem (i+1)` = words; same convention for output on halt. No tapes.
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
- **D11** (settled, then dropped by D17) Array extents: header Exprs
  over literals and reads of the reserved `INPUT` array only; compiler
  prologue computes cumulative bases by additions. Reserved
  `INPUT`/`OUTPUT` names carry the I/O convention.
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
- **D16** (mine, forced by the compiler) I/O is by AHU's read-only
  input tape and write-only output tape, with `read a` and `write o`
  instructions; memory starts all zero. Supersedes D3. Rationale in
  "Why the I/O convention had to change" above: with a memory-resident
  input the compiler has no statically-addressable scratch and a
  one-accumulator machine cannot then move memory to memory. Side
  benefits: the surface loses the `cells` function and the asymmetric
  "only the first `|y|+1` cells are constrained" clause, and it now
  matches the cited source verbatim. Cost: no sublinear-time
  algorithms, which this stack does not contain.
- **D17** (mine) IMP+ does its own I/O with `read`/`write` commands and
  has no header and no array extents. Array lengths belong to the
  initial environment (`initEnv ext x`), because the machine never
  represents them: they are exactly the fiction that makes
  out-of-range access stuck, and the machine's zeroed unbounded memory
  represents zero-filled arrays of *any* lengths for free. This kills
  D11's extent machinery, the prologue, the epilogue and the reserved
  names, and it restores the clean `t ≤ C_c · k` bound (I/O cost is in
  `k` because I/O is a command).
- **D18** (mine) Static layout: temps `0 … T-1`, scalars above them,
  arrays *interleaved* with stride `q` = number of arrays. Blocked
  arrays would need run-time bases (lengths are unbounded); striding
  keeps every address a static affine function of the index at a cost
  of `q` additions per access, and address space is free under D6.
- **D12** (settled) P3 denotation is a fuel interpreter
  `run : Prog → Env → ℕ → Option (Env × ℕ)` with fuel-monotonicity
  and a once-proved combinator rule library (seq/ite rules,
  while-rule with invariant + variant + cost potential); fuel never
  appears in per-algorithm proofs. Adequacy proved in the
  run-success → big-step direction only. (Rev 2 correction: rev 1's
  fuel-free `Option` state monad is not definable for `while`.)
