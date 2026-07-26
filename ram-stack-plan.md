# RAM stack plan (rev 1 — draft for Jan's review)

Status (2026-07-26): design draft. Nothing scaffolded yet. Review
boundary: decisions D1–D9 below, then step 1 freezes the concept
surface.

Goal: a reusable stack for honest algorithmic statements in Lax. The
concept surface talks about a **textbook RAM** — cost intrinsic to the
machine semantics, nothing annotation-based is trusted. The proof
package builds a tower of verified transpilation + reasoning layers
(P1–P3) so that algorithms are *written and verified once, shallowly*,
and compile down to RAM programs with cost bounds. Driver theorem:
**connected components in linear time**. Everything lands in a single
test submission (working dir `ram-linear-time/`); we split
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

## Proof-package tower

All of P1–P3 lives in `ram-linear-time/proofs/` for now (D8); the
split into a standalone package happens when a second consumer exists.

### P1 — IMP+ and verified compilation to RAM

Structured while-language, the compilation target of P3 and the level
where the RAM's flatness is dealt with once:

- Syntax: scalar variables and array names (both `String`), `Expr`
  over `+`/monus/literals/vars/array-reads, commands
  `skip / assign / arrStore / seq / if / while`, and a program header
  declaring each array's extent as an `Expr` over input-derived
  scalars.
- Semantics: big-step `⟨c, σ⟩ ⇓[t] σ'`, cost = 1 + expression sizes
  per executed construct. Distinct names are disjoint *by
  construction* — aliasing dies here, permanently; nothing above P1
  reasons about memory overlap (this is the move that replaces
  separation logic).
- Compiler `compileCom : ImpProg → Program`: prologue evaluates
  extents and lays out arrays (base-address table, bump layout),
  body lowers control flow to jumps, array indexing to
  base+index indirect addressing.
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

with three artifacts:

1. `denote : Prog → M Unit` where `M α := Env → Option (α × Env × ℕ)`
   is a fuel-free cost-counting state monad over the *named*
   environment (`Option` for divergence; termination obligations are
   discharged where the cost bound is proved — a cost bound is a
   fuel bound). **All reasoning happens here**: `denote` is
   executable, simp-friendly, and proofs relate it to pure model
   functions by induction on loops with invariants.
2. `compileProg : Prog → ImpCom` — structural, near-identity (Prog is
   IMP+-shaped by design; the DSL's value is the *denotation*, not
   syntax distance).
3. Adequacy: `denote p env = some (_, env', k)` implies the compiled
   command big-steps to the matching state in cost `≤ C_p * (k + 1)`.

So the workflow per algorithm is: write `Prog`; prove
`denote prog ∘ load = pure model` and `cost ≤ c * size` at the
denotation level against a pure Lean model function; get the RAM
program and its linear bound by composing adequacy + P1 simulation.
Tick-monad ergonomics, but the counts are *theorems about compiled
code*, not trusted annotations.

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

1. **Statement design** — freeze C0 exactly (RAM instruction list,
   `step`, I/O, `Computes*`, CSR validity, `ccLabels`, axiom
   packaging). Written against the pinned mathlib
   (toolchain v4.30.0, same rev as Lax5). → **Jan review, D-record
   updated, surface frozen.**
2. **Scaffold + concepts package** (`ram-linear-time/concepts/`,
   manifest, abstract stub). Builds green.
3. **P1**: IMP+ semantics, compiler, simulation theorem. Smoke test:
   a five-line IMP+ program ("sum the input") taken end-to-end to a
   RAM `ComputesLinear` by hand, *before* P3 exists — validates the
   chain early. → **checkpoint: report constants/pain level.**
4. **P2**: the thin Hoare kit, as needed by 3/5.
5. **P3**: `Prog`, `M`, `denote`, `compileProg`, adequacy. Re-run the
   smoke test at P3 (should shrink to a few lines of denotation
   reasoning). → **checkpoint: this is the make-or-break ergonomics
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

## Decision record (rev 1 — all pending Jan's sign-off)

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
- **D8** Single test submission holds C0 + P1–P3 + driver; split
  infra/headline later. Working id Lax6 (confirm numbering).
- **D9** P3 = deep first-order `Prog` DSL + shallow cost-monad
  denotation + compiler + adequacy; reasoning at the denotation,
  never on compiled artifacts. Fallback: lockstep refinement at P2.
