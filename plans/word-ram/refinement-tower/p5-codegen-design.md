# P5 design record — the verified code generator, IR → IMP+ `Com`

2026-07-30, supervisor-authored. This is the one component of the tower
without an Isabelle original (ledger D3: `isabelle_llvm_time`'s final
step is a trusted printer to LLVM text; ours is verified into the deep
IMP+ embedding). There is therefore no source to stay faithful to; this
note is the spec the waves implement, and deviations from *it* get
P5/D-flags.

## What exists on each side

- **IR** (`Refine/Ir/`): `Ir.Com` — skip / const / copy / binop / aget
  / aset / seq / ite / while over `String`-named cells; `Ir.State` =
  partial maps (`vars : String → Option Val`, `arrs : String → Option
  (List Val)`); deterministic `Ir.BigStep : Com → State → State → Cost
  → Prop` charging one unit of one `ir.*` currency per op
  (`Cost = ACost String ℕ`, `κ.toFun : String → ℕ`, support ⊆
  `Currency.all`). Every op *requires* its cells to exist (partiality =
  stuckness). No I/O, no bounds (D-a removed truncation).
- **IMP+** (`Imp.lean`, `Reasoning.lean`, `Spec.lean`): `Imp.Com` with
  compound `Expr`, total `Env` (plus `inp`/`out` tapes), unbounded
  `Imp.BigStep` costing `1 + size-of-expressions`, bounded
  `BigStepB B` (every produced value `< B`, via `evalB`), `Run B c σ σ'
  K` = cost-≤ closure, `Spec B P c Q K` phase interface, and the endorsed
  boundary `Transfer.Solves L c D f B K` →
  `computesInTime_of_solves` → `ComputesInTime w (compileProgram L c) D f T`.

## The five pieces

### 1. Embedding (`Refine/Codegen/Embed.lean`)

`embed : Ir.Com → Imp.Com`, name-identical, one IMP+ command per IR op:

| IR | IMP+ | IMP+ cost |
|---|---|---|
| `skip` | `skip` | 1 |
| `const x n` | `assign x (.lit n)` | 2 |
| `copy x y` | `assign x (.var y)` | 2 |
| `binop op x y z` | `assign x (.bin op (.var y) (.var z))` | 4 |
| `aget x a i` | `assign x (.get a (.var i))` | 3 |
| `aset a i v` | `store a (.var i) (.var v)` | 3 |
| `seq/ite/while` | structural | ite/while test: `1 + condSize = 4` |

`embedOperand` (cell → `.var`, lit → `.lit`), `embedCond` (eq/lt
pointwise). No layout map at this step — IMP+ is still name-based; the
existing endorsed `compileProgram L` handles names → machine. IR binops
are already `Imp.Bop`, so arithmetic agrees definitionally
(`Bop.apply`).

State agreement: `agree (s : Ir.State) (σ : Env) : Prop` — on every
cell where `s` is defined, `σ` holds the same value (σ unconstrained
elsewhere; IR programs touching undefined cells are stuck, so the
simulation never looks there).

### 2. Bounded IR runs (`Refine/Codegen/BigStepB.lean`)

`Ir.BigStepB (B : ℕ) : Com → State → State → Cost → Prop` — the mirror
of `Ir.BigStep` with `< B` side conditions **only at value-creation
sites**: `const` (`n < B`), `binop` (`op.apply m n < B`). All other ops
move existing values. With the global state invariant
`StateBound B s` (every defined scalar and every array entry `< B`):

- `BigStepB.bigStep` — projection to the plain run;
- determinism transfer: a `BigStep` and a `BigStepB` run from the same
  state coincide (via `Ir.BigStep.unique`);
- `BigStepB.stateBound` — `StateBound` is preserved to the final state.

This is the same design as IMP+'s own `BigStepB` ("one derivation
carries correctness, cost and bound together"), pushed up to the IR.

### 3. Simulation + cost cashing (`Refine/Codegen/Sim.lean`)

Weights: `weight : String → ℕ` per the table (skip 1, const 2, copy 2,
each binop currency 4, aget 3, aset 3, ite 4, while 4);
`Cost.cash κ := (Currency.all.map (fun c => weight c * κ.toFun c)).sum`.

**Simulation theorem** (induction over the `Ir.BigStepB` derivation):

```
Ir.BigStepB B c s s' κ → StateBound B s → agree s σ →
  ∃ σ', Imp.BigStepB B (embed c) σ σ' k ∧ agree s' σ' ∧ k ≤ κ.cash
       ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out
```

Reads are `< B` from `StateBound`; writes are `< B` from the side
conditions; `while` guards match because `agree` fixes the tested
cells. IR `while_false` charges 1 `ir.while` vs IMP+ `1 + condSize` ≤ 4
— covered by weight 4. Constant-factor preservation: `cash` is linear
with max coefficient 4.

### 4. I/O harness (`Refine/Codegen/Harness.lean`) — pure IMP+ side

IR has no tapes, so `Solves` needs a marshalling prelude/epilogue,
proved once with the existing `Spec` kit:

- `readScalars (xs : List String)` — read one input number per named
  cell, `Spec`-lemma with cost `|xs|`, plus `forRange`-style
  `readArr a n` — read `n` numbers into array `a` (length-prefixed
  convention: first input value = length, when needed).
- `writeScalar x` / `writeArr a n` — epilogues writing the result
  cells/array to the output tape.
- Marshal descriptors kept concrete and few (scalar tuple in / scalar
  out; scalars+array in / scalar out; scalars+array in / array out) —
  P7's BFS shape is covered by the third.

Arrays must be *initialized* (IR aset requires existence and length):
the prelude also materializes declared arrays (`initEnv` already
provides per-input array lengths via `ext`; the harness pins the
correspondence).

### 5. The cashing theorem (`Refine/Codegen/Cash.lean`)

The end-to-end assembly, per marshal shape:

```
hnRefine Γ c Γ' d R m                        -- synthesized by sepref (P4)
m ≤ SPEC post cost                           -- abstract correctness chain
Ir.BigStepB B c s₀ _ _  (∃-form)             -- bounds pass, per program
Γ holds at s₀ with credits = cost            -- init lemma per marshal
  ⇒ Transfer.Solves L (prelude; embed c; epilogue) D f B K
  ⇒ ComputesInTime w (compileProgram L …) D f (L.const * K ·)
```

Route: `nofailT` from the SPEC bound → `hnRefine` gives the wp run →
wp adequacy (P3) → `Ir.BigStep` → determinism ties it to the
`BigStepB` witness → simulation (§3) → IMP+ `BigStepB`; final
`irSTATE (Γ' ∗ R ra d ∗ F ∗ GC)` pins the result cells to the abstract
result (`natAssn`/`arrayAssn` are equalities) → epilogue writes `f x`;
cost: run cost ≤ credits ≤ abstract `cost` (attained: `attainsSup`),
cashed at factor ≤ 4, plus harness costs.

**The bound is a genuine per-program obligation** — it cannot come from
`hnRefine` (P4's `natAssn` is deliberately unbounded, matching the
NREST abstract layer; the Isabelle source has no such obligation only
because its concrete values are machine words, bounded by their type).
Discharging `∃ BigStepB B` gets a small VCG: per-op rules under a
default `StateBound B` invariant (only `const`/`add`/`mul`/`shiftl`
sites yield real goals; `sub/div/and/or/xor/shiftr` preserve `< B` for
`B` a power of two — record the power-of-two convention), a while rule
with bound-invariant + variant, an `ir_bound_vcg` seed tactic. The
obligations are the same arithmetic the abstract invariants already
prove (`i + 1 ≤ n + 1 < B`). If P7 telemetry shows this pass dominates
the authored-line count, the recorded fallback is the source-faithful
retrofit: bounded value assertions (`wordAssn B`) with side conditions
in the arithmetic hnr rules, discharged during synthesis — a P4 thaw,
deliberately not taken now (P5/D-a: two-derivation route at the IR,
against `Reasoning.lean`'s advice for *users*, because here the second
derivation is VCG-generated, not hand-built).

## Wave plan

- **A1 (satellite, frozen @ f427b67):** Embed + BigStepB + StateBound +
  simulation + cash. Ir + Imp only, no Sepref dependency.
- **A2 (satellite, parallel):** Harness — pure IMP+ `Spec` work, no IR
  dependency.
- **B (main worktree, after A1+A2+P4-acceptance merge):** bounds VCG +
  cashing theorem + P5 acceptance: the P4 toys (array reverse,
  filter-count) land at `computesInTime` mechanically.

*Acceptance (from the plan):* P4's toy programs land at
`computesInTime` mechanically. Telemetry: lines of per-program bounds
annotations (feeds the P7 gate decision on the wordAssn fallback).

## Flag ranges

Supervisor P5/D-a–g reserved (D-a assigned above); wave A1 h–p; wave A2
q–z; wave B aa–.
