# Vertex cover, the Fibonacci rung — plan, rev 1

Date: 2026-07-27 night. Authorized by Jan: "improve the base of the
vertex cover algorithm as far as possible, stay truthful to the RAM
model, create a new vertex cover submission." That instruction opens
the concept-surface gate that `vc-ladder-plan.md` VC6 reserved for Jan:
a **new submission** whose statement beats the `2^k` bound.

Goal: a new submission (working name `vertex-cover-fibonacci/`, id from
`lax init`, expected Lax15) with one theorem concept — vertex cover
decided in `c * Nat.fib (k + 2) * (x.length + 1)` word-RAM steps — and
a complete proof on the existing Lax13/Lax11 kit. `fib (k+2)` grows as
`(φ²/√5)·φ^k ≈ 1.17·φ^k` with `φ ≈ 1.618`: the base drops from 2 to
the golden ratio, and the
bound is stated through mathlib's `Nat.fib`, no new surface definition.

The orchestrator (Fable) plans and reviews; fresh Opus sessions
implement. The mathematics below is fixed and was stress-tested on
paper; implement it, do not redesign it. If a proof obligation seems to
fail, suspect the formalization first; if the arithmetic itself is
genuinely wrong, write a precise counterexample to `NIGHTLOG.md` and
stop — that is signal, not failure.

## The statement (concept surface, fixed verbatim)

```lean
open Classical in
axiom exists_fibTime_program_vertexCover :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k w : ℕ),
      ComputesInTime w p
        {x | EncodesParamInstance x n G k ∧ c * (x.length + k + 1) ≤ 2 ^ w}
        (fun _ => if G.vertexCoverNum ≤ (k : ℕ∞) then [1] else [0])
        (fun x => c * Nat.fib (k + 2) * (x.length + 1))
```

where `EncodesParamInstance` is **imported from `Lax11.VertexCover`**
(same input format, same offsets — reuse, don't redefine) and
`ComputesInTime`/`Program` come from `Lax13.RamComputes` as in Lax11.
The admissibility condition `c * (x.length + k + 1) ≤ 2 ^ w` is the
same as Lax11's and for the same reasons (its Formalization notes
carry over: every value the run holds is a vertex number `< |x|`, a
counter `< |x|`, or a budget `≤ k`); the fitting condition is still
deliberately not coupled to the running time.

## Decision record

- **VF1 — dependencies.** Concepts require mathlib (archive pin),
  Lax13 concepts @ `2087642`, Lax11 concepts @ `0bbcfec` (both via
  `git = https://github.com/lax-archive/lax-submissions`, `subDir`,
  matching the current record triples — verified: GitHub main is
  0bbcfec). Proofs additionally require `../concepts`, Lax13Proofs @
  `2087642`, Lax11Proofs @ `0bbcfec`. Reuse imported material
  (`Lax11Proofs.VCSpec`'s `Ok`, bridge, `¬ Ok M 0`; the Reasoning kit;
  `computesInTime_of_run`); never copy what can be imported.
- **VF2 — surface minimal.** One theorem concept, statement above,
  `type: theorem`. No new definitions on the surface: `Nat.fib` is
  mathlib's, the encoding is Lax11's. Concept prose in the register of
  `Lax11/VertexCover.lean`, explicitly positioned as the improved rung
  over Lax11's `2^k` statement.
- **VF3 (rev 2, after S1's Repeats.lean finding) — the algorithm is
  fixed** (section below). Encodings may list a neighbour repeatedly,
  so *slot counts are not degrees*: the found-test is "some unmarked
  owner has two unmarked slots with **distinct** targets" (⇔ a vertex
  of residual degree ≥ 2, `exists_two_slots_iff`), and residual edges
  are counted one per block (`ResOwners`: owner unmarked, some
  unmarked slot with `u < tgt j`, counted once per owner) — a lower
  bound on `(ResEdges).card` in general and *equal* to it when no
  vertex has residual degree ≥ 2. The YES/NO leaf tests therefore
  fire only in the ¬found (matching) case. Branch on the found owner;
  trail-array undo with per-frame trail base; frames as four stacks
  `stkV, stkB, stkT, stkP` of extent `n + 1`, storing
  `(v, bud-at-push, trail base, phase)`. The S1 transport lemmas in
  `Lax15Proofs/Residual.lean` are the proved bridge; the original
  rev-1 scheme (raw slot counts, unconditional early YES) is
  **unsound on repeat-encodings** — see NIGHTLOG VCF session 2.
- **VF4 — the potential** (stress-tested; the constants are
  load-bearing, do not simplify): `f b := 4 * Nat.fib (b + 2) - 3`,
  so `f 0 = 1`, `f 1 = 5`, `f b = f (b-1) + f (b-2) + 3` for `b ≥ 2`,
  `f` monotone, `f ≥ 1`. Pending work of a configuration:

      P := (mode = descend ? f bud : 0)
         + Σ_{frames i, phase 0} (f (b_i − 2) + 2)    -- ℕ-sub: b_i=1 gives f 0 + 2
         + Σ_{frames i, phase 1} 1
         + (mode ≠ done ? 1 : 0)

  Transition drops (each ≥ 1, checked below). Initial value
  `P = f k + 1 ≤ 4 * fib (k + 2)`. Loop potential
  `Φ σ := U * (x.length + 1) * P (decode σ)` with `decode` total off
  the arrays/scalars, `U` a numeral ≥ body cost per `(x.length + 1)`.
- **VF5 — machine untouched, RAM-truthful.** No edits to Lax13/Lax11;
  no multiplication anywhere in the *program* (`fib` appears only in
  bounds, never computed); all costs through the existing `Run` rules
  and `while_pot`; no new axioms — final `lean_verify` must show only
  propext, Classical.choice, Quot.sound.
- **VF6 — pure-model discipline** (the CC/VC house rule): invariant
  `J`, potential `P`, and all graph theory on a pure config; Env-level
  lemmas only say "the arrays represent this config" and chain `Run`
  steps.
- **VF7 — rung B (1.4656^k, branch on degree ≥ 3 + path/cycle solver)
  is out of scope tonight** unless S7 completes with ≥ 3 h of night
  left; orchestrator's call only. It would be a *second* theorem
  concept with a named recurrence — never a retrofit of the fib
  statement.
- **VF8 — no `lax submit` tonight.** Everything staged for Jan's
  morning: draft complete, `lax build` green, abstract and notes
  written, achieved constant logged. Submission is Jan's call.

## The algorithm (fixed; sessions implement, don't redesign)

Read phase exactly as Lax11's `vcCom`: `n`, `m`, offsets, targets
(CSR), one more `read` for `k` into `bud` (tape length
`3 + n + 2m + 1`).

State: arrays `off`, `tgt` (graph); `mark` (0/1 per vertex, extent
`n`); `trail` (marked vertices in order, extent `n + 1`); stacks
`stkV`, `stkB`, `stkT`, `stkP` (extent `n + 1`). Scalars `top`, `tt`
(trail top), `bud`, `mode` (0 descend, 1 backtrack, 2 done), `ans`,
plus scan temporaries.

Outer loop `while mode < 2`:

- **descend**: one CSR pass `j ∈ [0, 2m)` with block owner `u`
  (inner `while off[u+1] ≤ j` advances `u` and resets the per-owner
  registers; amortized ≤ `n`). Per-owner registers (reset on owner
  advance): `seen` (0/1: an unmarked slot target has been seen),
  `t1` (that first target), `cnted` (0/1: this owner already counted
  into `ro`). The pass computes, for unmarked owners `u` on unmarked
  slot targets `w = tgt j`:
  `ro` — number of owners with some such `w` satisfying `u < w`
  (set `cnted`, count once per owner); and the found-test — if
  `seen = 1` and `w ≠ t1`: `found := 1`, record `v := u` (first such
  owner; keep scanning — `ro` needs the full pass). Then:
  - `found`, `bud = 0`: `mode := 1` (a residual edge exists,
    `¬ Ok M 0`).
  - `found`, `bud ≥ 1`: **push** (below).
  - `¬found` (every unmarked vertex has residual degree ≤ 1, so
    `ro = (ResEdges).card` exactly): if `ro ≤ bud`: `ans := 1;
    mode := 2` (YES leaf); else `mode := 1` (matching lower bound).
  - **push**: `stkV[top] := v; stkB[top] := bud; stkT[top] := tt;
    stkP[top] := 0; top := top + 1; mark[v] := 1; trail[tt] := v;
    tt := tt + 1; bud := bud − 1` (stay in descend).
- **backtrack**: if `top = 0`: `ans := 0; mode := 2`. Else with the
  top frame `(v, b, tb, p)`:
  - `p = 0` (**flip**): unmark the trail above `tb` (here just `v`):
    `mark[trail[tb]] := 0`; `tt := tb`; `bud := b`. Then scan `v`'s
    row `j ∈ [off v, off (v+1))`: for each unmarked `w = tgt j`, mark
    it, `trail[tt] := w; tt := tt + 1` (this is `N(v)` residual over
    the marks below the frame, size `d ≥ 2`). Set `stkP[top−1] := 1`.
    If `tt − tb ≤ bud`: `bud := bud − (tt − tb); mode := 0`.
    Else: leave `mode = 1` (infeasible second branch; the next
    iteration pops it).
  - `p = 1` (**pop**): `while tt > tb`: `tt := tt − 1;
    mark[trail[tt]] := 0`. Then `bud := b; top := top − 1`
    (stay in backtrack).

Then `write ans`. Body cost per outer iteration ≤ `B * (x.length+1)`
for a numeral `B`: the descend scan is ≤ `2m + n` amortized steps plus
constants; flip is ≤ `deg v + const ≤ 2m + const`; pop's unmark loop
is ≤ `n` steps. Loose constants everywhere; `.mono` early.

## The mathematics (fixed)

Pure side, no `Env` anywhere. Reuse from `Lax11Proofs.VCSpec`: `Ok`,
the ℕ∞ bridge `Ok ∅ k ↔ G.vertexCoverNum ≤ k`, `¬ Ok M 0` under an
uncovered edge. New definitions over `G : SimpleGraph (Fin n)`,
`M : Finset (Fin n)`:

- `ResNbhd M v : Finset (Fin n)` — unmarked neighbors of `v`;
  `resDeg M v := (ResNbhd M v).card`.
- `ResEdges M : Finset (Sym2 (Fin n))` — edges with both endpoints
  unmarked (filter of `G.edgeFinset`).

The three new graph lemmas:

1. **Early YES**: `(ResEdges M).card ≤ b → Ok M b`. Witness cover
  `M ∪ (ResEdges M).image (pick an endpoint)` — one endpoint per
  residual edge (via `Sym2` choice, e.g. `Quot.out`; membership by
  `Sym2.out_fst_mem` or the pin's equivalent); every non-residual
  edge already meets `M`; the image has card ≤ `re ≤ b`.
2. **Matching lower bound**: if every unmarked vertex has
  `resDeg M · ≤ 1` and `(ResEdges M).card > b`, then `¬ Ok M b`.
  Any cover `S ⊇ M` meets each residual edge in `S \ M`; the map
  edge ↦ covering endpoint is injective because two residual edges
  sharing an endpoint give it residual degree ≥ 2.
3. **Neighborhood branch**: for `v ∉ M` with `d := resDeg M v`,
  `2 ≤ d`, `1 ≤ b`:
  `Ok M b ↔ Ok (insert v M) (b−1) ∨ (d ≤ b ∧ Ok (M ∪ ResNbhd M v) (b−d))`.
  (→: a cover missing `v` contains all of `ResNbhd M v`, which is
  disjoint from `M`, giving `d ≤ b`; ←: both disjuncts are covers
  within budget. `2 ≤ d` is not needed for the equivalence — keep the
  hypothesis only if it falls out naturally; the program guarantees
  it.)

(Proved in `Lax15Proofs/Residual.lean`, namespace `Lax15Proofs.VC`:
lemma 1 = `ok_of_card_resEdges_le`, lemma 2 =
`not_ok_of_lt_card_resEdges`, lemma 3 = `ok_branch_resNbhd`, plus the
CSR transport family `card_res*` / `exists_two_slots_iff` /
`thinBlocks_iff` and the helper `ok_of_ok_union`.)

**Pure config**: `frames : List Frame` with
`Frame := (v : Fin n) × (b : ℕ) × (phase : Bool) × (S : List (Fin n))`
(S = the vertices this frame marked, in trail order), plus `mode`,
`bud`, `ans`. Derived: `P_i := ⋃_{j<i} S_j` (as a Finset),
`M := P_{top}` ∪ nothing — i.e. the union of all `S_i`; the trail is
`(frames.map S).flatten`.

**Frame health** (part of the invariant `J`):
- the `S_i` are pairwise disjoint, nonempty, and `mark` (machine side)
  is the indicator of their union;
- phase-0 frame: `S_i = [v_i]`, `v_i ∉ P_i`, `2 ≤ resDeg P_i v_i`;
- phase-1 frame: `S_i.toFinset = ResNbhd P_i v_i` (nodup, so
  `|S_i| = resDeg P_i v_i ≥ 2`);
- `b_i = k − Σ_{j<i} |S_j|`, and in descend mode
  `bud = b_top − |S_top|` (no frames: `bud = k`);
- consequences the machine needs: `top ≤ n` and `tt ≤ n` (disjoint
  nonempty subsets of `Fin n`), so all stack/trail writes are in
  bounds at extent `n + 1`.

**The invariant** (with
`A := ⋁_{phase-0 frames i} (resDeg P_i v_i ≤ b_i ∧
Ok (P_i ∪ ResNbhd P_i v_i) (b_i − resDeg P_i v_i))`):

    J(C) :=  mode = descend  → (Ok ∅ k ↔ Ok M bud ∨ A)
           ∧ mode = backtrack → (Ok ∅ k ↔ A)
           ∧ mode = done     → (ans = 1 ↔ Ok ∅ k)
           ∧ frame health

**The transitions** (each preserves `J` and drops `P` by ≥ 1):

- T1 matching YES (descend, ¬found, `ro ≤ bud`): `ro = (ResEdges).card`
  in the ¬found case, so lemma 1 gives `Ok M bud`; to done, `ans = 1`.
  Drop `f bud + 1 − 1 ≥ 1`.
- T2 matching NO (descend, ¬found, `ro > bud`): lemma 2 (with
  `resDeg ≤ 1` from ¬found) gives `¬ Ok M bud`; to backtrack.
  Drop `f bud ≥ 1`.
- T3 budget NO (descend, found, `bud = 0`): `¬ Ok M 0` (VCSpec's
  `not_ok_zero`; found gives a residual edge); to backtrack.
  Drop `f 0 = 1`.
- T4 push (descend, found `v`, `bud ≥ 1`): lemma 3 rewrites
  `Ok M bud`; new frame's stored alternative is exactly the new
  `A`-term. Drop `f b − f (b−1) − (f (b−2) + 2) = 1` for `b ≥ 2`;
  at `b = 1` (ℕ-sub) `f 1 − f 0 − (f 0 + 2) = 5 − 4 = 1`.
- T5 exhausted (backtrack, `top = 0`): `A = False`, so `¬ Ok ∅ k`,
  `ans = 0`, done. Drop: the mode unit.
- T6 feasible flip (`d ≤ b_i`, forces `b_i ≥ 2`): the stored `A`-term
  becomes the active branch — `M' = P_i ∪ ResNbhd P_i v_i` and
  `bud' = b_i − d` on the nose. Drop
  `(f (b_i − 2) + 2) − f (b_i − d) − 1 ≥ 1` since `d ≥ 2` and `f`
  monotone.
- T7 infeasible flip (`d > b_i`): the stored `A`-term is `False` and
  leaves `A`; frame flips to phase 1 with `S = N`, mode stays
  backtrack. Drop `(f (b_i − 2) + 2) − 1 ≥ 2`.
- T8 pop (phase-1 top frame): removes a frame contributing nothing to
  `A`; marks shrink back to `P_i`. Drop: its phase-1 unit.

At `done`, the imported bridge turns `ans` into the concept's `if`.
Initial config: no frames, descend, `bud = k`, so `J` is trivial and
`P = f k + 1 = 4 * fib (k+2) − 2`.

## Milestones (relay-sized; one fresh Opus session each unless split)

- **S0 — scaffold.** `lax init vertex-cover-fibonacci` (offline
  fallback `--id Lax15`), manifest (title, authors as Lax11, bib:
  DowneyFellows1999 + CyganEtAl2015), LICENSE, abstract.md draft,
  lakefile pins per VF1, `lean-toolchain` v4.30.0, the concept file
  (statement verbatim + prose + Formalization notes), root modules;
  `lake build` green in `concepts/` and `proofs/` (proofs root may
  import a stub module; the dep build of Lax13Proofs+Lax11Proofs is
  the slow one-time cost — `lake exe cache get` first). Commit.
- **S1 — pure model, graph side** (`…Spec.lean` or `…Graph.lean`):
  residual defs, lemmas 1–3, CSR transport statements needed later
  (residual degree / residual edge count read off the scan through
  `EncodesGraph.adj_iff`, in the style of `CCGraph`/`VCSpec`'s
  cover-on-exhaustion). Green, no sorry, committed.
- **S2 — pure model, config side** (`…Config.lean`): `Frame`, config,
  `M`/`P_i`/trail, `J`, frame health, the eight transition lemmas
  (J-preservation + P-drop each), the `f` arithmetic
  (`f_succ_succ : f (b+2) = f (b+1) + f b + 3`, `f_pos`, `f_mono`,
  `pot_init : P C₀ = f k + 1`, `pot_init_le : … ≤ 4 * fib (k+2)`).
  Likely the riskiest pure session; split graph/config further if
  needed.
- **S3 — the program + smoke.** `vcfCom : Com`, `vcfCom_ok`, `#eval`
  the compiled machine program before any Run proofs on: triangle
  (k=1 no, k=2 yes), P₄ (k=1 no, k=2 yes), star K₁,₃ (k=1 yes — the
  d=3 branch), C₄ (k=1 no, k=2 yes), C₅ (k=2 no, k=3 yes — flips and
  pops), 2K₂ (k=1 no, k=2 yes — the matching leaf), K₄ (k=2 no, k=3
  yes), edgeless (k=0 yes), malformed non-crash, **and the
  repeat-encoding regressions**: `Repeats.lean`'s one-edge word
  `[2,2,0,2,4,1,1,0,0]` (k=0 no, k=1 yes) and a doubled-slots
  matching family instance (must stay linear-ish in steps, not 2^k).
  Log step counts; compare a couple against Lax11's `vcCom` if cheap.
- **S4 — inner-loop Run lemmas.** The descend scan (one `while_pot`
  with potential `a·(2m−j) + b·(n−u)`, conclusion: represents same
  config, `ro` = the `ResOwners` count and found-flag/witness `v` per
  VF3 rev 2, tied to the pure side by S1's transport lemmas
  (`exists_two_slots_iff`, `thinBlocks_iff`, `card_res*` in
  `Residual.lean`) — *an* arbitrary witness, first-ness never enters
  the invariant); the flip row scan (`while_count` or
  `while_pot` over `[off v, off (v+1))`, conclusion: marks become
  `P_i ∪ ResNbhd P_i v_i`, `tt − tb = resDeg P_i v_i`); the pop
  unmark loop (`while_pot` on `tt − tb`).
- **S5 — the outer body.** `outerBody_run`: case split on
  mode/branch, each case ≤ numeral · `(x.length+1)`, preserves
  "arrays represent `C` ∧ `J C`", drops `P` by ≥ 1 (T1–T8). The hard
  milestone; two sessions before escalating (split case-group A:
  descend cases / case-group B: backtrack cases if needed).
- **S6 — the loop + assembly.** `Run.while_pot` with
  `Φ = U·(x.length+1)·P∘decode`; read phase (Lax11 `vcCom` pattern),
  `write ans`, `computesInTime_of_run`, the endgame theorem with
  conclusion frontmatter (`conclusion:
  Lax15.VertexCover….exists_fibTime_program_vertexCover` — adjust to
  the actual id), explicit numeral `c`, `example : … = …ᶜᵒⁿᶜᵉᵖᵗ := rfl`
  check, `lake build` green, `lean_verify`: three background axioms
  only. Commit.
- **S7 — wrap-up (Jan-visible).** abstract.md final, notes.md,
  `lax build` (build-output refresh, not staged), achieved constant
  in the log, NIGHTLOG summary for Jan. **No submit** (VF8).

## Watch items

(All of `vc-ladder-plan.md`'s watch items apply: stale LSP after
external builds, no `simp` on pattern-matching concept defs, `omega`
vs structure fields, the `EncodesInstance`-destructuring idiom, keep
`Φ`/`J` pure.) New ones:

- The nonlinear-arithmetic recipe from the 2^k campaign (NIGHTLOG, VC
  sessions 3–4): pre-derive `Nat.mul_le_mul`, rewrite `potN` to `pot`
  at both ends, `generalize` the `fib` product to an atom before
  `omega`. Expect the same shape with `fib (k+2)` in place of `2^k`.
- `Nat.fib` grows slower than `2^b` — nothing in the kit assumes
  power-of-two potentials; if some lemma does, that is a plan bug:
  report, don't patch around.
- Frames are variable-length only through the trail; the stacks
  themselves are fixed-stride. In-bounds obligations for `trail`,
  `stk*` writes come from frame health (`top ≤ n`, `tt ≤ n`) — keep
  those in `J`, not derived ad hoc.
- `lax init` needs the server; if it fails use `--id Lax15` and log
  that the id is provisional (Jan resolves in the morning).
- Lake deps: pin revs exactly as VF1; `lake update` is forbidden; if
  the git fetch of the Lax deps fails, stop and report — do not
  vendor copies.
