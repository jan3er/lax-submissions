# ND-MC integration design — Σ-shape cost threading, the engine-swap map, and two campaign-level findings

Rev 1, 2026-07-30. Author: Integration-A (Fable). Status: **DESIGN
COMPLETE, SURGERY STOPPED AT THE BRIEF'S CHECKPOINT** — the paper
recurrence check (§2) shows the revision is *not* hypothesis-only, which
is the brief's named STOP condition. Two campaign-level findings (§3)
need owner decisions (§4) before any execution wave runs. What could be
landed without prejudice is landed and green (§9): the Σ-shaped loop
rule, the compiled star probe, and the compiled `n^ℓ` interface floor.

## Table of contents

- §1 What the wave was asked, and what stopped it
- §2 The paper recurrence check
  - §2.1 The recurrence the current interface induces (compiled floor)
  - §2.2 The recurrence the current *program* forces (finding F1)
  - §2.3 The mass bound at R = 0 (finding F2)
  - §2.4 The target recurrence, and that the P3 solver absorbs it
  - §2.5 Verdict
- §3 The two findings, precisely
- §4 Decision requests (D-1, D-2)
- §5 The revised cost interface — exact old → new (designed)
- §6 The R1 driver-program delta (designed)
- §7 The engine-swap map
- §8 Integration-B briefs B1–B7
- §9 Landed vs designed; falsification record; ledger

---

## §1 What the wave was asked, and what stopped it

The brief: revise the driver stack's cost interface so the tower's
touched-only per-pass costs (`ClusterSynth.clusterLoad0_le` 12n+15m+19,
`ExpandSynth.expPass_expandVal` 47n+30ns+4, `CoverSynth` carrier-free
emit, `ElimSynth6.engineK5` 333n+168ns+45, …) flow through
`levelImplements`/`driver_correct`/`driverRoot_decides_sentence` to the
C0 almost-linear bound — with a mandatory end-to-end paper check
*before* surgery, and a STOP if a floor survives that the mass bound
cannot absorb, or if the revision needs a structurally different driver
program rather than re-threaded hypotheses.

Both STOP conditions fire, independently:

- **F1**: `RamDriver.driverAux`'s own text has an `n^ℓ` run-cost floor
  — the centre loop runs `n` turns per call and every turn runs the
  nested driver unconditionally. No hypothesis revision changes what a
  program's runs cost. The repair is a (bounded, meaning-preserving,
  but *structural*) change to the loop skeleton: §6.
- **F2**: at `R = 0` — the only `R` at which the frozen correctness
  theorem exists — the cover-degree mass bound the Σ-recurrence stands
  on is mathematically unavailable: `CoverDegree.exists_cover_degree`
  requires `3·t ≤ R` and `2·cap ≤ 2^t`, and `cap = rhoMinus 0 q_top =
  9^((q_top+1)·q_top) ≥ 9` for every sentence of rank ≥ 1. The cost
  headline needs the `R > 0` ordering phase; correctness today exists
  only at `R = 0`. The intersection is empty until the two `tgt`
  couplings are closed (§3, F2).

Per the brief's §6 ("if the revision needs a structurally different
driver program (not just hypotheses), STOP at the design doc +
finding"), the `levelImplements`/root re-threading was **not**
executed: its final shape depends on D-1/D-2 below, and landing it
against the current program would be certain rework. Everything that is
decision-independent was landed green (§9).

## §2 The paper recurrence check

### §2.1 The recurrence the current interface induces

The frozen side conditions (verbatim, `RamDriverRoot.lean:277–280`):

```
hKs : ∀ j < ℓ, turnCost n ns cap mb q_top j φ (Ksc j) (Kl (j+1)) ≤ Ks j
hKl : ∀ j < ℓ, orderPhaseCost n ns W + (coverPhaseCost n ns + ((Ks j + 8) * n + 6)) ≤ Kl j
```

`turnCost` carries `Kin = Kl (j+1)` **additively** (its definition,
`RamDriverRoot.lean:124`), so `Ks j ≥ Kl (j+1)`, and `hKl` pays `n`
turns at the uniform budget, so `Kl j ≥ n · Kl (j+1)`. Downward
induction: `Kl 0 ≥ n^ℓ · Kl ℓ`. This is now **compiled**:
`Refine.CostShapeProbe.uniform_interface_floor_zero` proves `n ^ ℓ *
Kl ℓ ≤ Kl 0` from exactly those two hypotheses, for *every*
instantiation of the free parameters. The `n^ℓ` is in the hypothesis
shape, not in any engine cost — no tower export can flow through it.
(`CostRecurrence.lean`'s own closed form concedes the same:
`Kl 0 = Σ a j·n^j + Cbase·n^ℓ`.)

The loss is already fatal at one level: the star instance — one cluster
on `n−1` vertices, `n−1` singletons — has Σ-mass `2(n−1)` but uniform
cost `n(n−1)` (`CostShapeProbe.star_mass_linear` /
`star_uniform_quadratic` / `star_uniform_gap`, plus `#guard`s at
`n = 8, 32`). The negative control `sum_le_uniform` confirms the
Σ reading is a strict refinement — re-threading can never *lose* a
bound the uniform interface could state.

### §2.2 The recurrence the current program forces (F1)

Independent of every hypothesis: `driverAux (f+1) j` is

```
orderCom ; coverPhase ; cur := 0 ;
while cur < n do (clusterCom j (driverAux f (j+1)) ; cur := cur + 1)
```

(`RamDriver.lean:1657–1667`), and `clusterCom` is a plain `seq` whose
fourth component is `inner` — **unconditional** (`RamDriver.lean:1610`).
The guard reads the carrier scalar `"n"`; the loop body increments
`cur` by one; so every run of a fuel-`(f+1)` call executes the
fuel-`f` call exactly `n` times. By induction, every run of
`driverAt … 0` executes `baseCom` exactly `n^ℓ` times, each costing
≥ 1 step. Hence **every** `K` for which
`Spec B P (driverAt q_top cap mb R ℓ W φ 0) Q K` holds with a
satisfiable `P` (carrier `n`) obeys `K ≥ n^ℓ`. For `ℓ ≥ 2` — and
`ℓ = N (2s+2) ≥ 2` for every nontrivial class — `n^ℓ ≥ n²`, while C0
demands `c·(|x|+1)^{1+ε}` for **every** ε > 0. The current program text
cannot witness C0; the revision cannot be hypothesis-only. (Paper
proof; the compiled interface floor of §2.1 is its interface shadow.
Compiling the program floor itself needs a `BigStep` while-unrolling
induction — recorded as optional B2 collateral, not load-bearing.)

Beyond the skeleton, the per-turn Θ(n) floors the brief names (2F/D-a
carrier fills, 2G/N-3 expansion chains, the per-atom `copyCom`s of the
scatter phase, `readbackCom`'s carrier scan, `enumBatch`) and the
per-call Θ(n + ns) floors (order/cover engine carrier passes, at *every*
nested call) are each individually fatal by the same counting:
Θ(n)/turn × n turns = n² at depth 0 alone; Θ(n)/call × up-to-n calls at
depth 1 = n². **Every** carrier-width pass on the recursion's inside
must become active-set-driven. The mass bound absorbs active-set costs
(§2.4); it absorbs no carrier-width cost.

### §2.3 The mass bound at R = 0 (F2)

The Σ-recurrence needs, at every depth: `Σ_c |X_c| ≤ D · m` with
`D = ⌈c · n^δ⌉` subpolynomial. The only such fact in the repo is the
chain

```
exists_cover_degree  (CoverDegree.lean:367)   — degree ⌈c·m^δ⌉ of the wreach-fibre cover
isNeighborhoodCover_of_out (RamCover.lean:719) — the pass's cover IS that cover, given the wreach bound
sum_ncard_le_of_isNeighborhoodCover (CoverDegree.lean:525) — degree d ⇒ mass ≤ N·d
```

`exists_cover_degree` hypotheses: an `R`-round greedy augmentation
chain, `3·t ≤ R`, `2·rc ≤ 2^t`, in/back-degree minimality from the two
eliminations. At `R = 0`: `t = 0`, so `2·rc ≤ 1`, i.e. **radius-0
covers only**. The driver's covers are at radius `cap = rhoMinus 0
q_top = 9^((q_top+1)·q_top)` (`DistFO.lean:145`), so the C0 path needs

```
R ≥ R* := 3 · t*,   t* = ⌈log₂ (2 · cap)⌉   (constant in n, ~3·(q_top²+q_top)·log₂9 + 3)
```

At `R = R*` the augmentation fold is live: the counting sorts, the
`RamAugment` rounds (whose walk `RamDriverAugment.implements` **is**
already proven — the capital exists), and the ordering phase's two open
`tgt` couplings, which are exactly why `orderImplements₀` is stated at
`R = 0` (`RamDriverCompose`, its docstring). The P3 satellite already
settled the couplings' mathematics (`TgtCoupling.lean`: (a) refuted
ns-reuse via K₁,₄ — the array must widen; (b) `chainWidth` gives the
single width `W` dominating every round). What is missing is the
machine wave: `tgt` widened in `RamBfs`/`RamCover`/`RamScatter`/
`RamBfsPaths`, previously deprioritized as "buys the cover's degree
bound and nothing else" — that degree bound is now known to be
load-bearing for C0.

The 2E "R = 0 scope ruling" therefore holds for the **correctness**
half only. On the cost half, at R = 0, the best available mass bound is
the trivial `mm ≤ n·n` (`CoverHeldAt`), and the recurrence coefficient
degenerates to `n`: no almost-linear bound exists at R = 0, with any
interface and any program.

### §2.4 The target recurrence, and that the P3 solver absorbs it

With the §5 interface and the §6 program (R1), the level at depth `j`
on an arena of `m` alive vertices induces, writing `bs c` for block
sizes and `cnum ≤ m` for the compacted turn count:

```
Kl j m ≥ Ko j m + Kc j m + 6 + Σ_{c < cnum} (tb j (bs c) + 8) + Σ_{c < cnum} Kl (j+1) (sz c)
   with  sz c ≤ bs c,   Σ_c bs c ≤ D · m,   cnum ≤ m
Kl ℓ m ≥ Cb · (m + 1)                        (block-driven base pass)
```

where `tb j s ≤ α·s + β·(mb + edge-mass of the block)` (touched-only
leaves; edge terms charge `Σ_{v∈X_c}(1 + deg v)`, and per depth
`Σ_c Σ_{v∈X_c} deg v ≤ D · ns` by the same double counting —
`sum_ncard_le_mul`). Linear ansatz `Kl j m = u j · (m + 1)`:
using `Σ (bs c + 1) ≤ (D+1)·m` and monotonicity,

```
u j  =  a j + (D + 1) · u (j+1),      a j := (Ko-coeff + Kc-coeff + α + β' + 8)
```

— **exactly `CostRecurrence.solve` with coefficient `b ≡ D + 1` instead
of `n`**. The P3 solver is parametric in `b`, as promised by the plan
("P3's CostRecurrence solver is parametric and absorbs either shape"):
`solve_const_le` gives `u 0 ≤ (ℓ·A + Cb) · (D+1)^ℓ`. Compiled bridge:
`CostShapeProbe.sigma_coefficients_geometric` (it *is*
`solve_const_le` at `D`), plus the `#guard` contrast `b ≡ 100` vs
`b ≡ 2` on three levels (1101010 vs 78).

P4 then picks, for the requested real ε > 0, `δ := ε/ℓ` and gets from
`exists_cover_degree` a `D = ⌈c·n^δ⌉`, so

```
Kl 0 n ≤ (ℓ·A + Cb) · (⌈c·n^{ε/ℓ}⌉ + 1)^ℓ · (n + 1)  =  O((n + ns + 1)^{1+ε})
```

and `|x| = Θ(n + ns)` closes into the C0 form
`T x ≤ c·(|x|+1)^{1+ε}` — the real-exponent massage is the same one
`exists_cover_degree`'s proof already performs (its `X^(2·16^R) = m^δ`
step). Remaining P4 arithmetic: `(⌈c·n^{ε/ℓ}⌉+1)^ℓ ≤ c'·n^ε + c''`,
which is `Nat.ceil`-vs-`rpow` massage of the kind `CoverDegree` already
contains.

### §2.5 Verdict

| configuration | bound derivable |
|---|---|
| current interface, current program, any R | `Kl 0 ≥ n^ℓ` — **no** (compiled) |
| Σ/size interface (§5), current program | `≥ n^ℓ` still — **no** (F1, program floor) |
| Σ/size interface + R1 program (§6), R = 0 | mass bound only `n²` ⇒ coefficient `n` — **no** (F2) |
| Σ/size interface + R1 program, R = R* | `u j = a j + (D+1)·u(j+1)`, `D = ⌈c·n^{ε/ℓ}⌉` ⇒ **`O((|x|+1)^{1+ε})` — yes** |

`n^{1+ε}` does **not** come out at R = 0. That is the checked,
campaign-level answer the brief asked for before surgery.

## §3 The two findings, precisely

**F1 — the driver skeleton is `Ω(n^ℓ)`; the Σ revision is not
hypothesis-only.** The plan's Σ-shape ruling scheduled "a proofs-side
hypothesis revision of `levelImplements`/`driver_correct`/
`driverRoot_decides_sentence`". The check shows hypothesis revision is
necessary but not sufficient: the program's centre loop runs `n` turns
at every depth (guard on the carrier scalar) and recurses
unconditionally in each, so run cost — hence any `Spec`'s `K` — is
`≥ n^ℓ` (§2.2). The interface half of the floor is compiled
(`uniform_interface_floor`). The repair (§6) changes `driverAux`'s
text: compacted centre iteration + conditional/blocked turns +
active-set passes. That changes the subject term of the frozen theorem
statements (as P1's `bfsQCom` swap already did, at smaller scale) and
re-derives the level loop's partition argument — beyond this wave's
delegated authority over hypothesis shapes.

**F2 — the C0 cost path is not R = 0; the `tgt`-widening wave is
load-bearing.** §2.3. Consequences: (i) the 2E ruling's "dead code"
scope is correctness-only; the augment rounds, the counting sorts and
`AugmentSynth`'s tower capital are on the C0 cost path after all;
(ii) `orderImplements` must be discharged at `R = R*`, which requires
closing the two `tgt` couplings whose mathematics P3 settled
(`TgtCoupling.chainWidth`) and whose machine half is the four-file
`tgt` widening wave; (iii) `driverRoot_decides_sentence` must be
re-stated at parameter `R` (its proof skeleton is R-generic except the
one `orderImplements₀` slot — the correctness *walks* for `R > 0`
augmentation are already proven capital, `RamDriverAugment.implements`).

## §4 Decision requests

**D-1 (supervisor; touches frozen-surface subject terms): approve the
R1 skeleton revision** (§6) — compacted centre loop + active-set
passes — with the obligation Props' shapes preserved per §5 and the
`levelImplements` induction re-threaded, its partition argument
re-derived over the compacted centre list. Alternative: fallback
checkpoint with Jan (the plan's hard checkpoint clause; the old-style
cost wave inherits the same F1 floor, so falling back does not avoid
this decision — the old plan's own "the recursion as stated is n^ℓ"
item is this finding).

**D-2 (supervisor/Jan): the R-plan for C0.**
- **(a) recommended**: complete the `R > 0` ordering phase — the
  `tgt`-widening wave (B5) + `W ≥ chainWidth` threading + counting
  sorts; discharge C0 at `R = R*(q_top)`. All mathematics exists
  (`TgtCoupling`, `CoverDegree`, `AugmentedDensity`); the walks exist
  (`RamDriverAugment.implements`); this is machine-plumbing, not new
  proof content.
- (b) prove a wreach-degree bound for the un-augmented greedy ordering
  at radius `2·cap` — **not recommended**: no such theorem exists in
  the repo or in the source literature's toolkit; fraternal
  augmentation is the known mechanism.
- (c) weaken C0 — out of scope by charter (concept surface frozen).

## §5 The revised cost interface — exact old → new (designed, not landed)

Size vocabulary (new, `RamDriver.lean` or `Refine/`):

```lean
def arenaSize (n : ℕ) (M : ℕ → ℕ) : ℕ := (markSet n M).ncard     -- alive count
def blockSize (Xoff : ℕ → ℕ) (c : ℕ) : ℕ := Xoff (c+1) - Xoff c  -- cover block c
```

Per declaration (statement deltas only; **no postcondition's semantic
content moves**):

1. **`LevelImplements`** (`RamDriver.lean:2477`) — *Prop unchanged*
   (its `K` stays a bare `ℕ`). The threading changes: everywhere a
   caller instantiates it, the cost becomes `Kl j (arenaSize n M)`
   with `Kl : ℕ → ℕ → ℕ`, plus a global side hypothesis
   `hKmono : ∀ j, Monotone (Kl j)` (the closed-form solutions are
   monotone; `solve_mono` covers the witness).

2. **`ClusterStepImplements`** (`RamDriver.lean:2356`) and
   **`ClusterFrames`** (`RamDriverCluster.lean:990`) — new parameter
   `(k : ℕ)`, the turn index; precondition clause
   `σ.vars (curName j) < n` **becomes** `σ.vars (curName j) = k` (with
   `k < cnum` a hypothesis); the inner-driver antecedent's cost
   `Kin : ℕ` **becomes** `Kin : ℕ → ℕ` applied at
   `arenaSize n M'` (the antecedent already quantifies `M'`, so the
   cost may read it); conclusion cost instantiated per turn:
   `Kt j (blockSize Xoff k)`.

3. **`DescendStep`** (`RamDriverCluster.lean:589`) — postcondition
   gains one clause:
   `arenaSize n Alv' ≤ blockSize Xoff (σ.vars (curName j))`.
   Derivation for the discharger: `BatchData` gives
   `markSet n Alv' = X ∩ W ⊆ X`, and `CoverOut.block` at
   `c := curName`-value exhibits `X` as the image of the block's
   positions, so `X.ncard ≤ blockSize Xoff c`. (New sub-proof, walk
   local to `RamDriverDescend.descendStep`; no program change needed
   for this clause.)

4. **`OrderImplements`** (`RamDriver.lean:2243`) — postcondition
   existential gains a *parametric* conjunct:
   `∃ π ord, … ∧ RamCover.OrdersBy n π ord ∧ P π ord` with
   `P : Equiv.Perm (Fin n) → (ℕ → ℕ) → Prop` a new Prop parameter.
   Today's dischargers instantiate `P := fun _ _ => True` (zero new
   proof). At B5, `P := fun π _ => ∀ v, (wreach (masked G M) π
   (2·cap) v).ncard ≤ D` — the exact hypothesis of
   `isNeighborhoodCover_of_out`, produced by `exists_cover_degree`'s
   conclusion from the chain the R\*-phase builds.

5. **Mass at the level** — new math hypothesis of `levelImplements`
   (threaded from the root like `hQ`, discharged in P4):
   ```
   hmass : ∀ j < ℓ, ∀ M π ord Xoff Xmem asg mm, P π ord →
     RamCover.CoverOut (masked G M)?… → mm ≤ Kmass j * (arenaSize n M + 1)
   ```
   via `isNeighborhoodCover_of_out` + `sum_ncard_le_mul`, **plus** the
   block-injectivity fact `mm = Σ_c (cluster c).ncard` (B6: `CoverOut`
   blocks must enumerate without repetition — the emission scan writes
   each reached vertex once, and `CoverSynth`'s `ReachedList`
   injectivity conjunct is exactly this; strengthen `CoverOut` or
   derive at the pass).

6. **`levelImplements`** (`RamDriverCluster.lean:1055`) — the loop is
   composed by **`Refine.SigmaLoop.forRangeZeroSum`** (landed, green)
   instead of `Spec.forRangeZero`; `hstep`/`hframe` quantify the turn
   index; the cost side condition **becomes**

   ```
   hK : ∀ j < ℓ, ∀ m ≤ n, ∀ t ≤ m, ∀ bs : ℕ → ℕ,
     (Σ_{c<t} bs c ≤ Kmass j * (m + 1)) →
     Ko j m + (Kc j m + ((Σ_{c<t} (Kt j (bs c) + 8)) + 6)) ≤ Kl j m
   ```

   replacing `hK : ∀ j < ℓ, Ko j + (Kc j + ((Ks j + 8) * n + 6)) ≤ Kl j`.

7. **`turnCost`** (`RamDriverRoot.lean:124`) — becomes size-indexed,
   `turnCostΣ n ns cap mb q_top j φ Ksc s Kin`, its `Kin` slot filled
   with `Kl (j+1) s'`, `s' ≤ s` by §5.3 + `hKmono`; `hKs` becomes
   `∀ j < ℓ, ∀ s, turnCostΣ … s (Kl (j+1) s) ≤ Kt j s`.

8. **`driverRoot_decides_sentence`** — same statement, cost
   `Kdec + (Kl 0 (arenaSize n M₀) + Ksent)` where the root mask is
   all-alive (`arenaSize = n`); `hbnd/hcostI/hKsc/hatoms/hKsent`
   unchanged; `hKs/hKl` in the §5.6–5.7 forms; new `hKmono`, `hmass`,
   and (under D-2a) the `R = R*` order slot.

9. **`CostRecurrence`** — extension `exists_driverCostsSigma`: from
   `ℓ, D, Cb`, per-level coefficients `a`, the *witnesses*
   `Kl j m := solve a (fun _ => D+1) Cb ℓ j * (m + 1)`,
   `Kt j s := tb j s + Kl (j+1) s`, satisfying §5.6–5.7 verbatim, with
   `Kl 0` in closed form and least. Proof: `solve_const`,
   `solve_le_of_le`, `Finset.sum_le_sum` — same style as
   `exists_driverCosts`, which stays (the uniform corollary).

Compatibility: instantiating `bs` constantly and `Kt` size-blind
recovers today's interface exactly (`SigmaLoop.sum_const_eq_uniform`,
compiled), so the re-threading is a refinement; every current
discharger discharges the revised Props after the mechanical
re-parameterization, **except** the one new §5.3 clause and the §6
program deltas.

## §6 The R1 driver-program delta (designed; blocked on D-1)

R1.1 **Compacted centres.** The cover phase additionally materializes
`cenName j` (the list of nonempty-block centre positions, in order) and
the scalar `cnum j ≤ min(arena, mass)`; `coverSave` extends by one
compaction scan of `Xoff` — cost `O(n)` at the *root* call is fine; at
nested depths the scan must itself be member-list-driven (the parent
hands the sub-arena's member list down: R1.6).

R1.2 **The loop.** `while cur < cnum j` with
`ctr := cen[cur]`-indirection; `asg` re-indexed to compacted positions
by the cover pass (one more output of the same scan). The
`levelImplements` partition argument re-derives: exit at `cur = cnum`,
every vertex's `asg` names a compacted position (`CoverOut.asg_lt`
restated over `cnum`), turns partition the carrier as before.

R1.3 **Turn re-init (2F/D-a) — DECIDED: block-driven zeroing.** The
next-depth arrays are zeroed *only at the previous turn's touched
cells*, driven by the member list `Xmem[Xoff c′ .. Xoff (c′+1))` — the
touched set of a turn *is* its block, statically. `treset`-style trail
arrays (P0.4 mechanism) remain the fallback for passes whose touched
set is data-dependent (the expansion frontier, the BFS queue), where
the tower's trail acceptance already proved the pattern.

R1.4 **Per-turn leaves block-driven.** D2a/D4/D7a fills, D3/D7d/D8–D10
mask passes, the colour chains and the expansion chain (2G/D-c) walk
the member list, not the carrier: `ClusterSynth.scatPass` is the
block-scan template. Per-turn cost `O(Σ_{v∈X_c}(1 + deg v) + mb·cap)`.

R1.5 **Readback (2F/N-3) — DECIDED: retained boundary.** `readbackCom`
keeps its formula-generated body (the `botCom`/`baseCom` precedent:
name-generating, formula-indexed code stays hand-written); only its
loop header changes from the carrier scan to the member-list scan.

R1.6 **Nested order/cover phases active-set-driven.** The engines
receive the arena's member list (the parent's block, threaded like the
masks are today) and charge `Σ_{v∈X}(1 + deg v)`; `Elim`/`Cover`/`BFS`
block-driven variants are tower re-derivations in the established
shape (touched-only memory rule: charge active sets from the first
brief).

R1.7 **Scatter phase.** The two per-atom `copyCom`s become member-list
copies; the scatter engine's carrier terms (`scatK`'s `33·n`) get an
active-set variant. The per-atom count is a formula constant — only
the per-atom width matters.

R1.8 **Base case.** `baseCom`'s scans walk the member list (the
depth-ℓ arenas number up to `mass_{ℓ−1}` calls); `Cb·(m+1)` shape.

R1.9 **Unchanged**: the per-depth name generation, the two-arena
(work/game) discipline, `botCom`'s formula recursion, the obligation
Props' split (six phases + inner + frames), `RamDriverWrites`' frame
architecture (extended by the new names `cenName`/`cnum`).

## §7 The engine-swap map

| obligation / slot | current discharger | tower export | status / gap |
|---|---|---|---|
| BFS under cover | — | `BfsBridge.bfsQCom` + `bfsQCom_spec` | **integrated since P1** (text swap precedent) |
| `ElimAvail` (machine) → `ElimAvailA` | `RamElim.implements` | `ElimSynth6.elimAvailA_of_engine`, engine `elimEngine5_le`, `engineK5 = 333n+168ns+45` | **landed green** (parallel F1 wave, this session) |
| `OrderImplements` at R=0 | `RamDriverCompose.orderImplements₀` | `OrderSynth.orderPhase0_le` (consumes `ElimAvailA` — now discharged) | Spec-bridge to the driver Prop = **brief B1** (the PoC swap; 2E/E3) |
| `CoverImplements` | `RamDriverCompose.coverImplements` | `CoverSynth` turn loop + `emitRun_*` | gap: `ReachedList` discharge (a BFS-wave clause, `CoverSynth:843`); block-injectivity feeds §5.5 |
| cluster leaves (D2–D10, C1–C3) | `RamDriverDescend` walks | `ClusterSynth` (`scatPass`, `andPass`, `subPass`, self-reading variants), `OrderSynth.fillPass/copyPass` | green as leaf specs; block-driven forms = **B4** |
| expansion chain (D6) | hand chain | `ExpandSynth.expPass_expandVal` (47n+30ns+4; n·ns dead) | nested-loop composition debt (2F §9 debt 1); block-driven = B4 |
| scatter engine | `RamScatter.scatter_spec` | `ScatterSynth.scatterTowerCom_spec` (whole engine) | text swap ready; active-set variant = B4 |
| cluster load / masks | hand walks | `ClusterSynth.clusterLoad0_le` (12n+15m+19 vs 16n²) | the first touched-only proof — the Σ interface is what consumes it |
| `AugAvail` | `RamDriverAugment.implements` (retained, FLAG-2) | `AugmentSynth` 5/10 passes | **re-scoped by F2**: C0-relevant under D-2a; completion = B5 |
| base case | `RamDriverCompose.baseImplements` (retained, 2A ruling) | — | loop-header delta only (R1.8) |
| readback | `RamDriverBase.readbackStep` | retained boundary (R1.5 decision) | — |
| sentence readback / decode | `RamDriverIO` | — | untouched (root-only, O(n + ns)) |

Integration facts every B-wave brief must carry: entry stores pin
`zero`/`one` (and `"sv" = 1` for the cluster load — owned equal-value
cells consumed in context order, 2F/D-e); junk cells are consumed in
written order across leaf boundaries — pin composed programs from the
tool's report, never hand-seq (2E/D-d); loop states assemble with
`mopPair`/pack, never literal tuples (P4/D-m); `omega` is blind through
`Ir.Val` — bind at ℕ; `decide +kernel` on string-chain arithmetic;
never `simp [Codegen.embed]`; `ac_rfl` diverges past ~40 ACost atoms;
qualify `mopPred`/`mopSetIn` against `Sepref/IrOpsExtra`;
`Codegen.cash` ≠ bare `cash`.

## §8 Integration-B briefs

**B1 — PoC ordering-phase swap at R = 0** (executable now, no
decisions needed; recommended first). Discharge
`RamDriver.OrderImplements` (current shape) from
`OrderSynth.orderPhase0_le` + `ElimSynth6.elimAvailA_of_engine`,
replacing `orderImplements₀`'s hand-walked elimination interior, via a
`Spec`-level bridge in `Refine/OrderBridge.lean` on the P1 template
(BfsBridge's seven points; bridges thin, recorded). Validates: tower
export ↔ driver Prop vocabulary (`arrOf`/list, `OrdersBy` transport),
`engineK5` flowing into `Ko`. Budget: one session. Falsification: the
bridge Prop's negative control is `OrderSynth`'s own `ElimOut`
mismatch example; `lax` namespace audit gates.

**B2 — Σ/size re-threading** (§5; after D-1, jointly with B3). Order:
`SigmaLoop` (landed) → §5.2 turn-index + §5.3 descend clause → §5.6
induction re-thread → §5.7–5.9 root + solver extension. Falsify first:
the §5.6 side condition's star `#guard` (extend `CostShapeProbe`), a
negative control refuting the "Σ over all `n` blocks at the compacted
loop" mis-reading, and `Plausible` on `arenaSize`/`blockSize` lemmas.
The `levelImplements` induction survives with parameters re-threaded —
re-proving any semantic clause is the stop signal.

**B3 — R1 skeleton** (§6; after D-1). Cover-phase compaction outputs +
loop header + partition re-derivation + `RamDriverWrites` extension.
Single-owner (it is one induction); leaf swaps stay out (B4).

**B4 — block-driven leaves** (after B3; parallelizable per leaf).
Fills/masks/colour/expansion/scatter/readback-header per R1.3–R1.7,
each: tower re-derivation in `Refine/`, spec at the member-list
precondition, cost `O(block + edges(block))`, `#guard` probe on a
two-block instance, swap into `clusterCom`, re-discharge the (shape-
preserved) leaf Prop.

**B5 — the R\* ordering phase** (after D-2a; independent of B2–B4).
The `tgt`-widening wave across `RamBfs`/`RamCover`/`RamScatter`/
`RamBfsPaths` (width parameter per `RamElim.ElimPre`'s discipline),
`W ≥ chainWidth` threading (`TgtCoupling.chainWidth`), counting sorts
re-enabled, `orderImplements` at `R = R*`, the §5.4 predicate `P`
discharged from the chain via `exists_cover_degree`'s hypotheses
(all of them postconditions of the two engines — its docstring's "what
supplies the hypotheses" list). `AugmentSynth` completion folds in
here at supervisor discretion (FLAG-2).

**B6 — mass mathematics** (parallel, zero program contact).
(i) `CoverOut` block-injectivity ⇒ `mm = Σ_c (cluster c).ncard`
(strengthen the pass invariant or add the clause; `CoverSynth`'s
`ReachedList` injectivity is the tower-side twin); (ii) the §5.5
`hmass` lemma; (iii) `exists_driverCostsSigma` in `CostRecurrence`
(§5.9); (iv) the `(⌈c·n^{ε/ℓ}⌉+1)^ℓ ≤ c'·n^ε`-form real-exponent
lemma for P4.

**B7 — P4 assembly** (last): instantiate §5 with B4/B5 costs via B6's
solver, `Spec`→`ComputesInTime` bridge, C0 discharged kernel-three,
`lean_verify`, root `lax` audit, then FLAG-1 disposal.

Dependency order: B1 now; D-1 → B3 → B2 → B4; D-2a → B5; B6 anytime;
B7 last. B2 and B5 are the two critical paths; B4 fans out.

## §9 Landed vs designed; falsification record; ledger

**Landed this wave (green, additive; no frozen surface touched):**

- `proofs/Lax3Proofs/Refine/SigmaLoop.lean` — `forRangeZeroSum` (the
  Σ-shaped counted scan; per-turn budgets, cost `Σ (Kb k + 4) + 6`),
  `sum_const_eq_uniform` (constant instantiation = `forRangeZero`'s
  bound exactly).
- `proofs/Lax3Proofs/Refine/CostShapeProbe.lean` — star probe
  (`starSizes`, `star_mass_linear`, `star_uniform_quadratic`,
  `star_uniform_gap`, `#guard`s at n = 8, 32), negative control
  (`sum_le_uniform`), the compiled interface floor
  (`kin_le_turnCost`, `uniform_interface_floor`,
  `uniform_interface_floor_zero`), the solver-shape bridge
  (`sigma_coefficients_geometric`, `#guard` contrast).
- `proofs/Lax3Proofs.lean` — the two imports.

**Designed only (blocked on D-1/D-2):** everything in §5–§6; briefs
B1–B7 (B1 is unblocked and recommended as the next spawn).

**Falsification record:** star probe compiled before any design was
frozen (the Σ-vs-uniform gap is arithmetic, not opinion); the
uniform-interface floor is a *compiled refutation of the frozen
interface's fitness* — the strongest possible pre-surgery negative
control; `sum_le_uniform` / `sum_const_eq_uniform` are the two negative
controls showing the revision is conservative; the P3 solver's own
`#guard` falsification block (`CostRecurrence.lean` §Falsification)
covers the solver shapes reused in §2.4. The program floor (F1) is a
paper argument (§2.2) — six lines, no authored obligation rests on it
un-compiled; B2 may compile it as collateral.

**Ledger:**

- L1 (this wave): two additive files + two root imports in the ND-MC
  proofs package; no `word-ram/` contact; no `ElimSynth*` contact; no
  frozen statement edited; nothing committed (supervisor commits).
- L2 (this wave): surgery on `levelImplements`/`driver_correct`/
  `driverRoot_decides_sentence` deliberately **not** executed — brief
  §6 STOP on findings F1/F2; this document is the deliverable in its
  place.
- L3 (standing, for B-waves): the Σ-loop rule lives in the consumer
  package (`Lax3Proofs.Refine.SigmaLoop`) rather than the reasoning
  kit because `word-ram/` is another wave's; if the kit later adopts
  it, dedupe then (tower fidelity charter applies there, not here).

**Build/audit:** `lake build` in
`nowhere-dense-model-checking/proofs`: `Build completed successfully
(3513 jobs)` (includes the parallel wave's `ElimSynth6`).
`lax build --only proofs nowhere-dense-model-checking`: `OK` (the two
standing lakefile `require`-warnings are the plan-sanctioned
`Lax13Proofs`/`Lax12Proofs` requires).
