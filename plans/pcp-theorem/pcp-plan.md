# The PCP theorem by gap amplification — campaign plan

Rev 1, 2026-07-29. **Status: PROPOSAL — unscheduled.** Drafted on a
dare ("think bolder"); nothing in it is accepted, budgeted, or queued
until Jan resolves the JAN-FLAGs. On acceptance this document becomes
the contract in the refinement-tower sense: implementing sessions
follow it, deviations need an owner decision first.

**Working model** (unchanged): Fable supervises — plan, sequencing,
review, acceptance calls, commits — and Opus subagents write the Lean.
All standing disciplines apply from day one: refute-before-prove on
every authored obligation, worktree workflow, namespace/splitter audit
(`lax build`, not `lake build`), named-Prop isolation for deep
obligation chains, single-owner repair waves, landed proofs are
capital.

## Goal

No proof assistant has ever checked a hardness theorem. Formalized
algorithmics — this repo included, and every other ecosystem — is upper
bounds: correctness, sometimes with a cost certificate. The lower-bound
half of the field is formally virgin. This campaign builds its
foundation and takes the summit first: **Dinur's gap-amplification
proof of the PCP theorem, machine-checked end to end** — a
machine-checked proof that proofs need not be fully read.

Two headline artifacts, deliberately decoupled so neither gates the
other:

1. **The Amplification Theorem (P7, machine-free flagship).** Dinur's
   core is a purely combinatorial statement: an explicit size-linear
   transformation on constraint graphs that doubles the unsat gap
   until it hits a constant. No machines, no NP, no asymptotics hidden
   anywhere — an auditable `∀`-statement about finite objects, citable
   on its own and immune to any dispute about machine models.
2. **The PCP theorem proper (P8).** NP defined over the repo's word
   RAM, Cook–Levin by RAM→circuit→CSP, the verifier formulation with
   explicit randomness/query constants. The refinement tower makes the
   reductions' own polynomial running time a theorem rather than a
   remark — a two-sided artifact (verified statement + verified
   reduction cost) that exists in no ecosystem.

Why this repo is the one that can: the cost-carrying RAM stack is
exactly the missing infrastructure for formal hardness (a reduction
without a cost bound is not a reduction); the refutation discipline
was built for precisely this mode — authored-from-prose obligations
with no formal source to port; and the CSP core seeds the broader
hardness program (ETH/SETH reduction calculus, switching lemma,
inapproximability zoo) as future campaigns on shared surface.

## The proof as modules

```
  P8  Cook–Levin over word RAM ──▶ CGSAT NP-hard at gap 1/|E|
                                        │
      ┌─────────────────────────────────┘
      ▼
  G over Σ₀ ─▶ [ prep ▷ power_t ▷ compose ]^(⌈log₂|E|⌉) ─▶ gap ε₀
                  │        │          │
                  │        │          └─ P6  Hadamard/quadratic assignment
                  │        │              tester (BLR + self-correction +
                  │        │              tensor consistency); Σ_big → Σ₀,
                  │        │              gap ×β₃
                  │        └─ P5  walk-power graph G^t: gap ×β₂√t
                  │               (capped at 1/t)
                  └─ P4  degree-reduce (expander clouds) + expanderize
                         (superimpose X_|V|) + self-loops: gap ×β₁
                              │
                              ├─ P3  explicit (d₀,λ₀)-expanders at EVERY size
                              └─ P2  spectral core: mixing, easy Cheeger,
                                     superimposition, walk pair-correlations
  P1  constraint graphs, UNSAT, gap-reduction calculus (shared surface)
```

**Main Lemma (one round).** There are a constant alphabet Σ₀, constants
C and ε₀ > 0, and an explicit `A : CG Σ₀ → CG Σ₀` with
`size (A G) ≤ C * size G`, `UNSAT G = 0 → UNSAT (A G) = 0`, and
`UNSAT (A G) ≥ min (2 * UNSAT G) ε₀`. The constant chase that makes it
true: prep loses a factor β₁, powering gains β₂·√t (truncated at 1/t),
composition loses β₃; choose t with β₁β₂β₃·√t ≥ 2. Iterating
⌈log₂|E|⌉ rounds from the trivial 1/|E| base gap gives constant gap at
size ≤ size₀^(1+log₂ C) — polynomial with an explicit exponent, which
is all the theorem needs.

Where the danger lives, module by module:

- **P5 powering soundness is the boss fight.** Given a good assignment
  for G^t, extract a plurality assignment for G and run the
  second-moment method over t-step lazy walks. Four ingredient
  obligations: plurality decoding bounds (probability ≥ 1/|Σ| of
  agreeing with the plurality opinion), the F-truncation trick
  (μ = min(UNSAT, 1/t)), the lazy-walk shift bound
  (TV(Bin(t,½), Bin(t,½)+1) ≤ c/√t via central binomial estimates),
  and walk pair-correlations from P2. Dense conditioning bookkeeping
  throughout; this module decides the campaign.
- **P3 exact sizes are folklore.** Expander clouds need an explicit
  (d₀, λ₀ < d₀) family at *every* size n (cycles provably do not
  suffice — they lose a polynomial factor on stars). The literature
  waves at "known constructions plus padding"; the patch (nearest
  Gabber–Galil square in [n, 2n], merge classes ≤ 2, re-regularize,
  quotient bound on λ) is known-to-experts, written-nowhere-carefully.
  Classic phase-eating material — hence a P0 spike, its own phase, and
  a fallback route (hard-direction Cheeger bridge) budgeted.
- **P6 stays constant-size by design.** The tester only ever runs on
  constant-size predicates (alphabet after powering is Σ₀^(d^O(t)),
  all constants), so Hadamard/quadratic codes suffice and *asymptotic
  coding theory is out of scope entirely* — a hard scope wall.
- **P8 model bookkeeping.** NP over the word RAM; RAM→circuit by
  brute-force per-step multiplexers over touched memory (polynomial is
  all we claim — no obliviousness, no sorting networks); circuit→CSP
  via gate-neighborhood alphabet; one composition round normalizes the
  alphabet to Σ₀. Verifier form: sample an edge (O(log n) coins), two
  queries, constant repetitions to soundness ½.

## Sources (fidelity-first; P0 pins editions and section numbers)

Unlike the tower this is not a port of formal artifacts. Fidelity-first
here means: the prose proof is followed at paragraph granularity, the
governing text for each module is fixed in advance, and every deviation
(representation, probability substrate) is a ledger entry.

| source | governs |
|---|---|
| Dinur, *The PCP theorem by gap amplification*, J. ACM 54(3), 2007 | overall structure; prep; composition; assembly |
| Radhakrishnan–Sudan, *On Dinur's proof of the PCP theorem*, Bull. AMS 44(1), 2007 | the powering analysis (their smoothing is the cleanest) — governing text for P5 |
| Hoory–Linial–Wigderson, *Expander graphs and their applications*, Bull. AMS 43(4), 2006, §8 | Margulis/Gabber–Galil construction and its analysis |
| Reingold–Vadhan–Wigderson, Annals 155, 2002 | zig-zag alternate route (watch the base-graph explicitness pothole) |
| Karayel, AFP `Expander_Graphs`, 2023 | port candidate for spectral theory + mixing (+ audit whether a strongly explicit family is included) |
| Goldreich, *Introduction to Property Testing*, 2017, ch. 5; BLR, JCSS 47, 1993 | linearity testing; combinatorial (Fourier-free) route |
| Arora–Barak ch. 22 | map only, never source |
| van Emde Boas, *Machine models and simulations*, Handbook of TCS A | RAM→circuit simulation shape (P8) |

## Ecosystem audit (believed state; every row confirmed in P0)

| need | believed state | action |
|---|---|---|
| Hermitian spectral theorem, Rayleigh quotients | in mathlib | consume |
| Courant–Fischer min–max | uncertain | author in P2 if missing (independently useful) |
| `Finset.expect`, variance, Chebyshev over finite uniform spaces | present / partial | P0 pins exact forms |
| central binomial bounds (for the TV shift lemma) | partial (`Nat.centralBinom` estimates) | authored obligation in P5 |
| characters / DFT on ℤ_m × ℤ_m (GG analysis) | `AddChar`+Gauss-sum machinery exists; DFT form uncertain | P0; needed only on the GG route |
| expanders, mixing lemma, explicit families | absent in Lean; Isabelle AFP has spectral theory + mixing | audit for port — the tower proved the porting muscle |
| NP, reductions, Cook–Levin | nothing usable in Lean (mathlib TM poly-time exists, no NP; external repos unvetted) | define over word RAM in P8 |
| PCP theorem, any assistant | no complete formalization exists | P0 literature sweep re-confirms |

## Submissions

Five directories, each independently citable, dependency-ordered
(JAN-FLAG 4 for the split):

| dir | surface | first-in-Lean claim |
|---|---|---|
| `constraint-graphs/` | constraint graphs, UNSAT value, size, gap-reduction calculus, executable evaluators | the shared hardness core (ETH program consumes it later) |
| `spectral-expanders/` | normalized adjacency, λ, mixing lemma, easy Cheeger, superimposition, walk correlations; explicit family at every size | first expander library + first explicit family in Lean |
| `linearity-testing/` | BLR + self-correction, Hadamard/quadratic assignment tester | first BLR in Lean |
| `gap-amplification/` | prep, powering, composition, Main Lemma, iteration — the Amplification Theorem | first hardness-amplification theorem in any assistant |
| `pcp-theorem/` | NP over word RAM, Cook–Levin, verifier form, PCP proper | first PCP theorem in any assistant |

## Phases

Each phase lands green with zero `sorry`, commits on its own, and is
reviewed at its boundary. Standing rules throughout: every executable
layer gets `Decidable`/`#eval` instances and Plausible generators the
day it lands; every authored inequality is numerically instantiated
before its proof is attempted; **all constants stay symbolic** (named
rationals with proved inequalities) until P7 assembly — no numeral is
baked into any phase statement (ledger L2); elaboration wall-clock
recorded per phase.

A note on end-to-end testing, recorded honestly up front: at the true
constants, t is astronomical and the pipeline is not executable end to
end. The harness therefore differential-tests each module's
*bookkeeping and completeness* at unsound toy parameters (t = 2, tiny
expanders) against brute-force UNSAT on ≤ 6-vertex, ≤ 3-letter
instances, and checks each module's *soundness constants* in isolation
at small scale. Soundness of the composed pipeline is what the proof
is for.

### P0 — Sources, design record, expander spike · budget 2–3 sessions

Pin sources to editions/pages; run the ecosystem audit table; literature
sweep re-confirming no prior formal PCP. Deliverable:
`plans/pcp-theorem/design.md` — statement shapes for UNSAT, the Main
Lemma, the Amplification Theorem, and the P8 endpoints; representation
decisions (multigraph as indexed edge family `Fin m → V × V` with
first-class self-loops/parallels, symmetrization at evaluation — ledger
L6); the opened ledger. **Spike (timeboxed, in-phase): the exact-size
expander route** — GG + merge-patch vs zig-zag vs AFP port — with a
memo recommending one and costing the fallback. Harness skeleton lands:
brute-force UNSAT, Plausible generators, differential runner. Design
record is the campaign's biggest review point (JAN gate).

### P1 — `constraint-graphs/` core · budget 1–2 sessions

Objects, UNSAT value, size, satisfying-assignment predicates, the
gap-reduction calculus (completeness/soundness/size composition lemmas
— the interface every later phase and the future ETH program consumes),
executable evaluators. *Acceptance:* `#eval` UNSAT agrees with brute
force across the generator suite; Plausible suites green; `lax build`
namespace gate.

### P2 — Spectral core · budget 2–3 sessions

Normalized adjacency operator of a regular multigraph; λ via
Courant–Fischer (authored if mathlib lacks it); expander mixing lemma;
easy-direction Cheeger (h ≥ (d−λ)/2); superimposition subadditivity
(λ(A+B) bound on 1⊥); **the walk pair-correlation lemma** — for
stationary lazy walks, P[eᵢ ∈ F ∧ eⱼ ∈ F] ≤ μ(μ + λ̄^(|i−j|−1))-shape,
pinned to the exact form P5's second moment consumes (that exact form
is the acceptance contract between the two phases). Runs parallel to
P1 (different owners). *Acceptance:* correlation bound instantiated on
≥ 2 concrete graphs by exact ℚ walk-counting (matrix powers), including
one near-tight case (a cycle) to confirm the bound degrades honestly.

### P3 — Explicit expanders at every size · budget 2–4 sessions

Route per the P0 spike; default expectation: Gabber–Galil on ℤ_m × ℤ_m
(HLW §8), then the every-n patch — nearest square in [n, 2n], merge
classes ≤ 2, re-regularize with self-loops, quotient/Rayleigh bound on
the merged λ. Fallback if the λ-patch fights back: patch edge expansion
combinatorially and cross the h→λ bridge (hard-direction Cheeger,
budgeted as the fallback cost). Executable construction.
*Acceptance:* `expanderFamily n` with proved (d₀, λ₀); harness checks
edge expansion on all n ≤ 40 against the proved bound.

### P4 — Preprocessing · budget 1–2 sessions

Degree-reduce (equality-constraint expander clouds; plurality
extraction via cloud edge-expansion), expanderize (superimpose the P3
family, add self-loops), regularity + λ of the result, gap loss β₁
symbolic. Can develop against P3's *interface* before P3 lands.
*Acceptance:* completeness exact on the toy suite (satisfying
assignments map constructively); measured UNSAT ratios on exhaustive
small instances within the proved β₁.

### P5 — Powering · budget 4–6 sessions · the long pole

G^t on walk edges; opinion alphabet Σ^(ball(⌈t/2⌉)) kept abstract
(Fintype instances stated, never computed through — watch R4);
completeness; then the soundness ladder as named Props, one satellite
file each: plurality decoding, truncation, the TV shift bound
(authored: TV(Bin(t,½), Bin(t,½)+1) ≤ c/√t), per-position hit
analysis, second-moment assembly on P2's correlation lemma.
Governing text: Radhakrishnan–Sudan. Every intermediate claim is
Plausible-refuted on toy walk spaces before any proof attempt.
*Acceptance:* `unsat_power` with symbolic β₂; measured gap growth on
the toy suite consistent with the instantiated constants.

### P6 — Alphabet reduction · budget 2–4 sessions

`linearity-testing/`: BLR by the combinatorial route (ledger L7 —
constants are irrelevant, machinery is not), self-correction, tensor
consistency, quadratic arithmetization of a fixed predicate — the
Hadamard/quadratic assignment tester with perfect completeness and
constant rejection ratio. Then robustization (Hadamard-encode endpoint
values; distance ½ does the work) and the composition theorem, gap loss
β₃ symbolic. Partially parallel to P5 after P2 (different owners).
*Acceptance:* tester correctness; gadget exhaustively checked on one
small concrete predicate; composition bookkeeping differential-tested.

### P7 — Assembly: the Amplification Theorem · budget 1–2 sessions

The constant chase (choose t against β₁β₂β₃; fix ε₀, C as named
constants with proved inequalities), the Main Lemma, the iteration
induction (gap doubling, size ≤ size₀^(1+log₂ C), alphabet fixed at
Σ₀), and the flagship statement audited against the design record.
*Acceptance:* end-to-end pipeline runs at toy parameters
(plumbing/completeness); statement review with Jan before the
endorsement surface freezes (JAN gate).

### P8 — Machine closure: the PCP theorem · budget 3–5 sessions

NP over the word RAM (verifier RAMs, poly bounds, many-one reductions
with cost); Cook–Levin: RAM→circuit by brute-force multiplexer
simulation of touched memory (polynomial only), circuit→CSP with
gate-neighborhood alphabet, one composition round to Σ₀ — CGSAT
NP-hard at gap 1/|E|; the verifier formulation and
`NP ⊆ PCP[O(log n), O(1)]` with explicit constants. Reduction programs
ride the refinement tower (soft dependency: tower P5's cashing theorem;
fallback: hand-verified IMP+ via the existing kit). The NP-over-RAM
statement shape is endorsement-sensitive: JAN-FLAG 3.
*Acceptance:* `pcp_theorem` and `cook_levin_ram` land with the
constants visible; endorsement-surface review.

### P9 — Wrap · budget 1 session

One demonstration corollary if cheap (gap-3SAT via the standard
translation); ledger review with Jan; submission drafts (never
registered — standing consent rule); index/README/NIGHTLOG/memory.

**Total budget: 20–32 sessions** — the largest campaign this repo has
attempted, ~1.5× the tower's. P5 is the long pole; P1∥P2 and P5∥P6
parallelism can compress wall-clock but not the budget. Set
expectations by the budget, not recent luck.

## Ledger (seeded; P0 completes)

| id | decision | reason |
|---|---|---|
| L1 | probability = finite counting (`Finset.card`/`Finset.expect` over walk Fintypes), no measure theory | substrate ergonomics; every space is finite uniform |
| L2 | all constants symbolic until P7; no numerals in phase statements | a wrong constant must re-thread one file, not eight phases |
| L3 | composition alphabet Hadamard/quadratic only, constant size; asymptotic coding theory excluded | scope wall — the proof never needs it |
| L4 | expander route decided by P0 spike; GG default, AFP port if the audit pays, zig-zag last (base-graph explicitness pothole) | highest-variance prerequisite gets the earliest decision |
| L5 | machine model = word RAM; NP defined over it; no TM bridge this campaign | repo capital; the bridge is real work with zero new mathematics — flagged (JAN-FLAG 3) |
| L6 | multigraph = indexed edge family, self-loops/parallels first-class, symmetrize at evaluation | prep and powering create both; orientation bookkeeping decided once |
| L7 | BLR by the combinatorial proof, not F₂ Fourier | constants are irrelevant here; avoids a Fourier dependency (revisit only if the GG route imports characters anyway) |

## Risks

| id | risk | mitigation |
|---|---|---|
| R1 | powering analysis subtleties (the historical site of PCP-exposition bugs) | one governing text (R–S) at paragraph fidelity; every claim refuted numerically first; named-Prop satellites |
| R2 | exact-size expanders fight back | P0 spike; own phase; h→λ fallback budgeted; worst case "every n ≥ n₀ + finitely many by hand" is still a theorem |
| R3 | a constant is wrong late | L2 symbolic discipline; P7 is the only place numerals exist |
| R4 | Fintype/instance blowup on opinion alphabets (Σ^(d^t)) | parameters abstract; never `decide`/`#eval` through the big alphabet; wall-clock per phase watched |
| R5 | mathlib gaps (Courant–Fischer, binomial TV) | author them; each is independently citable |
| R6 | scope creep (codes, Fourier, optimal constants) | L3/L7 walls; "Not in scope" is contract |
| R7 | NP-over-RAM contested at endorsement | flag 3 up front; the machine-free P7 flagship is unconditional either way |

## Not in scope

Parallel repetition and anything UGC; optimal query/alphabet/soundness
constants; Håstad-style tight inapproximability; PCPPs beyond the fixed
constant-size assignment tester; quasi-linear-size PCPs; derandomized
amplification; asymptotic coding theory; the TM↔RAM bridge; more than
one demonstration corollary.

## Watch items

- **Tower timing:** P8 consumes the tower's cashing theorem (tower P5);
  on current cadence it lands long before PCP P8 — if not, the IMP+ kit
  fallback is already costed.
- **AFP `Expander_Graphs` port:** if the P0 audit finds a strongly
  explicit family there, P3 becomes a port phase and the budget's lower
  end applies.
- **Workforce contention:** ND-MC P7 walks and tower P3+ are live;
  PCP P0 must not make three campaigns compete for the same overnight
  slot (JAN-FLAG 2).
- **Downstream campaigns on this core** (not this plan, recorded so the
  surfaces are shaped for them): ETH/SETH as named hypotheses + the
  fine-grained reduction calculus on `constraint-graphs/`;
  switching-lemma/AC⁰ on the counting substrate; Reingold SL = L on
  `spectral-expanders/`; inapproximability corollaries on
  `pcp-theorem/`.

## JAN-FLAGs (all open)

1. **Charter scope.** Accept the campaign at all — and if so, through
   P8, or machine-free through P7 with P8 chartered separately?
   *Recommendation: charter through P8 with a hard review gate at P7.*
2. **Sequencing.** When does P0 start? *Recommendation: not as a third
   concurrent campaign — queue PCP P0 behind whichever of ND-MC P7 /
   tower closes its phase first; the plan holds until then.*
3. **NP over the word RAM, no TM bridge.** Acceptable endorsement
   surface for P8's headline? (P7's flagship is unaffected either way.)
   *Recommendation: yes — the RAM is the repo's endorsed model and the
   bridge adds no mathematics; state the model prominently in
   `pcp-theorem/concepts`.*
4. **Submission split.** Five directories as tabled, or fold
   `constraint-graphs/` and `linearity-testing/` into
   `gap-amplification/` for three? *Recommendation: five — each carries
   an independent first-in-ecosystem claim, and the core must outlive
   this campaign.*

## Progress log

- 2026-07-29 — rev 1 drafted (unsolicited dare, Jan's "think bolder"
  prompt); status PROPOSAL; JAN-FLAGs 1–4 open; no work scheduled.
