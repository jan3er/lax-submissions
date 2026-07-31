# P3.C design — mathlib asymptotic face

Status: ACTIVE, 2026-07-31. P3.C-A through P3.C-D are complete; P3.C-E is next. This note freezes the source-facing decomposition
for P3.C. It is subordinate to `tower-expansion-plan.md` and its source-first
firewall.

## Source and substrate pins

- `bzhan/Imperative_HOL_Time` commit
  `09f9bc7a7cf177d3adf1e9ce6adae09a85ebe5ec`:
  `Asymptotics/Asymptotics_1D.thy` (864 lines),
  `Asymptotics_2D.thy` (676), and
  `Asymptotics_Recurrences.thy` (589).
- Supporting ML architecture at the same pin:
  `landau_util.ML` and `landau_util_2d.ML`. These are design sources for named
  rule families; their Isabelle/ML registry and normalizer are not text-port
  targets.
- Lean substrate: mathlib commit
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`, especially
  `Analysis/Asymptotics/{Defs,Lemmas,Theta,SpecificAsymptotics}.lean`, genuine
  product filters, and `Computability/AkraBazzi/AkraBazzi.lean`.

## Frozen wave decomposition

The files are sequential because each later source theory imports the earlier
one. Workers create only their assigned leaf; the supervisor wires the root,
audits the source table, replays all gates, and commits to `main`.

| wave | owned Lean file | exact source family | gate |
|---|---|---|---|
| P3.C-A — complete | `Refine/Asymptotics/OneDimensional.lean` | 1D lines 7–384: nonnegativity, `polylog`, stability, eventual monotonicity, basic O/Ω eliminators and growth consequences | 38-row source table; strict polylog comparison; sum/product stability and monotonicity; O and Ω extraction; supervisor gates green |
| P3.C-B — complete | `Refine/Asymptotics/OneDimensionalOperations.lean` | 1D lines 386–854: composition, division/difference, ceiling/log, Θ addition, named normalization rules | 32 live declarations and four exclusions classified; composition, arithmetic/log, and named-rule gates green; supervisor gates green |
| P3.C-C — complete | `Refine/Asymptotics/TwoDimensional.lean` | 2D lines 5–270, 467–559, and 638–669 in dependency order: genuine product-filter notation, `polylog2`, stability/monotonicity, eliminators, multiplicative lifting | all 26 declarations mapped; genuine `atTop ×ˢ atTop`, independent-threshold/lifting gates, and supervisor builds green |
| P3.C-D — complete | `Refine/Asymptotics/TwoDimensionalComposition.lean` | 2D composition/comparison/normalization: lines 272, 342, 412, 432, 453, 563, 566, 602, 612, 624, 634, 671 plus the named rule family | 12 live declarations plus ML exclusion mapped; two-coordinate composition, partial comparison, and normalization gates green |
| P3.C-E | `Refine/Asymptotics/Recurrences.lean` | all public recurrence declarations at lines 7–585, including linear O/Ω/Θ families and bivariate families | source-shaped 1D and bivariate recurrence gates; reuse mathlib Akra–Bazzi rather than duplicate it |

After A–E are accepted, P3.C-F may add the plan's BfsQ O(n + ns) and
introsort O(n log n) demonstrations in a consumer/example leaf. It may not
strengthen either to Θ from an upper bound, and it may not import any ND-MC
module.

## Source dispositions fixed before implementation

- `polylog_power_compose` at 1D lines 489–498 ends in Isabelle `oops`; it is
  dead source and is an explicit exclusion, not a missing Lean proof.
- `landau_util*.ML`, `attribute_setup asym_bound`, and `method_setup
  master_theorem2` are substrate renderings. Named Lean declarations preserve
  the rule families; no tactic text-port is claimed.
- The executable `bla_time` and `ex` declarations in the recurrence theory are
  validation examples, not generic API, but their named definitions and gates
  remain scheduled because the source family is being ported at breadth.
- AFP Landau/Akra–Bazzi and CFML remain semantic references only. Adjacent
  source families are not active P3.C scope.

## P3.C risk register

These are acceptance-review items, not permission to redesign the source:

1. Isabelle Ω translates to reverse mathlib big-O (`g =O f`); every Ω theorem
   gets a direction audit.
2. The 2D carrier is the genuine product filter. Diagonal or iterated-limit
   substitutes are refuted controls, not alternate implementations.
3. Source `event_mono` is eventual monotonicity of the norm, not global Lean
   `Monotone`; source `stablebigO` scales natural arguments by positive natural
   constants.
4. Natural division and subtraction preserve truncation before coercion.
5. Nonnegative premises in monotonicity and Θ-addition rules are semantic;
   cancellation refutes their removal.
6. `polylog2` comparison is partial. Incomparable monomials remain a sum; a
   normalizer must not invent a total dominance order.
7. The ML reducers are partial, head-keyed auto2 infrastructure. P3.C ports
   their named theorem inputs and explicit gates, not equivalent automation.
8. Mathlib's Akra–Bazzi endpoint is reused. No duplicate recurrence object,
   theorem family, or master-theorem method is admitted.
9. The source's unused binder in `bivariateOmega`/`bivariateTheta` and poor
   global example names require an explicit D1 namespace/binder-rendering note
   if cleaned up; they may not be silently advertised as exact transcription.
10. Recurrence lower bounds retain pointwise nonnegativity where the source
    requires it. Weakening a premise to ease a proof changes the theorem.

## Acceptance law

Each wave must be zero-`sorry`/`admit`, build its leaf, carry kernel-three axiom
guards on principal exports, and include representative positive integration
checks. Per Jan's 2026-07-31 direction, routine source-shaped P3.C ports do not
need compiled falsification or negative-control suites; reserve those for a
genuinely new or subtle authored claim where source review and typechecking do
not adequately test the risk. P3.C closes only after a complete source-to-Lean
declaration table classifies every public declaration in all three theories as
ported, mathlib-supplied with a local source-shaped wrapper/gate, or explicitly
excluded for substrate/dead-code reasons.
