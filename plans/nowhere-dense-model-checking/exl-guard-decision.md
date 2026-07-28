# Decision request: the exL guard must carry its variable set (P2 session 2, 2026-07-28)

**Status: OPEN — needs Jan.** This reopens one file of the frozen
surface (`Lax3/DistFO.lean`). Nothing has been merged to main; the
proposed fix lives on branch `nd-mc-exl-guard` as a reviewable,
building prospective diff.

## The finding

The frozen `DistFO.exL` guard ranges over the **whole typed context**:

```
| _, m, .exL r φ => ∃ v, (∃ i, WithinDist G r (m i) v) ∧ Sat … (Fin.snoc m v) φ
```

The source's grammar does not do this. Its local quantification
(tex 495–499, 544–548) is `∃y (dist(x̄,y) ≤ ρ⁺(k+1,q−1)) ∧ φ(x̄y)`
where `x̄` is **an explicitly chosen variable set** recorded at
formula formation ("we write φ(x̄) to indicate that x̄ *contains* the
free variables of φ"); `dist(x̄,y) ≤ r` is by definition the
disjunction over exactly that set. A source formula placed in a wider
context keeps its own guard set; our frozen formula widens its guard
to everything in scope. Session 1 proved the symptom
(`not_forall_sat_rename`, `not_forall_sat_congr_of_usesOnly` in
`SyntaxLemmas.lean`): renaming and environment-congruence are false
for the frozen semantics precisely because the guard silently widens.

## Why it blocks the rest of P2

Session 1's prescription — "write out the guards as exU + binary
distLe atoms" — dies at Lemma 12 (far quantification, tex 868–1112),
which the remaining P2 work must formalize. Two places in its proof
embed a **one-variable capsule** β : `DistFO L 1` into the context
`ȳx` (k+1 variables) with x-only guards:

- the condition (2a) formula `∃x (dist(x,ȳ) ≤ ρ⁺) ∧ (dist(x,ȳ) > r) ∧ β(x)`
  (tex 1067–1074), and
- the cluster-intersection tests `∃x (dist(x,aᵢ) ≤ r) ∧ β(x)`
  (tex 1097) that condition (2b)'s counting formulas are built from.

Under the frozen semantics, every embedding of β (via `rename` or by
hand) widens β's internal guards to read ȳ — the exact
`not_forall_sat_rename` mechanism, e.g. β = "∃z within 1 of me,
colored 0" embedded next to ȳ picks up witnesses near ȳ. And the
write-out repair is **arithmetically impossible**: a guard pinned by
binary atoms must fit the atom budget ρ⁻ of the rank in force under
the binder, while guard radii legitimately run up to
ρ⁺ = 9^k · ρ⁻ at the same rank (`Horizon.rhoPlus_eq`). The rank
schedule has no slack anywhere — this is not a lemma-statement issue
but an expressibility gap of the frozen fragment.

Concretely, at rank (1,2): a capsule β(x) = ∃z (1 < d(z,x) ≤ 729) ∧
z-colored-0 (legal at (2,1), produced by the separation lemma's
annulus case) has a cluster test "∃x near ȳ with β(x)" that no
frozen-fragment (1,2) formula plus scatter sentences can express: the
inner quantifier cannot demand d(z,x) ≤ 729 without either reading ȳ
(wrong) or carrying a radius-729 atom where the budget is
ρ⁻(3,0) = 1.

The same disease infects the frozen **normalForm** axiom directly:
`scatterFml` places β at each of t bound witnesses via `rename`, so
under the frozen semantics each copy's local quantifiers read the
*other* witnesses — not the source's sentence (3). I therefore
believe both frozen axioms (`locality`, `normalForm`) are unprovable
and most likely **false** as they stand; the locality proof route is
certainly closed.

## The fix

`exL` carries its guard set, as the source's syntax does:

```
| exL {k : ℕ} (r : ℕ) (g : Finset (Fin k)) (φ : DistFO L (k + 1)) : DistFO L k
-- Sat:  ∃ v, (∃ i ∈ g, WithinDist G r (m i) v) ∧ Sat … (Fin.snoc m v) φ
-- rename f: guard set goes to g.image f
-- DRank.exL, IsLocal.exL: unchanged shape, no condition on g
```

The frozen behaviour is the special case `g = univ`; the empty guard
set keeps the "local quantifier of a sentence is vacuously false"
reading. The ≤-relaxed radius deviation (endorsed at P1) stays.

Consequences, all verified on paper end to end:

- `rename` and `UsesOnly`-congruence become **unconditionally** sound
  (the guard set travels with the formula); session 1's two
  counterexample theorems and all range-of-environment hypotheses
  disappear. `UsesOnly` gains `↑g ⊆ s` at `exL`, making it the honest
  "variables occurring in φ" it was meant to be.
- `scatterFml` becomes source-correct with **zero text changes** —
  `rename` now does the right thing.
- Lem 12 formalizes **verbatim**: cluster test = `exL r {yᵢ} (rename β)`,
  condition (2a) = `exL ρ⁺ univ (¬near-atoms ∧ rename β)`; all rank
  windows check against `Horizon` (4R ≤ 9^(k+1)ρ⁻ via
  `ClusterSystem.R_le`, i = 1 window per tex 1080–1087).
- Lem 8 (separation) needs no guard sets at all in the design I
  propose (outputs reindexed into per-side contexts, so `univ` guards
  are exactly the source's per-side guards); the guard sets are
  load-bearing only where the source embeds capsules.

Every statement on the rest of the surface is textually unchanged
(`Locality`, `NormalForm`, `ScatterSentences`, `ModelChecking`, all
graph-side files); they quantify over a now slightly richer syntax,
which makes the two axioms *stronger* and — unlike now — true.

## Blast radius

| file | change |
|------|--------|
| `concepts/Lax3/DistFO.lean` | the constructor + 5 clause updates + notes; **needs re-endorsement** |
| `proofs/Lax3Proofs/SyntaxLemmas.lean` | clause lemmas, unconditional rename/congruence, counterexamples deleted |
| `proofs/Lax3Proofs/SemLocal.lean` | exL cases restrict the guard to g — the induction only shrinks |
| everything else (concepts + Horizon, WalkDistance, Clusters, ScatterCore) | untouched, rebuild only |

The prospective rework on `nd-mc-exl-guard` builds green under
`lax build` with the usual kernel-axiom audit; the diff is the review
object. Cost if endorsed: ~0 extra sessions (this session did the
rework); separate + farQuant + assembly proceed next session as
planned. Cost if declined: no known route to the locality axiom —
the alternatives considered (keep frozen and hope for an exotic
proof; exU write-outs; per-depth atom pinning; reorganizing Lem 12
around ψ instead of capsules — the last rescues (2a) but provably not
the (2b) cluster tests) are each recorded above or fail on the ρ⁺/ρ⁻
budget gap.

## Ask

Endorse the revised `DistFO.lean` on `nd-mc-exl-guard` (or say what
should change). Until then P2 is paused; nothing surface-touching
lands on main.
