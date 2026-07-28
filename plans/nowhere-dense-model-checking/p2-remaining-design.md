# P2 remaining lemmas — design record (session 2, 2026-07-28)

Verified-on-paper designs for `separate` (Lem 8, tex 744–866),
`farQuant` (Lem 12, tex 868–1112) and the `locality`/`normalForm`
assembly (tex 1114–1162), all **contingent on the guard-set exL
surface** of `exl-guard-decision.md` (branch `nd-mc-exl-guard`).
Written now so the next session's track briefs are a copy-paste. Radii
below use `r⁻ := rhoMinus (k+1) q'` and `r⁺ := rhoPlus (k+1) q'` at
the rank in force.

## separate (Lem 8) — reindexed contexts, no substitution

Statement shape (the mixed-context form; no `UsesOnly`, no rename in
the statement):

```lean
theorem separate {L K a b k q : ℕ} (φ : DistFO L K) (hloc : IsLocal φ)
    (hφ : DRank k q φ) (e₁ : Fin a → Fin K) (e₂ : Fin b → Fin K)
    (h₁ : Function.Injective e₁) (h₂ : Function.Injective e₂)
    (hdis : ∀ i j, e₁ i ≠ e₂ j) (hcov : ∀ v, (∃ i, e₁ i = v) ∨ (∃ j, e₂ j = v)) :
    ∃ P : List (DistFO L a × DistFO L b),
      (∀ p ∈ P, IsLocal p.1 ∧ DRank k q p.1 ∧ IsLocal p.2 ∧ DRank k q p.2) ∧
      ∀ n (G : SimpleGraph (Fin n)) col (m : Fin K → Fin n),
        (∀ i j, ¬ WithinDist G (rhoMinus k q) (m (e₁ i)) (m (e₂ j))) →
        (Sat G col m φ ↔ ∃ p ∈ P, Sat G col (m ∘ e₁) p.1 ∧ Sat G col (m ∘ e₂) p.2)
```

Each output formula lives in its own side's context, so its guards
(`univ` or subsets of the side) *are* the source's per-side guards —
zero guard hypotheses, zero embeddings inside the induction. Induction
on the `DRank` derivation (rank steps (k+1, q−1) at binders come for
free), generalizing `a b e₁ e₂`; `IsLocal` kills the `exU` case.

- Atoms: one-sided atoms are rebuilt with reindexed variables (the
  side-preimage of each variable, from `hcov`/`hdis`); cross atoms are
  false under the far hypothesis (adj/eq/distLe radii ≤ ρ⁻(k,q)), so
  the output list is empty.
- not: De Morgan + distribute — DNF over the complemented pair list.
  and: pairwise products. Small list-algebra helpers (`bigAnd` etc.)
  with Sat/IsLocal/DRank lemmas.
- exL r g ψ (input guard set g): split the witness v by
  (1) within r⁻ of the full x̄-side, (2) within r⁻ of the full ȳ-side,
  (3) neither, and then ∃ i ∈ g within r of m i splits into
  3a (i on the x̄-side) / 3b (i on the ȳ-side).
  - Case 1: IH on ψ with split (x̄z ; ȳ) — far condition for the new
    split from the triangle inequality and
    `rhoPlus_add_rhoMinus_le` (2ρ⁻(k+1,q−1) ≤ ρ⁻(k,q)); output
    disjuncts β_j ∧ `.exL r⁻ univ α_j` on the a-context (relaxed guard
    bound admits radius r⁻ ≤ r⁺, `rhoMinus_le_rhoPlus`).
  - Case 2: symmetric.
  - Case 3a: IH on ψ with split (x̄z ; ȳ) again — far for (v, ȳ) holds
    because v is within r ≤ r⁺ of the x̄-side and
    ρ⁺(k+1,q−1) + ρ⁻(k+1,q−1) ≤ ρ⁻(k,q); output
    `.exL r (g∩x̄-side, reindexed) ((⋀ᵢ ¬ distLe r⁻ i.castSucc last) ∧ α_j)`
    — the ¬near-ȳ half of the source's annulus is implied by farness
    (eq. (eq1) of the tex, same Horizon inequality), so it is not
    written. Atom radius r⁻ is budget-exact at rank (k+1, q−1).
  - Case 3b: symmetric on the ȳ-side.

Session-1's `snoc_comp_renameLift` provides the environment identity
for the binder-extended embeddings (e₁' = snoc (castSucc ∘ e₁) (last),
e₂' = castSucc ∘ e₂).

## farQuant (Lem 12) — source-verbatim, capsule embedding now sound

```lean
theorem farQuant {L : ℕ} (choice : ScatterChoice) {k q' : ℕ} (hk : 1 ≤ k)
    (β : DistFO L 1) (hloc : IsLocal β) (hβ : DRank (k + 1) q' β) :
    ∃ bc : BC (DistFO L k ⊕ ScatterSentence L),
      (∀ ψ, Sum.inl ψ ∈ bc.atoms → IsLocal ψ ∧ DRank k (q' + 1) ψ) ∧
      (∀ σ, Sum.inr σ ∈ bc.atoms → σ.DRank k (q' + 1)) ∧
      ∀ n (G : SimpleGraph (Fin n)) col (m : Fin k → Fin n),
        ((∃ x, (∀ i, ¬ WithinDist G (rhoMinus (k + 1) q') (m i) x) ∧
            Sat G col (fun _ => x) β) ↔
          bc.eval (Sum.elim (Sat G col m) (ScatterSentence.Sat choice G col)))
```

Independent of `separate` (β is abstract) — parallelizable. Pieces:

- Capsule embedding `β↑ := rename (fun _ : Fin 1 => Fin.last k) β`;
  soundness `Sat (snoc m v) β↑ ↔ Sat (fun _ => v) β` is a direct
  instance of the unconditional `sat_rename`.
- `ClusterSystem` at r := ρ⁻(k+1,q') via `nonempty_clusterSystem hk`;
  X := {x | Sat (fun _ => x) β}; S from `choice.spec G (4·C.R) X`
  (finite by `Set.Finite` on `Fin n`); `scatterCore` with
  H := ρ⁺(k+1,q'), side condition 4·C.R + r ≤ H from `ClusterSystem.R_le`
  and `rhoPlus_eq` (4·9^(k−1)+1 ≤ 9^(k+1)).
- The cluster data (t-scale, I, sel) ranges over finitely many
  configurations, each recognized by a conjunction of distance
  atoms/negations among the m-entries at radii ≤ 8·9^(k−1)·r
  ≤ ρ⁻(k,q'+1) (tex 1046–1050; `nine_pow_mul_rhoMinus_le_rhoPlus` +
  `rhoPlus_le_rhoMinus`). BC-case over configurations.
- Condition (2a): `.exL r⁺ Finset.univ ((⋀ᵢ ¬ distLe r⁻ i.castSucc last) ∧ β↑)`.
- Condition (2b): per configuration, cluster test for cluster i:
  `.exL r⁻ {i's sel-class members…} β↑` — one guard-set singleton (or
  the class's members) per source tex 1097; counting formulas =
  boolean combinations over the ≤ k tests; s-value from scatter
  sentences ⟨4R, β, t⟩ for t ≤ k+1 ≤ k+q'+1, rank witness i = 1,
  window 4ρ⁻(k+1,q') ≤ 4R ≤ 9^(k+1)·ρ⁻(k+1,q') (tex 1080–1087).

## Assembly (Thm 1 → `locality` axiom; Cor 7 → `normalForm`)

Structural induction per tex 1119–1162. Needs a small BC-algebra
prelude (evaluate a `BC (φ ⊕ σ)` by cases on the scatter-atom truth
assignment; pull the scatter atoms out of a quantifier; conjunction/
negation/atom-map lemmas — `BC.eval`/`BC.atoms` are concept-side, the
lemmas proofs-side). Cases: atoms trivial; booleans by BC composition;
exL: IH, pull scatters out, wrap each local remainder (guard set and
radius unchanged, `DRank.exL`); exU with k = 0: scatter
⟨4ρ⁻(1,q'), ψ_τ, 1⟩ (ψ_τ : DistFO L 1 natively — no extraction);
exU with k ≥ 1: near disjunct `.exL r⁺ univ ψ_τ` ∨ far disjunct →
`separate` with e₁ = castSucc, e₂ = const (last k) (its b = 1 side is
the capsule, `(snoc m v) ∘ e₂ = fun _ => v` definitionally), then
`farQuant` per capsule; Obs 4/6 rank shifts via `DRank.antidiagonal` /
`ScatterSentence.DRank.antidiagonal` (landed session 1).
`normalForm`: instantiate `maxChoice`; correctness lemma
`sat_scatterFml`: `Sat Fin.elim0 (scatterFml r t β) ↔
ScatterSentence.Sat maxChoice …` — the t placements of β are sound by
unconditional `sat_rename`; the counting direction is
`Set.ncard`-arithmetic against `maxChoice.size` (both directions via
`exists_withinDist_of_maximal`-style arguments; the semantic-locality
side condition via `semLocal'` + the scatter radius window).

## Session split proposal (after the surface decision)

Three parallel tracks: (a) `separate`; (b) `farQuant`; (c) BC-algebra
+ `sat_scatterFml`. Then one serialized assembly session for
`locality` + `normalForm` + axiom discharge and the `lax build` +
kernel-axiom gate.
