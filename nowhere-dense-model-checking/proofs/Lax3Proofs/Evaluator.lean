import Lax3Proofs.Assembly
import Lax3Proofs.CoverConstruction
import Lax3Proofs.Isolate
import Lax3Proofs.Reduction
import Lax3Proofs.Relativize
import Lax3Proofs.SplitterMono
import Lax3Proofs.SplitterWin

/-!
The **model-checking evaluator**: the recursion that descends the
isolation splitter game tree of `Lax3.SplitterGame` evaluating distance
logic, together with its correctness against `Lax3.DistFO.Sat` and the
math-core checkpoint — the evaluator decides every plain first-order
sentence on every member of a nowhere dense class.

# The recursion

Three fixed parameters run through the whole file: a top quantifier rank
`q_top`, a radius cap `cap`, and a batch bound `mb`. Covers are taken at
radius `cap` and the splitter game is played at radius `2 * cap`.

*Local tables* `tablesLocal b A col β v` decide a local one-variable
formula `β` at the vertex `v` of the arena `A`, with `b` rounds of the
game left. With a round left and a non-edgeless arena the *cluster step*
runs:

1. **cover** — an `cap`-neighborhood cover `X` of `A` is chosen
   (`Lax3Proofs.CoverConstruction`), and `v` is assigned the center `u`
   whose cluster contains the `cap`-ball of `v`;
2. **batch** — Splitter's move at `u` is chosen: a set `W` of at most
   `mb` vertices of the `2 * cap`-ball of `u` whose isolation, after the
   restriction to that ball, leaves a position won in `b` rounds;
3. **relativize** — the arena is cut down to the cluster `X u`, the
   cluster itself is recorded as a new color and the old colors are
   intersected with it, and `β` is rewritten by `Lax3Proofs.Relativize`;
4. **isolate** — the batch is enumerated, the distances to its members
   and to the color classes are recorded as capped profile colors, the
   batch is isolated, and the formula is rewritten by
   `Lax3Proofs.Isolate`;
5. **recurse** — the rewritten formula is evaluated on the isolated
   arena with one round fewer, through the non-local phase.

*Non-local tables* `tablesNonlocal b A col ψ v` handle the formula the
isolation rewrite produces, which is no longer local: the locality
theorem `Lax3Proofs.Assembly.locality` turns it into a boolean
combination of local formulas and scatter sentences, the local atoms are
read off the local tables at the same arena and the same round budget,
and — this is the collapse the design predicted — each scatter atom is
evaluated *inline*, by running the greedy scatter process of
`Lax3.ScatterSentences.greedyChoice` over the local table of its own
one-variable formula. No sentence-level recursion is needed anywhere;
`sentenceEval` repeats the same shape at arity zero, with the trivial
`localSentenceEval` for its local atoms.

# The rank invariant

Every formula a table is ever asked about carries a distance rank
`(k', q')` with `1 ≤ k'` and `k' + q' ≤ q_top`. Both rewrites preserve
distance rank exactly, and the sum `k' + q'` is what keeps every radius
in sight under `cap = ρ⁻(0, q_top)`: `ρ⁻(k', q') ≤ ρ⁻(0, q_top)` because
the horizon grows along the antidiagonal, and the guard horizon
`ρ⁺(k' + 1, q' − 1)` is below the same bound by the derived chain of
`Lax3Proofs.Horizon`. Since `1 ≤ k'`, the rank is always first
*normalized* one step down the antidiagonal, to `(k' − 1, q' + 1)`; at
that shape the guard bound is `ρ⁺(k', q')`, which
`Lax3Proofs.Horizon.rhoPlus_le_rhoMinus` puts below `ρ⁻(k' − 1, q' + 1)`
with no arithmetic on the `9 ^ e` normal forms at all.

# The deferred base case

At round budget `0` — and, at any budget, on an edgeless arena — the
tables *are* `Sat`. That is not a cheat and not a stub: a winning
position at budget `0` is an edgeless arena, on which `Sat` of a formula
whose radii are all finite is a lookup in the color rows plus counting.
Turning that lookup into an algorithm is the business of the RAM phases,
which implement the unary-structure evaluation; the mathematics of the
descent is complete without it, and stating the base case as `Sat`
keeps the correctness theorem free of an evaluation model.

# Termination

By the lexicographic pair (round budget, phase): the cluster step of
`tablesLocal` drops the budget before entering `tablesNonlocal`, and
`tablesNonlocal` drops the phase before calling `tablesLocal` back at
the same budget. Both functions are therefore well-founded rather than
structural definitions, so they do not reduce definitionally; every
proof below unfolds them through their equation lemmas.

# Formalization notes

No concept-side definition is ever handed to a tactic. `Sat`,
`SatWithin`, `DRank`, `IsLocal`, `WithinDist`, `ball`, `deleteVerts`,
`SplitterWins`, `rhoMinus`, `rhoPlus` and the scatter definitions are
taken apart through the clause lemmas of `Lax3Proofs.SyntaxLemmas`,
`Lax3Proofs.SplitterBasics` and `Lax3Proofs.BCAlgebra`, through the
inequality kit of `Lax3Proofs.Horizon`, or through the two `Iff.rfl`
clause lemmas recorded in this file. The definitions introduced here are
unfolded freely.

The batch, the cover, the cluster assignment and the boolean combination
are all `Classical.choose` of a proved existence statement, so the
functions are total and rank-free: nothing in their *bodies* mentions a
rank, and the rank hypotheses appear only in the correctness theorems.
The price is that a proof may never invent its own witness — it must
reason about the very data the function chose, which is what every
`Classical.choose_spec` below does.
-/

namespace Lax3Proofs.Evaluator

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.NeighborhoodCovers
open Lax3.ScatterSentences Lax3.SplitterGame
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.UniformQuasiWideness
open Lax3Proofs.Horizon Lax3Proofs.SyntaxLemmas Lax3Proofs.WalkDistance

/-! ### Plumbing

Four small facts with no distance logic in them: an enumeration of a
finite vertex set, the two monotonicity directions of Lax12's
isolation, the two horizon bounds the rank invariant delivers, and the
normalization of a rank to arity one.
-/

section Plumbing

variable {n : ℕ}

/-- A finite vertex set is in bijection with `Fin` of its cardinality;
`Set.ncard` *is* `Nat.card` of the coercion, so no cast intervenes. -/
private noncomputable def enumEquiv (S : Set (Fin n)) : Fin S.ncard ≃ S :=
  (Finite.equivFinOfCardEq (Nat.card_coe_set_eq S)).symm

/-- An enumeration of a finite vertex set by its own cardinality. The
isolation rewrite of `Lax3Proofs.Isolate` addresses the batch by such an
enumeration; which one is immaterial, and this is the one the evaluator
uses. -/
noncomputable def enumOf (S : Set (Fin n)) : Fin S.ncard → Fin n :=
  fun i => (enumEquiv S i : Fin n)

/-- The enumeration of a vertex set enumerates exactly that set. -/
theorem range_enumOf (S : Set (Fin n)) : Set.range (enumOf S) = S := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (enumEquiv S i).2
  · intro hx
    exact ⟨(enumEquiv S).symm ⟨x, hx⟩,
      congrArg Subtype.val ((enumEquiv S).apply_symm_apply ⟨x, hx⟩)⟩

/-- Isolating a larger set gives a smaller graph. -/
theorem deleteVerts_mono_set {V : Type*} {G : SimpleGraph V} {S T : Set V} (h : S ⊆ T) :
    deleteVerts G T ≤ deleteVerts G S := by
  intro a b hab
  obtain ⟨hadj, ha, hb⟩ := SplitterBasics.deleteVerts_adj.mp hab
  exact SplitterBasics.deleteVerts_adj.mpr ⟨hadj, fun hc => ha (h hc), fun hc => hb (h hc)⟩

/-- Isolating the same set in a smaller graph gives a smaller graph. -/
theorem deleteVerts_mono_graph {V : Type*} {G G' : SimpleGraph V} {S : Set V} (h : G ≤ G') :
    deleteVerts G S ≤ deleteVerts G' S := by
  intro a b hab
  obtain ⟨hadj, ha, hb⟩ := SplitterBasics.deleteVerts_adj.mp hab
  exact SplitterBasics.deleteVerts_adj.mpr ⟨h hadj, ha, hb⟩

end Plumbing

/-! ### The two horizon bounds

Both are the antidiagonal monotonicity of `Lax3Proofs.Horizon`,
iterated: trading a free variable for a quantifier never shrinks the
horizon, so a rank whose two coordinates sum to at most `q_top` has both
its horizons under `ρ⁻(0, q_top)`. No `9 ^ e` arithmetic appears.
-/

section Radii

/-- Pushing the free-variable coordinate of a horizon all the way down
to zero along the antidiagonal. -/
private theorem rhoMinus_le_rhoMinus_zero_add {k q : ℕ} :
    rhoMinus k q ≤ rhoMinus 0 (k + q) := by
  induction k generalizing q with
  | zero => exact rhoMinus_mono le_rfl (by omega)
  | succ k ih =>
    exact (rhoMinus_succ_left_le k q).trans
      ((ih (q := q + 1)).trans (rhoMinus_mono le_rfl (by omega)))

/-- **The distance-atom horizon of a table rank stays under the cap.**
-/
theorem rhoMinus_le_cap {k q Q : ℕ} (h : k + q ≤ Q) : rhoMinus k q ≤ rhoMinus 0 Q :=
  rhoMinus_le_rhoMinus_zero_add.trans (rhoMinus_mono le_rfl h)

/-- **The guard horizon of a table rank stays under the cap.** One step
of the derived chain ρ⁺(k+1, q) ≤ ρ⁻(k, q+1) reduces it to the previous
bound. -/
theorem rhoPlus_le_cap {k q Q : ℕ} (h : k + 1 + q ≤ Q) :
    rhoPlus (k + 1) q ≤ rhoMinus 0 Q :=
  (rhoPlus_le_rhoMinus k q).trans (rhoMinus_le_cap (by omega))

end Radii

/-! ### Reading the rank -/

section Rank

variable {L k : ℕ} {φ : DistFO L k}

/-- Normalizing a rank to arity one: a formula of distance rank
`(j + 1, q)` has distance rank `(1, j + q)`, by `j` steps along the
antidiagonal. This is the shape `Lax3Proofs.Assembly.locality` wants of
a one-variable formula. -/
theorem drank_one_of_drank : ∀ {j q : ℕ}, DRank (j + 1) q φ → DRank 1 (j + q) φ := by
  intro j
  induction j with
  | zero => intro q h; simpa using h
  | succ j ih =>
    intro q h
    have hj := ih (DRank.antidiagonal h)
    have he : j + (q + 1) = j + 1 + q := by omega
    rwa [he] at hj

end Rank

/-- The clause of scatter-sentence satisfaction, spelled out once so
that no tactic is ever handed `Lax3.ScatterSentences.ScatterSentence.Sat`
itself. -/
theorem scatterSat_iff {L n : ℕ} {choice : ScatterChoice} {G : SimpleGraph (Fin n)}
    {col : Coloring n L} {σ : ScatterSentence L} :
    ScatterSentence.Sat choice G col σ ↔
      σ.t ≤ choice.size G σ.r {a | Sat G col (fun _ => a) σ.β} := Iff.rfl

/-! ### The sentence base

A sentence of distance logic has no atoms at its top level: an atom of
arity zero would need a variable in `Fin 0`. So a *local* sentence is
built from negation, conjunction and local quantification alone, and a
local quantifier over the empty context is unsatisfiable — its guard is
a disjunction over a `Finset (Fin 0)`, which is empty. `localSentenceEval`
therefore decides a local sentence outright, with no arena and no
coloring. The `exU` clause is junk: an unrestricted quantifier is not
local, so `IsLocal` rules it out.
-/

/-- The truth value of a local sentence: negation and conjunction
structurally, an unrestricted quantifier junk (`IsLocal` excludes it)
and a local quantifier false, since over an empty context there is no
variable for its guard to be local to. Atoms cannot occur at arity
zero. -/
def localSentenceEval {L : ℕ} : DistFO L 0 → Prop
  | .adj i _ => i.elim0
  | .eq i _ => i.elim0
  | .color _ i => i.elim0
  | .distLe _ i _ => i.elim0
  | .distColorLt _ _ i => i.elim0
  | .not φ => ¬ localSentenceEval φ
  | .and φ ψ => localSentenceEval φ ∧ localSentenceEval ψ
  | .exU _ => False
  | .exL _ _ _ => False

section LocalSentence

variable {L n : ℕ} {A : SimpleGraph (Fin n)} {col : Coloring n L} {m : Fin 0 → Fin n}

/-- **The sentence base is correct**: a local sentence is decided by
`localSentenceEval` in every colored graph. The only case with content
is the local quantifier, whose guard ranges over an empty set of
variables and is therefore never satisfied. -/
theorem localSentenceEval_iff : ∀ (φ : DistFO L 0), IsLocal φ →
    (localSentenceEval φ ↔ Sat A col m φ)
  | .adj i _, _ => i.elim0
  | .eq i _, _ => i.elim0
  | .color _ i, _ => i.elim0
  | .distLe _ i _, _ => i.elim0
  | .distColorLt _ _ i, _ => i.elim0
  | .not φ, h => by
      rw [localSentenceEval, sat_not]
      exact not_congr (localSentenceEval_iff φ ((isLocal_not φ).mp h))
  | .and φ ψ, h => by
      rw [localSentenceEval, sat_and]
      exact and_congr (localSentenceEval_iff φ ((isLocal_and φ ψ).mp h).1)
        (localSentenceEval_iff ψ ((isLocal_and φ ψ).mp h).2)
  | .exU φ, h => ((isLocal_exU φ).mp h).elim
  | .exL r g φ, _ => by
      rw [localSentenceEval, sat_exL]
      constructor
      · exact False.elim
      · rintro ⟨-, ⟨i, -, -⟩, -⟩
        exact i.elim0

end LocalSentence

/-! ### The data of one cluster step

Every choice the cluster step makes is `Classical.choose` of a proved
existence statement, wrapped here so that the recursion's body stays
readable and so that a proof can name the chosen object.
-/

section Step

variable {n : ℕ}

/-- The neighborhood cover the evaluator uses on an arena, at radius
`r`: the one produced by `Lax3Proofs.CoverConstruction`. Its degree is
never used. -/
noncomputable def clusterOf (A : SimpleGraph (Fin n)) (r : ℕ) : Fin n → Set (Fin n) :=
  Classical.choose (CoverConstruction.exists_neighborhoodCover_degree_wcol A r)

/-- The chosen family is a neighborhood cover. -/
theorem isNeighborhoodCover_clusterOf (A : SimpleGraph (Fin n)) (r : ℕ) :
    IsNeighborhoodCover A r (clusterOf A r) (Lax12.ColoringNumbers.wcol A (2 * r)) :=
  Classical.choose_spec (CoverConstruction.exists_neighborhoodCover_degree_wcol A r)

/-- The cluster center a vertex is assigned to: an index whose cluster
contains the `r`-ball of the vertex. -/
noncomputable def centerOf (A : SimpleGraph (Fin n)) (r : ℕ) (v : Fin n) : Fin n :=
  Classical.choose ((isNeighborhoodCover_clusterOf A r).ball_subset v)

/-- The assignment covers: the ball of a vertex lies in the cluster of
its center. -/
theorem ball_subset_clusterOf (A : SimpleGraph (Fin n)) (r : ℕ) (v : Fin n) :
    ball A r v ⊆ clusterOf A r (centerOf A r v) :=
  Classical.choose_spec ((isNeighborhoodCover_clusterOf A r).ball_subset v)

/-- Splitter has a legal batch at Connector's move `u` with which he
wins the remaining `b` rounds. This is the right disjunct of
`Lax3Proofs.SplitterBasics.splitterWins_succ_iff` at `u`, named so that
the recursion can branch on it. -/
def HasBatch (mb r b : ℕ) (A : SimpleGraph (Fin n)) (u : Fin n) : Prop :=
  ∃ W : Set (Fin n), W ⊆ ball A r u ∧ W.ncard ≤ mb ∧
    SplitterWins mb r b (deleteVerts (deleteVerts A (ball A r u)ᶜ) W)

end Step

/-! ### The extended palettes

Relativization adds one color, the cluster itself. Isolation adds one
color per (batch vertex, capped distance) and one per (color, capped
distance); the three families are packed into `Fin` by `Fin.castAdd` /
`Fin.natAdd` and `finProdFinEquiv`, and the three slot equations below
are what `Lax3Proofs.Isolate.sat_iso` asks for.
-/

section Palette

variable {n : ℕ}

/-- The relativized coloring: the cluster `X` as the marker color at the
last index, the old colors intersected with it. -/
noncomputable def relColoring {L : ℕ} (col : Coloring n L) (X : Set (Fin n)) :
    Coloring n (L + 1) :=
  Fin.lastCases X (fun c => col c ∩ X)

/-- The marker slot holds the cluster. -/
theorem relColoring_last {L : ℕ} (col : Coloring n L) (X : Set (Fin n)) :
    relColoring col X (Fin.last L) = X := by
  simp [relColoring]

/-- An old slot holds its color, intersected with the cluster. -/
theorem relColoring_castSucc {L : ℕ} (col : Coloring n L) (X : Set (Fin n)) (c : Fin L) :
    relColoring col X (Fin.castSucc c) = col c ∩ X := by
  simp [relColoring]

/-- The palette the isolation step extends to: the incoming palette,
one slot per batch vertex and capped distance, and one slot per color
and capped distance. -/
abbrev isoPalette (L' m' cap : ℕ) : ℕ := L' + (m' * (cap + 1) + L' * (cap + 1))

/-- Where an incoming color sits in the extended palette. -/
def slotOld {L' m' cap : ℕ} (c : Fin L') : Fin (isoPalette L' m' cap) :=
  Fin.castAdd _ c

/-- Where the distance profile of the batch vertex `j` at radius `a`
sits. -/
def slotPd {L' m' cap : ℕ} (j : Fin m') (a : Fin (cap + 1)) : Fin (isoPalette L' m' cap) :=
  Fin.natAdd _ (Fin.castAdd _ (finProdFinEquiv (j, a)))

/-- Where the distance profile of the color class `c` at radius `b`
sits. -/
def slotPu {L' m' cap : ℕ} (c : Fin L') (b : Fin (cap + 1)) : Fin (isoPalette L' m' cap) :=
  Fin.natAdd _ (Fin.natAdd _ (finProdFinEquiv (c, b)))

/-- The coloring of the isolation step: the incoming colors in the old
block, the batch distance profiles and the color-distance profiles in
the two new blocks. All distances are measured in the arena `A` being
isolated. -/
noncomputable def isoColoring {L' m' cap : ℕ} (A : SimpleGraph (Fin n))
    (col : Coloring n L') (w : Fin m' → Fin n) : Coloring n (isoPalette L' m' cap) :=
  Fin.addCases col
    (Fin.addCases
      (fun i => {x | WithinDist A ((finProdFinEquiv.symm i).2 : ℕ) x
        (w (finProdFinEquiv.symm i).1)})
      (fun i => {x | ∃ y ∈ col (finProdFinEquiv.symm i).1,
        WithinDist A ((finProdFinEquiv.symm i).2 : ℕ) x y}))

variable {L' m' cap : ℕ} {A : SimpleGraph (Fin n)} {col : Coloring n L'} {w : Fin m' → Fin n}

/-- The old-color slot equation. -/
theorem isoColoring_slotOld (c : Fin L') :
    isoColoring (cap := cap) A col w (slotOld c) = col c := by
  simp only [isoColoring, slotOld, Fin.addCases_left]

/-- The batch-profile slot equation. -/
theorem isoColoring_slotPd (j : Fin m') (a : Fin (cap + 1)) :
    isoColoring (cap := cap) A col w (slotPd j a) = {x | WithinDist A (a : ℕ) x (w j)} := by
  simp only [isoColoring, slotPd, Fin.addCases_right, Fin.addCases_left,
    Equiv.symm_apply_apply]

/-- The color-profile slot equation. -/
theorem isoColoring_slotPu (c : Fin L') (b : Fin (cap + 1)) :
    isoColoring (cap := cap) A col w (slotPu c b) =
      {x | ∃ y ∈ col c, WithinDist A (b : ℕ) x y} := by
  simp only [isoColoring, slotPu, Fin.addCases_right, Equiv.symm_apply_apply]

end Palette

/-! ### The three objects the cluster step recurses on -/

section StepObjects

variable {n : ℕ}

/-- The arena of a cluster step: restrict to the cluster, then isolate
the batch. -/
noncomputable def stepArena (A : SimpleGraph (Fin n)) (X W : Set (Fin n)) :
    SimpleGraph (Fin n) :=
  deleteVerts (deleteVerts A Xᶜ) (Set.range (enumOf W))

/-- The coloring of a cluster step: relativize to the cluster, then
record the profiles of the batch and of the colors. -/
noncomputable def stepColoring (cap : ℕ) {L : ℕ} (A : SimpleGraph (Fin n))
    (col : Coloring n L) (X W : Set (Fin n)) :
    Coloring n (isoPalette (L + 1) W.ncard cap) :=
  isoColoring (cap := cap) (deleteVerts A Xᶜ) (relColoring col X) (enumOf W)

/-- The formula of a cluster step: relativize to the cluster, then
translate through the isolation. -/
noncomputable def stepFormula (cap : ℕ) {L : ℕ} (W : Set (Fin n)) (β : DistFO L 1) :
    DistFO (isoPalette (L + 1) W.ncard cap) 1 :=
  Lax3Proofs.Isolate.iso (@slotOld (L + 1) W.ncard cap) (@slotPd (L + 1) W.ncard cap)
    (@slotPu (L + 1) W.ncard cap) (Lax3Proofs.Relativize.rel Fin.castSucc (Fin.last L) β)

end StepObjects

/-! ### The recursion -/

section Recursion

open Classical in
mutual

/-- **The local tables.** `tablesLocal b A col β v` decides the local
one-variable formula `β` at `v` in the arena `A` with `b` rounds of the
splitter game left.

At budget zero, and at any budget on an edgeless arena, the value *is*
satisfaction: a winning position at budget zero is edgeless, and on an
edgeless arena satisfaction is a lookup in the color rows. Turning that
lookup into a machine computation is deliberately deferred to the RAM
phases; the descent is complete without it.

Otherwise the cluster step runs: cover, batch, relativize, isolate,
recurse into the non-local phase with one round fewer. If Splitter has
no batch at the chosen center the value is `False` — junk, unreachable
whenever the arena is a winning position. -/
noncomputable def tablesLocal (q_top cap mb b : ℕ) {n : ℕ} (A : SimpleGraph (Fin n)) {L : ℕ}
    (col : Coloring n L) (β : DistFO L 1) (v : Fin n) : Prop :=
  match b with
  | 0 => Sat A col (fun _ => v) β
  | b + 1 =>
      if A = ⊥ then Sat A col (fun _ => v) β
      else if hW : HasBatch mb (2 * cap) b A (centerOf A cap v) then
        tablesNonlocal q_top cap mb b
          (stepArena A (clusterOf A cap (centerOf A cap v)) (Classical.choose hW))
          (stepColoring cap A col (clusterOf A cap (centerOf A cap v)) (Classical.choose hW))
          (stepFormula cap (Classical.choose hW) β) v
      else False
termination_by (b, 0)

/-- **The non-local tables.** `tablesNonlocal b A col ψ v` decides an
arbitrary one-variable formula `ψ` at `v` in `A`, by the locality
theorem: `ψ` becomes a boolean combination of local formulas — read off
the local tables at the same arena and budget — and scatter sentences,
each of which is evaluated inline by running the greedy scatter process
of `Lax3.ScatterSentences.greedyChoice` over the local table of its own
one-variable formula.

That inline evaluation is the collapse of the sentence phase: a scatter
sentence is a *sentence*, so nothing about it needs a further descent —
only the local table of its formula, which the same budget already
provides. If `ψ` carries no distance rank the recursion may use, the
value is `False`; the correctness theorem supplies the rank. -/
noncomputable def tablesNonlocal (q_top cap mb b : ℕ) {n : ℕ} (A : SimpleGraph (Fin n)) {L : ℕ}
    (col : Coloring n L) (ψ : DistFO L 1) (v : Fin n) : Prop :=
  if h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ then
    (Classical.choose
        (Assembly.locality greedyChoice ψ (Classical.choose_spec h).2)).eval
      (Sum.elim (fun β => tablesLocal q_top cap mb b A col β v)
        (fun σ => σ.t ≤ greedyChoice.size A σ.r
          {a | tablesLocal q_top cap mb b A col σ.β a}))
  else False
termination_by (b, 1)

end

end Recursion

/-! ### Correctness

The two theorems are proved together: `tablesNonlocal_iff_sat` is
uniform in the budget, assuming only that the local tables at that
budget are correct, and `tablesLocal_iff_sat` is the induction on the
budget that supplies that assumption.
-/

section Correctness

/-- The local tables at a given budget, arena and coloring are correct
on every formula the rank invariant admits. This is the hypothesis
`tablesNonlocal_iff_sat` runs on and the conclusion the budget induction
of `tablesLocal_iff_sat` establishes. -/
def LocalCorrect (q_top cap mb b : ℕ) {n : ℕ} (A : SimpleGraph (Fin n)) {L : ℕ}
    (col : Coloring n L) : Prop :=
  ∀ (β : DistFO L 1) (v : Fin n) (k' q' : ℕ), IsLocal β → 1 ≤ k' → DRank k' q' β →
    k' + q' ≤ q_top → (tablesLocal q_top cap mb b A col β v ↔ Sat A col (fun _ => v) β)

variable {q_top cap mb : ℕ}

/-- **The non-local tables are correct**, given the local tables at the
same budget. The rank is first normalized to arity one, which is what
the locality theorem wants and what the recursion's own case
distinction tests; from there the argument is entirely about the data
the function chose — its quantifier rank, its boolean combination — and
`Lax3Proofs.BCAlgebra.eval_congr` replaces each atom's table by its
truth value: a local atom by the assumed local correctness, a scatter
atom by the same correctness applied pointwise inside the set the greedy
process runs on. -/
theorem tablesNonlocal_iff_sat {b n : ℕ} {A : SimpleGraph (Fin n)} {L : ℕ}
    {col : Coloring n L} (hcorr : LocalCorrect q_top cap mb b A col) {ψ : DistFO L 1}
    {k' q' : ℕ} (hk : 1 ≤ k') (hq : DRank k' q' ψ) (hsum : k' + q' ≤ q_top) (v : Fin n) :
    tablesNonlocal q_top cap mb b A col ψ v ↔ Sat A col (fun _ => v) ψ := by
  obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
  have hcond : ∃ q₀ : ℕ, q₀ + 1 ≤ q_top ∧ DRank 1 q₀ ψ :=
    ⟨j + q', by omega, drank_one_of_drank hq⟩
  rw [tablesNonlocal, dif_pos hcond]
  obtain ⟨hq₀le, -⟩ := Classical.choose_spec hcond
  obtain ⟨hbl, hbs, hbeq⟩ :=
    Classical.choose_spec (Assembly.locality greedyChoice ψ (Classical.choose_spec hcond).2)
  rw [hbeq n A col (fun _ => v)]
  refine BCAlgebra.eval_congr _ ?_
  rintro (γ | σ) hmem
  · simp only [Sum.elim_inl]
    obtain ⟨hγloc, hγrank⟩ := hbl γ hmem
    exact hcorr γ v 1 _ hγloc le_rfl hγrank (by omega)
  · simp only [Sum.elim_inr]
    rw [scatterSat_iff]
    obtain ⟨-, i, hi1, hiq, hβloc, hβrank, -, -⟩ := scatterSentence_drank_iff.mp (hbs σ hmem)
    have hset : {a : Fin n | tablesLocal q_top cap mb b A col σ.β a} =
        {a : Fin n | Sat A col (fun _ => a) σ.β} :=
      Set.ext fun a => hcorr σ.β a (1 + i) _ hβloc (by omega) hβrank (by omega)
    rw [hset]

/-- **The local tables are correct.** Induction on the round budget.

At budget zero, and on an edgeless arena, the value is satisfaction by
definition. Otherwise the arena is a winning position with a round
left, so Splitter has the batch the recursion's case distinction asks
for, and the five links of the cluster step close the chain:

* semantic locality (`Lax3Proofs.SemLocal`) moves truth inside the
  cluster, since the cover contains the `cap`-ball of the vertex and
  every radius of the formula is under `cap`;
* the relativization rewrite (`Lax3Proofs.Relativize`) turns truth
  inside the cluster into truth over the restricted arena;
* the isolation rewrite (`Lax3Proofs.Isolate`) turns that into truth of
  the translated formula over the isolated arena;
* the isolated arena is a subgraph of the arena Splitter's move led to,
  so it is a winning position with one round fewer
  (`Lax3Proofs.SplitterMono`);
* the induction hypothesis, through `tablesNonlocal_iff_sat`, closes
  the recursion.

The rank is normalized one step down the antidiagonal before the radii
are read off, which is what makes both horizon bounds come out of
`Lax3Proofs.Horizon` alone. -/
theorem tablesLocal_iff_sat (hcap : cap = rhoMinus 0 q_top) (b : ℕ) :
    ∀ {n : ℕ} {A : SimpleGraph (Fin n)} {L : ℕ} (col : Coloring n L) (β : DistFO L 1)
      (v : Fin n) {k' q' : ℕ}, SplitterWins mb (2 * cap) b A → IsLocal β → 1 ≤ k' →
      DRank k' q' β → k' + q' ≤ q_top →
      (tablesLocal q_top cap mb b A col β v ↔ Sat A col (fun _ => v) β) := by
  induction b with
  | zero =>
    intro n A L col β v k' q' _ _ _ _ _
    rw [tablesLocal]
  | succ b ih =>
    intro n A L col β v k' q' hwin hloc hk hq hsum
    rw [tablesLocal]
    by_cases hbot : A = ⊥
    · rw [if_pos hbot]
    rw [if_neg hbot]
    -- Splitter's move at the center assigned to `v`.
    have hmove : ∀ u : Fin n, HasBatch mb (2 * cap) b A u := by
      rcases SplitterBasics.splitterWins_succ_iff.mp hwin with h | h
      · exact absurd h hbot
      · exact h
    have hW := hmove (centerOf A cap v)
    rw [dif_pos hW]
    -- The normalized rank.
    obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
    have hqn : DRank j (q' + 1) β := DRank.antidiagonal hq
    have hm : rhoMinus j (q' + 1) ≤ cap := hcap ▸ rhoMinus_le_cap (by omega)
    have hp : rhoPlus (j + 1) q' ≤ cap := hcap ▸ rhoPlus_le_cap (by omega)
    have hcap1 : 1 ≤ cap := Lax3Proofs.Isolate.one_le_cap_of_rhoMinus_le hm
    -- Names for the data the recursion chose.
    set u := centerOf A cap v with hu
    set X := clusterOf A cap u with hX
    set W := Classical.choose hW with hWdef
    obtain ⟨hWball, hWcard, hWwin⟩ := Classical.choose_spec hW
    -- The isolated arena is a winning position with one round fewer.
    have hXball : X ⊆ ball A (2 * cap) u := (isNeighborhoodCover_clusterOf A cap).subset_ball u
    have hle : stepArena A X W ≤ deleteVerts (deleteVerts A (ball A (2 * cap) u)ᶜ) W := by
      rw [stepArena, range_enumOf]
      exact deleteVerts_mono_graph (deleteVerts_mono_set (Set.compl_subset_compl.mpr hXball))
    have hwin₂ : SplitterWins mb (2 * cap) b (stepArena A X W) :=
      SplitterMono.splitterWins_anti hle hWwin
    -- The recursion's own step, through the non-local phase.
    have hstep : tablesNonlocal q_top cap mb b (stepArena A X W)
        (stepColoring cap A col X W) (stepFormula cap W β) v ↔
        Sat (stepArena A X W) (stepColoring cap A col X W) (fun _ => v)
          (stepFormula cap W β) := by
      refine tablesNonlocal_iff_sat (k' := j + 1) (q' := q') ?_ (by omega) ?_ (by omega) v
      · intro γ v' k'' q'' hγloc hk'' hγrank hsum''
        exact ih _ _ _ hwin₂ hγloc hk'' hγrank hsum''
      · exact Lax3Proofs.Isolate.drank_iso
          (Lax3Proofs.Relativize.drank_rel Fin.castSucc (Fin.last L) hq)
    rw [hstep]
    -- The isolation rewrite.
    have hiso : Sat (deleteVerts A Xᶜ) (relColoring col X) (fun _ => v)
        (Lax3Proofs.Relativize.rel Fin.castSucc (Fin.last L) β) ↔
        Sat (stepArena A X W) (stepColoring cap A col X W) (fun _ => v)
          (stepFormula cap W β) :=
      Lax3Proofs.Isolate.sat_iso (fun c => isoColoring_slotOld c)
        (fun jj a => isoColoring_slotPd jj a) (fun c b' => isoColoring_slotPu c b') hcap1 _
        (Lax3Proofs.Isolate.radiiLe_of_drank
          (Lax3Proofs.Relativize.drank_rel Fin.castSucc (Fin.last L) hqn) hm hp)
        (fun _ => v)
    rw [← hiso]
    -- The relativization rewrite.
    rw [Lax3Proofs.Relativize.sat_rel (relColoring_castSucc col X) (relColoring_last col X)]
    -- Semantic locality.
    exact (SemLocal.sat_iff_satWithin_of_ball_subset' A col hloc hqn (fun _ => v)
      (fun _ => (ball_mono_radius A v hm).trans (ball_subset_clusterOf A cap v))).symm

/-- **The non-local tables are correct at every budget**, on every arena
Splitter wins within that budget. The local-correctness hypothesis of
`tablesNonlocal_iff_sat` is exactly `tablesLocal_iff_sat`, so the two
phases are correct under the same assumptions; this is the form the
recursion driver of the RAM phases consumes. -/
theorem tablesNonlocal_iff_sat_of_splitterWins (hcap : cap = rhoMinus 0 q_top) (b : ℕ)
    {n : ℕ} {A : SimpleGraph (Fin n)} {L : ℕ} (col : Coloring n L) (ψ : DistFO L 1)
    (v : Fin n) {k' q' : ℕ} (hwin : SplitterWins mb (2 * cap) b A) (hk : 1 ≤ k')
    (hq : DRank k' q' ψ) (hsum : k' + q' ≤ q_top) :
    tablesNonlocal q_top cap mb b A col ψ v ↔ Sat A col (fun _ => v) ψ :=
  tablesNonlocal_iff_sat
    (fun γ v' _ _ hγloc hk'' hγrank hsum'' =>
      tablesLocal_iff_sat hcap b col γ v' hwin hγloc hk'' hγrank hsum'')
    hk hq hsum v

end Correctness

/-! ### The sentence evaluator -/

section Sentence

open Classical in
/-- **The sentence evaluator.** Same shape as the non-local tables at
arity zero: the locality theorem turns the sentence into a boolean
combination of local sentences — decided outright by
`localSentenceEval`, no arena needed — and scatter sentences, each
evaluated inline by the greedy process over the local table of its
one-variable formula. There is no recursion at all at this level. -/
noncomputable def sentenceEval (q_top cap mb b : ℕ) {n : ℕ} (A : SimpleGraph (Fin n)) {L : ℕ}
    (col : Coloring n L) (φ : DistFO L 0) : Prop :=
  if h : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ then
    (Classical.choose
        (Assembly.locality greedyChoice φ (Classical.choose_spec h).2)).eval
      (Sum.elim localSentenceEval
        (fun σ => σ.t ≤ greedyChoice.size A σ.r
          {a | tablesLocal q_top cap mb b A col σ.β a}))
  else False

variable {q_top cap mb : ℕ}

/-- **The sentence evaluator is correct** on every sentence of distance
rank `(0, q_top)`, at every arena Splitter wins in `b` rounds. The
argument is `tablesNonlocal_iff_sat` at arity zero: local atoms go
through the sentence base, scatter atoms through the local tables, whose
correctness is `tablesLocal_iff_sat`. -/
theorem sentenceEval_iff_sat (hcap : cap = rhoMinus 0 q_top) {b n : ℕ}
    {A : SimpleGraph (Fin n)} (hwin : SplitterWins mb (2 * cap) b A) {L : ℕ}
    (col : Coloring n L) (φ : DistFO L 0) (hq : DRank 0 q_top φ) :
    sentenceEval q_top cap mb b A col φ ↔ Sat A col Fin.elim0 φ := by
  have hcond : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ := ⟨q_top, le_rfl, hq⟩
  rw [sentenceEval, dif_pos hcond]
  obtain ⟨hq₀le, -⟩ := Classical.choose_spec hcond
  obtain ⟨hbl, hbs, hbeq⟩ :=
    Classical.choose_spec (Assembly.locality greedyChoice φ (Classical.choose_spec hcond).2)
  rw [hbeq n A col Fin.elim0]
  refine BCAlgebra.eval_congr _ ?_
  rintro (γ | σ) hmem
  · simp only [Sum.elim_inl]
    exact localSentenceEval_iff γ (hbl γ hmem).1
  · simp only [Sum.elim_inr]
    rw [scatterSat_iff]
    obtain ⟨-, i, hi1, hiq, hβloc, hβrank, -, -⟩ := scatterSentence_drank_iff.mp (hbs σ hmem)
    have hset : {a : Fin n | tablesLocal q_top cap mb b A col σ.β a} =
        {a : Fin n | Sat A col (fun _ => a) σ.β} :=
      Set.ext fun a =>
        tablesLocal_iff_sat hcap b col σ.β a hwin hβloc (by omega) hβrank (by omega)
    rw [hset]

end Sentence

/-! ### The checkpoint -/

/--
**The math-core checkpoint of the campaign: the evaluator decides every
first-order sentence on every member of a nowhere dense class.**

For every nowhere dense class and every plain first-order sentence there
are a round bound `ℓ` and a batch bound `mb` — the splitter-game
parameters of the class at radius `2 · ρ⁻(0, qr φ)` — such that the
evaluator, run at top rank `qr φ`, cap `ρ⁻(0, qr φ)` and those bounds,
returns exactly the truth value of the sentence in every member of the
class.

This is the exit criterion of the abstract-algorithm phase. It carries
no time bound: the recursion is the one the word-RAM program will
execute, and its cost accounting — the neighborhood-cover degree, the
per-arena bounded-depth work, the `n^(1+ε)` sum over the recursion tree
— belongs to the RAM phases, as does the algorithmic base case that
replaces `Sat` on an edgeless arena.

The splitter bound comes from the *proved*
`Lax3Proofs.SplitterWin.splitterWins_of_nowhereDense`, not from the
concept axiom, so the only assumption inherited beyond the kernel is
Lax12's uniform quasi-wideness of nowhere dense classes. -/
theorem evaluator_decides (C : GraphClass) (hC : NowhereDense C) (φ : Lax3.FirstOrder.FO 0) :
    ∃ ℓ mb : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      (sentenceEval (Lax3.FirstOrder.rank φ) (rhoMinus 0 (Lax3.FirstOrder.rank φ)) mb ℓ
          G (Fin.elim0 : Coloring n 0) (Reduction.toDistFO φ)
        ↔ Lax3.FirstOrder.Sat G Fin.elim0 φ) := by
  obtain ⟨ℓ, mb, hsplit⟩ := SplitterWin.splitterWins_of_nowhereDense C hC
    (2 * rhoMinus 0 (Lax3.FirstOrder.rank φ))
  refine ⟨ℓ, mb, fun n G hG => ?_⟩
  rw [sentenceEval_iff_sat rfl (hsplit n G hG) _ _ (Reduction.drank_toDistFO φ le_rfl)]
  exact Reduction.sat_toDistFO G _ Fin.elim0 φ

end Lax3Proofs.Evaluator
