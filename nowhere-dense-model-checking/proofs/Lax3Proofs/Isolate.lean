import Lax3Proofs.SyntaxLemmas
import Lax3Proofs.WalkDistance

/-!
The *isolation rewrite*: a purely syntactic translation `iso` of
distance logic that trades the edges incident to a batch of vertices for
recorded distance colors, so that truth over an arena is truth of the
translated formula over the isolated arena, at **every** tuple and with
no side condition on where the tuple sits.

# The setting

The arena is a colored graph `(A, col)` on `Fin n`. The batch is an
enumeration `w : Fin m' → Fin n`; the batch *set* is `Set.range w`, and
the isolated arena is `deleteVerts A (Set.range w)` — Lax12's isolation
move, which drops every edge incident to the batch and keeps the
carrier, so vertices persist and equality needs no readout at all.

What the isolated arena loses is exactly the metric information carried
by walks through the batch. That information is recorded as colors of an
extended palette `Fin L'`, addressed by three slot maps that the
translation takes as parameters:

* `old c` — where the old color `c` now lives;
* `pd j a` — the *cumulative profile* slot, holding `{v | dist(v, w j) ≤ a}`;
* `pu c b` — the *cumulative color-distance* slot, holding
  `{v | ∃ y ∈ col c, dist(v, y) ≤ b}`.

Both profile families are capped: their distance index runs over
`Fin (cap + 1)`, and the translation is correct on the formulas whose
radii all stay below `cap`, which is the predicate `RadiiLe`. No
injectivity and no disjointness is assumed anywhere — the correctness
lemma only assumes that the new coloring interprets the three slot
families as just described, so a consumer is free to pack them into
`Fin L'` however it likes.

# The translation, atom by atom

Equality and color atoms are unchanged (up to `old`). The remaining
atoms each get a disjunction, written with the derived connectives `or`
and `bigOr` of this file, since `DistFO` has no primitive disjunction:

* `adj i j` becomes "adjacent in the isolated arena, or distinct and
  joined through a batch vertex at profile distances `0` and `1`". The
  distinctness conjunct is load-bearing: without it the pair
  `(w j, w j)` would be accepted by the `0`/`0` reading of the profile
  slots.
* `distLe d i j` becomes "within `d` in the isolated arena, or joined
  through a batch vertex by two legs of recorded lengths adding up to at
  most `d`".
* `distColorLt r c i` is answered outright by a single color atom: the
  slot `pu c (r - 1)` already holds the vertices at distance less than
  `r` from the color class *in the original arena*, so no disjunction
  and no metric reasoning is needed. At `r = 0` the atom is
  unsatisfiable and the translation is falsity.

Connectives are structural, and so is unrestricted quantification.

# The metric kernel

Everything metric reduces to
`Lax3Proofs.WalkDistance.withinDist_deleteVerts_or_through`: a walk of
length at most `d` either avoids the batch, and then survives isolation
whole, or it meets the batch and splits there into two legs whose
lengths add up to at most `d`. Packaged here as
`withinDist_iff_deleteVerts_or_through`, an equivalence between being
within `d` in the arena and the disjunction "within `d` after isolation,
or `Through` the batch". The converse direction is the triangle
inequality plus the fact that isolation only removes edges.

# As-built deviation from design record §(a): the two-case local quantifier

The design record translates a local quantifier by turning its guard
into distance atoms inside the body and degrading the quantifier to an
unrestricted one, claiming that distance rank is preserved. **It is
not.** A guard of a formula of distance rank `(k', q + 1)` is allowed
radius up to `ρ⁺(k' + 1, q)`, while a binary distance atom sitting
inside that quantifier's body — which has rank `(k' + 1, q)` — is
allowed only `ρ⁻(k' + 1, q)`, and `ρ⁻(k' + 1, q) < ρ⁺(k' + 1, q)`. The
guard radius therefore does not fit into the body, and the rewriting
loses the rank the whole locality schedule is built on.

The translation here avoids the gap by splitting into two cases:

    exL r g φ  ↦  exL r g (iso φ)  ∨  exU (isoGuard r g ∧ iso φ)

Case 1 keeps a genuine local quantifier at the *same* radius `r`, so its
`DRank.exL` side condition is the input's unchanged. Case 2 is an
unrestricted quantifier whose guard `isoGuard` is built from **color
atoms only** — the profile slots — and color atoms carry every distance
rank, so `DRank.exU` needs nothing beyond the body's rank. Both cases
preserve distance rank exactly, and their disjunction is the intended
meaning: a witness guarded within `r` of the guard set is either
guarded within `r` *after* isolation, or reached through a batch vertex,
which is what the profile colors record. The empty guard set needs no
special treatment: it makes the source quantifier unsatisfiable and the
case-2 guard an empty disjunction, that is falsity.

Three smaller as-built notes. First, `sat_iso` carries the hypothesis
`1 ≤ cap`: the adjacency case reads the profile slot at distance `1`,
which does not exist when `cap = 0`, and no translation of an adjacency
atom can be correct when the recorded profiles see distance `0` only.
Every rank-driven instantiation supplies it for free, see
`one_le_cap_of_rhoMinus_le`. Second, out-of-range distance indices are
*clamped* rather than sent to falsity (`profIdx`); which of the two is
chosen is immaterial, since `RadiiLe cap` keeps every index in range at
every place the correctness lemma looks. Third, the guard set of a local
quantifier is enumerated by filtering `List.finRange`, not by
`Finset.toList`, which is noncomputable — the translation is meant to be
run by the evaluator, so `iso` is kept computable.

# Formalization notes

No tactic here is handed a concept-side definition: `Sat`, `DistFO`,
`DRank`, `WithinDist`, `deleteVerts`, `rhoMinus` and `rhoPlus` are taken
apart through the clause lemmas of `Lax3Proofs.SyntaxLemmas`, through
the walk lemmas of `Lax3Proofs.WalkDistance`, through the inequality kit
of `Lax3Proofs.Horizon`, or definitionally by `exact`. The definitions
introduced here — `or`, `bigOr`, `falsum`, `RadiiLe`, `iso` and its
pieces — are of course unfolded freely, and their `rfl`-lemmas are
recorded in this namespace.

`radiiLe_of_drank` reads the cap off a rank derivation. Its two
hypotheses are the two horizons of the *outer* rank: `ρ⁻(k', q)` bounds
the distance atoms and `ρ⁺(k' + 1, q - 1)` bounds the guards — the
latter because `DRank.exL` concludes rank `(k', q₀ + 1)` from a guard
bound at `q₀`. The induction descends through both, and needs only the
antidiagonal monotonicities already in `Lax3Proofs.Horizon`.
-/

namespace Lax3Proofs.Isolate

open Lax3.ColoredGraphs Lax3.DistFO
open Lax3Proofs.Horizon Lax3Proofs.SyntaxLemmas Lax3Proofs.WalkDistance
open Lax12.UniformQuasiWideness

/-! ### Derived connectives

`DistFO` has negation and conjunction but no disjunction, and no
constant for falsity. Both are written here, falsity as a refuted
equality on a variable that the use site supplies — every use site of
this file has one.
-/

section Connectives

variable {L k : ℕ}

/-- Disjunction, written with negation and conjunction. -/
def or (φ ψ : DistFO L k) : DistFO L k := .not (.and (.not φ) (.not ψ))

/-- Falsity on a nonempty context, written at the variable `i`. -/
def falsum (i : Fin k) : DistFO L k := .not (.eq i i)

/-- A finite disjunction over a list, with an explicit formula for the
empty case — passing falsity in avoids inventing a variable here. -/
def bigOr (fls : DistFO L k) : List (DistFO L k) → DistFO L k
  | [] => fls
  | φ :: l => or φ (bigOr fls l)

/-- The definition of `or`, for rewriting. -/
theorem or_def (φ ψ : DistFO L k) : or φ ψ = .not (.and (.not φ) (.not ψ)) := rfl

/-- The definition of `falsum`, for rewriting. -/
theorem falsum_def (i : Fin k) : (falsum i : DistFO L k) = .not (.eq i i) := rfl

/-- The empty disjunction is the supplied falsity. -/
theorem bigOr_nil (fls : DistFO L k) : bigOr fls ([] : List (DistFO L k)) = fls := rfl

/-- A nonempty disjunction peels off its head. -/
theorem bigOr_cons (fls φ : DistFO L k) (l : List (DistFO L k)) :
    bigOr fls (φ :: l) = or φ (bigOr fls l) := rfl

end Connectives

/-! ### Radii below a cap

The translation records distances only up to `cap`, so it is correct
exactly on the formulas whose radii — those of the two distance atoms
and those of the local quantifiers — stay below that bound.
-/

/-- `RadiiLe cap φ` says that every radius occurring in `φ` is at most
`cap`: those of the binary and unary distance atoms and those of the
local quantifiers. -/
def RadiiLe {L : ℕ} (cap : ℕ) : {k : ℕ} → DistFO L k → Prop
  | _, .adj _ _ => True
  | _, .eq _ _ => True
  | _, .color _ _ => True
  | _, .distLe r _ _ => r ≤ cap
  | _, .distColorLt r _ _ => r ≤ cap
  | _, .not φ => RadiiLe cap φ
  | _, .and φ ψ => RadiiLe cap φ ∧ RadiiLe cap ψ
  | _, .exU φ => RadiiLe cap φ
  | _, .exL r _ φ => r ≤ cap ∧ RadiiLe cap φ

section RadiiLeClauses

variable {L k cap : ℕ}

/-- An adjacency atom carries no radius. -/
theorem radiiLe_adj (i j : Fin k) : RadiiLe cap (.adj i j : DistFO L k) := trivial

/-- An equality atom carries no radius. -/
theorem radiiLe_eq (i j : Fin k) : RadiiLe cap (.eq i j : DistFO L k) := trivial

/-- A color atom carries no radius. -/
theorem radiiLe_color (c : Fin L) (i : Fin k) : RadiiLe cap (.color c i : DistFO L k) := trivial

/-- The radius condition at a binary distance atom. -/
theorem radiiLe_distLe (r : ℕ) (i j : Fin k) :
    RadiiLe cap (.distLe r i j : DistFO L k) ↔ r ≤ cap := Iff.rfl

/-- The radius condition at a unary distance atom. -/
theorem radiiLe_distColorLt (r : ℕ) (c : Fin L) (i : Fin k) :
    RadiiLe cap (.distColorLt r c i : DistFO L k) ↔ r ≤ cap := Iff.rfl

/-- The radius condition at a negation. -/
theorem radiiLe_not (φ : DistFO L k) : RadiiLe cap (.not φ) ↔ RadiiLe cap φ := Iff.rfl

/-- The radius condition at a conjunction. -/
theorem radiiLe_and (φ ψ : DistFO L k) :
    RadiiLe cap (.and φ ψ) ↔ RadiiLe cap φ ∧ RadiiLe cap ψ := Iff.rfl

/-- The radius condition at an unrestricted quantifier. -/
theorem radiiLe_exU (φ : DistFO L (k + 1)) : RadiiLe cap (.exU φ) ↔ RadiiLe cap φ := Iff.rfl

/-- The radius condition at a local quantifier: the guard radius counts
too. -/
theorem radiiLe_exL (r : ℕ) (g : Finset (Fin k)) (φ : DistFO L (k + 1)) :
    RadiiLe cap (.exL r g φ) ↔ r ≤ cap ∧ RadiiLe cap φ := Iff.rfl

/-- `RadiiLe` is closed under the derived disjunction. -/
theorem radiiLe_or {φ ψ : DistFO L k} (hφ : RadiiLe cap φ) (hψ : RadiiLe cap ψ) :
    RadiiLe cap (or φ ψ) := ⟨hφ, hψ⟩

/-- Falsity carries no radius. -/
theorem radiiLe_falsum (i : Fin k) : RadiiLe cap (falsum i : DistFO L k) := trivial

/-- `RadiiLe` is closed under finite disjunctions. -/
theorem radiiLe_bigOr {fls : DistFO L k} (hfls : RadiiLe cap fls) :
    ∀ l : List (DistFO L k), (∀ φ ∈ l, RadiiLe cap φ) → RadiiLe cap (bigOr fls l)
  | [], _ => hfls
  | φ :: l, hl =>
      radiiLe_or (hl φ (List.mem_cons_self ..))
        (radiiLe_bigOr hfls l fun ψ hψ => hl ψ (List.mem_cons_of_mem _ hψ))

end RadiiLeClauses

/-! ### Distance rank of the derived connectives -/

section DRankConnectives

variable {L k k' q : ℕ}

/-- The derived disjunction inherits the distance rank of its
disjuncts. -/
theorem drank_or {φ ψ : DistFO L k} (hφ : DRank k' q φ) (hψ : DRank k' q ψ) :
    DRank k' q (or φ ψ) := .not (.and (.not hφ) (.not hψ))

/-- Falsity has every distance rank. -/
theorem drank_falsum (i : Fin k) : DRank k' q (falsum i : DistFO L k) := .not (.eq i i)

/-- A finite disjunction of formulas of distance rank `(k', q)` has
distance rank `(k', q)`. -/
theorem drank_bigOr {fls : DistFO L k} (hfls : DRank k' q fls) :
    ∀ l : List (DistFO L k), (∀ φ ∈ l, DRank k' q φ) → DRank k' q (bigOr fls l)
  | [], _ => hfls
  | φ :: l, hl =>
      drank_or (hl φ (List.mem_cons_self ..))
        (drank_bigOr hfls l fun ψ hψ => hl ψ (List.mem_cons_of_mem _ hψ))

end DRankConnectives

/-! ### Satisfaction of the derived connectives -/

section SatConnectives

variable {L n k : ℕ} {G : SimpleGraph (Fin n)} {col : Coloring n L} {m : Fin k → Fin n}

/-- The derived disjunction is a disjunction. -/
theorem sat_or (φ ψ : DistFO L k) :
    Sat G col m (or φ ψ) ↔ Sat G col m φ ∨ Sat G col m ψ := by
  rw [or_def, sat_not, sat_and, sat_not, sat_not]
  tauto

/-- Falsity is false. -/
theorem sat_falsum (i : Fin k) : ¬ Sat G col m (falsum i : DistFO L k) := by
  rw [falsum_def, sat_not, sat_eq]
  exact fun h => h rfl

/-- A finite disjunction holds exactly when one of its disjuncts
does, provided the supplied empty case is false. -/
theorem sat_bigOr {fls : DistFO L k} (hfls : ¬ Sat G col m fls) :
    ∀ l : List (DistFO L k), Sat G col m (bigOr fls l) ↔ ∃ φ ∈ l, Sat G col m φ
  | [] => by simpa [bigOr_nil] using hfls
  | φ :: l => by simp [bigOr_cons, sat_or, sat_bigOr hfls l]

/-- The form of `sat_bigOr` the translation uses, with falsity as the
empty case. -/
theorem sat_bigOr_falsum (i : Fin k) (l : List (DistFO L k)) :
    Sat G col m (bigOr (falsum i) l) ↔ ∃ φ ∈ l, Sat G col m φ :=
  sat_bigOr (sat_falsum i) l

end SatConnectives

/-! ### List plumbing -/

section ListPlumbing

variable {α β : Type*}

/-- Existential quantification over a mapped list. -/
private theorem exists_mem_map {l : List α} {f : α → β} {P : β → Prop} :
    (∃ b ∈ l.map f, P b) ↔ ∃ a ∈ l, P (f a) := by
  constructor
  · rintro ⟨b, hb, hP⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact ⟨a, ha, hP⟩
  · rintro ⟨a, ha, hP⟩
    exact ⟨f a, List.mem_map.mpr ⟨a, ha, rfl⟩, hP⟩

/-- Existential quantification over a flat-mapped list. -/
private theorem exists_mem_flatMap {l : List α} {f : α → List β} {P : β → Prop} :
    (∃ b ∈ l.flatMap f, P b) ↔ ∃ a ∈ l, ∃ b ∈ f a, P b := by
  constructor
  · rintro ⟨b, hb, hP⟩
    obtain ⟨a, ha, hb'⟩ := List.mem_flatMap.mp hb
    exact ⟨a, ha, b, hb', hP⟩
  · rintro ⟨a, ha, b, hb, hP⟩
    exact ⟨b, List.mem_flatMap.mpr ⟨a, ha, hb⟩, hP⟩

end ListPlumbing

/-! ### Profile slots and index enumeration

The recorded distances are indexed by `Fin (cap + 1)`. Three pieces of
plumbing: a total clamp turning a natural number into such an index,
correct on the numbers that are in range; the list of pairs of indices
whose sum is at most a given radius; and a computable enumeration of a
guard set.
-/

/-- The profile index of the distance `a`, clamped into range so that
the translation is a total function. -/
private def profIdx (cap a : ℕ) : Fin (cap + 1) := ⟨min a cap, by omega⟩

/-- The clamp is the identity on the distances that are in range. -/
private theorem profIdx_val {cap a : ℕ} (h : a ≤ cap) : (profIdx cap a : ℕ) = a := by
  show min a cap = a
  omega

/-- The guard set of a local quantifier as a list. `Finset.toList` is
noncomputable, and the translation is meant to be run. -/
private def guardList {k : ℕ} (g : Finset (Fin k)) : List (Fin k) :=
  (List.finRange k).filter fun i => decide (i ∈ g)

/-- The guard list lists the guard set. -/
private theorem mem_guardList {k : ℕ} {g : Finset (Fin k)} {i : Fin k} :
    i ∈ guardList g ↔ i ∈ g := by
  simp [guardList]

/-- The pairs of recorded distances that add up to at most `d`. -/
def distPairs (cap d : ℕ) : List (Fin (cap + 1) × Fin (cap + 1)) :=
  ((List.finRange (cap + 1)).flatMap fun a =>
      (List.finRange (cap + 1)).map fun b => (a, b)).filter
    fun p => decide ((p.1 : ℕ) + (p.2 : ℕ) ≤ d)

/-- The only property of `distPairs` anything needs. -/
theorem mem_distPairs {cap d : ℕ} {p : Fin (cap + 1) × Fin (cap + 1)} :
    p ∈ distPairs cap d ↔ (p.1 : ℕ) + (p.2 : ℕ) ≤ d := by
  constructor
  · intro h
    have := (List.mem_filter.mp h).2
    simpa using this
  · intro h
    refine List.mem_filter.mpr
      ⟨List.mem_flatMap.mpr ⟨p.1, List.mem_finRange _, ?_⟩, by simpa using h⟩
    exact List.mem_map.mpr ⟨p.2, List.mem_finRange _, rfl⟩

/-! ### The translation -/

section Translation

variable {L L' m' cap : ℕ}

/-- The disjuncts recording that two variables are joined through a
batch vertex, the two legs having recorded lengths adding up to at most
`d`. -/
def profileList (pd : Fin m' → Fin (cap + 1) → Fin L') {k : ℕ} (d : ℕ) (i j : Fin k) :
    List (DistFO L' k) :=
  (List.finRange m').flatMap fun j' =>
    (distPairs cap d).map fun p =>
      .and (.color (pd j' p.1) i) (.color (pd j' p.2) j)

/-- The disjunction of `profileList`. -/
def profileOr (pd : Fin m' → Fin (cap + 1) → Fin L') {k : ℕ} (d : ℕ) (i j : Fin k) :
    DistFO L' k :=
  bigOr (falsum i) (profileList pd d i j)

/-- The translation of an adjacency atom: adjacent after isolation, or
distinct and joined through a batch vertex at profile distances `0` and
`1`. The distinctness conjunct is what keeps the batch vertex itself
from being read as adjacent to itself. -/
def isoAdj (pd : Fin m' → Fin (cap + 1) → Fin L') {k : ℕ} (i j : Fin k) : DistFO L' k :=
  or (.adj i j)
    (.and (.not (.eq i j))
      (bigOr (falsum i) ((List.finRange m').map fun j' =>
        or (.and (.color (pd j' (profIdx cap 0)) i) (.color (pd j' (profIdx cap 1)) j))
          (.and (.color (pd j' (profIdx cap 1)) i) (.color (pd j' (profIdx cap 0)) j)))))

/-- The translation of a binary distance atom: within `d` after
isolation, or joined through a batch vertex. -/
def isoDistLe (pd : Fin m' → Fin (cap + 1) → Fin L') {k : ℕ} (d : ℕ) (i j : Fin k) :
    DistFO L' k :=
  or (.distLe d i j) (profileOr pd d i j)

/-- The translation of a unary distance atom: a single color atom,
since the recorded color-distance slot already answers it in the
original arena. A zero radius makes the atom unsatisfiable. -/
def isoDistColorLt (pu : Fin L → Fin (cap + 1) → Fin L') {k : ℕ} (r : ℕ) (c : Fin L)
    (i : Fin k) : DistFO L' k :=
  if 0 < r then .color (pu c (profIdx cap (r - 1))) i else falsum i

/-- The through-the-batch reading of the guard of a local quantifier,
as a formula on the extended context: the newly bound variable is joined
to some guard variable through a batch vertex. Only color atoms occur in
it, which is why it carries every distance rank. -/
def isoGuard (pd : Fin m' → Fin (cap + 1) → Fin L') {k : ℕ} (r : ℕ) (g : Finset (Fin k)) :
    DistFO L' (k + 1) :=
  bigOr (falsum (Fin.last k))
    ((guardList g).flatMap fun i => profileList pd r i.castSucc (Fin.last k))

/-- The isolation rewrite. `old`, `pd` and `pu` say where the old
colors, the cumulative distance profiles of the batch and the cumulative
color-distance profiles live in the extended palette. -/
def iso (old : Fin L → Fin L') (pd : Fin m' → Fin (cap + 1) → Fin L')
    (pu : Fin L → Fin (cap + 1) → Fin L') : {k : ℕ} → DistFO L k → DistFO L' k
  | _, .adj i j => isoAdj pd i j
  | _, .eq i j => .eq i j
  | _, .color c i => .color (old c) i
  | _, .distLe d i j => isoDistLe pd d i j
  | _, .distColorLt r c i => isoDistColorLt pu r c i
  | _, .not φ => .not (iso old pd pu φ)
  | _, .and φ ψ => .and (iso old pd pu φ) (iso old pd pu ψ)
  | _, .exU φ => .exU (iso old pd pu φ)
  | _, .exL r g φ =>
      or (.exL r g (iso old pd pu φ)) (.exU (.and (isoGuard pd r g) (iso old pd pu φ)))

variable (old : Fin L → Fin L') (pd : Fin m' → Fin (cap + 1) → Fin L')
  (pu : Fin L → Fin (cap + 1) → Fin L') {k : ℕ}

/-- The translation of an adjacency atom. -/
theorem iso_adj (i j : Fin k) :
    iso old pd pu (.adj i j : DistFO L k) = isoAdj pd i j := rfl

/-- Equality atoms are unchanged: isolation keeps the carrier. -/
theorem iso_eq (i j : Fin k) :
    iso old pd pu (.eq i j : DistFO L k) = .eq i j := rfl

/-- Color atoms only move to their new slot. -/
theorem iso_color (c : Fin L) (i : Fin k) :
    iso old pd pu (.color c i : DistFO L k) = .color (old c) i := rfl

/-- The translation of a binary distance atom. -/
theorem iso_distLe (d : ℕ) (i j : Fin k) :
    iso old pd pu (.distLe d i j : DistFO L k) = isoDistLe pd d i j := rfl

/-- The translation of a unary distance atom. -/
theorem iso_distColorLt (r : ℕ) (c : Fin L) (i : Fin k) :
    iso old pd pu (.distColorLt r c i : DistFO L k) = isoDistColorLt pu r c i := rfl

/-- The translation of a negation. -/
theorem iso_not (φ : DistFO L k) :
    iso old pd pu (.not φ) = .not (iso old pd pu φ) := rfl

/-- The translation of a conjunction. -/
theorem iso_and (φ ψ : DistFO L k) :
    iso old pd pu (.and φ ψ) = .and (iso old pd pu φ) (iso old pd pu ψ) := rfl

/-- The translation of an unrestricted quantifier. -/
theorem iso_exU (φ : DistFO L (k + 1)) :
    iso old pd pu (.exU φ) = .exU (iso old pd pu φ) := rfl

/-- The translation of a local quantifier: the two-case shape discussed
in the module docstring. -/
theorem iso_exL (r : ℕ) (g : Finset (Fin k)) (φ : DistFO L (k + 1)) :
    iso old pd pu (.exL r g φ) =
      or (.exL r g (iso old pd pu φ)) (.exU (.and (isoGuard pd r g) (iso old pd pu φ))) := rfl

end Translation

/-! ### The metric kernel -/

section Kernel

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- A walk of length zero has equal endpoints. -/
theorem eq_of_withinDist_zero (h : WithinDist G 0 u v) : u = v := by
  obtain ⟨p, hp⟩ := h
  cases p with
  | nil => rfl
  | cons h' q => rw [SimpleGraph.Walk.length_cons] at hp; omega

/-- Distinct vertices within distance one are adjacent. -/
theorem adj_of_withinDist_one (h : WithinDist G 1 u v) (hne : u ≠ v) : G.Adj u v := by
  obtain ⟨p, hp⟩ := h
  cases p with
  | nil => exact absurd rfl hne
  | cons h' q =>
    cases q with
    | nil => exact h'
    | cons _ _ =>
      rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons] at hp
      omega

end Kernel

section Through

variable {n m' : ℕ}

/-- Two vertices are joined *through the batch* within `d` when some
batch vertex splits the budget between them. This is what the recorded
profile colors can see. -/
def Through (A : SimpleGraph (Fin n)) (w : Fin m' → Fin n) (d : ℕ) (u v : Fin n) : Prop :=
  ∃ j : Fin m', ∃ a b : ℕ, a + b ≤ d ∧ WithinDist A a u (w j) ∧ WithinDist A b v (w j)

/-- The metric identity the isolation rewrite runs on: a distance bound
in the arena is either a distance bound in the isolated arena or a
detour through the batch. The forward direction is the walk
decomposition of `Lax3Proofs.WalkDistance`, the backward one the
triangle inequality together with the fact that isolation only removes
edges. -/
theorem withinDist_iff_deleteVerts_or_through (A : SimpleGraph (Fin n)) (w : Fin m' → Fin n)
    (d : ℕ) (u v : Fin n) :
    WithinDist A d u v ↔
      WithinDist (deleteVerts A (Set.range w)) d u v ∨ Through A w d u v := by
  constructor
  · intro h
    rcases withinDist_deleteVerts_or_through (Set.range w) h with h' | ⟨s, hs, d₁, d₂, hd, h₁, h₂⟩
    · exact Or.inl h'
    · obtain ⟨j, rfl⟩ := hs
      exact Or.inr ⟨j, d₁, d₂, hd, h₁, withinDist_symm h₂⟩
  · rintro (h | ⟨j, a, b, hab, h₁, h₂⟩)
    · exact withinDist_deleteVerts h
    · exact withinDist_mono_radius hab (withinDist_trans h₁ (withinDist_symm h₂))

end Through

/-! ### Correctness of the pieces -/

section Semantics

variable {L L' n m' cap : ℕ} {A : SimpleGraph (Fin n)} {col : Coloring n L}
  {col' : Coloring n L'} {w : Fin m' → Fin n} {pd : Fin m' → Fin (cap + 1) → Fin L'}
  {pu : Fin L → Fin (cap + 1) → Fin L'}

/-- The profile disjuncts say exactly that the two variables are joined
through the batch. -/
theorem sat_profileList (hpd : ∀ (j : Fin m') (a : Fin (cap + 1)),
      col' (pd j a) = {v | WithinDist A (a : ℕ) v (w j)})
    {k d : ℕ} (hd : d ≤ cap) (m : Fin k → Fin n) (i j : Fin k) :
    (∃ ψ ∈ profileList pd d i j, Sat (deleteVerts A (Set.range w)) col' m ψ) ↔
      Through A w d (m i) (m j) := by
  rw [profileList, exists_mem_flatMap]
  constructor
  · rintro ⟨j', -, ψ, hψ, hsat⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hψ
    rw [sat_and, sat_color, sat_color, hpd, hpd] at hsat
    exact ⟨j', p.1, p.2, mem_distPairs.mp hp, hsat.1, hsat.2⟩
  · rintro ⟨j', a, b, hab, h₁, h₂⟩
    refine ⟨j', List.mem_finRange _, _,
      List.mem_map.mpr ⟨(⟨a, by omega⟩, ⟨b, by omega⟩), mem_distPairs.mpr hab, rfl⟩, ?_⟩
    rw [sat_and, sat_color, sat_color, hpd, hpd]
    exact ⟨h₁, h₂⟩

/-- The profile disjunction says exactly that the two variables are
joined through the batch. -/
theorem sat_profileOr (hpd : ∀ (j : Fin m') (a : Fin (cap + 1)),
      col' (pd j a) = {v | WithinDist A (a : ℕ) v (w j)})
    {k d : ℕ} (hd : d ≤ cap) (m : Fin k → Fin n) (i j : Fin k) :
    Sat (deleteVerts A (Set.range w)) col' m (profileOr pd d i j) ↔
      Through A w d (m i) (m j) := by
  rw [profileOr, sat_bigOr_falsum, sat_profileList hpd hd]

/-- Correctness of the translated binary distance atom. -/
theorem sat_isoDistLe (hpd : ∀ (j : Fin m') (a : Fin (cap + 1)),
      col' (pd j a) = {v | WithinDist A (a : ℕ) v (w j)})
    {k d : ℕ} (hd : d ≤ cap) (m : Fin k → Fin n) (i j : Fin k) :
    Sat (deleteVerts A (Set.range w)) col' m (isoDistLe pd d i j) ↔
      WithinDist A d (m i) (m j) := by
  rw [isoDistLe, sat_or, sat_distLe, sat_profileOr hpd hd]
  exact (withinDist_iff_deleteVerts_or_through A w d (m i) (m j)).symm

/-- Correctness of the translated adjacency atom. The recorded profile
at distance `1` is what an edge incident to the batch degrades to. -/
theorem sat_isoAdj (hpd : ∀ (j : Fin m') (a : Fin (cap + 1)),
      col' (pd j a) = {v | WithinDist A (a : ℕ) v (w j)})
    (hcap : 1 ≤ cap) {k : ℕ} (m : Fin k → Fin n) (i j : Fin k) :
    Sat (deleteVerts A (Set.range w)) col' m (isoAdj pd i j) ↔ A.Adj (m i) (m j) := by
  have h0 : ∀ (j' : Fin m') (u : Fin n), u ∈ col' (pd j' (profIdx cap 0)) ↔ u = w j' := by
    intro j' u
    rw [hpd, Set.mem_setOf_eq, profIdx_val (Nat.zero_le cap)]
    exact ⟨eq_of_withinDist_zero, fun h => withinDist_of_eq A 0 h⟩
  have h1 : ∀ (j' : Fin m') (u : Fin n),
      u ∈ col' (pd j' (profIdx cap 1)) ↔ WithinDist A 1 u (w j') := by
    intro j' u
    rw [hpd, Set.mem_setOf_eq, profIdx_val hcap]
  rw [isoAdj, sat_or, sat_adj, sat_and, sat_not, sat_eq, sat_bigOr_falsum, exists_mem_map]
  simp only [List.mem_finRange, true_and, sat_or, sat_and, sat_color, h0, h1]
  constructor
  · rintro (h | ⟨hne, j', h | h⟩)
    · exact h.1
    · have hd : WithinDist A 1 (m j) (m i) := by rw [h.1]; exact h.2
      exact (adj_of_withinDist_one hd (Ne.symm hne)).symm
    · have hd : WithinDist A 1 (m i) (m j) := by rw [h.2]; exact h.1
      exact adj_of_withinDist_one hd hne
  · intro hadj
    by_cases hi : m i ∈ Set.range w
    · obtain ⟨j', hj'⟩ := hi
      refine Or.inr ⟨hadj.ne, j', Or.inl ⟨hj'.symm, ?_⟩⟩
      rw [hj']
      exact withinDist_of_adj hadj.symm
    · by_cases hj : m j ∈ Set.range w
      · obtain ⟨j', hj'⟩ := hj
        refine Or.inr ⟨hadj.ne, j', Or.inr ⟨?_, hj'.symm⟩⟩
        rw [hj']
        exact withinDist_of_adj hadj
      · exact Or.inl ⟨hadj, hi, hj⟩

/-- Correctness of the translated unary distance atom: the recorded
color-distance slot answers it outright. -/
theorem sat_isoDistColorLt (hpu : ∀ (c : Fin L) (b : Fin (cap + 1)),
      col' (pu c b) = {v | ∃ y ∈ col c, WithinDist A (b : ℕ) v y})
    {k r : ℕ} (hr : r ≤ cap) (m : Fin k → Fin n) (c : Fin L) (i : Fin k) :
    Sat (deleteVerts A (Set.range w)) col' m (isoDistColorLt pu r c i) ↔
      ∃ y ∈ col c, ∃ p : A.Walk (m i) y, p.length < r := by
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · rw [isoDistColorLt, if_neg (by omega)]
    constructor
    · intro h; exact absurd h (sat_falsum i)
    · rintro ⟨y, -, p, hp⟩
      exact absurd hp (Nat.not_lt_zero _)
  · rw [isoDistColorLt, if_pos hpos, sat_color, hpu, Set.mem_setOf_eq,
      profIdx_val (by omega)]
    refine exists_congr fun y => and_congr_right fun _ => ?_
    rw [withinDist_iff]
    exact exists_congr fun p => by omega

/-- Correctness of the through-the-batch guard. -/
theorem sat_isoGuard (hpd : ∀ (j : Fin m') (a : Fin (cap + 1)),
      col' (pd j a) = {v | WithinDist A (a : ℕ) v (w j)})
    {k r : ℕ} (hr : r ≤ cap) (m : Fin k → Fin n) (g : Finset (Fin k)) (v : Fin n) :
    Sat (deleteVerts A (Set.range w)) col' (Fin.snoc m v) (isoGuard pd r g) ↔
      ∃ i ∈ g, Through A w r (m i) v := by
  rw [isoGuard, sat_bigOr_falsum, exists_mem_flatMap]
  constructor
  · rintro ⟨i, hi, hψ⟩
    refine ⟨i, mem_guardList.mp hi, ?_⟩
    have h := (sat_profileList hpd hr (Fin.snoc m v) i.castSucc (Fin.last k)).mp hψ
    simpa using h
  · rintro ⟨i, hi, h⟩
    refine ⟨i, mem_guardList.mpr hi,
      (sat_profileList hpd hr (Fin.snoc m v) i.castSucc (Fin.last k)).mpr ?_⟩
    simpa using h

/-- The guard of a local quantifier, split by the metric kernel: a
witness guarded in the arena is guarded after isolation or reached
through the batch. -/
private theorem guard_split (r : ℕ) {k : ℕ} (m : Fin k → Fin n) (g : Finset (Fin k))
    (v : Fin n) :
    (∃ i ∈ g, WithinDist A r (m i) v) ↔
      (∃ i ∈ g, WithinDist (deleteVerts A (Set.range w)) r (m i) v) ∨
        (∃ i ∈ g, Through A w r (m i) v) := by
  constructor
  · rintro ⟨i, hi, h⟩
    rcases (withinDist_iff_deleteVerts_or_through A w r (m i) v).mp h with h' | h'
    · exact Or.inl ⟨i, hi, h'⟩
    · exact Or.inr ⟨i, hi, h'⟩
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · exact ⟨i, hi, (withinDist_iff_deleteVerts_or_through A w r (m i) v).mpr (Or.inl h)⟩
    · exact ⟨i, hi, (withinDist_iff_deleteVerts_or_through A w r (m i) v).mpr (Or.inr h)⟩

variable {old : Fin L → Fin L'}

private theorem sat_iso_aux (hold : ∀ c, col' (old c) = col c)
    (hpd : ∀ (j : Fin m') (a : Fin (cap + 1)),
      col' (pd j a) = {v | WithinDist A (a : ℕ) v (w j)})
    (hpu : ∀ (c : Fin L) (b : Fin (cap + 1)),
      col' (pu c b) = {v | ∃ y ∈ col c, WithinDist A (b : ℕ) v y})
    (hcap : 1 ≤ cap) :
    ∀ {k : ℕ} (φ : DistFO L k), RadiiLe cap φ → ∀ m : Fin k → Fin n,
      (Sat A col m φ ↔ Sat (deleteVerts A (Set.range w)) col' m (iso old pd pu φ)) := by
  intro k φ
  induction φ with
  | adj i j =>
    intro _ m
    rw [sat_adj, iso_adj, sat_isoAdj hpd hcap]
  | eq i j =>
    intro _ m
    rw [iso_eq, sat_eq, sat_eq]
  | color c i =>
    intro _ m
    rw [sat_color, iso_color, sat_color, hold]
  | distLe d i j =>
    intro hφ m
    rw [sat_distLe, iso_distLe, sat_isoDistLe hpd ((radiiLe_distLe d i j).mp hφ)]
  | distColorLt r c i =>
    intro hφ m
    rw [sat_distColorLt, iso_distColorLt,
      sat_isoDistColorLt hpu ((radiiLe_distColorLt r c i).mp hφ)]
  | not φ ih =>
    intro hφ m
    rw [sat_not, iso_not, sat_not, ih ((radiiLe_not φ).mp hφ) m]
  | and φ ψ ihφ ihψ =>
    intro hφ m
    obtain ⟨h₁, h₂⟩ := (radiiLe_and φ ψ).mp hφ
    rw [sat_and, iso_and, sat_and, ihφ h₁ m, ihψ h₂ m]
  | exU φ ih =>
    intro hφ m
    rw [sat_exU, iso_exU, sat_exU]
    exact exists_congr fun v => ih ((radiiLe_exU φ).mp hφ) (Fin.snoc m v)
  | exL r g φ ih =>
    intro hφ m
    obtain ⟨hr, hφ'⟩ := (radiiLe_exL r g φ).mp hφ
    rw [sat_exL, iso_exL, sat_or, sat_exL, sat_exU]
    constructor
    · rintro ⟨v, hguard, hsat⟩
      rcases (guard_split r m g v).mp hguard with h | h
      · exact Or.inl ⟨v, h, (ih hφ' (Fin.snoc m v)).mp hsat⟩
      · refine Or.inr ⟨v, ?_⟩
        rw [sat_and]
        exact ⟨(sat_isoGuard hpd hr m g v).mpr h, (ih hφ' (Fin.snoc m v)).mp hsat⟩
    · rintro (⟨v, h, hsat⟩ | ⟨v, hv⟩)
      · exact ⟨v, (guard_split r m g v).mpr (Or.inl h), (ih hφ' (Fin.snoc m v)).mpr hsat⟩
      · rw [sat_and] at hv
        exact ⟨v, (guard_split r m g v).mpr (Or.inr ((sat_isoGuard hpd hr m g v).mp hv.1)),
          (ih hφ' (Fin.snoc m v)).mpr hv.2⟩

/-- **The isolation rewrite is correct.** For every formula whose radii
stay below the cap and at *every* tuple — on or off the batch — truth in
the arena is truth of the translation in the isolated arena under a
coloring that interprets the three slot families as recorded. No
injectivity or disjointness of the slot maps is assumed.

The hypothesis `1 ≤ cap` is needed by the adjacency case alone, which
reads the profile slot at distance one; see
`one_le_cap_of_rhoMinus_le` for the form a rank-driven caller uses. -/
theorem sat_iso (hold : ∀ c, col' (old c) = col c)
    (hpd : ∀ (j : Fin m') (a : Fin (cap + 1)),
      col' (pd j a) = {v | WithinDist A (a : ℕ) v (w j)})
    (hpu : ∀ (c : Fin L) (b : Fin (cap + 1)),
      col' (pu c b) = {v | ∃ y ∈ col c, WithinDist A (b : ℕ) v y})
    (hcap : 1 ≤ cap) {k : ℕ} (φ : DistFO L k) (hφ : RadiiLe cap φ) (m : Fin k → Fin n) :
    Sat A col m φ ↔ Sat (deleteVerts A (Set.range w)) col' m (iso old pd pu φ) :=
  sat_iso_aux hold hpd hpu hcap φ hφ m

end Semantics

/-! ### The translation preserves distance rank -/

section Rank

variable {L L' m' cap : ℕ} {pd : Fin m' → Fin (cap + 1) → Fin L'}
  {pu : Fin L → Fin (cap + 1) → Fin L'} {k k' q : ℕ}

/-- The profile disjuncts are built from color atoms, so they carry
every distance rank. -/
theorem drank_profileList (d : ℕ) (i j : Fin k) :
    ∀ ψ ∈ profileList pd d i j, DRank k' q ψ := by
  intro ψ hψ
  rw [profileList] at hψ
  obtain ⟨j', -, hψ⟩ := List.mem_flatMap.mp hψ
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hψ
  exact .and (.color _ _) (.color _ _)

/-- The profile disjunction carries every distance rank. -/
theorem drank_profileOr (d : ℕ) (i j : Fin k) : DRank k' q (profileOr pd d i j) := by
  rw [profileOr]
  exact drank_bigOr (drank_falsum i) _ (drank_profileList d i j)

/-- The translated adjacency atom carries every distance rank. -/
theorem drank_isoAdj (i j : Fin k) : DRank k' q (isoAdj pd i j) := by
  rw [isoAdj]
  refine drank_or (.adj i j) (.and (.not (.eq i j)) (drank_bigOr (drank_falsum i) _ ?_))
  intro ψ hψ
  obtain ⟨j', -, rfl⟩ := List.mem_map.mp hψ
  exact drank_or (.and (.color _ _) (.color _ _)) (.and (.color _ _) (.color _ _))

/-- The translated binary distance atom keeps the radius bound of the
atom it came from. -/
theorem drank_isoDistLe {d : ℕ} (i j : Fin k) (hr : d ≤ rhoMinus k' q) :
    DRank k' q (isoDistLe pd d i j) := by
  rw [isoDistLe]
  exact drank_or (.distLe i j hr) (drank_profileOr d i j)

/-- The translated unary distance atom is a color atom or falsity, so
it carries every distance rank — in particular the radius bound of the
atom it came from is not needed. -/
theorem drank_isoDistColorLt (r : ℕ) (c : Fin L) (i : Fin k) :
    DRank k' q (isoDistColorLt pu r c i) := by
  rw [isoDistColorLt]
  split
  · exact .color _ _
  · exact drank_falsum i

/-- The through-the-batch guard is built from color atoms, so it
carries every distance rank. This is what makes case 2 of the local
quantifier rank-neutral. -/
theorem drank_isoGuard (r : ℕ) (g : Finset (Fin k)) : DRank k' q (isoGuard pd r g) := by
  rw [isoGuard]
  refine drank_bigOr (drank_falsum _) _ ?_
  intro ψ hψ
  obtain ⟨i, -, hψ⟩ := List.mem_flatMap.mp hψ
  exact drank_profileList r i.castSucc (Fin.last k) ψ hψ

/-- **The isolation rewrite preserves distance rank exactly.** The two
cases of a local quantifier are what makes this work: the first keeps a
genuine guard at the same radius, and the second is an unrestricted
quantifier whose guard is rank-free. -/
theorem drank_iso {old : Fin L → Fin L'} {φ : DistFO L k} (h : DRank k' q φ) :
    DRank k' q (iso old pd pu φ) := by
  induction h with
  | adj i j => rw [iso_adj]; exact drank_isoAdj i j
  | eq i j => rw [iso_eq]; exact .eq i j
  | color c i => rw [iso_color]; exact .color _ i
  | distLe i j hr => rw [iso_distLe]; exact drank_isoDistLe i j hr
  | distColorLt c i _ => rw [iso_distColorLt]; exact drank_isoDistColorLt _ c i
  | not _ ih => rw [iso_not]; exact .not ih
  | and _ _ ih ih' => rw [iso_and]; exact .and ih ih'
  | exU _ ih => rw [iso_exU]; exact .exU ih
  | exL _ hr ih =>
    rw [iso_exL]
    exact drank_or (.exL ih hr) (.exU (.and (drank_isoGuard _ _) ih))

end Rank

/-! ### Reading the cap off a distance rank

A formula of distance rank `(k', q)` has its distance atoms bounded by
ρ⁻(k', q) and its guards by ρ⁺(k'+1, q−1) — the latter because
`DRank.exL` concludes rank `(k', q₀ + 1)` from a guard bounded at `q₀`.
Both bounds descend along the derivation by the antidiagonal
monotonicities of `Lax3Proofs.Horizon`.
-/

section Cap

variable {L k : ℕ}

/-- The auxiliary form of `radiiLe_of_drank`: the guard bound is stated
over the predecessors of `q`, so that a rank with no quantifiers at all
imposes no guard condition. -/
private theorem radiiLe_aux {k' q : ℕ} {φ : DistFO L k} (h : DRank k' q φ) :
    ∀ {cap : ℕ}, rhoMinus k' q ≤ cap → (∀ q₀, q = q₀ + 1 → rhoPlus (k' + 1) q₀ ≤ cap) →
      RadiiLe cap φ := by
  induction h with
  | adj i j => intro cap _ _; exact radiiLe_adj i j
  | eq i j => intro cap _ _; exact radiiLe_eq i j
  | color c i => intro cap _ _; exact radiiLe_color c i
  | distLe i j hr => intro cap hm _; exact hr.trans hm
  | distColorLt c i hr => intro cap hm _; exact hr.trans hm
  | not _ ih => intro cap hm hp; exact ih hm hp
  | and _ _ ih ih' => intro cap hm hp; exact ⟨ih hm hp, ih' hm hp⟩
  | @exU k' q _ _ _ ih =>
    intro cap hm hp
    refine (radiiLe_exU _).mpr (ih ((rhoMinus_succ_left_le k' q).trans hm) ?_)
    rintro q₀ rfl
    exact (rhoPlus_succ_left_le (k' + 1) q₀).trans (hp _ rfl)
  | @exL k' q _ _ _ _ _ hr ih =>
    intro cap hm hp
    refine (radiiLe_exL _ _ _).mpr ⟨hr.trans (hp q rfl), ih ((rhoMinus_succ_left_le k' q).trans hm)
      ?_⟩
    rintro q₀ rfl
    exact (rhoPlus_succ_left_le (k' + 1) q₀).trans (hp _ rfl)

/-- **Every radius of a `(k', q)`-ranked formula is below the cap**, as
soon as the cap dominates both horizons of that rank: ρ⁻(k', q) for the
distance atoms and ρ⁺(k'+1, q−1) for the guards. The natural-number
subtraction is harmless — at `q = 0` no local quantifier can occur, so
the second hypothesis is unused. -/
theorem radiiLe_of_drank {k' q cap : ℕ} {φ : DistFO L k} (h : DRank k' q φ)
    (hm : rhoMinus k' q ≤ cap) (hp : rhoPlus (k' + 1) (q - 1) ≤ cap) : RadiiLe cap φ := by
  refine radiiLe_aux h hm ?_
  rintro q₀ rfl
  simpa using hp

/-- The cap of a rank-driven caller is positive, which is the side
condition `sat_iso` needs for its adjacency case. -/
theorem one_le_cap_of_rhoMinus_le {k' q cap : ℕ} (hm : rhoMinus k' q ≤ cap) : 1 ≤ cap :=
  (one_le_rhoMinus k' q).trans hm

end Cap

end Lax3Proofs.Isolate
