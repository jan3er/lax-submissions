import Lax3Proofs.Augmentation
import Lax12Proofs.MinorBridge
import Lax12Proofs.NowhereDenseDensity

/-!
Depth-one density of the augmented graphs of a transitive–fraternal
augmentation chain.

# The obligation

`Lax3Proofs.Augmentation` proves everything about `r`-round augmentation
chains except one input of the in-degree bound for the chain the *program*
plays: `AugmentedDepthOneDensity`, the statement that the augmented graphs
of the rounds again have bounded depth-1 minor density.  It is what
`fratGraph_lowDegreeVertex` — the fraternity densification lemma, and with
it the whole greedy recursion — consumes at every round.  This file
discharges it on nowhere dense classes, for *arbitrary* chains with
per-round in-degree bounds, and re-runs the greedy recursion with no
density hypothesis left (`exists_greedy_chain_inDegLE`).

# Why the path invariant is not enough

Every arc of round `i` is realized by a `G`-walk of length at most `2 ^ i`
(`walk_of_arc`), so it is tempting to push a minor of the augmented graph
down along those walks.  That cannot work on its own: a star belongs to
every nowhere dense class and the square of a star is a clique, so
"realized by short walks" does not bound density at all.  Any proof has to
use the *orientation*: the in-degree bound is what makes the augmented
graph sparse, and it must enter the argument.  It does, in exactly one
place — `card_claims_le`.

The second obstruction is collision control.  Expanding an edge of the
augmented graph into its length-two realizing path introduces a witness
`w`, and witnesses of different edges collide, while the branch sets of a
minor model must be disjoint.  Expanding *all* the way down to `G` makes
this hopeless, since a vertex of `G` can lie on the realizing walks of
unboundedly many arcs.

# The route

One round at a time, in the graphs of the rounds themselves, never in `G`.

Every edge of the augmented graph `D'.toGraph` is either an edge of the
round's own graph `H` or has a witness `w` adjacent in `H` to both ends,
*one of which is an in-neighbour of `w`* (`edge_realization`).  So a branch
set may only ever claim a witness through a vertex of its own that is an
in-neighbour of it — and since in-degrees are at most `d` and branch sets
are disjoint, at most `d + 1` branch sets can claim any given vertex
(`card_claims_le`).

An *awarding* is a map `ω : Fin n → Fin m` giving every vertex of `H` to at
most one branch set; the awarded branch set of `ξ` is `ball H ω b (c ξ) ξ`,
everything reachable from the old centre inside the class `ω⁻¹ ξ`.
Disjointness and the radius bound of the resulting model are then free —
that is the point of the definition — and all the work moves into showing
that many edges survive.  An edge survives if `ω` obeys a demand:
finitely many vertices awarded a specified way.  The demand is built by
expanding the two centre-to-endpoint walks of the given model into `H`
(`exists_expand`) and then reading a *first crossing* off the
concatenation (`exists_first_entry`); crossing first is what makes the two
halves of the demand disjoint, so the demand really is a partial function
and not an unsatisfiable pair of constraints.  A demand names at most
`6a+6` vertices, each with at most `d+2` possible owners, so averaging
over all awardings (`exists_awarding`, a product-measure count on
`Fintype.piFinset`) produces one awarding that keeps a
`1 / (d+2) ^ (6a+6)` fraction of the edges.  That is `roundTransfer`: a
depth-`a` minor of the augmented graph becomes a depth-`(4a+4)` minor of
`H` on no more vertices, with a `stepFactor d a` loss in density.

Iterating `r` times (`chain_density`) bounds the depth-1 density of round
`i` by the depth-`chainDepth i 1` density of `G`, which on a nowhere dense
class is subpolynomial by `Lax12`'s density theorem
(`exists_densityAtMost_of_nowhereDense`).  No walk in `G` is ever
expanded, and no shallow-minor composition is needed: the induction stays
inside one round at a time.

# The joint recursion

The in-degree bound of round `i+1` needs the depth-1 density of round `i`,
and that density needs the in-degree bounds of the rounds *before* `i` —
never of round `i` itself.  So the two recursions close as one: `joint`
computes the pair (in-degree budget, depth-parametric density budget) and
`greedy_chain_joint` is the single induction that proves both halves,
`fratGraph_lowDegreeVertex` and `inDegLE_of_augStep` supplying the
in-degree step and `roundTransfer` the density step.

# What the program phase supplies

Its own chain (`IsAugChain G D r`), the fact that each round orients its
fraternity graph greedily (`GreedyFratRound`), and a starting in-degree
`d` for `D 0`; `exists_greedy_chain_inDegLE` then bounds every round's
in-degree by `(joint d ⌈c · m ^ δ⌉ i).1`.  A chain with in-degree bounds
from any other source instead instantiates `exists_chain_density`, whose
budget `chainDens dd D₁ i 1` is `chainConst dd i 1 * D₁` by
`chainDens_eq`: a polynomial in the earlier rounds' in-degrees times the
subpolynomial density of `G`.
-/

namespace Lax3Proofs.AugmentedDensity

open scoped SimpleGraph
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ShallowMinorDensity
open Lax3Proofs.Augmentation

variable {n : ℕ}

/-! ### Clause lemmas for the imported concepts

The submission's rules forbid unfolding a concept definition with a
tactic, so every use of `HasShallowMinor`, `HasDensityAtMost` and
`NowhereDense` below goes through one of these `Iff.rfl` lemmas. -/

/-- A depth-`r` minor is a nonempty set of models. -/
theorem hasShallowMinor_iff {V W : Type*} {G : SimpleGraph V} {r : ℕ} {J : SimpleGraph W} :
    HasShallowMinor G r J ↔ Nonempty (ShallowMinorModel r J G) := Iff.rfl

/-- The density bound, spelled out. -/
theorem hasDensityAtMost_iff {G : SimpleGraph (Fin n)} {r D₁ : ℕ} :
    HasDensityAtMost G r D₁ ↔
      ∀ (m : ℕ) (J : SimpleGraph (Fin m)), HasShallowMinor G r J →
        J.edgeSet.ncard ≤ D₁ * m := Iff.rfl

/-- The subpolynomial density of a class, spelled out. -/
theorem hasSubpolynomialDensity_iff {C : GraphClass} :
    HasSubpolynomialDensity C ↔
      ∀ (r : ℕ) (ε : ℝ), 0 < ε → ∃ c : ℝ,
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
          ∀ (m : ℕ) (J : SimpleGraph (Fin m)), HasShallowMinor G r J →
            (J.edgeSet.ncard : ℝ) ≤ c * (m : ℝ) ^ (1 + ε) := Iff.rfl

/-! ### Monotonicity of the minor and density predicates -/

/-- A shallow minor stays one at a larger depth. -/
theorem hasShallowMinor_mono_depth {V W : Type*} {G : SimpleGraph V} {J : SimpleGraph W}
    {a b : ℕ} (hab : a ≤ b) (h : HasShallowMinor G a J) : HasShallowMinor G b J := by
  obtain ⟨M⟩ := hasShallowMinor_iff.1 h
  exact hasShallowMinor_iff.2 ⟨{ M with
    radius_le := fun u x hx => by
      obtain ⟨w, hw, hsupp⟩ := M.radius_le u x hx
      exact ⟨w, hw.trans hab, hsupp⟩ }⟩

/-- A density bound at a larger depth is a density bound. -/
theorem hasDensityAtMost_mono_depth {G : SimpleGraph (Fin n)} {a b D₁ : ℕ} (hab : a ≤ b)
    (h : HasDensityAtMost G b D₁) : HasDensityAtMost G a D₁ :=
  fun m J hJ => hasDensityAtMost_iff.1 h m J (hasShallowMinor_mono_depth hab hJ)

/-- A density bound weakens. -/
theorem hasDensityAtMost_mono {G : SimpleGraph (Fin n)} {r D₁ D₂ : ℕ} (h12 : D₁ ≤ D₂)
    (h : HasDensityAtMost G r D₁) : HasDensityAtMost G r D₂ :=
  fun m J hJ => (hasDensityAtMost_iff.1 h m J hJ).trans (Nat.mul_le_mul_right m h12)

/-- Composition of shallow minors, in the concept's idiom: a depth-`b`
minor of a depth-`a` minor of `G` is a depth-`(2ab+a+b)` minor of `G`.
This is `Lax12Proofs.ShallowMinors.shallowMinor_trans` read through the
bridge. -/
theorem hasShallowMinor_trans {n m k : ℕ} {G : SimpleGraph (Fin n)} {X : SimpleGraph (Fin m)}
    {J : SimpleGraph (Fin k)} {a b : ℕ} (hX : HasShallowMinor G a X)
    (hJ : HasShallowMinor X b J) : HasShallowMinor G (2 * a * b + a + b) J :=
  Lax12Proofs.MinorBridge.hasShallowMinor_of_isShallowMinor
    (Lax12Proofs.ShallowMinors.shallowMinor_trans
      (Lax12Proofs.MinorBridge.isShallowMinor_of_hasShallowMinor hJ)
      (Lax12Proofs.MinorBridge.isShallowMinor_of_hasShallowMinor hX))

/-- Density passes to shallow minors: if `X` is a depth-`a` minor of `G`
and `G` has depth-`(2ab+a+b)` density at most `D₁`, then `X` has depth-`b`
density at most `D₁`. -/
theorem hasDensityAtMost_of_minor {m : ℕ} {G : SimpleGraph (Fin n)} {X : SimpleGraph (Fin m)}
    {a b D₁ : ℕ} (hX : HasShallowMinor G a X) (h : HasDensityAtMost G (2 * a * b + a + b) D₁) :
    HasDensityAtMost X b D₁ :=
  fun k J hJ => hasDensityAtMost_iff.1 h k J (hasShallowMinor_trans hX hJ)

/-- Density passes to subgraphs. -/
theorem hasDensityAtMost_of_isContained {m : ℕ} {G : SimpleGraph (Fin m)}
    {Gn : SimpleGraph (Fin n)} {r D₁ : ℕ} (hsub : G ⊑ Gn) (h : HasDensityAtMost Gn r D₁) :
    HasDensityAtMost G r D₁ :=
  fun k J hJ =>
    hasDensityAtMost_iff.1 h k J (Lax12Proofs.MinorBridge.hasShallowMinor_of_copy hsub hJ)

/-! ### The single-round transfer, as a named property

One round of the process turns a depth-`a` minor of the augmented graph
into a depth-`stepDepth a` minor of the round's own graph, at the price
of a factor `stepFactor d a` in the density.  `RoundTransfer` names that
statement; it is proved as `roundTransfer` below and is stated separately
only so that the chain bookkeeping can be read off from it. -/

/-- The depth in the round's own graph of the minor built from a depth-`a`
minor of the augmented graph. -/
def stepDepth (a : ℕ) : ℕ := 4 * a + 4

/-- The density factor one round costs, at in-degree `d` and depth `a`:
the number of ways the `6a+6` vertices an edge constrains can be awarded
to the `d+2` branch sets that may claim them. -/
def stepFactor (d a : ℕ) : ℕ := (d + 2) ^ (6 * a + 6)

theorem le_stepDepth (a : ℕ) : a ≤ stepDepth a := by
  rw [stepDepth]; omega

theorem stepDepth_mono {a b : ℕ} (h : a ≤ b) : stepDepth a ≤ stepDepth b := by
  rw [stepDepth, stepDepth]; omega

/-- **The single-round density transfer.**  If the arcs of `D` are edges
of `H`, `D` has in-degree at most `d` and `H` has depth-`stepDepth a`
density at most `D₁`, then every graph augmented from `D` has depth-`a`
density at most `stepFactor d a * D₁`. -/
def RoundTransfer : Prop :=
  ∀ ⦃n : ℕ⦄ (H : SimpleGraph (Fin n)) (D D' : Orientation n) (d D₁ a : ℕ),
    (∀ u v : Fin n, u ∈ D.inN v → H.Adj u v) → AugStep D D' → D.InDegLE d →
    HasDensityAtMost H (stepDepth a) D₁ →
    HasDensityAtMost D'.toGraph a (stepFactor d a * D₁)

/-! ### Awarding witnesses to branch sets

The proof of the transfer.  A depth-`a` minor model of `J` in the
augmented graph is turned into a model in `H` by *awarding* every vertex
of `H` to at most one branch set: an awarding is a map
`ω : Fin n → Fin m`, and the branch set of `ξ` becomes the set of
vertices reachable from the old center inside the class `ω⁻¹ ξ`.
Disjointness and the radius bound are then free, and all the work is in
showing that a `1 / (d+2) ^ (8a+8)` fraction of the edges of `J` survives
for some awarding. -/

section Transfer

variable {H : SimpleGraph (Fin n)} {D D' : Orientation n}

/-- Every edge of the augmented graph is an edge of the round's graph, or
runs through a witness `w` of which one of its two ends is an
in-neighbour.  This one-sidedness is what bounds the number of branch
sets that can lay claim to `w`. -/
theorem edge_realization (harc : ∀ u v : Fin n, u ∈ D.inN v → H.Adj u v)
    (hstep : AugStep D D') {u v : Fin n} (h : D'.toGraph.Adj u v) :
    H.Adj u v ∨ ∃ w : Fin n, H.Adj u w ∧ H.Adj w v ∧ (u ∈ D.inN w ∨ v ∈ D.inN w) := by
  have key : ∀ p q : Fin n, p ∈ D'.inN q →
      H.Adj p q ∨ ∃ w : Fin n, H.Adj p w ∧ H.Adj w q ∧ (p ∈ D.inN w ∨ q ∈ D.inN w) := by
    intro p q hpq
    rcases hstep.tight p q hpq with h1 | ⟨w, hpw, hwq⟩ | ⟨w, hpw, hqw⟩
    · exact Or.inl (harc _ _ h1)
    · exact Or.inr ⟨w, harc _ _ hpw, harc _ _ hwq, Or.inl hpw⟩
    · exact Or.inr ⟨w, harc _ _ hpw, (harc _ _ hqw).symm, Or.inl hpw⟩
  rcases h with h | h
  · exact key u v h
  · rcases key v u h with h' | ⟨w, h1, h2, h3⟩
    · exact Or.inl h'.symm
    · exact Or.inr ⟨w, h2.symm, h1.symm, h3.symm⟩

/-- `z` may be awarded to the branch set `ξ`: either it lies in it, or it
is a witness with an in-neighbour there. -/
def Dem (D : Orientation n) {m : ℕ} (B : Fin m → Set (Fin n)) (ξ : Fin m) (z : Fin n) : Prop :=
  z ∈ B ξ ∨ ∃ t ∈ B ξ, t ∈ D.inN z

/-- **Expansion.**  A walk in the augmented graph becomes a walk in the
round's graph of at most twice the length, every vertex of which is a
vertex of the original walk or a witness with an in-neighbour on it. -/
theorem exists_expand (harc : ∀ u v : Fin n, u ∈ D.inN v → H.Adj u v) (hstep : AugStep D D')
    {s t : Fin n} (W : D'.toGraph.Walk s t) :
    ∃ P : H.Walk s t, P.length ≤ 2 * W.length ∧
      ∀ z ∈ P.support, z ∈ W.support ∨ ∃ y ∈ W.support, y ∈ D.inN z := by
  induction W with
  | nil =>
      refine ⟨SimpleGraph.Walk.nil, by simp, fun z hz => Or.inl ?_⟩
      simpa using hz
  | @cons s s' t h W' ih =>
      obtain ⟨P', hlen, hsupp⟩ := ih
      have hmono : ∀ z, (z ∈ W'.support ∨ ∃ y ∈ W'.support, y ∈ D.inN z) →
          (z ∈ (SimpleGraph.Walk.cons h W').support ∨
            ∃ y ∈ (SimpleGraph.Walk.cons h W').support, y ∈ D.inN z) := by
        rintro z (hz | ⟨y, hy, hyz⟩)
        · exact Or.inl (by simp [hz])
        · exact Or.inr ⟨y, by simp [hy], hyz⟩
      rcases edge_realization harc hstep h with hadj | ⟨w, h1, h2, h3⟩
      · refine ⟨SimpleGraph.Walk.cons hadj P', ?_, fun z hz => ?_⟩
        · rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons]; omega
        · rcases List.mem_cons.1 (by simpa using hz) with rfl | hz'
          · exact Or.inl (by simp)
          · exact hmono z (hsupp z hz')
      · refine ⟨SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P'), ?_, fun z hz => ?_⟩
        · rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons,
            SimpleGraph.Walk.length_cons]
          omega
        · have hz' : z = s ∨ z = w ∨ z ∈ P'.support := by simpa using hz
          rcases hz' with rfl | rfl | hz''
          · exact Or.inl (by simp)
          · refine Or.inr ?_
            rcases h3 with h3 | h3
            · exact ⟨s, by simp, h3⟩
            · exact ⟨s', by simp, h3⟩
          · exact hmono z (hsupp z hz'')

/-- **First entry.**  A walk that starts outside a set and ends inside it
crosses an edge from outside to inside; the part before the crossing
avoids the set. -/
theorem exists_first_entry {s t : Fin n} (S : Set (Fin n)) (Z : H.Walk s t) :
    t ∈ S → s ∉ S → ∃ (u v : Fin n) (Zu : H.Walk s u), H.Adj u v ∧ v ∈ S ∧
      Zu.length ≤ Z.length ∧ ∀ y ∈ Zu.support, y ∈ Z.support ∧ y ∉ S := by
  induction Z with
  | nil => intro ht hs; exact absurd ht hs
  | @cons s s' t h W' ih =>
      intro ht hs
      by_cases hs' : s' ∈ S
      · refine ⟨s, s', SimpleGraph.Walk.nil, h, hs', by simp, fun y hy => ?_⟩
        have : y = s := by simpa using hy
        subst this
        exact ⟨by simp, hs⟩
      · obtain ⟨u, v, Zu, hadj, hvS, hlen, hsub⟩ := ih ht hs'
        refine ⟨u, v, SimpleGraph.Walk.cons h Zu, hadj, hvS, ?_, fun y hy => ?_⟩
        · rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons]; omega
        · rcases List.mem_cons.1 (by simpa using hy) with rfl | hy'
          · exact ⟨by simp, hs⟩
          · exact ⟨by simp [(hsub y hy').1], (hsub y hy').2⟩

/-! ### The awarded branch sets -/

/-- The branch set awarded to `ξ`: everything reachable from the center
`c` by an `H`-walk of length at most `b` all of whose vertices `ω` awards
to `ξ`. -/
def ball {m : ℕ} (H : SimpleGraph (Fin n)) (ω : Fin n → Fin m) (b : ℕ) (c : Fin n)
    (ξ : Fin m) : Set (Fin n) :=
  {z | ∃ P : H.Walk c z, P.length ≤ b ∧ ∀ y ∈ P.support, ω y = ξ}

theorem mem_ball_iff {m : ℕ} {ω : Fin n → Fin m} {b : ℕ} {c z : Fin n} {ξ : Fin m} :
    z ∈ ball H ω b c ξ ↔ ∃ P : H.Walk c z, P.length ≤ b ∧ ∀ y ∈ P.support, ω y = ξ := Iff.rfl

/-- Everything in a ball is awarded to its own index — which is why balls
of different indices are disjoint. -/
theorem award_eq_of_mem_ball {m : ℕ} {ω : Fin n → Fin m} {b : ℕ} {c z : Fin n} {ξ : Fin m}
    (h : z ∈ ball H ω b c ξ) : ω z = ξ := by
  obtain ⟨P, -, hP⟩ := mem_ball_iff.1 h
  exact hP z P.end_mem_support

theorem center_mem_ball {m : ℕ} {ω : Fin n → Fin m} {b : ℕ} {c : Fin n} {ξ : Fin m}
    (h : ω c = ξ) : c ∈ ball H ω b c ξ := by
  refine mem_ball_iff.2 ⟨SimpleGraph.Walk.nil, by simp, fun y hy => ?_⟩
  have : y = c := by simpa using hy
  simpa [this] using h

/-- Balls have radius `b` inside themselves: a prefix of a witnessing
walk witnesses its own endpoint. -/
theorem ball_radius {m : ℕ} {ω : Fin n → Fin m} {b : ℕ} {c z : Fin n} {ξ : Fin m}
    (h : z ∈ ball H ω b c ξ) :
    ∃ P : H.Walk c z, P.length ≤ b ∧ ∀ y ∈ P.support, y ∈ ball H ω b c ξ := by
  classical
  obtain ⟨P, hlen, hP⟩ := mem_ball_iff.1 h
  refine ⟨P, hlen, fun y hy => mem_ball_iff.2 ⟨P.takeUntil y hy, ?_, fun x hx => ?_⟩⟩
  · exact (P.length_takeUntil_le hy).trans hlen
  · exact hP x (P.support_takeUntil_subset_support hy hx)

theorem ball_mono {m : ℕ} {ω : Fin n → Fin m} {b b' : ℕ} {c : Fin n} {ξ : Fin m}
    (hb : b ≤ b') : ball H ω b c ξ ⊆ ball H ω b' c ξ := by
  rintro z hz
  obtain ⟨P, hlen, hP⟩ := mem_ball_iff.1 hz
  exact mem_ball_iff.2 ⟨P, hlen.trans hb, hP⟩

private theorem card_support_toFinset_le {s t : Fin n} (P : H.Walk s t) :
    P.support.toFinset.card ≤ P.length + 1 := by
  classical
  simpa [SimpleGraph.Walk.length_support] using List.toFinset_card_le P.support

/-! ### The demand of one edge

An edge of `J` survives an awarding `ω` if `ω` maps a bounded set of
vertices the way that edge asks for.  The set is built from the two walks
that connect the endpoints' centres to the realizing edge: the awarding
is read off a *first crossing* of the concatenated walk, which is what
keeps the two halves of the demand disjoint, so that the demand really is
a partial function and not an unsatisfiable pair of constraints. -/

private theorem exists_demand_of_walks {m : ℕ} {B : Fin m → Set (Fin n)} {cx cy : Fin n}
    {x y : Fin m} (hxy : x ≠ y) (hcx : cx ∈ B x) (hcy : cy ∈ B y)
    (hdisj : ∀ ξ η : Fin m, ξ ≠ η → Disjoint (B ξ) (B η))
    {e₁ e₂ : Fin n} {L K R : ℕ} (Qx : H.Walk cx e₁) (Qy : H.Walk cy e₂) (hadj : H.Adj e₁ e₂)
    (hQx : Qx.length ≤ L) (hQy : Qy.length ≤ L) (hK : 3 * L + 3 ≤ K) (hR : 2 * L + 1 ≤ R)
    (hQxdem : ∀ z ∈ Qx.support, Dem D B x z) (hQydem : ∀ z ∈ Qy.support, Dem D B y z) :
    ∃ (T : Finset (Fin n)) (g : Fin n → Fin m),
      T.card ≤ K ∧ (∀ z ∈ T, Dem D B (g z) z) ∧
      cx ∈ T ∧ g cx = x ∧ cy ∈ T ∧ g cy = y ∧
      ∀ ω : Fin n → Fin m, (∀ z ∈ T, ω z = g z) →
        ∃ u ∈ ball H ω R cx x, ∃ v ∈ ball H ω R cy y, H.Adj u v := by
  classical
  have hcne : cx ≠ cy := fun hc => Set.disjoint_left.1 (hdisj x y hxy) hcx (hc ▸ hcy)
  by_cases hcase : cx ∈ Qy.support
  · -- the centre of `x` already lies on the `y`-side walk: award it to `x`
    -- and stop the `y`-side just before it
    have hRsupp : ∀ z ∈ (Qy.takeUntil cx hcase).support, z ∈ Qy.support := fun z hz =>
      Qy.support_takeUntil_subset_support hcase hz
    have hRlen : (Qy.takeUntil cx hcase).length ≤ L :=
      (Qy.length_takeUntil_le hcase).trans hQy
    obtain ⟨u, v, Zu, hadj', hvS, hlen, hsub⟩ :=
      exists_first_entry {z | z = cx} (Qy.takeUntil cx hcase) rfl (by simpa using hcne.symm)
    have hvcx : v = cx := hvS
    refine ⟨insert cx Zu.support.toFinset, fun z => if z = cx then x else y, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · refine (Finset.card_insert_le _ _).trans ?_
      have := card_support_toFinset_le Zu
      omega
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz'
      · simpa using (Or.inl hcx : Dem D B x z)
      · have hzne : z ≠ cx := (hsub z (List.mem_toFinset.1 hz')).2
        simpa [hzne] using hQydem z (hRsupp z (hsub z (List.mem_toFinset.1 hz')).1)
    · exact Finset.mem_insert_self _ _
    · simp
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.2 Zu.start_mem_support)
    · simp [hcne.symm]
    · intro ω hω
      have hωcx : ω cx = x := by simpa using hω cx (Finset.mem_insert_self _ _)
      refine ⟨cx, center_mem_ball hωcx, u, mem_ball_iff.2 ⟨Zu, by omega, fun z hz => ?_⟩, ?_⟩
      · have hzne : z ≠ cx := (hsub z hz).2
        have := hω z (Finset.mem_insert_of_mem (List.mem_toFinset.2 hz))
        simpa [hzne] using this
      · exact (hvcx ▸ hadj' : H.Adj u cx).symm
  · -- the generic case: cross from the `x`-side to the `y`-side at the
    -- first vertex of the `y`-side walk the concatenation meets
    have hZsupp : ∀ z ∈ (Qx.append (hadj.toWalk.append Qy.reverse)).support,
        z ∈ Qx.support ∨ z ∈ Qy.support := by
      intro z hz
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hz with hz' | hz'
      · exact Or.inl hz'
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hz' with hz'' | hz''
      · have : z = e₁ ∨ z = e₂ := by simpa using hz''
        rcases this with rfl | rfl
        · exact Or.inl Qx.end_mem_support
        · exact Or.inr Qy.end_mem_support
      · exact Or.inr (by simpa using hz'')
    have hZlen : (Qx.append (hadj.toWalk.append Qy.reverse)).length ≤ 2 * L + 1 := by
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_reverse]
      have hone : hadj.toWalk.length = 1 := rfl
      omega
    obtain ⟨u, v, Zu, hadj', hvS, hlen, hsub⟩ :=
      exists_first_entry {z | z ∈ Qy.support} (Qx.append (hadj.toWalk.append Qy.reverse))
        Qy.start_mem_support hcase
    have hRsupp : ∀ z ∈ (Qy.takeUntil v hvS).support, z ∈ Qy.support := fun z hz =>
      Qy.support_takeUntil_subset_support hvS hz
    have hRlen : (Qy.takeUntil v hvS).length ≤ L := (Qy.length_takeUntil_le hvS).trans hQy
    refine ⟨Zu.support.toFinset ∪ (Qy.takeUntil v hvS).support.toFinset,
      fun z => if z ∈ Zu.support then x else y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine (Finset.card_union_le _ _).trans ?_
      have h1 := card_support_toFinset_le Zu
      have h2 := card_support_toFinset_le (Qy.takeUntil v hvS)
      omega
    · intro z hz
      by_cases hzu : z ∈ Zu.support
      · have hzx : z ∈ Qx.support := by
          rcases hZsupp z (hsub z hzu).1 with h | h
          · exact h
          · exact absurd h (hsub z hzu).2
        simpa [hzu] using hQxdem z hzx
      · have hzr : z ∈ (Qy.takeUntil v hvS).support := by
          rcases Finset.mem_union.1 hz with h | h
          · exact absurd (List.mem_toFinset.1 h) hzu
          · exact List.mem_toFinset.1 h
        simpa [hzu] using hQydem z (hRsupp z hzr)
    · exact Finset.mem_union_left _ (List.mem_toFinset.2 Zu.start_mem_support)
    · simp [Zu.start_mem_support]
    · exact Finset.mem_union_right _
        (List.mem_toFinset.2 (Qy.takeUntil v hvS).start_mem_support)
    · have : cy ∉ Zu.support := fun hc => (hsub cy hc).2 Qy.start_mem_support
      simp [this]
    · intro ω hω
      have hωx : ∀ z ∈ Zu.support, ω z = x := by
        intro z hz
        have := hω z (Finset.mem_union_left _ (List.mem_toFinset.2 hz))
        simpa [hz] using this
      have hωy : ∀ z ∈ (Qy.takeUntil v hvS).support, ω z = y := by
        intro z hz
        have hzu : z ∉ Zu.support := fun hc => (hsub z hc).2 (hRsupp z hz)
        have := hω z (Finset.mem_union_right _ (List.mem_toFinset.2 hz))
        simpa [hzu] using this
      exact ⟨u, mem_ball_iff.2 ⟨Zu, by omega, hωx⟩,
        v, mem_ball_iff.2 ⟨Qy.takeUntil v hvS, by omega, hωy⟩, hadj'⟩

/-- **The demand of one edge.**  Every edge of a depth-`a` minor of the
augmented graph asks at most `6a+6` vertices to be awarded in a specific
way; each of them may legitimately be awarded that way, and any awarding
that obeys the demand realizes the edge between the awarded balls of
radius `4a+3` around the two centres. -/
theorem exists_demand {m : ℕ} {J : SimpleGraph (Fin m)} {a : ℕ}
    (harc : ∀ u v : Fin n, u ∈ D.inN v → H.Adj u v) (hstep : AugStep D D')
    (M : ShallowMinorModel a J D'.toGraph) {x y : Fin m} (hxy : J.Adj x y) :
    ∃ (T : Finset (Fin n)) (g : Fin n → Fin m),
      T.card ≤ 6 * a + 6 ∧ (∀ z ∈ T, Dem D M.branch (g z) z) ∧
      M.center x ∈ T ∧ g (M.center x) = x ∧ M.center y ∈ T ∧ g (M.center y) = y ∧
      ∀ ω : Fin n → Fin m, (∀ z ∈ T, ω z = g z) →
        ∃ u ∈ ball H ω (4 * a + 3) (M.center x) x,
          ∃ v ∈ ball H ω (4 * a + 3) (M.center y) y, H.Adj u v := by
  classical
  obtain ⟨p, hp, q, hq, hpq⟩ := M.adj x y hxy
  obtain ⟨Wx, hWxlen, hWxsupp⟩ := M.radius_le x p hp
  obtain ⟨Wy, hWylen, hWysupp⟩ := M.radius_le y q hq
  obtain ⟨Px, hPxlen, hPxsupp⟩ := exists_expand harc hstep Wx
  obtain ⟨Py, hPylen, hPysupp⟩ := exists_expand harc hstep Wy
  have hPxdem : ∀ z ∈ Px.support, Dem D M.branch x z := by
    intro z hz
    rcases hPxsupp z hz with h | ⟨t, ht, htz⟩
    · exact Or.inl (hWxsupp z h)
    · exact Or.inr ⟨t, hWxsupp t ht, htz⟩
  have hPydem : ∀ z ∈ Py.support, Dem D M.branch y z := by
    intro z hz
    rcases hPysupp z hz with h | ⟨t, ht, htz⟩
    · exact Or.inl (hWysupp z h)
    · exact Or.inr ⟨t, hWysupp t ht, htz⟩
  have hPxle : Px.length ≤ 2 * a + 1 := by omega
  have hPyle : Py.length ≤ 2 * a + 1 := by omega
  have hxyne : x ≠ y := J.ne_of_adj hxy
  rcases edge_realization harc hstep hpq with hadj | ⟨w, h1, h2, h3⟩
  · exact exists_demand_of_walks hxyne (M.center_mem x) (M.center_mem y) M.disjoint Px Py hadj
      hPxle hPyle (by omega) (by omega) hPxdem hPydem
  · have hone : ∀ {s t : Fin n} (h : H.Adj s t), h.toWalk.length = 1 := fun _ => rfl
    rcases h3 with h3 | h3
    · refine exists_demand_of_walks hxyne (M.center_mem x) (M.center_mem y) M.disjoint
        (Px.append h1.toWalk) Py h2 ?_ hPyle (by omega) (by omega) ?_ hPydem
      · rw [SimpleGraph.Walk.length_append, hone]; omega
      · intro z hz
        rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hz with hz' | hz'
        · exact hPxdem z hz'
        · have : z = p ∨ z = w := by simpa using hz'
          rcases this with rfl | rfl
          · exact hPxdem z Px.end_mem_support
          · exact Or.inr ⟨p, hp, h3⟩
    · refine exists_demand_of_walks hxyne (M.center_mem x) (M.center_mem y) M.disjoint
        Px (Py.append h2.symm.toWalk) h1 hPxle ?_ (by omega) (by omega) hPxdem ?_
      · rw [SimpleGraph.Walk.length_append, hone]; omega
      · intro z hz
        rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hz with hz' | hz'
        · exact hPydem z hz'
        · have : z = q ∨ z = w := by simpa using hz'
          rcases this with rfl | rfl
          · exact hPydem z Py.end_mem_support
          · exact Or.inr ⟨q, hq, h3⟩

/-! ### How many branch sets can claim one vertex

This is the only place the in-degree bound is used, and it is what makes
the averaging work: a vertex lies in at most one branch set and has at
most `d` in-neighbours, so at most `d + 1` branch sets may claim it. -/

/-- The branch sets that may claim `z`. -/
noncomputable def claims (D : Orientation n) {m : ℕ} (B : Fin m → Set (Fin n)) (z : Fin n) :
    Finset (Fin m) :=
  @Finset.filter _ (fun ξ => Dem D B ξ z) (Classical.decPred _) Finset.univ

theorem mem_claims {m : ℕ} {B : Fin m → Set (Fin n)} {z : Fin n} {ξ : Fin m} :
    ξ ∈ claims D B z ↔ Dem D B ξ z := by
  rw [claims, @Finset.mem_filter _ _ (Classical.decPred _)]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem card_claims_le {m : ℕ} {B : Fin m → Set (Fin n)} {d : ℕ} (hd : D.InDegLE d)
    (hdisj : ∀ ξ η : Fin m, ξ ≠ η → Disjoint (B ξ) (B η)) (z : Fin n) :
    (claims D B z).card ≤ d + 1 := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := claims D B z) (p := fun ξ => z ∈ B ξ)
  have hin : ((claims D B z).filter (fun ξ => z ∈ B ξ)).card ≤ 1 := by
    refine Finset.card_le_one.2 fun ξ hξ η hη => ?_
    by_contra hne
    exact Set.disjoint_left.1 (hdisj ξ η hne) (Finset.mem_filter.1 hξ).2
      (Finset.mem_filter.1 hη).2
  have hout : ((claims D B z).filter (fun ξ => ¬ z ∈ B ξ)).card ≤ d := by
    have hex : ∀ ξ : Fin m, ∃ t : Fin n,
        ξ ∈ (claims D B z).filter (fun ξ => ¬ z ∈ B ξ) → (t ∈ B ξ ∧ t ∈ D.inN z) := by
      intro ξ
      by_cases h : ξ ∈ (claims D B z).filter (fun ξ => ¬ z ∈ B ξ)
      · obtain ⟨hmem, hnot⟩ := Finset.mem_filter.1 h
        rcases mem_claims.1 hmem with hc | ⟨t, ht, htz⟩
        · exact absurd hc hnot
        · exact ⟨t, fun _ => ⟨ht, htz⟩⟩
      · exact ⟨z, fun hc => absurd hc h⟩
    choose f hf using hex
    refine le_trans (Finset.card_le_card_of_injOn f (fun ξ hξ => (hf ξ hξ).2) ?_) (hd z)
    intro ξ hξ η hη hfe
    by_contra hne
    exact Set.disjoint_left.1 (hdisj ξ η hne) (hf ξ hξ).1 (hfe ▸ (hf η hη).1)
  omega

/-! ### Averaging over awardings -/

/-- The edges of `E` whose demand the awarding `ω` obeys. -/
noncomputable def survivors {ι : Type} {m : ℕ} (E : Finset ι) (T : ι → Finset (Fin n))
    (g : ι → Fin n → Fin m) (ω : Fin n → Fin m) : Finset ι :=
  @Finset.filter _ (fun e => ∀ z ∈ T e, ω z = g e z) (Classical.decPred _) E

theorem mem_survivors {ι : Type} {m : ℕ} {E : Finset ι} {T : ι → Finset (Fin n)}
    {g : ι → Fin n → Fin m} {ω : Fin n → Fin m} {e : ι} :
    e ∈ survivors E T g ω ↔ e ∈ E ∧ ∀ z ∈ T e, ω z = g e z := by
  rw [survivors, @Finset.mem_filter _ _ (Classical.decPred _)]

/-- **Averaging.**  If every vertex has at most `q` possible owners and
every edge constrains the owners of at most `K` vertices, then some
awarding obeys the demands of a `1 / q ^ K` fraction of the edges. -/
theorem exists_awarding {ι : Type} {m : ℕ} (E : Finset ι) {q K : ℕ} (hq1 : 1 ≤ q)
    (Cs : Fin n → Finset (Fin m)) (hne : ∀ z, (Cs z).Nonempty) (hq : ∀ z, (Cs z).card ≤ q)
    (T : ι → Finset (Fin n)) (g : ι → Fin n → Fin m)
    (hmem : ∀ e ∈ E, ∀ z ∈ T e, g e z ∈ Cs z) (hK : ∀ e ∈ E, (T e).card ≤ K) :
    ∃ ω : Fin n → Fin m, E.card ≤ q ^ K * (survivors E T g ω).card := by
  classical
  have hΩne : (Fintype.piFinset Cs).Nonempty := Fintype.piFinset_nonempty.2 hne
  have key : ∀ e ∈ E, (Fintype.piFinset Cs).card ≤
      q ^ K * ((Fintype.piFinset Cs).filter (fun ω => ∀ z ∈ T e, ω z = g e z)).card := by
    intro e he
    have hfe : (Fintype.piFinset Cs).filter (fun ω => ∀ z ∈ T e, ω z = g e z)
        = Fintype.piFinset (fun z => if z ∈ T e then {g e z} else Cs z) := by
      ext ω
      simp only [Finset.mem_filter, Fintype.mem_piFinset]
      constructor
      · rintro ⟨hall, hagree⟩ z
        by_cases hz : z ∈ T e
        · simp [hz, hagree z hz]
        · simpa [hz] using hall z
      · intro h
        refine ⟨fun z => ?_, fun z hz => ?_⟩
        · by_cases hz : z ∈ T e
          · have hz' := h z
            rw [if_pos hz, Finset.mem_singleton] at hz'
            rw [hz']
            exact hmem e he z hz
          · simpa [hz] using h z
        · have hz' := h z
          rw [if_pos hz, Finset.mem_singleton] at hz'
          exact hz'
    rw [hfe, Fintype.card_piFinset, Fintype.card_piFinset]
    have hsplitL := Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin n))
      (fun z => z ∈ T e) (fun z => (Cs z).card)
    have hsplitR := Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin n))
      (fun z => z ∈ T e) (fun z => (if z ∈ T e then ({g e z} : Finset (Fin m)) else Cs z).card)
    have hR1 : ∏ z ∈ Finset.univ.filter (fun z => z ∈ T e),
        (if z ∈ T e then ({g e z} : Finset (Fin m)) else Cs z).card = 1 := by
      refine Finset.prod_eq_one fun z hz => ?_
      rw [if_pos (Finset.mem_filter.1 hz).2, Finset.card_singleton]
    have hR2 : ∏ z ∈ Finset.univ.filter (fun z => ¬ z ∈ T e),
        (if z ∈ T e then ({g e z} : Finset (Fin m)) else Cs z).card
        = ∏ z ∈ Finset.univ.filter (fun z => ¬ z ∈ T e), (Cs z).card := by
      refine Finset.prod_congr rfl fun z hz => ?_
      rw [if_neg (Finset.mem_filter.1 hz).2]
    have hL1 : ∏ z ∈ Finset.univ.filter (fun z => z ∈ T e), (Cs z).card ≤ q ^ K := by
      calc ∏ z ∈ Finset.univ.filter (fun z => z ∈ T e), (Cs z).card
          ≤ ∏ _z ∈ Finset.univ.filter (fun z => z ∈ T e), q :=
            Finset.prod_le_prod' fun z _ => hq z
        _ = q ^ (T e).card := by
            rw [Finset.prod_const, Finset.filter_univ_mem]
        _ ≤ q ^ K := Nat.pow_le_pow_right hq1 (hK e he)
    calc ∏ z, (Cs z).card
        = (∏ z ∈ Finset.univ.filter (fun z => z ∈ T e), (Cs z).card) *
            ∏ z ∈ Finset.univ.filter (fun z => ¬ z ∈ T e), (Cs z).card := hsplitL.symm
      _ ≤ q ^ K * ∏ z ∈ Finset.univ.filter (fun z => ¬ z ∈ T e), (Cs z).card :=
          Nat.mul_le_mul_right _ hL1
      _ = q ^ K * ∏ z, (if z ∈ T e then ({g e z} : Finset (Fin m)) else Cs z).card := by
          rw [← hsplitR, hR1, hR2, one_mul]
  have hcount : ∑ ω ∈ Fintype.piFinset Cs, (survivors E T g ω).card
      = ∑ e ∈ E, ((Fintype.piFinset Cs).filter (fun ω => ∀ z ∈ T e, ω z = g e z)).card := by
    simp only [survivors, Finset.card_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun w _ => by congr
  have hsum : ∑ _ω ∈ Fintype.piFinset Cs, E.card
      ≤ ∑ ω ∈ Fintype.piFinset Cs, q ^ K * (survivors E T g ω).card := by
    rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, hcount, Finset.mul_sum]
    calc (Fintype.piFinset Cs).card * E.card = ∑ _e ∈ E, (Fintype.piFinset Cs).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ e ∈ E, q ^ K *
            ((Fintype.piFinset Cs).filter (fun ω => ∀ z ∈ T e, ω z = g e z)).card :=
          Finset.sum_le_sum key
  obtain ⟨ω, -, hω⟩ := Finset.exists_le_of_sum_le hΩne hsum
  exact ⟨ω, hω⟩

end Transfer

/-! ### The transfer -/

/-- **The single-round density transfer**, proved.  A depth-`a` minor of
the augmented graph becomes, for a suitable awarding of the witnesses, a
depth-`(4a+4)` minor of the round's own graph on no more vertices, keeping
a `1 / (d+2) ^ (6a+6)` fraction of the edges. -/
theorem roundTransfer : RoundTransfer := by
  classical
  intro n H D D' d D₁ a harc hstep hd hdens
  refine hasDensityAtMost_iff.2 (fun m J hJ => ?_)
  haveI : DecidableRel J.Adj := Classical.decRel _
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hempty : J.edgeSet = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun e he => ?_
      induction e using Sym2.ind with
      | _ u v => exact u.elim0
    rw [hempty]
    simp
  obtain ⟨M⟩ := hasShallowMinor_iff.1 hJ
  -- an ordered representative of every edge
  have hrep : ∀ e : Sym2 (Fin m), ∃ p : Fin m × Fin m, s(p.1, p.2) = e := by
    intro e
    induction e using Sym2.ind with
    | _ u v => exact ⟨(u, v), rfl⟩
  choose rep hrep using hrep
  have hadj_of_mem : ∀ e ∈ J.edgeFinset, J.Adj (rep e).1 (rep e).2 := by
    intro e he
    have hmem : e ∈ J.edgeSet := by simpa using he
    rw [← hrep e] at hmem
    exact hmem
  -- the demand of every edge
  have hdemand : ∀ e : Sym2 (Fin m), ∃ (T : Finset (Fin n)) (g : Fin n → Fin m),
      T.card ≤ 6 * a + 6 ∧ (∀ z ∈ T, Dem D M.branch (g z) z) ∧
      (J.Adj (rep e).1 (rep e).2 →
        M.center (rep e).1 ∈ T ∧ g (M.center (rep e).1) = (rep e).1 ∧
        M.center (rep e).2 ∈ T ∧ g (M.center (rep e).2) = (rep e).2 ∧
        ∀ ω : Fin n → Fin m, (∀ z ∈ T, ω z = g z) →
          ∃ u ∈ ball H ω (4 * a + 3) (M.center (rep e).1) (rep e).1,
            ∃ v ∈ ball H ω (4 * a + 3) (M.center (rep e).2) (rep e).2, H.Adj u v) := by
    intro e
    by_cases h : J.Adj (rep e).1 (rep e).2
    · obtain ⟨T, g, h1, h2, h3, h4, h5, h6, h7⟩ := exists_demand harc hstep M h
      exact ⟨T, g, h1, h2, fun _ => ⟨h3, h4, h5, h6, h7⟩⟩
    · exact ⟨∅, fun _ => ⟨0, hm⟩, by simp, by simp, fun hc => absurd hc h⟩
  choose T g hTcard hTdem hTreal using hdemand
  -- the possible owners of every vertex
  set Cs : Fin n → Finset (Fin m) := fun z => insert ⟨0, hm⟩ (claims D M.branch z) with hCsdef
  have hCsne : ∀ z, (Cs z).Nonempty := fun z => ⟨⟨0, hm⟩, Finset.mem_insert_self _ _⟩
  have hCscard : ∀ z, (Cs z).card ≤ d + 2 := by
    intro z
    refine (Finset.card_insert_le _ _).trans ?_
    have := card_claims_le hd M.disjoint z
    omega
  obtain ⟨ω, hω⟩ := exists_awarding J.edgeFinset (q := d + 2) (K := 6 * a + 6) (by omega)
    Cs hCsne hCscard T g
    (fun e _ z hz => Finset.mem_insert_of_mem (mem_claims.2 (hTdem e z hz)))
    (fun e _ => hTcard e)
  -- the indices whose centre the awarding leaves in place
  set X : Finset (Fin m) := Finset.univ.filter (fun ξ => ω (M.center ξ) = ξ) with hXdef
  have hmemX : ∀ ξ : Fin m, ξ ∈ X ↔ ω (M.center ξ) = ξ := by
    intro ξ
    rw [hXdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hendX : ∀ e ∈ survivors J.edgeFinset T g ω, (rep e).1 ∈ X ∧ (rep e).2 ∈ X := by
    intro e he
    obtain ⟨heE, hagree⟩ := mem_survivors.1 he
    obtain ⟨hc1, hg1, hc2, hg2, -⟩ := hTreal e (hadj_of_mem e heE)
    exact ⟨(hmemX _).2 (by rw [hagree _ hc1, hg1]), (hmemX _).2 (by rw [hagree _ hc2, hg2])⟩
  have hEcard : J.edgeSet.ncard = J.edgeFinset.card := Lax12Proofs.MinorBridge.ncard_edgeSet J
  rcases X.eq_empty_or_nonempty with hXe | hXne
  · -- nothing survives, so there was nothing to count
    have hzero : (survivors J.edgeFinset T g ω).card = 0 := by
      rw [Finset.card_eq_zero]
      refine Finset.eq_empty_iff_forall_notMem.2 fun e he => ?_
      have := (hendX e he).1
      rw [hXe] at this
      exact absurd this (Finset.notMem_empty _)
    rw [hEcard]
    have : J.edgeFinset.card = 0 := by
      have := hω
      rw [hzero] at this
      omega
    omega
  -- the awarded model
  have hXpos : 0 < X.card := Finset.card_pos.2 hXne
  set f : Fin X.card → Fin m := fun i => ((X.equivFin.symm i : {z // z ∈ X}) : Fin m) with hfdef
  have hfX : ∀ i, f i ∈ X := fun i => (X.equivFin.symm i).2
  have hfinj : Function.Injective f := fun i j hij =>
    X.equivFin.symm.injective (Subtype.ext hij)
  set gg : Fin m → Fin X.card := fun z => if h : z ∈ X then X.equivFin ⟨z, h⟩ else ⟨0, hXpos⟩
    with hggdef
  have hfg : ∀ z ∈ X, f (gg z) = z := by
    intro z hz
    simp [hfdef, hggdef, hz]
  set bset : Fin X.card → Set (Fin n) :=
    fun i => ball H ω (stepDepth a) (M.center (f i)) (f i) with hbset
  set Mg : SimpleGraph (Fin X.card) :=
    { Adj := fun i j => i ≠ j ∧ ∃ u ∈ bset i, ∃ v ∈ bset j, H.Adj u v
      symm := by
        rintro i j ⟨hne, u, hu, v, hv, huv⟩
        exact ⟨hne.symm, v, hv, u, hu, huv.symm⟩
      loopless := ⟨fun i h => h.1 rfl⟩ } with hMg
  have hMgadj : ∀ i j, Mg.Adj i j ↔ (i ≠ j ∧ ∃ u ∈ bset i, ∃ v ∈ bset j, H.Adj u v) :=
    fun _ _ => Iff.rfl
  have hminor : HasShallowMinor H (stepDepth a) Mg :=
    hasShallowMinor_iff.2 ⟨{
      branch := bset
      center := fun i => M.center (f i)
      center_mem := fun i => center_mem_ball ((hmemX _).1 (hfX i))
      disjoint := fun i j hij => Set.disjoint_left.2 fun z hzi hzj =>
        hij (hfinj ((award_eq_of_mem_ball hzi).symm.trans (award_eq_of_mem_ball hzj)))
      radius_le := fun i x hx => ball_radius hx
      adj := fun i j h => ((hMgadj i j).1 h).2 }⟩
  have hMgcard : Mg.edgeSet.ncard ≤ D₁ * X.card :=
    hasDensityAtMost_iff.1 hdens X.card Mg hminor
  -- the surviving edges inject into the edges of the model
  have hRle : (survivors J.edgeFinset T g ω).card ≤ Mg.edgeSet.ncard := by
    have hinj : Set.InjOn (fun e => s(gg (rep e).1, gg (rep e).2))
        ↑(survivors J.edgeFinset T g ω) := by
      intro e he e' he' hee
      obtain ⟨h1, h2⟩ := hendX e he
      obtain ⟨h1', h2'⟩ := hendX e' he'
      rw [← hrep e, ← hrep e']
      rcases Sym2.eq_iff.1 hee with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [show (rep e).1 = (rep e').1 by rw [← hfg _ h1, ← hfg _ h1', ha],
          show (rep e).2 = (rep e').2 by rw [← hfg _ h2, ← hfg _ h2', hb]]
      · rw [show (rep e).1 = (rep e').2 by rw [← hfg _ h1, ← hfg _ h2', ha],
          show (rep e).2 = (rep e').1 by rw [← hfg _ h2, ← hfg _ h1', hb]]
        exact Sym2.eq_swap
    have himg : ((survivors J.edgeFinset T g ω).image
        (fun e => s(gg (rep e).1, gg (rep e).2))).card = (survivors J.edgeFinset T g ω).card :=
      Finset.card_image_of_injOn hinj
    have hsub : (↑((survivors J.edgeFinset T g ω).image
        (fun e => s(gg (rep e).1, gg (rep e).2))) : Set (Sym2 (Fin X.card))) ⊆ Mg.edgeSet := by
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨e, he, rfl⟩ := hx
      obtain ⟨heE, hagree⟩ := mem_survivors.1 he
      obtain ⟨h1, h2⟩ := hendX e he
      obtain ⟨-, -, -, -, hreal⟩ := hTreal e (hadj_of_mem e heE)
      obtain ⟨u, hu, v, hv, huv⟩ := hreal ω hagree
      refine (SimpleGraph.mem_edgeSet Mg).2 ((hMgadj _ _).2 ⟨?_, ?_⟩)
      · intro hc
        exact J.ne_of_adj (hadj_of_mem e heE)
          (by rw [← hfg _ h1, ← hfg _ h2, hc])
      · refine ⟨u, ?_, v, ?_, huv⟩
        · show u ∈ ball H ω (stepDepth a) (M.center (f (gg (rep e).1))) (f (gg (rep e).1))
          rw [hfg _ h1]
          exact ball_mono (by rw [stepDepth]; omega) hu
        · show v ∈ ball H ω (stepDepth a) (M.center (f (gg (rep e).2))) (f (gg (rep e).2))
          rw [hfg _ h2]
          exact ball_mono (by rw [stepDepth]; omega) hv
    calc (survivors J.edgeFinset T g ω).card = _ := himg.symm
      _ ≤ Mg.edgeSet.ncard := by
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hEcard]
  calc J.edgeFinset.card ≤ (d + 2) ^ (6 * a + 6) * (survivors J.edgeFinset T g ω).card := hω
    _ ≤ (d + 2) ^ (6 * a + 6) * (D₁ * X.card) :=
        Nat.mul_le_mul_left _ (hRle.trans hMgcard)
    _ ≤ stepFactor d a * (D₁ * m) := by
        rw [stepFactor]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
          (le_trans (Finset.card_le_univ X) (by simp)))
    _ = stepFactor d a * D₁ * m := by ring

/-! ### The chain bookkeeping

Iterating the transfer `i` times bounds the depth-`a` density of the
`i`-th round's graph by the depth-`chainDepth i a` density of `G`, times
`chainDens`, a product of one factor per earlier round.  Only the
in-degree bounds of the rounds *before* `i` enter — which is what lets
the density recursion and the in-degree recursion of a greedy chain be
run as one joint induction. -/

/-- The depth in `G` needed for depth `a` at round `i`. -/
def chainDepth : ℕ → ℕ → ℕ
  | 0, a => a
  | i + 1, a => chainDepth i (stepDepth a)

/-- The density budget for depth `a` at round `i`, given the per-round
in-degree bounds `dd` and the depth-`chainDepth i a` density `D₁` of
`G`. -/
def chainDens (dd : ℕ → ℕ) (D₁ : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => D₁
  | i + 1, a => stepFactor (dd i) a * chainDens dd D₁ i (stepDepth a)

/-- The factor the budget of round `i` costs: one `stepFactor` per
earlier round, depending only on the in-degrees of those rounds. -/
def chainConst (dd : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | i + 1, a => stepFactor (dd i) a * chainConst dd i (stepDepth a)

/-- The density budget is linear in the density of `G`: it is
`poly(d₀, …, d_{i-1}) · D₁`. -/
theorem chainDens_eq (dd : ℕ → ℕ) (D₁ : ℕ) :
    ∀ i a, chainDens dd D₁ i a = chainConst dd i a * D₁
  | 0, _ => (one_mul D₁).symm
  | i + 1, a => by
      rw [show chainDens dd D₁ (i + 1) a
            = stepFactor (dd i) a * chainDens dd D₁ i (stepDepth a) from rfl,
        show chainConst dd (i + 1) a
            = stepFactor (dd i) a * chainConst dd i (stepDepth a) from rfl,
        chainDens_eq dd D₁ i (stepDepth a), mul_assoc]

theorem chainDepth_mono_depth {a b : ℕ} (hab : a ≤ b) :
    ∀ i, chainDepth i a ≤ chainDepth i b
  | 0 => hab
  | i + 1 => chainDepth_mono_depth (stepDepth_mono hab) i

theorem chainDepth_mono_round (a : ℕ) {i j : ℕ} (hij : i ≤ j) :
    chainDepth i a ≤ chainDepth j a := by
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · refine (ih (by omega)).trans ?_
        rw [show chainDepth (j + 1) a = chainDepth j (stepDepth a) from rfl]
        exact chainDepth_mono_depth (le_stepDepth a) j
      · rw [Nat.le_antisymm hij h]

/-- The underlying graph of an orientation of `G` is `G`. -/
theorem toGraph_eq_of_orients {G : SimpleGraph (Fin n)} {D : Orientation n}
    (h : D.Orients G) : D.toGraph = G := by
  ext u v
  exact (h u v).symm

/-- **Density along a chain.**  Along any augmentation chain whose rounds
have in-degrees `dd i`, the depth-`a` density of round `i` is bounded by
the depth-`chainDepth i a` density of `G`, times `chainDens`. -/
theorem chain_density {G : SimpleGraph (Fin n)} {D : ℕ → Orientation n}
    {r : ℕ} (hchain : IsAugChain G D r) {dd : ℕ → ℕ} (hdeg : ∀ i < r, (D i).InDegLE (dd i))
    {D₁ : ℕ} :
    ∀ i ≤ r, ∀ a : ℕ, HasDensityAtMost G (chainDepth i a) D₁ →
      HasDensityAtMost (D i).toGraph a (chainDens dd D₁ i a) := by
  intro i
  induction i with
  | zero =>
      intro _ a hG
      rw [toGraph_eq_of_orients hchain.1]
      exact hG
  | succ i ih =>
      intro hi a hG
      have hprev := ih (by omega) (stepDepth a) hG
      exact roundTransfer (D i).toGraph (D i) (D (i + 1)) (dd i) _ a (fun _ _ h => Or.inl h)
        (hchain.2 i (by omega)) (hdeg i (by omega)) hprev

/-! ### The joint recursion of a greedy chain

The in-degree bound of round `i + 1` needs the depth-1 density of round
`i`, and that density needs the in-degree bounds of the rounds before
`i`.  The two recursions therefore close as one: `joint` computes the
pair, and `greedy_chain_joint` is the single induction that establishes
both halves. -/

/-- The joint recursion: `(joint d D₁ i).1` is the in-degree budget of
round `i` of a greedy chain started at in-degree `d`, and
`(joint d D₁ i).2 a` the depth-`a` density budget of round `i`'s graph,
given the depth-`chainDepth i a` density `D₁` of `G`. -/
def joint (d D₁ : ℕ) : ℕ → ℕ × (ℕ → ℕ)
  | 0 => (d, fun _ => D₁)
  | i + 1 =>
      ((joint d D₁ i).1 + (joint d D₁ i).1 * (joint d D₁ i).1 +
          ((joint d D₁ i).1 * (joint d D₁ i).1 + (joint d D₁ i).1 * (joint d D₁ i).2 1),
        fun a => stepFactor (joint d D₁ i).1 a * (joint d D₁ i).2 (stepDepth a))

/-- **The joint induction.**  Along a greedy chain, round `i` has
in-degree at most `(joint d D₁ i).1`, and its graph has depth-`a` density
at most `(joint d D₁ i).2 a`. -/
theorem greedy_chain_joint {G : SimpleGraph (Fin n)}
    {D : ℕ → Orientation n} {r d D₁ : ℕ} (hchain : IsAugChain G D r)
    (hgreedy : ∀ i < r, GreedyFratRound (D i) (D (i + 1))) (hd0 : (D 0).InDegLE d)
    (hG : HasDensityAtMost G (chainDepth r 1) D₁) :
    ∀ i ≤ r, (D i).InDegLE (joint d D₁ i).1 ∧
      ∀ a : ℕ, HasDensityAtMost G (chainDepth i a) D₁ →
        HasDensityAtMost (D i).toGraph a ((joint d D₁ i).2 a) := by
  intro i
  induction i with
  | zero =>
      intro _
      refine ⟨hd0, fun a hGa => ?_⟩
      rw [toGraph_eq_of_orients hchain.1]
      exact hGa
  | succ i ih =>
      intro hi
      obtain ⟨hdeg, hdens⟩ := ih (by omega)
      have hdens1 : HasDensityAtMost (D i).toGraph 1 ((joint d D₁ i).2 1) :=
        hdens 1 (hasDensityAtMost_mono_depth (chainDepth_mono_round 1 (by omega : i ≤ r)) hG)
      refine ⟨?_, fun a hGa => ?_⟩
      · have hlow : LowDegreeVertices (fratGraph (D i))
            ((joint d D₁ i).1 * (joint d D₁ i).1 + (joint d D₁ i).1 * (joint d D₁ i).2 1) :=
          fratGraph_lowDegreeVertex (fun _ _ h => Or.inl h) hdeg hdens1
        obtain ⟨σ, hσ, hor⟩ := hgreedy i (by omega) _ hlow
        exact inDegLE_of_augStep (hchain.2 i (by omega)) hdeg (fratIn_le_of_backDegLE hσ hor)
      · exact roundTransfer (D i).toGraph (D i) (D (i + 1)) _ _ a (fun _ _ h => Or.inl h)
          (hchain.2 i (by omega)) hdeg (hdens (stepDepth a) hGa)

/-- The in-degree half of the joint induction: the recursion the greedy
algorithm runs, now unconditional in the density input. -/
theorem greedy_chain_joint_inDegLE {G : SimpleGraph (Fin n)}
    {D : ℕ → Orientation n} {r d D₁ : ℕ} (hchain : IsAugChain G D r)
    (hgreedy : ∀ i < r, GreedyFratRound (D i) (D (i + 1))) (hd0 : (D 0).InDegLE d)
    (hG : HasDensityAtMost G (chainDepth r 1) D₁) :
    ∀ i ≤ r, (D i).InDegLE (joint d D₁ i).1 :=
  fun i hi => (greedy_chain_joint hchain hgreedy hd0 hG i hi).1

/-! ### Nowhere dense hosts

`Lax12`'s density theorem gives `c · m ^ (1 + δ)` edges for the depth-`b`
minors of a member; on a subgraph of a member with `m` vertices that is
`⌈c · m ^ δ⌉ · k` edges on `k` vertices, since a minor has no more
vertices than its host.  That is the numeric shape `HasDensityAtMost`
asks for. -/

/-- Every subgraph of a member of a nowhere dense class has depth-`b`
density at most `⌈c · m ^ δ⌉`, for a constant `c` depending only on the
class, the depth and `δ`. -/
theorem exists_densityAtMost_of_nowhereDense (C : GraphClass) (hC : NowhereDense C) (b : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        HasDensityAtMost G b ⌈c * (m : ℝ) ^ δ⌉₊ := by
  obtain ⟨c, hc⟩ :=
    hasSubpolynomialDensity_iff.1
      (Lax12Proofs.NowhereDenseDensity.hasSubpolynomialDensity_of_nowhereDense C hC) b δ hδ
  refine ⟨max c 0, fun n Gn hGn m G hsub => hasDensityAtMost_iff.2 (fun k J hJ => ?_)⟩
  have hkm : k ≤ m := by
    simpa using Lax12Proofs.MinorBridge.card_le_of_hasShallowMinor hJ
  have hbound := hc n Gn hGn k J (Lax12Proofs.MinorBridge.hasShallowMinor_of_copy hsub hJ)
  have hc0 : (0 : ℝ) ≤ max c 0 := le_max_right _ _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hle : ((J.edgeSet.ncard : ℕ) : ℝ) ≤ 0 := by
      simpa [Real.zero_rpow (by positivity : (1 : ℝ) + δ ≠ 0)] using hbound
    have hzero : J.edgeSet.ncard = 0 := by
      exact_mod_cast le_antisymm hle (by positivity)
    simp [hzero]
  · have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hsplit : (k : ℝ) ^ (1 + δ) = (k : ℝ) * (k : ℝ) ^ δ := by
      rw [Real.rpow_add hk0, Real.rpow_one]
    have hmono : (k : ℝ) ^ δ ≤ (m : ℝ) ^ δ :=
      Real.rpow_le_rpow (le_of_lt hk0) (by exact_mod_cast hkm) (le_of_lt hδ)
    have hfinal : ((J.edgeSet.ncard : ℕ) : ℝ) ≤ (⌈max c 0 * (m : ℝ) ^ δ⌉₊ : ℝ) * (k : ℝ) :=
      calc ((J.edgeSet.ncard : ℕ) : ℝ) ≤ c * (k : ℝ) ^ (1 + δ) := hbound
        _ ≤ max c 0 * (k : ℝ) ^ (1 + δ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ = (max c 0 * (k : ℝ) ^ δ) * (k : ℝ) := by rw [hsplit]; ring
        _ ≤ (max c 0 * (m : ℝ) ^ δ) * (k : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hc0) (le_of_lt hk0)
        _ ≤ (⌈max c 0 * (m : ℝ) ^ δ⌉₊ : ℝ) * (k : ℝ) :=
            mul_le_mul_of_nonneg_right (Nat.le_ceil _) (le_of_lt hk0)
    exact_mod_cast hfinal

/-! ### Monotonicity of the budgets -/

theorem one_le_stepFactor (d a : ℕ) : 1 ≤ stepFactor d a :=
  Nat.one_le_pow _ _ (by omega)

theorem stepFactor_mono_depth (d : ℕ) {a b : ℕ} (hab : a ≤ b) : stepFactor d a ≤ stepFactor d b :=
  Nat.pow_le_pow_right (by omega) (by omega)

theorem chainDens_mono_depth (dd : ℕ → ℕ) (D₁ : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∀ i, chainDens dd D₁ i a ≤ chainDens dd D₁ i b
  | 0 => le_rfl
  | i + 1 =>
      Nat.mul_le_mul (stepFactor_mono_depth _ hab)
        (chainDens_mono_depth dd D₁ (stepDepth_mono hab) i)

theorem chainDens_mono_round (dd : ℕ → ℕ) (D₁ a : ℕ) {i j : ℕ} (hij : i ≤ j) :
    chainDens dd D₁ i a ≤ chainDens dd D₁ j a := by
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · refine (ih (by omega)).trans ?_
        rw [show chainDens dd D₁ (j + 1) a
              = stepFactor (dd j) a * chainDens dd D₁ j (stepDepth a) from rfl]
        exact (chainDens_mono_depth dd D₁ (le_stepDepth a) j).trans
          (Nat.le_mul_of_pos_left _ (one_le_stepFactor _ _))
      · rw [Nat.le_antisymm hij h]

/-! ### The augmented density theorem -/

/-- **The augmented density theorem.**  For every nowhere dense class
`C`, every number of rounds `r` and every `δ > 0` there is a constant `c`
such that: on every subgraph `G` of a member, on `m` vertices, every
`r`-round augmentation chain whose rounds have in-degrees `dd i` has

```
∇₁((D i).toGraph) ≤ chainDens dd ⌈c · m ^ δ⌉ i 1
```

for every `i ≤ r`.  The budget for round `i` mentions only the in-degrees
of the rounds *before* `i`, which is what the greedy recursion needs. -/
theorem exists_chain_density (C : GraphClass) (hC : NowhereDense C)
    (r : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ (D : ℕ → Orientation m) (dd : ℕ → ℕ), IsAugChain G D r →
          (∀ i < r, (D i).InDegLE (dd i)) →
          ∀ i ≤ r, HasDensityAtMost (D i).toGraph 1 (chainDens dd ⌈c * (m : ℝ) ^ δ⌉₊ i 1) := by
  obtain ⟨c, hc⟩ := exists_densityAtMost_of_nowhereDense C hC (chainDepth r 1) δ hδ
  exact ⟨c, fun n Gn hGn m G hsub D dd hchain hdeg i hi =>
    chain_density hchain hdeg i hi 1
      (hasDensityAtMost_mono_depth (chainDepth_mono_round 1 hi) (hc n Gn hGn m G hsub))⟩

/-- The hypothesis `AugmentedDepthOneDensity` of `Augmentation`,
discharged: on a nowhere dense class every chain with per-round
in-degrees `dd i` has subpolynomial depth-1 density in all of its
rounds. -/
theorem exists_augmentedDepthOneDensity (C : GraphClass)
    (hC : NowhereDense C) (r : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ (D : ℕ → Orientation m) (dd : ℕ → ℕ), IsAugChain G D r →
          (∀ i < r, (D i).InDegLE (dd i)) →
          AugmentedDepthOneDensity D r (chainDens dd ⌈c * (m : ℝ) ^ δ⌉₊ r 1) := by
  obtain ⟨c, hc⟩ := exists_chain_density C hC r δ hδ
  refine ⟨c, fun n Gn hGn m G hsub D dd hchain hdeg i hi => ?_⟩
  exact hasDensityAtMost_mono (chainDens_mono_round dd _ 1 (le_of_lt hi))
    (hc n Gn hGn m G hsub D dd hchain hdeg i (le_of_lt hi))

/-- **The greedy chain, unconditionally.**  On a nowhere dense class the
in-degrees of a greedy chain follow the joint recursion: no density
hypothesis is left. -/
theorem exists_greedy_chain_inDegLE (C : GraphClass) (hC : NowhereDense C)
    (r : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ (D : ℕ → Orientation m) (d : ℕ), IsAugChain G D r →
          (∀ i < r, GreedyFratRound (D i) (D (i + 1))) → (D 0).InDegLE d →
          ∀ i ≤ r, (D i).InDegLE (joint d ⌈c * (m : ℝ) ^ δ⌉₊ i).1 := by
  obtain ⟨c, hc⟩ := exists_densityAtMost_of_nowhereDense C hC (chainDepth r 1) δ hδ
  exact ⟨c, fun n Gn hGn m G hsub D d hchain hgreedy hd0 =>
    greedy_chain_joint_inDegLE hchain hgreedy hd0 (hc n Gn hGn m G hsub)⟩

end Lax3Proofs.AugmentedDensity
