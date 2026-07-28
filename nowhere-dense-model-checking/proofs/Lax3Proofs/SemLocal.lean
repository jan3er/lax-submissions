import Lax3Proofs.Horizon
import Lax3Proofs.WalkDistance

/-!
The source's semantic locality lemma (arXiv:2606.23180,
`lem:ltp-local-subgraph`): a *local* formula of distance rank `(k, q)` —
one that quantifies only locally — is semantically ρ⁻(k, q)-local, that
is, its truth on a tuple is decided already by the ρ⁻(k, q)-neighborhood
of that tuple.

The lemma is proved through a strengthening,
`sat_iff_satWithin_of_ball_subset`: satisfaction and satisfaction
relativized to a vertex set `D` agree at *every* `D` that contains the
ρ⁻(k, q)-ball around every entry of the tuple, not only at the union of
those balls. Semantic locality is the instance `D = ⋃ i, ball G r (m i)`
of that statement, and the extra room is what lets the induction pass
the *same* `D` to a subformula whose own horizon is smaller.

Carrying an arbitrary `D` also replaces the source's evaluation-trace
bookkeeping. The source bounds the distance from the tuple to a variable
introduced after `j` local quantifiers by the telescoping sum
∑_{h ≤ j} ρ⁺(k+h, q−h) and compares it with the radius ρ⁻(k+j, q−j) that
atoms in the scope of those quantifiers may carry. Here that sum never
appears: each local quantifier consumes one of its summands, in the step
that re-establishes the invariant for the extended tuple. A local
quantifier of a rank-`(k, q+1)` formula guards at radius at most
ρ⁺(k+1, q), so the ρ⁻(k+1, q)-ball around the new vertex lies inside the
ρ⁻(k, q+1)-ball around the vertex that guarded it — this is
`Horizon.rhoPlus_add_rhoMinus_le`, one step of the telescope — while the
old entries of the tuple keep their invariant by
`Horizon.rhoMinus_succ_left_le`. Nothing else about the horizon
functions is used.

# Formalization notes

Both statements come in two forms. In `semLocal` and
`sat_iff_satWithin_of_ball_subset` the rank's first argument is the
arity of the formula; in the primed `semLocal'` and
`sat_iff_satWithin_of_ball_subset'` it is an independent parameter, as
`DRank` allows and as the source intends — its "at most `k` free
variables" is a bound, not a count. The primed forms are what is
actually proved: the induction never inspects the arity, and every step
of it is an inequality between horizon values at the rank. The unprimed
forms are their diagonal instances, and are the ones to quote when the
two agree.

**The lemma is proved for every `k`, including `k = 0`; the source
assumes `k ≥ 1`.** The source's hypothesis is needed because for a
sentence its relativization is to the empty neighborhood, hence to the
empty structure, which is a genuinely different structure: an ordinary
first-order sentence such as ∃x (x = x) tells the two apart. It does not
bite here, because on *local* sentences `Sat` and `SatWithin ∅` cannot
be told apart. With no free variables there is no atom to write down at
all — the atoms take variables from the empty `Fin 0` — and a local
quantifier is guarded by a disjunction over the free variables, which is
empty and therefore false; so a local sentence is a boolean combination
of formulas that are false under `Sat` and false under `SatWithin ∅`
alike, for the same reason. That reading of `exL` at `k = 0` is the
frozen semantics of `Lax3.DistFO` and is deliberate there. Dropping the
hypothesis is therefore a strengthening, and the `k = 0` case needs no
separate argument: the induction below never inspects `k`, and its
local-quantifier case is vacuous when there is no free variable to
supply a guard.

The unrestricted-quantifier case of the induction is discharged by
`IsLocal`, which is `False` there — the one place where locality of the
formula is used, and the reason the lemma is about local formulas only.

`Sat`, `SatWithin` and `IsLocal` are unfolded definitionally — by
`exact` against the unfolded shape — and never by `simp only [Sat]`.
Simplifying with the equation lemmas of a concept-side definition
manufactures its match splitters, which are named in the *concept's*
namespace but are elaborated, and hence recorded, in whichever proof
module first asks for them; the submission's namespace discipline
rejects that. All three definitions recurse structurally, so the
definitional route costs nothing.
-/

namespace Lax3Proofs.SemLocal

open Lax3.ColoredGraphs Lax3.DistFO
open Lax3Proofs.Horizon Lax3Proofs.WalkDistance

/-! ### Walks inside a ball -/

/-- Every vertex on a walk is within the walk's length of its start. -/
theorem withinDist_of_mem_support {V : Type*} {G : SimpleGraph V} {u v x : V}
    (p : G.Walk u v) (hx : x ∈ p.support) : WithinDist G p.length u x := by
  classical
  have hlen := congrArg SimpleGraph.Walk.length (p.take_spec hx)
  rw [SimpleGraph.Walk.length_append] at hlen
  exact ⟨p.takeUntil x hx, by omega⟩

/-- A walk of length at most `d` never leaves the ball of radius `d`
around its start. -/
theorem support_subset_ball {V : Type*} {G : SimpleGraph V} {u v : V} {d : ℕ}
    (p : G.Walk u v) (hp : p.length ≤ d) {x : V} (hx : x ∈ p.support) :
    x ∈ ball G d u :=
  withinDist_mono_radius hp (withinDist_of_mem_support p hx)

/-- Distance inside `D` is distance: forgetting the containment leaves a
walk of the same length. -/
theorem withinDist_of_withinDistIn {V : Type*} {G : SimpleGraph V} {D : Set V} {d : ℕ}
    {u v : V} (h : WithinDistIn D G d u v) : WithinDist G d u v := by
  obtain ⟨p, hp, -⟩ := h
  exact ⟨p, hp⟩

/-- Conversely, a distance bound below the radius of a ball contained in
`D` already holds inside `D`: the witnessing walk is too short to leave
the ball. -/
theorem withinDistIn_of_withinDist {V : Type*} {G : SimpleGraph V} {D : Set V} {d r : ℕ}
    {u v : V} (hr : r ≤ d) (hball : ball G d u ⊆ D) (h : WithinDist G r u v) :
    WithinDistIn D G r u v := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp, fun x hx => hball (support_subset_ball p (hp.trans hr) hx)⟩

/-! ### Inverting the distance rank -/

/-- The radius of a binary distance atom of distance rank `(k', q)`. -/
theorem le_rhoMinus_of_distLe {L k k' q r : ℕ} {i j : Fin k}
    (h : DRank k' q (DistFO.distLe (L := L) r i j)) : r ≤ rhoMinus k' q := by
  cases h with
  | distLe _ _ hr => exact hr

/-- The radius of a unary distance atom of distance rank `(k', q)`. -/
theorem le_rhoMinus_of_distColorLt {L k k' q r : ℕ} {c : Fin L} {i : Fin k}
    (h : DRank k' q (DistFO.distColorLt r c i)) : r ≤ rhoMinus k' q := by
  cases h with
  | distColorLt _ _ hr => exact hr

/-- Negation preserves the distance rank, downwards. -/
theorem drank_of_not {L k k' q : ℕ} {φ : DistFO L k} (h : DRank k' q φ.not) :
    DRank k' q φ := by
  cases h with
  | not h => exact h

/-- Conjunction preserves the distance rank, downwards. -/
theorem drank_of_and_left {L k k' q : ℕ} {φ ψ : DistFO L k} (h : DRank k' q (φ.and ψ)) :
    DRank k' q φ := by
  cases h with
  | and h _ => exact h

/-- Conjunction preserves the distance rank, downwards. -/
theorem drank_of_and_right {L k k' q : ℕ} {φ ψ : DistFO L k} (h : DRank k' q (φ.and ψ)) :
    DRank k' q ψ := by
  cases h with
  | and _ h => exact h

/-- A local quantifier of distance rank `(k', q)` has a positive
quantifier budget, guards at radius at most ρ⁺ one level in, and has a
body of distance rank one level in. -/
theorem exists_drank_of_exL {L k k' q r : ℕ} {φ : DistFO L (k + 1)}
    (h : DRank k' q (DistFO.exL r φ)) :
    ∃ q', q = q' + 1 ∧ DRank (k' + 1) q' φ ∧ r ≤ rhoPlus (k' + 1) q' := by
  cases h with
  | exL h hr => exact ⟨_, rfl, h, hr⟩

/-! ### Semantic locality -/

/-- The induction behind `sat_iff_satWithin_of_ball_subset`, stated with
every parameter of the induction quantified inside so that the induction
hypothesis is available at the rank, tuple and vertex set of the
subformula. -/
private theorem sat_iff_satWithin_aux {L n : ℕ} (G : SimpleGraph (Fin n))
    (col : Coloring n L) :
    ∀ {k : ℕ} (φ : DistFO L k) (k' q : ℕ) (m : Fin k → Fin n) (D : Set (Fin n)),
      IsLocal φ → DRank k' q φ → (∀ i, ball G (rhoMinus k' q) (m i) ⊆ D) →
      (Sat G col m φ ↔ SatWithin D G col m φ) := by
  intro k φ
  induction φ with
  | adj i j =>
    intro k' q m D _ _ hD
    exact ⟨fun h => ⟨h, hD i (mem_ball_self G _ _), hD j (mem_ball_self G _ _)⟩, fun h => h.1⟩
  | eq i j =>
    intro k' q m D _ _ _
    exact Iff.rfl
  | color c i =>
    intro k' q m D _ _ hD
    exact ⟨fun h => ⟨h, hD i (mem_ball_self G _ _)⟩, fun h => h.1⟩
  | distLe r i j =>
    intro k' q m D _ hφ hD
    have hr := le_rhoMinus_of_distLe hφ
    exact ⟨withinDistIn_of_withinDist hr (hD i), withinDist_of_withinDistIn⟩
  | distColorLt r c i =>
    intro k' q m D _ hφ hD
    have hr := le_rhoMinus_of_distColorLt hφ
    constructor
    · rintro ⟨y, hy, p, hp⟩
      have hsub : ∀ x ∈ p.support, x ∈ D := fun x hx =>
        hD i (support_subset_ball p (hp.trans_le hr).le hx)
      exact ⟨y, hy, hsub y p.end_mem_support, p, hp, hsub⟩
    · rintro ⟨y, hy, -, p, hp, -⟩
      exact ⟨y, hy, p, hp⟩
  | not ψ ih =>
    intro k' q m D hloc hφ hD
    exact not_congr (ih k' q m D hloc (drank_of_not hφ) hD)
  | and ψ χ ihψ ihχ =>
    intro k' q m D hloc hφ hD
    exact and_congr (ihψ k' q m D hloc.1 (drank_of_and_left hφ) hD)
      (ihχ k' q m D hloc.2 (drank_of_and_right hφ) hD)
  | exU ψ _ =>
    intro k' q m D hloc _ _
    -- `IsLocal` is `False` at an unrestricted quantifier
    exact False.elim hloc
  | exL r ψ ih =>
    -- the induction generalized the arity; `k` names it in this case
    rename_i k
    intro k' q m D hloc hφ hD
    obtain ⟨q', rfl, hψ, hr⟩ := exists_drank_of_exL hφ
    -- the guard radius is below the horizon of the whole formula
    have hrle : r ≤ rhoMinus k' (q' + 1) := hr.trans (rhoPlus_le_rhoMinus k' q')
    -- One telescoping step: whichever free variable guarded the new vertex `v`,
    -- the invariant survives the extension of the tuple by `v`.
    have key : ∀ (i : Fin k) (v : Fin n), WithinDist G r (m i) v →
        ∀ j : Fin (k + 1),
          ball G (rhoMinus (k' + 1) q') ((Fin.snoc m v : Fin (k + 1) → Fin n) j) ⊆ D := by
      intro i v hv j
      induction j using Fin.lastCases with
      | last =>
        -- the new entry: ρ⁺(k'+1, q') + ρ⁻(k'+1, q') ≤ ρ⁻(k', q'+1)
        rw [Fin.snoc_last]
        intro x hx
        exact hD i (withinDist_mono_radius (rhoPlus_add_rhoMinus_le k' q')
          (withinDist_trans (withinDist_mono_radius hr hv) (mem_ball.mp hx)))
      | cast i' =>
        -- an old entry: its ball only shrank, by ρ⁻(k'+1, q') ≤ ρ⁻(k', q'+1)
        rw [Fin.snoc_castSucc]
        exact (ball_mono_radius G (m i') (rhoMinus_succ_left_le k' q')).trans (hD i')
    constructor
    · rintro ⟨v, ⟨i, hiv⟩, hsat⟩
      exact ⟨v, hD i (withinDist_mono_radius hrle hiv),
        ⟨i, withinDistIn_of_withinDist hrle (hD i) hiv⟩,
        (ih (k' + 1) q' (Fin.snoc m v) D hloc hψ (key i v hiv)).mp hsat⟩
    · rintro ⟨v, -, ⟨i, hiv⟩, hsat⟩
      have hiv' : WithinDist G r (m i) v := withinDist_of_withinDistIn hiv
      exact ⟨v, ⟨i, hiv'⟩, (ih (k' + 1) q' (Fin.snoc m v) D hloc hψ (key i v hiv')).mpr hsat⟩

/-- **Semantic locality, in the form the induction proves.** A local
formula of distance rank `(k', q)` cannot tell the graph apart from the
substructure induced on any vertex set `D` that contains the
ρ⁻(k', q)-ball around every entry of the tuple. The rank argument `k'`
is a bound on the number of free variables and is independent of the
arity, as `DRank` allows; the induction never looks at the arity. -/
theorem sat_iff_satWithin_of_ball_subset' {L n : ℕ} (G : SimpleGraph (Fin n))
    (col : Coloring n L) {k k' q : ℕ} {φ : DistFO L k}
    (hloc : IsLocal φ) (hφ : DRank k' q φ) (m : Fin k → Fin n) {D : Set (Fin n)}
    (hD : ∀ i, ball G (rhoMinus k' q) (m i) ⊆ D) :
    Sat G col m φ ↔ SatWithin D G col m φ :=
  sat_iff_satWithin_aux G col φ k' q m D hloc hφ hD

/-- **Semantic locality, in the form the induction proves**, at a rank
whose first argument is the arity. -/
theorem sat_iff_satWithin_of_ball_subset {L n : ℕ} (G : SimpleGraph (Fin n))
    (col : Coloring n L) {k q : ℕ} {φ : DistFO L k}
    (hloc : IsLocal φ) (hφ : DRank k q φ) (m : Fin k → Fin n) {D : Set (Fin n)}
    (hD : ∀ i, ball G (rhoMinus k q) (m i) ⊆ D) :
    Sat G col m φ ↔ SatWithin D G col m φ :=
  sat_iff_satWithin_of_ball_subset' G col hloc hφ m hD

/-- **The source's Lemma `lem:ltp-local-subgraph`.** A local formula of
distance rank `(k', q)` is semantically ρ⁻(k', q)-local: its truth on a
tuple is unchanged by discarding every vertex further than ρ⁻(k', q)
from that tuple. -/
theorem semLocal' {L : ℕ} {k k' q : ℕ} (φ : DistFO L k)
    (hloc : IsLocal φ) (hφ : DRank k' q φ) :
    SemanticallyLocal (rhoMinus k' q) φ := fun _ G col m =>
  sat_iff_satWithin_of_ball_subset' G col hloc hφ m
    (Set.subset_iUnion fun i => ball G (rhoMinus k' q) (m i))

/-- **The source's Lemma `lem:ltp-local-subgraph`** at a rank whose
first argument is the arity. -/
theorem semLocal {L : ℕ} {k q : ℕ} (φ : DistFO L k)
    (hloc : IsLocal φ) (hφ : DRank k q φ) :
    SemanticallyLocal (rhoMinus k q) φ :=
  semLocal' φ hloc hφ

end Lax3Proofs.SemLocal
