import Lax3.DistFO
import Lax3Proofs.SyntaxLemmas
import Lax3Proofs.WalkDistance
import Lax3Proofs.SplitterBasics

/-!
The **relativization rewrite**: a syntactic translation `rel` that turns
satisfaction *inside* a vertex subset into plain satisfaction over the
arena with the complement of that subset isolated.

The evaluator of this submission reads a formula's truth inside a
cluster of a neighborhood cover. Semantic locality
(`Lax3Proofs.SemLocal`) says that a local formula of distance rank
`(k, q)` cannot tell the whole arena from the substructure induced on
any set containing the ρ⁻-balls around its tuple, so the evaluator may
replace `Sat A col m β` by `SatWithin X A col m β` for a cluster `X`
holding those balls. But `SatWithin` is not the shape the recursion
runs on: to isolate a splitter batch inside the cluster and descend, the
evaluator needs a *plain* satisfaction statement over a *smaller arena*.
That is what `rel` provides — it rewrites `β` into a formula which, over
the arena `deleteVerts A Xᶜ` with the outside of the cluster isolated,
says exactly what `β` said inside the cluster. The cluster survives the
move only as data: a marker color.

# Why every atom case is exact

Two devices remove all side conditions, so `sat_rel` holds at *every*
tuple, with no hypothesis relating the tuple to the cluster.

*The arena carries the edge conjuncts.* An edge of `deleteVerts A Xᶜ` is
an edge of `A` with both endpoints outside `Xᶜ`, that is, both endpoints
in the cluster — verbatim the conjuncts `SatWithin` puts on an adjacency
atom. Adjacency atoms therefore translate to themselves.

*The coloring carries the color conjuncts.* The target coloring is
assumed pre-intersected with the cluster, `col' (old c) = col c ∩ X`,
which is how the evaluator builds it anyway; a color atom translates to
a color atom with nothing added.

What neither device knows is where the isolated part of the arena is: an
isolated vertex is adjacent to nothing, but it is still within distance
`d` of itself, and the empty walk at it is a walk. The **marker color**
`col' mk = X` repairs exactly those endpoint cases. A binary distance
atom picks up a marker conjunct at each of its two endpoints, a unary one
at its single free endpoint, and each quantifier — unrestricted or local
— picks one up on the vertex it binds, which is what confines
quantification to the cluster. Nothing is needed away from the
endpoints: every edge of the isolated arena has both ends in `X`, so a
walk that starts in the cluster never leaves it. The two walk-conversion
lemmas below, `withinDistIn_of_withinDist_deleteVerts_compl` and
`withinDist_deleteVerts_compl_of_withinDistIn`, are that observation, and
everything the induction of `sat_rel` does with distances reduces to
them.

# Where it is used

In the evaluator's cluster step: for a cluster `X` of the cover,
`Lax3Proofs.SemLocal.sat_iff_satWithin_of_ball_subset'` moves from the
arena to the cluster, `sat_rel` moves from the cluster back to plain
satisfaction over the cluster arena, and the isolation rewrite of the
splitter batch then applies inside that arena. `drank_rel` and
`isLocal_rel` carry the two syntactic invariants the next level of the
recursion consumes: the translated formula has the same distance rank
and is again local, so semantic locality applies to it in turn.
-/

namespace Lax3Proofs.Relativize

open Lax3.ColoredGraphs Lax3.DistFO
open Lax12.UniformQuasiWideness
open Lax3Proofs.SyntaxLemmas Lax3Proofs.WalkDistance

/-! ### Walks in the isolated arena

Isolating the complement of `X` and staying inside `X` are the same
condition on a walk, once one endpoint is known to lie in `X`. Both
directions are proved at the level of walks, keeping the length, so that
the `≤ d` of a binary distance atom and the `< r` of a unary one read
off the same two lemmas.
-/

section Walks

variable {V : Type*} {A : SimpleGraph V} {X : Set V} {u v : V} {d : ℕ}

/-- A walk of the arena with `Xᶜ` isolated, one of whose endpoints lies
in `X`, is a walk of the original arena of the same length that stays
inside `X`. Every edge of the isolated arena has both ends in `X`, so
the containment propagates from the first vertex along the walk; a walk
of length zero is covered by either endpoint hypothesis. -/
theorem exists_walk_of_deleteVerts_compl (p : (deleteVerts A Xᶜ).Walk u v)
    (h : u ∈ X ∨ v ∈ X) :
    ∃ q : A.Walk u v, q.length = p.length ∧ ∀ x ∈ q.support, x ∈ X := by
  revert h
  induction p with
  | nil =>
    intro h
    exact ⟨.nil, rfl, by simpa using h.elim id id⟩
  | @cons a b c hab p ih =>
    intro _
    have ha : a ∈ X := Set.notMem_compl_iff.mp hab.2.1
    have hb : b ∈ X := Set.notMem_compl_iff.mp hab.2.2
    obtain ⟨q, hq, hqs⟩ := ih (Or.inl hb)
    refine ⟨.cons hab.1 q, by simp [hq], ?_⟩
    intro x hx
    rcases List.mem_cons.mp (by simpa using hx) with rfl | hx
    · exact ha
    · exact hqs x hx

/-- Conversely, a walk that stays inside `X` survives the isolation of
`Xᶜ`, at the same length: both ends of each of its edges lie in `X`. -/
theorem exists_walk_deleteVerts_compl (p : A.Walk u v) (hp : ∀ x ∈ p.support, x ∈ X) :
    ∃ q : (deleteVerts A Xᶜ).Walk u v, q.length = p.length :=
  exists_walk_deleteVerts p fun x hx => Set.notMem_compl_iff.mpr (hp x hx)

/-- A distance bound in the arena with `Xᶜ` isolated is a distance bound
inside `X`, as soon as one of the two vertices lies in `X`. The
hypothesis is exactly what the empty walk needs: an isolated vertex is
within every distance of itself. -/
theorem withinDistIn_of_withinDist_deleteVerts_compl
    (h : WithinDist (deleteVerts A Xᶜ) d u v) (hx : u ∈ X ∨ v ∈ X) :
    WithinDistIn X A d u v := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq, hqs⟩ := exists_walk_of_deleteVerts_compl p hx
  exact ⟨q, hq ▸ hp, hqs⟩

/-- A distance bound inside `X` is a distance bound in the arena with
`Xᶜ` isolated, with no side condition. -/
theorem withinDist_deleteVerts_compl_of_withinDistIn (h : WithinDistIn X A d u v) :
    WithinDist (deleteVerts A Xᶜ) d u v := by
  obtain ⟨p, hp, hps⟩ := h
  obtain ⟨q, hq⟩ := exists_walk_deleteVerts_compl p hps
  exact ⟨q, hq ▸ hp⟩

/-- The two distance notions agree once one endpoint is marked. This is
the form the local quantifier of `sat_rel` consumes, where the marker
conjunct of the body supplies the endpoint. -/
theorem withinDist_deleteVerts_compl_iff (hx : u ∈ X ∨ v ∈ X) :
    WithinDist (deleteVerts A Xᶜ) d u v ↔ WithinDistIn X A d u v :=
  ⟨fun h => withinDistIn_of_withinDist_deleteVerts_compl h hx,
    withinDist_deleteVerts_compl_of_withinDistIn⟩

/-- Both endpoints of a walk that stays inside `X` lie in `X`. -/
theorem mem_of_withinDistIn_left (h : WithinDistIn X A d u v) : u ∈ X := by
  obtain ⟨p, -, hps⟩ := h
  exact hps u p.start_mem_support

/-- The other endpoint, likewise. -/
theorem mem_of_withinDistIn_right (h : WithinDistIn X A d u v) : v ∈ X := by
  obtain ⟨p, -, hps⟩ := h
  exact hps v p.end_mem_support

end Walks

/-! ### The translation -/

variable {L L' n : ℕ}

/-- The relativization of a formula to a vertex subset recorded as the
marker color `mk`, with the old colors relocated along `old`.

Adjacency atoms are unchanged — the isolated arena's edges already carry
the membership conjuncts — and so are equality atoms; a color atom only
moves to its new slot, the coloring being assumed pre-intersected with
the subset. The marker conjuncts appear exactly where the isolated arena
cannot see the subset on its own: at the endpoints of a distance atom,
and at the vertex each quantifier binds, which is what restricts
quantification to the subset. -/
def rel (old : Fin L → Fin L') (mk : Fin L') : {k : ℕ} → DistFO L k → DistFO L' k
  | _, .adj i j => .adj i j
  | _, .eq i j => .eq i j
  | _, .color c i => .color (old c) i
  | _, .distLe d i j => .and (.distLe d i j) (.and (.color mk i) (.color mk j))
  | _, .distColorLt r c i => .and (.distColorLt r (old c) i) (.color mk i)
  | _, .not φ => .not (rel old mk φ)
  | _, .and φ ψ => .and (rel old mk φ) (rel old mk ψ)
  | k, .exU φ => .exU (.and (.color mk (Fin.last k)) (rel old mk φ))
  | k, .exL r g φ => .exL r g (.and (.color mk (Fin.last k)) (rel old mk φ))

section Clauses

variable (old : Fin L → Fin L') (mk : Fin L') {k : ℕ}

/-- Relativizing an adjacency atom changes nothing. -/
theorem rel_adj (i j : Fin k) : rel old mk (.adj i j) = (.adj i j : DistFO L' k) := rfl

/-- Relativizing an equality atom changes nothing. -/
theorem rel_eq (i j : Fin k) : rel old mk (.eq i j) = (.eq i j : DistFO L' k) := rfl

/-- Relativizing a color atom moves it to its new slot. -/
theorem rel_color (c : Fin L) (i : Fin k) :
    rel old mk (.color c i) = (.color (old c) i : DistFO L' k) := rfl

/-- Relativizing a binary distance atom marks both endpoints. -/
theorem rel_distLe (d : ℕ) (i j : Fin k) :
    rel old mk (.distLe d i j) =
      (.and (.distLe d i j) (.and (.color mk i) (.color mk j)) : DistFO L' k) := rfl

/-- Relativizing a unary distance atom marks its endpoint. -/
theorem rel_distColorLt (r : ℕ) (c : Fin L) (i : Fin k) :
    rel old mk (.distColorLt r c i) =
      (.and (.distColorLt r (old c) i) (.color mk i) : DistFO L' k) := rfl

/-- Relativizing a negation. -/
theorem rel_not (φ : DistFO L k) : rel old mk (.not φ) = .not (rel old mk φ) := rfl

/-- Relativizing a conjunction. -/
theorem rel_and (φ ψ : DistFO L k) :
    rel old mk (.and φ ψ) = .and (rel old mk φ) (rel old mk ψ) := rfl

/-- Relativizing an unrestricted quantifier marks the bound vertex. -/
theorem rel_exU (φ : DistFO L (k + 1)) :
    rel old mk (.exU φ) = .exU (.and (.color mk (Fin.last k)) (rel old mk φ)) := rfl

/-- Relativizing a local quantifier marks the bound vertex and keeps
both the radius and the guard set. -/
theorem rel_exL (r : ℕ) (g : Finset (Fin k)) (φ : DistFO L (k + 1)) :
    rel old mk (.exL r g φ) =
      .exL r g (.and (.color mk (Fin.last k)) (rel old mk φ)) := rfl

end Clauses

/-! ### Correctness -/

/-- **The relativization rewrite.** Over the arena with the complement
of `X` isolated and a coloring that carries the old colors
pre-intersected with `X` and `X` itself as the marker `mk`, the
relativized formula says exactly what the original formula says inside
`X`.

There is no hypothesis on the tuple `m`: the marker conjuncts make every
atom case an equivalence rather than an implication, so the statement is
uniform in the tuple, as the evaluator needs it to be. -/
theorem sat_rel {old : Fin L → Fin L'} {mk : Fin L'} {A : SimpleGraph (Fin n)}
    {col : Coloring n L} {col' : Coloring n L'} {X : Set (Fin n)}
    (hold : ∀ c, col' (old c) = col c ∩ X) (hmk : col' mk = X)
    {k : ℕ} (φ : DistFO L k) (m : Fin k → Fin n) :
    Sat (deleteVerts A Xᶜ) col' m (rel old mk φ) ↔ SatWithin X A col m φ := by
  induction φ with
  | adj i j =>
    simp only [rel_adj, sat_adj, satWithin_adj, SplitterBasics.deleteVerts_adj,
      Set.notMem_compl_iff]
  | eq i j => simp only [rel_eq, sat_eq, satWithin_eq]
  | color c i =>
    simp only [rel_color, sat_color, satWithin_color, hold c, Set.mem_inter_iff]
  | distLe d i j =>
    simp only [rel_distLe, sat_and, sat_distLe, sat_color, satWithin_distLe, hmk]
    refine ⟨fun h => withinDistIn_of_withinDist_deleteVerts_compl h.1 (Or.inl h.2.1), fun h => ?_⟩
    exact ⟨withinDist_deleteVerts_compl_of_withinDistIn h,
      mem_of_withinDistIn_left h, mem_of_withinDistIn_right h⟩
  | distColorLt r c i =>
    simp only [rel_distColorLt, sat_and, sat_distColorLt, sat_color, satWithin_distColorLt,
      hold c, hmk, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨y, ⟨hyc, hyX⟩, p, hp⟩, hi⟩
      obtain ⟨q, hq, hqs⟩ := exists_walk_of_deleteVerts_compl p (Or.inl hi)
      exact ⟨y, hyc, hyX, q, hq ▸ hp, hqs⟩
    · rintro ⟨y, hyc, hyX, p, hp, hps⟩
      obtain ⟨q, hq⟩ := exists_walk_deleteVerts_compl p hps
      exact ⟨⟨y, ⟨hyc, hyX⟩, q, hq ▸ hp⟩, hps _ p.start_mem_support⟩
  | not φ ih =>
    simp only [rel_not, sat_not, satWithin_not]
    exact not_congr (ih m)
  | and φ ψ ihφ ihψ =>
    simp only [rel_and, sat_and, satWithin_and]
    exact and_congr (ihφ m) (ihψ m)
  | exU φ ih =>
    simp only [rel_exU, sat_exU, sat_and, sat_color, satWithin_exU, Fin.snoc_last, hmk]
    exact exists_congr fun v => and_congr_right fun _ => ih (Fin.snoc m v)
  | exL r g φ ih =>
    simp only [rel_exL, sat_exL, sat_and, sat_color, satWithin_exL, Fin.snoc_last, hmk]
    constructor
    · rintro ⟨v, ⟨i, hig, hiv⟩, hv, hsat⟩
      exact ⟨v, hv, ⟨i, hig, withinDistIn_of_withinDist_deleteVerts_compl hiv (Or.inr hv)⟩,
        (ih (Fin.snoc m v)).mp hsat⟩
    · rintro ⟨v, hv, ⟨i, hig, hiv⟩, hsat⟩
      exact ⟨v, ⟨i, hig, withinDist_deleteVerts_compl_of_withinDistIn hiv⟩, hv,
        (ih (Fin.snoc m v)).mpr hsat⟩

/-! ### The two syntactic invariants -/

/-- Relativization preserves distance rank. The conjuncts it adds are
color atoms, which have every distance rank, and no radius and no
quantifier is touched. -/
theorem drank_rel (old : Fin L → Fin L') (mk : Fin L') {k k' q : ℕ} {φ : DistFO L k}
    (h : DRank k' q φ) : DRank k' q (rel old mk φ) := by
  induction h with
  | adj i j => simp only [rel_adj]; exact .adj _ _
  | eq i j => simp only [rel_eq]; exact .eq _ _
  | color c i => simp only [rel_color]; exact .color _ _
  | distLe i j hr =>
    simp only [rel_distLe]
    exact .and (.distLe _ _ hr) (.and (.color _ _) (.color _ _))
  | distColorLt c i hr =>
    simp only [rel_distColorLt]
    exact .and (.distColorLt _ _ hr) (.color _ _)
  | not _ ih => simp only [rel_not]; exact .not ih
  | and _ _ ih ih' => simp only [rel_and]; exact .and ih ih'
  | exU _ ih => simp only [rel_exU]; exact .exU (.and (.color _ _) ih)
  | exL _ hr ih => simp only [rel_exL]; exact .exL (.and (.color _ _) ih) hr

/-- Relativization preserves locality: a local quantifier stays a local
quantifier, and the marker conjuncts are atoms. -/
theorem isLocal_rel (old : Fin L → Fin L') (mk : Fin L') {k : ℕ} {φ : DistFO L k}
    (h : IsLocal φ) : IsLocal (rel old mk φ) := by
  revert h
  induction φ with
  | adj i j => intro _; simp only [rel_adj]; exact isLocal_adj _ _
  | eq i j => intro _; simp only [rel_eq]; exact isLocal_eq _ _
  | color c i => intro _; simp only [rel_color]; exact isLocal_color _ _
  | distLe d i j =>
    intro _
    simp only [rel_distLe]
    exact (isLocal_and _ _).mpr ⟨isLocal_distLe _ _ _,
      (isLocal_and _ _).mpr ⟨isLocal_color _ _, isLocal_color _ _⟩⟩
  | distColorLt r c i =>
    intro _
    simp only [rel_distColorLt]
    exact (isLocal_and _ _).mpr ⟨isLocal_distColorLt _ _ _, isLocal_color _ _⟩
  | not φ ih =>
    intro h
    simp only [rel_not]
    exact (isLocal_not _).mpr (ih ((isLocal_not _).mp h))
  | and φ ψ ihφ ihψ =>
    intro h
    obtain ⟨hφ, hψ⟩ := (isLocal_and _ _).mp h
    simp only [rel_and]
    exact (isLocal_and _ _).mpr ⟨ihφ hφ, ihψ hψ⟩
  | exU φ ih => intro h; exact ((isLocal_exU φ).mp h).elim
  | exL r g φ ih =>
    intro h
    simp only [rel_exL]
    exact (isLocal_exL _ _ _).mpr
      ((isLocal_and _ _).mpr ⟨isLocal_color _ _, ih ((isLocal_exL _ _ _).mp h)⟩)

end Lax3Proofs.Relativize
