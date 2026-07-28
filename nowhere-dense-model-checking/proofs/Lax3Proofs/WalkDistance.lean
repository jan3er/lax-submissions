import Lax3.ColoredGraphs
import Lax12.UniformQuasiWideness
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
The first slice of the walk-distance API of `Lax3.ColoredGraphs`:
`WithinDist` is reflexive, symmetric and additively transitive, it grows
with the radius and with the graph, and it descends along Lax12's
`deleteVerts` — the isolation move that this submission's splitter game
and its rewriting step both perform.

The load-bearing statement is `withinDist_deleteVerts_or_through`: a
walk of length at most `d` either avoids an isolated set `S` altogether,
in which case every one of its edges survives isolation, or it meets `S`
somewhere and splits there into two walks whose lengths add up to at
most `d`. That is the `≥` half of the metric identity

    dist G u v = min (dist (deleteVerts G S) u v) (min over s ∈ S of
                      dist G u s + dist G s v)

which the isolation rewrite reduces to; the `≤` half is
`withinDist_deleteVerts` together with `withinDist_trans`. Endpoints in
`S` and walks of length zero need no separate treatment: the split point
is taken anywhere in the support, so `u ∈ S` splits a walk into an empty
prefix and the walk itself.
-/

namespace Lax3Proofs.WalkDistance

open Lax3.ColoredGraphs
open Lax12.UniformQuasiWideness

variable {V : Type*} {G G' : SimpleGraph V} {S : Set V} {u v w : V} {d d' d₁ d₂ : ℕ}

/-! ### Basic metric properties of `WithinDist` -/

/-- Every vertex is within any distance of itself. -/
theorem withinDist_refl (G : SimpleGraph V) (d : ℕ) (v : V) : WithinDist G d v v :=
  ⟨.nil, by simp⟩

/-- Equal vertices are within any distance of each other. -/
theorem withinDist_of_eq (G : SimpleGraph V) (d : ℕ) (h : u = v) : WithinDist G d u v :=
  h ▸ withinDist_refl G d u

/-- `WithinDist` is symmetric: walks reverse. -/
theorem withinDist_symm (h : WithinDist G d u v) : WithinDist G d v u := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩

/-- `WithinDist` adds along concatenation of walks. -/
theorem withinDist_trans (h₁ : WithinDist G d₁ u v) (h₂ : WithinDist G d₂ v w) :
    WithinDist G (d₁ + d₂) u w := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  exact ⟨p.append q, by rw [SimpleGraph.Walk.length_append]; omega⟩

/-- Adjacent vertices are within distance one. -/
theorem withinDist_of_adj (h : G.Adj u v) : WithinDist G 1 u v :=
  ⟨SimpleGraph.Walk.cons h .nil, by simp⟩

/-- `WithinDist` is monotone in the radius. -/
theorem withinDist_mono_radius (hd : d ≤ d') (h : WithinDist G d u v) :
    WithinDist G d' u v := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.trans hd⟩

/-- A walk of a subgraph is a walk of the graph, at the same length. -/
theorem exists_walk_of_le (hG : G ≤ G') (p : G.Walk u v) :
    ∃ q : G'.Walk u v, q.length = p.length := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons a b c hab p ih =>
    obtain ⟨q, hq⟩ := ih
    exact ⟨SimpleGraph.Walk.cons (hG hab) q, by simp [hq]⟩

/-- `WithinDist` is monotone in the graph: adding edges only shortens
walks. -/
theorem withinDist_mono_graph (hG : G ≤ G') (h : WithinDist G d u v) :
    WithinDist G' d u v := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := exists_walk_of_le hG p
  exact ⟨q, hq ▸ hp⟩

/-! ### Isolating a vertex set -/

/-- Isolating a vertex set only removes edges. -/
theorem deleteVerts_le (G : SimpleGraph V) (S : Set V) : deleteVerts G S ≤ G :=
  fun _ _ h => h.1

/-- Vertices within distance `d` after isolating `S` are within distance
`d` before. -/
theorem withinDist_deleteVerts (h : WithinDist (deleteVerts G S) d u v) :
    WithinDist G d u v :=
  withinDist_mono_graph (deleteVerts_le G S) h

/-- A walk avoiding `S` survives the isolation of `S`, at the same
length. -/
theorem exists_walk_deleteVerts (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∉ S) :
    ∃ q : (deleteVerts G S).Walk u v, q.length = p.length := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons a b c hab p ih =>
    obtain ⟨q, hq⟩ := ih fun x hx => hp x (by simp [hx])
    exact ⟨SimpleGraph.Walk.cons ⟨hab, hp a (by simp), hp b (by simp)⟩ q, by simp [hq]⟩

/-- The decomposition the isolation rewrite runs on: a walk of length at
most `d` either avoids the isolated set `S`, and then survives isolation
whole, or it passes through some `s ∈ S`, and then splits at `s` into
two walks whose lengths add up to at most `d`. -/
theorem withinDist_deleteVerts_or_through (S : Set V) (h : WithinDist G d u v) :
    WithinDist (deleteVerts G S) d u v ∨
      ∃ s ∈ S, ∃ d₁ d₂ : ℕ, d₁ + d₂ ≤ d ∧ WithinDist G d₁ u s ∧ WithinDist G d₂ s v := by
  classical
  obtain ⟨p, hp⟩ := h
  by_cases hS : ∃ x ∈ p.support, x ∈ S
  · obtain ⟨x, hx, hxS⟩ := hS
    have hlen := congrArg SimpleGraph.Walk.length (p.take_spec hx)
    rw [SimpleGraph.Walk.length_append] at hlen
    exact Or.inr ⟨x, hxS, (p.takeUntil x hx).length, (p.dropUntil x hx).length,
      by omega, ⟨_, le_rfl⟩, ⟨_, le_rfl⟩⟩
  · simp only [not_exists, not_and] at hS
    obtain ⟨q, hq⟩ := exists_walk_deleteVerts p hS
    exact Or.inl ⟨q, hq ▸ hp⟩

/-! ### Balls -/

/-- Membership in a ball is the distance bound it is defined by. -/
theorem mem_ball : u ∈ ball G d v ↔ WithinDist G d v u := Iff.rfl

/-- Every ball contains its center. -/
theorem mem_ball_self (G : SimpleGraph V) (d : ℕ) (v : V) : v ∈ ball G d v :=
  withinDist_refl G d v

/-- Balls grow with the radius. -/
theorem ball_mono_radius (G : SimpleGraph V) (v : V) (hd : d ≤ d') :
    ball G d v ⊆ ball G d' v :=
  fun _ hu => withinDist_mono_radius hd hu

/-- Balls grow with the graph. -/
theorem ball_mono_graph (v : V) (hG : G ≤ G') : ball G d v ⊆ ball G' d v :=
  fun _ hu => withinDist_mono_graph hG hu

/-- Isolating a vertex set shrinks every ball. -/
theorem ball_deleteVerts_subset (G : SimpleGraph V) (S : Set V) (d : ℕ) (v : V) :
    ball (deleteVerts G S) d v ⊆ ball G d v :=
  fun _ hu => withinDist_deleteVerts hu

end Lax3Proofs.WalkDistance
