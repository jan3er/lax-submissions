import Lax15Proofs.Residual
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
The solver: what a node of the search costs once no vertex is worth
branching on.

The second rung of the ladder branches on a vertex of residual degree
at least three. When no such vertex exists the residual graph has all
degrees at most two — a disjoint union of paths and cycles — and the
node is not a leaf to be guessed at but a subproblem to be *solved*: a
graph of maximum degree two has a smallest vertex cover of size

    compCost = Σ_C ⌈e_C / 2⌉,

the sum over connected components of half their edge count, rounded up.
This file proves that, in both directions, in the vocabulary the search
speaks: the residual graph `R G M` of `Lax15Proofs.VC`'s marking, the
budget predicate `Ok` of `Lax11Proofs.VC`, and the residual degree of
`Residual.lean`.

The lower bound is a counting argument: a cover meets every residual
edge, one of its vertices covers at most two of them, and components
are disjoint. The upper bound is an induction on the number of edges
that isolates one vertex at a time, and the whole difficulty is that
isolating a vertex must not tear a component into two edge-bearing
pieces — deleting the middle vertex of a five-vertex path costs one and
saves nothing. Two rules avoid it: if some vertex has degree one, delete
its *neighbour*, and if none has, every component with an edge is a
cycle, where the two neighbours of the deleted vertex stay connected —
by the handshake lemma applied to one component, since a component with
exactly one odd-degree vertex cannot exist.

The last section transports the branching test to threshold three, in
the slot vocabulary of `Residual.lean`: a block naming three pairwise
different unmarked vertices is a vertex of residual degree three, and a
scan that finds none certifies that every unmarked vertex has residual
degree at most two — the hypothesis of both bounds.

Decidability is classical throughout: the residual graph is a
specification, never a program, and the two local instances below fix
one derivation of every finiteness instance mathlib's graph library
asks for, so that its lemmas apply on the nose.
-/

namespace Lax15Proofs.VC3

open Lax11Proofs.VC Lax15Proofs.VC Lax11.GraphEncoding Lax11Proofs.CC SimpleGraph

variable {n : ℕ} {G : SimpleGraph (Fin n)} {M : Finset (Fin n)} {b : ℕ}

noncomputable local instance decAdj (H : SimpleGraph (Fin n)) : DecidableRel H.Adj :=
  Classical.decRel _

noncomputable local instance decEqComp (H : SimpleGraph (Fin n)) :
    DecidableEq H.ConnectedComponent :=
  Classical.decEq _

/-! ### The residual graph -/

/-- **The residual graph**: the edges of `G` that the marking `M` has
not yet paid for, as a graph in their own right. Its edge set is
`ResEdges G M` and its degrees are the residual degrees — at a marked
vertex, zero. -/
def R (G : SimpleGraph (Fin n)) (M : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∧ a ∉ M ∧ b ∉ M
  symm := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

@[simp] theorem R_adj {a c : Fin n} : (R G M).Adj a c ↔ G.Adj a c ∧ a ∉ M ∧ c ∉ M := Iff.rfl

theorem R_le : R G M ≤ G := fun _ _ h => h.1

/-- The residual graph's edges are the residual edges. -/
theorem edgeFinset_R : (R G M).edgeFinset = ResEdges G M := by
  ext e
  induction e with | _ a c =>
  simp [mem_resEdges]

theorem neighborFinset_R {v : Fin n} (hv : v ∉ M) :
    (R G M).neighborFinset v = ResNbhd G M v := by
  ext w
  simp [mem_resNbhd, hv]

/-- The residual graph's degree at an unmarked vertex is the residual
degree. -/
theorem degree_R {v : Fin n} (hv : v ∉ M) : (R G M).degree v = resDeg G M v := by
  rw [SimpleGraph.degree, neighborFinset_R hv, resDeg_eq_card]

/-- At a marked vertex the residual graph has no edges at all. -/
theorem degree_R_of_mem {v : Fin n} (hv : v ∈ M) : (R G M).degree v = 0 := by
  rw [SimpleGraph.degree, Finset.card_eq_zero]
  ext w
  simp [hv]

/-- The hypothesis the solver runs on, transported to the residual
graph: a bound on residual degrees is a bound on all its degrees, the
marked vertices being isolated in it. -/
theorem degree_R_le_two (hdeg : ∀ v : Fin n, v ∉ M → resDeg G M v ≤ 2) (v : Fin n) :
    (R G M).degree v ≤ 2 := by
  by_cases hv : v ∈ M
  · simp [degree_R_of_mem hv]
  · rw [degree_R hv]; exact hdeg v hv

/-! ### Components and their cost -/

/-- The edges of `H` inside the component `C`. An edge is assigned to
the component of its smaller endpoint, which is also the component of
its larger one — so this is what it says it is, and the assignment is a
function, which is what makes the components partition the edges. -/
noncomputable def compEdges (H : SimpleGraph (Fin n)) (C : H.ConnectedComponent) :
    Finset (Sym2 (Fin n)) :=
  {e ∈ H.edgeFinset | H.connectedComponentMk e.inf = C}

theorem mem_compEdges {H : SimpleGraph (Fin n)} {C : H.ConnectedComponent} {a c : Fin n} :
    s(a, c) ∈ compEdges H C ↔ H.Adj a c ∧ H.connectedComponentMk a = C := by
  have hmk : ∀ x y : Fin n, H.Adj x y → H.connectedComponentMk x = H.connectedComponentMk y :=
    fun _ _ h => ConnectedComponent.sound h.reachable
  constructor
  · intro h
    rw [compEdges, Finset.mem_filter] at h
    obtain ⟨h1, h2⟩ := h
    have hadj : H.Adj a c := by simpa using h1
    refine ⟨hadj, ?_⟩
    rcases le_total a c with hac | hac
    · rwa [Sym2.inf_mk, min_eq_left hac] at h2
    · rw [Sym2.inf_mk, min_eq_right hac] at h2
      rwa [hmk a c hadj]
  · rintro ⟨hadj, hC⟩
    rw [compEdges, Finset.mem_filter]
    refine ⟨by simpa using hadj, ?_⟩
    rcases le_total a c with hac | hac
    · rwa [Sym2.inf_mk, min_eq_left hac]
    · rw [Sym2.inf_mk, min_eq_right hac, ← hmk a c hadj]
      exact hC

theorem compEdges_subset {H : SimpleGraph (Fin n)} {C : H.ConnectedComponent} :
    compEdges H C ⊆ H.edgeFinset := Finset.filter_subset _ _

/-- Both endpoints of an edge of a component lie in that component. -/
theorem mem_of_mem_compEdges {H : SimpleGraph (Fin n)} {C : H.ConnectedComponent}
    {e : Sym2 (Fin n)} (he : e ∈ compEdges H C) {x : Fin n} (hx : x ∈ e) :
    H.connectedComponentMk x = C := by
  induction e with | _ a c =>
  obtain ⟨hadj, hC⟩ := mem_compEdges.1 he
  rcases Sym2.mem_iff.1 hx with rfl | rfl
  · exact hC
  · rw [← hC]
    exact (ConnectedComponent.sound hadj.reachable).symm

/-- **The components partition the edges**: every edge belongs to
exactly one of them. -/
theorem sum_card_compEdges (H : SimpleGraph (Fin n)) :
    ∑ C : H.ConnectedComponent, (compEdges H C).card = H.edgeFinset.card := by
  refine (Finset.card_eq_sum_card_fiberwise
    (f := fun e => H.connectedComponentMk (Sym2.inf e)) (t := Finset.univ)
    (fun e _ => Finset.mem_univ _)).symm

/-- **The cost of a graph of maximum degree two**: half the edges of
each component, rounded up. In `ℕ` the rounding is `(e + 1) / 2`. -/
noncomputable def compCost' (H : SimpleGraph (Fin n)) : ℕ :=
  ∑ C : H.ConnectedComponent, ((compEdges H C).card + 1) / 2

/-- The cost of the residual graph at a node of the search: what the
solver block computes and compares against the budget. -/
noncomputable def compCost (G : SimpleGraph (Fin n)) (M : Finset (Fin n)) : ℕ :=
  compCost' (R G M)

theorem compCost_eq (G : SimpleGraph (Fin n)) (M : Finset (Fin n)) :
    compCost G M = compCost' (R G M) := rfl

/-- The cost vanishes exactly on graphs without edges. -/
theorem compCost'_eq_zero_iff (H : SimpleGraph (Fin n)) :
    compCost' H = 0 ↔ H.edgeFinset.card = 0 := by
  rw [compCost', Finset.sum_eq_zero_iff, ← sum_card_compEdges H, Finset.sum_eq_zero_iff]
  constructor
  · intro h C hC
    have := h C hC
    omega
  · intro h C hC
    have := h C hC
    omega

/-- The residual edges gathered by component: the count the solver's
sweep accumulates, one component at a time. Stated in `ResEdges` so that
it can be used without the residual graph's finiteness instances. -/
theorem sum_card_compEdges_R (G : SimpleGraph (Fin n)) (M : Finset (Fin n)) :
    ∑ C : (R G M).ConnectedComponent, (compEdges (R G M) C).card = (ResEdges G M).card := by
  rw [sum_card_compEdges, edgeFinset_R]

/-- The solver's cost vanishes exactly when the marking is already a
cover. -/
theorem compCost_eq_zero_iff (G : SimpleGraph (Fin n)) (M : Finset (Fin n)) :
    compCost G M = 0 ↔ (ResEdges G M).card = 0 := by
  rw [compCost_eq, compCost'_eq_zero_iff, edgeFinset_R]

/-! ### The lower bound -/

/-- At most `H.degree x` edges of a set of edges pass through `x`. -/
theorem card_filter_mem_le_degree {H : SimpleGraph (Fin n)} (x : Fin n)
    {s : Finset (Sym2 (Fin n))} (hs : s ⊆ H.edgeFinset) :
    (s.filter (fun e => x ∈ e)).card ≤ H.degree x := by
  classical
  set F : Sym2 (Fin n) → Fin n := fun e =>
    if h : ∃ y, e = s(x, y) then h.choose else x with hF
  have hFspec : ∀ e ∈ s.filter (fun e => x ∈ e), e = s(x, F e) := by
    intro e he
    have hx : x ∈ e := (Finset.mem_filter.1 he).2
    have h : ∃ y, e = s(x, y) := Sym2.mem_iff_exists.1 hx
    simp only [hF, dif_pos h]
    exact h.choose_spec
  have hmaps : ∀ e ∈ s.filter (fun e => x ∈ e), F e ∈ H.neighborFinset x := by
    intro e he
    have hmem : e ∈ H.edgeFinset := hs (Finset.mem_filter.1 he).1
    rw [hFspec e he] at hmem
    rw [SimpleGraph.mem_neighborFinset]
    simpa using hmem
  refine le_trans (Finset.card_le_card_of_injOn F hmaps ?_) le_rfl
  intro e₁ h₁ e₂ h₂ heq
  rw [hFspec e₁ (Finset.mem_coe.1 h₁), hFspec e₂ (Finset.mem_coe.1 h₂), heq]

/-- **Two edges per cover vertex**: inside one component, a cover has to
supply a vertex for every residual edge, and each of its vertices takes
care of at most two of them. -/
theorem card_compEdges_le_two_mul {H : SimpleGraph (Fin n)}
    (hdeg : ∀ v : Fin n, H.degree v ≤ 2) {T : Finset (Fin n)} (hT : H.IsVertexCover ↑T)
    (C : H.ConnectedComponent) :
    (compEdges H C).card ≤ 2 * (T.filter (fun x => H.connectedComponentMk x = C)).card := by
  classical
  have hex : ∀ e ∈ compEdges H C, ∃ x, x ∈ e ∧ x ∈ T := by
    intro e he
    induction e with | _ a c =>
    obtain ⟨hadj, -⟩ := mem_compEdges.1 he
    rcases hT hadj with h | h
    · exact ⟨a, Sym2.mem_mk_left _ _, by simpa using h⟩
    · exact ⟨c, Sym2.mem_mk_right _ _, by simpa using h⟩
  set F : Sym2 (Fin n) → Fin n := fun e =>
    if h : ∃ x, x ∈ e ∧ x ∈ T then h.choose else e.inf with hF
  have hFspec : ∀ e ∈ compEdges H C, F e ∈ e ∧ F e ∈ T := by
    intro e he
    have h := hex e he
    simp only [hF, dif_pos h]
    exact h.choose_spec
  refine Finset.card_le_mul_card_image_of_maps_to (f := F) (fun e he => ?_) 2 (fun x hx => ?_)
  · exact Finset.mem_filter.2 ⟨(hFspec e he).2,
      mem_of_mem_compEdges he (hFspec e he).1⟩
  · have hsub : {e ∈ compEdges H C | F e = x} ⊆ {e ∈ compEdges H C | x ∈ e} := by
      intro e he
      rw [Finset.mem_filter] at he ⊢
      exact ⟨he.1, he.2 ▸ (hFspec e he.1).1⟩
    calc {e ∈ compEdges H C | F e = x}.card
        ≤ {e ∈ compEdges H C | x ∈ e}.card := Finset.card_le_card hsub
      _ ≤ H.degree x := card_filter_mem_le_degree x compEdges_subset
      _ ≤ 2 := hdeg x

/-- **The lower bound**: no vertex cover of a graph of maximum degree
two is cheaper than the sum over its components of half their edges,
rounded up. -/
theorem compCost'_le_card {H : SimpleGraph (Fin n)} (hdeg : ∀ v : Fin n, H.degree v ≤ 2)
    {T : Finset (Fin n)} (hT : H.IsVertexCover ↑T) : compCost' H ≤ T.card := by
  classical
  calc compCost' H
      ≤ ∑ C : H.ConnectedComponent,
          (T.filter (fun x => H.connectedComponentMk x = C)).card := by
        refine Finset.sum_le_sum (fun C _ => ?_)
        have := card_compEdges_le_two_mul hdeg hT C
        omega
    _ = T.card := (Finset.card_eq_sum_card_fiberwise
        (f := fun x => H.connectedComponentMk x) (fun x _ => Finset.mem_univ _)).symm

/-- **The lower bound at a node of the search**: with every unmarked
vertex of residual degree at most two, a budget below the solver's cost
cannot be met. This is the solver's NO. -/
theorem not_ok_of_lt_compCost (hdeg : ∀ v : Fin n, v ∉ M → resDeg G M v ≤ 2)
    (hb : b < compCost G M) : ¬ Ok G M b := by
  classical
  rintro ⟨S, hS, hMS, hcard⟩
  have hcov : (R G M).IsVertexCover ↑(S \ M) := by
    intro a c hac
    obtain ⟨hadj, ha, hc⟩ := hac
    rcases hS hadj with h | h
    · exact Or.inl (by simpa [Finset.mem_sdiff] using ⟨by simpa using h, ha⟩)
    · exact Or.inr (by simpa [Finset.mem_sdiff] using ⟨by simpa using h, hc⟩)
  have := compCost'_le_card (degree_R_le_two hdeg) hcov
  rw [← compCost_eq] at this
  omega

/-! ### Isolating a vertex -/

/-- `isolate H v`: the graph `H` with every edge at `v` removed. The
induction that builds a cheap cover deletes one vertex at a time;
isolating it rather than removing it from the vertex type keeps the two
graphs' components in the same family, so that they can be compared at
all. -/
def isolate (H : SimpleGraph (Fin n)) (v : Fin n) : SimpleGraph (Fin n) where
  Adj a c := H.Adj a c ∧ a ≠ v ∧ c ≠ v
  symm := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun _ h => H.irrefl h.1⟩

@[simp] theorem isolate_adj {H : SimpleGraph (Fin n)} {v a c : Fin n} :
    (isolate H v).Adj a c ↔ H.Adj a c ∧ a ≠ v ∧ c ≠ v := Iff.rfl

theorem isolate_le (H : SimpleGraph (Fin n)) (v : Fin n) : isolate H v ≤ H := fun _ _ h => h.1

/-- The isolated vertex is isolated. -/
theorem not_adj_isolate (H : SimpleGraph (Fin n)) (v z : Fin n) : ¬ (isolate H v).Adj v z :=
  fun h => h.2.1 rfl

/-- Membership in a neighbourhood, with the graph implicit — the form
every step below wants. -/
theorem mem_nbr {H : SimpleGraph (Fin n)} {x w : Fin n} :
    w ∈ H.neighborFinset x ↔ H.Adj x w :=
  SimpleGraph.mem_neighborFinset _ _ _

theorem neighborFinset_isolate {H : SimpleGraph (Fin n)} {v x : Fin n} (hx : x ≠ v) :
    (isolate H v).neighborFinset x = (H.neighborFinset x).erase v := by
  ext w
  simp only [mem_nbr, isolate_adj, Finset.mem_erase, hx, ne_eq, not_false_eq_true, true_and]
  tauto

theorem degree_isolate_le {H : SimpleGraph (Fin n)} (v x : Fin n) :
    (isolate H v).degree x ≤ H.degree x := by
  refine Finset.card_le_card (fun w hw => ?_)
  rw [mem_nbr] at hw ⊢
  exact hw.1

theorem edgeFinset_isolate_subset (H : SimpleGraph (Fin n)) (v : Fin n) :
    (isolate H v).edgeFinset ⊆ H.edgeFinset := by
  intro e he
  induction e with | _ a c =>
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
  exact he.1

/-- Isolating a vertex that carries an edge strictly lowers the edge
count — which is what the induction counts down. -/
theorem card_edgeFinset_isolate_lt {H : SimpleGraph (Fin n)} {v z : Fin n} (h : H.Adj v z) :
    (isolate H v).edgeFinset.card < H.edgeFinset.card := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset (edgeFinset_isolate_subset H v)).2
    ⟨s(v, z), by simpa using h, ?_⟩)
  intro hmem
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hmem
  exact hmem.2.1 rfl

/-- Reachability from an isolated vertex reaches nothing else. -/
theorem eq_of_reachable_isolated {K : SimpleGraph (Fin n)} {u : Fin n}
    (hiso : ∀ z, ¬ K.Adj u z) {a : Fin n} (h : K.Reachable u a) : a = u := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hiso _)

/-- A walk that starts outside `v`'s component never meets `v`, so it
survives isolating `v`. -/
theorem reachable_isolate {H : SimpleGraph (Fin n)} {v x y : Fin n}
    (hxy : H.Reachable x y) (hx : ¬ H.Reachable x v) : (isolate H v).Reachable x y := by
  have key : ∀ {a c : Fin n} (_ : H.Walk a c), ¬ H.Reachable a v → (isolate H v).Reachable a c := by
    intro a c p
    induction p with
    | nil => intro _; exact SimpleGraph.Reachable.refl _
    | @cons a b c hadj _ ih =>
        intro ha
        have hav : a ≠ v := by rintro rfl; exact ha (SimpleGraph.Reachable.refl _)
        have hbv : b ≠ v := by rintro rfl; exact ha hadj.reachable
        have hb : ¬ H.Reachable b v := fun h => ha (hadj.reachable.trans h)
        exact (SimpleGraph.Adj.reachable (show (isolate H v).Adj a b from ⟨hadj, hav, hbv⟩)).trans
          (ih hb)
  obtain ⟨p⟩ := hxy
  exact key p hx

/-- **Isolating leaves the rest of the component hanging on a
neighbour**: truncate a walk to `v` at its first arrival, and what is
left is a walk to a neighbour of `v` that avoids `v`. This is the only
structural fact about deletion the whole induction uses. -/
theorem exists_adj_reachable_isolate {H : SimpleGraph (Fin n)} {v x : Fin n}
    (h : H.Reachable x v) (hx : x ≠ v) :
    ∃ z, H.Adj v z ∧ (isolate H v).Reachable x z := by
  have key : ∀ {a c : Fin n} (_ : H.Walk a c), c = v → a ≠ v →
      ∃ z, H.Adj v z ∧ (isolate H v).Reachable a z := by
    intro a c p
    induction p with
    | nil => intro h1 h2; exact absurd h1 h2
    | @cons a b c hadj _ ih =>
        intro h1 h2
        by_cases hbv : b = v
        · subst hbv
          exact ⟨a, hadj.symm, SimpleGraph.Reachable.refl _⟩
        · obtain ⟨z, hz, hr⟩ := ih h1 hbv
          exact ⟨z, hz, (SimpleGraph.Adj.reachable
            (show (isolate H v).Adj a b from ⟨hadj, h2, hbv⟩)).trans hr⟩
  obtain ⟨p⟩ := h
  exact key p rfl hx

/-! ### Comparing the components of a subgraph -/

/-- Every component of a subgraph sits inside one component of the
graph. -/
noncomputable def liftComp {H K : SimpleGraph (Fin n)} (hle : K ≤ H) :
    K.ConnectedComponent → H.ConnectedComponent :=
  ConnectedComponent.lift (fun x => H.connectedComponentMk x)
    (fun _ _ p _ => ConnectedComponent.sound (SimpleGraph.Reachable.mono hle p.reachable))

@[simp] theorem liftComp_mk {H K : SimpleGraph (Fin n)} (hle : K ≤ H) (x : Fin n) :
    liftComp hle (K.connectedComponentMk x) = H.connectedComponentMk x := rfl

/-- The components of the subgraph that a component of the graph falls
into. -/
noncomputable def fiber {H K : SimpleGraph (Fin n)} (hle : K ≤ H) (C : H.ConnectedComponent) :
    Finset K.ConnectedComponent :=
  {C' ∈ (Finset.univ : Finset K.ConnectedComponent) | liftComp hle C' = C}

theorem mem_fiber {H K : SimpleGraph (Fin n)} {hle : K ≤ H} {C : H.ConnectedComponent}
    {C' : K.ConnectedComponent} : C' ∈ fiber hle C ↔ liftComp hle C' = C := by
  simp [fiber]

/-- The cost of a subgraph, gathered along the components of the graph
it sits in. -/
theorem compCost'_eq_sum_fiber {H K : SimpleGraph (Fin n)} (hle : K ≤ H) :
    compCost' K = ∑ C : H.ConnectedComponent,
      ∑ C' ∈ fiber hle C, ((compEdges K C').card + 1) / 2 := by
  simp only [fiber]
  exact (Finset.sum_fiberwise_of_maps_to (fun C' _ => Finset.mem_univ _) _).symm

/-- A component with an edge has an edge. -/
theorem exists_adj_of_card_compEdges_pos {K : SimpleGraph (Fin n)} {C' : K.ConnectedComponent}
    (h : 0 < (compEdges K C').card) : ∃ x c, K.Adj x c ∧ K.connectedComponentMk x = C' := by
  obtain ⟨e, he⟩ := Finset.card_pos.1 h
  induction e with | _ a c =>
  obtain ⟨hadj, hmk⟩ := mem_compEdges.1 he
  exact ⟨a, c, hadj, hmk⟩

/-- Away from `v`, isolating `v` changes nothing: the component of `x`
keeps its vertices and its edges. -/
theorem compEdges_isolate_eq {H : SimpleGraph (Fin n)} {v x : Fin n} (hxv : ¬ H.Reachable x v) :
    compEdges (isolate H v) ((isolate H v).connectedComponentMk x)
      = compEdges H (H.connectedComponentMk x) := by
  ext e
  induction e with | _ a c =>
  rw [mem_compEdges, mem_compEdges]
  constructor
  · rintro ⟨hadj, hmk⟩
    exact ⟨hadj.1, ConnectedComponent.sound
      (SimpleGraph.Reachable.mono (isolate_le H v) (ConnectedComponent.exact hmk))⟩
  · rintro ⟨hadj, hmk⟩
    have hax : H.Reachable a x := ConnectedComponent.exact hmk
    have hav : ¬ H.Reachable a v := fun h => hxv (hax.symm.trans h)
    have hcv : ¬ H.Reachable c v := fun h => hav (hadj.reachable.trans h)
    refine ⟨⟨hadj, ?_, ?_⟩, ConnectedComponent.sound (reachable_isolate hax hav)⟩
    · rintro rfl; exact hav (SimpleGraph.Reachable.refl _)
    · rintro rfl; exact hcv (SimpleGraph.Reachable.refl _)

/-- **The drop lemma**: if the pieces `v`'s component falls into pay for
themselves, isolating `v` buys a unit of cost. Away from `v` nothing
changes, so the whole comparison is the one at `v`'s component, which
the hypothesis supplies. -/
theorem compCost'_isolate_succ_le {H : SimpleGraph (Fin n)} {v : Fin n}
    (hsplit : (∑ C' ∈ fiber (isolate_le H v) (H.connectedComponentMk v),
        ((compEdges (isolate H v) C').card + 1) / 2) + 1
      ≤ ((compEdges H (H.connectedComponentMk v)).card + 1) / 2) :
    compCost' (isolate H v) + 1 ≤ compCost' H := by
  classical
  have hother : ∀ C : H.ConnectedComponent, C ≠ H.connectedComponentMk v →
      (∑ C' ∈ fiber (isolate_le H v) C, ((compEdges (isolate H v) C').card + 1) / 2)
        = ((compEdges H C).card + 1) / 2 := by
    intro C hC
    induction C using ConnectedComponent.ind with | _ x =>
    have hxv : ¬ H.Reachable x v := fun h => hC (ConnectedComponent.sound h)
    have hfib : fiber (isolate_le H v) (H.connectedComponentMk x)
        = {(isolate H v).connectedComponentMk x} := by
      ext C'
      induction C' using ConnectedComponent.ind with | _ y =>
      rw [mem_fiber, liftComp_mk, Finset.mem_singleton]
      constructor
      · intro h
        have hyx : H.Reachable y x := ConnectedComponent.exact h
        exact ConnectedComponent.sound
          (reachable_isolate hyx (fun hyv => hxv (hyx.symm.trans hyv)))
      · intro h
        exact ConnectedComponent.sound (SimpleGraph.Reachable.mono (isolate_le H v)
          (ConnectedComponent.exact h))
    rw [hfib, Finset.sum_singleton, compEdges_isolate_eq hxv]
  rw [compCost'_eq_sum_fiber (isolate_le H v), compCost']
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (H.connectedComponentMk v)),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (H.connectedComponentMk v))]
  have hcongr : (∑ C ∈ Finset.univ.erase (H.connectedComponentMk v),
        ∑ C' ∈ fiber (isolate_le H v) C, ((compEdges (isolate H v) C').card + 1) / 2)
      = ∑ C ∈ Finset.univ.erase (H.connectedComponentMk v), ((compEdges H C).card + 1) / 2 :=
    Finset.sum_congr rfl (fun C hC => hother C (Finset.mem_erase.1 hC).1)
  omega

/-- The bookkeeping at `v`'s own component: one piece carries all its
edges, and that piece is at least two edges — or all of them — short of
the component it came from. -/
theorem split_bound {H : SimpleGraph (Fin n)} {v : Fin n}
    (W : (isolate H v).ConnectedComponent)
    (hW : liftComp (isolate_le H v) W = H.connectedComponentMk v)
    (hone : ∀ C' : (isolate H v).ConnectedComponent,
      liftComp (isolate_le H v) C' = H.connectedComponentMk v →
      0 < (compEdges (isolate H v) C').card → C' = W)
    (hcard : (compEdges (isolate H v) W).card + 2 ≤ (compEdges H (H.connectedComponentMk v)).card ∨
      ((compEdges (isolate H v) W).card = 0 ∧
        1 ≤ (compEdges H (H.connectedComponentMk v)).card)) :
    (∑ C' ∈ fiber (isolate_le H v) (H.connectedComponentMk v),
      ((compEdges (isolate H v) C').card + 1) / 2) + 1
      ≤ ((compEdges H (H.connectedComponentMk v)).card + 1) / 2 := by
  classical
  have hsum : (∑ C' ∈ fiber (isolate_le H v) (H.connectedComponentMk v),
      ((compEdges (isolate H v) C').card + 1) / 2)
      = ((compEdges (isolate H v) W).card + 1) / 2 := by
    refine Finset.sum_eq_single_of_mem W (mem_fiber.2 hW) (fun C' hC' hne => ?_)
    have h0 : (compEdges (isolate H v) C').card = 0 := by
      by_contra h
      exact hne (hone C' (mem_fiber.1 hC') (Nat.pos_of_ne_zero h))
    simp [h0]
  rw [hsum]
  omega

/-- Every edge-bearing piece of `v`'s component hangs on the same
neighbour `w` of `v`, provided the other neighbour `u` either stays
connected to `w` or has nothing left to hang on. -/
theorem eq_comp_of_card_pos {H : SimpleGraph (Fin n)} {v u w : Fin n}
    (hnb : H.neighborFinset v = {u, w})
    (hu : (isolate H v).Reachable u w ∨ ∀ z, ¬ (isolate H v).Adj u z) :
    ∀ C' : (isolate H v).ConnectedComponent,
      liftComp (isolate_le H v) C' = H.connectedComponentMk v →
      0 < (compEdges (isolate H v) C').card →
      C' = (isolate H v).connectedComponentMk w := by
  intro C' hfib hpos
  obtain ⟨x, c, hadj, hxC⟩ := exists_adj_of_card_compEdges_pos hpos
  have hxv : x ≠ v := hadj.2.1
  rw [← hxC, liftComp_mk] at hfib
  obtain ⟨z, hz, hreach⟩ := exists_adj_reachable_isolate (ConnectedComponent.exact hfib) hxv
  have hzmem : z ∈ H.neighborFinset v := mem_nbr.2 hz
  rw [hnb, Finset.mem_insert, Finset.mem_singleton] at hzmem
  rcases hzmem with hzu | hzw
  · subst hzu
    rcases hu with hreachuw | hisou
    · rw [← hxC]
      exact ConnectedComponent.sound (hreach.trans hreachuw)
    · exfalso
      have hxu : x = z := eq_of_reachable_isolated hisou hreach.symm
      subst hxu
      exact hisou c hadj
  · subst hzw
    rw [← hxC]
    exact ConnectedComponent.sound hreach

/-- The edges of `w`'s piece are edges of `v`'s component. -/
theorem compEdges_isolate_subset {H : SimpleGraph (Fin n)} {v w : Fin n} (hw : H.Adj v w) :
    compEdges (isolate H v) ((isolate H v).connectedComponentMk w)
      ⊆ compEdges H (H.connectedComponentMk v) := by
  intro e he
  induction e with | _ a c =>
  obtain ⟨hadj, hmk⟩ := mem_compEdges.1 he
  refine mem_compEdges.2 ⟨hadj.1, ConnectedComponent.sound ?_⟩
  exact (SimpleGraph.Reachable.mono (isolate_le H v) (ConnectedComponent.exact hmk)).trans
    hw.symm.reachable

/-- Two edges of `v`'s component die with `v`, so what is left is two
edges short. -/
theorem card_compEdges_add_two_le {H : SimpleGraph (Fin n)} {v u w : Fin n}
    (hu : H.Adj v u) (hw : H.Adj v w) (huw : u ≠ w) :
    (compEdges (isolate H v) ((isolate H v).connectedComponentMk w)).card + 2
      ≤ (compEdges H (H.connectedComponentMk v)).card := by
  classical
  have hnotin : ∀ y : Fin n,
      s(v, y) ∉ compEdges (isolate H v) ((isolate H v).connectedComponentMk w) := by
    intro y hy
    exact (mem_compEdges.1 hy).1.2.1 rfl
  have hne : s(v, u) ≠ s(v, w) := by
    rw [Ne, Sym2.eq_iff]
    push Not
    exact ⟨fun _ => huw, fun h => absurd h hw.ne⟩
  have hsub : insert s(v, u) (insert s(v, w)
      (compEdges (isolate H v) ((isolate H v).connectedComponentMk w)))
      ⊆ compEdges H (H.connectedComponentMk v) := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact mem_compEdges.2 ⟨hu, rfl⟩
    rcases Finset.mem_insert.1 he with rfl | he
    · exact mem_compEdges.2 ⟨hw, rfl⟩
    · exact compEdges_isolate_subset hw he
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by
      rw [Finset.mem_insert]
      push Not
      exact ⟨hne, hnotin u⟩),
    Finset.card_insert_of_notMem (hnotin w)] at hcard
  omega

/-! ### The handshake lemma on one component -/

/-- `H` restricted to the component `C`: the same edges inside `C`, and
nothing outside it. Its degree sum is the component's, so the handshake
lemma applies to one component at a time. -/
noncomputable def restrictComp (H : SimpleGraph (Fin n)) (C : H.ConnectedComponent) :
    SimpleGraph (Fin n) where
  Adj a c := H.Adj a c ∧ H.connectedComponentMk a = C
  symm := fun _ _ h =>
    ⟨h.1.symm, by rw [← ConnectedComponent.sound h.1.reachable]; exact h.2⟩
  loopless := ⟨fun _ h => H.irrefl h.1⟩

@[simp] theorem restrictComp_adj {H : SimpleGraph (Fin n)} {C : H.ConnectedComponent}
    {a c : Fin n} :
    (restrictComp H C).Adj a c ↔ H.Adj a c ∧ H.connectedComponentMk a = C := Iff.rfl

theorem edgeFinset_restrictComp (H : SimpleGraph (Fin n)) (C : H.ConnectedComponent) :
    (restrictComp H C).edgeFinset = compEdges H C := by
  ext e
  induction e with | _ a c =>
  rw [mem_compEdges, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact Iff.rfl

theorem degree_restrictComp_of_mem {H : SimpleGraph (Fin n)} {C : H.ConnectedComponent}
    {x : Fin n} (hx : H.connectedComponentMk x = C) :
    (restrictComp H C).degree x = H.degree x := by
  rw [SimpleGraph.degree, SimpleGraph.degree]
  congr 1
  ext w
  simp [hx]

theorem degree_restrictComp_of_notMem {H : SimpleGraph (Fin n)} {C : H.ConnectedComponent}
    {x : Fin n} (hx : H.connectedComponentMk x ≠ C) : (restrictComp H C).degree x = 0 := by
  rw [SimpleGraph.degree, Finset.card_eq_zero]
  ext w
  simp [hx]

/-- **The handshake lemma, one component at a time**: the degrees of a
component sum to twice its edges. A component with exactly one vertex of
odd degree therefore cannot exist — which is how the induction knows
that removing a vertex from a cycle leaves the rest connected. -/
theorem sum_degree_comp (H : SimpleGraph (Fin n)) (C : H.ConnectedComponent) :
    ∑ x ∈ {x ∈ (Finset.univ : Finset (Fin n)) | H.connectedComponentMk x = C}, H.degree x
      = 2 * (compEdges H C).card := by
  classical
  have h1 : (∑ x ∈ {x ∈ (Finset.univ : Finset (Fin n)) | H.connectedComponentMk x = C},
        H.degree x)
      = ∑ x ∈ {x ∈ (Finset.univ : Finset (Fin n)) | H.connectedComponentMk x = C},
          (restrictComp H C).degree x :=
    Finset.sum_congr rfl (fun x hx => (degree_restrictComp_of_mem (Finset.mem_filter.1 hx).2).symm)
  have h2 : (∑ x ∈ {x ∈ (Finset.univ : Finset (Fin n)) | H.connectedComponentMk x = C},
        (restrictComp H C).degree x)
      = ∑ x : Fin n, (restrictComp H C).degree x :=
    Finset.sum_subset (Finset.filter_subset _ _)
      (fun x _ hx => degree_restrictComp_of_notMem (by simpa using hx))
  rw [h1, h2, SimpleGraph.sum_degrees_eq_twice_card_edges, edgeFinset_restrictComp]

/-- **Cycles stay connected**: with every degree zero or two, isolating
a vertex keeps its two neighbours in one piece. Otherwise the piece of
one of them would be a component carrying a single odd degree. -/
theorem reachable_isolate_of_degree_two {H : SimpleGraph (Fin n)}
    (hdeg : ∀ x : Fin n, H.degree x = 0 ∨ H.degree x = 2) {v u w : Fin n}
    (hnb : H.neighborFinset v = {u, w}) (huw : u ≠ w) : (isolate H v).Reachable u w := by
  classical
  by_contra hcon
  have hvu : H.Adj v u := by rw [← mem_nbr, hnb]; exact Finset.mem_insert_self _ _
  have hvw : H.Adj v w := by
    rw [← mem_nbr, hnb]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have huv : u ≠ v := hvu.ne'
  have hiso : ∀ z, ¬ (isolate H v).Adj v z := not_adj_isolate H v
  have hdu : (isolate H v).degree u = 1 := by
    have hmem : v ∈ H.neighborFinset u := mem_nbr.2 hvu.symm
    have h2 : (H.neighborFinset u).card = 2 := by
      rcases hdeg u with h | h
      · exfalso
        rw [Finset.card_eq_zero.1 (show (H.neighborFinset u).card = 0 from h)] at hmem
        simp at hmem
      · exact h
    rw [SimpleGraph.degree, neighborFinset_isolate huv, Finset.card_erase_of_mem hmem, h2]
  have hsum := sum_degree_comp (isolate H v) ((isolate H v).connectedComponentMk u)
  have humem : u ∈ {x ∈ (Finset.univ : Finset (Fin n)) |
      (isolate H v).connectedComponentMk x = (isolate H v).connectedComponentMk u} :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  have heven : ∀ x ∈ ({x ∈ (Finset.univ : Finset (Fin n)) |
      (isolate H v).connectedComponentMk x = (isolate H v).connectedComponentMk u}).erase u,
      2 ∣ (isolate H v).degree x := by
    intro x hx
    obtain ⟨hxu, hxmem⟩ := Finset.mem_erase.1 hx
    have hxD : (isolate H v).connectedComponentMk x = (isolate H v).connectedComponentMk u :=
      (Finset.mem_filter.1 hxmem).2
    have hxv : x ≠ v := by
      rintro rfl
      exact hxu (eq_of_reachable_isolated hiso (ConnectedComponent.exact hxD)).symm
    have hxw : x ≠ w := by
      rintro rfl
      exact hcon (ConnectedComponent.exact hxD).symm
    have hvnb : v ∉ H.neighborFinset x := by
      rw [mem_nbr]
      intro hadj
      have hxin : x ∈ H.neighborFinset v := mem_nbr.2 hadj.symm
      rw [hnb, Finset.mem_insert, Finset.mem_singleton] at hxin
      rcases hxin with rfl | rfl
      · exact hxu rfl
      · exact hxw rfl
    have hdx : (isolate H v).degree x = H.degree x := by
      rw [SimpleGraph.degree, neighborFinset_isolate hxv, Finset.erase_eq_of_notMem hvnb,
        SimpleGraph.degree]
    rw [hdx]
    rcases hdeg x with h | h <;> simp [h]
  obtain ⟨k, hk⟩ := Finset.dvd_sum heven
  rw [← Finset.sum_erase_add _ _ humem, hdu, hk] at hsum
  omega

/-! ### The upper bound -/

/-- **The vertex to isolate**: the neighbour of a vertex of degree one
if there is one, and any endpoint of an edge otherwise. Either way,
isolating it buys a unit of cost. -/
theorem exists_isolate_drop {H : SimpleGraph (Fin n)} (hdeg : ∀ x : Fin n, H.degree x ≤ 2)
    (hne : H.edgeFinset.Nonempty) :
    ∃ v z, H.Adj v z ∧ compCost' (isolate H v) + 1 ≤ compCost' H := by
  classical
  by_cases hdeg1 : ∃ u : Fin n, H.degree u = 1
  · obtain ⟨u, hu⟩ := hdeg1
    obtain ⟨v, hv⟩ := Finset.card_eq_one.1 (show (H.neighborFinset u).card = 1 from hu)
    have hadj : H.Adj u v := by
      rw [← mem_nbr, hv]; exact Finset.mem_singleton_self _
    have hiso : ∀ z, ¬ (isolate H v).Adj u z := by
      intro z hz
      have hmem : z ∈ (isolate H v).neighborFinset u := mem_nbr.2 hz
      rw [neighborFinset_isolate hadj.ne, hv, Finset.erase_singleton] at hmem
      simp at hmem
    have hnoedge : (compEdges (isolate H v) ((isolate H v).connectedComponentMk u)).card = 0 := by
      by_contra h
      obtain ⟨x, c, hxc, hmk⟩ := exists_adj_of_card_compEdges_pos (Nat.pos_of_ne_zero h)
      have hxu : x = u := eq_of_reachable_isolated hiso (ConnectedComponent.exact hmk.symm)
      subst hxu
      exact hiso c hxc
    have hvpos : 1 ≤ (compEdges H (H.connectedComponentMk v)).card :=
      Finset.card_pos.2 ⟨s(v, u), mem_compEdges.2 ⟨hadj.symm, rfl⟩⟩
    have humem : u ∈ H.neighborFinset v := mem_nbr.2 hadj.symm
    have hdv : H.degree v = 1 ∨ H.degree v = 2 := by
      have h0 : H.degree v ≠ 0 := by
        intro h
        rw [Finset.card_eq_zero.1 (show (H.neighborFinset v).card = 0 from h)] at humem
        simp at humem
      have := hdeg v
      omega
    refine ⟨v, u, hadj.symm, compCost'_isolate_succ_le ?_⟩
    have hmain : ∀ w : Fin n, H.neighborFinset v = {u, w} →
        ((compEdges (isolate H v) ((isolate H v).connectedComponentMk w)).card + 2
            ≤ (compEdges H (H.connectedComponentMk v)).card ∨
          ((compEdges (isolate H v) ((isolate H v).connectedComponentMk w)).card = 0 ∧
            1 ≤ (compEdges H (H.connectedComponentMk v)).card)) →
        (∑ C' ∈ fiber (isolate_le H v) (H.connectedComponentMk v),
          ((compEdges (isolate H v) C').card + 1) / 2) + 1
          ≤ ((compEdges H (H.connectedComponentMk v)).card + 1) / 2 := by
      intro w hnb hcard
      have hvw : H.Adj v w := by
        rw [← mem_nbr, hnb]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      refine split_bound ((isolate H v).connectedComponentMk w) ?_
        (eq_comp_of_card_pos hnb (Or.inr hiso)) hcard
      rw [liftComp_mk]
      exact ConnectedComponent.sound hvw.symm.reachable
    rcases hdv with hdv | hdv
    · obtain ⟨u', hu'⟩ := Finset.card_eq_one.1 (show (H.neighborFinset v).card = 1 from hdv)
      have hu'u : u' = u := by
        rw [hu', Finset.mem_singleton] at humem
        exact humem.symm
      subst hu'u
      exact hmain u' (by rw [hu', Finset.pair_eq_singleton]) (Or.inr ⟨hnoedge, hvpos⟩)
    · obtain ⟨a, c, hac, hpair⟩ :=
        Finset.card_eq_two.1 (show (H.neighborFinset v).card = 2 from hdv)
      have humem' := humem
      rw [hpair, Finset.mem_insert, Finset.mem_singleton] at humem'
      have hleft : ∀ w : Fin n, H.neighborFinset v = {u, w} → u ≠ w →
          (compEdges (isolate H v) ((isolate H v).connectedComponentMk w)).card + 2
            ≤ (compEdges H (H.connectedComponentMk v)).card := by
        intro w hnb huw
        have hvw : H.Adj v w := by
          rw [← mem_nbr, hnb]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        exact card_compEdges_add_two_le hadj.symm hvw huw
      rcases humem' with rfl | rfl
      · exact hmain c hpair (Or.inl (hleft c hpair hac))
      · have hpair' : H.neighborFinset v = {u, a} := by rw [hpair, Finset.pair_comm]
        exact hmain a hpair' (Or.inl (hleft a hpair' (Ne.symm hac)))
  · push Not at hdeg1
    have hdeg2 : ∀ x : Fin n, H.degree x = 0 ∨ H.degree x = 2 := by
      intro x
      have := hdeg x
      have := hdeg1 x
      omega
    obtain ⟨e, he⟩ := hne
    induction e with | _ v z =>
    have hadj : H.Adj v z := by rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hzmem : z ∈ H.neighborFinset v := mem_nbr.2 hadj
    have hdv : H.degree v = 2 := by
      rcases hdeg2 v with h | h
      · exfalso
        rw [Finset.card_eq_zero.1 (show (H.neighborFinset v).card = 0 from h)] at hzmem
        simp at hzmem
      · exact h
    obtain ⟨a, c, hac, hpair⟩ := Finset.card_eq_two.1 (show (H.neighborFinset v).card = 2 from hdv)
    have hva : H.Adj v a := by rw [← mem_nbr, hpair]; exact Finset.mem_insert_self _ _
    have hvc : H.Adj v c := by
      rw [← mem_nbr, hpair]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    refine ⟨v, z, hadj, compCost'_isolate_succ_le ?_⟩
    refine split_bound ((isolate H v).connectedComponentMk c) ?_
      (eq_comp_of_card_pos hpair (Or.inl (reachable_isolate_of_degree_two hdeg2 hpair hac)))
      (Or.inl (card_compEdges_add_two_le hva hvc hac))
    rw [liftComp_mk]
    exact ConnectedComponent.sound hvc.symm.reachable

/-- **The upper bound, abstractly**: a graph of maximum degree two has a
vertex cover as cheap as its component cost. The induction isolates the
vertex `exists_isolate_drop` names, pays one for it, and recurses on a
graph with fewer edges. -/
theorem exists_isVertexCover_card_le_aux : ∀ (m : ℕ) (H : SimpleGraph (Fin n)),
    H.edgeFinset.card ≤ m → (∀ x : Fin n, H.degree x ≤ 2) →
    ∃ S : Finset (Fin n), H.IsVertexCover ↑S ∧ S.card ≤ compCost' H := by
  classical
  have hempty : ∀ H : SimpleGraph (Fin n), ¬ H.edgeFinset.Nonempty →
      ∃ S : Finset (Fin n), H.IsVertexCover ↑S ∧ S.card ≤ compCost' H := by
    intro H hne
    refine ⟨∅, fun a c hac => ?_, by simp⟩
    exact absurd ⟨s(a, c), by simpa using hac⟩ hne
  intro m
  induction m with
  | zero =>
      intro H hm _
      refine hempty H (fun hx => ?_)
      obtain ⟨e, he⟩ := hx
      rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hm)] at he
      simp at he
  | succ m ih =>
      intro H hm hdeg
      by_cases hne : H.edgeFinset.Nonempty
      · obtain ⟨v, z, hadj, hdrop⟩ := exists_isolate_drop hdeg hne
        have hlt := card_edgeFinset_isolate_lt hadj
        obtain ⟨S, hS, hcard⟩ := ih (isolate H v) (by omega)
          (fun x => le_trans (degree_isolate_le v x) (hdeg x))
        refine ⟨insert v S, fun a c hac => ?_, ?_⟩
        · by_cases hav : a = v
          · exact Or.inl (by simp [hav])
          by_cases hcv : c = v
          · exact Or.inr (by simp [hcv])
          · rcases hS (show (isolate H v).Adj a c from ⟨hac, hav, hcv⟩) with h | h
            · exact Or.inl (by simp only [Finset.coe_insert, Set.mem_insert_iff]; exact Or.inr h)
            · exact Or.inr (by simp only [Finset.coe_insert, Set.mem_insert_iff]; exact Or.inr h)
        · calc (insert v S).card ≤ S.card + 1 := Finset.card_insert_le _ _
            _ ≤ compCost' (isolate H v) + 1 := by omega
            _ ≤ compCost' H := hdrop
      · exact hempty H hne

theorem exists_isVertexCover_card_le (H : SimpleGraph (Fin n))
    (hdeg : ∀ x : Fin n, H.degree x ≤ 2) :
    ∃ S : Finset (Fin n), H.IsVertexCover ↑S ∧ S.card ≤ compCost' H :=
  exists_isVertexCover_card_le_aux _ H le_rfl hdeg

/-- **The upper bound at a node of the search**: with every unmarked
vertex of residual degree at most two, the solver's cost is affordable —
the marking together with a cheapest cover of the residual graph is a
cover of the whole graph. This is the solver's YES. -/
theorem ok_of_compCost_le (hdeg : ∀ v : Fin n, v ∉ M → resDeg G M v ≤ 2)
    (hb : compCost G M ≤ b) : Ok G M b := by
  classical
  obtain ⟨S, hS, hcard⟩ := exists_isVertexCover_card_le (R G M) (degree_R_le_two hdeg)
  refine ⟨M ∪ S, fun a c hac => ?_, Finset.subset_union_left, ?_⟩
  · by_cases ha : a ∈ M
    · exact Or.inl (by simp [ha])
    by_cases hc : c ∈ M
    · exact Or.inr (by simp [hc])
    · rcases hS (show (R G M).Adj a c from ⟨hac, ha, hc⟩) with h | h
      · exact Or.inl (by simp only [Finset.coe_union, Set.mem_union]; exact Or.inr h)
      · exact Or.inr (by simp only [Finset.coe_union, Set.mem_union]; exact Or.inr h)
  · have hsub : (M ∪ S) \ M ⊆ S := by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_union] at hx
      tauto
    calc ((M ∪ S) \ M).card ≤ S.card := Finset.card_le_card hsub
      _ ≤ compCost' (R G M) := hcard
      _ ≤ b := hb

/-- **The solver lemma**: at a node whose residual degrees are all at
most two, the budget suffices exactly when it covers the component cost.
The search does not guess here, it computes. -/
theorem ok_iff_compCost_le (hdeg : ∀ v : Fin n, v ∉ M → resDeg G M v ≤ 2) :
    Ok G M b ↔ compCost G M ≤ b := by
  constructor
  · intro h
    by_contra hlt
    exact not_ok_of_lt_compCost hdeg (by omega) h
  · exact ok_of_compCost_le hdeg

/-! ### The threshold-three scan -/

variable {g : List ℕ} {J : ℕ}

/-- An unmarked slot of an unmarked owner's block names a residual
neighbour. This is the step every transport in this file and in
`Residual.lean` takes; here it is once, as a lemma. -/
theorem exists_mem_resNbhd_of_slot (hg : EncodesGraph g n G) {o : Fin n} {j : ℕ}
    (h₁ : offset g (o : ℕ) ≤ j) (h₂ : j < offset g ((o : ℕ) + 1))
    (h₃ : target g j ∉ markedVals M) :
    ∃ w : Fin n, (w : ℕ) = target g j ∧ w ∈ ResNbhd G M o := by
  obtain ⟨ha, hb, hadj⟩ := adjn_of_slot hg o.2 h₁ h₂
  refine ⟨⟨target g j, hb⟩, rfl, mem_resNbhd.2 ⟨by simpa using hadj, ?_⟩⟩
  exact fun hm => h₃ ((mem_markedVals_iff hb).2 hm)

/-- **Three unmarked slots of one block with pairwise different targets
are three residual neighbours.** The threshold-three analogue of
`two_le_resDeg_of_slots`: the flag the descend scan raises names its
witness, and the witness is what the deeper branch spends budget on. -/
theorem three_le_resDeg_of_slots (hg : EncodesGraph g n G) {o : Fin n} {p₁ p₂ p₃ : ℕ}
    (ha₁ : offset g (o : ℕ) ≤ p₁) (hb₁ : p₁ < offset g ((o : ℕ) + 1))
    (ha₂ : offset g (o : ℕ) ≤ p₂) (hb₂ : p₂ < offset g ((o : ℕ) + 1))
    (ha₃ : offset g (o : ℕ) ≤ p₃) (hb₃ : p₃ < offset g ((o : ℕ) + 1))
    (hu₁ : target g p₁ ∉ markedVals M) (hu₂ : target g p₂ ∉ markedVals M)
    (hu₃ : target g p₃ ∉ markedVals M)
    (h₁₂ : target g p₁ ≠ target g p₂) (h₁₃ : target g p₁ ≠ target g p₃)
    (h₂₃ : target g p₂ ≠ target g p₃) : 3 ≤ resDeg G M o := by
  obtain ⟨w₁, hv₁, hm₁⟩ := exists_mem_resNbhd_of_slot hg ha₁ hb₁ hu₁
  obtain ⟨w₂, hv₂, hm₂⟩ := exists_mem_resNbhd_of_slot hg ha₂ hb₂ hu₂
  obtain ⟨w₃, hv₃, hm₃⟩ := exists_mem_resNbhd_of_slot hg ha₃ hb₃ hu₃
  rw [resDeg_eq_card]
  refine Finset.two_lt_card_iff.2 ⟨w₁, w₂, w₃, hm₁, hm₂, hm₃, ?_, ?_, ?_⟩
  · exact fun h => h₁₂ (by rw [← hv₁, ← hv₂, h])
  · exact fun h => h₁₃ (by rw [← hv₁, ← hv₃, h])
  · exact fun h => h₂₃ (by rw [← hv₂, ← hv₃, h])

/-- The residual blocks are thin at threshold three: the unmarked slots
in the block of an unmarked vertex name at most two different vertices.
This is what the descend scan certifies when it fails to find a vertex
to branch on. -/
def ThinBlocks3 (g : List ℕ) (M : Finset (Fin n)) : Prop :=
  ∀ o : Fin n, o ∉ M → ∀ j₁ j₂ j₃,
    offset g (o : ℕ) ≤ j₁ → j₁ < offset g ((o : ℕ) + 1) →
    offset g (o : ℕ) ≤ j₂ → j₂ < offset g ((o : ℕ) + 1) →
    offset g (o : ℕ) ≤ j₃ → j₃ < offset g ((o : ℕ) + 1) →
    target g j₁ ∉ markedVals M → target g j₂ ∉ markedVals M → target g j₃ ∉ markedVals M →
    target g j₁ = target g j₂ ∨ target g j₁ = target g j₃ ∨ target g j₂ = target g j₃

/-- **Thin blocks at threshold three are the solver's hypothesis**, and
conversely: an unmarked vertex with three residual neighbours is exactly
an unmarked vertex whose block names three different unmarked vertices.
The `thinBlocks_iff` of the first rung, one threshold up. -/
theorem thinBlocks3_iff (hg : EncodesGraph g n G) :
    ThinBlocks3 g M ↔ ∀ v : Fin n, v ∉ M → resDeg G M v ≤ 2 := by
  constructor
  · intro hthin v hv
    by_contra hlt
    rw [resDeg_eq_card] at hlt
    obtain ⟨w₁, w₂, w₃, hm₁, hm₂, hm₃, h₁₂, h₁₃, h₂₃⟩ :=
      Finset.two_lt_card_iff.1 (by omega : 2 < (ResNbhd G M v).card)
    obtain ⟨j₁, a₁, b₁, c₁, d₁⟩ := exists_slot_of_mem_resNbhd hg hm₁
    obtain ⟨j₂, a₂, b₂, c₂, d₂⟩ := exists_slot_of_mem_resNbhd hg hm₂
    obtain ⟨j₃, a₃, b₃, c₃, d₃⟩ := exists_slot_of_mem_resNbhd hg hm₃
    rcases hthin v hv j₁ j₂ j₃ a₁ b₁ a₂ b₂ a₃ b₃ d₁ d₂ d₃ with h | h | h
    · exact h₁₂ (Fin.ext (by rw [← c₁, ← c₂, h]))
    · exact h₁₃ (Fin.ext (by rw [← c₁, ← c₃, h]))
    · exact h₂₃ (Fin.ext (by rw [← c₂, ← c₃, h]))
  · intro hdeg o ho j₁ j₂ j₃ a₁ b₁ a₂ b₂ a₃ b₃ u₁ u₂ u₃
    by_contra hne
    push Not at hne
    obtain ⟨h₁₂, h₁₃, h₂₃⟩ := hne
    have := three_le_resDeg_of_slots hg a₁ b₁ a₂ b₂ a₃ b₃ u₁ u₂ u₃ h₁₂ h₁₃ h₂₃
    have := hdeg o ho
    omega

/-- Thin blocks at threshold three bound every residual degree by
two. -/
theorem resDeg_le_two_of_thinBlocks3 (hg : EncodesGraph g n G) (hthin : ThinBlocks3 g M) :
    ∀ v : Fin n, v ∉ M → resDeg G M v ≤ 2 :=
  (thinBlocks3_iff hg).1 hthin

end Lax15Proofs.VC3
