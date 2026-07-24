import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Sym.Sym2
import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor.Full

namespace Lax5Proofs.Source.Catalog.SparsityLectures.ShallowTopologicalMinor

open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor

/-- A depth-`d` topological minor model of `H` in `G`.

Each vertex of `H` is mapped injectively to a branch vertex of `G`. Every edge
of `H` is routed by a path between the corresponding branch vertices, of length
at most `2d + 1`. Internal routed vertices avoid all branch vertices, and the
internal vertices of routed paths for distinct edges are disjoint.
(Defs 1.12, 2.15-2.16) -/
structure ShallowTopologicalMinorModel {V W : Type}
    (H : SimpleGraph W) (G : SimpleGraph V) (d : ℕ) where
  branchVertex : W ↪ V
  edgeTail : H.edgeSet → W
  edgeTail_mem : ∀ e : H.edgeSet, edgeTail e ∈ (e : Sym2 W)
  edgePath : ∀ e : H.edgeSet,
    G.Walk (branchVertex (edgeTail e))
           (branchVertex (Sym2.Mem.other (edgeTail_mem e)))
  edgePath_isPath : ∀ e, (edgePath e).IsPath
  edgePath_length : ∀ e, (edgePath e).length ≤ 2 * d + 1
  edgePath_interior_avoids_branch :
    ∀ e {x : V},
      x ∈ (edgePath e).support →
      x ≠ branchVertex (edgeTail e) →
      x ≠ branchVertex (Sym2.Mem.other (edgeTail_mem e)) →
      ∀ w : W, x ≠ branchVertex w
  edgePath_interior_disjoint :
    ∀ e e' {x : V},
      e ≠ e' →
      x ∈ (edgePath e).support →
      x ∈ (edgePath e').support →
      x ≠ branchVertex (edgeTail e) →
      x ≠ branchVertex (Sym2.Mem.other (edgeTail_mem e)) →
      x ≠ branchVertex (edgeTail e') →
      x ≠ branchVertex (Sym2.Mem.other (edgeTail_mem e')) →
      False

/-- `H` is a depth-`d` topological minor of `G`. -/
def IsShallowTopologicalMinor {V W : Type}
    (H : SimpleGraph W) (G : SimpleGraph V) (d : ℕ) : Prop :=
  Nonempty (ShallowTopologicalMinorModel H G d)

noncomputable def ShallowTopologicalMinorModel.ofSubgraph
    {V W : Type} {H : SimpleGraph W} {G G' : SimpleGraph V} {d : ℕ}
    (m : ShallowTopologicalMinorModel H G d)
    (hsub : ∀ {u v}, G.Adj u v → G'.Adj u v) :
    ShallowTopologicalMinorModel H G' d :=
  { branchVertex := m.branchVertex
    edgeTail := m.edgeTail
    edgeTail_mem := m.edgeTail_mem
    edgePath := fun e => by
      let p := m.edgePath e
      have hedge : ∀ e' ∈ p.edges, e' ∈ G'.edgeSet := by
        intro e' he'
        have hmem := SimpleGraph.Walk.edges_subset_edgeSet p he'
        revert hmem
        refine e'.ind ?_
        intro a b hab
        exact show G'.Adj a b by exact hsub hab
      exact p.transfer G' hedge
    edgePath_isPath := by
      intro e
      let p := m.edgePath e
      have hedge : ∀ e' ∈ p.edges, e' ∈ G'.edgeSet := by
        intro e' he'
        have hmem := SimpleGraph.Walk.edges_subset_edgeSet p he'
        revert hmem
        refine e'.ind ?_
        intro a b hab
        exact show G'.Adj a b by exact hsub hab
      simpa [p] using (m.edgePath_isPath e).transfer hedge
    edgePath_length := by
      intro e
      let p := m.edgePath e
      have hedge : ∀ e' ∈ p.edges, e' ∈ G'.edgeSet := by
        intro e' he'
        have hmem := SimpleGraph.Walk.edges_subset_edgeSet p he'
        revert hmem
        refine e'.ind ?_
        intro a b hab
        exact show G'.Adj a b by exact hsub hab
      rw [show ((p.transfer G' hedge)).length = p.length by
        rw [SimpleGraph.Walk.length_transfer]]
      exact m.edgePath_length e
    edgePath_interior_avoids_branch := by
      intro e x hx htail hhead w
      let p := m.edgePath e
      have hedge : ∀ e' ∈ p.edges, e' ∈ G'.edgeSet := by
        intro e' he'
        have hmem := SimpleGraph.Walk.edges_subset_edgeSet p he'
        revert hmem
        refine e'.ind ?_
        intro a b hab
        exact show G'.Adj a b by exact hsub hab
      rw [show (p.transfer G' hedge).support = p.support by
        rw [SimpleGraph.Walk.support_transfer]] at hx
      exact m.edgePath_interior_avoids_branch e hx htail hhead w
    edgePath_interior_disjoint := by
      intro e e' x hne hx hx' htail hhead htail' hhead'
      let p := m.edgePath e
      let p' := m.edgePath e'
      have hedge : ∀ e'' ∈ p.edges, e'' ∈ G'.edgeSet := by
        intro e'' he''
        have hmem := SimpleGraph.Walk.edges_subset_edgeSet p he''
        revert hmem
        refine e''.ind ?_
        intro a b hab
        exact show G'.Adj a b by exact hsub hab
      have hedge' : ∀ e'' ∈ p'.edges, e'' ∈ G'.edgeSet := by
        intro e'' he''
        have hmem := SimpleGraph.Walk.edges_subset_edgeSet p' he''
        revert hmem
        refine e''.ind ?_
        intro a b hab
        exact show G'.Adj a b by exact hsub hab
      rw [show (p.transfer G' hedge).support = p.support by
        rw [SimpleGraph.Walk.support_transfer]] at hx
      rw [show (p'.transfer G' hedge').support = p'.support by
        rw [SimpleGraph.Walk.support_transfer]] at hx'
      exact m.edgePath_interior_disjoint e e' hne hx hx' htail hhead htail' hhead' }

theorem shallowTopologicalMinor_of_subgraph
    {V W : Type} {H : SimpleGraph W} {G G' : SimpleGraph V} {d : ℕ}
    (hsub : ∀ {u v}, G.Adj u v → G'.Adj u v) :
    IsShallowTopologicalMinor H G d → IsShallowTopologicalMinor H G' d := by
  rintro ⟨m⟩
  exact ⟨m.ofSubgraph hsub⟩

private def routedPathSplit {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (d : ℕ) : ℕ :=
  min d (p.length - 1)

private def routedPrefixVertices {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (d : ℕ) : Set V :=
  {x | ∃ i ≤ routedPathSplit p d, x = p.getVert i}

private def routedSuffixVertices {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (d : ℕ) : Set V :=
  {x | ∃ i, routedPathSplit p d + 1 ≤ i ∧ i ≤ p.length ∧ x = p.getVert i}

private def topologicalBranchSet {V W : Type}
    {H : SimpleGraph W} {G : SimpleGraph V} {d : ℕ}
    (m : ShallowTopologicalMinorModel H G d) (w : W) : Set V :=
  {x | x = m.branchVertex w ∨
      ∃ e : H.edgeSet,
        (m.edgeTail e = w ∧ x ∈ routedPrefixVertices (m.edgePath e) d) ∨
        (Sym2.Mem.other (m.edgeTail_mem e) = w ∧ x ∈ routedSuffixVertices (m.edgePath e) d)}

private theorem mem_topologicalBranchSet_center
    {V W : Type} {H : SimpleGraph W} {G : SimpleGraph V} {d : ℕ}
    (m : ShallowTopologicalMinorModel H G d) (w : W) :
    m.branchVertex w ∈ topologicalBranchSet m w := by
  left
  rfl

private theorem edgePath_internal_not_branchVertex
    {V W : Type} {H : SimpleGraph W} {G : SimpleGraph V} {d : ℕ}
    (m : ShallowTopologicalMinorModel H G d) (e : H.edgeSet) {i : ℕ}
    (hi0 : 0 < i) (hil : i < (m.edgePath e).length) :
    ∀ w : W, (m.edgePath e).getVert i ≠ m.branchVertex w := by
  intro w
  have hp := m.edgePath_isPath e
  have hne_tail : (m.edgePath e).getVert i ≠ m.branchVertex (m.edgeTail e) := by
    intro hEq
    have hi_eq : i = 0 := (hp.getVert_eq_start_iff hil.le).mp (by simpa using hEq)
    omega
  have hne_head : (m.edgePath e).getVert i ≠
      m.branchVertex (Sym2.Mem.other (m.edgeTail_mem e)) := by
    intro hEq
    have hi_eq : i = (m.edgePath e).length :=
      (hp.getVert_eq_end_iff hil.le).mp (by simpa using hEq)
    omega
  exact m.edgePath_interior_avoids_branch e ((m.edgePath e).getVert_mem_support i)
    hne_tail hne_head w

private theorem mem_topologicalBranchSet_noncenter
    {V W : Type} {H : SimpleGraph W} {G : SimpleGraph V} {d : ℕ}
    (m : ShallowTopologicalMinorModel H G d) {w : W} {x : V}
    (hx : x ∈ topologicalBranchSet m w) (hxc : x ≠ m.branchVertex w) :
    ∃ e : H.edgeSet, ∃ i : ℕ,
      x = (m.edgePath e).getVert i ∧
      0 < i ∧ i < (m.edgePath e).length ∧
      ((m.edgeTail e = w ∧ i ≤ routedPathSplit (m.edgePath e) d) ∨
        (Sym2.Mem.other (m.edgeTail_mem e) = w ∧
          routedPathSplit (m.edgePath e) d + 1 ≤ i)) := by
  rcases hx with rfl | ⟨e, hx⟩
  · exact (hxc rfl).elim
  · rcases hx with ⟨hw, hx⟩ | ⟨hw, hx⟩
    · rcases hx with ⟨i, hi, rfl⟩
      have hi_pos : 0 < i := by
        by_contra hi0
        apply hxc
        have : i = 0 := Nat.eq_zero_of_not_pos hi0
        simpa [hw, this] using (m.edgePath e).getVert_zero
      refine ⟨e, i, rfl, hi_pos, ?_, Or.inl ⟨hw, hi⟩⟩
      · have hi' : i ≤ (m.edgePath e).length - 1 := le_trans hi (Nat.min_le_right _ _)
        have hlen : 1 < (m.edgePath e).length := by
          exact Nat.sub_pos_iff_lt.mp (lt_of_lt_of_le hi_pos hi')
        have hsucc : i + 1 ≤ (m.edgePath e).length :=
          (Nat.le_sub_iff_add_le hlen.le).mp hi'
        exact lt_of_lt_of_le (Nat.lt_succ_self i) hsucc
    · rcases hx with ⟨i, hi, hilen, rfl⟩
      refine ⟨e, i, rfl, ?_, ?_, Or.inr ⟨hw, hi⟩⟩
      · omega
      · by_contra hlt
        have hi_eq : i = (m.edgePath e).length :=
          le_antisymm hilen (Nat.not_lt.mp hlt)
        apply hxc
        simpa [hw, hi_eq] using (m.edgePath e).getVert_length

private theorem topologicalBranchSet_disjoint
    {V W : Type} {H : SimpleGraph W} {G : SimpleGraph V} {d : ℕ}
    (m : ShallowTopologicalMinorModel H G d) :
    ∀ u v, u ≠ v → Disjoint (topologicalBranchSet m u) (topologicalBranchSet m v) := by
  intro u v huv
  refine Set.disjoint_left.mpr ?_
  intro x hxu hxv
  by_cases hxu0 : x = m.branchVertex u
  · by_cases hxv0 : x = m.branchVertex v
    · exact huv (m.branchVertex.injective (hxu0.symm.trans hxv0))
    · obtain ⟨e, i, hxi, hi0, hil, _⟩ := mem_topologicalBranchSet_noncenter m hxv hxv0
      exact (edgePath_internal_not_branchVertex m e hi0 hil u) (hxi.symm.trans hxu0)
  · by_cases hxv0 : x = m.branchVertex v
    · obtain ⟨e, i, hxi, hi0, hil, _⟩ := mem_topologicalBranchSet_noncenter m hxu hxu0
      exact (edgePath_internal_not_branchVertex m e hi0 hil v) (hxi.symm.trans hxv0)
    · obtain ⟨e, i, hxi, hi0, hil, hside_u⟩ := mem_topologicalBranchSet_noncenter m hxu hxu0
      obtain ⟨e', j, hxj, hj0, hjl, hside_v⟩ := mem_topologicalBranchSet_noncenter m hxv hxv0
      by_cases he : e = e'
      · subst e'
        have hp := m.edgePath_isPath e
        have hij : i = j := hp.getVert_injOn (by simp [hil.le]) (by simp [hjl.le])
          (hxi.symm.trans hxj)
        rcases hside_u with ⟨hu, hi_le⟩ | ⟨hu, hi_ge⟩
        · rcases hside_v with ⟨hv, hj_le⟩ | ⟨hv, hj_ge⟩
          · exact huv (hu.symm.trans hv)
          · have : i < j := by omega
            exact this.ne hij
        · rcases hside_v with ⟨hv, hj_le⟩ | ⟨hv, hj_ge⟩
          · have : j < i := by omega
            exact this.ne hij.symm
          · exact huv (hu.symm.trans hv)
      · have hx_support : x ∈ (m.edgePath e).support := by
          rw [hxi]
          exact (m.edgePath e).getVert_mem_support i
        have hx_support' : x ∈ (m.edgePath e').support := by
          rw [hxj]
          exact (m.edgePath e').getVert_mem_support j
        have hne_tail : x ≠ m.branchVertex (m.edgeTail e) := by
          simpa [hxi] using (edgePath_internal_not_branchVertex m e hi0 hil (m.edgeTail e))
        have hne_head : x ≠ m.branchVertex (Sym2.Mem.other (m.edgeTail_mem e)) := by
          simpa [hxi] using
            (edgePath_internal_not_branchVertex m e hi0 hil
              (Sym2.Mem.other (m.edgeTail_mem e)))
        have hne_tail' : x ≠ m.branchVertex (m.edgeTail e') := by
          simpa [hxj] using
            (edgePath_internal_not_branchVertex m e' hj0 hjl (m.edgeTail e'))
        have hne_head' : x ≠ m.branchVertex (Sym2.Mem.other (m.edgeTail_mem e')) := by
          simpa [hxj] using
            (edgePath_internal_not_branchVertex m e' hj0 hjl
              (Sym2.Mem.other (m.edgeTail_mem e')))
        exact m.edgePath_interior_disjoint e e' he hx_support hx_support'
          hne_tail hne_head hne_tail' hne_head'

private theorem topologicalBranchSet_radius
    {V W : Type} {H : SimpleGraph W} {G : SimpleGraph V} {d : ℕ}
    (m : ShallowTopologicalMinorModel H G d) :
    ∀ v x, x ∈ topologicalBranchSet m v →
      ∃ p : G.Walk (m.branchVertex v) x, p.IsPath ∧ p.length ≤ d ∧
        ∀ w ∈ p.support, w ∈ topologicalBranchSet m v := by
  intro v x hx
  rcases hx with rfl | ⟨e, hx⟩
  · refine ⟨SimpleGraph.Walk.nil, by simp, by simp, ?_⟩
    intro w hw
    simp at hw
    simpa [hw] using mem_topologicalBranchSet_center m v
  · rcases hx with ⟨hv, hx⟩ | ⟨hv, hx⟩
    · rcases hx with ⟨i, hi, rfl⟩
      let p := m.edgePath e
      have hi_len : i ≤ p.length := by
        exact le_trans hi (le_trans (Nat.min_le_right d (p.length - 1)) (Nat.sub_le _ _))
      refine ⟨(p.take i).copy (by simpa [hv]) rfl, ?_, ?_, ?_⟩
      · simpa [p] using (m.edgePath_isPath e).take i
      · rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length, Nat.min_eq_left hi_len]
        exact le_trans hi (Nat.min_le_left d (p.length - 1))
      · intro w hw
        have hw' : w ∈ (p.take i).support := by simpa using hw
        rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw' with ⟨j, rfl, hj⟩
        have hj' : j ≤ i := by
          rwa [SimpleGraph.Walk.take_length, Nat.min_eq_left hi_len] at hj
        right
        refine ⟨e, Or.inl ?_⟩
        refine ⟨hv, ⟨j, le_trans hj' hi, ?_⟩⟩
        rw [SimpleGraph.Walk.take_getVert]
        simpa [p, Nat.min_eq_right hj']
    · rcases hx with ⟨i, hi_split, hi_len, rfl⟩
      let p := m.edgePath e
      have hi_split' : routedPathSplit p d + 1 ≤ i := by simpa [p] using hi_split
      have hi_len' : i ≤ p.length := by simpa [p] using hi_len
      have hp_len : p.length ≤ 2 * d + 1 := by simpa [p] using m.edgePath_length e
      have hdrop_len : p.length - i ≤ d := by
        dsimp [routedPathSplit] at hi_split'
        by_cases hmin : d ≤ p.length - 1
        · rw [Nat.min_eq_left hmin] at hi_split'
          omega
        · rw [Nat.min_eq_right (Nat.le_of_not_ge hmin)] at hi_split'
          omega
      refine ⟨((p.drop i).reverse).copy (by simpa [hv]) rfl, ?_, ?_, ?_⟩
      · simpa [p] using ((m.edgePath_isPath e).drop i).reverse
      · rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.drop_length]
        exact hdrop_len
      · intro w hw
        have hw' : w ∈ ((p.drop i).reverse).support := by simpa using hw
        rw [SimpleGraph.Walk.support_reverse] at hw'
        have hw'' : w ∈ (p.drop i).support := List.mem_reverse.mp hw'
        rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw'' with ⟨j, rfl, hj⟩
        have hij : i + j ≤ p.length := by
          rw [SimpleGraph.Walk.drop_length] at hj
          simpa [Nat.add_comm] using Nat.add_le_of_le_sub hi_len' hj
        right
        refine ⟨e, Or.inr ?_⟩
        refine ⟨hv, ⟨i + j, le_trans hi_split' (Nat.le_add_right _ _), hij, ?_⟩⟩
        rw [SimpleGraph.Walk.drop_getVert]

private theorem topologicalBranchSet_edge
    {V W : Type} {H : SimpleGraph W} {G : SimpleGraph V} {d : ℕ}
    (m : ShallowTopologicalMinorModel H G d) :
    ∀ u v, H.Adj u v →
      ∃ x ∈ topologicalBranchSet m u, ∃ y ∈ topologicalBranchSet m v, G.Adj x y := by
  intro u v huv
  let e : H.edgeSet := ⟨s(u, v), huv⟩
  let p := m.edgePath e
  let s := routedPathSplit p d
  have htail_mem : m.edgeTail e ∈ (e : Sym2 W) := m.edgeTail_mem e
  have hother_ne : Sym2.Mem.other htail_mem ≠ m.edgeTail e :=
    H.edge_other_ne e.property htail_mem
  have hp_not_nil : ¬ p.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    intro hEq
    exact hother_ne (m.branchVertex.injective hEq.symm)
  have hs_lt : s < p.length := by
    have hp_pos : 0 < p.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp hp_not_nil
    dsimp [s, routedPathSplit]
    exact lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hp_pos (by decide))
  have htail_cases : m.edgeTail e = u ∨ m.edgeTail e = v := by
    simpa [e] using htail_mem
  rcases htail_cases with htail_u | htail_v
  · have hother_v : Sym2.Mem.other htail_mem = v := by
      have hmem : Sym2.Mem.other htail_mem ∈ (e : Sym2 W) := Sym2.other_mem htail_mem
      have hne : Sym2.Mem.other htail_mem ≠ u := by simpa [htail_u] using hother_ne
      have hmem' : Sym2.Mem.other htail_mem = u ∨ Sym2.Mem.other htail_mem = v := by
        simpa [e] using hmem
      exact hmem'.resolve_left hne
    refine ⟨p.getVert s, ?_, p.getVert (s + 1), ?_, p.adj_getVert_succ hs_lt⟩
    · right
      refine ⟨e, Or.inl ?_⟩
      refine ⟨htail_u, ?_⟩
      exact ⟨s, le_rfl, rfl⟩
    · right
      refine ⟨e, Or.inr ?_⟩
      refine ⟨hother_v, ?_⟩
      exact ⟨s + 1, le_rfl, Nat.succ_le_of_lt hs_lt, rfl⟩
  · have hother_u : Sym2.Mem.other htail_mem = u := by
      have hmem : Sym2.Mem.other htail_mem ∈ (e : Sym2 W) := Sym2.other_mem htail_mem
      have hne : Sym2.Mem.other htail_mem ≠ v := by simpa [htail_v] using hother_ne
      have hmem' : Sym2.Mem.other htail_mem = u ∨ Sym2.Mem.other htail_mem = v := by
        simpa [e] using hmem
      exact hmem'.resolve_right hne
    refine ⟨p.getVert (s + 1), ?_, p.getVert s, ?_, (p.adj_getVert_succ hs_lt).symm⟩
    · right
      refine ⟨e, Or.inr ?_⟩
      refine ⟨hother_u, ?_⟩
      exact ⟨s + 1, le_rfl, Nat.succ_le_of_lt hs_lt, rfl⟩
    · right
      refine ⟨e, Or.inl ?_⟩
      refine ⟨htail_v, ?_⟩
      exact ⟨s, le_rfl, rfl⟩

private def ShallowTopologicalMinorModel.toShallowMinorModel
    {V W : Type} {H : SimpleGraph W} {G : SimpleGraph V} {d : ℕ}
    (m : ShallowTopologicalMinorModel H G d) : ShallowMinorModel H G d :=
  { branchSet := topologicalBranchSet m
    center := m.branchVertex
    center_mem := mem_topologicalBranchSet_center m
    branchDisjoint := topologicalBranchSet_disjoint m
    branchRadius := topologicalBranchSet_radius m
    branchEdge := topologicalBranchSet_edge m }

/-- Every depth-`d` shallow topological minor is a depth-`d` shallow minor. -/
theorem shallowTopologicalMinor_toShallowMinor
    {V W : Type} {H : SimpleGraph W} {G : SimpleGraph V} {d : ℕ} :
    IsShallowTopologicalMinor H G d → IsShallowMinor H G d := by
  rintro ⟨m⟩
  exact ⟨m.toShallowMinorModel⟩

end Lax5Proofs.Source.Catalog.SparsityLectures.ShallowTopologicalMinor
