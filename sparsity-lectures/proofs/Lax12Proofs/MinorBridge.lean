import Lax12.NowhereDenseClasses
import Lax12.ShallowMinorDensity
import Lax12.ShallowTopologicalMinors
import Lax12Proofs.ShallowMinors
import Lax12Proofs.TopologicalMinors
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
The bridge between the minor notions of the submitted concepts, which
range over the canonical carriers `Fin n` and are stated with walks, and
the minor notions of the ported sparsity development, which range over
arbitrary finite vertex types and are stated with paths.

The shallow-minor direction is a pointwise repackaging in both
directions: a path is a walk, and a walk bypasses to a path with a
smaller support.  The topological direction additionally has to move
between the concept's walks indexed by adjacent *pairs* and the ported
model's routed paths indexed by the *edge set*, which is where the `Sym2`
plumbing lives.

The file also collects the concept-level helpers the headline glue proof
consumes: nowhere denseness of the subgraph closure, the vertex bound for
shallow minors, the fact that a depth-`r` topological minor is a depth-`r`
minor, and the edge-count bridge between `Set.ncard` and `edgeFinset`.
-/

namespace Lax12Proofs.MinorBridge

open scoped SimpleGraph
open Lax12.NowhereDenseClasses Lax12.ShallowMinorDensity
open Lax12.ShallowTopologicalMinors
open Lax12Proofs.TopologicalMinors

/-! ### Edge counts -/

/-- The natural cardinality of the edge set is the cardinality of the
edge finset. -/
theorem ncard_edgeSet {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] : H.edgeSet.ncard = H.edgeFinset.card := by
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]

/-- A simple graph on `m` vertices has at most `m * m` edges. -/
theorem edgeFinset_card_le_sq {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] :
    H.edgeFinset.card ≤ Fintype.card V * Fintype.card V := by
  calc H.edgeFinset.card
      ≤ (Fintype.card V).choose 2 := SimpleGraph.card_edgeFinset_le_card_choose_two
    _ = Fintype.card V * (Fintype.card V - 1) / 2 := Nat.choose_two_right _
    _ ≤ Fintype.card V * (Fintype.card V - 1) := Nat.div_le_self _ 2
    _ ≤ Fintype.card V * Fintype.card V := Nat.mul_le_mul_left _ (Nat.sub_le _ 1)

/-! ### Shallow minors: concept versus ported development -/

/-- A ported minor model gives a concept minor model: paths are walks. -/
theorem hasShallowMinor_of_isShallowMinor {V W : Type}
    {H : SimpleGraph W} {G : SimpleGraph V} {r : ℕ}
    (h : Lax12Proofs.ShallowMinors.IsShallowMinor H G r) :
    HasShallowMinor G r H := by
  obtain ⟨M⟩ := h
  exact ⟨{ branch := M.branchSet
           center := M.center
           center_mem := M.center_mem
           disjoint := M.branchDisjoint
           radius_le := fun u x hx => by
             obtain ⟨p, _, hlen, hsupp⟩ := M.branchRadius u x hx
             exact ⟨p, hlen, hsupp⟩
           adj := M.branchEdge }⟩

/-- A concept minor model gives a ported minor model: bypassing a walk
yields a path with a smaller support. -/
theorem isShallowMinor_of_hasShallowMinor {V W : Type}
    {H : SimpleGraph W} {G : SimpleGraph V} {r : ℕ}
    (h : HasShallowMinor G r H) :
    Lax12Proofs.ShallowMinors.IsShallowMinor H G r := by
  classical
  obtain ⟨M⟩ := h
  exact ⟨{ branchSet := M.branch
           center := M.center
           center_mem := M.center_mem
           branchDisjoint := M.disjoint
           branchRadius := fun u x hx => by
             obtain ⟨w, hlen, hsupp⟩ := M.radius_le u x hx
             exact ⟨w.bypass, w.bypass_isPath, w.length_bypass_le.trans hlen,
               fun y hy => hsupp y (w.support_bypass_subset hy)⟩
           branchEdge := M.adj }⟩

/-- A shallow minor has at most as many vertices as its host: the branch
sets are nonempty and pairwise disjoint. -/
theorem card_le_of_hasShallowMinor {V W : Type*} [Fintype V] [Fintype W]
    {H : SimpleGraph W} {G : SimpleGraph V} {r : ℕ}
    (h : HasShallowMinor G r H) : Fintype.card W ≤ Fintype.card V := by
  obtain ⟨M⟩ := h
  refine Fintype.card_le_of_injective M.center fun u v huv => ?_
  by_contra hne
  exact Set.disjoint_left.1 (M.disjoint u v hne) (M.center_mem u) (huv ▸ M.center_mem v)

/-! ### Graph classes: the subgraph closure -/

/-- The closure of a submitted class under subgraph copies, as a
submitted class. -/
def closure (C : Lax12.GraphClasses.GraphClass) : Lax12.GraphClasses.GraphClass :=
  fun m H => ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧ H ⊑ G

/-- The type-polymorphic closure of a submitted class under subgraph
copies, as a class of the ported development. -/
def subgraphClosure (C : Lax12.GraphClasses.GraphClass) :
    Lax12Proofs.ShallowMinors.GraphClass :=
  fun {_} _ _ H => ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧ H ⊑ G

/-- Every member of a class is a member of its subgraph closure. -/
theorem subgraphClosure_self {n : ℕ} {C : Lax12.GraphClasses.GraphClass}
    {G : SimpleGraph (Fin n)} (hG : C n G) : subgraphClosure C G :=
  ⟨n, G, hG, SimpleGraph.IsContained.refl G⟩

/-- Push a ported minor model through a graph copy. -/
private theorem isShallowMinor_of_copy {U W V : Type}
    {K : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V} {r : ℕ}
    (f : SimpleGraph.Copy H G) (h : Lax12Proofs.ShallowMinors.IsShallowMinor K H r) :
    Lax12Proofs.ShallowMinors.IsShallowMinor K G r := by
  obtain ⟨M⟩ := h
  refine ⟨{
    branchSet := fun u => f '' M.branchSet u
    center := fun u => f (M.center u)
    center_mem := fun u => ⟨M.center u, M.center_mem u, rfl⟩
    branchDisjoint := fun u v huv => ?_
    branchRadius := fun u x hx => ?_
    branchEdge := fun u v hadj => ?_ }⟩
  · exact Set.disjoint_image_of_injective f.injective (M.branchDisjoint u v huv)
  · obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨p, hp, hlen, hsupp⟩ := M.branchRadius u y hy
    refine ⟨p.map f.toHom,
      SimpleGraph.Walk.map_isPath_of_injective f.injective hp, ?_, ?_⟩
    · rw [SimpleGraph.Walk.length_map]; exact hlen
    · intro w hw
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hw
      obtain ⟨z, hz, rfl⟩ := hw
      exact ⟨z, hsupp z hz, rfl⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := M.branchEdge u v hadj
    exact ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩, f.toHom.map_adj hxy⟩

/-- Push a concept minor model through a graph copy. -/
theorem hasShallowMinor_of_copy {m n k : ℕ} {r : ℕ}
    {K : SimpleGraph (Fin k)} {H : SimpleGraph (Fin m)} {G : SimpleGraph (Fin n)}
    (f : H ⊑ G) (h : HasShallowMinor H r K) : HasShallowMinor G r K := by
  obtain ⟨f⟩ := f
  exact hasShallowMinor_of_isShallowMinor
    (isShallowMinor_of_copy f (isShallowMinor_of_hasShallowMinor h))

/-- Nowhere denseness of a class transfers to its subgraph closure. -/
theorem nowhereDense_closure {C : Lax12.GraphClasses.GraphClass}
    (h : NowhereDense C) : NowhereDense (closure C) := by
  intro r
  obtain ⟨t, ht⟩ := h r
  refine ⟨t, ?_⟩
  rintro m H ⟨n, G, hG, hHG⟩ hminor
  exact ht n G hG (hasShallowMinor_of_copy hHG hminor)

/-- Nowhere denseness of a class transfers to the ported formulation for
the subgraph closure. -/
theorem isNowhereDense_subgraphClosure {C : Lax12.GraphClasses.GraphClass}
    (h : NowhereDense C) :
    Lax12Proofs.ShallowMinors.IsNowhereDense (subgraphClosure C) := by
  intro r
  obtain ⟨t, ht⟩ := h r
  refine ⟨t, fun {V} _ _ H hH hminor => ?_⟩
  obtain ⟨n, G, hG, ⟨f⟩⟩ := hH
  obtain ⟨M⟩ := hasShallowMinor_of_isShallowMinor (isShallowMinor_of_copy f hminor)
  have hle : t ≤ t + 1 := Nat.le_succ t
  refine ht n G hG ⟨{
    branch := fun u => M.branch (Fin.castLE hle u)
    center := fun u => M.center (Fin.castLE hle u)
    center_mem := fun u => M.center_mem _
    disjoint := fun u v huv =>
      M.disjoint _ _ fun hc => huv (Fin.castLE_injective hle hc)
    radius_le := fun u => M.radius_le _
    adj := fun u v huv => by
      have hne : u ≠ v := by simpa using huv
      exact M.adj _ _ (by simpa using fun hc => hne (Fin.castLE_injective hle hc)) }⟩

/-! ### Shallow topological minors: concept versus ported development

The concept indexes connecting walks by adjacent *pairs*, the ported
development by the *edge set* together with a chosen tail.  Both
translations therefore have to name, for an ordered pair `(u, v)`, the
edge `s(u, v)` and decide whether its ported tail is `u` or `v`. -/

section Topological

variable {V W : Type} {H : SimpleGraph W} {G : SimpleGraph V} {r : ℕ}

/-- The edge of `H` carried by an adjacent ordered pair. -/
private def edgeOf {u v : W} (huv : H.Adj u v) : H.edgeSet := ⟨s(u, v), huv⟩

private theorem tail_other (M : ShallowTopologicalMinorModel H G r) {u v : W}
    (huv : H.Adj u v) :
    (M.edgeTail (edgeOf huv) = u ∧
      Sym2.Mem.other (M.edgeTail_mem (edgeOf huv)) = v) ∨
    (M.edgeTail (edgeOf huv) = v ∧
      Sym2.Mem.other (M.edgeTail_mem (edgeOf huv)) = u) :=
  Sym2.eq_iff.1 (Sym2.other_spec (M.edgeTail_mem (edgeOf huv)))

private theorem other_eq_right (M : ShallowTopologicalMinorModel H G r) {u v : W}
    (huv : H.Adj u v) (h : M.edgeTail (edgeOf huv) = u) :
    Sym2.Mem.other (M.edgeTail_mem (edgeOf huv)) = v := by
  rcases tail_other M huv with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h2
  · exact absurd (h.symm.trans h1) huv.ne

private theorem other_eq_left (M : ShallowTopologicalMinorModel H G r) {u v : W}
    (huv : H.Adj u v) (h : M.edgeTail (edgeOf huv) = v) :
    Sym2.Mem.other (M.edgeTail_mem (edgeOf huv)) = u := by
  rcases tail_other M huv with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact absurd (h1.symm.trans h) huv.ne
  · exact h2

private theorem tail_eq (M : ShallowTopologicalMinorModel H G r) {u v : W}
    (huv : H.Adj u v) :
    M.edgeTail (edgeOf huv) = u ∨ M.edgeTail (edgeOf huv) = v :=
  (tail_other M huv).imp And.left And.left

open Classical in
/-- The routed path of the edge `s(u, v)`, oriented from `u` to `v`. -/
private noncomputable def orientedPath (M : ShallowTopologicalMinorModel H G r)
    {u v : W} (huv : H.Adj u v) :
    G.Walk (M.branchVertex u) (M.branchVertex v) :=
  if h : M.edgeTail (edgeOf huv) = u then
    (M.edgePath (edgeOf huv)).copy (congrArg M.branchVertex h)
      (congrArg M.branchVertex (other_eq_right M huv h))
  else
    have h' : M.edgeTail (edgeOf huv) = v := (tail_eq M huv).resolve_left h
    ((M.edgePath (edgeOf huv)).copy (congrArg M.branchVertex h')
      (congrArg M.branchVertex (other_eq_left M huv h'))).reverse

private theorem orientedPath_support (M : ShallowTopologicalMinorModel H G r)
    {u v : W} (huv : H.Adj u v) {x : V} (hx : x ∈ (orientedPath M huv).support) :
    x ∈ (M.edgePath (edgeOf huv)).support := by
  unfold orientedPath at hx
  split at hx
  · rwa [SimpleGraph.Walk.support_copy] at hx
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse,
      SimpleGraph.Walk.support_copy] at hx
    exact hx

private theorem orientedPath_length (M : ShallowTopologicalMinorModel H G r)
    {u v : W} (huv : H.Adj u v) :
    (orientedPath M huv).length = (M.edgePath (edgeOf huv)).length := by
  unfold orientedPath
  split
  · rw [SimpleGraph.Walk.length_copy]
  · rw [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_copy]

/-- A ported topological minor model gives a concept topological minor
model. -/
theorem hasShallowTopologicalMinor_of_isShallowTopologicalMinor
    (h : IsShallowTopologicalMinor H G r) : HasShallowTopologicalMinor G r H := by
  obtain ⟨M⟩ := h
  refine ⟨{
    principal := M.branchVertex
    principal_inj := M.branchVertex.injective
    walk := fun u v huv => orientedPath M huv
    length_le := fun u v huv => by
      rw [orientedPath_length M huv]; exact M.edgePath_length _
    principal_eq := ?_
    disjoint := ?_ }⟩
  · intro u v huv w hw
    by_contra hcon
    push_neg at hcon
    have hx := orientedPath_support M huv hw
    have h1 : M.branchVertex w ≠ M.branchVertex (M.edgeTail (edgeOf huv)) := by
      intro hc
      rcases tail_eq M huv with h | h
      · exact hcon.1 (M.branchVertex.injective (h ▸ hc))
      · exact hcon.2 (M.branchVertex.injective (h ▸ hc))
    have h2 : M.branchVertex w ≠
        M.branchVertex (Sym2.Mem.other (M.edgeTail_mem (edgeOf huv))) := by
      intro hc
      by_cases h : M.edgeTail (edgeOf huv) = u
      · exact hcon.2 (M.branchVertex.injective (other_eq_right M huv h ▸ hc))
      · have h' : M.edgeTail (edgeOf huv) = v := (tail_eq M huv).resolve_left h
        exact hcon.1 (M.branchVertex.injective (other_eq_left M huv h' ▸ hc))
    exact M.edgePath_interior_avoids_branch _ hx h1 h2 w rfl
  · intro u v huv u' v' huv' x hx hx' hrange
    by_contra hcon
    have hne : edgeOf huv ≠ edgeOf huv' := by
      intro hc
      have hs : (s(u, v) : Sym2 W) = s(u', v') := congrArg Subtype.val hc
      rw [Sym2.eq_iff] at hs
      exact hcon (by tauto)
    have hb : ∀ w : W, x ≠ M.branchVertex w := fun w hw => hrange ⟨w, hw.symm⟩
    exact M.edgePath_interior_disjoint _ _ hne (orientedPath_support M huv hx)
      (orientedPath_support M huv' hx') (hb _) (hb _) (hb _) (hb _)

/-! ### The concept model as a ported model -/

private theorem exists_mem_sym2 (e : Sym2 W) : ∃ w : W, w ∈ e :=
  e.ind fun a b => ⟨a, Sym2.mem_mk_left a b⟩

/-- A chosen end of an unordered pair. -/
private noncomputable def pick (e : Sym2 W) : W := (exists_mem_sym2 e).choose

private theorem pick_mem (e : Sym2 W) : pick e ∈ e := (exists_mem_sym2 e).choose_spec

/-- A concept topological minor model gives a ported topological minor
model: the chosen end of an edge orients it, and bypassing the connecting
walk turns it into a routed path with a smaller support. -/
theorem isShallowTopologicalMinor_of_hasShallowTopologicalMinor
    (h : HasShallowTopologicalMinor G r H) : IsShallowTopologicalMinor H G r := by
  classical
  obtain ⟨M⟩ := h
  -- the two ends of an edge, in the order given by `pick`
  have hspec : ∀ e : H.edgeSet,
      (s(pick (e : Sym2 W), Sym2.Mem.other (pick_mem (e : Sym2 W))) : Sym2 W) = (e : Sym2 W) :=
    fun e => Sym2.other_spec (pick_mem (e : Sym2 W))
  have hadj : ∀ e : H.edgeSet,
      H.Adj (pick (e : Sym2 W)) (Sym2.Mem.other (pick_mem (e : Sym2 W))) := by
    intro e
    have := e.2
    rw [← hspec e] at this
    exact this
  refine ⟨{
    branchVertex := ⟨M.principal, M.principal_inj⟩
    edgeTail := fun e => pick (e : Sym2 W)
    edgeTail_mem := fun e => pick_mem (e : Sym2 W)
    edgePath := fun e => (M.walk _ _ (hadj e)).bypass
    edgePath_isPath := fun e => SimpleGraph.Walk.bypass_isPath _
    edgePath_length := fun e =>
      (SimpleGraph.Walk.length_bypass_le _).trans (M.length_le _ _ (hadj e))
    edgePath_interior_avoids_branch := ?_
    edgePath_interior_disjoint := ?_ }⟩
  · intro e x hx hne1 hne2 w hxw
    have hx' : x ∈ (M.walk _ _ (hadj e)).support :=
      SimpleGraph.Walk.support_bypass_subset _ hx
    rw [hxw] at hx'
    rcases M.principal_eq _ _ (hadj e) w hx' with h | h
    · exact hne1 (by rw [hxw, h])
    · exact hne2 (by rw [hxw, h])
  · intro e e' x hne hx hx' hne1 hne2 hne3 hne4
    have hxs : x ∈ (M.walk _ _ (hadj e)).support :=
      SimpleGraph.Walk.support_bypass_subset _ hx
    have hxs' : x ∈ (M.walk _ _ (hadj e')).support :=
      SimpleGraph.Walk.support_bypass_subset _ hx'
    have hrange : x ∉ Set.range M.principal := by
      rintro ⟨w, rfl⟩
      rcases M.principal_eq _ _ (hadj e) w hxs with h | h
      · exact hne1 (by rw [h]; rfl)
      · exact hne2 (by rw [h]; rfl)
    rcases M.disjoint _ _ (hadj e) _ _ (hadj e') x hxs hxs' hrange with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hne (Subtype.ext
        ((hspec e).symm.trans ((Sym2.eq_iff.2 (Or.inl ⟨h1, h2⟩)).trans (hspec e'))))
    · exact hne (Subtype.ext
        ((hspec e).symm.trans ((Sym2.eq_iff.2 (Or.inr ⟨h1, h2⟩)).trans (hspec e'))))

/-- A depth-`r` topological minor is a depth-`r` minor. -/
theorem hasShallowMinor_of_hasShallowTopologicalMinor
    (h : HasShallowTopologicalMinor G r H) : HasShallowMinor G r H :=
  hasShallowMinor_of_isShallowMinor
    (shallowTopologicalMinor_toShallowMinor
      (isShallowTopologicalMinor_of_hasShallowTopologicalMinor h))

/-- Transport a concept topological minor model along an isomorphism of
the minor. -/
theorem hasShallowTopologicalMinor_of_iso {V W W' : Type*} {H : SimpleGraph W}
    {H' : SimpleGraph W'} {G : SimpleGraph V} {r : ℕ} (f : H' ≃g H)
    (h : HasShallowTopologicalMinor G r H) : HasShallowTopologicalMinor G r H' := by
  obtain ⟨M⟩ := h
  have hrange : ∀ x : V, x ∉ Set.range (fun w : W' => M.principal (f w)) →
      x ∉ Set.range M.principal := by
    rintro x hx ⟨w, rfl⟩
    exact hx ⟨f.symm w, by simp⟩
  refine ⟨{
    principal := fun w => M.principal (f w)
    principal_inj := fun a b hab => f.injective (M.principal_inj hab)
    walk := fun u v huv => M.walk (f u) (f v) (f.map_adj_iff.2 huv)
    length_le := fun u v huv => M.length_le _ _ _
    principal_eq := fun u v huv w hw =>
      (M.principal_eq _ _ _ (f w) hw).imp (fun h => f.injective h) (fun h => f.injective h)
    disjoint := fun u v huv u' v' huv' x hx hx' hx'' =>
      ((M.disjoint _ _ _ _ _ _ x hx hx' (hrange x hx'')).imp
        (fun h => ⟨f.injective h.1, f.injective h.2⟩)
        (fun h => ⟨f.injective h.1, f.injective h.2⟩)) }⟩

end Topological

/-- An edge-density bound for the depth-`r` minors of `G` is in
particular one for its depth-`r` topological minors. -/
theorem hasTopologicalDensityAtMost_of_hasDensityAtMost {n : ℕ}
    {G : SimpleGraph (Fin n)} {r d : ℕ} (h : HasDensityAtMost G r d) :
    HasTopologicalDensityAtMost G r d :=
  fun m H hH => h m H (hasShallowMinor_of_hasShallowTopologicalMinor hH)


end Lax12Proofs.MinorBridge
