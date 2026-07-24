import Lax5Proofs.Ramsey
import Lax5Proofs.Subdivision
import Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.NowhereDense.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowTopologicalMinor.Full
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort

/-!
Equivalence of the two nowhere-dense definitions in play: the
shallow-minor grad bound of the ported sparsity development
(`IsNowhereDense`) and Mählmann's local, subdivision-based definition
(`IsLocallyNowhereDense`, Def. 13.1).  The backward direction is the
substantial one; it extracts a subdivided clique of uniform interior
length from a shallow-minor model by routing every path between two
principal branch sets through a private helper branch set (see the
"helper routing" section docstring below).
-/

namespace Lax5Proofs.NowhereDenseBridge

open Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries
open Lax5Proofs.Source.Catalog.SparsityLectures.NowhereDense
open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor
open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowTopologicalMinor
open Lax5Proofs.Subdivision

/-- A graph class `𝓒` is *locally nowhere dense* (Mählmann Def. 13.1,
p. 166) iff for every radius `r : ℕ` there is a bound `N_r : ℕ` such
that no graph in `𝓒` contains the `r`-subdivided clique of order `N_r`
(`subdividedClique N_r r`) as a subgraph.

This is Mählmann's local form of nowhere-denseness, distinct from the
shallow-topological-minor grad bound `IsNowhereDense` of the ported
sparsity development. The two are classically equivalent:
`isLocallyNowhereDense_iff_isNowhereDense` below. -/
def IsLocallyNowhereDense (C : GraphClass) : Prop :=
  ∀ r : ℕ, ∃ N : ℕ, ∀ {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V),
    C G → ¬ (subdividedClique N r).IsContained G


/-- Adjacency between two consecutive subdivision vertices on the same
oriented edge of `subdividedClique N r`. -/
private lemma subdividedClique_adj_subdivision
    {N r : ℕ} (e : {p : Fin N × Fin N // p.1 < p.2})
    (k k' : Fin r) (h : k.val + 1 = k'.val) :
    (subdividedClique N r).Adj
      (Sum.inr ⟨e, k⟩ : SubdividedCliqueVert N r)
      (Sum.inr ⟨e, k'⟩ : SubdividedCliqueVert N r) := by
  refine ⟨fun heq => ?_, Or.inl ⟨rfl, h⟩⟩
  simp only [Sum.inr.injEq, Prod.mk.injEq] at heq
  have : k.val = k'.val := congrArg Fin.val heq.2
  omega

/-- Adjacency between the last subdivision vertex of an oriented edge and
its head principal vertex. -/
private lemma subdividedClique_adj_principal_right
    {N r : ℕ} (e : {p : Fin N × Fin N // p.1 < p.2})
    (k : Fin r) (hk : k.val = r - 1) :
    (subdividedClique N r).Adj
      (Sum.inr ⟨e, k⟩ : SubdividedCliqueVert N r)
      (Sum.inl e.1.2 : SubdividedCliqueVert N r) := by
  refine ⟨?_, Or.inr (Or.inr ⟨rfl, hk⟩)⟩
  intro heq; nomatch heq

/-- Adjacency between the tail principal vertex of an oriented edge and
its first subdivision vertex. -/
private lemma subdividedClique_adj_principal_left
    {N r : ℕ} (e : {p : Fin N × Fin N // p.1 < p.2})
    (k : Fin r) (hk : k.val = 0) :
    (subdividedClique N r).Adj
      (Sum.inl e.1.1 : SubdividedCliqueVert N r)
      (Sum.inr ⟨e, k⟩ : SubdividedCliqueVert N r) := by
  refine ⟨?_, Or.inl (Or.inl ⟨rfl, hk⟩)⟩
  intro heq; nomatch heq

/-- The tail segment of a subdivided-clique edge path, starting at the
subdivision vertex indexed by `k` and ending at the head principal
vertex. -/
private def subdivisionTailWalk :
    {N : ℕ} → {r : ℕ} → (e : {p : Fin N × Fin N // p.1 < p.2}) → (k : Fin r) →
      (subdividedClique N r).Walk (Sum.inr ⟨e, k⟩) (Sum.inl e.1.2)
  | _, 0, _, k => k.elim0
  | N, r' + 1, e, k =>
    Fin.reverseInduction
      (motive := fun (k : Fin (r' + 1)) =>
        (subdividedClique N (r' + 1)).Walk
          (Sum.inr ⟨e, k⟩ : SubdividedCliqueVert N (r' + 1))
          (Sum.inl e.1.2))
      (SimpleGraph.Walk.cons
        (subdividedClique_adj_principal_right e (Fin.last r') rfl)
        SimpleGraph.Walk.nil)
      (fun i w =>
        SimpleGraph.Walk.cons
          (subdividedClique_adj_subdivision e i.castSucc i.succ rfl)
          w)
      k

private lemma subdivisionTailWalk_length
    {N r : ℕ} (e : {p : Fin N × Fin N // p.1 < p.2}) (k : Fin r) :
    (subdivisionTailWalk e k).length = r - k.val := by
  match r, k with
  | r' + 1, k =>
    induction k using Fin.reverseInduction with
    | last =>
      simp [subdivisionTailWalk]
    | cast i ih =>
      simp [subdivisionTailWalk] at ih ⊢
      have hi : i.val < r' := i.isLt
      omega

private lemma mem_subdivisionTailWalk_support
    {N r : ℕ} (e : {p : Fin N × Fin N // p.1 < p.2}) (k : Fin r)
    {x : SubdividedCliqueVert N r}
    (hx : x ∈ (subdivisionTailWalk e k).support) :
    x = .inl e.1.2 ∨ ∃ j : Fin r, k.val ≤ j.val ∧ x = .inr ⟨e, j⟩ := by
  revert x
  match r, k with
  | r' + 1, k =>
    induction k using Fin.reverseInduction with
    | last =>
      intro x hx
      simp [subdivisionTailWalk] at hx
      rcases hx with rfl | rfl
      · exact Or.inr ⟨Fin.last r', le_rfl, rfl⟩
      · exact Or.inl rfl
    | cast i ih =>
      intro x hx
      simp [subdivisionTailWalk] at hx
      rcases hx with rfl | hx
      · exact Or.inr ⟨i.castSucc, le_rfl, rfl⟩
      · rcases ih hx with h | ⟨j, hj, hxj⟩
        · exact Or.inl h
        · refine Or.inr ⟨j, ?_, hxj⟩
          have : i.castSucc.val + 1 = i.succ.val := rfl
          omega

private lemma subdivisionTailWalk_isPath
    {N r : ℕ} (e : {p : Fin N × Fin N // p.1 < p.2}) (k : Fin r) :
    (subdivisionTailWalk e k).IsPath := by
  match r, k with
  | r' + 1, k =>
    induction k using Fin.reverseInduction with
    | last =>
      simp [subdivisionTailWalk]
    | cast i ih =>
      simp [subdivisionTailWalk]
      refine ⟨ih, ?_⟩
      intro hmem
      rcases mem_subdivisionTailWalk_support e i.succ hmem with h | ⟨j, hj, hxj⟩
      · nomatch h
      · simp only [Sum.inr.injEq, Prod.mk.injEq] at hxj
        have hval : i.castSucc.val = j.val := congrArg Fin.val hxj.2
        have hi : i.castSucc.val + 1 = i.succ.val := rfl
        omega

/-- The canonical routed walk along the subdivided edge corresponding to
`e`. -/
private def forwardSubdivisionWalk :
    {N : ℕ} → {r : ℕ} → (e : {p : Fin N × Fin N // p.1 < p.2}) →
    (subdividedClique N r).Walk (Sum.inl e.1.1) (Sum.inl e.1.2)
  | _, 0, e =>
    SimpleGraph.Walk.cons
      (show (subdividedClique _ 0).Adj (Sum.inl e.1.1) (Sum.inl e.1.2) from
        ⟨fun heq => absurd (Sum.inl.inj heq) (Fin.ne_of_lt e.2),
          Or.inl rfl⟩)
      SimpleGraph.Walk.nil
  | _, r' + 1, e =>
    SimpleGraph.Walk.cons
      (subdividedClique_adj_principal_left e (⟨0, Nat.succ_pos _⟩ : Fin (r' + 1)) rfl)
      (subdivisionTailWalk e (⟨0, Nat.succ_pos _⟩ : Fin (r' + 1)))

private lemma forwardSubdivisionWalk_length
    {N r : ℕ} (e : {p : Fin N × Fin N // p.1 < p.2}) :
    (@forwardSubdivisionWalk N r e).length = r + 1 := by
  match r with
  | 0 => simp [forwardSubdivisionWalk]
  | r' + 1 =>
    simp [forwardSubdivisionWalk, subdivisionTailWalk_length]

private lemma forwardSubdivisionWalk_isPath
    {N r : ℕ} (e : {p : Fin N × Fin N // p.1 < p.2}) :
    (@forwardSubdivisionWalk N r e).IsPath := by
  match r with
  | 0 =>
    simp [forwardSubdivisionWalk]
    exact Fin.ne_of_lt e.2
  | r' + 1 =>
    simp [forwardSubdivisionWalk]
    refine ⟨subdivisionTailWalk_isPath e _, ?_⟩
    intro hmem
    rcases mem_subdivisionTailWalk_support e _ hmem with h | ⟨j, _, hxj⟩
    · exact absurd (Sum.inl.inj h) (Fin.ne_of_lt e.2)
    · nomatch hxj

private noncomputable def completeEdgeOrient
    {N : ℕ} (e : (SimpleGraph.completeGraph (Fin N)).edgeSet) :
    {p : Fin N × Fin N // p.1 < p.2} := by
  have hne : e.1.out.1 ≠ e.1.out.2 := by
    have heMem : s(e.1.out.1, e.1.out.2) ∈ (SimpleGraph.completeGraph (Fin N)).edgeSet := by
      rw [Sym2.mk, e.1.out_eq]
      exact e.2
    have heAdj : (SimpleGraph.completeGraph (Fin N)).Adj e.1.out.1 e.1.out.2 := by
      rwa [SimpleGraph.mem_edgeSet] at heMem
    exact (SimpleGraph.top_adj _ _).mp heAdj
  by_cases h : e.1.out.1 < e.1.out.2
  · exact ⟨(e.1.out.1, e.1.out.2), h⟩
  · exact ⟨(e.1.out.2, e.1.out.1), lt_of_le_of_ne (le_of_not_gt h) hne.symm⟩

private lemma completeEdgeOrient_spec
    {N : ℕ} (e : (SimpleGraph.completeGraph (Fin N)).edgeSet) :
    s((completeEdgeOrient e).1.1, (completeEdgeOrient e).1.2) = (e : Sym2 (Fin N)) := by
  by_cases h : e.1.out.1 < e.1.out.2
  · simp [completeEdgeOrient, h, Sym2.mk, e.1.out_eq]
  · simp [completeEdgeOrient, h, Sym2.eq_swap, Sym2.mk, e.1.out_eq]

private noncomputable def completeEdgeTail
    {N : ℕ} (e : (SimpleGraph.completeGraph (Fin N)).edgeSet) : Fin N :=
  (completeEdgeOrient e).1.1

private lemma completeEdgeTail_mem
    {N : ℕ} (e : (SimpleGraph.completeGraph (Fin N)).edgeSet) :
    completeEdgeTail e ∈ (e : Sym2 (Fin N)) := by
  refine ⟨(completeEdgeOrient e).1.2, ?_⟩
  simpa [completeEdgeTail] using (completeEdgeOrient_spec e).symm

private noncomputable def completeEdgeHead
    {N : ℕ} (e : (SimpleGraph.completeGraph (Fin N)).edgeSet) : Fin N :=
  Sym2.Mem.other (completeEdgeTail_mem e)

private lemma completeEdgeHead_eq
    {N : ℕ} (e : (SimpleGraph.completeGraph (Fin N)).edgeSet) :
    completeEdgeHead e = (completeEdgeOrient e).1.2 := by
  have hmem : completeEdgeHead e ∈ (e : Sym2 (Fin N)) := by
    exact Sym2.other_mem (completeEdgeTail_mem e)
  have hmem' : completeEdgeHead e ∈
      s((completeEdgeOrient e).1.1, (completeEdgeOrient e).1.2) := by
    simpa [completeEdgeOrient_spec e] using hmem
  have hne : completeEdgeHead e ≠ completeEdgeTail e := by
    simpa [completeEdgeHead] using
      (SimpleGraph.completeGraph (Fin N)).edge_other_ne e.2 (completeEdgeTail_mem e)
  have hcases : completeEdgeHead e = completeEdgeTail e ∨
      completeEdgeHead e = (completeEdgeOrient e).1.2 := by
    simpa [completeEdgeTail] using (Sym2.mem_iff.mp hmem')
  exact hcases.resolve_left hne

private noncomputable def completeEdgeWalk
    {N r : ℕ} (e : (SimpleGraph.completeGraph (Fin N)).edgeSet) :
    (subdividedClique N r).Walk
      (Sum.inl (completeEdgeTail e))
      (Sum.inl (Sym2.Mem.other (completeEdgeTail_mem e))) := by
  exact (forwardSubdivisionWalk (completeEdgeOrient e)).copy rfl
    (congrArg Sum.inl (completeEdgeHead_eq e).symm)

/-- Every vertex on the canonical subdivided-edge walk lies either at one
endpoint or on the subdivision chain of that same edge. -/
private lemma mem_forwardSubdivisionWalk_support
    {N r : ℕ} (e : {p : Fin N × Fin N // p.1 < p.2})
    {x : SubdividedCliqueVert N r}
    (hx : x ∈ (forwardSubdivisionWalk e).support) :
    x = .inl e.1.1 ∨ x = .inl e.1.2 ∨ ∃ k : Fin r, x = .inr ⟨e, k⟩ := by
  match r with
  | 0 =>
    simp [forwardSubdivisionWalk] at hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  | r' + 1 =>
    simp [forwardSubdivisionWalk] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · rcases mem_subdivisionTailWalk_support e _ hx with h | ⟨j, _, hj⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨j, hj⟩)

/-- Forward-direction helper: a subgraph copy of an `r`-subdivided clique
of order `N` induces a depth-`⌈r/2⌉` shallow topological minor model of
`K_N`. The eventual Close session should build the explicit routed paths
along the subdivision edges. -/
private theorem subdividedClique_isShallowTopologicalMinor
    {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    (N r : ℕ) (hContain : (subdividedClique N r).IsContained G) :
    IsShallowTopologicalMinor (SimpleGraph.completeGraph (Fin N)) G ((r + 1) / 2) := by
  rcases hContain with ⟨copy⟩
  let model :
      ShallowTopologicalMinorModel
        (SimpleGraph.completeGraph (Fin N))
        G
        ((r + 1) / 2) :=
    { branchVertex :=
        ⟨fun i => copy (Sum.inl i), fun _ _ h => Sum.inl.inj (copy.injective h)⟩
      edgeTail := completeEdgeTail
      edgeTail_mem := completeEdgeTail_mem
      edgePath := fun e => (completeEdgeWalk e).map copy.toHom
      edgePath_isPath := by
        intro e
        exact SimpleGraph.Walk.map_isPath_of_injective copy.injective
          (by simpa [completeEdgeWalk] using
            (forwardSubdivisionWalk_isPath (completeEdgeOrient e)))
      edgePath_length := by
        intro e
        calc
          ((completeEdgeWalk e).map copy.toHom).length = r + 1 := by
            simp [completeEdgeWalk, forwardSubdivisionWalk_length]
          _ ≤ 2 * ((r + 1) / 2) + 1 := by omega
      edgePath_interior_avoids_branch := by
        intro e x hx htail hhead w
        rw [SimpleGraph.Walk.support_map] at hx
        rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
        have hy' : y ∈ (forwardSubdivisionWalk (completeEdgeOrient e)).support := by
          simpa [completeEdgeWalk] using hy
        rcases mem_forwardSubdivisionWalk_support (e := completeEdgeOrient e) hy' with
          htail' | hhead' | ⟨k, hk⟩
        · exact (htail (by simpa [completeEdgeWalk] using congrArg copy htail')).elim
        · have hheadEq :
              copy (Sum.inl (completeEdgeOrient e).1.2) =
                copy (Sum.inl (Sym2.Mem.other (completeEdgeTail_mem e))) := by
              rw [← completeEdgeHead_eq e]
              rfl
          exact (hhead ((congrArg copy hhead').trans hheadEq)).elim
        · intro hw
          have : (Sum.inr ⟨completeEdgeOrient e, k⟩ : SubdividedCliqueVert N r) = Sum.inl w := by
            exact hk.symm.trans (copy.injective hw)
          nomatch this
      edgePath_interior_disjoint := by
        intro e e' x hne hx hx' htail hhead htail' hhead'
        rw [SimpleGraph.Walk.support_map] at hx hx'
        rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
        rcases List.mem_map.mp hx' with ⟨y', hy', hyy'⟩
        have hy0 : y ∈ (forwardSubdivisionWalk (completeEdgeOrient e)).support := by
          simpa [completeEdgeWalk] using hy
        have hy0' : y' ∈ (forwardSubdivisionWalk (completeEdgeOrient e')).support := by
          simpa [completeEdgeWalk] using hy'
        rcases mem_forwardSubdivisionWalk_support (e := completeEdgeOrient e) hy0 with
          hxTail | hxHead | ⟨k, hk⟩
        · exact (htail (by simpa [completeEdgeWalk] using congrArg copy hxTail)).elim
        · have hheadEq :
              copy (Sum.inl (completeEdgeOrient e).1.2) =
                copy (Sum.inl (Sym2.Mem.other (completeEdgeTail_mem e))) := by
              rw [← completeEdgeHead_eq e]
              rfl
          exact (hhead ((congrArg copy hxHead).trans hheadEq)).elim
        · rcases mem_forwardSubdivisionWalk_support (e := completeEdgeOrient e') hy0' with
            hxTail' | hxHead' | ⟨k', hk'⟩
          · exact (htail' (hyy'.symm.trans (by simpa [completeEdgeWalk] using congrArg copy hxTail'))).elim
          · have hheadEq' :
                copy (Sum.inl (completeEdgeOrient e').1.2) =
                  copy (Sum.inl (Sym2.Mem.other (completeEdgeTail_mem e'))) := by
                rw [← completeEdgeHead_eq e']
                rfl
            exact (hhead' (hyy'.symm.trans ((congrArg copy hxHead').trans hheadEq'))).elim
          · have horient :
                completeEdgeOrient e = completeEdgeOrient e' := by
              have hyy : y = y' := copy.injective hyy'.symm
              have hpair :
                  (⟨completeEdgeOrient e, k⟩ : {p : Fin N × Fin N // p.1 < p.2} × Fin r) =
                    ⟨completeEdgeOrient e', k'⟩ := by
                exact Sum.inr.inj (hk.symm.trans (hyy.trans hk'))
              exact congrArg Prod.fst hpair
            apply hne
            apply Subtype.ext
            have hsym :
                s((completeEdgeOrient e).1.1, (completeEdgeOrient e).1.2) =
                  s((completeEdgeOrient e').1.1, (completeEdgeOrient e').1.2) := by
              simpa using
                congrArg (fun z : {p : Fin N × Fin N // p.1 < p.2} => s(z.1.1, z.1.2)) horient
            calc
              (e : Sym2 (Fin N)) = s((completeEdgeOrient e).1.1, (completeEdgeOrient e).1.2) :=
                (completeEdgeOrient_spec e).symm
              _ = s((completeEdgeOrient e').1.1, (completeEdgeOrient e').1.2) := hsym
              _ = (e' : Sym2 (Fin N)) := completeEdgeOrient_spec e' }
  exact ⟨model⟩

/-- Shallow-minor nowhere denseness implies the local subdivided-clique
formulation. This is the linear parameter translation
`N_r := ω_{⌈r/2⌉}(C) + 1`. -/
private theorem isLocallyNowhereDense_of_isNowhereDense
    (C : GraphClass)
    (hNd : IsNowhereDense C) :
    IsLocallyNowhereDense C := by
  intro r
  rcases hNd ((r + 1) / 2) with ⟨t, ht⟩
  refine ⟨t + 1, ?_⟩
  intro V _ _ G hCG hContain
  have hTop :
      IsShallowTopologicalMinor (SimpleGraph.completeGraph (Fin (t + 1))) G ((r + 1) / 2) :=
    subdividedClique_isShallowTopologicalMinor G (t + 1) r hContain
  exact ht G hCG (shallowTopologicalMinor_toShallowMinor hTop)

/-! ### Backward direction: helper routing

`isNowhereDense_of_isLocallyNowhereDense` must turn a depth-`d` shallow-minor
model of a huge clique into a subgraph-subdivided clique of bounded interior
length.  Trimming the pairwise centre-to-centre walks of the model cannot
work: Ramsey-homogeneous *funneling* branch sets admit no common trimmed
centre, so no trimming of the pairwise walks yields an internally disjoint
system.  Instead the branch sets are split into few *principals* and many
*helpers*, and each subdivision path between two principals is routed through
a private helper branch set:

1. *Focus step* (`focus_step`): for one principal and a helper pool, the
   walks from the principal's centre to the bridge endpoints towards the
   helpers (*legs*: paths of length ≤ `d` inside the branch set) are
   normalised.  A pigeonhole makes the leg lengths uniform; one multicolour
   Ramsey run over the pairwise collision patterns of the legs makes the
   pattern uniform; and a three-walk transitivity argument plus path
   injectivity forces that pattern onto the diagonal.  Trimming at the last
   shared level yields one trimmed centre and pairwise-disjoint tails of
   uniform length to all surviving helpers.
2. *Nested refinement* (`multi_focus`): the focus step is applied principal
   by principal, each time shrinking the common helper pool (tower-type
   bound `multiThreshold`, harmless for a qualitative statement).
3. *Uniformisation and assembly* (`exists_uniform_subdivision`): principals
   are pigeonholed to a common tail length, each principal pair receives a
   private helper injectively, the helper-side middle segments are made
   uniform by one final Ramsey run over principal pairs, and the routed path
   system assembles into a subgraph copy of `subdividedClique n r` with a
   uniform interior length `r ≤ 4d + 1` (`RoutedSystem.isContained`).
4. `isNowhereDense_of_isLocallyNowhereDense` does the bookkeeping: the local
   bound is instantiated at every radius up to `4d + 1` and the clique order
   is chosen large enough for the Ramsey/pigeonhole chain.
-/

/-- The Ramsey number sufficient to extract, from any symmetric colouring of
pairs by colours in a fintype `C`, a monochromatic subset of size `Q`. -/
private noncomputable def ramseyFor (C : Type) [Fintype C] [Nonempty C] (Q : ℕ) : ℕ :=
  (Ramsey.multicolor_ramsey (List.replicate (Fintype.card C) Q)
    (by rw [ne_eq, List.replicate_eq_nil_iff]; exact Fintype.card_ne_zero)).choose

private lemma le_ramseyFor (C : Type) [Fintype C] [Nonempty C] (Q : ℕ) :
    Q ≤ ramseyFor C Q := by
  classical
  have hne : List.replicate (Fintype.card C) Q ≠ [] := by
    rw [ne_eq, List.replicate_eq_nil_iff]; exact Fintype.card_ne_zero
  have hle : (Ramsey.multicolor_ramsey (List.replicate (Fintype.card C) Q)
      hne).choose ≤ Fintype.card (Fin (ramseyFor C Q)) := by
    rw [Fintype.card_fin]; exact le_rfl
  obtain ⟨i, S, hS, -⟩ :=
    (Ramsey.multicolor_ramsey (List.replicate (Fintype.card C) Q) hne).choose_spec
      (V := Fin (ramseyFor C Q)) hle
      (fun _ => ⟨0, by rw [List.length_replicate]; exact Fintype.card_pos⟩)
  calc Q = (List.replicate (Fintype.card C) Q).get i := by simp
    _ ≤ S.card := hS
    _ ≤ Fintype.card (Fin (ramseyFor C Q)) := S.card_le_univ
    _ = ramseyFor C Q := Fintype.card_fin _

/-- Monochromatic-subset extraction for a symmetric colouring by an arbitrary
fintype of colours: the packaged form of `multicolor_ramsey` with a
replicated sizes list.  Both Ramsey runs of the backward direction (the
focus-step collision patterns and the final middle-segment lengths) go
through this lemma. -/
private lemma exists_monochromatic_subset {ι : Type} [DecidableEq ι] [Fintype ι]
    {C : Type} [DecidableEq C] [Fintype C] [Nonempty C]
    (colour : ι → ι → C) (hsymm : ∀ a b, colour a b = colour b a) (Q : ℕ)
    (hcard : ramseyFor C Q ≤ Fintype.card ι) :
    ∃ (c₀ : C) (T : Finset ι), Q ≤ T.card ∧
      ∀ a ∈ T, ∀ b ∈ T, a ≠ b → colour a b = c₀ := by
  classical
  let equivC : C ≃ Fin (Fintype.card C) := (Fintype.truncEquivFin C).out
  have hlen : (List.replicate (Fintype.card C) Q).length = Fintype.card C :=
    List.length_replicate
  obtain ⟨i, T, hTcard, hTpair⟩ :=
    (Ramsey.multicolor_ramsey (List.replicate (Fintype.card C) Q)
      (by rw [ne_eq, List.replicate_eq_nil_iff]; exact Fintype.card_ne_zero)).choose_spec
      hcard
      (Sym2.lift ⟨fun a b => Fin.cast hlen.symm (equivC (colour a b)),
        fun a b => by simp only [hsymm]⟩)
  refine ⟨equivC.symm (Fin.cast hlen i), T, ?_, ?_⟩
  · calc Q = (List.replicate (Fintype.card C) Q).get i := by simp
      _ ≤ T.card := hTcard
  · intro a ha b hb hab
    have hpair := hTpair (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
    have hval : Fin.cast hlen.symm (equivC (colour a b)) = i := by
      simpa [Sym2.lift_mk] using hpair
    have h2 : equivC (colour a b) = Fin.cast hlen i :=
      Fin.ext (by simpa using congrArg Fin.val hval)
    calc colour a b = equivC.symm (equivC (colour a b)) :=
          (equivC.symm_apply_apply _).symm
      _ = equivC.symm (Fin.cast hlen i) := by rw [h2]

/-- Colour palette for the focus-step Ramsey: the collision pattern between
two legs records, for every pair of positions, whether the legs agree
there. -/
private abbrev PatternT (d : ℕ) : Type := Fin (d + 1) → Fin (d + 1) → Bool

/-- Helper-pool size consumed by one focus step producing a refined pool of
size `Q`: `d + 1` leg-length classes times the pattern-Ramsey number. -/
private noncomputable def focusThreshold (d Q : ℕ) : ℕ :=
  (d + 1) * ramseyFor (PatternT d) Q

/-- Helper-pool size consumed by the nested refinement over `k` principals
producing a final pool of size `Q`. -/
private noncomputable def multiThreshold (d Q : ℕ) : ℕ → ℕ
  | 0 => Q
  | k + 1 => focusThreshold d (multiThreshold d Q k)

private lemma le_focusThreshold (d Q : ℕ) : Q ≤ focusThreshold d Q :=
  le_trans (le_ramseyFor _ Q) (Nat.le_mul_of_pos_left _ (Nat.succ_pos d))

private lemma le_multiThreshold (d Q : ℕ) : ∀ k, Q ≤ multiThreshold d Q k
  | 0 => le_rfl
  | k + 1 => le_trans (le_multiThreshold d Q k) (le_focusThreshold d _)

/-- The focus step at one principal.  The *legs* are paths of length at most
`d` from a common start `c` (the principal's centre) to prescribed endpoints
`x h` (the bridge endpoints towards the helpers `h ∈ H`), staying inside a
set `B` (the principal's branch set).  Pigeonholing the leg lengths and
running one pattern Ramsey yields a sub-pool of size `Q` on which the legs
consist of a common initial segment up to a level `r*` followed by
pairwise-disjoint tails of uniform length: the common level-`r*` vertex is
the trimmed centre `v` and the tails are the returned walks.

The diagonal argument inside: if the monochromatic collision pattern relates
two positions `s ≠ s'`, then comparing three legs forces one leg to visit
the same vertex at both positions, contradicting path injectivity.  Hence
collisions happen only level-by-level, and above the last shared level the
legs are pairwise disjoint. -/
private lemma focus_step {V : Type} [DecidableEq V] {G : SimpleGraph V} {t d : ℕ}
    {B : Set V} {c : V} {x : Fin (t + 1) → V} {H : Finset (Fin (t + 1))} {Q : ℕ}
    (hQ : 3 ≤ Q)
    (leg : ∀ h ∈ H, G.Walk c (x h))
    (hpath : ∀ h hh, (leg h hh).IsPath)
    (hlen : ∀ h hh, (leg h hh).length ≤ d)
    (hsupp : ∀ h hh, ∀ w ∈ (leg h hh).support, w ∈ B)
    (hH : focusThreshold d Q ≤ H.card) :
    ∃ pool : Finset (Fin (t + 1)), pool ⊆ H ∧ Q ≤ pool.card ∧
      ∃ (τ : ℕ) (v : V) (tail : ∀ h ∈ pool, G.Walk v (x h)),
        τ ≤ d ∧ v ∈ B ∧
        (∀ h hh, (tail h hh).IsPath) ∧
        (∀ h hh, (tail h hh).length = τ) ∧
        (∀ h hh, ∀ w ∈ (tail h hh).support, w ∈ B) ∧
        (∀ h hh h' hh', h ≠ h' → ∀ w, w ∈ (tail h hh).support →
          w ∈ (tail h' hh').support → w = v) := by
  classical
  -- Pigeonhole the leg lengths into `d + 1` classes.
  set lenF : Fin (t + 1) → Fin (d + 1) := fun h =>
    if hh : h ∈ H then (⟨min (leg h hh).length d, by omega⟩ : Fin (d + 1)) else 0
    with hlenF
  obtain ⟨lam0, -, hfiber⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (f := lenF) (n := ramseyFor (PatternT d) Q)
      (fun a _ => Finset.mem_univ _) Finset.univ_nonempty
      (by
        rw [Finset.card_univ, Fintype.card_fin]
        exact le_trans (Nat.le_of_eq rfl) hH)
  set H₁ : Finset (Fin (t + 1)) := {h ∈ H | lenF h = lam0} with hH₁def
  have hH₁H : H₁ ⊆ H := Finset.filter_subset _ _
  set lam := (lam0 : Fin (d + 1)).1 with hlamdef
  have hlam_le : lam ≤ d := Nat.lt_succ_iff.mp lam0.isLt
  have hlamlen : ∀ h (hhH : h ∈ H) (_ : h ∈ H₁), (leg h hhH).length = lam := by
    intro h hhH hh
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hh
    simp only [hlenF] at h2
    rw [dif_pos h1] at h2
    have := congrArg Fin.val h2
    simpa [Nat.min_eq_left (hlen h h1)] using this
  -- The pattern Ramsey on the uniform-length class.
  obtain ⟨P₀, T, hTcard, hTpat⟩ :=
    exists_monochromatic_subset (ι := ↥H₁) (C := PatternT d)
      (colour := fun a b =>
        if a ≤ b then
          (fun s s' : Fin (d + 1) =>
            decide ((leg a.1 (hH₁H a.2)).getVert s.1 =
              (leg b.1 (hH₁H b.2)).getVert s'.1))
        else
          (fun s s' : Fin (d + 1) =>
            decide ((leg b.1 (hH₁H b.2)).getVert s.1 =
              (leg a.1 (hH₁H a.2)).getVert s'.1)))
      (fun a b => by
        beta_reduce
        rcases le_or_gt a b with hab | hba
        · rcases eq_or_lt_of_le hab with rfl | hlt
          · rfl
          · rw [if_pos hab, if_neg (not_le.mpr hlt)]
        · rw [if_neg (not_le.mpr hba), if_pos (le_of_lt hba)])
      Q
      (by rw [Fintype.card_coe]; exact hfiber)
  have key : ∀ a b : ↥H₁, a ∈ T → b ∈ T → a < b → ∀ s s' : Fin (d + 1),
      ((leg a.1 (hH₁H a.2)).getVert s.1 = (leg b.1 (hH₁H b.2)).getVert s'.1) ↔
        P₀ s s' = true := by
    intro a b ha hb hab s s'
    have h1 := hTpat a ha b hb (ne_of_lt hab)
    rw [if_pos (le_of_lt hab)] at h1
    have h2 := congrFun (congrFun h1 s) s'
    constructor
    · intro h3; rw [← h2]; exact decide_eq_true h3
    · intro h3; rw [← h2] at h3; exact of_decide_eq_true h3
  -- Push everything down to the image pool in `Fin (t + 1)`.
  set pool := T.image Subtype.val with hpooldef
  have hpoolH₁ : pool ⊆ H₁ := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨a, -, rfl⟩
    exact a.2
  have hpoolsub : pool ⊆ H := hpoolH₁.trans hH₁H
  have hpoolQ : Q ≤ pool.card := by
    rw [hpooldef, Finset.card_image_of_injective _ Subtype.val_injective]
    exact hTcard
  have patP : ∀ g g' (hg : g ∈ pool) (hg' : g' ∈ pool), g < g' →
      ∀ s s' : ℕ, ∀ (hs : s ≤ lam) (hs' : s' ≤ lam),
      (((leg g (hpoolsub hg)).getVert s = (leg g' (hpoolsub hg')).getVert s') ↔
        P₀ ⟨s, by omega⟩ ⟨s', by omega⟩ = true) := by
    intro g g' hg hg' hlt s s' hs hs'
    rw [hpooldef] at hg hg'
    rcases Finset.mem_image.mp hg with ⟨a, haT, ha⟩
    rcases Finset.mem_image.mp hg' with ⟨b, hbT, hb⟩
    subst ha; subst hb
    exact key a b haT hbT (Subtype.coe_lt_coe.mp hlt) ⟨s, by omega⟩ ⟨s', by omega⟩
  -- Three sorted pool elements for the diagonal argument.
  have hpool3 : 3 ≤ pool.card := hQ.trans hpoolQ
  have hne1 : pool.Nonempty := Finset.card_pos.mp (by omega)
  set g₁ := pool.min' hne1 with hg₁def
  have hg₁ : g₁ ∈ pool := Finset.min'_mem _ _
  have hne2 : (pool.erase g₁).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hg₁]; omega)
  set g₂ := (pool.erase g₁).min' hne2 with hg₂def
  have hg₂e : g₂ ∈ pool.erase g₁ := Finset.min'_mem _ _
  have hg₂ : g₂ ∈ pool := Finset.mem_of_mem_erase hg₂e
  have h12 : g₁ < g₂ :=
    lt_of_le_of_ne (Finset.min'_le _ _ hg₂) (Finset.ne_of_mem_erase hg₂e).symm
  have hne3 : ((pool.erase g₁).erase g₂).Nonempty :=
    Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem hg₂e, Finset.card_erase_of_mem hg₁]; omega)
  set g₃ := ((pool.erase g₁).erase g₂).min' hne3 with hg₃def
  have hg₃e : g₃ ∈ (pool.erase g₁).erase g₂ := Finset.min'_mem _ _
  have hg₃ : g₃ ∈ pool :=
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hg₃e)
  have h23 : g₂ < g₃ :=
    lt_of_le_of_ne (Finset.min'_le _ _ (Finset.mem_of_mem_erase hg₃e))
      (Finset.ne_of_mem_erase hg₃e).symm
  have h13 : g₁ < g₃ := h12.trans h23
  -- The homogeneous pattern is diagonal.
  have diag : ∀ s s' : ℕ, ∀ (hs : s ≤ lam) (hs' : s' ≤ lam),
      P₀ ⟨s, by omega⟩ ⟨s', by omega⟩ = true → s = s' := by
    intro s s' hs hs' hP
    have e12 := (patP g₁ g₂ hg₁ hg₂ h12 s s' hs hs').mpr hP
    have e13 := (patP g₁ g₃ hg₁ hg₃ h13 s s' hs hs').mpr hP
    have e23 : (leg g₂ (hpoolsub hg₂)).getVert s' =
        (leg g₃ (hpoolsub hg₃)).getVert s' := e12.symm.trans e13
    have hP' := (patP g₂ g₃ hg₂ hg₃ h23 s' s' hs' hs').mp e23
    have e12' := (patP g₁ g₂ hg₁ hg₂ h12 s' s' hs' hs').mpr hP'
    have heq : (leg g₁ (hpoolsub hg₁)).getVert s =
        (leg g₁ (hpoolsub hg₁)).getVert s' := e12.trans e12'.symm
    have hlg₁ : (leg g₁ (hpoolsub hg₁)).length = lam := hlamlen g₁ (hpoolsub hg₁) (hpoolH₁ hg₁)
    exact (hpath g₁ (hpoolsub hg₁)).getVert_injOn
      (by rw [Set.mem_setOf_eq, hlg₁]; omega)
      (by rw [Set.mem_setOf_eq, hlg₁]; omega) heq
  -- Level `0` is always shared; find the last shared level `r*`.
  have hP00 : P₀ ⟨0, Nat.succ_pos d⟩ ⟨0, Nat.succ_pos d⟩ = true := by
    refine (patP g₁ g₂ hg₁ hg₂ h12 0 0 (Nat.zero_le _) (Nat.zero_le _)).mp ?_
    simp
  set rStar :=
    Nat.findGreatest (fun s => ∃ hs : s < d + 1, P₀ ⟨s, hs⟩ ⟨s, hs⟩ = true) lam
    with hrStardef
  have hrStar_le : rStar ≤ lam := hrStardef ▸ Nat.findGreatest_le lam
  have hshared : P₀ ⟨rStar, by omega⟩ ⟨rStar, by omega⟩ = true := by
    have h :=
      Nat.findGreatest_spec
        (P := fun s => ∃ hs : s < d + 1, P₀ ⟨s, hs⟩ ⟨s, hs⟩ = true)
        (Nat.zero_le lam) ⟨Nat.succ_pos d, hP00⟩
    rw [← hrStardef] at h
    exact h.choose_spec
  have hmax : ∀ s (_ : rStar < s) (_ : s ≤ lam) (hs : s < d + 1),
      ¬ (P₀ ⟨s, hs⟩ ⟨s, hs⟩ = true) := by
    intro s h1 h2 hs hcon
    have h3 :=
      Nat.findGreatest_is_greatest
        (P := fun s => ∃ hs : s < d + 1, P₀ ⟨s, hs⟩ ⟨s, hs⟩ = true)
        (hrStardef ▸ h1) h2
    exact h3 ⟨hs, hcon⟩
  -- The trimmed centre.
  set v := (leg g₁ (hpoolsub hg₁)).getVert rStar with hvdef
  have hvB : v ∈ B := by
    refine hsupp g₁ (hpoolsub hg₁) v (SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
      ⟨rStar, hvdef.symm, ?_⟩)
    rw [hlamlen g₁ (hpoolsub hg₁) (hpoolH₁ hg₁)]; omega
  have hsharedAll : ∀ g (hg : g ∈ pool), (leg g (hpoolsub hg)).getVert rStar = v := by
    intro g hg
    rcases lt_trichotomy g g₁ with h | h | h
    · exact ((patP g g₁ hg hg₁ h rStar rStar hrStar_le hrStar_le).mpr hshared).trans
        hvdef.symm
    · subst h; exact hvdef.symm
    · exact (((patP g₁ g hg₁ hg h rStar rStar hrStar_le hrStar_le).mpr
        hshared).symm).trans hvdef.symm
  -- Package the tails.
  refine ⟨pool, hpoolsub, hpoolQ, lam - rStar, v,
    fun h hh => ((leg h (hpoolsub hh)).drop rStar).copy (hsharedAll h hh) rfl,
    by omega, hvB, ?_, ?_, ?_, ?_⟩
  · intro h hh
    simpa using (hpath h (hpoolsub hh)).drop rStar
  · intro h hh
    simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.drop_length, hlamlen h (hpoolsub hh) (hpoolH₁ hh)]
  · intro h hh w hw
    rw [SimpleGraph.Walk.support_copy] at hw
    obtain ⟨i, hieq, hile⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
    rw [SimpleGraph.Walk.drop_getVert] at hieq
    rw [SimpleGraph.Walk.drop_length, hlamlen h (hpoolsub hh) (hpoolH₁ hh)] at hile
    refine hsupp h (hpoolsub hh) w (SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
      ⟨rStar + i, hieq, ?_⟩)
    rw [hlamlen h (hpoolsub hh) (hpoolH₁ hh)]; omega
  · intro h hh h' hh' hne w hw hw'
    rw [SimpleGraph.Walk.support_copy] at hw hw'
    obtain ⟨i, hieq, hile⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
    obtain ⟨i', hieq', hile'⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw'
    rw [SimpleGraph.Walk.drop_getVert] at hieq hieq'
    rw [SimpleGraph.Walk.drop_length, hlamlen h (hpoolsub hh) (hpoolH₁ hh)] at hile
    rw [SimpleGraph.Walk.drop_length, hlamlen h' (hpoolsub hh') (hpoolH₁ hh')] at hile'
    have hb : rStar + i ≤ lam := by omega
    have hb' : rStar + i' ≤ lam := by omega
    have heq : (leg h (hpoolsub hh)).getVert (rStar + i) =
        (leg h' (hpoolsub hh')).getVert (rStar + i') := hieq.trans hieq'.symm
    have hii : i = i' := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := diag _ _ hb hb' ((patP h h' hh hh' hlt _ _ hb hb').mp heq)
        omega
      · have := diag _ _ hb' hb ((patP h' h hh' hh hgt _ _ hb' hb).mp heq.symm)
        omega
    subst hii
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [Nat.add_zero] at hieq
      exact hieq.symm.trans (hsharedAll h hh)
    · exfalso
      have hPt : P₀ ⟨rStar + i, by omega⟩ ⟨rStar + i, by omega⟩ = true := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact (patP h h' hh hh' hlt _ _ hb hb).mp heq
        · exact (patP h' h hh' hh hgt _ _ hb hb).mp heq.symm
      exact hmax (rStar + i) (by omega) hb (by omega) hPt

/-- Nested refinement: the focus step applied principal by principal.  From
legs for every principal `p ∈ P` towards every helper `h ∈ H`, extract one
common surviving helper pool of size `Q` together with, for every principal,
a trimmed centre `hub p` inside the branch set, a uniform tail length `τ p`,
and pairwise-disjoint tails towards all surviving helpers. -/
private lemma multi_focus {V : Type} [DecidableEq V] {G : SimpleGraph V} {t d : ℕ}
    {B : Fin (t + 1) → Set V} {c : Fin (t + 1) → V}
    (x : Fin (t + 1) → Fin (t + 1) → V)
    (P H : Finset (Fin (t + 1))) (Q : ℕ) (hQ : 3 ≤ Q)
    (leg : ∀ p ∈ P, ∀ h ∈ H, G.Walk (c p) (x p h))
    (hpath : ∀ p hp h hh, (leg p hp h hh).IsPath)
    (hlen : ∀ p hp h hh, (leg p hp h hh).length ≤ d)
    (hsupp : ∀ p hp h hh, ∀ w ∈ (leg p hp h hh).support, w ∈ B p)
    (hH : multiThreshold d Q P.card ≤ H.card) :
    ∃ pool : Finset (Fin (t + 1)), pool ⊆ H ∧ Q ≤ pool.card ∧
      ∃ (τ : Fin (t + 1) → ℕ) (hub : Fin (t + 1) → V)
        (tail : ∀ p ∈ P, ∀ h ∈ pool, G.Walk (hub p) (x p h)),
        (∀ p, p ∈ P → τ p ≤ d ∧ hub p ∈ B p) ∧
        (∀ p hp h hh, (tail p hp h hh).IsPath ∧ (tail p hp h hh).length = τ p ∧
          ∀ w ∈ (tail p hp h hh).support, w ∈ B p) ∧
        (∀ p hp h hh h' hh', h ≠ h' → ∀ w, w ∈ (tail p hp h hh).support →
          w ∈ (tail p hp h' hh').support → w = hub p) := by
  classical
  induction P using Finset.cons_induction generalizing H with
  | empty =>
      exact ⟨H, subset_rfl, by simpa [multiThreshold] using hH,
        fun _ => 0, c, fun p hp => absurd hp (Finset.notMem_empty p),
        fun p hp => absurd hp (Finset.notMem_empty p),
        fun p hp => absurd hp (Finset.notMem_empty p),
        fun p hp => absurd hp (Finset.notMem_empty p)⟩
  | cons p P₀ hpP₀ ih =>
      rw [Finset.card_cons] at hH
      have hH' : focusThreshold d (multiThreshold d Q P₀.card) ≤ H.card := hH
      -- Focus step at the new principal `p`.
      obtain ⟨pool₁, hp1H, hp1card, τp, vp, tailp, hτp, hvp, htpPath, htpLen,
          htpSupp, htpInter⟩ :=
        focus_step (le_trans hQ (le_multiThreshold d Q P₀.card))
          (fun h hh => leg p (Finset.mem_cons_self _ _) h hh)
          (fun h hh => hpath p _ h hh)
          (fun h hh => hlen p _ h hh)
          (fun h hh => hsupp p _ h hh)
          hH'
      -- Recurse on the remaining principals with the refined pool.
      obtain ⟨pool, hpsub, hpcard, τ₀, hub₀, tail₀, hspec1, hspec2, hspec3⟩ :=
        ih pool₁
          (fun q hq h hh => leg q (Finset.mem_cons_of_mem hq) h (hp1H hh))
          (fun q hq h hh => hpath q _ h _)
          (fun q hq h hh => hlen q _ h _)
          (fun q hq h hh => hsupp q _ h _)
          hp1card
      -- Combine the data.
      set τ' : Fin (t + 1) → ℕ := fun q => if q = p then τp else τ₀ q with hτ'def
      set hub' : Fin (t + 1) → V := fun q => if q = p then vp else hub₀ q with hhub'def
      have τ'p : τ' p = τp := if_pos rfl
      have τ'q : ∀ q, q ≠ p → τ' q = τ₀ q := fun q hq => if_neg hq
      have hub'p : hub' p = vp := if_pos rfl
      have hub'q : ∀ q, q ≠ p → hub' q = hub₀ q := fun q hq => if_neg hq
      set tail' : ∀ q ∈ Finset.cons p P₀ hpP₀, ∀ h ∈ pool, G.Walk (hub' q) (x q h) :=
        fun q hq h hh =>
          if hqp : q = p then
            (tailp h (hpsub hh)).copy (by rw [hqp, hub'p]) (by rw [hqp])
          else
            (tail₀ q ((Finset.mem_cons.mp hq).resolve_left hqp) h hh).copy
              (hub'q q hqp).symm rfl
        with htail'def
      have tail_pos : ∀ (hq : p ∈ Finset.cons p P₀ hpP₀) h (hh : h ∈ pool),
          tail' p hq h hh = (tailp h (hpsub hh)).copy hub'p.symm rfl :=
        fun hq h hh => dif_pos rfl
      have tail_neg : ∀ q (hqp : q ≠ p) (hq : q ∈ Finset.cons p P₀ hpP₀) h
          (hh : h ∈ pool),
          tail' q hq h hh =
            (tail₀ q ((Finset.mem_cons.mp hq).resolve_left hqp) h hh).copy
              (hub'q q hqp).symm rfl :=
        fun q hqp hq h hh => dif_neg hqp
      refine ⟨pool, hpsub.trans hp1H, hpcard, τ', hub', tail', ?_, ?_, ?_⟩
      · intro q hq
        by_cases hqp : q = p
        · subst hqp
          rw [τ'p, hub'p]
          exact ⟨hτp, hvp⟩
        · rw [τ'q q hqp, hub'q q hqp]
          exact hspec1 q ((Finset.mem_cons.mp hq).resolve_left hqp)
      · intro q hq h hh
        by_cases hqp : q = p
        · subst hqp
          rw [tail_pos hq h hh, τ'p]
          refine ⟨?_, ?_, ?_⟩
          · simpa using htpPath h (hpsub hh)
          · simpa using htpLen h (hpsub hh)
          · intro w hw
            rw [SimpleGraph.Walk.support_copy] at hw
            exact htpSupp h (hpsub hh) w hw
        · rw [tail_neg q hqp hq h hh, τ'q q hqp]
          have h₀ := hspec2 q ((Finset.mem_cons.mp hq).resolve_left hqp) h hh
          refine ⟨?_, ?_, ?_⟩
          · simpa using h₀.1
          · simpa using h₀.2.1
          · intro w hw
            rw [SimpleGraph.Walk.support_copy] at hw
            exact h₀.2.2 w hw
      · intro q hq h hh h' hh' hne w hw hw'
        by_cases hqp : q = p
        · subst hqp
          rw [tail_pos hq h hh, SimpleGraph.Walk.support_copy] at hw
          rw [tail_pos hq h' hh', SimpleGraph.Walk.support_copy] at hw'
          rw [hub'p]
          exact htpInter h (hpsub hh) h' (hpsub hh') hne w hw hw'
        · rw [tail_neg q hqp hq h hh, SimpleGraph.Walk.support_copy] at hw
          rw [tail_neg q hqp hq h' hh', SimpleGraph.Walk.support_copy] at hw'
          rw [hub'q q hqp]
          exact hspec3 q ((Finset.mem_cons.mp hq).resolve_left hqp) h hh h' hh'
            hne w hw hw'

/-- An internally disjoint system of uniform-length routed paths between
distinguished hub vertices: exactly the data of a subgraph copy of
`subdividedClique n r` in `G` (for `r ≥ 1`), with the interior of the path
for an edge `e` providing the `r` subdivision vertices of `e`. -/
private structure RoutedSystem {V : Type} (G : SimpleGraph V) (n r : ℕ) where
  hub : Fin n → V
  hub_inj : Function.Injective hub
  path : (e : {z : Fin n × Fin n // z.1 < z.2}) → G.Walk (hub e.1.1) (hub e.1.2)
  path_isPath : ∀ e, (path e).IsPath
  path_length : ∀ e, (path e).length = r + 1
  hub_avoid : ∀ e a, a ≠ e.1.1 → a ≠ e.1.2 → ∀ w ∈ (path e).support, w ≠ hub a
  path_inter : ∀ e e', e ≠ e' → ∀ w, w ∈ (path e).support →
    w ∈ (path e').support → w = hub e.1.1 ∨ w = hub e.1.2

/-- The vertex map of the subgraph copy induced by a routed system. -/
private def routedMap {V : Type} {G : SimpleGraph V} {n r : ℕ}
    (sys : RoutedSystem G n r) : SubdividedCliqueVert n r → V
  | .inl a => sys.hub a
  | .inr (e, k) => (sys.path e).getVert (k.1 + 1)

/-- A routed system yields a subgraph copy of the subdivided clique. -/
private theorem RoutedSystem.isContained {V : Type} {G : SimpleGraph V} {n r : ℕ}
    (sys : RoutedSystem G n r) (hr : 1 ≤ r) :
    (subdividedClique n r).IsContained G := by
  classical
  -- Interior vertices lie on the path's support.
  have hmem : ∀ (e : {z : Fin n × Fin n // z.1 < z.2}) (k : Fin r),
      (sys.path e).getVert (k.1 + 1) ∈ (sys.path e).support := by
    intro e k
    refine SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨k.1 + 1, rfl, ?_⟩
    rw [sys.path_length e]
    have := k.isLt
    omega
  -- Interior vertices differ from both endpoints of their own path.
  have hne_start : ∀ e (k : Fin r),
      (sys.path e).getVert (k.1 + 1) ≠ sys.hub e.1.1 := by
    intro e k hcon
    have h0 : (sys.path e).getVert 0 = sys.hub e.1.1 :=
      SimpleGraph.Walk.getVert_zero _
    have := (sys.path_isPath e).getVert_injOn
      (by rw [Set.mem_setOf_eq, sys.path_length e]; have := k.isLt; omega)
      (by rw [Set.mem_setOf_eq, sys.path_length e]; omega)
      (hcon.trans h0.symm)
    omega
  have hne_end : ∀ e (k : Fin r),
      (sys.path e).getVert (k.1 + 1) ≠ sys.hub e.1.2 := by
    intro e k hcon
    have hlen := sys.path_length e
    have h0 : (sys.path e).getVert (r + 1) = sys.hub e.1.2 := by
      rw [← hlen]; exact SimpleGraph.Walk.getVert_length _
    have := (sys.path_isPath e).getVert_injOn
      (by rw [Set.mem_setOf_eq, hlen]; have := k.isLt; omega)
      (by rw [Set.mem_setOf_eq, hlen])
      (hcon.trans h0.symm)
    have := k.isLt
    omega
  -- Adjacency preservation.
  have hadj : ∀ {z z' : SubdividedCliqueVert n r},
      (subdividedClique n r).Adj z z' →
        G.Adj (routedMap sys z) (routedMap sys z') := by
    intro z z' hzz'
    obtain ⟨hne, hrel⟩ := hzz'
    rcases z with a | ⟨e, k⟩ <;> rcases z' with b | ⟨e', k'⟩
    · -- inl / inl: impossible since r ≥ 1
      exfalso
      rcases hrel with h | h
      · exact absurd (h : r = 0) (by omega)
      · exact absurd (h : r = 0) (by omega)
    · -- inl / inr
      have hcase : (a = e'.val.1 ∧ k'.val = 0) ∨ (a = e'.val.2 ∧ k'.val = r - 1) := by
        rcases hrel with h | h
        · exact h
        · exact h.elim
      show G.Adj (sys.hub a) ((sys.path e').getVert (k'.1 + 1))
      rcases hcase with ⟨rfl, hk0⟩ | ⟨rfl, hkr⟩
      · have h0 : (sys.path e').getVert 0 = sys.hub e'.1.1 :=
          SimpleGraph.Walk.getVert_zero _
        have hstep : G.Adj ((sys.path e').getVert 0) ((sys.path e').getVert (0 + 1)) :=
          (sys.path e').adj_getVert_succ (by rw [sys.path_length e']; omega)
        rw [hk0]
        rw [h0] at hstep
        exact hstep
      · have hlen := sys.path_length e'
        have hend : (sys.path e').getVert (r + 1) = sys.hub e'.1.2 := by
          rw [← hlen]; exact SimpleGraph.Walk.getVert_length _
        have hstep : G.Adj ((sys.path e').getVert r) ((sys.path e').getVert (r + 1)) :=
          (sys.path e').adj_getVert_succ (by rw [hlen]; omega)
        have hk1 : k'.1 + 1 = r := by have := k'.isLt; omega
        rw [hk1]
        rw [hend] at hstep
        exact hstep.symm
    · -- inr / inl
      have hcase : (b = e.val.1 ∧ k.val = 0) ∨ (b = e.val.2 ∧ k.val = r - 1) := by
        rcases hrel with h | h
        · exact h.elim
        · exact h
      show G.Adj ((sys.path e).getVert (k.1 + 1)) (sys.hub b)
      rcases hcase with ⟨rfl, hk0⟩ | ⟨rfl, hkr⟩
      · have h0 : (sys.path e).getVert 0 = sys.hub e.1.1 :=
          SimpleGraph.Walk.getVert_zero _
        have hstep : G.Adj ((sys.path e).getVert 0) ((sys.path e).getVert (0 + 1)) :=
          (sys.path e).adj_getVert_succ (by rw [sys.path_length e]; omega)
        rw [hk0]
        rw [h0] at hstep
        exact hstep.symm
      · have hlen := sys.path_length e
        have hend : (sys.path e).getVert (r + 1) = sys.hub e.1.2 := by
          rw [← hlen]; exact SimpleGraph.Walk.getVert_length _
        have hstep : G.Adj ((sys.path e).getVert r) ((sys.path e).getVert (r + 1)) :=
          (sys.path e).adj_getVert_succ (by rw [hlen]; omega)
        have hk1 : k.1 + 1 = r := by have := k.isLt; omega
        rw [hk1]
        rw [hend] at hstep
        exact hstep
    · -- inr / inr
      show G.Adj ((sys.path e).getVert (k.1 + 1)) ((sys.path e').getVert (k'.1 + 1))
      rcases hrel with ⟨heq, hkk'⟩ | ⟨heq, hkk'⟩
      · obtain rfl := heq
        have hstep : G.Adj ((sys.path e).getVert (k.1 + 1))
            ((sys.path e).getVert (k.1 + 1 + 1)) :=
          (sys.path e).adj_getVert_succ
            (by rw [sys.path_length e]; have := k'.isLt; omega)
        have hk1 : k'.1 = k.1 + 1 := hkk'.symm
        rw [hk1]
        exact hstep
      · obtain rfl := heq
        have hstep : G.Adj ((sys.path e').getVert (k'.1 + 1))
            ((sys.path e').getVert (k'.1 + 1 + 1)) :=
          (sys.path e').adj_getVert_succ
            (by rw [sys.path_length e']; have := k.isLt; omega)
        have hk1 : k.1 = k'.1 + 1 := hkk'.symm
        rw [hk1]
        exact hstep.symm
  -- Injectivity.
  have hinj : Function.Injective (routedMap sys) := by
    intro z z' heq
    rcases z with a | ⟨e, k⟩ <;> rcases z' with b | ⟨e', k'⟩
    · rw [sys.hub_inj heq]
    · exfalso
      have heq' : sys.hub a = (sys.path e').getVert (k'.1 + 1) := heq
      by_cases ha1 : a = e'.1.1
      · subst ha1; exact hne_start e' k' heq'.symm
      by_cases ha2 : a = e'.1.2
      · subst ha2; exact hne_end e' k' heq'.symm
      exact sys.hub_avoid e' a ha1 ha2 _ (hmem e' k') heq'.symm
    · exfalso
      have heq' : (sys.path e).getVert (k.1 + 1) = sys.hub b := heq
      by_cases hb1 : b = e.1.1
      · subst hb1; exact hne_start e k heq'
      by_cases hb2 : b = e.1.2
      · subst hb2; exact hne_end e k heq'
      exact sys.hub_avoid e b hb1 hb2 _ (hmem e k) heq'
    · have heq' : (sys.path e).getVert (k.1 + 1) =
          (sys.path e').getVert (k'.1 + 1) := heq
      by_cases hee : e = e'
      · subst hee
        have hkk : k.1 + 1 = k'.1 + 1 :=
          (sys.path_isPath e).getVert_injOn
            (by rw [Set.mem_setOf_eq, sys.path_length e]; have := k.isLt; omega)
            (by rw [Set.mem_setOf_eq, sys.path_length e]; have := k'.isLt; omega)
            heq'
        have : k = k' := Fin.ext (by omega)
        rw [this]
      · exfalso
        have hw := sys.path_inter e e' hee _ (hmem e k)
          (by rw [heq']; exact hmem e' k')
        rcases hw with h1 | h1
        · exact hne_start e k h1
        · exact hne_end e k h1
  exact ⟨⟨⟨routedMap sys, fun {a b} h => hadj h⟩, hinj⟩⟩

/-- Middle-length palette bound: bypassed middle segments have length at most
`2d`, so the final Ramsey over principal pairs uses `2d + 1` colours. -/
private noncomputable def middleRamsey (d m : ℕ) : ℕ := ramseyFor (Fin (2 * d + 1)) m

/-- Number of principal branch sets: enough for the tail-length pigeonhole
followed by the middle-length Ramsey. -/
private noncomputable def principalCount (d m : ℕ) : ℕ := (d + 1) * middleRamsey d m

/-- Number of helper branch sets: enough for the nested refinement to leave a
pool that can serve every principal pair a private helper. -/
private noncomputable def helperCount (d m : ℕ) : ℕ :=
  multiThreshold d (principalCount d m ^ 2 + 3) (principalCount d m)

/-- Total number of branch sets consumed by the helper-routing argument. -/
private noncomputable def bridgeThreshold (d m : ℕ) : ℕ :=
  principalCount d m + helperCount d m

/-- The helper-routing construction: a depth-`d` shallow-minor model of
`K_{t+1}` with `t + 1 ≥ bridgeThreshold d m` yields subgraph copies of
`subdividedClique n r` for every `n ≤ m`, at one uniform interior length
`r ≤ 4d + 1`. -/
private theorem exists_uniform_subdivision
    {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {d t : ℕ}
    (model : ShallowMinorModel (SimpleGraph.completeGraph (Fin (t + 1))) G d)
    (m : ℕ) (ht : bridgeThreshold d m ≤ t + 1) :
    ∃ r, r ≤ 4 * d + 1 ∧ ∀ n, n ≤ m → (subdividedClique n r).IsContained G := by
  classical
  -- Split the branch sets into principals `P` and helpers `H`.
  obtain ⟨P, -, hPcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin (t + 1))))
      (n := principalCount d m)
      (by rw [Finset.card_univ, Fintype.card_fin]; unfold bridgeThreshold at ht; omega)
  obtain ⟨H, hHsub, hHcard⟩ :=
    Finset.exists_subset_card_eq (s := Finset.univ \ P) (n := helperCount d m)
      (by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
          Fintype.card_fin, hPcard]
        unfold bridgeThreshold at ht
        omega)
  have hPH : ∀ {q : Fin (t + 1)}, q ∈ H → q ∉ P := by
    intro q hq
    have h1 := hHsub hq
    rw [Finset.mem_sdiff] at h1
    exact h1.2
  have hPHne : ∀ p h : Fin (t + 1), p ∈ P → h ∈ H → p ≠ h := by
    intro p h hp hh hcon
    subst hcon
    exact hPH hh hp
  -- Choose bridge edges and centre-to-bridge legs on both sides.
  have key : ∀ p h : Fin (t + 1), ∃ (xv yv : V)
      (wP : G.Walk (model.center p) xv) (wH : G.Walk (model.center h) yv),
      p ∈ P → h ∈ H →
        xv ∈ model.branchSet p ∧ yv ∈ model.branchSet h ∧ G.Adj xv yv ∧
        wP.IsPath ∧ wP.length ≤ d ∧ (∀ z ∈ wP.support, z ∈ model.branchSet p) ∧
        wH.IsPath ∧ wH.length ≤ d ∧ (∀ z ∈ wH.support, z ∈ model.branchSet h) := by
    intro p h
    by_cases hc : p ∈ P ∧ h ∈ H
    · have hne : p ≠ h := hPHne p h hc.1 hc.2
      have hadj : (SimpleGraph.completeGraph (Fin (t + 1))).Adj p h :=
        (SimpleGraph.top_adj _ _).mpr hne
      obtain ⟨xv, hxv, yv, hyv, hxy⟩ := model.branchEdge p h hadj
      obtain ⟨wP, hwP1, hwP2, hwP3⟩ := model.branchRadius p xv hxv
      obtain ⟨wH, hwH1, hwH2, hwH3⟩ := model.branchRadius h yv hyv
      exact ⟨xv, yv, wP, wH, fun _ _ =>
        ⟨hxv, hyv, hxy, hwP1, hwP2, hwP3, hwH1, hwH2, hwH3⟩⟩
    · exact ⟨model.center p, model.center h, SimpleGraph.Walk.nil,
        SimpleGraph.Walk.nil, fun hp hh => absurd ⟨hp, hh⟩ hc⟩
  choose bx byv legP legH hkey using key
  -- Nested refinement over all principals.
  obtain ⟨pool, hpoolH, hpoolQ, τf, hubf, tails, hspec1, hspec2, hspec3⟩ :=
    multi_focus (B := model.branchSet) (c := model.center) bx P H
      (principalCount d m ^ 2 + 3) (by omega)
      (fun p hp h hh => legP p h)
      (fun p hp h hh => (hkey p h hp hh).2.2.2.1)
      (fun p hp h hh => (hkey p h hp hh).2.2.2.2.1)
      (fun p hp h hh => (hkey p h hp hh).2.2.2.2.2.1)
      (by rw [hHcard, hPcard]; exact le_rfl)
  -- Pigeonhole the principals to a common tail length `τ0`.
  set τsel : Fin (t + 1) → Fin (d + 1) := fun p => ⟨min (τf p) d, by omega⟩
    with hτseldef
  obtain ⟨τ0f, -, hfib⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (f := τsel) (n := middleRamsey d m)
      (fun a _ => Finset.mem_univ _) Finset.univ_nonempty
      (by rw [Finset.card_univ, Fintype.card_fin, hPcard]; exact le_rfl)
  set P' := {p ∈ P | τsel p = τ0f} with hP'def
  have hP'P : P' ⊆ P := Finset.filter_subset _ _
  set τ0 : ℕ := (τ0f : Fin (d + 1)).1 with hτ0def
  have hτ0d : τ0 ≤ d := Nat.lt_succ_iff.mp τ0f.isLt
  have hP'τ : ∀ p, p ∈ P' → τf p = τ0 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    simp only [hτseldef] at hp2
    have h3 := congrArg Fin.val hp2
    have h4 := (hspec1 p hp1).1
    simpa [Nat.min_eq_left h4] using h3
  -- Assign a private helper to every principal pair.
  set D := {z : Fin (t + 1) × Fin (t + 1) // z.1 ∈ P' ∧ z.2 ∈ P' ∧ z.1 < z.2}
    with hDdef
  have hcardD : Fintype.card D ≤ principalCount d m ^ 2 + 3 := by
    have h1 : Fintype.card D ≤ Fintype.card (↥P' × ↥P') :=
      Fintype.card_le_of_embedding
        ⟨fun z => (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2.1⟩), by
          intro z z' hzz'
          have h1 := congrArg (fun w : ↥P' × ↥P' => (w.1 : Fin (t + 1))) hzz'
          have h2 := congrArg (fun w : ↥P' × ↥P' => (w.2 : Fin (t + 1))) hzz'
          simp only at h1 h2
          exact Subtype.ext (Prod.ext h1 h2)⟩
    have h2 : Fintype.card (↥P' × ↥P') = P'.card * P'.card := by
      rw [Fintype.card_prod, Fintype.card_coe]
    have h3 : P'.card ≤ principalCount d m := by
      calc P'.card ≤ P.card := Finset.card_le_card hP'P
        _ = principalCount d m := hPcard
    calc Fintype.card D ≤ Fintype.card (↥P' × ↥P') := h1
      _ = P'.card * P'.card := h2
      _ ≤ principalCount d m * principalCount d m := Nat.mul_le_mul h3 h3
      _ = principalCount d m ^ 2 := (pow_two _).symm
      _ ≤ principalCount d m ^ 2 + 3 := Nat.le_add_right _ 3
  obtain ⟨φ, hφrange⟩ :=
    Function.Embedding.exists_of_card_le_finset (α := D) (s := pool)
      (le_trans hcardD hpoolQ)
  have hφmem : ∀ z : D, φ z ∈ pool := fun z =>
    Finset.mem_coe.mp (hφrange ⟨z, rfl⟩)
  have hzP1 : ∀ z : D, z.1.1 ∈ P := fun z => hP'P z.2.1
  have hzP2 : ∀ z : D, z.1.2 ∈ P := fun z => hP'P z.2.2.1
  have hφH : ∀ z : D, φ z ∈ H := fun z => hpoolH (hφmem z)
  -- Middle segments through the private helpers.
  set mid : (z : D) → G.Walk (byv z.1.1 (φ z)) (byv z.1.2 (φ z)) := fun z =>
    ((legH z.1.1 (φ z)).reverse.append (legH z.1.2 (φ z))).bypass with hmiddef
  have hmid_isPath : ∀ z : D, (mid z).IsPath := fun z =>
    SimpleGraph.Walk.bypass_isPath _
  have hmid_len : ∀ z : D, (mid z).length ≤ 2 * d := by
    intro z
    have h1 := (hkey z.1.1 (φ z) (hzP1 z) (hφH z)).2.2.2.2.2.2.2.1
    have h2 := (hkey z.1.2 (φ z) (hzP2 z) (hφH z)).2.2.2.2.2.2.2.1
    calc (mid z).length
        ≤ ((legH z.1.1 (φ z)).reverse.append (legH z.1.2 (φ z))).length :=
          SimpleGraph.Walk.length_bypass_le _
      _ = (legH z.1.1 (φ z)).length + (legH z.1.2 (φ z)).length := by
          rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
      _ ≤ 2 * d := by omega
  have hmid_supp : ∀ z : D, ∀ w ∈ (mid z).support, w ∈ model.branchSet (φ z) := by
    intro z w hw
    have hw2 := SimpleGraph.Walk.support_bypass_subset _ hw
    rw [SimpleGraph.Walk.mem_support_append_iff] at hw2
    rcases hw2 with hw3 | hw3
    · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw3
      exact (hkey z.1.1 (φ z) (hzP1 z) (hφH z)).2.2.2.2.2.2.2.2 w hw3
    · exact (hkey z.1.2 (φ z) (hzP2 z) (hφH z)).2.2.2.2.2.2.2.2 w hw3
  -- Final Ramsey: uniform middle length `ρ` over principal pairs.
  set midLen : Fin (t + 1) → Fin (t + 1) → ℕ := fun a b =>
    if hz : a ∈ P' ∧ b ∈ P' ∧ a < b then (mid ⟨(a, b), hz⟩).length else 0
    with hmidLendef
  have hmidLen_le : ∀ a b, midLen a b ≤ 2 * d := by
    intro a b
    simp only [hmidLendef]
    split
    · exact hmid_len _
    · omega
  obtain ⟨ρ0, S', hS'card, hS'pat⟩ :=
    exists_monochromatic_subset (ι := ↥P') (C := Fin (2 * d + 1))
      (colour := fun a b =>
        if (a : Fin (t + 1)) < b then
          (⟨midLen a b, by have := hmidLen_le (a : Fin (t + 1)) b; omega⟩ :
            Fin (2 * d + 1))
        else if (b : Fin (t + 1)) < a then
          ⟨midLen b a, by have := hmidLen_le (b : Fin (t + 1)) a; omega⟩
        else 0)
      (fun a b => by
        beta_reduce
        rcases lt_trichotomy (a : Fin (t + 1)) (b : Fin (t + 1)) with h | h | h
        · simp only [if_pos h, if_neg (lt_asymm h)]
        · have h1 : ¬((a : Fin (t + 1)) < b) := by rw [h]; exact lt_irrefl _
          have h2 : ¬((b : Fin (t + 1)) < a) := by rw [← h]; exact lt_irrefl _
          simp only [if_neg h1, if_neg h2]
        · simp only [if_pos h, if_neg (lt_asymm h)])
      m
      (by rw [Fintype.card_coe]; exact hfib)
  set S := S'.image Subtype.val with hSdef
  have hSP' : S ⊆ P' := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨a, -, rfl⟩
    exact a.2
  have hScard : m ≤ S.card := by
    rw [hSdef, Finset.card_image_of_injective _ Subtype.val_injective]
    exact hS'card
  set ρ : ℕ := (ρ0 : Fin (2 * d + 1)).1 with hρdef
  have hρ2d : ρ ≤ 2 * d := Nat.lt_succ_iff.mp ρ0.isLt
  have hSmid : ∀ a b (_ : a ∈ S) (_ : b ∈ S) (_ : a < b)
      (hz : a ∈ P' ∧ b ∈ P' ∧ a < b), (mid ⟨(a, b), hz⟩).length = ρ := by
    intro a b ha hb hab hz
    rw [hSdef] at ha hb
    rcases Finset.mem_image.mp ha with ⟨a', ha', rfl⟩
    rcases Finset.mem_image.mp hb with ⟨b', hb', rfl⟩
    have hne : a' ≠ b' := fun hcon =>
      absurd (congrArg Subtype.val hcon) (ne_of_lt hab)
    have h1 := hS'pat a' ha' b' hb' hne
    beta_reduce at h1
    rw [if_pos hab] at h1
    have h2 := congrArg Fin.val h1
    simp only [hmidLendef] at h2
    rw [dif_pos hz] at h2
    exact h2
  -- The uniform interior length.
  refine ⟨2 * τ0 + ρ + 1, by omega, ?_⟩
  intro n hn
  obtain ⟨S₀, hS₀S, hS₀card⟩ := Finset.exists_subset_card_eq (le_trans hn hScard)
  set ι := S₀.orderIsoOfFin hS₀card with hιdef
  have hkS : ∀ k : Fin n, (ι k : Fin (t + 1)) ∈ S := fun k => hS₀S (ι k).2
  have hkP' : ∀ k : Fin n, (ι k : Fin (t + 1)) ∈ P' := fun k => hSP' (hkS k)
  have hkP : ∀ k : Fin n, (ι k : Fin (t + 1)) ∈ P := fun k => hP'P (hkP' k)
  have hι_lt : ∀ {a b : Fin n}, a < b → (ι a : Fin (t + 1)) < (ι b : Fin (t + 1)) := by
    intro a b hab
    have h1 : ι a < ι b := (OrderIso.lt_iff_lt ι).mpr hab
    exact_mod_cast h1
  have hι_inj : ∀ {a b : Fin n}, (ι a : Fin (t + 1)) = (ι b : Fin (t + 1)) → a = b := by
    intro a b hab
    exact ι.injective (Subtype.ext hab)
  -- Edge bookkeeping.
  set edgeD : {z : Fin n × Fin n // z.1 < z.2} → D := fun e =>
    ⟨((ι e.1.1 : Fin (t + 1)), (ι e.1.2 : Fin (t + 1))),
      hkP' e.1.1, hkP' e.1.2, hι_lt e.2⟩ with hedgeDdef
  have hedgeD_inj : ∀ {e e' : {z : Fin n × Fin n // z.1 < z.2}},
      e ≠ e' → edgeD e ≠ edgeD e' := by
    intro e e' hne hcon
    apply hne
    have h1 := congrArg (fun z : D => z.1.1) hcon
    have h2 := congrArg (fun z : D => z.1.2) hcon
    simp only [hedgeDdef] at h1 h2
    exact Subtype.ext (Prod.ext (hι_inj h1) (hι_inj h2))
  have hbridge : ∀ (p h : Fin (t + 1)), p ∈ P → h ∈ H → G.Adj (bx p h) (byv p h) :=
    fun p h hp hh => (hkey p h hp hh).2.2.1
  -- The routed path of an edge:
  -- tail into the bridge, middle through the private helper, reversed tail out.
  set route : (e : {z : Fin n × Fin n // z.1 < z.2}) →
      G.Walk (hubf (ι e.1.1 : Fin (t + 1))) (hubf (ι e.1.2 : Fin (t + 1))) := fun e =>
    (tails _ (hkP e.1.1) _ (hφmem (edgeD e))).append
      (SimpleGraph.Walk.cons (hbridge _ _ (hkP e.1.1) (hφH (edgeD e)))
        ((mid (edgeD e)).append
          (SimpleGraph.Walk.cons (hbridge _ _ (hkP e.1.2) (hφH (edgeD e))).symm
            (tails _ (hkP e.1.2) _ (hφmem (edgeD e))).reverse)))
    with hroutedef
  have hroute_supp_eq : ∀ e, (route e).support =
      (tails _ (hkP e.1.1) _ (hφmem (edgeD e))).support ++
      ((mid (edgeD e)).support ++
        (tails _ (hkP e.1.2) _ (hφmem (edgeD e))).reverse.support) := by
    intro e
    simp only [hroutedef, SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_cons, List.tail_cons]
  have hroute_len : ∀ e, (route e).length = 2 * τ0 + ρ + 2 := by
    intro e
    simp only [hroutedef, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse]
    have h1 := (hspec2 _ (hkP e.1.1) _ (hφmem (edgeD e))).2.1
    have h2 := (hspec2 _ (hkP e.1.2) _ (hφmem (edgeD e))).2.1
    have h3 : (mid (edgeD e)).length = ρ :=
      hSmid _ _ (hkS e.1.1) (hkS e.1.2) (hι_lt e.2) _
    have hτ1 : τf (ι e.1.1 : Fin (t + 1)) = τ0 := hP'τ _ (hkP' e.1.1)
    have hτ2 : τf (ι e.1.2 : Fin (t + 1)) = τ0 := hP'τ _ (hkP' e.1.2)
    omega
  have hroute_isPath : ∀ e, (route e).IsPath := by
    intro e
    rw [SimpleGraph.Walk.isPath_def, hroute_supp_eq e]
    have hA := (hspec2 _ (hkP e.1.1) _ (hφmem (edgeD e))).1
    have hC := (hspec2 _ (hkP e.1.2) _ (hφmem (edgeD e))).1
    have hsuppA := (hspec2 _ (hkP e.1.1) _ (hφmem (edgeD e))).2.2
    have hsuppC := (hspec2 _ (hkP e.1.2) _ (hφmem (edgeD e))).2.2
    have hne12 : (ι e.1.1 : Fin (t + 1)) ≠ (ι e.1.2 : Fin (t + 1)) :=
      ne_of_lt (hι_lt e.2)
    have hneH1 : (ι e.1.1 : Fin (t + 1)) ≠ φ (edgeD e) :=
      hPHne _ _ (hkP e.1.1) (hφH (edgeD e))
    have hneH2 : (ι e.1.2 : Fin (t + 1)) ≠ φ (edgeD e) :=
      hPHne _ _ (hkP e.1.2) (hφH (edgeD e))
    refine List.Nodup.append (hA.support_nodup)
      (List.Nodup.append (hmid_isPath (edgeD e)).support_nodup
        (hC.reverse.support_nodup) ?_) ?_
    · -- middle vs reversed tail: helper branch set vs second principal's
      intro w hw hw'
      have hwB := hmid_supp (edgeD e) w hw
      have hw'' : w ∈ (tails _ (hkP e.1.2) _ (hφmem (edgeD e))).support := by
        rw [SimpleGraph.Walk.support_reverse] at hw'
        exact List.mem_reverse.mp hw'
      have hwB' := hsuppC w hw''
      exact Set.disjoint_left.mp (model.branchDisjoint _ _ hneH2.symm) hwB hwB'
    · -- first tail vs the rest
      intro w hw hw2
      have hwB := hsuppA w hw
      rcases List.mem_append.mp hw2 with hw3 | hw3
      · have hwB' := hmid_supp (edgeD e) w hw3
        exact Set.disjoint_left.mp (model.branchDisjoint _ _ hneH1) hwB hwB'
      · have hw'' : w ∈ (tails _ (hkP e.1.2) _ (hφmem (edgeD e))).support := by
          rw [SimpleGraph.Walk.support_reverse] at hw3
          exact List.mem_reverse.mp hw3
        have hwB' := hsuppC w hw''
        exact Set.disjoint_left.mp (model.branchDisjoint _ _ hne12) hwB hwB'
  -- Segment classification of a support vertex.
  have hsegment : ∀ e w, w ∈ (route e).support →
      (w ∈ (tails _ (hkP e.1.1) _ (hφmem (edgeD e))).support ∧
        w ∈ model.branchSet (ι e.1.1 : Fin (t + 1))) ∨
      w ∈ model.branchSet (φ (edgeD e)) ∨
      (w ∈ (tails _ (hkP e.1.2) _ (hφmem (edgeD e))).support ∧
        w ∈ model.branchSet (ι e.1.2 : Fin (t + 1))) := by
    intro e w hw
    rw [hroute_supp_eq e] at hw
    rcases List.mem_append.mp hw with hw1 | hw23
    · exact Or.inl ⟨hw1, (hspec2 _ (hkP e.1.1) _ (hφmem (edgeD e))).2.2 w hw1⟩
    rcases List.mem_append.mp hw23 with hw2 | hw3
    · exact Or.inr (Or.inl (hmid_supp (edgeD e) w hw2))
    · have hw3' : w ∈ (tails _ (hkP e.1.2) _ (hφmem (edgeD e))).support := by
        rw [SimpleGraph.Walk.support_reverse] at hw3
        exact List.mem_reverse.mp hw3
      exact Or.inr (Or.inr ⟨hw3',
        (hspec2 _ (hkP e.1.2) _ (hφmem (edgeD e))).2.2 w hw3'⟩)
  -- Transport a tail membership along an equality of principals.
  have htails_congr : ∀ p p' (hp : p ∈ P) (hp' : p' ∈ P), p = p' →
      ∀ h (hh : h ∈ pool) w, w ∈ (tails p' hp' h hh).support →
      w ∈ (tails p hp h hh).support := by
    intro p p' hp hp' heq h hh w hw
    subst heq
    exact hw
  -- Hub bookkeeping.
  have hhub_mem : ∀ p, p ∈ P → hubf p ∈ model.branchSet p :=
    fun p hp => (hspec1 p hp).2
  have hhub_inj : Function.Injective (fun k : Fin n => hubf (ι k : Fin (t + 1))) := by
    intro a b hcon
    by_contra hne'
    have hne'' : (ι a : Fin (t + 1)) ≠ (ι b : Fin (t + 1)) :=
      fun hcc => hne' (hι_inj hcc)
    refine Set.disjoint_left.mp (model.branchDisjoint _ _ hne'')
      (hhub_mem _ (hkP a)) ?_
    have hcon' : hubf (ι a : Fin (t + 1)) = hubf (ι b : Fin (t + 1)) := hcon
    rw [hcon']
    exact hhub_mem _ (hkP b)
  have hhub_avoid : ∀ (e : {z : Fin n × Fin n // z.1 < z.2}) (a : Fin n),
      a ≠ e.1.1 → a ≠ e.1.2 → ∀ w ∈ (route e).support,
      w ≠ hubf (ι a : Fin (t + 1)) := by
    intro e a ha1 ha2 w hw hcon
    have hwa : w ∈ model.branchSet (ι a : Fin (t + 1)) := by
      rw [hcon]
      exact hhub_mem _ (hkP a)
    rcases hsegment e w hw with ⟨-, hwB⟩ | hwB | ⟨-, hwB⟩
    · have hneA : (ι a : Fin (t + 1)) ≠ (ι e.1.1 : Fin (t + 1)) :=
        fun hcc => ha1 (hι_inj hcc)
      exact Set.disjoint_left.mp (model.branchDisjoint _ _ hneA) hwa hwB
    · have hneA : (ι a : Fin (t + 1)) ≠ φ (edgeD e) :=
        hPHne _ _ (hkP a) (hφH (edgeD e))
      exact Set.disjoint_left.mp (model.branchDisjoint _ _ hneA) hwa hwB
    · have hneA : (ι a : Fin (t + 1)) ≠ (ι e.1.2 : Fin (t + 1)) :=
        fun hcc => ha2 (hι_inj hcc)
      exact Set.disjoint_left.mp (model.branchDisjoint _ _ hneA) hwa hwB
  have hpath_inter : ∀ (e e' : {z : Fin n × Fin n // z.1 < z.2}), e ≠ e' →
      ∀ w, w ∈ (route e).support → w ∈ (route e').support →
      w = hubf (ι e.1.1 : Fin (t + 1)) ∨ w = hubf (ι e.1.2 : Fin (t + 1)) := by
    intro e e' hnee w hw hw'
    have hφne : φ (edgeD e) ≠ φ (edgeD e') := φ.injective.ne (hedgeD_inj hnee)
    have hHP : ∀ (p q : Fin (t + 1)), p ∈ P → q ∈ H →
        w ∈ model.branchSet p → w ∈ model.branchSet q → False := by
      intro p q hp hq hw1 hw2
      exact Set.disjoint_left.mp
        (model.branchDisjoint _ _ (hPHne p q hp hq)) hw1 hw2
    rcases hsegment e w hw with ⟨hwt, hwB⟩ | hwB | ⟨hwt, hwB⟩ <;>
      rcases hsegment e' w hw' with ⟨hwt', hwB'⟩ | hwB' | ⟨hwt', hwB'⟩
    · -- first tail vs first tail
      by_cases hpp : (ι e.1.1 : Fin (t + 1)) = (ι e'.1.1 : Fin (t + 1))
      · have hw'' := htails_congr _ _ (hkP e.1.1) (hkP e'.1.1) hpp _
          (hφmem (edgeD e')) w hwt'
        exact Or.inl (hspec3 _ (hkP e.1.1) _ (hφmem (edgeD e)) _
          (hφmem (edgeD e')) hφne w hwt hw'')
      · exact (Set.disjoint_left.mp (model.branchDisjoint _ _ hpp) hwB hwB').elim
    · exact (hHP _ _ (hkP e.1.1) (hφH (edgeD e')) hwB hwB').elim
    · -- first tail vs second tail
      by_cases hpp : (ι e.1.1 : Fin (t + 1)) = (ι e'.1.2 : Fin (t + 1))
      · have hw'' := htails_congr _ _ (hkP e.1.1) (hkP e'.1.2) hpp _
          (hφmem (edgeD e')) w hwt'
        exact Or.inl (hspec3 _ (hkP e.1.1) _ (hφmem (edgeD e)) _
          (hφmem (edgeD e')) hφne w hwt hw'')
      · exact (Set.disjoint_left.mp (model.branchDisjoint _ _ hpp) hwB hwB').elim
    · exact (hHP _ _ (hkP e'.1.1) (hφH (edgeD e)) hwB' hwB).elim
    · exact (Set.disjoint_left.mp
        (model.branchDisjoint _ _ hφne) hwB hwB').elim
    · exact (hHP _ _ (hkP e'.1.2) (hφH (edgeD e)) hwB' hwB).elim
    · -- second tail vs first tail
      by_cases hpp : (ι e.1.2 : Fin (t + 1)) = (ι e'.1.1 : Fin (t + 1))
      · have hw'' := htails_congr _ _ (hkP e.1.2) (hkP e'.1.1) hpp _
          (hφmem (edgeD e')) w hwt'
        exact Or.inr (hspec3 _ (hkP e.1.2) _ (hφmem (edgeD e)) _
          (hφmem (edgeD e')) hφne w hwt hw'')
      · exact (Set.disjoint_left.mp (model.branchDisjoint _ _ hpp) hwB hwB').elim
    · exact (hHP _ _ (hkP e.1.2) (hφH (edgeD e')) hwB hwB').elim
    · -- second tail vs second tail
      by_cases hpp : (ι e.1.2 : Fin (t + 1)) = (ι e'.1.2 : Fin (t + 1))
      · have hw'' := htails_congr _ _ (hkP e.1.2) (hkP e'.1.2) hpp _
          (hφmem (edgeD e')) w hwt'
        exact Or.inr (hspec3 _ (hkP e.1.2) _ (hφmem (edgeD e)) _
          (hφmem (edgeD e')) hφne w hwt hw'')
      · exact (Set.disjoint_left.mp (model.branchDisjoint _ _ hpp) hwB hwB').elim
  exact (RoutedSystem.mk (fun k => hubf (ι k : Fin (t + 1))) hhub_inj route
    hroute_isPath (fun e => by have := hroute_len e; omega)
    hhub_avoid hpath_inter).isContained (by omega)

/-- Local subdivided-clique nowhere denseness implies the shallow-minor
formulation, by the helper-routing construction; see the section
docstring. -/
private theorem isNowhereDense_of_isLocallyNowhereDense
    (C : GraphClass)
    (hLoc : IsLocallyNowhereDense C) :
    IsNowhereDense C := by
  intro d
  choose Nb hNb using hLoc
  set m := (Finset.range (4 * d + 2)).sup Nb with hmdef
  refine ⟨bridgeThreshold d m, ?_⟩
  intro V _ _ G hCG hMinor
  obtain ⟨model⟩ := hMinor
  obtain ⟨r, hr, hcont⟩ := exists_uniform_subdivision model m (by omega)
  have hrm : Nb r ≤ m := by
    rw [hmdef]
    exact Finset.le_sup (by rw [Finset.mem_range]; omega)
  exact hNb r G hCG (hcont (Nb r) hrm)

/-- Folklore equivalence between the local and shallow-minor
formulations of nowhere-denseness. -/
theorem isLocallyNowhereDense_iff_isNowhereDense (C : GraphClass) :
    IsLocallyNowhereDense C ↔
      IsNowhereDense C := by
  constructor
  · exact isNowhereDense_of_isLocallyNowhereDense C
  · exact isLocallyNowhereDense_of_isNowhereDense C


end Lax5Proofs.NowhereDenseBridge
