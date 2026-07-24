import Lax5Proofs.Ramsey
import Lax5Proofs.Subdivision
import Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.NowhereDense.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowTopologicalMinor.Full

/-!
Equivalence of the two nowhere-dense definitions in play: the
shallow-minor grad bound of the ported sparsity development
(`IsNowhereDense`) and Mählmann's local, subdivision-based definition
(`IsLocallyNowhereDense`, Def. 13.1).  The backward direction is the
substantial one: candidate paths → Ramsey-uniform length → canonical
pattern → trimming → a clean 1-subdivision.
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

/-- Step 1 data for the backward direction: starting from a shallow minor
model of `K_{t+1}`, record the centre-to-centre candidate walks obtained
by concatenating the branch-radius walks with the bridge edge. Each walk
has length at most `2 d + 1`. -/
private structure CandidatePathData {V : Type} (G : SimpleGraph V) (d t : ℕ) where
  model : ShallowMinorModel (SimpleGraph.completeGraph (Fin (t + 1))) G d
  /-- For every pair of distinct clique vertices `i ≠ j`, a walk in `G`
  between the corresponding branch-set centres. -/
  candidateWalk : ∀ {i j : Fin (t + 1)}, i ≠ j →
    G.Walk (model.center i) (model.center j)
  /-- Each candidate walk has length at most `2 d + 1`. -/
  candidateWalk_length_le : ∀ {i j : Fin (t + 1)} (h : i ≠ j),
    (candidateWalk h).length ≤ 2 * d + 1

/-- Step 2 data: after a multicolour Ramsey pass, all candidate paths on a
subclique `subclique` of size at least `m` share a common length
`commonLength ≤ 2d + 1`.

`hasCommonLengthWalk` is stated existentially (rather than fixing
`candidateWalk` itself) so that we can symmetrise the orientation: for a
subclique edge `{i, j}`, the common-length walk is realised by whichever of
`candidateWalk (i ≠ j)` or the reverse of `candidateWalk (j ≠ i)` matches
the Ramsey-monochromatic colour. Step 1 makes no symmetry guarantee
between `candidateWalk h` and `candidateWalk h.symm`, and the existential
form keeps Step 1 unchanged.

The size parameter `m` records the lower bound on the monochromatic
subclique produced by `multicolorRamsey`. It threads through downstream
steps so that Step 6 can pick a final `t` large enough to contradict the
local nowhere-dense hypothesis. -/
private structure UniformLengthData {V : Type} (G : SimpleGraph V) (d t m : ℕ)
    extends CandidatePathData G d t where
  subclique : Finset (Fin (t + 1))
  subclique_card_ge : m ≤ subclique.card
  commonLength : ℕ
  commonLength_le : commonLength ≤ 2 * d + 1
  hasCommonLengthWalk : ∀ {i j : Fin (t + 1)},
    i ∈ subclique → j ∈ subclique → i ≠ j →
    ∃ w : G.Walk (model.center i) (model.center j), w.length = commonLength

/-- Step 3 data: after the iterative two-colour Ramsey refinement, the
branching pattern at every interior level is canonical on the surviving
subclique. Concretely:

* `canonicalWalk` fixes a specific common-length walk between subclique
  centres, chosen via `Classical.choose` on the inherited
  `hasCommonLengthWalk` existential so that the rest of the scaffold can
  talk about concrete vertices of the walk.
* `patternShared i h` is the shared/disjoint flag at focus vertex `i` and
  interior level `h`: `true` means all canonical walks from `center i`
  pass through the same `h`-th vertex on the subclique, `false` means the
  `h`-th vertices are pairwise distinct as the other endpoint varies.
  Values outside the relevant range (`h ≥ commonLength`) are unspecified
  and the spec fields take no view of them. -/
private structure CanonicalPatternData {V : Type} (G : SimpleGraph V) (d t m : ℕ)
    extends UniformLengthData G d t m where
  /-- A concrete walk of length `commonLength` between the branch-set centres
  of any two distinct subclique vertices. Chosen to realise the inherited
  `hasCommonLengthWalk` existential. -/
  canonicalWalk : ∀ {i j : Fin (t + 1)},
    i ∈ subclique → j ∈ subclique → i ≠ j →
    G.Walk (model.center i) (model.center j)
  /-- Each canonical walk has length exactly `commonLength`. -/
  canonicalWalk_length : ∀ {i j : Fin (t + 1)}
    (hi : i ∈ subclique) (hj : j ∈ subclique) (hij : i ≠ j),
    (canonicalWalk hi hj hij).length = commonLength
  /-- Branching-pattern bit: for each focus vertex `i` and level `h`,
  `patternShared i h = true` means "all canonical walks from `center i`
  share the `h`-th vertex on the subclique", `false` means "they have
  pairwise distinct `h`-th vertices". Levels `h ≥ commonLength` are
  unconstrained. -/
  patternShared : Fin (t + 1) → ℕ → Bool
  /-- Spec for the "shared" bit: if `patternShared i h = true`, then for any
  two other subclique vertices `j`, `k`, the `h`-th vertices of the
  canonical walks `center i → center j` and `center i → center k` agree. -/
  patternShared_shared : ∀ {i j k : Fin (t + 1)}
    (hi : i ∈ subclique) (hj : j ∈ subclique) (hk : k ∈ subclique)
    (hij : i ≠ j) (hik : i ≠ k)
    {h : ℕ}, h < commonLength → patternShared i h = true →
    (canonicalWalk hi hj hij).getVert h =
      (canonicalWalk hi hk hik).getVert h
  /-- Spec for the "disjoint" bit: if `patternShared i h = false`, then for
  any two distinct other subclique vertices `j ≠ k`, the `h`-th vertices of
  the canonical walks `center i → center j` and `center i → center k`
  differ. -/
  patternShared_disjoint : ∀ {i j k : Fin (t + 1)}
    (hi : i ∈ subclique) (hj : j ∈ subclique) (hk : k ∈ subclique)
    (hij : i ≠ j) (hik : i ≠ k) (_hjk : j ≠ k)
    {h : ℕ}, h < commonLength → patternShared i h = false →
    (canonicalWalk hi hj hij).getVert h ≠
      (canonicalWalk hi hk hik).getVert h

/-- Step 4 data: after the shared prefixes/suffixes have been trimmed and any
residual interior collisions cleaned up, we have, on the surviving subclique,
a new system of internally disjoint walks of uniform length `trimmedLength + 1`
between trimmed centres `c_i' ∈ B_i`, with `trimmedLength ≤ 2d`.

The interior-disjointness spec is stated so that Step 5 can assemble a
`subdividedClique`-shaped subgraph copy: interiors of distinct trimmed walks
are entirely disjoint, and no interior vertex of a walk coincides with any
trimmed centre (other than the walk's own endpoints). -/
private structure TrimmedPathData {V : Type} (G : SimpleGraph V) (d t m : ℕ)
    extends CanonicalPatternData G d t m where
  /-- Uniform internal-path length, `ℓ' ≤ 2d`. -/
  trimmedLength : ℕ
  trimmedLength_le : trimmedLength ≤ 2 * d
  /-- Trimmed centre `c_i'` at the tip of `i`'s shared prefix. Lies in the
  branch set `B_i` of the minor model for every subclique vertex `i`. -/
  trimmedCenter : Fin (t + 1) → V
  trimmedCenter_mem : ∀ {i : Fin (t + 1)},
    i ∈ subclique → trimmedCenter i ∈ model.branchSet i
  /-- Trimmed walk between the trimmed centres of two distinct subclique
  vertices, of uniform length `trimmedLength + 1`. -/
  trimmedWalk : ∀ {i j : Fin (t + 1)},
    i ∈ subclique → j ∈ subclique → i ≠ j →
    G.Walk (trimmedCenter i) (trimmedCenter j)
  trimmedWalk_length : ∀ {i j : Fin (t + 1)}
    (hi : i ∈ subclique) (hj : j ∈ subclique) (hij : i ≠ j),
    (trimmedWalk hi hj hij).length = trimmedLength + 1
  trimmedWalk_isPath : ∀ {i j : Fin (t + 1)}
    (hi : i ∈ subclique) (hj : j ∈ subclique) (hij : i ≠ j),
    (trimmedWalk hi hj hij).IsPath
  /-- Centre-avoidance: no vertex of any trimmed walk equals any trimmed
  centre of the subclique, except at the walk's two own endpoints. -/
  trimmedWalk_avoids_centres : ∀ {i j k : Fin (t + 1)}
    (hi : i ∈ subclique) (hj : j ∈ subclique) (_hk : k ∈ subclique)
    (hij : i ≠ j) {v : V},
    v ∈ (trimmedWalk hi hj hij).support →
    v = trimmedCenter k → k = i ∨ k = j
  /-- Pairwise interior-disjointness: if a vertex lies on two trimmed walks
  indexed by distinct unordered pairs, it must already be one of the two
  endpoints of the first walk (and hence, by centre-avoidance on the other
  walk, also an endpoint of the second — the shared endpoint case). -/
  trimmedWalk_interior_disjoint : ∀ {i j i' j' : Fin (t + 1)}
    (hi : i ∈ subclique) (hj : j ∈ subclique) (hij : i ≠ j)
    (hi' : i' ∈ subclique) (hj' : j' ∈ subclique) (hi'j' : i' ≠ j')
    (_hpair_ne : s(i, j) ≠ s(i', j'))
    {v : V},
    v ∈ (trimmedWalk hi hj hij).support →
    v ∈ (trimmedWalk hi' hj' hi'j').support →
    v = trimmedCenter i ∨ v = trimmedCenter j

/-- Step 5 data: the cleaned path system has been packaged as a subgraph copy
of a subdivided clique in `G`. The subdivision order is at least `m`, which
is what Step 6 eventually inverts against the local nowhere-dense bound. -/
private structure CleanSubdivisionData {V : Type} (G : SimpleGraph V) (d t m : ℕ)
    extends TrimmedPathData G d t m where
  subdivisionOrder : ℕ
  subdivisionOrder_ge : m ≤ subdivisionOrder
  contained : (subdividedClique subdivisionOrder trimmedLength).IsContained G

/-- Backward direction, Step 1: from a shallow minor model, build the
centre-to-centre candidate paths of length at most `2d + 1`. -/
private noncomputable def backward_step1_candidate_paths
    {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    {d t : ℕ}
    (hMinor : IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) G d) :
    CandidatePathData G d t := by
  classical
  let model := hMinor.some
  have hwalk : ∀ {i j : Fin (t + 1)}, i ≠ j →
      ∃ w : G.Walk (model.center i) (model.center j), w.length ≤ 2 * d + 1 := by
    intro i j hij
    have hadj : (SimpleGraph.completeGraph (Fin (t + 1))).Adj i j :=
      (SimpleGraph.top_adj i j).mpr hij
    obtain ⟨x, hx, y, hy, hxy⟩ := model.branchEdge i j hadj
    obtain ⟨pxi, _, hxilen, _⟩ := model.branchRadius i x hx
    obtain ⟨pyj, _, hyjlen, _⟩ := model.branchRadius j y hy
    refine ⟨pxi.append (SimpleGraph.Walk.cons hxy pyj.reverse), ?_⟩
    simp [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_reverse]
    omega
  exact
    { model := model
      candidateWalk := fun {_ _} h => (hwalk h).choose
      candidateWalk_length_le := fun {_ _} h => (hwalk h).choose_spec }

/-- Backward direction, Step 2: multicolour Ramsey normalises the candidate
path lengths. We apply `Ramsey.multicolor_ramsey`
to the colouring `{i, j} ↦ min ((candidateWalk (i ≠ j)).length)
((candidateWalk (j ≠ i)).length)`, with all colours targeting a
monochromatic subclique of size `m`. The hypothesis `hThresh` asserts that
the Ramsey threshold fits into `t + 1`, so Ramsey fires and the output
carries a subclique of size at least `m`. The final `t` / `m` choice is
deferred to `backward_step6_extract_bound`. -/
private noncomputable def backward_step2_uniform_length
    {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    {d t m : ℕ}
    (hStep1 : CandidatePathData G d t)
    (hThresh :
      (Ramsey.multicolor_ramsey
          (List.replicate (2 * d + 2) m)
          List.replicate_succ_ne_nil).choose ≤ t + 1) :
    UniformLengthData G d t m := by
  classical
  -- Symmetric length function on ordered pairs; clamp to `Fin (2d + 2)`.
  let lenFn : Fin (t + 1) → Fin (t + 1) → ℕ := fun i j =>
    if h : i = j then 0
    else min (hStep1.candidateWalk h).length
            (hStep1.candidateWalk (Ne.symm h)).length
  have lenFn_le : ∀ i j, lenFn i j ≤ 2 * d + 1 := by
    intro i j
    change (if h : i = j then 0 else _) ≤ _
    by_cases h : i = j
    · simp [h]
    · rw [dif_neg h]
      have h1 := hStep1.candidateWalk_length_le h
      have h2 := hStep1.candidateWalk_length_le (Ne.symm h)
      omega
  have lenFn_symm : ∀ i j, lenFn i j = lenFn j i := by
    intro i j
    change (if h : i = j then 0 else _) = (if h : j = i then 0 else _)
    by_cases h : i = j
    · subst h; rfl
    · have h' : j ≠ i := Ne.symm h
      rw [dif_neg h, dif_neg h']
      exact Nat.min_comm _ _
  -- `multicolorRamsey` demands colours in `Fin sizes.length`. With
  -- `sizes := List.replicate (2 d + 2) m`, `sizes.length` is propositionally
  -- but not definitionally `2 d + 2`, so the colour function is typed in
  -- `Fin sizes.length` and we bridge via `List.length_replicate`.
  let colourFn : Sym2 (Fin (t + 1)) →
      Fin (List.replicate (2 * d + 2) m).length :=
    Sym2.lift
      ⟨fun i j => ⟨lenFn i j, by
          rw [List.length_replicate]
          exact Nat.lt_succ_of_le (lenFn_le i j)⟩,
        fun i j => Fin.ext (lenFn_symm i j)⟩
  -- `multicolorRamsey` lives in `Prop`; the target type `UniformLengthData`
  -- is a `Type`, so destructuring via `obtain` would fail with
  -- `Exists.casesOn can only eliminate into Prop`. Use `Classical.choose`
  -- instead, mirroring the Step 1 idiom for `IsShallowMinor`.
  let hRam :=
    Ramsey.multicolor_ramsey
      (List.replicate (2 * d + 2) m)
      List.replicate_succ_ne_nil
  have hcard : hRam.choose ≤ Fintype.card (Fin (t + 1)) := by
    simpa [Fintype.card_fin] using hThresh
  let hRamOut := hRam.choose_spec hcard colourFn
  let i_ram : Fin (List.replicate (2 * d + 2) m).length := hRamOut.choose
  let hS := hRamOut.choose_spec
  let S : Finset (Fin (t + 1)) := hS.choose
  have hSpair : (↑S : Set (Fin (t + 1))).Pairwise
      (fun u v => colourFn s(u, v) = i_ram) :=
    hS.choose_spec.2
  have hSgeM : m ≤ S.card := by
    have hsize : (List.replicate (2 * d + 2) m).get i_ram ≤ S.card :=
      hS.choose_spec.1
    -- `get` of a replicated list is the replicated value.
    have hi_lt : i_ram.val < 2 * d + 2 := by
      have := i_ram.isLt
      simpa [List.length_replicate] using this
    have hget : (List.replicate (2 * d + 2) m).get i_ram = m := by
      simp [List.get_eq_getElem, List.getElem_replicate]
    rw [hget] at hsize
    exact hsize
  refine
    { toCandidatePathData := hStep1
      subclique := S
      subclique_card_ge := hSgeM
      commonLength := i_ram.val
      commonLength_le := by
        have hi := i_ram.isLt
        have hLen : (List.replicate (2 * d + 2) m).length = 2 * d + 2 :=
          List.length_replicate
        omega
      hasCommonLengthWalk := ?_ }
  intro a b ha hb hab
  have haSet : a ∈ (↑S : Set (Fin (t + 1))) := by simpa using ha
  have hbSet : b ∈ (↑S : Set (Fin (t + 1))) := by simpa using hb
  have hcol : colourFn s(a, b) = i_ram := hSpair haSet hbSet hab
  have hval : lenFn a b = i_ram.val := by
    have hv := congrArg Fin.val hcol
    simpa [colourFn, Sym2.lift_mk] using hv
  have hlen : min (hStep1.candidateWalk hab).length
      (hStep1.candidateWalk (Ne.symm hab)).length = i_ram.val := by
    have : lenFn a b = min (hStep1.candidateWalk hab).length
        (hStep1.candidateWalk (Ne.symm hab)).length := by
      change (if h : a = b then 0 else _) = _
      rw [dif_neg hab]
    rw [this] at hval
    exact hval
  rcases Nat.le_total (hStep1.candidateWalk hab).length
      (hStep1.candidateWalk (Ne.symm hab)).length with hle | hle
  · refine ⟨hStep1.candidateWalk hab, ?_⟩
    rw [Nat.min_eq_left hle] at hlen
    exact hlen
  · refine ⟨(hStep1.candidateWalk (Ne.symm hab)).reverse, ?_⟩
    rw [SimpleGraph.Walk.length_reverse]
    rw [Nat.min_eq_right hle] at hlen
    exact hlen

/-- Non-emptiness helper for Step 3's Ramsey sizes list: the list is
`List.replicate K m` with `K` positive. -/
private lemma step3_sizes_ne_nil (d t m : ℕ) :
    List.replicate
        (Fintype.card (Fin (t + 1) → Fin (2 * d + 1) → Bool)) m ≠ [] := by
  rw [ne_eq, List.replicate_eq_nil_iff]
  exact Fintype.card_ne_zero

/-- Backward direction, Step 3: iterative two-colour Ramsey normalises the
shared-prefix/shared-suffix branching pattern.

`hThresh3` bounds the threshold returned by multicolour Ramsey applied with
`(t+1)*(2d+1)`-bit colours (one bit per focus vertex, interior level).
Combined with the inherited `m ≤ hStep2.subclique.card`, it guarantees the
Ramsey call fires on the subclique's subtype. The Ramsey-monochromatic
colour then reads off the canonical branching pattern: for each focus
vertex `i` in the refined subclique and each interior level `h`, either all
canonical walks from `center i` share the same `h`-th vertex on the refined
subclique, or they have pairwise distinct `h`-th vertices. -/
private noncomputable def backward_step3_canonical_pattern
    {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    {d t m : ℕ}
    (hStep2 : UniformLengthData G d t m)
    (hThresh3 :
      (Ramsey.multicolor_ramsey
          (List.replicate
            (Fintype.card (Fin (t + 1) → Fin (2 * d + 1) → Bool)) m)
          (step3_sizes_ne_nil d t m)).choose ≤ m) :
    CanonicalPatternData G d t m := by
  classical
  -- Shorthand for hStep2's subclique.
  let S₂ : Finset (Fin (t + 1)) := hStep2.subclique
  -- Pick concrete walks from the inherited existential.
  let walk : ∀ {i j : Fin (t + 1)},
      i ∈ S₂ → j ∈ S₂ → i ≠ j →
      G.Walk (hStep2.model.center i) (hStep2.model.center j) :=
    fun hi hj hij => (hStep2.hasCommonLengthWalk hi hj hij).choose
  have walk_length : ∀ {i j : Fin (t + 1)} (hi : i ∈ S₂) (hj : j ∈ S₂)
      (hij : i ≠ j),
      (walk hi hj hij).length = hStep2.commonLength :=
    fun hi hj hij => (hStep2.hasCommonLengthWalk hi hj hij).choose_spec
  -- Colour type for the Step-3 Ramsey: one Bool per (focus vertex, level).
  let ColourT : Type := Fin (t + 1) → Fin (2 * d + 1) → Bool
  let K : ℕ := Fintype.card ColourT
  let sizes : List ℕ := List.replicate K m
  -- Raw colour: given two subclique vertices `a ≠ b`, for each `(i, h)` the
  -- bit says whether the `h`-th vertex of walk `i → a` equals walk `i → b`
  -- at position `h`. When `i ∈ {a, b}` or `i ∉ S₂` we return `true`
  -- (the branch is irrelevant; chosen so the raw function is symmetric in
  -- `a, b`).
  let rawBit : ↥S₂ → ↥S₂ → ColourT := fun a b i h =>
    if hia : i = a.val then true
    else if hib : i = b.val then true
    else if hi : i ∈ S₂ then
      decide ((walk hi a.property hia).getVert h.val =
              (walk hi b.property hib).getVert h.val)
    else true
  have rawBit_sym : ∀ a b, rawBit a b = rawBit b a := by
    intro a b
    funext i h
    show (if hia : i = a.val then (true : Bool)
          else if hib : i = b.val then (true : Bool)
          else if hi : i ∈ S₂ then
            decide ((walk hi a.property hia).getVert h.val =
                    (walk hi b.property hib).getVert h.val)
          else (true : Bool)) =
         (if hia : i = b.val then (true : Bool)
          else if hib : i = a.val then (true : Bool)
          else if hi : i ∈ S₂ then
            decide ((walk hi b.property hia).getVert h.val =
                    (walk hi a.property hib).getVert h.val)
          else (true : Bool))
    by_cases hia : i = a.val
    · by_cases hib : i = b.val
      · rw [dif_pos hia, dif_pos hib]
      · rw [dif_pos hia, dif_neg hib, dif_pos hia]
    · by_cases hib : i = b.val
      · rw [dif_neg hia, dif_pos hib, dif_pos hib]
      · by_cases hi : i ∈ S₂
        · rw [dif_neg hia, dif_neg hib, dif_pos hi,
              dif_neg hib, dif_neg hia, dif_pos hi]
          congr 1
          exact propext eq_comm
        · rw [dif_neg hia, dif_neg hib, dif_neg hi,
              dif_neg hib, dif_neg hia, dif_neg hi]
  -- Sym2-lifted colour on subclique pairs.
  let colourFn : Sym2 ↥S₂ → ColourT := Sym2.lift ⟨rawBit, rawBit_sym⟩
  -- We need `colourFn` typed as `Sym2 ↥S₂ → Fin sizes.length`. Bridge via
  -- `Fintype.truncEquivFin` and `List.length_replicate`.
  let equivCol : ColourT ≃ Fin K := (Fintype.truncEquivFin ColourT).out
  have sizes_length : sizes.length = K := List.length_replicate
  let finColourFn : Sym2 ↥S₂ → Fin sizes.length := fun p =>
    Fin.cast sizes_length.symm (equivCol (colourFn p))
  -- Apply the multicolour Ramsey.
  have hRam_le : (Ramsey.multicolor_ramsey
      sizes (step3_sizes_ne_nil d t m)).choose ≤ Fintype.card (↥S₂) := by
    rw [Fintype.card_coe]
    exact hThresh3.trans hStep2.subclique_card_ge
  let hRam := Ramsey.multicolor_ramsey
      sizes (step3_sizes_ne_nil d t m)
  let hOut := hRam.choose_spec hRam_le finColourFn
  let c_ram : Fin sizes.length := hOut.choose
  let hOut2 := hOut.choose_spec
  let T : Finset ↥S₂ := hOut2.choose
  have hT_card : sizes.get c_ram ≤ T.card := hOut2.choose_spec.1
  have hT_pair : (↑T : Set ↥S₂).Pairwise
      (fun u v => finColourFn s(u, v) = c_ram) := hOut2.choose_spec.2
  -- `sizes.get c_ram = m` since all entries of `sizes` are `m`.
  have h_get_eq_m : sizes.get c_ram = m := by
    have hi_lt : c_ram.val < K := by
      simpa [sizes_length] using c_ram.isLt
    simp [sizes, List.get_eq_getElem, List.getElem_replicate]
  rw [h_get_eq_m] at hT_card
  -- Refined subclique in `Fin (t + 1)`.
  let S₃ : Finset (Fin (t + 1)) := T.image Subtype.val
  have hS₃_sub : ∀ {x}, x ∈ S₃ → x ∈ S₂ := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨⟨y, hy⟩, _, rfl⟩
    exact hy
  have hS₃_card : m ≤ S₃.card := by
    rw [show S₃.card = T.card from Finset.card_image_of_injective _ Subtype.val_injective]
    exact hT_card
  -- The monochromatic colour tuple, pulled back through `equivCol`.
  let patternCol : ColourT := equivCol.symm (Fin.cast sizes_length c_ram)
  -- Pattern on arbitrary levels: use the Ramsey colour bit for `h < 2*d+1`,
  -- and `true` elsewhere (vacuous; only `h < commonLength ≤ 2*d+1` is used).
  let patternShared : Fin (t + 1) → ℕ → Bool := fun i h =>
    if h_lt : h < 2 * d + 1 then patternCol i ⟨h, h_lt⟩ else true
  -- Key bridging fact: for two distinct elements `j ≠ k` of `T` (as
  -- subclique members), the raw colour at position `(i, h)` equals the
  -- monochromatic pattern bit `patternCol i h`.
  have colour_eq : ∀ {j k : ↥S₂}, j ∈ T → k ∈ T → j ≠ k →
      rawBit j k = patternCol := by
    intro j k hj hk hjk
    have hpair : finColourFn s(j, k) = c_ram := hT_pair hj hk hjk
    have hcol_eq : colourFn s(j, k) = patternCol := by
      have hrev : equivCol (colourFn s(j, k)) = Fin.cast sizes_length c_ram := by
        have := congrArg (Fin.cast sizes_length) hpair
        simpa [finColourFn, Fin.cast_cast] using this
      have := congrArg equivCol.symm hrev
      simpa [patternCol] using this
    simpa [colourFn, Sym2.lift_mk] using hcol_eq
  -- Build the shared spec.
  have shared_spec : ∀ {i j k : Fin (t + 1)}
      (hi : i ∈ S₃) (hj : j ∈ S₃) (hk : k ∈ S₃)
      (hij : i ≠ j) (hik : i ≠ k) {h : ℕ}, h < hStep2.commonLength →
      patternShared i h = true →
      (walk (hS₃_sub hi) (hS₃_sub hj) hij).getVert h =
        (walk (hS₃_sub hi) (hS₃_sub hk) hik).getVert h := by
    intro i j k hi hj hk hij hik h hh_lt hpat
    -- Case split j = k (trivial) vs j ≠ k (use Ramsey monochromaticity).
    by_cases hjk : j = k
    · subst hjk; rfl
    -- `hh_lt : h < commonLength ≤ 2*d+1`, so patternShared unfolds to patternCol.
    have hh_lt_all : h < 2 * d + 1 :=
      lt_of_lt_of_le hh_lt hStep2.commonLength_le
    have hpat_col : patternCol i ⟨h, hh_lt_all⟩ = true := by
      change (if h_lt : h < 2 * d + 1 then patternCol i ⟨h, h_lt⟩
              else (true : Bool)) = true at hpat
      rwa [dif_pos hh_lt_all] at hpat
    -- Extract ⟨j, _⟩, ⟨k, _⟩ ∈ T. j, k ∈ S₃ means their "upgraded" versions are in T.
    rcases Finset.mem_image.mp hj with ⟨jT, hjT, hjeq⟩
    rcases Finset.mem_image.mp hk with ⟨kT, hkT, hkeq⟩
    subst hjeq
    subst hkeq
    have hj_ne_k : jT ≠ kT := by
      intro heq; apply hjk; exact congrArg Subtype.val heq
    -- Apply colour_eq: rawBit jT kT = patternCol, in particular at (i, ⟨h, hh_lt_all⟩).
    have hbit : rawBit jT kT i ⟨h, hh_lt_all⟩ = patternCol i ⟨h, hh_lt_all⟩ := by
      rw [colour_eq hjT hkT hj_ne_k]
    rw [hpat_col] at hbit
    -- Unfold rawBit at the (i, ⟨h, hh_lt_all⟩) arguments with i ≠ jT.val, i ≠ kT.val,
    -- i ∈ S₂ (via hi ∈ S₃ ⇒ S₂).
    have hi_S₂ : i ∈ S₂ := hS₃_sub hi
    have hi_ne_j : i ≠ jT.val := hij
    have hi_ne_k : i ≠ kT.val := hik
    simp only [rawBit] at hbit
    rw [dif_neg hi_ne_j, dif_neg hi_ne_k, dif_pos hi_S₂] at hbit
    have : decide
        ((walk hi_S₂ jT.property hi_ne_j).getVert h =
         (walk hi_S₂ kT.property hi_ne_k).getVert h) = true := hbit
    exact of_decide_eq_true this
  have disjoint_spec : ∀ {i j k : Fin (t + 1)}
      (hi : i ∈ S₃) (hj : j ∈ S₃) (hk : k ∈ S₃)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      {h : ℕ}, h < hStep2.commonLength → patternShared i h = false →
      (walk (hS₃_sub hi) (hS₃_sub hj) hij).getVert h ≠
        (walk (hS₃_sub hi) (hS₃_sub hk) hik).getVert h := by
    intro i j k hi hj hk hij hik hjk h hh_lt hpat
    have hh_lt_all : h < 2 * d + 1 :=
      lt_of_lt_of_le hh_lt hStep2.commonLength_le
    have hpat_col : patternCol i ⟨h, hh_lt_all⟩ = false := by
      change (if h_lt : h < 2 * d + 1 then patternCol i ⟨h, h_lt⟩
              else (true : Bool)) = false at hpat
      rwa [dif_pos hh_lt_all] at hpat
    rcases Finset.mem_image.mp hj with ⟨jT, hjT, hjeq⟩
    rcases Finset.mem_image.mp hk with ⟨kT, hkT, hkeq⟩
    subst hjeq
    subst hkeq
    have hj_ne_k : jT ≠ kT := by
      intro heq; apply hjk; exact congrArg Subtype.val heq
    have hbit : rawBit jT kT i ⟨h, hh_lt_all⟩ = patternCol i ⟨h, hh_lt_all⟩ := by
      rw [colour_eq hjT hkT hj_ne_k]
    rw [hpat_col] at hbit
    have hi_S₂ : i ∈ S₂ := hS₃_sub hi
    have hi_ne_j : i ≠ jT.val := hij
    have hi_ne_k : i ≠ kT.val := hik
    simp only [rawBit] at hbit
    rw [dif_neg hi_ne_j, dif_neg hi_ne_k, dif_pos hi_S₂] at hbit
    exact of_decide_eq_false hbit
  -- Package the data.
  refine
    { toUniformLengthData :=
        { toCandidatePathData := hStep2.toCandidatePathData
          subclique := S₃
          subclique_card_ge := hS₃_card
          commonLength := hStep2.commonLength
          commonLength_le := hStep2.commonLength_le
          hasCommonLengthWalk := fun hi hj hij =>
            hStep2.hasCommonLengthWalk (hS₃_sub hi) (hS₃_sub hj) hij }
      canonicalWalk := fun hi hj hij => walk (hS₃_sub hi) (hS₃_sub hj) hij
      canonicalWalk_length := fun hi hj hij =>
        walk_length (hS₃_sub hi) (hS₃_sub hj) hij
      patternShared := patternShared
      patternShared_shared := @shared_spec
      patternShared_disjoint := @disjoint_spec }

/-- Backward direction, Step 4: cut the shared prefixes and suffixes,
perform one more Ramsey round on interior collisions, and produce the
system of internally disjoint trimmed walks required by Step 5.

Currently an open scaffold leaf; see `cor6a-plan.md` for the proof
plan. The design of `TrimmedPathData` above
matches what `backward_step5_build_subdivision` needs to assemble an
`IsContained` witness: uniform-length walks between branch-set-anchored
centres, pairwise interior-disjoint, each a path. -/
private noncomputable def backward_step4_trim_paths
    {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    {d t m : ℕ}
    (hStep3 : CanonicalPatternData G d t m) :
    TrimmedPathData G d t m := by
  sorry

/-- Backward direction, Step 5: package the cleaned path system as a
subdivided-clique subgraph. -/
private noncomputable def backward_step5_build_subdivision
    {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    {d t m : ℕ}
    (hStep4 : TrimmedPathData G d t m) :
    CleanSubdivisionData G d t m := by
  sorry

/-- Backward direction, Step 6: choose a Ramsey threshold `t(d)` and a
subdivision-order target `m` so that any cleaned Step-5 subdivision witness
of order `≥ m` contradicts the local nowhere-dense hypothesis. The
`hThresh` field feeds Step 2's multicolour-Ramsey threshold; `hThresh3`
similarly feeds Step 3's branching-pattern Ramsey. This is where the
six-step scaffold collapses back to the shallow-minor bound
`HasShallowCliqueBound C d t(d)`. -/
private theorem backward_step6_extract_bound
    (C : GraphClass)
    (hLoc : IsLocallyNowhereDense C)
    (d : ℕ) :
    ∃ (t m : ℕ),
      (Ramsey.multicolor_ramsey
          (List.replicate (2 * d + 2) m)
          List.replicate_succ_ne_nil).choose ≤ t + 1 ∧
      (Ramsey.multicolor_ramsey
          (List.replicate
            (Fintype.card (Fin (t + 1) → Fin (2 * d + 1) → Bool)) m)
          (step3_sizes_ne_nil d t m)).choose ≤ m ∧
      ∀ {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V},
        C G → CleanSubdivisionData G d t m → False := by
  sorry

/-- Local subdivided-clique nowhere denseness implies the shallow-minor
formulation. The Ramsey bookkeeping is split into the six helper steps
above. -/
private theorem isNowhereDense_of_isLocallyNowhereDense
    (C : GraphClass)
    (hLoc : IsLocallyNowhereDense C) :
    IsNowhereDense C := by
  intro d
  rcases backward_step6_extract_bound C hLoc d with
    ⟨t, m, hThresh, hThresh3, hStep6⟩
  refine ⟨t, ?_⟩
  intro V _ _ G hCG hMinor
  let step1 : CandidatePathData G d t := backward_step1_candidate_paths hMinor
  let step2 : UniformLengthData G d t m :=
    backward_step2_uniform_length step1 hThresh
  let step3 : CanonicalPatternData G d t m :=
    backward_step3_canonical_pattern step2 hThresh3
  let step4 : TrimmedPathData G d t m := backward_step4_trim_paths step3
  let step5 : CleanSubdivisionData G d t m :=
    backward_step5_build_subdivision step4
  exact hStep6 hCG step5

/-- Folklore equivalence between the local and shallow-minor
formulations of nowhere-denseness. -/
theorem isLocallyNowhereDense_iff_isNowhereDense (C : GraphClass) :
    IsLocallyNowhereDense C ↔
      IsNowhereDense C := by
  constructor
  · exact isNowhereDense_of_isLocallyNowhereDense C
  · exact isLocallyNowhereDense_of_isNowhereDense C


end Lax5Proofs.NowhereDenseBridge
