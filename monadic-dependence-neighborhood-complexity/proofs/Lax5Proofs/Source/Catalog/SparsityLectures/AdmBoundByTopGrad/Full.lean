import Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowTopologicalMinor.Full
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Ring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

open Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers
open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowTopologicalMinor
open Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility
open Classical

namespace Lax5Proofs.Source.Catalog.SparsityLectures.AdmBoundByTopGrad

noncomputable section

/-! ## Subset admissibility

A family of paths from `v` into a subset `S`, with internal vertices outside
`S`, pairwise vertex-disjoint except at `v`. This is the source proof's local
quantity `b_r(S, v)`. -/

private structure IsSubsetAdmFamily {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (S : Set V) (v : V)
    {ι : Type} (paths : ι → (u : V) × G.Walk v u) : Prop where
  target_mem : ∀ i, (paths i).1 ∈ S
  target_ne : ∀ i, (paths i).1 ≠ v
  isPath : ∀ i, (paths i).2.IsPath
  length_le : ∀ i, (paths i).2.length ≤ r
  internal_avoids :
    ∀ i, ∀ j : ℕ, 0 < j → j < (paths i).2.length → (paths i).2.getVert j ∉ S
  disjoint : ∀ i j, i ≠ j →
    ∀ w, w ∈ (paths i).2.support → w ∈ (paths j).2.support → w = v

private noncomputable def subsetAdmValue {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (S : Set V) (v : V) : ℕ :=
  Finset.sup (Finset.range (Fintype.card V)) (fun k =>
    if ∃ (paths : Fin k → (u : V) × G.Walk v u), IsSubsetAdmFamily G r S v paths
    then k else 0)

/-! ## List-based linear order construction -/

private theorem idxOf_injective_of_nodup_of_mem_all {V : Type} [DecidableEq V] {l : List V}
    (hNodup : l.Nodup) (hall : ∀ v : V, v ∈ l) :
    Function.Injective fun v => l.idxOf v := by
  let e := hNodup.getEquivOfForallMemList l hall
  intro a b hab
  apply e.symm.injective
  apply Fin.ext
  simpa [e, List.Nodup.getEquivOfForallMemList] using hab

private abbrev listIndexOrder {V : Type} [DecidableEq V] {l : List V}
    (hNodup : l.Nodup) (hall : ∀ v : V, v ∈ l) : LinearOrder V :=
  LinearOrder.lift' (fun v => l.idxOf v) (idxOf_injective_of_nodup_of_mem_all hNodup hall)

/-! ## Trimming: admVertex ≤ 1 + subsetAdmValue

Key lemma: given a split of `V` into `(list for S \ {x}) ++ [x] ++ (rest)`, the
admissibility of `x` under the list-index order is at most
`1 + subsetAdmValue G r S x`.

Proof idea: any admissible family at `x` (paths to vertices below `x`) can be
trimmed to a subset-admissible family by stopping each path at the first vertex
in `S \ {x}`. -/

private theorem admVertex_le_one_add_subsetAdmValue_of_splitOrder
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (s : Finset V) (x : V) (l m : List V)
    (hl : ∀ v, v ∈ l ↔ v ∈ s.erase x)
    (hLnodup : (l ++ x :: m).Nodup)
    (hall : ∀ v : V, v ∈ l ++ x :: m) :
    let _ : LinearOrder V := listIndexOrder hLnodup hall
    let _ : LinearOrder V := listIndexOrder hLnodup hall
    admVertex G r x ≤ 1 + subsetAdmValue G r (s : Set V) x := by
  letI : LinearOrder V := listIndexOrder hLnodup hall
  change admVertex G r x ≤ 1 + subsetAdmValue G r (↑s) x
  unfold admVertex subsetAdmValue
  -- It suffices to show: sup of adm-family sizes ≤ sup of subset-adm-family sizes
  suffices hAB :
      (Finset.range (Fintype.card V)).sup
          (fun k =>
            if ∃ paths : Fin k → (u : V) × G.Walk x u, IsAdmFamily G r x paths then k else 0) ≤
        (Finset.range (Fintype.card V)).sup
          (fun k =>
            if ∃ paths : Fin k → (u : V) × G.Walk x u,
                IsSubsetAdmFamily G r (↑s) x paths then k else 0) by
    simpa [Nat.add_comm] using Nat.succ_le_succ hAB
  apply Finset.sup_le
  intro k hk
  split_ifs with hkAdm
  · rcases hkAdm with ⟨paths, hpaths⟩
    have hx_not_mem_l : x ∉ l := by
      intro hx_in
      have : x ∈ s.erase x := (hl x).1 hx_in
      simp at this
    -- Vertices below x in the ordering are exactly l = s.erase x
    have htarget : ∀ i, (paths i).1 ∈ s.erase x := by
      intro i
      have hidx : (l ++ x :: m).idxOf (paths i).1 < (l ++ x :: m).idxOf x := by
        change (paths i).1 < x
        simpa [listIndexOrder] using hpaths.target_lt i
      have hidxx : (l ++ x :: m).idxOf x = l.length := by
        rw [List.idxOf_append_of_notMem hx_not_mem_l]
        simp
      have hmeml : (paths i).1 ∈ l := by
        have hp : l <+: l ++ x :: m := l.prefix_append (x :: m)
        exact (hp.mem_iff_idxOf_lt_length (paths i).1).2 (hidxx ▸ hidx)
      exact (hl _).1 hmeml
    -- For each path, find the first vertex in s \ {x} and trim there
    have hConvert : ∀ i : Fin k,
        ∃ (y : V) (q : G.Walk x y),
          y ∈ (s : Set V) ∧ y ≠ x ∧ q.IsPath ∧ q.length ≤ r ∧
          (∀ idx, 0 < idx → idx < q.length → q.getVert idx ∉ (s : Set V)) ∧
          (∀ w, w ∈ q.support → w ∈ (paths i).2.support) := by
      intro i
      let p := (paths i).2
      -- The walk goes from x to (paths i).1 ∈ s.erase x
      -- Find smallest j > 0 with p.getVert j ∈ s.erase x
      have hlen_pos : 0 < p.length := by
        rcases Nat.eq_zero_or_pos p.length with h0 | hpos
        · exfalso
          have : (paths i).1 = x := by
            have := p.getVert_length
            rw [h0, SimpleGraph.Walk.getVert_zero] at this
            exact this.symm
          exact (Finset.mem_erase.mp (htarget i)).1 this
        · exact hpos
      have hEndMem : p.getVert p.length ∈ s.erase x := by
        rw [p.getVert_length]; exact htarget i
      -- Predicate: j > 0 ∧ j ≤ p.length ∧ p.getVert j ∈ s.erase x
      let P := fun j => 0 < j ∧ j ≤ p.length ∧ p.getVert j ∈ s.erase x
      have hPex : ∃ j, P j := ⟨p.length, hlen_pos, le_refl _, hEndMem⟩
      let j := Nat.find hPex
      have hj : P j := Nat.find_spec hPex
      have hjmin : ∀ j' < j, ¬P j' := fun j' hlt => Nat.find_min hPex hlt
      -- The trimmed walk is p.take j
      refine ⟨p.getVert j, p.take j, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (Finset.mem_erase.mp hj.2.2).2
      · exact (Finset.mem_erase.mp hj.2.2).1
      · exact (hpaths.isPath i).take j
      · calc (p.take j).length = min j p.length := p.take_length j
          _ ≤ p.length := min_le_right _ _
          _ ≤ r := hpaths.length_le i
      · -- Internal vertices avoid s
        intro idx hidx0 hidxlen
        have hidxj : idx < j := by
          rw [p.take_length] at hidxlen
          exact lt_of_lt_of_le hidxlen (min_le_left _ _)
        have hgetVert : (p.take j).getVert idx = p.getVert idx := by
          rw [p.take_getVert]
          congr 1
          exact min_eq_right (le_of_lt hidxj)
        rw [hgetVert]
        intro hmem
        have hidxle : idx ≤ p.length := le_trans (le_of_lt hidxj) hj.2.1
        -- p.getVert idx ∈ s and idx > 0, so p.getVert idx ∈ s.erase x
        -- (since path is injective, getVert idx ≠ getVert 0 = x)
        have hne_x : p.getVert idx ≠ x := by
          intro heq
          have := (hpaths.isPath i).getVert_injOn
            (show idx ∈ {i | i ≤ p.length} from hidxle)
            (show 0 ∈ {i | i ≤ p.length} from Nat.zero_le _)
            (heq.trans p.getVert_zero.symm)
          omega
        exact hjmin idx hidxj ⟨hidx0, hidxle, Finset.mem_erase.mpr ⟨hne_x, hmem⟩⟩
      · -- Support subset
        intro w hw
        have hsub := p.take_support_eq_support_take_succ j
        rw [hsub] at hw
        exact List.take_subset _ _ hw
    -- Build the converted family
    choose y q hy hne hpath hlen hint hsub using hConvert
    have hsubset : ∃ newPaths : Fin k → (u : V) × G.Walk x u,
        IsSubsetAdmFamily G r (↑s) x newPaths := by
      refine ⟨fun i => ⟨y i, q i⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i; exact hy i
      · intro i; exact hne i
      · intro i; exact hpath i
      · intro i; exact hlen i
      · intro i; exact hint i
      · intro i₁ i₂ hi w hw1 hw2
        exact hpaths.disjoint i₁ i₂ hi w (hsub i₁ w hw1) (hsub i₂ w hw2)
    have hkval :
        (if ∃ paths : Fin k → (u : V) × G.Walk x u,
            IsSubsetAdmFamily G r (↑s) x paths then k else 0) = k := by
      simp [hsubset]
    calc
      k = (if ∃ paths : Fin k → (u : V) × G.Walk x u,
          IsSubsetAdmFamily G r (↑s) x paths then k else 0) := hkval.symm
      _ ≤ (Finset.range (Fintype.card V)).sup
            (fun k =>
              if ∃ paths : Fin k → (u : V) × G.Walk x u,
                  IsSubsetAdmFamily G r (↑s) x paths then k else 0) :=
        Finset.le_sup (f := fun k =>
              if ∃ paths : Fin k → (u : V) × G.Walk x u,
                  IsSubsetAdmFamily G r (↑s) x paths then k else 0) hk
  · simp

/-! ## Greedy peeling (Phase A)

Build a `LinearOrder V` with bounded admissibility by repeatedly peeling the
vertex with minimum `subsetAdmValue` from the remaining set. -/

private structure PrefixData {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (B : ℕ) (s : Finset V)
    (m : List V) (hmNodup : m.Nodup) (hmMem : ∀ v : V, v ∈ m ↔ v ∉ s) where
  list : List V
  nodup : list.Nodup
  mem_iff : ∀ v, v ∈ list ↔ v ∈ s
  bound :
    ∀ (hLnodup : (list ++ m).Nodup) (hall : ∀ v : V, v ∈ list ++ m),
      let _ : LinearOrder V := listIndexOrder hLnodup hall
      ∀ v ∈ s, admVertex G r v ≤ 1 + B

private noncomputable def choosePeelVertex {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r : ℕ) {B : ℕ}
    (hBound :
      ∀ S : Set V, S.Nonempty →
        ∃ v ∈ S, subsetAdmValue G r S v ≤ B)
    (s : Finset V) (hs : s.Nonempty) :
    {x // x ∈ s ∧ subsetAdmValue G r (s : Set V) x ≤ B} := by
  let hx := hBound (s : Set V) ⟨hs.choose, by simpa using hs.choose_spec⟩
  let x : V := Classical.choose hx
  have hx_mem : x ∈ (s : Set V) := (Classical.choose_spec hx).1
  have hxB : subsetAdmValue G r (s : Set V) x ≤ B := (Classical.choose_spec hx).2
  exact ⟨x, by simpa using hx_mem, hxB⟩

private theorem listIndexOrder_eq_of_eqList {V : Type} [DecidableEq V] {l l' : List V}
    (h : l = l') (hNodup : l.Nodup) (hall : ∀ v : V, v ∈ l)
    (hNodup' : l'.Nodup) (hall' : ∀ v : V, v ∈ l') :
    @listIndexOrder V _ l hNodup hall = @listIndexOrder V _ l' hNodup' hall' := by
  subst h
  cases Subsingleton.elim hNodup hNodup'
  cases Subsingleton.elim hall hall'
  rfl

private noncomputable def buildPrefixData {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r : ℕ) {B : ℕ}
    (hBound :
      ∀ S : Set V, S.Nonempty →
        ∃ v ∈ S, subsetAdmValue G r S v ≤ B)
    (s : Finset V) (m : List V) (hmNodup : m.Nodup) (hmMem : ∀ v : V, v ∈ m ↔ v ∉ s) :
    PrefixData G r B s m hmNodup hmMem := by
  by_cases hs : s.Nonempty
  · let choice := choosePeelVertex G r hBound s hs
    let x := choice.1
    have hx : x ∈ s := choice.2.1
    have hxB : subsetAdmValue G r (s : Set V) x ≤ B := choice.2.2
    have hxm : x ∉ m := by
      intro hxm
      exact ((hmMem x).1 hxm) hx
    have hmConsNodup : (x :: m).Nodup := by
      simp [hxm, hmNodup]
    have hmConsMem : ∀ v : V, v ∈ x :: m ↔ v ∉ s.erase x := by
      intro v
      by_cases hvx : v = x
      · subst hvx
        simp [hx]
      · simp [hmMem v, Finset.mem_erase, hvx]
    let prev :=
      buildPrefixData G r hBound (s.erase x) (x :: m) hmConsNodup hmConsMem
    refine
      { list := prev.list ++ [x]
        nodup := by
          have hx_not_mem_prev : x ∉ prev.list := by
            intro hxList
            have : x ∈ s.erase x := (prev.mem_iff x).1 hxList
            simp at this
          refine List.nodup_append.2 ⟨prev.nodup, by simp, ?_⟩
          intro a ha b hb
          simp at hb
          subst b
          exact fun hax => hx_not_mem_prev (hax ▸ ha)
        mem_iff := by
          intro v
          by_cases hvx : v = x
          · subst hvx
            simp [hx]
          · simp [prev.mem_iff, Finset.mem_erase, hvx]
        bound := by
          intro hLnodup hall
          have hsplitNodup : (prev.list ++ x :: m).Nodup := by
            simpa [List.append_assoc] using hLnodup
          have hsplitAll : ∀ w : V, w ∈ prev.list ++ x :: m := by
            simpa [List.append_assoc] using hall
          have hboundSplit :
              let _ : LinearOrder V := listIndexOrder hsplitNodup hsplitAll
              ∀ v ∈ s, admVertex G r v ≤ 1 + B := by
            letI : LinearOrder V := listIndexOrder hsplitNodup hsplitAll
            change ∀ v ∈ s, admVertex G r v ≤ 1 + B
            intro v hv
            by_cases hvx : v = x
            · subst hvx
              exact admVertex_le_one_add_subsetAdmValue_of_splitOrder
                G r s x prev.list m prev.mem_iff hsplitNodup hsplitAll
                |>.trans (Nat.add_le_add_left hxB 1)
            · have hvt : v ∈ s.erase x := by
                simpa [Finset.mem_erase, hvx] using hv
              exact prev.bound hsplitNodup hsplitAll v hvt
          have hOrderEq :
              listIndexOrder hsplitNodup hsplitAll = listIndexOrder hLnodup hall := by
            apply listIndexOrder_eq_of_eqList (h := by simp [List.append_assoc])
          rw [← hOrderEq]
          exact hboundSplit }
  · refine
      { list := []
        nodup := by simp
        mem_iff := by
          intro v
          simp [Finset.not_nonempty_iff_eq_empty.mp hs]
        bound := by
          intro hLnodup hall
          letI : LinearOrder V := listIndexOrder hLnodup hall
          change ∀ v ∈ s, admVertex G r v ≤ 1 + B
          intro v hv
          simp [Finset.not_nonempty_iff_eq_empty.mp hs] at hv }
termination_by s.card
decreasing_by
  simpa using
    Finset.card_erase_lt_of_mem ((choosePeelVertex G r hBound s hs).2.1)

private theorem exists_order_adm_le_of_subsetAdmBound
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r : ℕ) {B : ℕ}
    (hBound :
      ∀ S : Set V, S.Nonempty →
        ∃ v ∈ S, subsetAdmValue G r S v ≤ B) :
    ∃ ord : LinearOrder V,
      letI := ord; adm G r ≤ 1 + B := by
  let data := buildPrefixData G r hBound Finset.univ [] (by simp) (by intro v; simp)
  let hLnodup : (data.list ++ []).Nodup := by
    simpa using data.nodup
  let hall : ∀ v : V, v ∈ data.list ++ [] := by
    intro v
    simpa using (data.mem_iff v).2 (by simp)
  refine ⟨listIndexOrder hLnodup hall, ?_⟩
  letI : LinearOrder V := listIndexOrder hLnodup hall
  change adm G r ≤ 1 + B
  rw [adm]
  have hboundAll : ∀ v ∈ (Finset.univ : Finset V), admVertex G r v ≤ 1 + B := by
    simpa using data.bound hLnodup hall
  by_cases huniv : (Finset.univ : Finset V).Nonempty
  · obtain ⟨v, hv, hsup⟩ := Finset.exists_mem_eq_sup Finset.univ huniv (fun w => admVertex G r w)
    simpa [hsup] using hboundAll v hv
  · simp [Finset.not_nonempty_iff_eq_empty.mp huniv]

/-! ## Phase B: every nonempty subset has a vertex with bounded subsetAdmValue

If all depth-`(r-1)` topological minors have edge density at most `d`, then for
every nonempty `S ⊆ V`, there exists `v ∈ S` with
`subsetAdmValue G r S v ≤ 6 * r * d ^ 3`.

Proof (from source): if all `b_r(S, v) > ℓ = 6rd³`, build a maximal matching
of paths between pairs of `S`, extract an independent set from the resulting
graph, trim path families, assemble a topological minor that is too dense,
contradicting the density hypothesis. -/

/-! ### Helper: subsetAdmValue = 0 when r = 0 -/

private theorem subsetAdmValue_eq_zero_of_r_eq_zero
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (S : Set V) (v : V) :
    subsetAdmValue G 0 S v = 0 := by
  unfold subsetAdmValue
  apply le_antisymm _ (Nat.zero_le _)
  apply Finset.sup_le
  intro k _
  split_ifs with h
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact le_refl _
    · exfalso
      obtain ⟨paths, hpaths⟩ := h
      let i : Fin k := ⟨0, hk⟩
      have hlen : (paths i).2.length = 0 := Nat.le_zero.mp (hpaths.length_le i)
      have heq : (paths i).1 = v := by
        have h1 := (paths i).2.getVert_length
        rw [hlen, SimpleGraph.Walk.getVert_zero] at h1
        exact h1.symm
      exact hpaths.target_ne i heq
  · exact le_refl _

/-! ### Helper: independent set from edge bound

A graph with at most d·|V| edges has an independent set I with
|V| ≤ |I|·(2d+1). Standard degeneracy/coloring argument. -/

private theorem exists_indepset_of_edge_bound
    {W : Type} [DecidableEq W] [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (d : ℕ)
    (hEdge : H.edgeFinset.card ≤ d * Fintype.card W) :
    ∃ I : Finset W, (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬H.Adj u v) ∧
      Fintype.card W ≤ I.card * (2 * d + 1) := by
  set n := Fintype.card W with hn_def
  by_cases hn : n = 0
  · -- W is empty
    haveI : IsEmpty W := Fintype.card_eq_zero_iff.mp hn
    exact ⟨∅, fun u hu => absurd hu (by simp), by simp [hn]⟩
  · -- W is nonempty
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    haveI : Nonempty W := Fintype.card_pos_iff.mp hn_pos
    set α := H.indepNum
    -- α ≥ 1 (any singleton is independent)
    have hα_pos : 1 ≤ α := by
      have v : W := Classical.choice inferInstance
      have : H.IsIndepSet (↑({v} : Finset W)) := by
        rw [SimpleGraph.isIndepSet_iff]
        intro a ha b hb hab
        simp at ha hb; exact absurd (hb ▸ ha) hab
      simpa using this.card_le_indepNum
    -- Hᶜ is CliqueFree (α + 1)
    have hCF : Hᶜ.CliqueFree (α + 1) := by
      intro s hs
      have hIndep : H.IsIndepSet ↑s := (SimpleGraph.isClique_compl H).mp hs.isClique
      have h1 : s.card ≤ α := hIndep.card_le_indepNum
      have h2 : s.card = α + 1 := hs.card_eq
      omega
    -- Turán bound on complement: 2α·|E(Hᶜ)| ≤ (α-1)·n²
    have hTuran : 2 * α * Hᶜ.edgeFinset.card ≤ (α - 1) * n ^ 2 := by
      calc 2 * α * Hᶜ.edgeFinset.card
          ≤ 2 * α * (SimpleGraph.turanGraph n α).edgeFinset.card := by
            apply Nat.mul_le_mul_left
            rw [SimpleGraph.card_edgeFinset_turanGraph]
            exact hCF.card_edgeFinset_le
        _ ≤ (α - 1) * n ^ 2 :=
            SimpleGraph.mul_card_edgeFinset_turanGraph_le
    -- Edge partition: |E(H)| + |E(Hᶜ)| = C(n,2)
    have hSub : H.edgeFinset ⊆ (⊤ : SimpleGraph W).edgeFinset :=
      SimpleGraph.edgeFinset_mono le_top
    have hCompl : Hᶜ.edgeFinset = (⊤ : SimpleGraph W).edgeFinset \ H.edgeFinset := by
      ext e; refine Sym2.ind ?_ e; intro u v
      simp only [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj, SimpleGraph.top_adj]
    have hPartition : H.edgeFinset.card + Hᶜ.edgeFinset.card = n.choose 2 := by
      have h1 := Finset.card_sdiff_add_card_eq_card hSub
      rw [← hCompl] at h1
      rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, ← hn_def] at h1
      omega
    -- Double partition: n + 2|E(H)| + 2|E(Hᶜ)| = n²
    have hDouble : n + 2 * H.edgeFinset.card + 2 * Hᶜ.edgeFinset.card = n ^ 2 := by
      rw [Nat.add_assoc,
        show 2 * H.edgeFinset.card + 2 * Hᶜ.edgeFinset.card =
          2 * (H.edgeFinset.card + Hᶜ.edgeFinset.card) from by ring,
        hPartition, Nat.choose_two_right,
        Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
      rcases n with _ | m; · exact absurd rfl hn
      simp; ring
    -- Key: n² ≤ α·n·(2d+1)
    -- Step 1: (α-1)·n² + n² = α·n²
    have hαn : (α - 1) * n ^ 2 + n ^ 2 = α * n ^ 2 := by
      rcases α with _ | a; · omega
      simp; ring
    -- Step 2: n² + 2α|E(Hᶜ)| ≤ α·n² (from Turán)
    have h1 : n ^ 2 + 2 * α * Hᶜ.edgeFinset.card ≤ α * n ^ 2 :=
      calc n ^ 2 + 2 * α * Hᶜ.edgeFinset.card
          ≤ n ^ 2 + (α - 1) * n ^ 2 := Nat.add_le_add_left hTuran _
        _ = (α - 1) * n ^ 2 + n ^ 2 := Nat.add_comm ..
        _ = α * n ^ 2 := hαn
    -- Step 3: α·n² = α·n + 2α|E(H)| + 2α|E(Hᶜ)| (from hDouble × α)
    have hαDouble : α * n + 2 * α * H.edgeFinset.card +
        2 * α * Hᶜ.edgeFinset.card = α * n ^ 2 := by
      calc α * n + 2 * α * H.edgeFinset.card + 2 * α * Hᶜ.edgeFinset.card
          = α * (n + 2 * H.edgeFinset.card + 2 * Hᶜ.edgeFinset.card) := by ring
        _ = α * n ^ 2 := by rw [hDouble]
    -- Step 4: n² ≤ α·n + 2α|E(H)|
    have h3 : n ^ 2 ≤ α * n + 2 * α * H.edgeFinset.card :=
      Nat.le_of_add_le_add_right (hαDouble ▸ h1)
    -- Step 5: n² ≤ α·n·(2d+1)
    have hKey : n * n ≤ α * n * (2 * d + 1) := by
      calc n * n = n ^ 2 := by ring
        _ ≤ α * n + 2 * α * H.edgeFinset.card := h3
        _ ≤ α * n + 2 * α * (d * n) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hEdge) _
        _ = α * n * (2 * d + 1) := by ring
    have hKey' : n * n ≤ α * (2 * d + 1) * n := by
      calc n * n ≤ α * n * (2 * d + 1) := hKey
        _ = α * (2 * d + 1) * n := by ring
    have hFinal : n ≤ α * (2 * d + 1) := Nat.le_of_mul_le_mul_right hKey' hn_pos
    -- Extract the concrete independent set
    obtain ⟨I, hI⟩ := SimpleGraph.exists_isNIndepSet_indepNum (G := H)
    refine ⟨I, ?_, ?_⟩
    · intro u hu v hv huv
      exact (SimpleGraph.isIndepSet_iff H).mp hI.isIndepSet hu hv huv
    · rw [hI.card_eq]; exact hFinal

/-! ### Raw connector infrastructure

A `RawConnector` is a graph H on S together with a topological minor model
witnessing H ≼^top_{r-1} G, where branch vertices are the identity on S.
The maximal connector is built by iterating: start with the empty graph and
greedily add edges until no more short paths exist. -/

private structure RawConnector {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (S : Set V) [Fintype S] where
  H : SimpleGraph S
  model : ShallowTopologicalMinorModel H G (r - 1)
  branch_vertex : ∀ w : S, model.branchVertex w = w.1

private def rawConnectorInternalFinset
    {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {r : ℕ} {S : Set V} [Fintype S]
    (M : RawConnector G r S) (e : M.H.edgeSet) : Finset V :=
  (((M.model.edgePath e).support.toFinset).erase
    (M.model.branchVertex (M.model.edgeTail e))).erase
    (M.model.branchVertex (Sym2.Mem.other (M.model.edgeTail_mem e)))

private def rawConnectorK
    {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {r : ℕ} {S : Set V} [Fintype S]
    (M : RawConnector G r S) : Finset V :=
  Finset.univ.biUnion (rawConnectorInternalFinset M)

private def emptyRawConnector
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (S : Set V) [Fintype S] :
    RawConnector G r S where
  H := ⊥
  model :=
    { branchVertex := ⟨Subtype.val, fun _ _ h => Subtype.ext h⟩
      edgeTail := fun e => absurd e.2 (by simp)
      edgeTail_mem := fun e => absurd e.2 (by simp)
      edgePath := fun e => absurd e.2 (by simp)
      edgePath_isPath := fun e => absurd e.2 (by simp)
      edgePath_length := fun e => absurd e.2 (by simp)
      edgePath_interior_avoids_branch := fun e _ _ _ _ _ => absurd e.2 (by simp)
      edgePath_interior_disjoint := fun e _ _ _ _ _ _ _ _ => absurd e.2 (by simp) }
  branch_vertex := fun _ => rfl

private theorem rawConnectorInternalFinset_card_bound
    {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {r : ℕ} {S : Set V} [Fintype S]
    (M : RawConnector G r S) (e : M.H.edgeSet) :
    (rawConnectorInternalFinset M e).card ≤ 2 * r - 2 := by
  let p := M.model.edgePath e
  let tail := M.model.branchVertex (M.model.edgeTail e)
  let head := M.model.branchVertex (Sym2.Mem.other (M.model.edgeTail_mem e))
  have hpPath : p.IsPath := M.model.edgePath_isPath e
  have htail_mem : tail ∈ p.support.toFinset := by
    simpa [p, tail] using p.getVert_mem_support 0
  have hhead_mem : head ∈ p.support.toFinset := by
    simpa [p, head] using p.getVert_mem_support p.length
  have htail_ne_head : tail ≠ head := by
    intro hEq
    exact M.H.edge_other_ne e.property (M.model.edgeTail_mem e)
      (M.model.branchVertex.injective hEq.symm)
  have hhead_mem_erase : head ∈ p.support.toFinset.erase tail :=
    Finset.mem_erase.mpr ⟨htail_ne_head.symm, hhead_mem⟩
  have hcard_support : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hpPath.support_nodup,
      SimpleGraph.Walk.length_support]
  have hcard_internal : (rawConnectorInternalFinset M e).card = p.length - 1 := by
    have h1 : (p.support.toFinset.erase tail).card = p.length := by
      rw [Finset.card_erase_of_mem htail_mem, hcard_support]; omega
    have h2 : ((p.support.toFinset.erase tail).erase head).card = p.length - 1 := by
      rw [Finset.card_erase_of_mem hhead_mem_erase, h1]
    simpa [rawConnectorInternalFinset, p, tail, head] using h2
  rw [hcard_internal]
  have : p.length ≤ 2 * (r - 1) + 1 := by simpa [p] using M.model.edgePath_length e
  omega

private theorem rawConnectorK_card_bound
    {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {r : ℕ} {S : Set V} [Fintype S]
    (M : RawConnector G r S) :
    (rawConnectorK M).card ≤ M.H.edgeFinset.card * (2 * r - 2) := by
  calc (rawConnectorK M).card
      ≤ (Finset.univ : Finset M.H.edgeSet).card * (2 * r - 2) := by
        simpa [rawConnectorK] using
          Finset.card_biUnion_le_card_mul Finset.univ (rawConnectorInternalFinset M)
            (2 * r - 2) (fun e _ => rawConnectorInternalFinset_card_bound M e)
    _ = M.H.edgeFinset.card * (2 * r - 2) := by
        rw [SimpleGraph.edgeSet_univ_card]

private theorem rawConnector_internal_mem_K
    {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {r : ℕ} {S : Set V} [Fintype S]
    (M : RawConnector G r S) (e : M.H.edgeSet) (i : ℕ)
    (hi0 : 0 < i) (hil : i < (M.model.edgePath e).length) :
    (M.model.edgePath e).getVert i ∈ rawConnectorK M := by
  let p := M.model.edgePath e
  have hpPath : p.IsPath := M.model.edgePath_isPath e
  have hil' : i < p.length := hil
  have hne_tail : p.getVert i ≠ M.model.branchVertex (M.model.edgeTail e) := by
    intro hEq
    have : i = 0 := (hpPath.getVert_eq_start_iff hil'.le).mp (by simpa [p] using hEq)
    omega
  have hne_head : p.getVert i ≠
      M.model.branchVertex (Sym2.Mem.other (M.model.edgeTail_mem e)) := by
    intro hEq
    have : i = p.length := (hpPath.getVert_eq_end_iff hil'.le).mp (by simpa [p] using hEq)
    omega
  exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _,
    Finset.mem_erase.mpr ⟨hne_head, Finset.mem_erase.mpr
      ⟨hne_tail, by simpa using p.getVert_mem_support i⟩⟩⟩

private theorem rawConnector_mem_K_of_support
    {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {r : ℕ} {S : Set V} [Fintype S]
    (M : RawConnector G r S) (e : M.H.edgeSet) {x : V}
    (hx : x ∈ (M.model.edgePath e).support)
    (htail : x ≠ M.model.branchVertex (M.model.edgeTail e))
    (hhead : x ≠ M.model.branchVertex (Sym2.Mem.other (M.model.edgeTail_mem e))) :
    x ∈ rawConnectorK M := by
  let p := M.model.edgePath e
  have hpPath : p.IsPath := M.model.edgePath_isPath e
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx with ⟨i, rfl, hi_le⟩
  have hi0 : 0 < i := by
    by_contra hi0
    exact htail (by simp_all [p, Nat.eq_zero_of_not_pos hi0])
  have hil : i < p.length := by
    by_contra hil
    exact hhead (by simp_all [p, le_antisymm hi_le (Nat.not_lt.mp hil)])
  simpa [p] using rawConnector_internal_mem_K M e i hi0 hil

private theorem exists_extend_rawConnector
    {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {r : ℕ} {S : Set V} [Fintype S]
    (M : RawConnector G r S)
    {u v : S} (huv : u ≠ v) (hAdj : ¬ M.H.Adj u v)
    (p : G.Walk u.1 v.1) (hpPath : p.IsPath) (hpLen : p.length ≤ 2 * r - 1)
    (hpAvoid : ∀ i : ℕ, 0 < i → i < p.length →
      p.getVert i ∉ (S ∪ (rawConnectorK M : Set V))) :
    ∃ M' : RawConnector G r S,
      M'.H.edgeFinset.card = M.H.edgeFinset.card + 1 := by
  let H' : SimpleGraph S := M.H ⊔ SimpleGraph.edge u v
  have mem_S_of_eq_branch (w : S) {x : V} (hEq : x = M.model.branchVertex w) : x ∈ S := by
    rw [M.branch_vertex w] at hEq; exact hEq.symm ▸ w.2
  have hpInternalAvoid :
      ∀ {x : V}, x ∈ p.support →
        x ≠ M.model.branchVertex u →
        x ≠ M.model.branchVertex v →
        x ∉ (S ∪ (rawConnectorK M : Set V)) := by
    intro x hx hxu hxv
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx with ⟨i, rfl, hi_le⟩
    have hi0 : 0 < i := by
      by_contra hi0
      exact hxu (by simp_all [M.branch_vertex u, Nat.eq_zero_of_not_pos hi0])
    have hil : i < p.length := by
      by_contra hil
      exact hxv (by simp_all [M.branch_vertex v, le_antisymm hi_le (Nat.not_lt.mp hil)])
    exact hpAvoid i hi0 hil
  -- Define edge tail for H'
  let edgeTail' : H'.edgeSet → S := fun e =>
    if hOld : (e : Sym2 S) ∈ M.H.edgeSet then M.model.edgeTail ⟨e, hOld⟩
    else e.1.out.1
  have edgeTail_mem' : ∀ e : H'.edgeSet, edgeTail' e ∈ (e : Sym2 S) := by
    intro e
    by_cases hOld : (e : Sym2 S) ∈ M.H.edgeSet
    · simpa [edgeTail', hOld] using M.model.edgeTail_mem ⟨e, hOld⟩
    · simpa [edgeTail', hOld] using Sym2.out_fst_mem (e : Sym2 S)
  -- For new edges, classify tail/head
  have hnew_edge :
      ∀ e : H'.edgeSet, ¬ (e : Sym2 S) ∈ M.H.edgeSet →
        (e : Sym2 S) = s(u, v) ∧
          ((edgeTail' e = u ∧ Sym2.Mem.other (edgeTail_mem' e) = v) ∨
            (edgeTail' e = v ∧ Sym2.Mem.other (edgeTail_mem' e) = u)) := by
    intro e hOld
    have he_new : (e : Sym2 S) ∈ (SimpleGraph.edge u v).edgeSet := by
      have : (e : Sym2 S) ∈ M.H.edgeSet ∪ (SimpleGraph.edge u v).edgeSet := by
        simpa [H'] using e.property
      exact this.resolve_left hOld
    have he_uv : (e : Sym2 S) = s(u, v) := by
      simpa [SimpleGraph.edge_edgeSet_of_ne huv] using he_new
    have htail_mem_uv : edgeTail' e ∈ s(u, v) := by
      simpa [he_uv] using edgeTail_mem' e
    have htail_cases : edgeTail' e = u ∨ edgeTail' e = v := by
      simpa using htail_mem_uv
    refine ⟨he_uv, ?_⟩
    rcases htail_cases with htailu | htailv
    · left; refine ⟨htailu, ?_⟩
      have hother_mem : Sym2.Mem.other (edgeTail_mem' e) ∈ s(u, v) := by
        simpa [he_uv] using Sym2.other_mem (edgeTail_mem' e)
      have hother_ne_u : Sym2.Mem.other (edgeTail_mem' e) ≠ u := by
        simpa [htailu] using H'.edge_other_ne e.property (edgeTail_mem' e)
      exact (Sym2.mem_iff.mp hother_mem).resolve_left hother_ne_u
    · right; refine ⟨htailv, ?_⟩
      have hother_mem : Sym2.Mem.other (edgeTail_mem' e) ∈ s(u, v) := by
        simpa [he_uv] using Sym2.other_mem (edgeTail_mem' e)
      have hother_ne_v : Sym2.Mem.other (edgeTail_mem' e) ≠ v := by
        simpa [htailv] using H'.edge_other_ne e.property (edgeTail_mem' e)
      exact ((Sym2.mem_iff.mp hother_mem).resolve_right hother_ne_v)
  -- Define edge paths for H'
  let edgePath' :
      ∀ e : H'.edgeSet,
        G.Walk (M.model.branchVertex (edgeTail' e))
          (M.model.branchVertex (Sym2.Mem.other (edgeTail_mem' e))) := by
    intro e
    by_cases hOld : (e : Sym2 S) ∈ M.H.edgeSet
    · -- Old edge: copy the existing path
      let eOld : M.H.edgeSet := ⟨e, hOld⟩
      have htailEq : edgeTail' e = M.model.edgeTail eOld := by simp [edgeTail', eOld, hOld]
      have hotherEq :
          Sym2.Mem.other (M.model.edgeTail_mem eOld) =
            Sym2.Mem.other (edgeTail_mem' e) := by
        apply Sym2.congr_right.mp
        have hs2 : s(M.model.edgeTail eOld, Sym2.Mem.other (edgeTail_mem' e)) = (e : Sym2 S) :=
          (congrArg (s(·, Sym2.Mem.other (edgeTail_mem' e))) htailEq.symm).trans
            (Sym2.other_spec (edgeTail_mem' e))
        calc s(M.model.edgeTail eOld, Sym2.Mem.other (M.model.edgeTail_mem eOld))
            = (e : Sym2 S) := Sym2.other_spec (M.model.edgeTail_mem eOld)
          _ = s(M.model.edgeTail eOld, Sym2.Mem.other (edgeTail_mem' e)) := hs2.symm
      exact (M.model.edgePath eOld).copy
        (congrArg M.model.branchVertex htailEq.symm)
        (congrArg M.model.branchVertex hotherEq)
    · -- New edge: use p or p.reverse depending on tail direction
      by_cases htailu : edgeTail' e = u
      · have hotherv : Sym2.Mem.other (edgeTail_mem' e) = v := by
          obtain ⟨_, hdir | hdir⟩ := hnew_edge e hOld
          · exact hdir.2
          · exact absurd (hdir.1.symm.trans htailu) (Ne.symm huv)
        exact p.copy
          ((M.branch_vertex u).symm.trans (congrArg M.model.branchVertex htailu.symm))
          ((M.branch_vertex v).symm.trans (congrArg M.model.branchVertex hotherv.symm))
      · have htailv : edgeTail' e = v := by
          obtain ⟨_, hdir | hdir⟩ := hnew_edge e hOld
          · exact absurd hdir.1 htailu
          · exact hdir.1
        have hotheru : Sym2.Mem.other (edgeTail_mem' e) = u := by
          obtain ⟨_, hdir | hdir⟩ := hnew_edge e hOld
          · exact absurd hdir.1 htailu
          · exact hdir.2
        exact p.reverse.copy
          ((M.branch_vertex v).symm.trans (congrArg M.model.branchVertex htailv.symm))
          ((M.branch_vertex u).symm.trans (congrArg M.model.branchVertex hotheru.symm))
  -- Build the extended raw connector
  let M' : RawConnector G r S :=
    { H := H'
      model :=
        { branchVertex := M.model.branchVertex
          edgeTail := edgeTail'
          edgeTail_mem := edgeTail_mem'
          edgePath := edgePath'
          edgePath_isPath := by
            intro e
            by_cases hOld : (e : Sym2 S) ∈ M.H.edgeSet
            · simpa [edgePath', hOld] using M.model.edgePath_isPath ⟨e, hOld⟩
            · by_cases htailu : edgeTail' e = u
              · obtain ⟨_, hdir | hdir⟩ := hnew_edge e hOld
                · simpa [edgePath', hOld, htailu, hdir.2] using hpPath
                · exact absurd (hdir.1.symm.trans htailu) (Ne.symm huv)
              · obtain ⟨_, hdir | hdir⟩ := hnew_edge e hOld
                · exact absurd hdir.1 htailu
                · simpa [edgePath', hOld, htailu, hdir.1, hdir.2,
                    show v ≠ u from fun h => huv h.symm] using hpPath.reverse
          edgePath_length := by
            intro e
            have hpLen' : p.length ≤ 2 * (r - 1) + 1 := by omega
            by_cases hOld : (e : Sym2 S) ∈ M.H.edgeSet
            · simpa [edgePath', hOld] using M.model.edgePath_length ⟨e, hOld⟩
            · by_cases htailu : edgeTail' e = u
              · obtain ⟨_, hdir | hdir⟩ := hnew_edge e hOld
                · simpa [edgePath', hOld, htailu, hdir.2] using hpLen'
                · exact absurd (hdir.1.symm.trans htailu) (Ne.symm huv)
              · obtain ⟨_, hdir | hdir⟩ := hnew_edge e hOld
                · exact absurd hdir.1 htailu
                · simpa [edgePath', hOld, htailu, hdir.1, hdir.2,
                    show v ≠ u from fun h => huv h.symm] using hpLen'
          edgePath_interior_avoids_branch := by
            intro e x hx htail hhead w
            by_cases hOld : (e : Sym2 S) ∈ M.H.edgeSet
            · exact M.model.edgePath_interior_avoids_branch ⟨e, hOld⟩
                (by simpa [edgePath', hOld] using hx)
                (by simpa [edgeTail', hOld, edgeTail_mem'] using htail)
                (by simpa [edgeTail', hOld, edgeTail_mem'] using hhead)
                w
            · by_cases htailu : edgeTail' e = u
              · obtain ⟨_, hdir | hdir⟩ := hnew_edge e hOld
                · have hxP : x ∈ p.support := by
                    simpa [edgePath', hOld, htailu, hdir.2] using hx
                  have htailP : x ≠ M.model.branchVertex u := by
                    simpa [edgeTail', hOld, htailu] using htail
                  have hheadP : x ≠ M.model.branchVertex v := by
                    exact fun hEq => hhead (hEq.trans (congrArg M.model.branchVertex hdir.2.symm))
                  have hxAvoid := hpInternalAvoid hxP htailP hheadP
                  exact fun hEq => hxAvoid (Set.mem_union_left _ (mem_S_of_eq_branch w hEq))
                · exact absurd (hdir.1.symm.trans htailu) (Ne.symm huv)
              · obtain ⟨_, hdir | hdir⟩ := hnew_edge e hOld
                · exact absurd hdir.1 htailu
                · have hxP : x ∈ p.support := by
                    simpa [edgePath', hOld, htailu, hdir.1, hdir.2,
                      SimpleGraph.Walk.support_reverse,
                      show v ≠ u from fun h => huv h.symm] using hx
                  have htailP : x ≠ M.model.branchVertex v := by
                    simpa [edgeTail', hOld, hdir.1] using htail
                  have hheadP : x ≠ M.model.branchVertex u := by
                    exact fun hEq =>
                      hhead (hEq.trans (congrArg M.model.branchVertex hdir.2.symm))
                  have hxAvoid := hpInternalAvoid hxP hheadP htailP
                  exact fun hEq => hxAvoid (Set.mem_union_left _ (mem_S_of_eq_branch w hEq))
          edgePath_interior_disjoint := by
            intro e e' x hne hx hx' htail hhead htail' hhead'
            by_cases hOld : (e : Sym2 S) ∈ M.H.edgeSet
            · by_cases hOld' : (e' : Sym2 S) ∈ M.H.edgeSet
              · -- Both old edges
                have hneOld : (⟨e.val, hOld⟩ : M.H.edgeSet) ≠ ⟨e'.val, hOld'⟩ := by
                  intro h
                  have hvalEq : (e : Sym2 S) = (e' : Sym2 S) :=
                    congrArg (fun x : M.H.edgeSet => (x : Sym2 S)) h
                  exact hne (Subtype.ext hvalEq)
                exact M.model.edgePath_interior_disjoint ⟨e, hOld⟩ ⟨e', hOld'⟩ hneOld
                  (by simpa [edgePath', hOld] using hx)
                  (by simpa [edgePath', hOld'] using hx')
                  (by simpa [edgeTail', hOld, edgeTail_mem'] using htail)
                  (by simpa [edgeTail', hOld, edgeTail_mem'] using hhead)
                  (by simpa [edgeTail', hOld', edgeTail_mem'] using htail')
                  (by simpa [edgeTail', hOld', edgeTail_mem'] using hhead')
              · -- e old, e' new: x ∈ K from old, x ∉ K from new
                have hxinK : x ∈ rawConnectorK M :=
                  rawConnector_mem_K_of_support M ⟨e, hOld⟩
                    (by simpa [edgePath', hOld] using hx)
                    (by simpa [edgeTail', hOld, edgeTail_mem'] using htail)
                    (by simpa [edgeTail', hOld, edgeTail_mem'] using hhead)
                by_cases htailu' : edgeTail' e' = u
                · obtain ⟨_, hdir | hdir⟩ := hnew_edge e' hOld'
                  · have hxP : x ∈ p.support := by
                      simpa [edgePath', hOld', htailu', hdir.2] using hx'
                    have htailP : x ≠ M.model.branchVertex u := by
                      simpa [edgeTail', hOld', htailu'] using htail'
                    have hheadP : x ≠ M.model.branchVertex v := by
                      exact fun hEq =>
                        hhead' (hEq.trans (congrArg M.model.branchVertex hdir.2.symm))
                    exact (hpInternalAvoid hxP htailP hheadP) (Or.inr hxinK)
                  · exact absurd (hdir.1.symm.trans htailu') (Ne.symm huv)
                · obtain ⟨_, hdir | hdir⟩ := hnew_edge e' hOld'
                  · exact absurd hdir.1 htailu'
                  · have hxP : x ∈ p.support := by
                      simpa [edgePath', hOld', htailu', hdir.1, hdir.2,
                        SimpleGraph.Walk.support_reverse,
                        show v ≠ u from fun h => huv h.symm] using hx'
                    have htailP : x ≠ M.model.branchVertex v := by
                      simpa [edgeTail', hOld', hdir.1] using htail'
                    have hheadP : x ≠ M.model.branchVertex u := by
                      exact fun hEq =>
                        hhead' (hEq.trans (congrArg M.model.branchVertex hdir.2.symm))
                    exact (hpInternalAvoid hxP hheadP htailP) (Or.inr hxinK)
            · by_cases hOld' : (e' : Sym2 S) ∈ M.H.edgeSet
              · -- e new, e' old: symmetric
                have hxinK : x ∈ rawConnectorK M :=
                  rawConnector_mem_K_of_support M ⟨e', hOld'⟩
                    (by simpa [edgePath', hOld'] using hx')
                    (by simpa [edgeTail', hOld', edgeTail_mem'] using htail')
                    (by simpa [edgeTail', hOld', edgeTail_mem'] using hhead')
                by_cases htailu : edgeTail' e = u
                · obtain ⟨_, hdir | hdir⟩ := hnew_edge e hOld
                  · have hxP : x ∈ p.support := by
                      simpa [edgePath', hOld, htailu, hdir.2] using hx
                    have htailP : x ≠ M.model.branchVertex u := by
                      simpa [edgeTail', hOld, htailu] using htail
                    have hheadP : x ≠ M.model.branchVertex v := by
                      exact fun hEq =>
                        hhead (hEq.trans (congrArg M.model.branchVertex hdir.2.symm))
                    exact (hpInternalAvoid hxP htailP hheadP) (Or.inr hxinK)
                  · exact absurd (hdir.1.symm.trans htailu) (Ne.symm huv)
                · obtain ⟨_, hdir | hdir⟩ := hnew_edge e hOld
                  · exact absurd hdir.1 htailu
                  · have hxP : x ∈ p.support := by
                      simpa [edgePath', hOld, htailu, hdir.1, hdir.2,
                        SimpleGraph.Walk.support_reverse,
                        show v ≠ u from fun h => huv h.symm] using hx
                    have htailP : x ≠ M.model.branchVertex v := by
                      simpa [edgeTail', hOld, hdir.1] using htail
                    have hheadP : x ≠ M.model.branchVertex u := by
                      exact fun hEq =>
                        hhead (hEq.trans (congrArg M.model.branchVertex hdir.2.symm))
                    exact (hpInternalAvoid hxP hheadP htailP) (Or.inr hxinK)
              · -- Both new: both must be s(u,v), so e = e'
                obtain ⟨he_uv, _⟩ := hnew_edge e hOld
                obtain ⟨he_uv', _⟩ := hnew_edge e' hOld'
                exact hne (Subtype.ext (he_uv.trans he_uv'.symm)) }
      branch_vertex := M.branch_vertex }
  refine ⟨M', ?_⟩
  have := SimpleGraph.card_edgeFinset_sup_edge M.H hAdj huv
  convert this using 2
  ext e; simp [M', H']

/-! ### Helper: maximal connector model

Builds a maximal family of short paths between S-vertex pairs (internal
vertices outside S). Returns the graph H on S, its decidable adjacency,
the kernel K of internal vertices, and:
- H is a depth-(r-1) topological minor of G
- |K| ≤ |E(H)| · (2r-2)
- Maximality: for non-adjacent S-pairs, no short path avoids S ∪ K -/

private theorem exists_maximal_connector
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (S : Set V) [Fintype S] :
    ∃ (H : SimpleGraph S) (_ : DecidableRel H.Adj) (K : Finset V),
      IsShallowTopologicalMinor H G (r - 1) ∧
      K.card ≤ H.edgeFinset.card * (2 * r - 2) ∧
      (∀ u v : S, u ≠ v → ¬H.Adj u v →
        ¬∃ p : G.Walk u.1 v.1,
          p.IsPath ∧ p.length ≤ 2 * r - 1 ∧
            ∀ i : ℕ, 0 < i → i < p.length → p.getVert i ∉ (S ∪ (K : Set V))) := by
  let P : ℕ → Prop := fun n =>
    ∃ M : RawConnector G r S, M.H.edgeFinset.card = n
  have hP0 : P 0 := ⟨emptyRawConnector G r S, by simp [emptyRawConnector]⟩
  let bound := (Fintype.card S).choose 2
  have hPN : P (Nat.findGreatest P bound) := Nat.findGreatest_spec (Nat.zero_le _) hP0
  obtain ⟨M, hMcard⟩ := hPN
  refine ⟨M.H, inferInstance, rawConnectorK M, ⟨M.model⟩, rawConnectorK_card_bound M, ?_⟩
  intro u v huv hAdj hPath
  obtain ⟨p, hpPath, hpLen, hpAvoid⟩ := hPath
  obtain ⟨M', hM'card⟩ := exists_extend_rawConnector M huv hAdj p hpPath hpLen hpAvoid
  have hM'bound : M'.H.edgeFinset.card ≤ bound := by
    simpa [bound] using SimpleGraph.card_edgeFinset_le_card_choose_two (G := M'.H)
  have hlt : Nat.findGreatest P bound < M'.H.edgeFinset.card := by
    rw [← hMcard, hM'card]; omega
  exact Nat.findGreatest_is_greatest hlt hM'bound ⟨M', rfl⟩

/-! ### Helper: maximal connector + independent set (assembly)

Combines the maximal connector model with the density hypothesis and
independent set extraction. -/

private theorem exists_connector_and_indepset
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r d : ℕ) (S : Set V) [Fintype S]
    (hd : ∀ {W : Type} [DecidableEq W] [Fintype W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      IsShallowTopologicalMinor H G (r - 1) →
      H.edgeFinset.card ≤ d * Fintype.card W) :
    ∃ (K : Finset V) (I : Finset S),
      K.card ≤ d * Fintype.card S * (2 * r - 2) ∧
      Fintype.card S ≤ I.card * (2 * d + 1) ∧
      (∀ u ∈ I, ∀ v ∈ I, u ≠ v →
        ¬ ∃ p : G.Walk u.1 v.1,
          p.IsPath ∧ p.length ≤ 2 * r - 1 ∧
            ∀ i : ℕ, 0 < i → i < p.length → p.getVert i ∉ (S ∪ (K : Set V))) := by
  obtain ⟨H, instDecH, K, hMinor, hKcard, hMaximal⟩ := exists_maximal_connector G r S
  letI : DecidableRel H.Adj := instDecH
  have hEdge : H.edgeFinset.card ≤ d * Fintype.card S := hd H hMinor
  have hKbound : K.card ≤ d * Fintype.card S * (2 * r - 2) :=
    le_trans hKcard (mul_le_mul_of_nonneg_right hEdge (Nat.zero_le _))
  obtain ⟨I, hIndep, hIcard⟩ := exists_indepset_of_edge_bound H d hEdge
  exact ⟨K, I, hKbound, hIcard,
    fun u hu v hv huv => hMaximal u v huv (hIndep u hu v hv huv)⟩

/-! ### Helper: extract a concrete path family from subsetAdmValue -/

private theorem exists_subsetAdmFamily_of_le_subsetAdmValue
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (S : Set V) (v : V) {n : ℕ}
    (hn : 0 < n)
    (hvn : n ≤ subsetAdmValue G r S v) :
    ∃ paths : Fin n → (u : V) × G.Walk v u, IsSubsetAdmFamily G r S v paths := by
  unfold subsetAdmValue at hvn
  obtain ⟨k, _, hkLe⟩ :=
    (Finset.le_sup_iff (s := Finset.range (Fintype.card V))
      (f := fun k =>
        if ∃ paths : Fin k → (u : V) × G.Walk v u, IsSubsetAdmFamily G r S v paths
        then k else 0) hn).mp hvn
  split_ifs at hkLe with hkWitness
  · rcases hkWitness with ⟨pathsK, hpathsK⟩
    exact ⟨fun i => pathsK ⟨i.1, lt_of_lt_of_le i.2 hkLe⟩,
      ⟨fun i => hpathsK.target_mem ⟨i.1, lt_of_lt_of_le i.2 hkLe⟩,
       fun i => hpathsK.target_ne ⟨i.1, lt_of_lt_of_le i.2 hkLe⟩,
       fun i => hpathsK.isPath ⟨i.1, lt_of_lt_of_le i.2 hkLe⟩,
       fun i => hpathsK.length_le ⟨i.1, lt_of_lt_of_le i.2 hkLe⟩,
       fun i j hj0 hjlen =>
         hpathsK.internal_avoids ⟨i.1, lt_of_lt_of_le i.2 hkLe⟩ j hj0 hjlen,
       fun i j hij => hpathsK.disjoint ⟨i.1, lt_of_lt_of_le i.2 hkLe⟩
         ⟨j.1, lt_of_lt_of_le j.2 hkLe⟩ (by
           intro hEq; exact hij (Fin.ext (Fin.mk.inj hEq)))⟩⟩
  · omega

/-! ### Helper: dense shallow minor from large path families

Given that every vertex of S has subsetAdmValue ≥ n, plus a kernel set K
and an independent set I whose pairs admit no short path avoiding S ∪ K,
construct a depth-(r-1) topological minor J of G with:
  • |V(J)| ≤ |S| + |K|
  • |E(J)| ≥ |I| · n -/

private theorem exists_dense_shallow_minor
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (S : Set V) [Fintype S] (n : ℕ)
    (hn : 0 < n)
    (hLarge : ∀ v ∈ S, n ≤ subsetAdmValue G r S v)
    (K : Finset V) (I : Finset S)
    (hNoCross : ∀ u ∈ I, ∀ v ∈ I, u ≠ v →
      ¬ ∃ p : G.Walk u.1 v.1,
        p.IsPath ∧ p.length ≤ 2 * r - 1 ∧
          ∀ i : ℕ, 0 < i → i < p.length → p.getVert i ∉ (S ∪ (K : Set V))) :
    ∃ (W' : Type) (_ : DecidableEq W') (_ : Fintype W') (J : SimpleGraph W')
      (_ : DecidableRel J.Adj),
      IsShallowTopologicalMinor J G (r - 1) ∧
      Fintype.card W' ≤ Fintype.card S + K.card ∧
      I.card * n ≤ J.edgeFinset.card := by
  -- Set up types
  let W := {x : V // x ∈ S ∨ x ∈ (K : Set V)}
  let U : Set V := S ∪ (K : Set V)
  let IV : Type := ↥I
  let A : Type := IV × Fin n
  -- Extract path families for each vertex in I
  have hLargeIV : ∀ v : IV, n ≤ subsetAdmValue G r S v.1.1 :=
    fun v => hLarge v.1.1 v.1.2
  choose rawPaths rawFamily using fun v : IV =>
    exists_subsetAdmFamily_of_le_subsetAdmValue G r S v.1.1 hn (hLargeIV v)
  let root : IV → V := fun v => v.1.1
  let rootW : IV → W := fun v => ⟨root v, Or.inl v.1.2⟩
  let rawTarget : A → V := fun a => (rawPaths a.1 a.2).1
  let rawWalk : ∀ a : A, G.Walk (root a.1) (rawTarget a) := fun a => (rawPaths a.1 a.2).2
  -- Find first hit in U for each raw walk
  let hitSet : A → Finset V := fun a =>
    Finset.univ.filter fun x => x ∈ U ∧ x ≠ root a.1
  have hHitNonempty : ∀ a : A, {x ∈ hitSet a | x ∈ (rawWalk a).support}.Nonempty := by
    intro a
    refine ⟨rawTarget a, ?_⟩
    have hmemS : rawTarget a ∈ S := (rawFamily a.1).target_mem a.2
    have hne : rawTarget a ≠ root a.1 := (rawFamily a.1).target_ne a.2
    have hsupport : rawTarget a ∈ (rawWalk a).support :=
      (rawWalk a).end_mem_support
    simp [hitSet, U, hmemS, hne, hsupport]
  -- Extract first-hit vertex
  have hFirstHit : ∀ a : A, ∃ x ∈ hitSet a, ∃ (hx : x ∈ (rawWalk a).support),
      ∀ t ∈ hitSet a, t ∈ ((rawWalk a).takeUntil x hx).support → t = x :=
    fun a => (rawWalk a).exists_mem_support_forall_mem_support_imp_eq (hitSet a) (hHitNonempty a)
  let hit : A → V := fun a => Classical.choose (hFirstHit a)
  have hHit_mem_set : ∀ a : A, hit a ∈ hitSet a :=
    fun a => (Classical.choose_spec (hFirstHit a)).1
  have hHit_mem_support : ∀ a : A, hit a ∈ (rawWalk a).support :=
    fun a => (Classical.choose_spec (hFirstHit a)).2.1
  have hHit_first :
      ∀ a : A, ∀ t ∈ hitSet a,
        t ∈ ((rawWalk a).takeUntil (hit a) (hHit_mem_support a)).support → t = hit a :=
    fun a => (Classical.choose_spec (hFirstHit a)).2.2
  -- Trimmed walks
  let q : ∀ a : A, G.Walk (root a.1) (hit a) := fun a =>
    (rawWalk a).takeUntil (hit a) (hHit_mem_support a)
  have hqPath : ∀ a : A, (q a).IsPath :=
    fun a => (rawFamily a.1).isPath a.2 |>.takeUntil (hHit_mem_support a)
  have hqLen : ∀ a : A, (q a).length ≤ r :=
    fun a => le_trans ((rawWalk a).length_takeUntil_le (hHit_mem_support a))
      ((rawFamily a.1).length_le a.2)
  have hHit_mem_union : ∀ a : A, hit a ∈ U :=
    fun a => (show hit a ∈ U ∧ hit a ≠ root a.1 from by simpa [hitSet] using hHit_mem_set a).1
  have hHit_ne_root : ∀ a : A, hit a ≠ root a.1 :=
    fun a => (show hit a ∈ U ∧ hit a ≠ root a.1 from by simpa [hitSet] using hHit_mem_set a).2
  let endW : A → W := fun a => ⟨hit a, hHit_mem_union a⟩
  -- Interior of trimmed walk avoids U
  have hqSupportAvoid :
      ∀ a : A, ∀ {x : V}, x ∈ (q a).support →
        x ≠ root a.1 → x ≠ hit a → x ∉ U := by
    intro a x hx hxroot hxhit hxU
    have hxHitSet : x ∈ hitSet a := by simpa [hitSet, U, hxU, hxroot]
    exact hxhit (hHit_first a x hxHitSet hx)
  have hqAvoid :
      ∀ a : A, ∀ i : ℕ, 0 < i → i < (q a).length → (q a).getVert i ∉ U := by
    intro a i hi0 hil
    refine hqSupportAvoid a ((q a).getVert_mem_support i) ?_ ?_
    · intro hEq
      have : i = 0 := (hqPath a).getVert_eq_start_iff (le_of_lt hil) |>.mp (by
        simpa [q, root] using hEq)
      exact hi0.ne' this
    · intro hEq
      have : i = (q a).length := (hqPath a).getVert_eq_end_iff (le_of_lt hil) |>.mp (by
        simpa [q] using hEq)
      exact (Nat.ne_of_lt hil) this
  -- r ≥ 1 (vacuous when A is empty)
  have hrPos : ∀ a : A, 1 ≤ r := by
    intro a
    by_contra hr
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
    have hzero : subsetAdmValue G 0 S (root a.1) = 0 :=
      subsetAdmValue_eq_zero_of_r_eq_zero G S (root a.1)
    have : n ≤ 0 := by simpa [root, hr0, hzero] using hLargeIV a.1
    exact (Nat.not_lt_of_ge this) hn
  -- hit a ≠ root b for distinct IV components
  have hHit_ne_other_root :
      ∀ a b : A, a.1 ≠ b.1 → hit a ≠ root b.1 := by
    intro a b hab hEq
    let u : S := a.1.1
    let v : S := b.1.1
    have huv : u ≠ v := by
      intro huv; exact hab (Subtype.ext huv)
    have hlen : (q a).length ≤ 2 * r - 1 := by
      exact le_trans (hqLen a) (by omega)
    let hp : G.Walk u.1 v.1 := (q a).copy rfl hEq
    exact hNoCross u a.1.2 v b.1.2 huv ⟨hp, by simpa [hp] using hqPath a,
      by simpa [hp] using hlen, by
        intro i hi0 hil
        simpa [hp, U] using hqAvoid a i hi0 (by simpa [hp] using hil)⟩
  -- Prefix of q avoids hit at end
  have hTakeUntil_not_hit :
      ∀ {a : A} {x : V} (hx : x ∈ (q a).support),
        x ≠ root a.1 → x ≠ hit a →
        hit a ∉ ((q a).takeUntil x hx).support := by
    intro a x hx hxroot hxhit hmem
    let qa : G.Walk (root a.1) x := (q a).takeUntil x hx
    have hqa_lt : qa.length < (q a).length := by
      have hle : qa.length ≤ (q a).length := (q a).length_takeUntil_le hx
      by_contra hlt
      have hEqLen : qa.length = (q a).length := le_antisymm hle (Nat.not_lt.mp hlt)
      have hxEnd : x = hit a := by
        have htake : qa.getVert qa.length = (q a).getVert qa.length :=
          (q a).getVert_takeUntil hx le_rfl
        have hxAt : (q a).getVert qa.length = x := by
          rw [← htake]; exact qa.getVert_length
        have hEnd : (q a).getVert qa.length = hit a := by
          simpa [hEqLen] using (q a).getVert_length
        exact hxAt.symm.trans hEnd
      exact hxhit hxEnd
    rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmem with ⟨j, hjEq, hjle⟩
    have htake : qa.getVert j = (q a).getVert j :=
      (q a).getVert_takeUntil hx hjle
    have hqEq : (q a).getVert j = hit a := by rw [← htake, hjEq]
    have hjEnd : j = (q a).length :=
      (hqPath a).getVert_eq_end_iff (le_trans hjle (le_of_lt hqa_lt)) |>.mp hqEq
    exact (Nat.not_le_of_lt hqa_lt) (hjEnd ▸ hjle)
  -- Prefix of q: interior avoids U
  have hTakeUntil_avoid :
      ∀ {a : A} {x w : V} (hx : x ∈ (q a).support),
        x ≠ root a.1 → x ≠ hit a →
        w ∈ ((q a).takeUntil x hx).support →
        w ≠ root a.1 → w ∉ U := by
    intro a x w hx hxroot hxhit hw hwroot
    have hwq : w ∈ (q a).support := (q a).support_takeUntil_subset hx hw
    have hwhit : w ≠ hit a := by
      intro hwEq
      exact hTakeUntil_not_hit hx hxroot hxhit (hwEq ▸ hw)
    exact hqSupportAvoid a hwq hwroot hwhit
  -- Cross-path impossibility: paths from different IV components can't share
  -- an interior vertex
  have hNoCrossInterior :
      ∀ {a b : A} {x : V},
        a.1 ≠ b.1 →
        x ∈ (q a).support →
        x ∈ (q b).support →
        x ≠ root a.1 →
        x ≠ hit a →
        x ≠ root b.1 →
        x ≠ hit b →
        False := by
    intro a b x hab hxa hxb hxra hxea hxrb hxeb
    let qa : G.Walk (root a.1) x := (q a).takeUntil x hxa
    let qb : G.Walk (root b.1) x := (q b).takeUntil x hxb
    have hqa_lt : qa.length < (q a).length := by
      have hle : qa.length ≤ (q a).length := (q a).length_takeUntil_le hxa
      by_contra hlt
      have hEqLen : qa.length = (q a).length := le_antisymm hle (Nat.not_lt.mp hlt)
      have hxEnd : x = hit a := by
        have htake : qa.getVert qa.length = (q a).getVert qa.length :=
          (q a).getVert_takeUntil hxa le_rfl
        have hxAt : (q a).getVert qa.length = x := by rw [← htake]; exact qa.getVert_length
        exact hxAt.symm.trans (by simpa [hEqLen] using (q a).getVert_length)
      exact hxea hxEnd
    have hqb_lt : qb.length < (q b).length := by
      have hle : qb.length ≤ (q b).length := (q b).length_takeUntil_le hxb
      by_contra hlt
      have hEqLen : qb.length = (q b).length := le_antisymm hle (Nat.not_lt.mp hlt)
      have hxEnd : x = hit b := by
        have htake : qb.getVert qb.length = (q b).getVert qb.length :=
          (q b).getVert_takeUntil hxb le_rfl
        have hxAt : (q b).getVert qb.length = x := by rw [← htake]; exact qb.getVert_length
        exact hxAt.symm.trans (by simpa [hEqLen] using (q b).getVert_length)
      exact hxeb hxEnd
    let raw : G.Walk (root a.1) (root b.1) := qa.append qb.reverse
    let p : G.Walk (root a.1) (root b.1) := raw.bypass
    have hpPath : p.IsPath := raw.bypass_isPath
    have hpLen : p.length ≤ 2 * r - 1 := by
      have hr1 : 1 ≤ r := hrPos a
      have hraw : raw.length ≤ 2 * r - 1 := by
        rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
        have hqa_le : qa.length + 1 ≤ r := lt_of_lt_of_le hqa_lt (hqLen a)
        have hqb_le : qb.length + 1 ≤ r := lt_of_lt_of_le hqb_lt (hqLen b)
        omega
      exact le_trans raw.length_bypass_le hraw
    have hpAvoid :
        ∀ i : ℕ, 0 < i → i < p.length → p.getVert i ∉ U := by
      intro i hi0 hil
      have hwRaw : p.getVert i ∈ raw.support :=
        raw.support_bypass_subset (p.getVert_mem_support i)
      have hwStart : p.getVert i ≠ root a.1 := by
        intro hEq
        have : i = 0 := (hpPath.getVert_eq_start_iff (le_of_lt hil)).mp (by
          simpa [p, root] using hEq)
        exact hi0.ne' this
      have hwEnd : p.getVert i ≠ root b.1 := by
        intro hEq
        have : i = p.length := (hpPath.getVert_eq_end_iff (le_of_lt hil)).mp (by
          simpa [p, root] using hEq)
        exact (Nat.ne_of_lt hil) this
      rw [SimpleGraph.Walk.mem_support_append_iff] at hwRaw
      rcases hwRaw with hwqa | hwqb
      · exact hTakeUntil_avoid hxa hxra hxea hwqa hwStart
      · have hwqb' : p.getVert i ∈ qb.support :=
          List.mem_reverse.mp (by simpa [SimpleGraph.Walk.support_reverse] using hwqb)
        exact hTakeUntil_avoid hxb hxrb hxeb hwqb' hwEnd
    let u : S := a.1.1
    let v : S := b.1.1
    have huv : u ≠ v := by intro huv; exact hab (Subtype.ext huv)
    exact hNoCross u a.1.2 v b.1.2 huv ⟨p, hpPath, hpLen, by
      intro i hi0 hil; exact hpAvoid i hi0 hil⟩
  -- Build J on W
  let edgeSym : A → Sym2 W := fun a => s(rootW a.1, endW a)
  let E : Finset (Sym2 W) := Finset.univ.image edgeSym
  let J : SimpleGraph W := SimpleGraph.fromEdgeSet ((E : Finset (Sym2 W)) : Set (Sym2 W))
  have hEnd_ne_rootW : ∀ a : A, endW a ≠ rootW a.1 := by
    intro a hEq; exact hHit_ne_root a (congrArg Subtype.val hEq)
  -- Edge injection
  have hEdgeInj : Function.Injective edgeSym := by
    intro a b hab'
    rcases (Sym2.eq_iff.mp hab') with h | h
    · rcases h with ⟨hroot, hend⟩
      have hVeq : (rootW a.1).1 = (rootW b.1).1 := congrArg Subtype.val hroot
      have hrootIV : a.1 = b.1 := Subtype.ext (Subtype.ext hVeq)
      have hhit : hit a = hit b := congrArg Subtype.val hend
      have hidx : a.2 = b.2 := by
        by_contra hne
        have hSupportEq : (rawPaths a.1 b.2).2.support = (rawPaths b.1 b.2).2.support :=
          congrArg (fun v => (rawPaths v b.2).2.support) hrootIV
        have hbmem0 : hit a ∈ (rawPaths b.1 b.2).2.support := by
          simpa [hhit] using hHit_mem_support b
        have hbmem : hit a ∈ (rawPaths a.1 b.2).2.support := hSupportEq ▸ hbmem0
        have hdisj := (rawFamily a.1).disjoint a.2 b.2 hne (hit a)
          (hHit_mem_support a) hbmem
        exact hHit_ne_root a hdisj
      exact Prod.ext hrootIV hidx
    · rcases h with ⟨ha, hb⟩
      exfalso
      have hv : a.1 ≠ b.1 := by
        intro hEq
        have : endW b = rootW b.1 := by simpa [hEq] using ha.symm
        exact hEnd_ne_rootW b this
      exact (hHit_ne_other_root b a (by simpa using hv.symm)) ((congrArg Subtype.val ha).symm)
  -- Edge membership
  have hEdge_mem : ∀ a : A, edgeSym a ∈ J.edgeSet := by
    intro a
    have hmemE : edgeSym a ∈ ((E : Finset (Sym2 W)) : Set (Sym2 W)) :=
      Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    have hnotDiag : edgeSym a ∉ Sym2.diagSet :=
      fun hdiag => hEnd_ne_rootW a hdiag.symm
    simpa [J, SimpleGraph.edgeSet_fromEdgeSet] using ⟨hmemE, hnotDiag⟩
  let edgeEmb : A → J.edgeSet := fun a => ⟨edgeSym a, hEdge_mem a⟩
  have hEdgeIndex_injective : Function.Injective edgeEmb :=
    fun a b hEq => hEdgeInj (congrArg Subtype.val hEq)
  -- For the model: edge decomposition
  have hEdgeIndexExists : ∀ e : J.edgeSet, ∃ a : A, edgeSym a = (e : Sym2 W) := by
    intro e
    have heE : (e : Sym2 W) ∈ E := by
      have : (e : Sym2 W) ∈ (((E : Finset (Sym2 W)) : Set (Sym2 W)) \ Sym2.diagSet) := by
        simpa [J, SimpleGraph.edgeSet_fromEdgeSet] using e.2
      exact this.1
    exact Finset.mem_image.mp heE |>.imp fun a ha => ha.2
  let edgeIndex : J.edgeSet → A := fun e => Classical.choose (hEdgeIndexExists e)
  have hEdgeIndex_spec : ∀ e : J.edgeSet, edgeSym (edgeIndex e) = (e : Sym2 W) :=
    fun e => Classical.choose_spec (hEdgeIndexExists e)
  let edgeTail : J.edgeSet → W := fun e => rootW (edgeIndex e).1
  have hEdgeTail_mem : ∀ e : J.edgeSet, edgeTail e ∈ (e : Sym2 W) := by
    intro e
    have hmem : edgeTail e ∈ edgeSym (edgeIndex e) := by simp [edgeTail, edgeSym]
    exact (hEdgeIndex_spec e).symm ▸ hmem
  have hEdgeOther : ∀ e : J.edgeSet, Sym2.Mem.other (hEdgeTail_mem e) = endW (edgeIndex e) := by
    intro e
    exact Sym2.congr_right.mp <|
      calc
        s(edgeTail e, Sym2.Mem.other (hEdgeTail_mem e)) = (e : Sym2 W) :=
          Sym2.other_spec (hEdgeTail_mem e)
        _ = s(edgeTail e, endW (edgeIndex e)) := by
          simpa [edgeTail, edgeSym] using (hEdgeIndex_spec e).symm
  have hEdgeHead : ∀ e : J.edgeSet,
      hit (edgeIndex e) = ↑(Sym2.Mem.other (hEdgeTail_mem e)) := by
    intro e
    simpa [endW] using congrArg Subtype.val (hEdgeOther e).symm
  -- Build the ShallowTopologicalMinorModel
  let model : ShallowTopologicalMinorModel J G (r - 1) :=
    { branchVertex := ⟨Subtype.val, Subtype.coe_injective⟩
      edgeTail := edgeTail
      edgeTail_mem := hEdgeTail_mem
      edgePath := fun e => (q (edgeIndex e)).copy rfl (hEdgeHead e)
      edgePath_isPath := by
        intro e; simpa [hEdgeHead e] using hqPath (edgeIndex e)
      edgePath_length := by
        intro e
        have hlen : (q (edgeIndex e)).length ≤ r := hqLen (edgeIndex e)
        have hr : 1 ≤ r := hrPos (edgeIndex e)
        calc ((q (edgeIndex e)).copy rfl (hEdgeHead e)).length
            = (q (edgeIndex e)).length := by simp
          _ ≤ r := hlen
          _ ≤ 2 * (r - 1) + 1 := by omega
      edgePath_interior_avoids_branch := by
        intro e x hx htail hhead w
        have hnot : x ∉ U := by
          refine hqSupportAvoid (edgeIndex e) ?_ ?_ ?_
          · simpa [hEdgeHead e] using hx
          · simpa [edgeTail] using htail
          · simpa [hEdgeHead e] using hhead
        exact fun hEq => hnot (hEq.symm ▸ w.2)
      edgePath_interior_disjoint := by
        intro e e' x hne hx hx' htail hhead htail' hhead'
        let a := edgeIndex e
        let b := edgeIndex e'
        have hab : a ≠ b := by
          intro hEq; apply hne; apply Subtype.ext
          simpa [a, b, hEdgeIndex_spec e, hEdgeIndex_spec e'] using congrArg edgeSym hEq
        by_cases hroot : a.1 = b.1
        · have hidx : a.2 ≠ b.2 := by
            intro hEq; exact hab (Prod.ext hroot hEq)
          have hxRaw : x ∈ (rawWalk a).support :=
            (rawWalk a).support_takeUntil_subset (hHit_mem_support a)
              (by simpa [a, hEdgeHead e] using hx)
          have hxRaw' : x ∈ (rawWalk b).support :=
            (rawWalk b).support_takeUntil_subset (hHit_mem_support b)
              (by simpa [b, hEdgeHead e'] using hx')
          have hEqRoot : x = root a.1 := by
            have hSupportEq : (rawPaths a.1 b.2).2.support = (rawPaths b.1 b.2).2.support :=
              congrArg (fun v => (rawPaths v b.2).2.support) hroot
            have hxRaw''0 : x ∈ (rawPaths b.1 b.2).2.support := by
              simpa [rawWalk, rawTarget] using hxRaw'
            have hxRaw'' : x ∈ (rawPaths a.1 b.2).2.support := hSupportEq ▸ hxRaw''0
            exact (rawFamily a.1).disjoint a.2 b.2 hidx x hxRaw hxRaw''
          exact htail (by simpa [a, edgeTail] using hEqRoot)
        · exact hNoCrossInterior hroot
            (by simpa [a, hEdgeHead e] using hx)
            (by simpa [b, hEdgeHead e'] using hx')
            (by simpa [a, edgeTail] using htail)
            (by simpa [a, hEdgeHead e] using hhead)
            (by simpa [b, edgeTail] using htail')
            (by simpa [b, hEdgeHead e'] using hhead') }
  -- Vertex bound: |W| ≤ |S| + |K|
  have hVertBound : Fintype.card W ≤ Fintype.card S + K.card := by
    have h1 : Fintype.card W ≤ Fintype.card S +
        Fintype.card {x : V // x ∈ (K : Set V)} := by
      convert Fintype.card_subtype_or (fun x : V => x ∈ S) (fun x => x ∈ (K : Set V)) using 1
    have h2 : Fintype.card {x : V // x ∈ (K : Set V)} = K.card := by
      convert Fintype.card_coe K
    omega
  -- Edge bound: I.card * n ≤ |E(J)|
  -- Pin the Fintype instance for J.edgeSet to match the existential witness
  letI : Fintype J.edgeSet := J.fintypeEdgeSet
  have hEdgeBound : I.card * n ≤ J.edgeFinset.card := by
    have hAcard : I.card * n = (Finset.univ : Finset A).card := by
      simp [Finset.card_univ, A, IV, Fintype.card_coe, Fintype.card_fin]
    have hImage : (Finset.univ.image edgeSym).card = (Finset.univ : Finset A).card :=
      Finset.card_image_of_injective _ hEdgeInj
    have hImageSub : Finset.univ.image edgeSym ⊆ J.edgeFinset := by
      intro e he
      rw [Finset.mem_image] at he
      obtain ⟨a, _, rfl⟩ := he
      exact SimpleGraph.mem_edgeFinset.mpr (hEdge_mem a)
    calc I.card * n = (Finset.univ : Finset A).card := hAcard
      _ = (Finset.univ.image edgeSym).card := hImage.symm
      _ ≤ J.edgeFinset.card := Finset.card_le_card hImageSub
  exact ⟨W, inferInstance, inferInstance, J, inferInstance, ⟨model⟩, hVertBound, hEdgeBound⟩

/-! ### Helper: Phase B arithmetic

The key numerical fact: for d ≥ 1 and r ≥ 1,
  d · (2d+1) · (1 + d · (2r-2)) < 6r · d³ + 1.
Equivalently: after expanding, the difference equals
  2d²r(d-1) + 4d³ - d + 1 ≥ 4 > 0. -/

private theorem phase_b_arith (r d : ℕ) (hr : 1 ≤ r) (hd : 1 ≤ d) :
    d * (2 * d + 1) * (1 + d * (2 * r - 2)) < 6 * r * d ^ 3 + 1 := by
  suffices d * (2 * d + 1) * (1 + d * (2 * r - 2)) ≤ 6 * r * d ^ 3 by omega
  rw [show 2 * r - 2 = 2 * (r - 1) from by omega]
  calc d * (2 * d + 1) * (1 + d * (2 * (r - 1)))
      ≤ d * (3 * d) * (1 + d * (2 * (r - 1))) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left d (by omega))
    _ = 3 * d ^ 2 * (1 + 2 * d * (r - 1)) := by ring
    _ ≤ 3 * d ^ 2 * (2 * d * r) :=
        Nat.mul_le_mul_left _ (by
          calc 1 + 2 * d * (r - 1)
              ≤ 2 * d + 2 * d * (r - 1) := by omega
            _ = 2 * d * (1 + (r - 1)) := by ring
            _ = 2 * d * r := by congr 1; omega)
    _ = 6 * r * d ^ 3 := by ring

/-! ### Main Phase B theorem -/

private theorem exists_bounded_subsetAdm_vertex
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r d : ℕ)
    (hd : ∀ {W : Type} [DecidableEq W] [Fintype W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      IsShallowTopologicalMinor H G (r - 1) →
      H.edgeFinset.card ≤ d * Fintype.card W) :
    ∀ S : Set V, S.Nonempty →
      ∃ v ∈ S, subsetAdmValue G r S v ≤ 6 * r * d ^ 3 := by
  intro S hS
  -- r = 0: subsetAdmValue = 0 ≤ 0
  by_cases hr0 : r = 0
  · obtain ⟨v, hv⟩ := hS
    exact ⟨v, hv, by simp [hr0, subsetAdmValue_eq_zero_of_r_eq_zero]⟩
  -- Assume for contradiction that every vertex has large subsetAdmValue
  by_contra hContra
  push_neg at hContra
  -- hContra : ∀ v ∈ S, 6 * r * d ^ 3 < subsetAdmValue G r S v
  haveI : Fintype S := Set.Finite.fintype (Set.toFinite S)
  haveI : Nonempty S := Set.nonempty_coe_sort.mpr hS
  have hrd : 1 ≤ r := Nat.pos_of_ne_zero hr0
  -- Build maximal connector and extract independent set
  obtain ⟨K, I, hKbound, hIcard, hNoCross⟩ :=
    exists_connector_and_indepset G r d S hd
  -- S is nonempty → |S| ≥ 1 → |I| ≥ 1
  have hScard : 0 < Fintype.card S := Fintype.card_pos
  have hIpos : 0 < I.card := by
    rcases Nat.eq_zero_or_pos I.card with h0 | h0
    · simp only [h0, zero_mul] at hIcard
      omega
    · exact h0
  -- Everyone has subsetAdmValue ≥ ℓ + 1
  set ℓ := 6 * r * d ^ 3 with hℓ_def
  have hLarge : ∀ v ∈ S, ℓ + 1 ≤ subsetAdmValue G r S v :=
    fun v hv => hContra v hv
  -- Build dense minor J
  obtain ⟨W', instW'Dec, instW'Fin, J, instJDec, hJminor, hJverts, hJedges⟩ :=
    exists_dense_shallow_minor G r S (ℓ + 1) (by omega) hLarge K I hNoCross
  -- Install instances for W' and J
  letI : DecidableEq W' := instW'Dec
  letI : Fintype W' := instW'Fin
  letI : DecidableRel J.Adj := instJDec
  -- Apply density hypothesis to J
  have hJdensity : J.edgeFinset.card ≤ d * Fintype.card W' := hd J hJminor
  -- Chain: I.card * (ℓ+1) ≤ |E(J)| ≤ d * |V(J)| ≤ d * (|S| + |K|)
  have h1 : I.card * (ℓ + 1) ≤ d * (Fintype.card S + K.card) :=
    calc I.card * (ℓ + 1)
        ≤ J.edgeFinset.card := hJedges
      _ ≤ d * Fintype.card W' := hJdensity
      _ ≤ d * (Fintype.card S + K.card) := Nat.mul_le_mul_left d hJverts
  -- Step-by-step to d * (2d+1) * (1 + d*(2r-2)) * I.card
  have h2 : d * (Fintype.card S + K.card) ≤
      d * (Fintype.card S + d * Fintype.card S * (2 * r - 2)) :=
    Nat.mul_le_mul_left d (Nat.add_le_add_left hKbound _)
  have h3 : d * (Fintype.card S + d * Fintype.card S * (2 * r - 2)) ≤
      d * (I.card * (2 * d + 1) + d * (I.card * (2 * d + 1)) * (2 * r - 2)) :=
    Nat.mul_le_mul_left d (Nat.add_le_add
      hIcard (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left d hIcard)))
  have h4 : d * (I.card * (2 * d + 1) + d * (I.card * (2 * d + 1)) * (2 * r - 2)) =
      d * (2 * d + 1) * (1 + d * (2 * r - 2)) * I.card := by
    generalize 2 * r - 2 = m; ring
  -- Combine and cancel I.card
  have h_chain : I.card * (ℓ + 1) ≤
      d * (2 * d + 1) * (1 + d * (2 * r - 2)) * I.card :=
    calc I.card * (ℓ + 1)
        ≤ d * (Fintype.card S + K.card) := h1
      _ ≤ d * (Fintype.card S + d * Fintype.card S * (2 * r - 2)) := h2
      _ ≤ d * (I.card * (2 * d + 1) + d * (I.card * (2 * d + 1)) * (2 * r - 2)) := h3
      _ = d * (2 * d + 1) * (1 + d * (2 * r - 2)) * I.card := h4
  have h_cancel : ℓ + 1 ≤ d * (2 * d + 1) * (1 + d * (2 * r - 2)) := by
    rw [show I.card * (ℓ + 1) = (ℓ + 1) * I.card from Nat.mul_comm ..] at h_chain
    exact Nat.le_of_mul_le_mul_right h_chain hIpos
  -- d = 0: ℓ + 1 = 1 > 0 = RHS, immediate contradiction
  by_cases hd0 : d = 0
  · simp [hd0] at h_cancel
  -- d ≥ 1, r ≥ 1: use phase_b_arith for contradiction
  · exact Nat.lt_irrefl _
      (lt_of_lt_of_le (phase_b_arith r d hrd (Nat.pos_of_ne_zero hd0)) h_cancel)

/-! ## Main theorem -/

/-- Lemma 3.2/ch2: adm_r(G) ≤ 1 + 6r · d³ via a greedy ordering. -/
theorem adm_le_of_topGrad_bound
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (r d : ℕ)
    (hd : ∀ {W : Type} [DecidableEq W] [Fintype W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      IsShallowTopologicalMinor H G (r - 1) →
      H.edgeFinset.card ≤ d * Fintype.card W) :
    ∃ (ord : LinearOrder V),
      letI := ord; adm G r ≤ 1 + 6 * r * d ^ 3 := by
  exact exists_order_adm_le_of_subsetAdmBound G r
    (exists_bounded_subsetAdm_vertex G r d hd)

end

end Lax5Proofs.Source.Catalog.SparsityLectures.AdmBoundByTopGrad
