import Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.NowhereDense.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.UniformQuasiWideness.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowTopologicalMinor.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.OddStepReduction.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.EvenStepReduction.Full
import Lax5Proofs.BipartiteRamsey
import Lax5Proofs.Ramsey

namespace Lax5Proofs.Source.Catalog.SparsityLectures.NDImpliesUQW

open Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries Lax5Proofs.Source.Catalog.SparsityLectures.NowhereDense Lax5Proofs.Source.Catalog.SparsityLectures.UniformQuasiWideness
open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor
open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowTopologicalMinor
open Lax5Proofs.Source.Catalog.SparsityLectures.OddStepReduction Lax5Proofs.Source.Catalog.SparsityLectures.EvenStepReduction
open Lax5Proofs.BipartiteRamsey Lax5Proofs.Ramsey

/-! ## Helper lemmas -/

/-- Lift an H-walk to a G-walk through composed branch sets. -/
private theorem liftWalk {V W : Type}
    {H : SimpleGraph W} {G : SimpleGraph V} {a : ℕ}
    (MHG : ShallowMinorModel H G a)
    {w₁ w₃ : W} (q : H.Walk w₁ w₃) :
    ∃ qG : G.Walk (MHG.center w₁) (MHG.center w₃),
      qG.length ≤ (2 * a + 1) * q.length ∧
      ∀ x ∈ qG.support, ∃ w' ∈ q.support, x ∈ MHG.branchSet w' := by
  induction q with
  | nil =>
    exact ⟨.nil, by simp, fun x hx => by
      simp only [SimpleGraph.Walk.support_nil, List.mem_cons,
        List.mem_nil_iff, or_false] at hx ⊢
      exact ⟨_, rfl, hx ▸ MHG.center_mem _⟩⟩
  | @cons wa wb wc hadj_H rest ih_rest =>
    obtain ⟨q_rest, hq_rest_len, hq_rest_sup⟩ := ih_rest
    obtain ⟨x, hx, y, hy, hadj_G⟩ := MHG.branchEdge wa wb hadj_H
    obtain ⟨p1, _, hp1len, hp1sup⟩ := MHG.branchRadius wa x hx
    obtain ⟨p2, _, hp2len, hp2sup⟩ := MHG.branchRadius wb y hy
    refine ⟨(p1.append (.cons hadj_G p2.reverse)).append q_rest, ?_, ?_⟩
    · simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_reverse]
      calc p1.length + (p2.length + 1) + q_rest.length
          ≤ a + (a + 1) + (2 * a + 1) * rest.length := by omega
        _ = (2 * a + 1) * rest.length + (2 * a + 1) := by omega
        _ = (2 * a + 1) * (rest.length + 1) := by rw [Nat.mul_add, Nat.mul_one]
    · intro z hz
      rw [SimpleGraph.Walk.support_append] at hz
      rcases List.mem_append.mp hz with hz | hz
      · rw [SimpleGraph.Walk.support_append] at hz
        rcases List.mem_append.mp hz with hz | hz
        · exact ⟨wa, .head _, hp1sup z hz⟩
        · have hz' := List.tail_subset _ hz
          rw [SimpleGraph.Walk.support_cons] at hz'
          rcases List.mem_cons.mp hz' with rfl | hz'
          · exact ⟨wa, .head _, hx⟩
          · rw [SimpleGraph.Walk.support_reverse] at hz'
            exact ⟨wb, .tail _ (SimpleGraph.Walk.start_mem_support _),
              hp2sup z (List.mem_reverse.mp hz')⟩
      · obtain ⟨w', hw', hz'⟩ := hq_rest_sup z (List.tail_subset _ hz)
        exact ⟨w', .tail _ hw', hz'⟩

/-- Composition of shallow minors: if `K ⪯_b H` and `H ⪯_a G`, then
    `K ⪯_{2ab+a+b} G`. -/
private theorem shallowMinor_compose {U V W : Type}
    {K : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V} {a b : ℕ}
    (hKH : IsShallowMinor K H b) (hHG : IsShallowMinor H G a) :
    IsShallowMinor K G (2 * a * b + a + b) := by
  let MKH := hKH.some; let MHG := hHG.some
  exact ⟨{
    branchSet := fun u => ⋃ w ∈ MKH.branchSet u, MHG.branchSet w
    center := fun u => MHG.center (MKH.center u)
    center_mem := fun u => Set.mem_biUnion (MKH.center_mem u) (MHG.center_mem _)
    branchDisjoint := fun u₁ u₂ h =>
      Set.disjoint_left.mpr fun v hv1 hv2 => by
        simp only [Set.mem_iUnion] at hv1 hv2
        obtain ⟨w1, hw1, hv1⟩ := hv1; obtain ⟨w2, hw2, hv2⟩ := hv2
        rcases eq_or_ne w1 w2 with rfl | hne
        · exact Set.disjoint_left.mp (MKH.branchDisjoint u₁ u₂ h) hw1 hw2
        · exact Set.disjoint_left.mp (MHG.branchDisjoint w1 w2 hne) hv1 hv2
    branchRadius := fun u v hv => by
      classical
      simp only [Set.mem_iUnion] at hv
      obtain ⟨w, hw, hv⟩ := hv
      obtain ⟨pH, _, hlenH, hsupH⟩ := MKH.branchRadius u w hw
      obtain ⟨pG_tail, _, hlenG_tail, hsupG_tail⟩ := MHG.branchRadius w v hv
      obtain ⟨qG, hqGlen, hqGsup⟩ := liftWalk MHG pH
      let full := qG.append pG_tail
      let p' := full.bypass
      refine ⟨p', full.bypass_isPath, ?_, ?_⟩
      · have hfl := SimpleGraph.Walk.length_append qG pG_tail
        have hqG_bound : qG.length ≤ 2 * a * b + b := by
          have h1 := Nat.mul_le_mul_left (2 * a + 1) hlenH
          have : (2 * a + 1) * b = 2 * a * b + b := by
            rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
          omega
        calc p'.length ≤ full.length := full.length_bypass_le
          _ = qG.length + pG_tail.length := hfl
          _ ≤ 2 * a * b + a + b := by omega
      · intro x hx
        have hx' := full.support_bypass_subset hx
        rw [SimpleGraph.Walk.support_append] at hx'
        rcases List.mem_append.mp hx' with h | h
        · obtain ⟨w', hw', hxw'⟩ := hqGsup x h
          exact Set.mem_biUnion (hsupH w' hw') hxw'
        · exact Set.mem_biUnion hw (hsupG_tail x (List.tail_subset _ h))
    branchEdge := fun u₁ u₂ hadj => by
      obtain ⟨w1, hw1, w2, hw2, hadjH⟩ := MKH.branchEdge u₁ u₂ hadj
      obtain ⟨x, hx, y, hy, hadjG⟩ := MHG.branchEdge w1 w2 hadjH
      exact ⟨x, Set.mem_biUnion hw1 hx, y, Set.mem_biUnion hw2 hy, hadjG⟩ }⟩

/-- A depth-`d` minor of `deleteVerts G S` is a depth-`d` minor of `G`. -/
private theorem shallowMinor_of_subgraph {U V : Type}
    {H : SimpleGraph U} {G G' : SimpleGraph V} {d : ℕ}
    (hsub : ∀ {u v}, G.Adj u v → G'.Adj u v)
    (h : IsShallowMinor H G d) :
    IsShallowMinor H G' d := by
  let M := h.some
  exact ⟨{
    branchSet := M.branchSet
    center := M.center
    center_mem := M.center_mem
    branchDisjoint := M.branchDisjoint
    branchRadius := fun v x hx => by
      obtain ⟨p, hp, hlen, hsup⟩ := M.branchRadius v x hx
      have hedge : ∀ e ∈ p.edges, e ∈ G'.edgeSet := by
        intro e he
        have hmem := SimpleGraph.Walk.edges_subset_edgeSet p he
        revert hmem
        refine e.ind ?_
        intro a b hab
        exact show G'.Adj a b by exact hsub hab
      exact ⟨p.transfer G' hedge, hp.transfer hedge,
        by rw [SimpleGraph.Walk.length_transfer]; exact hlen,
        by rw [SimpleGraph.Walk.support_transfer]; exact hsup⟩
    branchEdge := fun u v hadj => by
      obtain ⟨x, hx, y, hy, hadj'⟩ := M.branchEdge u v hadj
      exact ⟨x, hx, y, hy, hsub hadj'⟩ }⟩

/-- A depth-`d` minor of `deleteVerts G S` is a depth-`d` minor of `G`. -/
private theorem shallowMinor_of_deleteVerts {V W : Type}
    {H : SimpleGraph W} {G : SimpleGraph V} {S : Set V} {d : ℕ}
    (h : IsShallowMinor H (deleteVerts G S) d) :
    IsShallowMinor H G d := by
  exact shallowMinor_of_subgraph (fun {u v} h' => by
    have h'' : G.Adj u v ∧ u ∉ S ∧ v ∉ S := by
      simpa [deleteVerts] using h'
    exact h''.1) h

/-- Every set is distance-0 independent: any walk between distinct vertices has
    length ≥ 1 > 0. -/
private lemma distIndependent_zero {V : Type} (G : SimpleGraph V) (A : Set V) :
    DistIndependent G 0 A := by
  intro u _ v _ huv p
  exact Nat.pos_of_ne_zero fun h => huv (SimpleGraph.Walk.eq_of_length_eq_zero h)

/-- `deleteVerts G ∅` preserves `DistIndependent`. -/
private lemma distIndependent_deleteVerts_empty {V : Type}
    {G : SimpleGraph V} {r : ℕ} {A : Set V}
    (h : DistIndependent G r A) :
    DistIndependent (deleteVerts G (∅ : Set V)) r A := by
  convert h using 1; ext u v; simp [deleteVerts]

/-- Coercion helper: `↑(∅ : Finset V) = (∅ : Set V)`. -/
private lemma finset_coe_empty {V : Type} :
    (↑(∅ : Finset V) : Set V) = (∅ : Set V) := Finset.coe_empty

/-- `deleteVerts` is associative: removing `S₁` then `S₂` = removing `S₁ ∪ S₂`. -/
private lemma deleteVerts_deleteVerts {V : Type} (G : SimpleGraph V) (S₁ S₂ : Set V) :
    deleteVerts (deleteVerts G S₁) S₂ = deleteVerts G (S₁ ∪ S₂) := by
  ext u v; simp only [deleteVerts, Set.mem_union, not_or]; tauto

/-- A clique of size `n` gives `completeGraph (Fin n)` as a depth-0 minor. -/
private lemma clique_gives_minor {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (h : ¬G.CliqueFree n) :
    IsShallowMinor (SimpleGraph.completeGraph (Fin n)) G 0 := by
  rw [SimpleGraph.not_cliqueFree_iff] at h
  obtain ⟨f⟩ := h
  exact ⟨{
    branchSet := fun i => {f i}
    center := fun i => f i
    center_mem := fun _ => Set.mem_singleton _
    branchDisjoint := fun i j hij => by
      exact Set.disjoint_singleton.mpr (fun h => hij (f.injective h))
    branchRadius := fun i x hx => by
      rw [Set.mem_singleton_iff] at hx; subst hx
      exact ⟨.nil, .nil, le_refl _, fun w hw => by
        rw [SimpleGraph.Walk.support_nil, List.mem_cons, List.mem_nil_iff, or_false] at hw
        rw [hw]; exact Set.mem_singleton _⟩
    branchEdge := fun i j hij => by
      exact ⟨f i, Set.mem_singleton _, f j, Set.mem_singleton _,
        (f.toHom.map_adj hij : G.Adj (f i) (f j))⟩ }⟩

/-- A clique in `Gᶜ` gives a distance-1 independent set in `G`. -/
private lemma compl_clique_distIndep {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {n : ℕ}
    (h : ¬Gᶜ.CliqueFree n) :
    ∃ B : Finset V, n ≤ B.card ∧ DistIndependent G 1 ↑B := by
  rw [SimpleGraph.not_cliqueFree_iff] at h
  obtain ⟨f⟩ := h
  refine ⟨Finset.univ.map f.toEmbedding, ?_, ?_⟩
  · simp [Finset.card_map]
  · intro u hu v hv huv p
    simp only [Finset.coe_map, Finset.coe_univ, Set.image_univ, Set.mem_range] at hu hv
    obtain ⟨i, rfl⟩ := hu; obtain ⟨j, rfl⟩ := hv
    have hij : i ≠ j := fun h => huv (congrArg f h)
    have hnadj : ¬G.Adj (f i) (f j) := by
      have := f.toHom.map_adj (hij : (SimpleGraph.completeGraph (Fin n)).Adj i j)
      simp only [SimpleGraph.compl_adj] at this
      exact this.2
    by_contra hle; push_neg at hle
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · exact huv (SimpleGraph.Walk.eq_of_length_eq_zero h0)
    · exact hnadj (SimpleGraph.Walk.adj_of_length_eq_one h1)

/-- From the complete bipartite data K_{t,t}, build K_t as a depth-1 minor. -/
private lemma ktt_gives_minor {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {X Y : Finset V} {t : ℕ}
    (hXY : Disjoint X Y)
    (htX : t ≤ X.card) (htY : t ≤ Y.card)
    (hAdj : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) :
    IsShallowMinor (SimpleGraph.completeGraph (Fin t)) G 1 := by
  obtain ⟨fx, hfx⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin t) (s := X) (by simp; exact htX)
  obtain ⟨fy, hfy⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin t) (s := Y) (by simp; exact htY)
  exact ⟨{
    branchSet := fun i => {fx i, fy i}
    center := fun i => fx i
    center_mem := fun i => Set.mem_insert _ _
    branchDisjoint := fun i j hij => by
      have hfxi : fx i ∈ X := Finset.mem_coe.mp (hfx (Set.mem_range_self i))
      have hfxj : fx j ∈ X := Finset.mem_coe.mp (hfx (Set.mem_range_self j))
      have hfyi : fy i ∈ Y := Finset.mem_coe.mp (hfy (Set.mem_range_self i))
      have hfyj : fy j ∈ Y := Finset.mem_coe.mp (hfy (Set.mem_range_self j))
      exact Set.disjoint_left.mpr fun x hx1 hx2 => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx1 hx2
        rcases hx1 with rfl | rfl <;> rcases hx2 with h | h
        · exact hij (fx.injective h)
        · exact Finset.disjoint_left.mp hXY hfxi (h ▸ hfyj)
        · exact Finset.disjoint_left.mp hXY (h ▸ hfxj) hfyi
        · exact hij (fy.injective h)
    branchRadius := fun i x hx => by
      rcases hx with rfl | rfl
      · exact ⟨.nil, .nil, Nat.zero_le _, fun w hw => by
          rw [SimpleGraph.Walk.support_nil, List.mem_cons, List.mem_nil_iff, or_false] at hw
          rw [hw]; exact Set.mem_insert _ _⟩
      · have hfxi : fx i ∈ X := Finset.mem_coe.mp (hfx (Set.mem_range_self i))
        have hfyi : fy i ∈ Y := Finset.mem_coe.mp (hfy (Set.mem_range_self i))
        have hadj := hAdj (fx i) hfxi (fy i) hfyi
        have hne : fx i ≠ fy i := fun h =>
          Finset.disjoint_left.mp hXY hfxi (h ▸ hfyi)
        exact ⟨.cons hadj .nil,
          ⟨⟨by simp [SimpleGraph.Walk.edges_cons]⟩,
           by simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, hne]⟩,
          le_refl _,
          fun w hw => by
            simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
            rcases hw with rfl | rfl
            · exact Set.mem_insert _ _
            · exact Set.mem_insert_of_mem _ rfl⟩
    branchEdge := fun i j hij => by
      have hfxi : fx i ∈ X := Finset.mem_coe.mp (hfx (Set.mem_range_self i))
      have hfyj : fy j ∈ Y := Finset.mem_coe.mp (hfy (Set.mem_range_self j))
      exact ⟨fx i, Set.mem_insert _ _, fy j, Set.mem_insert_of_mem _ rfl, hAdj _ hfxi _ hfyj⟩ }⟩

/-- The bipartite no-common-neighbor condition implies distance-2 independence
    in `deleteVerts`. -/
private lemma no_common_neighbor_distIndep {V : Type} [DecidableEq V]
    {G : SimpleGraph V}
    {A : Finset V} {S : Finset V}
    (hAindep : (↑A : Set V).Pairwise fun u v => ¬G.Adj u v)
    (_hAS : Disjoint A S)
    (hpair : (↑A : Set V).Pairwise fun u v =>
      ∀ w, w ∉ (↑S : Set V) → ¬(G.Adj u w ∧ G.Adj v w)) :
    DistIndependent (deleteVerts G ↑S) 2 ↑A := by
  intro u hu v hv huv p
  by_contra hle; push_neg at hle
  -- p has length ≤ 2 in deleteVerts G S between distinct u, v ∈ A
  rcases Nat.lt_or_eq_of_le hle with h | h
  · -- length ≤ 1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega : p.length ≤ 1) with h0 | h1
    · exact huv (SimpleGraph.Walk.eq_of_length_eq_zero h0)
    · -- length = 1: adjacent in deleteVerts → adjacent in G → contradiction
      exact hAindep hu hv huv (SimpleGraph.Walk.adj_of_length_eq_one h1).1
  · -- length = 2: there exists an intermediate vertex w
    have h2 : p.length = 2 := by omega
    -- Extract the intermediate vertex from the walk
    have hw0 : 0 < p.length := by omega
    have hw1 : 1 < p.length := by omega
    have hadj1 := p.adj_getVert_succ (by omega : 0 < p.length)
    have hadj2 := p.adj_getVert_succ (by omega : 1 < p.length)
    have hv0 : p.getVert 0 = u := SimpleGraph.Walk.getVert_zero p
    have hv2 : p.getVert 2 = v := by rw [← h2]; exact SimpleGraph.Walk.getVert_length p
    rw [hv0, show 0 + 1 = 1 from rfl] at hadj1
    rw [show 1 + 1 = 2 from rfl, hv2] at hadj2
    let w := p.getVert 1
    exact hpair hu hv huv w hadj1.2.2 ⟨hadj1.1, hadj2.1.symm⟩

/-! ## Main induction -/

/-- Core induction: backward from distance `r` down to distance `r - d`.

At each level, given a set `A` that is distance-`(r-d)` independent in `G - S₀`,
produce a separator `S ⊇ S₀` and a set `B ⊆ A` that is distance-`r` independent
in `G - S`. -/
private lemma stepLemma (C : GraphClass)
    (t : ℕ → ℕ) (ht : ∀ d, HasShallowCliqueBound C d (t d))
    (r : ℕ) : ∀ (d : ℕ),
    ∃ (N : ℕ → ℕ) (s : ℕ),
      ∀ (m : ℕ) {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V),
        C G → ∀ (S₀ A : Finset V),
          Disjoint A S₀ →
          DistIndependent (deleteVerts G ↑S₀) (r - d) ↑A → N m ≤ A.card →
          ∃ (S : Finset V) (B : Finset V),
            S₀ ⊆ S ∧ S.card ≤ S₀.card + s ∧
            (↑B : Set V) ⊆ ↑A \ ↑S ∧ m ≤ B.card ∧
            DistIndependent (deleteVerts G ↑S) r ↑B := by
  intro d
  induction d with
  | zero =>
    -- Base case: r - 0 = r, A is already distance-r independent
    refine ⟨id, 0, fun m V _ _ G _ S₀ A hAS hA hcard => ⟨S₀, A, Finset.Subset.refl _, by omega, ?_, hcard, hA⟩⟩
    intro x hx
    simp only [Set.mem_diff, Finset.mem_coe]
    exact ⟨hx, fun h => absurd h (Finset.disjoint_left.mp hAS hx)⟩
  | succ d ih =>
    obtain ⟨N_next, s_next, hstep_next⟩ := ih
    -- When d+1 > r, r - (d+1) = 0 and r - d = 0; reuse IH
    by_cases hdr : d + 1 ≤ r
    · -- Meaningful step: reduce from distance i = r-(d+1) to i+1 = r-d
      by_cases heven : Even (r - (d + 1))
      · ---- EVEN i = 2j: Odd step via OddStepReduction + Ramsey ----
        obtain ⟨j, hj⟩ := heven
        have hj_eq : 2 * j = r - (d + 1) := by omega
        have hrd : 2 * j + 1 = r - d := by omega
        -- N = Ramsey bound (depends on m, so we use choose after ∀ m)
        refine ⟨fun m => (ramsey (t j + 1) (N_next m)).choose, s_next,
          fun m V _ _ G hG S₀ A hAS hA hAcard => ?_⟩
        classical
        rw [show r - (d + 1) = 2 * j from hj_eq.symm] at hA
        -- Apply OddStepReduction to deleteVerts G S₀
        obtain ⟨W, hWdec, hWfin, H, hHG, hHcard, hlift⟩ :=
          oddStepReduction (deleteVerts G ↑S₀) j A hA
        -- Apply Ramsey to H
        letI := hWdec; letI := hWfin
        haveI : DecidableRel H.Adj := Classical.decRel _
        rcases (ramsey (t j + 1) (N_next m)).choose_spec H
          (le_trans hAcard hHcard) with hclique | hindep
        · -- Clique ⟹ contradiction with ND
          exfalso
          have hKG := shallowMinor_compose (clique_gives_minor hclique)
            (shallowMinor_of_deleteVerts hHG)
          have h_depth : 2 * j * 0 + j + 0 = j := by omega
          rw [h_depth] at hKG
          exact ht j G hG hKG
        · -- Independent set ⟹ lift and apply IH
          obtain ⟨B_ind, hB_card, hB_indep⟩ := compl_clique_distIndep hindep
          obtain ⟨B', hB'sub, hB'card, hB'indep⟩ :=
            hlift (N_next m) ⟨B_ind, hB_card, hB_indep⟩
          rw [hrd] at hB'indep
          have hAS' : Disjoint B' S₀ := by
            rw [Finset.disjoint_left]; intro x hx
            exact Finset.disjoint_left.mp hAS (Finset.mem_coe.mp (hB'sub hx))
          obtain ⟨S_f, B_f, hS₀S, hScard, hBsub_f, hBcard_f, hBindep_f⟩ :=
            hstep_next m G hG S₀ B' hAS' hB'indep hB'card
          exact ⟨S_f, B_f, hS₀S, hScard,
            fun x hx => by
              have := hBsub_f hx
              simp only [Set.mem_diff, Finset.mem_coe] at this ⊢
              exact ⟨Finset.mem_coe.mp (hB'sub this.1), this.2⟩,
            hBcard_f, hBindep_f⟩
      · ---- ODD i = 2j+1: Even step via EvenStepReduction + IterBipRamsey ----
        obtain ⟨j, hj⟩ : ∃ j, r - (d + 1) = 2 * j + 1 := by
          rcases Nat.even_or_odd (r - (d + 1)) with ⟨k, hk⟩ | ⟨k, hk⟩
          · exact absurd ⟨k, hk⟩ heven
          · exact ⟨k, hk⟩
        have hj_eq : 2 * j + 1 = r - (d + 1) := by omega
        have hrd : 2 * (j + 1) = r - d := by omega
        let t_param := t (3 * j + 1) + 1
        refine ⟨fun m => (iterated_bipartite_ramsey (N_next m) t_param).choose,
          s_next + (t_param - 1),
          fun m V _ _ G hG S₀ A hAS hA hAcard => ?_⟩
        classical
        rw [show r - (d + 1) = 2 * j + 1 from hj_eq.symm] at hA
        -- Apply EvenStepReduction
        obtain ⟨W, hWdec, hWfin, H, AW, hHG, hAWcard, hAWnonadj, hlift⟩ :=
          evenStepReduction (deleteVerts G ↑S₀) j A hA
        letI := hWdec; letI := hWfin
        haveI : DecidableRel H.Adj := Classical.decRel _
        -- Build bipartite restriction: keep only edges incident to AW
        let B_side : Finset W := Finset.univ \ AW
        let H_bip : SimpleGraph W :=
          { Adj := fun u v => H.Adj u v ∧ (u ∈ AW ∨ v ∈ AW)
            symm := fun u v ⟨h1, h2⟩ => ⟨H.symm h1, h2.symm⟩
            loopless := ⟨fun u ⟨h, _⟩ => H.loopless.irrefl u h⟩ }
        haveI : DecidableRel H_bip.Adj := Classical.decRel _
        have hBip : ∀ u v, H_bip.Adj u v →
            (u ∈ AW ∧ v ∈ B_side) ∨ (u ∈ B_side ∧ v ∈ AW) := by
          intro u v ⟨hadj, hor⟩
          have hnotboth : ¬(u ∈ AW ∧ v ∈ AW) := fun ⟨hu, hv⟩ =>
            hAWnonadj (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv)
              (fun h => H.loopless.irrefl u (h ▸ hadj)) hadj
          rcases hor with hu | hv
          · left; exact ⟨hu, Finset.mem_sdiff.mpr
              ⟨Finset.mem_univ _, fun hv => hnotboth ⟨hu, hv⟩⟩⟩
          · right; exact ⟨Finset.mem_sdiff.mpr
              ⟨Finset.mem_univ _, fun hu => hnotboth ⟨hu, hv⟩⟩, hv⟩
        have hDisj_bip : Disjoint AW B_side := by
          rw [Finset.disjoint_left]; intro x hx hxB
          exact (Finset.mem_sdiff.mp hxB).2 hx
        -- Apply IterBipRamsey
        rcases (iterated_bipartite_ramsey (N_next m) t_param).choose_spec
          H_bip AW B_side hDisj_bip hBip (le_trans hAcard hAWcard) with
          ⟨A', S_H, hA'sub, hSsub, hA'card, hScard, hA'pair⟩ |
          ⟨M, hMrange⟩ |
          ⟨X, Y, hXsub, hYsub, hXcard, hYcard, hXYadj⟩
        · -- Outcome (a): no common neighbor → dist-2 → lift → IH
          have hA'pair_H : (↑A' : Set W).Pairwise fun u v =>
              ∀ w, w ∉ (↑S_H : Set W) → ¬(H.Adj u w ∧ H.Adj v w) := by
            intro u hu v hv huv w hwS ⟨huw, hvw⟩
            exact hA'pair hu hv huv w hwS
              ⟨⟨huw, Or.inl (hA'sub (Finset.mem_coe.mp hu))⟩,
               ⟨hvw, Or.inl (hA'sub (Finset.mem_coe.mp hv))⟩⟩
          have hA'indep : (↑A' : Set W).Pairwise fun u v => ¬H.Adj u v :=
            Set.Pairwise.mono (Finset.coe_subset.mpr hA'sub) hAWnonadj
          have hA'S_H : Disjoint A' S_H := by
            rw [Finset.disjoint_left]; intro x hx hxS
            exact (Finset.mem_sdiff.mp (hSsub hxS)).2 (hA'sub hx)
          have hA'dist2 := no_common_neighbor_distIndep hA'indep hA'S_H hA'pair_H
          have hSH_AW : Disjoint S_H AW := by
            rw [Finset.disjoint_left]; intro x hx
            exact (Finset.mem_sdiff.mp (hSsub hx)).2
          obtain ⟨S'_V, B', hS'card, hB'sub, hB'S'disj, hB'card, hB'indep⟩ :=
            hlift S_H (N_next m) hSH_AW ⟨A', hA'sub, hA'card, hA'dist2⟩
          rw [deleteVerts_deleteVerts, ← Finset.coe_union] at hB'indep
          rw [hrd] at hB'indep
          have hAS' : Disjoint B' (S₀ ∪ S'_V) := by
            rw [Finset.disjoint_union_right]
            exact ⟨Finset.disjoint_of_subset_left (fun x hx => Finset.mem_coe.mp (hB'sub hx)) hAS,
                   hB'S'disj⟩
          obtain ⟨S_f, B_f, hS₀S, hScard_f, hBsub_f, hBcard_f, hBindep_f⟩ :=
            hstep_next m G hG (S₀ ∪ S'_V) B' hAS' hB'indep hB'card
          exact ⟨S_f, B_f,
            fun x hx => hS₀S (Finset.subset_union_left hx),
            le_trans hScard_f (by
              have := Finset.card_union_le S₀ S'_V
              have : S'_V.card ≤ t_param - 1 := by
                have := hS'card; have := hScard; omega
              omega),
            fun x hx => by
              have := hBsub_f hx
              simp only [Set.mem_diff, Finset.mem_coe] at this ⊢
              exact ⟨Finset.mem_coe.mp (hB'sub (Finset.mem_coe.mpr this.1)), this.2⟩,
            hBcard_f, hBindep_f⟩
        · -- Outcome (b): topological minor → shallow minor → contradiction with ND
          exfalso
          have hKH_bip : IsShallowMinor (SimpleGraph.completeGraph (Fin t_param)) H_bip 1 :=
            shallowTopologicalMinor_toShallowMinor
              (show IsShallowTopologicalMinor
                (SimpleGraph.completeGraph (Fin t_param)) H_bip 1 from ⟨M⟩)
          have hKH : IsShallowMinor (SimpleGraph.completeGraph (Fin t_param)) H 1 :=
            shallowMinor_of_subgraph (fun {u v} h => by
              exact h.1) hKH_bip
          have hHG' := shallowMinor_of_deleteVerts hHG
          have hKG := shallowMinor_compose hKH hHG'
          have h_depth : 2 * j * 1 + j + 1 = 3 * j + 1 := by omega
          rw [h_depth] at hKG
          exact ht (3 * j + 1) G hG hKG
        · -- Outcome (c): K_{t,t} → K_t ⪯_1 H → contradiction with ND
          exfalso
          have hKH : IsShallowMinor (SimpleGraph.completeGraph (Fin t_param)) H 1 :=
            ktt_gives_minor
              (Finset.disjoint_of_subset_left hXsub
                (Finset.disjoint_of_subset_right hYsub hDisj_bip))
              hXcard hYcard
              (fun x hx y hy => (hXYadj x hx y hy).1)
          have hHG' := shallowMinor_of_deleteVerts hHG
          have hKG := shallowMinor_compose hKH hHG'
          have h_depth : 2 * j * 1 + j + 1 = 3 * j + 1 := by omega
          rw [h_depth] at hKG
          exact ht (3 * j + 1) G hG hKG
    · -- d + 1 > r: trivially reuse IH since r-(d+1) = 0 = r-d
      push_neg at hdr
      exact ⟨N_next, s_next, fun m V _ _ G hG S₀ A hAS hA hcard => by
        have h1 : r - (d + 1) = 0 := Nat.sub_eq_zero_of_le (by omega)
        have h2 : r - d = 0 := Nat.sub_eq_zero_of_le (by omega)
        rw [h1] at hA; rw [h2] at hstep_next
        exact hstep_next m G hG S₀ A hAS hA hcard⟩

/-- Lemma 3.4: if a class `C` is nowhere dense, then `C` is uniformly
    quasi-wide. -/
theorem nd_implies_uqw (C : GraphClass) :
    IsNowhereDense C → UniformlyQuasiWide C := by
  intro hND r
  -- Extract clique bounds from ND
  choose t ht using hND
  -- Apply step lemma with d = r (going from distance 0 to distance r)
  obtain ⟨N, s, hstep⟩ := stepLemma C t ht r r
  refine ⟨N, s, fun m V _ _ G hG A hAcard => ?_⟩
  -- Every set is distance-0 independent
  have hA_indep : DistIndependent (deleteVerts G (↑(∅ : Finset V))) (r - r) ↑A := by
    rw [Nat.sub_self, finset_coe_empty]
    exact distIndependent_deleteVerts_empty (distIndependent_zero G ↑A)
  obtain ⟨S, B, _, hScard, hBsub, hBcard, hBindep⟩ :=
    hstep m G hG ∅ A (Finset.disjoint_empty_right A) hA_indep hAcard
  refine ⟨S, B, by simpa using hScard, ?_, hBcard, hBindep⟩
  intro x hx
  have := hBsub (Finset.mem_coe.mpr hx)
  simp only [Set.mem_diff, Finset.mem_coe] at this
  exact Finset.mem_sdiff.mpr this

end Lax5Proofs.Source.Catalog.SparsityLectures.NDImpliesUQW
