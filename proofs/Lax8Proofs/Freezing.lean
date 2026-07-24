import Lax8Proofs.ChiInfra

/-!
# Freezing for the χ-boundedness proof (Lemma 4.1)

This file develops the "freezing" construction used to prove Lemma 4.1 of
Bonamy–Geniet: a graph with a structurally ω-bounded merge sequence of radius-2
width `k` is `k`-colourable.

The construction fixes a single partition `𝒫` (the *frozen* partition) built from
the *maximally unresolved* parts of the merge sequence, together with an index
function.  We show the parts of `𝒫` are independent and the quotient graph is
`(k-1)`-degenerate w.r.t. the index order, then conclude with
`colorable_of_partition_degenerate`.
-/

namespace Lax8Proofs

open Lax8.MergeWidth

open scoped Classical
open Finset

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- A merge sequence is **structurally ω-bounded** if, whenever a part of `Pᵢ`
does not induce an independent set (it contains an edge `ab`), then every edge
incident to a vertex of that part is a resolved pair in `Rᵢ`. -/
def StructurallyOmegaBounded (S : MergeSeq G) : Prop :=
  ∀ i, 1 ≤ i → i ≤ S.length → ∀ u a b : V,
    (S.part i).r u a → (S.part i).r u b → G.Adj a b →
    ∀ w, G.Adj u w → (S.resolved i).Adj u w

/-- Auxiliary: a graph with no edges is `1`-colourable. -/
theorem colorable_one_of_edgeless {W : Type u} (H : SimpleGraph W)
    (hno : ∀ u v, ¬ H.Adj u v) : H.Colorable 1 :=
  ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 1)) (fun {a b} h => (hno a b h).elim)⟩

/-- The part of `Pᵢ` containing `v` is **unresolved** at step `i` if some edge of
`G` incident to a vertex of that part is not a resolved pair in `Rᵢ`. -/
def unresolvedAt (S : MergeSeq G) (i : ℕ) (v : V) : Prop :=
  ∃ a b : V, (S.part i).r v a ∧ G.Adj a b ∧ ¬ (S.resolved i).Adj a b

/-- The **index** of `v`: the largest step `i` (in `[1, length]`) at which the
part of `v` is unresolved, or `0` if there is none. -/
noncomputable def idxU (S : MergeSeq G) (v : V) : ℕ :=
  ((Finset.Icc 1 S.length).filter (fun i => unresolvedAt S i v)).sup id

/-- `unresolvedAt` depends only on the part of `v` at step `i`. -/
theorem unresolvedAt_congr (S : MergeSeq G) {i : ℕ} {v w : V}
    (h : (S.part i).r v w) : unresolvedAt S i v → unresolvedAt S i w := by
  rintro ⟨a, b, hva, hab, hnr⟩
  exact ⟨a, b, Setoid.trans' _ (Setoid.symm' _ h) hva, hab, hnr⟩

/-- The index is at most the length of the sequence. -/
theorem idxU_le_length (S : MergeSeq G) (v : V) : idxU S v ≤ S.length := by
  unfold idxU
  apply Finset.sup_le
  intro i hi
  simp at hi
  exact hi.1.2

/-- If the index of `v` is positive, the part of `v` is unresolved at that step. -/
theorem unresolvedAt_idxU (S : MergeSeq G) (v : V) (h : 1 ≤ idxU S v) :
    unresolvedAt S (idxU S v) v := by
  unfold idxU at h ⊢
  have hne : ((Finset.Icc 1 S.length).filter fun i => unresolvedAt S i v) ≠ ∅ := by
    contrapose! h
    simp [h]
  obtain ⟨a, ha, ha'⟩ := Finset.exists_max_image ((Finset.Icc 1 S.length).filter fun i => unresolvedAt S i v) id (Finset.nonempty_iff_ne_empty.mpr hne)
  have hsup_eq : ((Finset.Icc 1 S.length).filter fun i => unresolvedAt S i v).sup id = a := by
    apply le_antisymm
    · exact Finset.sup_le fun x hx => ha' x hx
    · exact Finset.le_sup (f := id) ha
  rw [hsup_eq]
  exact Finset.mem_filter.mp ha |>.2

/-- Beyond the index, the part of `v` is resolved. -/
theorem not_unresolvedAt_of_gt (S : MergeSeq G) {v : V} {j : ℕ}
    (h : idxU S v < j) (hj : j ≤ S.length) : ¬ unresolvedAt S j v := by
  intro hunres
  have hj1 : 1 ≤ j := by omega
  have hjmem : j ∈ (Finset.Icc 1 S.length).filter (fun i => unresolvedAt S i v) := by
    simp [hj1, hj, hunres]
  have : idxU S v ≥ j := Finset.le_sup (f := id) hjmem
  omega

/-- If `u, v` share a part at step `i = idxU u ≥ 1`, then `idxU v = i` too:
the maximally unresolved parts are well defined. -/
theorem idxU_eq_of_part_rel (S : MergeSeq G) {u v : V} {i : ℕ}
    (hi : idxU S u = i) (h1 : 1 ≤ i) (hr : (S.part i).r u v) : idxU S v = i := by
  have h1' : 1 ≤ idxU S u := hi ▸ h1
  have hunres_u : unresolvedAt S i u := by rw [← hi]; exact unresolvedAt_idxU S u h1'
  have hunres_v : unresolvedAt S i v := unresolvedAt_congr S hr hunres_u
  have hilen : i ≤ S.length := hi ▸ idxU_le_length S u
  have hi_mem : i ∈ (Finset.Icc 1 S.length).filter (fun j => unresolvedAt S j v) := by
    simp [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨h1, hilen⟩, hunres_v⟩
  have h_upper : ∀ j ∈ (Finset.Icc 1 S.length).filter (fun j => unresolvedAt S j v), j ≤ i := by
    intro j hj_mem
    by_contra hj_gt
    push_neg at hj_gt
    simp [Finset.mem_filter] at hj_mem
    have hjlen : j ≤ S.length := hj_mem.1.2
    have hrij : (S.part j).r u v := S.part_mono (by omega) (le_of_lt hj_gt) hjlen hr
    have hunres_j_u : unresolvedAt S j u := unresolvedAt_congr S (@Setoid.symm' V _ u v hrij) hj_mem.2
    exact not_unresolvedAt_of_gt S (hi ▸ hj_gt) hjlen hunres_j_u
  apply le_antisymm
  · simp only [idxU]
    apply Finset.sup_le
    intro j hj
    exact h_upper j hj
  · apply Finset.le_sup (f := id) hi_mem

/-- An unresolved part induces an independent set (uses structural
ω-boundedness). -/
theorem part_indep_of_unresolvedAt (S : MergeSeq G)
    (hSOB : StructurallyOmegaBounded S) {i : ℕ} (hi1 : 1 ≤ i) (hilen : i ≤ S.length)
    {u v : V} (hunres : unresolvedAt S i u) (hr : (S.part i).r u v) : ¬ G.Adj u v := by
  rintro hadj
  obtain ⟨a, b, hau, hab, hnres⟩ := hunres
  by_cases hbu : (S.part i).r u b
  · have hab_part : (S.part i).r a b := Setoid.trans' (S.part i) (Setoid.symm' (S.part i) hau) hbu
    have hrefl : (S.part i).r a a := @Setoid.refl V (S.part i) _
    have hres := hSOB i hi1 hilen a a b hrefl hab_part hab b hab
    exact hnres hres
  · have hau_sym : (S.part i).r a u := Setoid.symm' (S.part i) hau
    have hav : (S.part i).r a v := Setoid.trans' (S.part i) hau_sym hr
    have hres := hSOB i hi1 hilen a u v hau_sym hav hadj b hab
    exact hnres hres

/-- If `idxU u ≥ 1`, then `idxU u < length` (uses structural ω-boundedness: the
top part `⊤` at the last step is resolved whenever `G` has an edge). -/
theorem idxU_lt_length (S : MergeSeq G) (hSOB : StructurallyOmegaBounded S)
    {u : V} (hi : 1 ≤ idxU S u) : idxU S u < S.length := by
  by_contra h
  push_neg at h
  have heq : idxU S u = S.length := Nat.le_antisymm (idxU_le_length S u) h
  have hunres : unresolvedAt S (idxU S u) u := unresolvedAt_idxU S u hi
  rw [heq] at hunres
  obtain ⟨a, b, _ha, hab, hnb⟩ := hunres
  have htop : S.part S.length = ⊤ := S.part_length
  have hrwa : (S.part S.length).r a a := htop ▸ trivial
  have hrwb : (S.part S.length).r a b := htop ▸ trivial
  have := hSOB S.length S.one_le_length (le_refl _) a a b hrwa hrwb hab b hab
  exact hnb this

/-- The **frozen relation**: two vertices are related iff equal, or they share a
part at their (common, positive) index. -/
def frozenRel (S : MergeSeq G) (u v : V) : Prop :=
  u = v ∨ (1 ≤ idxU S u ∧ idxU S u = idxU S v ∧ (S.part (idxU S u)).r u v)

/-- The **frozen partition** as a setoid. -/
noncomputable def frozenSetoid (S : MergeSeq G) : Setoid V where
  r := frozenRel S
  iseqv := by
    constructor
    · intro x; left; rfl
    · rintro x y (rfl | ⟨h1, h2, h3⟩)
      · left; rfl
      · right; exact ⟨h2 ▸ h1, h2.symm, h2 ▸ Setoid.symm' _ h3⟩
    · rintro x y z (rfl | ⟨hx1, hx2, hx3⟩) hyz
      · exact hyz
      · rcases hyz with rfl | ⟨hy1, hy2, hy3⟩
        · exact Or.inr ⟨hx1, hx2, hx3⟩
        · exact Or.inr ⟨hx1, hx2.trans hy2, Setoid.trans' _ hx3 (by rw [hx2]; exact hy3)⟩

/-- For a vertex of positive index, its frozen part equals its part at that
index. -/
theorem frozenPart_eq (S : MergeSeq G) {u : V} (hi : 1 ≤ idxU S u) (v : V) :
    (frozenSetoid S).r u v ↔ (S.part (idxU S u)).r u v := by
  constructor
  · rintro (rfl | ⟨h1, h2, h3⟩)
    · exact (S.part (idxU S u)).iseqv.refl u
    · exact h3
  · intro h
    right
    refine ⟨hi, ?_, h⟩
    exact (idxU_eq_of_part_rel S rfl hi h).symm

/-- The parts of the frozen partition are independent in `G`. -/
theorem frozen_indep (S : MergeSeq G) (hSOB : StructurallyOmegaBounded S) :
    ∀ u v, (frozenSetoid S).r u v → ¬ G.Adj u v := by
  intro u v h
  rcases h with rfl | ⟨hi, _, hr⟩
  · simp
  · have hilen := idxU_le_length S u
    have hunres := unresolvedAt_idxU S u hi
    exact part_indep_of_unresolvedAt S hSOB hi hilen hunres hr

/-- `idxU` is constant on frozen parts. -/
theorem frozen_idx_const (S : MergeSeq G) :
    ∀ u v, (frozenSetoid S).r u v → idxU S u = idxU S v := by
  rintro u v (rfl | ⟨_, h, _⟩)
  · rfl
  · exact h

/-- **Claim 4.2.** For a maximally unresolved part (positive index `i = idxU u`),
there is a vertex `x` with `xy ∈ R_{i+1}` for every `y` in the part. -/
theorem claim42 (S : MergeSeq G) (hSOB : StructurallyOmegaBounded S) {u : V}
    (hu : 1 ≤ idxU S u) :
    ∃ x : V, ∀ y : V, (S.part (idxU S u)).r u y →
      (S.resolved (idxU S u + 1)).Adj x y := by
  set i := idxU S u with hidef
  have hlen : i < S.length := idxU_lt_length S hSOB hu
  have hilen1 : i + 1 ≤ S.length := by omega
  obtain ⟨a, b, hua, hab, hnr⟩ := unresolvedAt_idxU S u hu
  refine ⟨b, ?_⟩
  intro y hy
  have hbnotpart : ¬ (S.part i).r u b := by
    intro hub
    have hab_part : (S.part i).r a b := Setoid.trans' _ (Setoid.symm' _ hua) hub
    have hresab := hSOB i hu (le_of_lt hlen) a a b (Setoid.refl' _ a) hab_part hab b hab
    exact hnr hresab
  have hby : b ≠ y := by
    intro h; apply hbnotpart; rw [h]; exact hy
  by_cases hres : (S.resolved i).Adj b y
  · exact S.resolved_mono hu (by omega) hilen1 hres
  · have hbne_a : b ≠ a := fun h => hab.ne h.symm
    have hnr_ba : ¬ (S.resolved i).Adj b a := fun h => hnr h.symm
    have hpay : (S.part i).r a y := Setoid.trans' _ (Setoid.symm' _ hua) hy
    have huniform := S.uniform hu (le_of_lt hlen) (Setoid.refl' _ b) hpay hbne_a hby hnr_ba hres
    have hGby : G.Adj b y := huniform.mp hab.symm
    have hnotU := not_unresolvedAt_of_gt S (by omega : idxU S u < i + 1) hilen1
    have hyb1 : (S.part (i + 1)).r u y := S.part_mono hu (by omega) hilen1 hy
    have hres_yb : (S.resolved (i + 1)).Adj y b := by
      by_contra hc
      exact hnotU ⟨y, b, hyb1, hGby.symm, hc⟩
    exact hres_yb.symm

/-- `numAccessible` is bounded by the width for steps `i ∈ [2, length]`. -/
theorem numAccessible_le_width (S : MergeSeq G) {r i : ℕ} (h2 : 2 ≤ i)
    (hlen : i ≤ S.length) (v : V) : S.numAccessible r i v ≤ S.width r := by
  simp only [MergeSeq.width]
  refine le_trans ?_ (Finset.le_sup (f := fun i => Finset.univ.sup fun v => S.numAccessible r i v)
    (Finset.mem_Icc.mpr ⟨h2, hlen⟩))
  exact Finset.le_sup (f := fun v => S.numAccessible r i v) (Finset.mem_univ v)

/-- If two vertices of index `≥ i ≥ 1` share a part at step `i`, they share a
frozen part. -/
theorem frozen_of_Pi_rel_of_idx_ge (S : MergeSeq G) {i : ℕ} (hi1 : 1 ≤ i)
    {b b' : V} (hb : i ≤ idxU S b)
    (hr : (S.part i).r b b') : (frozenSetoid S).r b b' := by
  have hjlen : idxU S b ≤ S.length := idxU_le_length S b
  have hpj : (S.part (idxU S b)).r b b' := S.part_mono hi1 hb hjlen hr
  have hb'eq : idxU S b' = idxU S b :=
    idxU_eq_of_part_rel S rfl (le_trans hi1 hb) hpj
  exact Or.inr ⟨le_trans hi1 hb, hb'eq.symm, hpj⟩

/-- Witness for Claim 4.2 in ball form: there is `x` with `u` in the radius-2
`R_{i+1}`-ball of `x`, and any `G`-edge `pb` with `p` in the frozen part of `u`
puts `b` in that ball too. -/
theorem exists_ball_witness (S : MergeSeq G) (hSOB : StructurallyOmegaBounded S)
    {u : V} (hi : 1 ≤ idxU S u) :
    ∃ x : V,
      u ∈ resolvedBall (S.resolved (idxU S u + 1)) 2 x ∧
      ∀ p b : V, (frozenSetoid S).r u p → G.Adj p b →
        b ∈ resolvedBall (S.resolved (idxU S u + 1)) 2 x := by
  obtain ⟨x, hx⟩ := claim42 S hSOB hi
  use x
  refine ⟨?_, fun p b hp hab => ?_⟩
  · -- u is in its own part, so x Adj u
    have hu_part : (S.part (idxU S u)).r u u := (S.part (idxU S u)).iseqv.refl u
    have hxu := hx u hu_part
    exact ⟨SimpleGraph.Walk.cons hxu SimpleGraph.Walk.nil, by simp⟩
  · -- p is frozen-eq to u, so p is in the same part at idxU S u
    have hp_part : (S.part (idxU S u)).r u p := by
      rw [frozenPart_eq S hi] at hp
      exact hp
    have hxp := hx p hp_part
    -- Since the part at idxU S u is unresolved, all edges from vertices in that part are resolved
    have hunres : unresolvedAt S (idxU S u) u := unresolvedAt_idxU S u hi
    -- By structural ω-boundedness, all edges from p are resolved at step idxU S u
    -- idxU S u < S.length, so idxU S u + 1 is valid
    have hlt := idxU_lt_length S hSOB hi
    have hilen_succ : idxU S u + 1 ≤ S.length := by omega
    -- Get the unresolved edge at idxU S u
    obtain ⟨a, b', hau, hab', hnres⟩ := hunres
    -- p is in the same part as u at idxU S u
    have hp_u : (S.part (idxU S u)).r p u := Setoid.symm' (S.part (idxU S u)) hp_part
    -- Either b is in the same part as u, or it's not
    by_cases hb : (S.part (idxU S u)).r u b
    · -- Case 1: b is in the same part as u (and p)
      -- The edge (p, b) is internal to the part. Use hSOB at step idxU S u.
      have hp_b : (S.part (idxU S u)).r p b := Setoid.trans' (S.part (idxU S u)) hp_u hb
      have hpp : (S.part (idxU S u)).r p p := @Setoid.refl V (S.part (idxU S u)) _
      have hp_res : (S.resolved (idxU S u)).Adj p b :=
        hSOB (idxU S u) hi (idxU_le_length S u) p p b hpp hp_b hab b hab
      -- Lift to idxU S u + 1 by monotonicity
      have hpb_succ : (S.resolved (idxU S u + 1)).Adj p b :=
        S.resolved_mono (by omega : 1 ≤ idxU S u) (by omega) hilen_succ hp_res
      -- Walk x -> p -> b of length 2
      exact ⟨SimpleGraph.Walk.cons hxp (SimpleGraph.Walk.cons hpb_succ SimpleGraph.Walk.nil), by simp⟩
    · -- Case 2: b is not in the same part as u
      -- At step idxU S u + 1, ¬unresolvedAt, so all edges from u's part are resolved
      have hp_part_succ : (S.part (idxU S u + 1)).r u p :=
        S.part_mono (by omega : 1 ≤ idxU S u) (by omega) hilen_succ hp_part
      have hnot_unres : ¬unresolvedAt S (idxU S u + 1) u :=
        not_unresolvedAt_of_gt S (by omega) hilen_succ
      unfold unresolvedAt at hnot_unres
      push_neg at hnot_unres
      have hp_res_succ := hnot_unres p b hp_part_succ hab
      -- Walk x -> p -> b of length 2
      exact ⟨SimpleGraph.Walk.cons hxp (SimpleGraph.Walk.cons hp_res_succ SimpleGraph.Walk.nil), by simp⟩


/-- `numAccessible` as the cardinality of a `Finset` image of the resolved ball. -/
theorem numAccessible_eq_image (S : MergeSeq G) (r i : ℕ) (v : V) :
    S.numAccessible r i v =
      ((resolvedBall (S.resolved i) r v).toFinset.image
        (Quotient.mk (S.part (i - 1)))).card := by
  simp [MergeSeq.numAccessible, Set.ncard_eq_toFinset_card']

/-- Degree bound for a **singleton** vertex (`idxU u = 0`): all its `G`-edges are
resolved at step 1, so its `R₂`-ball of radius 2 (whose `P₁`-image has size
`≤ width ≤ k`) contains `u` and all its neighbours, giving `deg(u) + 1 ≤ k`. -/
theorem singleton_degree_bound (S : MergeSeq G) (k : ℕ) (hW : S.width 2 ≤ k)
    (h2len : 2 ≤ S.length) {u : V} (hi : idxU S u = 0) :
    (G.neighborFinset u).card + 1 ≤ k := by
  -- When idxU S u = 0, there is no step where u is in an unresolved part
  -- This means all edges from u are resolved at every step, in particular at step 1
  have hres: ∀ v : V, G.Adj u v → (S.resolved 1).Adj u v := by
    intro v hadj
    by_contra hnres
    have hu_part : (S.part 1).r u u := S.part_one ▸ rfl
    have hunres : unresolvedAt S 1 u := ⟨u, v, hu_part, hadj, hnres⟩
    have hmem : 1 ∈ (Finset.Icc 1 S.length).filter (fun i => unresolvedAt S i u) := by
      simp [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨by omega, hunres⟩
    have : idxU S u ≥ 1 := Finset.le_sup (f := id) hmem
    omega
  -- All neighbors are resolved at step 2 (by monotonicity from step 1)
  have hres2 : ∀ v : V, G.Adj u v → (S.resolved 2).Adj u v := by
    intro v hadj
    exact (S.resolved_mono (by omega) (by omega) (by omega)) (hres v hadj)
  -- The image of neighborFinset ∪ {u} under P₁ has size deg(u) + 1
  -- This is a subset of the numAccessible image at (r=2, i=2)
  have huniv : G.neighborFinset u ∪ {u} ⊆ (resolvedBall (S.resolved 2) 2 u).toFinset := by
    intro v hv
    simp at hv
    rw [Set.mem_toFinset, resolvedBall]
    rcases hv with rfl | hadj
    · exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · exact ⟨SimpleGraph.Walk.cons (hres2 v hadj) (SimpleGraph.Walk.nil), by simp⟩
  -- The quotient map at step 1 is injective since P_1 = ⊥
  have hinj : Function.Injective (Quotient.mk (S.part 1)) := by
    intro x y hxy
    rw [Quotient.eq] at hxy
    rw [S.part_one] at hxy
    exact hxy
  -- The image of neighborFinset ∪ {u} under the quotient map has size deg(u) + 1
  have hcard : ((G.neighborFinset u ∪ {u}).image (Quotient.mk (S.part 1))).card =
      (G.neighborFinset u).card + 1 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  -- The numAccessible 2 2 u counts the distinct P_1 parts in the resolved ball
  have hna_eq : S.numAccessible 2 2 u =
      ((resolvedBall (S.resolved 2) 2 u).toFinset.image (Quotient.mk (S.part 1))).card := by
    rw [numAccessible_eq_image]
  -- The image of neighbors ∪ {u} is a subset of the numAccessible image
  have hsub : ((G.neighborFinset u ∪ {u}).image (Quotient.mk (S.part 1))) ⊆
      ((resolvedBall (S.resolved 2) 2 u).toFinset.image (Quotient.mk (S.part 1))) := by
    apply Finset.image_subset_image
    exact huniv
  -- Put it all together
  calc (G.neighborFinset u).card + 1 = ((G.neighborFinset u ∪ {u}).image (Quotient.mk (S.part 1))).card := hcard.symm
    _ ≤ ((resolvedBall (S.resolved 2) 2 u).toFinset.image (Quotient.mk (S.part 1))).card := Finset.card_le_card hsub
    _ = S.numAccessible 2 2 u := hna_eq.symm
    _ ≤ S.width 2 := numAccessible_le_width S (by omega) (by omega) u
    _ ≤ k := hW

/-- **Generic back-degree counting.**  If `g : V → β` maps every `G`-edge `pb`
with `p` frozen-equivalent to `u` into `T`, and is "frozen-injective" on the
relevant edge endpoints, then the number of quotient-neighbour parts of `⟦u⟧` of
index `≥ idxU u` is at most `T.card`. -/
theorem card_frozen_backneighbors_le {β : Type u} (S : MergeSeq G) (u : V)
    (T : Finset β) (g : V → β)
    (hmaps : ∀ p b : V, Quotient.mk (frozenSetoid S) p = Quotient.mk (frozenSetoid S) u →
        G.Adj p b → g b ∈ T)
    (hinj : ∀ p1 b1 p2 b2 : V,
        Quotient.mk (frozenSetoid S) p1 = Quotient.mk (frozenSetoid S) u → G.Adj p1 b1 →
        idxU S u ≤ idxU S b1 →
        Quotient.mk (frozenSetoid S) p2 = Quotient.mk (frozenSetoid S) u → G.Adj p2 b2 →
        idxU S u ≤ idxU S b2 →
        g b1 = g b2 →
        Quotient.mk (frozenSetoid S) b1 = Quotient.mk (frozenSetoid S) b2) :
    (((quotientGraph G (frozenSetoid S)).neighborFinset
      (Quotient.mk (frozenSetoid S) u)).filter
      (fun q => ∃ a, Quotient.mk (frozenSetoid S) a = q ∧ idxU S u ≤ idxU S a)).card
      ≤ T.card := by
  let S' := ((quotientGraph G (frozenSetoid S)).neighborFinset
      (Quotient.mk (frozenSetoid S) u)).filter
      (fun q => ∃ a, Quotient.mk (frozenSetoid S) a = q ∧ idxU S u ≤ idxU S a)
  -- For each q ∈ S', there exists a neighbor edge (p, b) with Quotient.mk p = u, Quotient.mk b = q
  -- Define a function that picks b and returns g b
  have hchoice : ∀ q ∈ S', ∃ b : V, ∃ p : V, Quotient.mk (frozenSetoid S) p = Quotient.mk (frozenSetoid S) u ∧
      Quotient.mk (frozenSetoid S) b = q ∧ G.Adj p b := by
    intro q hq
    have hmem : q ∈ (quotientGraph G (frozenSetoid S)).neighborFinset (Quotient.mk (frozenSetoid S) u) :=
      Finset.mem_filter.mp hq |>.1
    rw [SimpleGraph.mem_neighborFinset] at hmem
    obtain ⟨p, b, hp, hb, hab⟩ := hmem.2
    exact ⟨b, p, hp, hb, hab⟩
  -- Define f : S' → T using Classical.choose
  let choiceB : ∀ q : Quotient (frozenSetoid S), q ∈ S' → V := fun q hq => (hchoice q hq).choose
  let choiceP : ∀ q : Quotient (frozenSetoid S), q ∈ S' → V := fun q hq => (hchoice q hq).choose_spec.choose
  have hchoice_spec : ∀ q : Quotient (frozenSetoid S), ∀ hq : q ∈ S', Quotient.mk (frozenSetoid S) (choiceP q hq) = Quotient.mk (frozenSetoid S) u ∧
      Quotient.mk (frozenSetoid S) (choiceB q hq) = q ∧ G.Adj (choiceP q hq) (choiceB q hq) :=
    fun q hq => (hchoice q hq).choose_spec.choose_spec
  -- The function f : S' → T
  let f : ∀ q : Quotient (frozenSetoid S), q ∈ S' → T := fun q hq =>
    ⟨g (choiceB q hq), hmaps (choiceP q hq) (choiceB q hq) ((hchoice_spec q hq).1) ((hchoice_spec q hq).2.2)⟩
  -- Prove f is injective
  have hinj_f : ∀ q1 hq1 q2 hq2, f q1 hq1 = f q2 hq2 → q1 = q2 := by
    intro q1 hq1 q2 hq2 hef
    have hg_eq : g (choiceB q1 hq1) = g (choiceB q2 hq2) := by
      have := hef
      exact Subtype.ext_iff.mp this
    -- Extract index bounds from membership in S'
    have hq1' := hq1
    have hq2' := hq2
    rw [Finset.mem_filter] at hq1' hq2'
    obtain ⟨hq1_nbr, a1, ha1_eq, ha1_idx⟩ := hq1'
    obtain ⟨hq2_nbr, a2, ha2_eq, ha2_idx⟩ := hq2'
    -- Use frozen_idx_const to get idxU bounds for choiceB
    have hidx1 : idxU S (choiceB q1 hq1) = idxU S a1 := by
      rcases Quotient.exact ((hchoice_spec q1 hq1).2.1.trans ha1_eq.symm) with rfl | ⟨_, heq, _⟩
      · rfl
      · exact heq
    have hidx2 : idxU S (choiceB q2 hq2) = idxU S a2 := by
      rcases Quotient.exact ((hchoice_spec q2 hq2).2.1.trans ha2_eq.symm) with rfl | ⟨_, heq, _⟩
      · rfl
      · exact heq
    have hidx1' : idxU S u ≤ idxU S (choiceB q1 hq1) := by rw [hidx1]; exact ha1_idx
    have hidx2' : idxU S u ≤ idxU S (choiceB q2 hq2) := by rw [hidx2]; exact ha2_idx
    -- Apply hinj to get ⟦choiceB q1 hq1⟧ = ⟦choiceB q2 hq2⟧
    have hq_eq : Quotient.mk (frozenSetoid S) (choiceB q1 hq1) = Quotient.mk (frozenSetoid S) (choiceB q2 hq2) :=
      hinj (choiceP q1 hq1) (choiceB q1 hq1) (choiceP q2 hq2) (choiceB q2 hq2)
        (hchoice_spec q1 hq1).1 (hchoice_spec q1 hq1).2.2 hidx1'
        (hchoice_spec q2 hq2).1 (hchoice_spec q2 hq2).2.2 hidx2' hg_eq
    rw [(hchoice_spec q1 hq1).2.1, (hchoice_spec q2 hq2).2.1] at hq_eq
    exact hq_eq
  -- Now use injectivity to bound cardinality
  -- Define a non-dependent function to Option β
  let f'' : Quotient (frozenSetoid S) → Option β := fun q =>
    if hq : q ∈ S' then some (f q hq : β) else none
  have hcard : S'.card ≤ T.card := by
    have hmaps : ∀ q ∈ S', f'' q ∈ T.image (fun x => some x) := by
      intro q hq
      simp [f'', hq]
    have hinj_on : Set.InjOn f'' (S' : Set _) := by
      intro a ha b hb hab
      have ha' : a ∈ S' := ha
      have hb' : b ∈ S' := hb
      simp only [f''] at hab
      rw [dif_pos ha', dif_pos hb'] at hab
      exact hinj_f a ha' b hb' (Subtype.val_inj.mp (Option.some.inj hab))
    calc S'.card = (S'.image f'').card := (Finset.card_image_of_injOn hinj_on).symm
      _ ≤ (T.image (fun x => some x)).card := Finset.card_le_card (Finset.image_subset_iff.mpr hmaps)
      _ = T.card := Finset.card_image_of_injective _ (Option.some_injective _)
  exact hcard


/-- Back-degree bound for a **singleton** vertex (`idxU u = 0`): its `G`-degree,
hence its number of quotient-neighbours, is at most `k - 1`. -/
theorem singleton_backdeg (S : MergeSeq G) (k : ℕ) (hk : 1 ≤ k)
    (hW : S.width 2 ≤ k) (h2len : 2 ≤ S.length) {u : V} (hi : idxU S u = 0) :
    (((quotientGraph G (frozenSetoid S)).neighborFinset
      (Quotient.mk (frozenSetoid S) u)).filter
      (fun q => ∃ a, Quotient.mk (frozenSetoid S) a = q ∧ idxU S u ≤ idxU S a)).card
      ≤ k - 1 := by
  have hdeg : (G.neighborFinset u).card + 1 ≤ k := singleton_degree_bound S k hW h2len hi
  refine le_trans (card_frozen_backneighbors_le S u (G.neighborFinset u) id ?_ ?_) (by omega)
  · -- hmaps: with `idxU u = 0`, `⟦p⟧ = ⟦u⟧` forces `p = u`.
    intro p b hpu hadj
    have hpeq : p = u := by
      rcases Quotient.exact hpu with h | ⟨hle, heq, _⟩
      · exact h
      · rw [hi] at heq; omega
    subst hpeq
    simpa [SimpleGraph.mem_neighborFinset] using hadj
  · -- hinj: `g = id`.
    intro p1 b1 p2 b2 _ _ _ _ _ _ hg
    exact congrArg (Quotient.mk (frozenSetoid S)) (by simpa using hg)

/-- Back-degree bound for a vertex of **positive index** (`idxU u ≥ 1`): the
number of quotient-neighbour parts of index `≥ idxU u` is at most `k - 1`. -/
theorem index_pos_backdeg (S : MergeSeq G) (hSOB : StructurallyOmegaBounded S)
    (k : ℕ) (hk : 1 ≤ k) (hW : S.width 2 ≤ k) {u : V} (hi : 1 ≤ idxU S u) :
    (((quotientGraph G (frozenSetoid S)).neighborFinset
      (Quotient.mk (frozenSetoid S) u)).filter
      (fun q => ∃ a, Quotient.mk (frozenSetoid S) a = q ∧ idxU S u ≤ idxU S a)).card
      ≤ k - 1 := by
  obtain ⟨x, hxu, hxball⟩ := exists_ball_witness S hSOB hi
  have hlt : idxU S u < S.length := idxU_lt_length S hSOB hi
  set i := idxU S u with hidef
  -- Target finset: `Pᵢ`-classes accessible from `x`, minus the class of `u`.
  set img : Finset (Quotient (S.part i)) :=
    (resolvedBall (S.resolved (i + 1)) 2 x).toFinset.image (Quotient.mk (S.part i)) with himgdef
  set t0 : Quotient (S.part i) := Quotient.mk (S.part i) u with ht0def
  have ht0mem : t0 ∈ img := by
    rw [himgdef, Finset.mem_image]
    exact ⟨u, by simpa using hxu, rfl⟩
  have hidx : i + 1 - 1 = i := by omega
  have himg_card : img.card = S.numAccessible 2 (i + 1) x := by
    rw [himgdef, numAccessible_eq_image, hidx]
  have hnum : S.numAccessible 2 (i + 1) x ≤ k :=
    le_trans (numAccessible_le_width S (by omega) (by omega) x) hW
  refine le_trans (card_frozen_backneighbors_le S u (img \ {t0})
    (Quotient.mk (S.part i)) ?hmaps ?hinj) ?_
  case hmaps =>
    intro p b hpu hadj
    have hrup : (frozenSetoid S).r u p := Setoid.symm' _ (Quotient.exact hpu)
    have hbball : b ∈ resolvedBall (S.resolved (i + 1)) 2 x := hxball p b hrup hadj
    have hbimg : Quotient.mk (S.part i) b ∈ img := by
      rw [himgdef, Finset.mem_image]; exact ⟨b, by simpa using hbball, rfl⟩
    have hne : Quotient.mk (S.part i) b ≠ t0 := by
      intro heq
      have hrub : (S.part i).r u b := Setoid.symm' _ (Quotient.exact heq)
      have : (frozenSetoid S).r p b := by
        have hfb : (frozenSetoid S).r u b := by
          rw [frozenPart_eq S hi]; exact hrub
        exact Setoid.trans' _ (Quotient.exact hpu) hfb
      exact frozen_indep S hSOB p b this hadj
    exact Finset.mem_sdiff.mpr ⟨hbimg, by simpa using hne⟩
  case hinj =>
    intro p1 b1 p2 b2 _ _ hb1 _ _ _ hg
    have hr : (S.part i).r b1 b2 := Quotient.exact hg
    exact Quotient.sound (frozen_of_Pi_rel_of_idx_ge S hi hb1 hr)
  · rw [← Finset.erase_eq, Finset.card_erase_of_mem ht0mem, himg_card]
    omega

/-- **Lemma 4.1.** A graph with a structurally ω-bounded merge sequence of
radius-2 width `k` (with `k ≥ 1`) is `k`-colourable. -/
theorem colorable_of_structurallyOmegaBounded (k : ℕ) (hk : 1 ≤ k) (S : MergeSeq G)
    (hS : S.width 2 ≤ k) (hSOB : StructurallyOmegaBounded S) : G.Colorable k := by
  -- Handle the degenerate case `length = 1` (`⊥ = ⊤`, so `V` is a subsingleton).
  rcases Nat.lt_or_ge S.length 2 with hlen | hlen
  · -- length ≤ 1, so `part 1 = ⊥ = ⊤`, hence any two vertices are equal.
    have hlen1 : S.length = 1 := le_antisymm (by omega) S.one_le_length
    have hbot : S.part 1 = ⊥ := S.part_one
    have htop : S.part 1 = ⊤ := by rw [← hlen1]; exact S.part_length
    have hsub : Subsingleton V := by
      constructor
      intro a b
      have : (⊤ : Setoid V).r a b := trivial
      rw [← htop, hbot] at this
      exact this
    refine (colorable_one_of_edgeless G ?_).mono hk
    intro u v huv
    exact absurd (Subsingleton.elim u v) huv.ne
  · -- Main case: apply the partition-degeneracy principle.
    have hcol : G.Colorable (k - 1 + 1) := by
      refine colorable_of_partition_degenerate G (frozenSetoid S) (idxU S) (k - 1)
        (frozen_indep S hSOB) (frozen_idx_const S) ?_
      intro u
      rcases Nat.eq_zero_or_pos (idxU S u) with h0 | hpos
      · exact singleton_backdeg S k hk hS hlen h0
      · exact index_pos_backdeg S hSOB k hk hS hpos
    rwa [Nat.sub_add_cancel hk] at hcol

end Lax8Proofs
