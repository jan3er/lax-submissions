import Lax9Proofs.MergeWidthBasic

/-!
# Restriction of merge sequences to the blocks of a partition

Given a finite simple graph $G$ with a merge sequence $S$ and a partition $Q$
(a setoid) of its vertices, consider the graph $H = G ⊓ blockGraph Q$ whose edges
are exactly the edges of $G$ lying inside a single $Q$-block.  (Equivalently $H$
is the disjoint union of the induced subgraphs $G[block]$.)

We build a merge sequence for $H$ of radius-$r$ width at most $max (S.width r) 1$:
refine each partition $Pᵢ$ of $S$ by $Q$, keep only the resolved pairs of $Rᵢ$
lying inside a $Q$-block, and append a final step merging everything to $⊤$ (all
in-block pairs resolved).  This shows merge-width does not increase under this
"disjoint union of induced subgraphs" operation.
-/

namespace Lax9Proofs

open Lax9.MergeWidth

open scoped Classical

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- The graph of distinct pairs lying inside a common $Q$-block. -/
def blockGraph (Q : Setoid V) : SimpleGraph V := SimpleGraph.fromRel (fun x y => Q.r x y)

@[simp] theorem blockGraph_adj (Q : Setoid V) (x y : V) :
    (blockGraph Q).Adj x y ↔ x ≠ y ∧ Q.r x y := by
  rw [blockGraph, SimpleGraph.fromRel_adj]
  refine and_congr_right (fun _ => ?_)
  exact ⟨fun h => h.elim id (fun h => Q.iseqv.symm h), fun h => Or.inl h⟩

/-- The within-block restriction of $G$ by $Q$: edges of $G$ inside a $Q$-block. -/
def restrictGraph (G : SimpleGraph V) (Q : Setoid V) : SimpleGraph V :=
  G ⊓ blockGraph Q

@[simp] theorem restrictGraph_adj (G : SimpleGraph V) (Q : Setoid V) (x y : V) :
    (restrictGraph G Q).Adj x y ↔ G.Adj x y ∧ Q.r x y := by
  simp only [restrictGraph, SimpleGraph.inf_adj, blockGraph_adj]
  constructor
  · rintro ⟨hg, _, hq⟩; exact ⟨hg, hq⟩
  · rintro ⟨hg, hq⟩; exact ⟨hg, hg.ne, hq⟩

/-- The refined partition at step $i$: $Pᵢ ⊓ Q$ up to $length$, then $⊤$. -/
noncomputable def rpart (S : MergeSeq G) (Q : Setoid V) (i : ℕ) : Setoid V :=
  if i ≤ S.length then S.part i ⊓ Q else ⊤

/-- The restricted resolved graph at step $i$: $Rᵢ$ inside blocks, then all
in-block pairs. -/
noncomputable def rresolved (S : MergeSeq G) (Q : Setoid V) (i : ℕ) : SimpleGraph V :=
  if i ≤ S.length then S.resolved i ⊓ blockGraph Q else blockGraph Q

theorem rpart_one (S : MergeSeq G) (Q : Setoid V) : rpart S Q 1 = ⊥ := by
  unfold rpart
  rw [if_pos S.one_le_length, S.part_one, bot_inf_eq]

theorem rpart_length (S : MergeSeq G) (Q : Setoid V) :
    rpart S Q (S.length + 1) = ⊤ := by
  unfold rpart; rw [if_neg (by omega)]

theorem rpart_mono (S : MergeSeq G) (Q : Setoid V) :
    ∀ ⦃i j⦄, 1 ≤ i → i ≤ j → j ≤ S.length + 1 → rpart S Q i ≤ rpart S Q j := by
  intro i j hi hij hj
  unfold rpart
  by_cases hjl : j ≤ S.length
  · rw [if_pos (le_trans hij hjl), if_pos hjl]
    intro x y hxy
    exact ⟨S.part_mono hi hij hjl hxy.1, hxy.2⟩
  · rw [if_neg hjl]
    intro x y _; trivial

theorem rresolved_mono (S : MergeSeq G) (Q : Setoid V) :
    ∀ ⦃i j⦄, 1 ≤ i → i ≤ j → j ≤ S.length + 1 → rresolved S Q i ≤ rresolved S Q j := by
  intro i j hi hij hj
  unfold rresolved
  by_cases hjl : j ≤ S.length
  · rw [if_pos (le_trans hij hjl), if_pos hjl]
    intro x y hxy
    exact ⟨S.resolved_mono hi hij hjl hxy.1, hxy.2⟩
  · rw [if_neg hjl]
    by_cases hil : i ≤ S.length
    · rw [if_pos hil]; exact inf_le_right
    · rw [if_neg hil]

/-- Uniformity of the restricted sequence. -/
theorem runiform (S : MergeSeq G) (Q : Setoid V) :
    ∀ ⦃i⦄, 1 ≤ i → i ≤ S.length + 1 → ∀ ⦃x x' y y' : V⦄,
      (rpart S Q i).r x x' → (rpart S Q i).r y y' → x ≠ y → x' ≠ y' →
      ¬ (rresolved S Q i).Adj x y → ¬ (rresolved S Q i).Adj x' y' →
      ((restrictGraph G Q).Adj x y ↔ (restrictGraph G Q).Adj x' y') := by
  intro i hi1 hi2 x x' y y' hxx' hyy' hne_xyz hne_x'y' hnr_xy hnr_x'y'
  unfold rpart at hxx' hyy'
  unfold rresolved at hnr_xy hnr_x'y'
  by_cases hil : i ≤ S.length
  · rw [if_pos hil] at hxx' hyy' hnr_xy hnr_x'y'
    have hxx'' : S.part i x x' ∧ Q.r x x' := hxx'
    have hyy'' : S.part i y y' ∧ Q.r y y' := hyy'
    simp only [SimpleGraph.inf_adj] at hnr_xy hnr_x'y'
    push_neg at hnr_xy hnr_x'y'
    by_cases hQ_xy : Q.r x y
    · by_cases hQ_x'y' : Q.r x' y'
      · -- Both pairs are in the same Q-block, use S.uniform
        have hnr_S_xy : ¬(S.resolved i).Adj x y := by
          intro hadj
          exact hnr_xy hadj ⟨hne_xyz, Or.inl hQ_xy⟩
        have hnr_S_x'y' : ¬(S.resolved i).Adj x' y' := by
          intro hadj
          exact hnr_x'y' hadj ⟨hne_x'y', Or.inl hQ_x'y'⟩
        have hadj_xy : (restrictGraph G Q).Adj x y ↔ G.Adj x y := by
          simp [restrictGraph_adj, hne_xyz, hQ_xy]
        have hadj_x'y' : (restrictGraph G Q).Adj x' y' ↔ G.Adj x' y' := by
          simp [restrictGraph_adj, hne_x'y', hQ_x'y']
        rw [hadj_xy, hadj_x'y', S.uniform hi1 hil hxx''.1 hyy''.1 hne_xyz hne_x'y' hnr_S_xy hnr_S_x'y']
      · -- Q x y holds but Q x' y' doesn't: derive contradiction from transitivity
        have h1 : Q.r x x' := hxx''.2
        have h2 : Q.r y y' := hyy''.2
        have h_x'y : Q.r x' y := Q.trans (Q.symm h1) hQ_xy
        have h_x'y' : Q.r x' y' := Q.trans h_x'y h2
        exact absurd h_x'y' hQ_x'y'
    · -- Q x y doesn't hold: both sides are false
      have h1 : Q.r x x' := hxx''.2
      have h2 : Q.r y y' := hyy''.2
      refine iff_of_false (fun h => ?_) (fun h => ?_)
      · simp only [restrictGraph_adj] at h
        exact absurd h.2 hQ_xy
      · -- If (blockGraph Q).Adj x' y' holds, derive Q x y by transitivity
        simp [blockGraph_adj] at h
        have hQ_x'y' : Q.r x' y' := h.2
        have hQ_xy' : Q.r x y' := Q.trans h1 hQ_x'y'
        have hQ_yx' : Q.r y' y := Q.symm h2
        exact hQ_xy (Q.trans hQ_xy' hQ_yx')
  · rw [if_neg (by simpa using hil)] at hnr_xy hnr_x'y'
    simp only [blockGraph_adj] at hnr_xy hnr_x'y'
    push_neg at hnr_xy hnr_x'y'
    refine iff_of_false (fun h => ?_) (fun h => ?_)
    · exact hnr_xy h.2.1 (h.2.2.elim id fun h => Q.symm h)
    · exact hnr_x'y' h.2.1 (h.2.2.elim id fun h => Q.symm h)


/-- The restricted merge sequence: refine each partition by $Q$, keep resolved
pairs inside blocks, and add a final step merging to $⊤$. -/
noncomputable def restrictSeq (S : MergeSeq G) (Q : Setoid V) :
    MergeSeq (restrictGraph G Q) where
  length := S.length + 1
  one_le_length := by omega
  part := rpart S Q
  resolved := rresolved S Q
  part_one := rpart_one S Q
  part_length := rpart_length S Q
  part_mono := rpart_mono S Q
  resolved_mono := rresolved_mono S Q
  uniform := runiform S Q

/-- The restricted sequence has radius-$r$ width at most $max (S.width r) 1$. -/
theorem restrictSeq_width_le (S : MergeSeq G) (Q : Setoid V) (r : ℕ) :
    (restrictSeq S Q).width r ≤ max (S.width r) 1 := by
  unfold MergeSeq.width
  simp only [restrictSeq]
  -- Need to show sup over Icc 2 (S.length + 1) ≤ max (sup over Icc 2 S.length) 1
  apply Finset.sup_le
  intro i hi
  by_cases h : i ≤ S.length
  · -- Case i ∈ [2, S.length]: bound by S.width r
    refine le_trans ?_ (le_max_left _ _)
    apply Finset.sup_le
    intro v _
    -- rpart S Q (i-1) = S.part (i-1) ⊓ Q
    -- There's a surjection Quotient (S.part (i-1) ⊓ Q) → Quotient (S.part (i-1))
    -- So numAccessible for restrictSeq ≤ numAccessible for S
    have h_bound : (restrictSeq S Q).numAccessible r i v ≤ S.numAccessible r i v := by
      -- unfold numAccessible
      unfold MergeSeq.numAccessible
      -- Simplify (restrictSeq S Q).resolved i
      have hresolved_eq : (restrictSeq S Q).resolved i = rresolved S Q i := rfl
      rw [hresolved_eq]
      -- Simplify rresolved for i ≤ S.length
      have hrresolved : rresolved S Q i = S.resolved i ⊓ blockGraph Q := by
        unfold rresolved
        rw [if_pos h]
      rw [hrresolved]
      -- Simplify rpart for i-1 ≤ S.length
      have hrpart : rpart S Q (i - 1) = S.part (i - 1) ⊓ Q := by
        unfold rpart
        rw [if_pos (by omega : i - 1 ≤ S.length)]
      -- Define quotient map q : Quotient (S.part (i-1) ⊓ Q) → Quotient (S.part (i-1))
      set s := S.part (i - 1) with hs_def
      -- q is induced by id : V → V
      let q : Quotient (s ⊓ Q) → Quotient s := Quotient.lift (Quotient.mk s) (fun a b hab => Quotient.sound hab.1)
      -- q is well-defined and satisfies q(⟦a⟧) = ⟦a⟧
      have hq : ∀ a : V, q (Quotient.mk (s ⊓ Q) a) = Quotient.mk s a := by
        intro a; rfl
      -- The LHS image under q equals the RHS image of ball₁
      set ball₁ := resolvedBall (S.resolved i ⊓ blockGraph Q) r v with hball₁
      set ball₂ := resolvedBall (S.resolved i) r v with hball₂
      -- All vertices in ball₁ are Q-equivalent to v (connected by blockGraph Q edges)
      have h_Q_equiv : ∀ u ∈ ball₁, Q u v := by
        intro u ⟨w, _⟩
        -- Each edge in blockGraph Q connects Q-equivalent vertices
        have h_edge_Q : ∀ x y, (blockGraph Q).Adj x y → Q x y := by
          intro x y hadj
          rw [blockGraph_adj] at hadj
          exact hadj.2
        -- Convert walk from subgraph to blockGraph
        have h_inf_right : ∀ a b, (S.resolved i ⊓ blockGraph Q).Adj a b → (blockGraph Q).Adj a b :=
          fun a b h => h.2
        let hincl : (S.resolved i ⊓ blockGraph Q) →g blockGraph Q := {
          toFun := id
          map_rel' := @h_inf_right
        }
        have h_hincl_v : hincl v = v := rfl
        have h_hincl_u : hincl u = u := rfl
        let w' := w.map hincl
        -- Walk in blockGraph Q implies Q relation
        have walk_implies_Q : Q v u := by
          rw [h_hincl_v, h_hincl_u] at w'
          refine @SimpleGraph.Walk.recOn _ (blockGraph Q) (fun x y _ => Q x y) v u w' ?_ ?_
          · intro u; exact Q.iseqv.refl u
          · intro a b c hadj _ ih; exact Q.trans (h_edge_Q a b hadj) ih
        exact Q.symm walk_implies_Q
      have h_ball_sub : ball₁ ⊆ ball₂ := by
        intro u ⟨w, hw⟩
        have hsub : (S.resolved i ⊓ blockGraph Q) ≤ S.resolved i := inf_le_left
        let f : (S.resolved i ⊓ blockGraph Q) →g S.resolved i := {
          toFun := id
          map_rel' := by intro a b h; exact hsub h
        }
        exact ⟨w.map f, by
          have hlen : (w.map f).length = w.length :=
            SimpleGraph.Walk.length_map f w
          exact hlen.symm ▸ hw⟩
      -- q '' LHS_image = RHS_image of ball₁
      have h_q_image : q '' ((fun u => Quotient.mk (s ⊓ Q) u) '' ball₁) = (fun u => Quotient.mk s u) '' ball₁ := by
        ext x
        simp only [Set.mem_image]
        constructor
        · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
          exact ⟨u, hu, hq u⟩
        · rintro ⟨u, hu, rfl⟩
          exact ⟨Quotient.mk (s ⊓ Q) u, ⟨u, hu, rfl⟩, hq u⟩
      -- RHS_image of ball₁ ⊆ RHS_image of ball₂
      have h_rhs_sub : (fun u => Quotient.mk s u) '' ball₁ ⊆ (fun u => Quotient.mk s u) '' ball₂ :=
        Set.image_mono h_ball_sub
      -- So q '' LHS ⊆ RHS
      have h_q_lhs_sub_rhs : q '' ((fun u => Quotient.mk (s ⊓ Q) u) '' ball₁) ⊆ (fun u => Quotient.mk s u) '' ball₂ :=
        h_q_image ▸ h_rhs_sub
      -- q is injective on LHS_image: if ⟦a₁⟧ and ⟦a₂⟧ map to same, then a₁ ~ a₂ in s and both ~ v in Q
      -- So a₁ ~ a₂ in s ⊓ Q, hence ⟦a₁⟧ = ⟦a₂⟧
      have h_q_inj : Set.InjOn q ((fun u => Quotient.mk (s ⊓ Q) u) '' ball₁) := by
        intro x hx y hy hxy
        simp only [Set.mem_image] at hx hy
        obtain ⟨a₁, ha₁, rfl⟩ := hx
        obtain ⟨a₂, ha₂, rfl⟩ := hy
        -- hxy : q ⟦a₁⟧ = q ⟦a₂⟧ means ⟦a₁⟧_s = ⟦a₂⟧_s, so s a₁ a₂
        rw [hq] at hxy
        have has : s a₁ a₂ := (Quotient.eq.mp hxy)
        -- Both a₁ and a₂ are in ball₁, so they're Q-equivalent to v
        have ha₁Q : Q a₁ v := h_Q_equiv a₁ ha₁
        have ha₂Q : Q a₂ v := h_Q_equiv a₂ ha₂
        have ha₁a₂_Q : Q a₁ a₂ := Q.trans ha₁Q (Q.symm ha₂Q)
        exact Quotient.eq.mpr ⟨has, ha₁a₂_Q⟩
      -- ncard (LHS) = ncard (q '' LHS) since q is injective on LHS
      -- and ncard (q '' LHS) ≤ ncard (RHS) since q '' LHS ⊆ RHS
      have hLHS : ((fun u => Quotient.mk (s ⊓ Q) u) '' ball₁) = ((fun u => ⟦u⟧) '' ball₁) := rfl
      refine le_trans ?_ (Set.ncard_le_ncard h_rhs_sub)
      rw [← h_q_image]
      apply le_of_eq
      convert (Set.ncard_image_of_injOn h_q_inj).symm
    calc (restrictSeq S Q).numAccessible r i v
        ≤ S.numAccessible r i v := h_bound
      _ ≤ S.width r := by
          unfold MergeSeq.width
          refine Finset.le_sup_of_le (Finset.mem_Icc.mpr ⟨Finset.mem_Icc.mp hi |>.1, h⟩) ?_
          exact Finset.le_sup (Finset.mem_univ v)
  · -- Case i = S.length + 1: bound by 1
    have hlb := Finset.mem_Icc.mp hi |>.1
    have hub := Finset.mem_Icc.mp hi |>.2
    have hi_eq : i = S.length + 1 := by omega
    subst hi_eq
    -- At step S.length + 1, part S.length = ⊤ ⊓ Q = Q
    -- resolved (S.length + 1) = blockGraph Q
    -- The accessible parts are subsets of Q-blocks, so at most 1
    apply Nat.le_trans (Finset.sup_le (fun v _ => show _ ≤ 1 by
      -- numAccessible counts parts of Q reachable via blockGraph Q
      -- But blockGraph Q only connects vertices in the same Q-block
      -- So there's at most 1 accessible part (the one containing v)
      unfold MergeSeq.numAccessible
      -- The resolved ball in blockGraph Q only reaches same Q-block
      have h_ball : ∀ u ∈ resolvedBall (blockGraph Q) r v, (Q : Setoid V).r v u := by
        intro u ⟨w, hw⟩
        -- Each edge in blockGraph Q connects Q-equivalent vertices
        -- By transitivity along the walk, Q v u
        have h_eq : ∀ x y, (blockGraph Q).Adj x y → Q x y := by
          intro x y hadj
          rw [blockGraph_adj] at hadj
          exact hadj.2
        have walk_implies_rel : (blockGraph Q).Walk v u → Q v u := by
          intro w
          refine @SimpleGraph.Walk.recOn _ (blockGraph Q) (fun x y _ => Q x y) v u w
            ?_ ?_
          · intro u; exact Q.iseqv.refl u
          · intro a b c hadj _ ih; exact Q.trans (h_eq a b hadj) ih
        exact walk_implies_rel w
      -- All vertices in the ball are Q-equivalent to v, so the image is a singleton
      have h_singleton : ((fun a => (⟦a⟧ : Quotient Q)) '' resolvedBall (blockGraph Q) r v) ⊆ ({(⟦v⟧ : Quotient Q)} : Set (Quotient Q)) := by
        intro x hx
        simp only [Set.mem_image] at hx
        obtain ⟨a, ha, hx_eq⟩ := hx
        rw [← hx_eq]
        exact Set.mem_singleton_iff.mpr (Quotient.eq.mpr (Q.iseqv.symm (h_ball a ha)))
      have h_v_in_ball : v ∈ resolvedBall (blockGraph Q) r v := ⟨SimpleGraph.Walk.nil, by simp⟩
      have h_len : S.length + 1 - 1 = S.length := Nat.add_sub_cancel S.length 1
      simp only [le_refl, ↓reduceIte, S.part_length, top_inf_eq, h_len] at *
      have h_rresolved : rresolved S Q (S.length + 1) = blockGraph Q := by
        simp [rresolved, Nat.lt_irrefl]
      rw [h_rresolved]
      have h_sub : Set.Subsingleton ((fun a => (⟦a⟧ : Quotient Q)) '' resolvedBall (blockGraph Q) r v) := by
        intro a ha b hb
        have ha' := h_singleton ha
        have hb' := h_singleton hb
        simp at ha' hb'
        rw [ha', hb']
      let Q' := rpart S Q (S.length + 1 - 1)
      have h_Q'_eq_Q : Q' = Q := by simp [Q', rpart, S.part_length, Nat.add_sub_cancel]
      have h_singleton' : (((fun a => (⟦a⟧ : Quotient Q')) '' resolvedBall (blockGraph Q) r v) ⊆ {(⟦v⟧ : Quotient Q')}) := by
        rw [h_Q'_eq_Q]
        exact h_singleton
      refine Nat.le_trans (Set.ncard_le_ncard h_singleton' (Set.finite_singleton _)) ?_
      exact le_of_eq (Set.ncard_singleton _)
    )) (le_max_right _ _)

/-- **Merge-width monotonicity under within-block restriction.**
If $G$ has a merge sequence of radius-$r$ width $≤ k$ (with $1 ≤ k$), then so does
its within-block restriction by any partition $Q$. -/
theorem exists_restrict_mergeSeq (S : MergeSeq G) (Q : Setoid V) (r k : ℕ)
    (hk : 1 ≤ k) (hS : S.width r ≤ k) :
    ∃ S' : MergeSeq (restrictGraph G Q), S'.width r ≤ k := by
  refine ⟨restrictSeq S Q, ?_⟩
  refine le_trans (restrictSeq_width_le S Q r) ?_
  exact max_le hS hk

end Lax9Proofs
