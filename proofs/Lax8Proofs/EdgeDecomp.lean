import Lax8Proofs.Freezing
import Lax8Proofs.KtFreezing
import Lax8Proofs.Minimal

/-!
# Edge decomposition for Lemma 4.3

Working with the $Kt$-frozen partition $Q = ktSetoid S t$ of a merge sequence $S$
of radius-2 width $k$, we split the edges of $G$ into three graphs:

* $restrictGraph G Q$ — edges inside a block (the $GI$ of the paper);
* $edgeR S t$ — edges between distinct blocks that are *resolved* (at the step
  just after the minimum of the two block indices);
* $edgeU S t$ — edges between distinct blocks that are *unresolved*.

We show $G = edgeR ⊔ edgeU ⊔ restrictGraph G Q$, that $edgeU$ is $(k·t+1)$-colourable
(Claim 4.4 — degeneracy), and that $edgeR$ is $k$-colourable (Claim 4.5 — a
structurally ω-bounded merge sequence).  Combined with the $GI$ facts this yields
$exists_edge_decomposition$.
-/

namespace Lax8Proofs

open Lax8.MergeWidth

open scoped Classical
open Finset

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- The between-block **resolved** edges: $G$-edges $xy$ in different blocks that
are resolved at step $min (idxKt x) (idxKt y) + 1$. -/
noncomputable def edgeR (S : MergeSeq G) (t : ℕ) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => G.Adj x y ∧ ¬ (ktSetoid S t).r x y ∧
    (S.resolved (min (idxKt S t x) (idxKt S t y) + 1)).Adj x y)

/-- The between-block **unresolved** edges. -/
noncomputable def edgeU (S : MergeSeq G) (t : ℕ) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => G.Adj x y ∧ ¬ (ktSetoid S t).r x y ∧
    ¬ (S.resolved (min (idxKt S t x) (idxKt S t y) + 1)).Adj x y)

omit [Fintype V] in
@[simp] theorem edgeR_adj (S : MergeSeq G) (t : ℕ) (x y : V) :
    (edgeR S t).Adj x y ↔ G.Adj x y ∧ ¬ (ktSetoid S t).r x y ∧
      (S.resolved (min (idxKt S t x) (idxKt S t y) + 1)).Adj x y := by
  rw [edgeR, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, (⟨hg, hnq, hr⟩ | ⟨hg, hnq, hr⟩)⟩
    · exact ⟨hg, hnq, hr⟩
    · exact ⟨hg.symm, fun hq => hnq ((ktSetoid S t).symm hq), by rw [min_comm]; exact hr.symm⟩
  · intro h
    exact ⟨h.1.ne, Or.inl h⟩

omit [Fintype V] in
@[simp] theorem edgeU_adj (S : MergeSeq G) (t : ℕ) (x y : V) :
    (edgeU S t).Adj x y ↔ G.Adj x y ∧ ¬ (ktSetoid S t).r x y ∧
      ¬ (S.resolved (min (idxKt S t x) (idxKt S t y) + 1)).Adj x y := by
  rw [edgeU, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, (⟨hg, hnq, hr⟩ | ⟨hg, hnq, hr⟩)⟩
    · exact ⟨hg, hnq, hr⟩
    · exact ⟨hg.symm, fun hq => hnq ((ktSetoid S t).symm hq),
        by rw [min_comm]; exact fun hh => hr hh.symm⟩
  · intro h
    exact ⟨h.1.ne, Or.inl h⟩

/-- The three graphs edge-partition $G$. -/
theorem edge_decomp_eq (S : MergeSeq G) (t : ℕ) :
    G = edgeR S t ⊔ edgeU S t ⊔ restrictGraph G (ktSetoid S t) := by
  ext x y
  simp only [SimpleGraph.sup_adj, edgeR_adj, edgeU_adj, restrictGraph_adj]
  constructor
  · intro hg
    by_cases hq : (ktSetoid S t).r x y
    · exact Or.inr ⟨hg, hq⟩
    · by_cases hr : (S.resolved (min (idxKt S t x) (idxKt S t y) + 1)).Adj x y
      · exact Or.inl (Or.inl ⟨hg, hq, hr⟩)
      · exact Or.inl (Or.inr ⟨hg, hq, hr⟩)
  · rintro ((⟨hg, _, _⟩ | ⟨hg, _, _⟩) | ⟨hg, _⟩) <;> exact hg

omit [Fintype V] in
/-- The $Kt$-index is constant on $Kt$-frozen blocks. -/
theorem ktSetoid_idx_const (S : MergeSeq G) (t : ℕ) {a b : V}
    (h : (ktSetoid S t).r a b) : idxKt S t a = idxKt S t b := by
  rcases h with rfl | ⟨heq, _⟩
  · rfl
  · exact heq

/-- **Witness for Claim 4.4.**  If $X$ is a $t$-clique inside the part $P_{i+1}$
of $u$ (where $i = idxKt u$), and $pb$ is an $edgeU$-edge with $p$ in $u$'s block
and $idxKt u ≤ idxKt b$, then $b$ lies in the radius-2 $R_{i+1}$-ball of some
$x ∈ X$. -/
theorem edgeU_witness (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t) (homega : G.cliqueNum = t)
    {u : V} {X : Finset V} (hXcard : X.card = t) (hXclique : G.IsClique (X : Set V))
    (hXpart : ∀ x ∈ X, (S.part (idxKt S t u + 1)).r u x)
    {p b : V} (hp : (ktSetoid S t).r u p) (hedge : (edgeU S t).Adj p b)
    (hbidx : idxKt S t u ≤ idxKt S t b) :
    ∃ x ∈ X, b ∈ resolvedBall (S.resolved (idxKt S t u + 1)) 2 x := by
  set i := idxKt S t u with hidef
  have h1i : 1 ≤ i := one_le_idxKt S ht u
  have hilt : i < S.length := idxKt_lt_length S ht homega u
  have hilen1 : i + 1 ≤ S.length := by omega
  have hidxp : idxKt S t p = i := (ktSetoid_idx_const S t hp).symm
  rw [edgeU_adj] at hedge
  obtain ⟨hGpb, _, hnr_pb⟩ := hedge
  have hmineq : min (idxKt S t p) (idxKt S t b) = i := by
    rw [hidxp]; exact min_eq_left hbidx
  rw [hmineq] at hnr_pb
  -- $u ~ p$ in $P_i$, hence in $P_{i+1}$.
  have hup_i : (S.part i).r u p := (ktSetoid_rel_iff S ht u p).mp hp
  have hup1 : (S.part (i + 1)).r u p := S.part_mono h1i (by omega) hilen1 hup_i
  by_cases hbX : b ∈ X
  · exact ⟨b, hbX, mem_resolvedBall_self _ _ _⟩
  · -- some $x ∈ X$ is non-adjacent to $b$, else $X ∪ {b}$ is a $(t+1)$-clique.
    have hexne : ∃ x ∈ X, ¬ G.Adj x b := by
      by_contra hcon
      push_neg at hcon
      have hclique : G.IsClique (↑(insert b X) : Set V) := by
        rw [Finset.coe_insert]
        intro a ha c hc hac
        simp only [Set.mem_insert_iff] at ha hc
        rcases ha with rfl | ha <;> rcases hc with rfl | hc
        · exact absurd rfl hac
        · exact (hcon c hc).symm
        · exact hcon a ha
        · exact hXclique ha hc hac
      have hcardins : (insert b X).card = t + 1 := by
        rw [Finset.card_insert_of_notMem hbX, hXcard]
      have hle : (insert b X).card ≤ G.cliqueNum := hclique.card_le_cliqueNum
      rw [hcardins, homega] at hle
      omega
    obtain ⟨x, hxX, hxnb⟩ := hexne
    have hxu1 : (S.part (i + 1)).r u x := hXpart x hxX
    have hxb_ne : x ≠ b := fun h => hbX (h ▸ hxX)
    have hpb_ne : p ≠ b := hGpb.ne
    have hpx : (S.part (i + 1)).r p x := Setoid.trans' _ (Setoid.symm' _ hup1) hxu1
    have hres_xb : (S.resolved (i + 1)).Adj x b := by
      by_contra hnr_xb
      have huni := S.uniform (by omega : 1 ≤ i + 1) hilen1 hpx
        ((S.part (i + 1)).iseqv.refl b) hpb_ne hxb_ne hnr_pb hnr_xb
      rw [huni] at hGpb
      exact hxnb hGpb
    exact ⟨x, hxX, mem_resolvedBall_of_adj _ (by norm_num) hres_xb⟩

/-- **Claim 4.4 (degeneracy of $edgeU$).**  With respect to the $Kt$-frozen
partition and its index order, each block is $edgeU$-adjacent to at most $k·t$
blocks of index $≥$ its own. -/
theorem edgeU_backdeg (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t) (k : ℕ)
    (hW : S.width 2 ≤ k) (homega : G.cliqueNum = t) (u : V) :
    (((quotientGraph (edgeU S t) (ktSetoid S t)).neighborFinset
      (Quotient.mk (ktSetoid S t) u)).filter
      (fun q => ∃ a, Quotient.mk (ktSetoid S t) a = q ∧ idxKt S t u ≤ idxKt S t a)).card
      ≤ k * t := by
  classical
  set i := idxKt S t u with hidef
  have h1i : 1 ≤ i := one_le_idxKt S ht u
  have hilt : i < S.length := idxKt_lt_length S ht homega u
  -- A $t$-clique $X$ inside the part $P_{i+1}$ of $u$.
  obtain ⟨X0, hX0card, hX0clique, hX0part⟩ := partHasClique_succ S ht homega u
  obtain ⟨X, hXsub, hXcard⟩ := Finset.le_card_iff_exists_subset_card.mp hX0card
  have hXclique : G.IsClique (X : Set V) := hX0clique.subset (Finset.coe_subset.mpr hXsub)
  have hXpart : ∀ x ∈ X, (S.part (i + 1)).r u x := fun x hx => hX0part x (hXsub hx)
  -- The $P_i$-parts accessible from $x$ within the radius-2 $R_{i+1}$-ball.
  set accP : V → Finset (Quotient (S.part i)) := fun x =>
    (resolvedBall (S.resolved (i + 1)) 2 x).toFinset.image (Quotient.mk (S.part i)) with haccPdef
  have haccP_card : ∀ x, (accP x).card ≤ k := by
    intro x
    have h1 : S.numAccessible 2 (i + 1) x = (accP x).card := numAccessible_eq_image S 2 (i + 1) x
    have h2 : S.numAccessible 2 (i + 1) x ≤ k :=
      le_trans (numAccessible_le_width S (by omega) (by omega) x) hW
    omega
  -- Target set and the map $g$.
  set g : V → V × Quotient (S.part i) := fun b =>
    (if h : ∃ x, x ∈ X ∧ b ∈ resolvedBall (S.resolved (i + 1)) 2 x then h.choose else u,
     Quotient.mk (S.part i) b) with hgdef
  set T : Finset (V × Quotient (S.part i)) :=
    X.biUnion (fun x => (accP x).image (fun p => (x, p))) with hTdef
  have hTcard : T.card ≤ k * t := by
    calc T.card ≤ ∑ x ∈ X, ((accP x).image (fun p => (x, p))).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ X, k := Finset.sum_le_sum (fun x _ => le_trans Finset.card_image_le (haccP_card x))
      _ = X.card * k := by rw [Finset.sum_const, smul_eq_mul]
      _ = k * t := by rw [hXcard]; ring
  refine le_trans (card_backneighbors_le (edgeU S t) (ktSetoid S t) (idxKt S t) u T g
    (fun a b h => ktSetoid_idx_const S t h) ?hmaps ?hinj) hTcard
  case hmaps =>
    intro p b hpq hedge hbidx
    have hp : (ktSetoid S t).r u p := Setoid.symm' _ (Quotient.exact hpq)
    have hex : ∃ x, x ∈ X ∧ b ∈ resolvedBall (S.resolved (i + 1)) 2 x :=
      edgeU_witness S ht homega hXcard hXclique hXpart hp hedge hbidx
    have hgb : g b = (hex.choose, Quotient.mk (S.part i) b) := by
      simp only [hgdef, dif_pos hex]
    rw [hgb, hTdef, Finset.mem_biUnion]
    refine ⟨hex.choose, hex.choose_spec.1, ?_⟩
    rw [Finset.mem_image]
    refine ⟨Quotient.mk (S.part i) b, ?_, rfl⟩
    rw [haccPdef, Finset.mem_image]
    exact ⟨b, by simpa using hex.choose_spec.2, rfl⟩
  case hinj =>
    intro p1 b1 p2 b2 _ _ hb1 _ _ _ hgeq
    have hsnd : Quotient.mk (S.part i) b1 = Quotient.mk (S.part i) b2 := by
      have := congrArg Prod.snd hgeq
      simpa [hgdef] using this
    have hrel : (S.part i).r b1 b2 := Quotient.exact hsnd
    have hmono : (S.part (idxKt S t b1)).r b1 b2 :=
      S.part_mono h1i hb1 (idxKt_le_length S t b1) hrel
    exact Quotient.sound ((ktSetoid_rel_iff S ht b1 b2).mpr hmono)

/-- $edgeU$ is $(k·t + 1)$-colourable. -/
theorem edgeU_colorable (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t) (k : ℕ)
    (hW : S.width 2 ≤ k) (homega : G.cliqueNum = t) :
    (edgeU S t).Colorable (k * t + 1) := by
  refine colorable_of_partition_degenerate (edgeU S t) (ktSetoid S t) (idxKt S t) (k * t)
    ?_ ?_ ?_
  · intro u v huv hadj
    exact ((edgeU_adj S t u v).mp hadj).2.1 huv
  · intro u v huv
    rcases huv with rfl | ⟨h, _⟩
    · rfl
    · exact h
  · intro u
    exact edgeU_backdeg S ht k hW homega u

/-- **Claim 4.5 (transfer direction).**  Under the minimality of $S$, if $xy$ and
$x'y'$ are two unresolved pairs at step $i$ in the same two parts, and $xy$ is an
edge of $edgeR$, then so is $x'y'$. -/
theorem edgeR_adj_transfer (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t) (hmin : Minimal S)
    (homega : G.cliqueNum = t) {i : ℕ} (hi : 1 ≤ i) (hilen : i ≤ S.length)
    {x x' y y' : V} (hx : (S.part i).r x x') (hy : (S.part i).r y y')
    (hne : x ≠ y) (hne' : x' ≠ y')
    (hnr : ¬ (S.resolved i).Adj x y) (hnr' : ¬ (S.resolved i).Adj x' y')
    (h : (edgeR S t).Adj x y) : (edgeR S t).Adj x' y' := by
  rw [edgeR_adj] at h ⊢
  obtain ⟨hG, hnq, hres⟩ := h
  set jx := idxKt S t x with hjx
  set jy := idxKt S t y with hjy
  -- $min jx jy ≥ i$, else the resolved pair $xy$ at step $min+1 ≤ i$ contradicts $hnr$.
  have hjge : i ≤ min jx jy := by
    by_contra hlt
    push_neg at hlt
    exact hnr (S.resolved_mono (by omega) (by omega) hilen hres)
  have hix : i ≤ jx := le_trans hjge (min_le_left _ _)
  have hiy : i ≤ jy := le_trans hjge (min_le_right _ _)
  -- $x, x'$ (resp. $y, y'$) lie in the same $Kt$-frozen block, with equal indices.
  have hpxx' : (S.part jx).r x x' := S.part_mono hi hix (idxKt_le_length S t x) hx
  have hpyy' : (S.part jy).r y y' := S.part_mono hi hiy (idxKt_le_length S t y) hy
  have hkxx' : (ktSetoid S t).r x x' := (ktSetoid_rel_iff S ht x x').mpr hpxx'
  have hkyy' : (ktSetoid S t).r y y' := (ktSetoid_rel_iff S ht y y').mpr hpyy'
  have hidxx' : idxKt S t x' = jx := idxKt_eq_of_part_rel S ht rfl hpxx'
  have hidxy' : idxKt S t y' = jy := idxKt_eq_of_part_rel S ht rfl hpyy'
  refine ⟨(S.uniform hi hilen hx hy hne hne' hnr hnr').mp hG, ?_, ?_⟩
  · -- $x', y'$ are in different blocks, else $x, y$ would be too.
    intro hxy'
    exact hnq (Setoid.trans' _ hkxx' (Setoid.trans' _ hxy' (Setoid.symm' _ hkyy')))
  · -- $x'y'$ is resolved at step $min jx jy + 1$, by Lemma 2.1.
    rw [hidxx', hidxy']
    have hjlen : min jx jy + 1 ≤ S.length := by
      have := idxKt_lt_length S ht homega x
      have hmm : min jx jy ≤ jx := min_le_left _ _
      omega
    exact lemma21 S hmin hi hilen hx hy hne' hnr hnr' (by omega) hjlen hres

/-- **Claim 4.5.**  When $S$ is minimal, $S$ (same partitions and resolved sets)
is also a valid merge sequence for $edgeR$: uniformity holds for $edgeR$. -/
theorem edgeR_uniform (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t) (hmin : Minimal S)
    (homega : G.cliqueNum = t) :
    ∀ ⦃i⦄, 1 ≤ i → i ≤ S.length → ∀ ⦃x x' y y' : V⦄,
      (S.part i).r x x' → (S.part i).r y y' → x ≠ y → x' ≠ y' →
      ¬ (S.resolved i).Adj x y → ¬ (S.resolved i).Adj x' y' →
      ((edgeR S t).Adj x y ↔ (edgeR S t).Adj x' y') := by
  intro i hi hilen x x' y y' hx hy hne hne' hnr hnr'
  exact ⟨edgeR_adj_transfer S ht hmin homega hi hilen hx hy hne hne' hnr hnr',
    edgeR_adj_transfer S ht hmin homega hi hilen (Setoid.symm' _ hx) (Setoid.symm' _ hy)
      hne' hne hnr' hnr⟩

/-- The merge sequence for $edgeR$ given by the same partitions and resolved
sets as $S$ (valid by $edgeR_uniform$). -/
noncomputable def edgeR_seq (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t) (hmin : Minimal S)
    (homega : G.cliqueNum = t) :
    MergeSeq (edgeR S t) where
  length := S.length
  one_le_length := S.one_le_length
  part := S.part
  resolved := S.resolved
  part_one := S.part_one
  part_length := S.part_length
  part_mono := S.part_mono
  resolved_mono := S.resolved_mono
  uniform := edgeR_uniform S ht hmin homega

/-- The merge sequence $edgeR_seq$ is structurally ω-bounded for $edgeR$. -/
theorem edgeR_SOB (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t) (hmin : Minimal S)
    (homega : G.cliqueNum = t) :
    StructurallyOmegaBounded (edgeR_seq S ht hmin homega) := by
  intro i hi1 hilen u a b ha hb hab w hw
  rw [edgeR_adj] at hab hw
  have hnot_kt : ¬ (ktSetoid S t).r a b := hab.2.1
  rw [ktSetoid_rel_iff S ht] at hnot_kt
  by_cases hi_le_kta : i ≤ idxKt S t a
  · -- Case i ≤ idxKt S t a: contradiction since a, b should be in same part
    have hua : (S.part (idxKt S t a)).r u a := S.part_mono hi1 hi_le_kta (idxKt_le_length S t a) ha
    have hub : (S.part (idxKt S t a)).r u b := S.part_mono hi1 hi_le_kta (idxKt_le_length S t a) hb
    have hab' : (S.part (idxKt S t a)).r a b := Setoid.trans' _ (Setoid.symm' _ hua) hub
    exact absurd hab' hnot_kt
  · -- Case i > idxKt S t a: use resolution monotonicity
    push_neg at hi_le_kta
    have hilen' : i ≤ S.length := hilen
    have hclq_a : partHasClique S t i a := partHasClique_of_gt S t hi_le_kta hilen'
    have ha' : (S.part i).r a u := Setoid.symm' _ ha
    have hclq_u : partHasClique S t i u := partHasClique_congr S t ha' hclq_a
    -- Helper: if partHasClique at i and i ≤ j, then partHasClique at j (by part monotonicity)
    have clq_mono : ∀ {j}, i ≤ j → j ≤ S.length → partHasClique S t i u → partHasClique S t j u := by
      intro j hij hlen hclq
      obtain ⟨X, hcard, hclique, hmem⟩ := hclq
      exact ⟨X, hcard, hclique, fun x hx => S.part_mono hi1 hij hlen (hmem x hx)⟩
    have hidx_u_lt : idxKt S t u < i := by
      by_contra h
      push_neg at h
      -- h : i ≤ idxKt S t u
      have hidx_le : idxKt S t u ≤ S.length := idxKt_le_length S t u
      have hclq_idx : partHasClique S t (idxKt S t u) u := clq_mono h hidx_le hclq_u
      exact not_partHasClique_idxKt S ht u hclq_idx
    -- Now use resolution monotonicity
    have heq_res : (edgeR_seq S ht hmin homega).resolved = S.resolved := rfl
    rw [heq_res]
    have hir : min (idxKt S t u) (idxKt S t w) + 1 ≤ i := by
      have hmin_le : min (idxKt S t u) (idxKt S t w) ≤ idxKt S t u := min_le_left _ _
      omega
    have hi1' : 1 ≤ min (idxKt S t u) (idxKt S t w) + 1 := by omega
    have hilen_res : i ≤ S.length := hilen
    exact ((S.resolved_mono hi1' hir hilen_res) hw.2.2)

/-- $edgeR$ is $k$-colourable (Claim 4.5 + Lemma 4.1). -/
theorem edgeR_colorable (S : MergeSeq G) {t : ℕ} (ht : 2 ≤ t) (k : ℕ) (hk : 1 ≤ k)
    (hW : S.width 2 ≤ k) (hmin : Minimal S) (homega : G.cliqueNum = t) :
    (edgeR S t).Colorable k :=
  colorable_of_structurallyOmegaBounded k hk (edgeR_seq S ht hmin homega) hW
    (edgeR_SOB S ht hmin homega)

end Lax8Proofs
