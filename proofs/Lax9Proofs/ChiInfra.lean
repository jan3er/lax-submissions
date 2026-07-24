import Lax9Proofs.MergeWidthBasic

/-!
# Colouring infrastructure for the χ-boundedness proof

Reusable, general colouring lemmas used in the proof of Theorem 1.2:

* $colorable_sup$ — a proper colouring of an edge-union $G ⊔ H$ from colourings
  of $G$ and $H$ (chromatic number of an edge union is at most the product);
* $quotientGraph$ and $colorable_of_quotientGraph$ — colouring a graph via a
  colouring of a quotient whose parts are independent;
* $colorable_of_backdegree$ — a $(d+1)$-colouring of a $d$-degenerate graph
  (greedy colouring);
* $colorable_of_partition_degenerate$ — the combined principle: a graph whose
  independent-set partition has a $d$-degenerate quotient (w.r.t. an index
  order) is $(d+1)$-colourable.
-/

namespace Lax9Proofs

open Lax9.MergeWidth

open scoped Classical
open Finset

universe u
variable {V : Type u} [Fintype V]

omit [Fintype V] in
/-- Product colouring: an edge-union $G ⊔ H$ is $(m·n)$-colourable when $G$ is
$m$-colourable and $H$ is $n$-colourable. -/
theorem colorable_sup {G H : SimpleGraph V} {m n : ℕ}
    (h1 : G.Colorable m) (h2 : H.Colorable n) : (G ⊔ H).Colorable (m * n) := by
  -- Recipe: from $colorable_iff_exists_bdd_nat_coloring$ get colourings
  -- $cG : G.Coloring ℕ$ with $cG v < m$ and $cH : H.Coloring ℕ$ with $cH v < n$.
  -- Define $c v = cH v + cG v * n$.  It is bounded by $m*n$ and proper on
  -- $G ⊔ H$: from $c u = c v$, taking $% n$ gives $cH u = cH v$ and $/ n$ gives
  -- $cG u = cG v$ (using $n > 0$, which holds since $V$ is then nonempty), so an
  -- edge of $G$ or of $H$ forces $c u ≠ c v$.
  unfold SimpleGraph.Colorable at h1 h2
  obtain ⟨cG⟩ := h1
  obtain ⟨cH⟩ := h2
  -- Define combined coloring: c v = (cG v, cH v) encoded as Fin (m * n)
  -- We use cG v * n + cH v
  let c : V → Fin (m * n) := fun v => ⟨cG v * n + cH v, by
    have h1 : (cG v).val < m := (cG v).is_lt
    have h2 : (cH v).val < n := (cH v).is_lt
    nlinarith⟩
  have hc_valid : ∀ u v, (G ⊔ H).Adj u v → c u ≠ c v := by
    intro u v huv
    simp only [SimpleGraph.sup_adj] at huv
    rcases huv with huvG | huvH
    · intro heq
      have hne := cG.valid huvG
      rw [Fin.ext_iff] at heq
      have hu : (cG u).val < m := (cG u).is_lt
      have hv : (cG v).val < m := (cG v).is_lt
      have hhu : (cH u).val < n := (cH u).is_lt
      have hhv : (cH v).val < n := (cH v).is_lt
      have heq' : (cG u).val * n + (cH u).val = (cG v).val * n + (cH v).val := by
        simp only [c] at heq
        exact heq
      -- Key lemma: if a*n + b = c*n + d with b,d < n, then a = c
      set a := (cG u).val with ha
      set a' := (cG v).val with ha'
      set b := (cH u).val with hb
      set b' := (cH v).val with hb'
      have hab : a * n + b = a' * n + b' := heq'
      have hb_bound : b < n := hhu
      have hb'_bound : b' < n := hhv
      have ha_eq_a' : a = a' := by
        simp only [ha, ha'] at hab ⊢
        nlinarith
      have hmul : (cG u).val * n = (cG v).val * n := by omega
      have : (cG u).val = (cG v).val := by
        rcases n with _ | n <;> simp_all
      exact hne (Fin.ext this)
    · intro heq
      rw [Fin.ext_iff] at heq
      have hu : (cH u).val < n := (cH u).is_lt
      have hv : (cH v).val < n := (cH v).is_lt
      have hhu : (cG u).val < m := (cG u).is_lt
      have hhv : (cG v).val < m := (cG v).is_lt
      have heq' : (cG u).val * n + (cH u).val = (cG v).val * n + (cH v).val := by
        simp only [c] at heq
        exact heq
      have ha_eq_a' : (cG u).val = (cG v).val := by nlinarith
      have hne := cH.valid huvH
      have : (cH u).val = (cH v).val := by nlinarith
      exact hne (Fin.ext this)
  refine ⟨⟨c, ?_⟩⟩
  intro u v huv
  simp [hc_valid u v huv]

/-- The quotient graph of $G$ by a partition $P$: two distinct parts are
adjacent iff some edge of $G$ joins them. -/
noncomputable def quotientGraph (G : SimpleGraph V) (P : Setoid V) :
    SimpleGraph (Quotient P) where
  Adj q q' := q ≠ q' ∧ ∃ a b, Quotient.mk P a = q ∧ Quotient.mk P b = q' ∧ G.Adj a b
  symm := by rintro q q' ⟨hne, a, b, ha, hb, hab⟩; exact ⟨hne.symm, b, a, hb, ha, hab.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [Fintype V] in
/-- If the parts of $P$ are independent in $G$, a colouring of the quotient graph
pulls back to a colouring of $G$. -/
theorem colorable_of_quotientGraph (G : SimpleGraph V) (P : Setoid V) {n : ℕ}
    (hindep : ∀ u v, P.r u v → ¬ G.Adj u v)
    (h : (quotientGraph G P).Colorable n) : G.Colorable n := by
  obtain ⟨cq⟩ := h
  refine ⟨⟨cq ∘ Quotient.mk'', ?_⟩⟩
  intro u v hadj
  have hne : (Quotient.mk'' u : Quotient P) ≠ Quotient.mk'' v := by
    intro heq
    apply hindep u v _ hadj
    exact Quotient.exact heq
  have hadjQ : (quotientGraph G P).Adj (Quotient.mk'' u) (Quotient.mk'' v) :=
    ⟨hne, u, v, rfl, rfl, hadj⟩
  have h := cq.map_rel' hadjQ
  simp [SimpleGraph.completeGraph] at h
  exact h

/-- **Greedy colouring of a degenerate graph.**
If $r$ is an injective ranking of the vertices of a finite graph $K$ such that
each vertex has at most $d$ neighbours of strictly larger rank, then $K$ is
$(d+1)$-colourable. -/
theorem colorable_of_backdegree {W : Type u} [Fintype W] (K : SimpleGraph W)
    (r : W → ℕ) (hr : Function.Injective r) (d : ℕ)
    (hdeg : ∀ w, ((K.neighborFinset w).filter (fun u => r w < r u)).card ≤ d) :
    K.Colorable (d + 1) := by
  -- Recipe: strong induction on $Fintype.card W$.  If $W$ is empty, done.
  -- Otherwise let $w₀$ minimise $r$ (unique by injectivity); every neighbour of
  -- $w₀$ has larger rank, so $w₀$ has at most $d$ neighbours in total
  -- ($hdeg w₀$).  Recurse on the induced subgraph on ${w₀}ᶜ$ (its back-degrees
  -- are no larger) to $(d+1)$-colour it, then extend to $w₀$ with a colour in
  -- $Fin (d+1)$ avoiding its $≤ d$ neighbours' colours.
  by_cases hne : Nonempty W
  · -- Strong induction on Fintype.card W
    induction hc : Fintype.card W using Nat.strong_induction_on generalizing W K r d with
    | _ n ih =>
      -- n = 0 contradicts hne
      by_cases hn : n = 0
      · exfalso; rw [← hc] at hn; exact Fintype.card_ne_zero hn
      · -- Find minimum r-value among vertices
        have hrng : (Finset.univ.image r).Nonempty := Finset.image_nonempty.mpr ⟨hne.some, Finset.mem_univ _⟩
        let m := (Finset.univ.image r).min' hrng
        -- There exists a vertex achieving this minimum
        have hm_in_image : m ∈ Finset.image r Finset.univ := Finset.min'_mem _ hrng
        obtain ⟨w₀, _, hw₀r⟩ := Finset.mem_image.mp hm_in_image
        -- w₀ has minimum r value
        have hw₀min : ∀ w : W, r w₀ ≤ r w := by
          intro w
          have := Finset.min'_le _ _ (Finset.mem_image_of_mem r (Finset.mem_univ w))
          linarith
        -- Neighbors of w₀ have strictly larger rank (since r is injective)
        have hw₀nbr : ∀ w ∈ K.neighborFinset w₀, r w₀ < r w := by
          intro w hwbr
          rw [SimpleGraph.mem_neighborFinset] at hwbr
          have hne : w₀ ≠ w := hwbr.ne
          exact lt_of_le_of_ne (hw₀min w) (fun h => hne (hr h))
        -- So w₀ has at most d neighbors total
        have hw₀deg : (K.neighborFinset w₀).card ≤ d := by
          have := hdeg w₀
          have hsub : K.neighborFinset w₀ ⊆ {u ∈ K.neighborFinset w₀ | r w₀ < r u} := by
            intro w hw
            rw [Finset.mem_filter]
            exact ⟨hw, hw₀nbr w hw⟩
          exact le_trans (Finset.card_le_card hsub) this
        -- Define induced subgraph on W \ {w₀}
        let W' : Type u := {w : W | w ≠ w₀}
        let K' : SimpleGraph W' := K.induce {w | w ≠ w₀}
        -- W' has smaller cardinality
        have hcard : Fintype.card W' = n - 1 := by
          simp only [W', Fintype.card_subtype] at *
          rw [← hc]
          have h1 : Fintype.card W > 0 := by rw [hc]; exact Nat.pos_of_ne_zero hn
          rw [← Finset.card_univ]
          simp [Finset.card_univ, Finset.filter_ne', Finset.card_erase_of_mem]
        -- Restrict the ranking to W'
        let r' : W' → ℕ := fun w => r w.val
        have hr' : Function.Injective r' := fun a b h => by
          simp only [r'] at h
          exact Subtype.ext (hr h)
        -- Back-degree condition for K'
        have hdeg' : ∀ w : W', ({u ∈ K'.neighborFinset w | r' w < r' u}).card ≤ d := by
          intro w
          apply le_trans _ (hdeg w.val)
          let S : Finset W' := K'.neighborFinset w |>.filter fun u => r' w < r' u
          let T : Finset W := K.neighborFinset w.val |>.filter fun u => r w.val < r u
          have hinj : Function.Injective (fun u : W' => u.val) := by
            intro a b hab
            exact Subtype.ext hab
          have himage : Finset.image (fun u : W' => u.val) S ⊆ T := by
            intro x hx
            rw [Finset.mem_image] at hx
            obtain ⟨u, hu, rfl⟩ := hx
            simp only [S, Finset.mem_filter] at hu
            simp only [T, Finset.mem_filter]
            refine ⟨?_, hu.2⟩
            rw [SimpleGraph.mem_neighborFinset] at hu ⊢
            obtain ⟨hadj, _⟩ := hu
            exact hadj
          calc S.card = (Finset.image (fun u : W' => u.val) S).card := (Finset.card_image_of_injective _ hinj).symm
            _ ≤ T.card := Finset.card_le_card himage
        -- If n = 1, K has only one vertex, so it's colorable
        by_cases hn1 : n = 1
        · -- K has exactly one vertex, so it's colorable
          have hcard1 : Fintype.card W = 1 := hc ▸ hn1
          rw [SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
          obtain ⟨w₁, hw₁⟩ := Fintype.card_eq_one_iff.mp hcard1
          have hadj : ∀ u v, ¬ K.Adj u v := fun u v huv => by
            exfalso
            exact huv.ne (hw₁ u ▸ hw₁ v ▸ rfl)
          use ⟨fun w => 0, fun huv => False.elim (hadj _ _ huv)⟩
          intro w
          simp
        · -- Apply induction hypothesis to get a coloring of K'
          have hne' : Nonempty W' := by
            have hn2 : n ≥ 2 := by omega
            have hcard2 : Fintype.card W ≥ 2 := by rw [hc]; exact hn2
            have h2 : ∃ x : W, x ≠ w₀ := by
              by_contra h
              push_neg at h
              have : Fintype.card W ≤ 1 := by
                apply Fintype.card_le_one_iff.mpr
                intro x y
                rw [h x, h y]
              omega
            exact ⟨⟨h2.choose, h2.choose_spec⟩⟩
          have ih' := ih (n - 1) (by omega) K' r' hr' d hdeg' hne' hcard
          -- Get a coloring of K'
          rw [SimpleGraph.colorable_iff_exists_bdd_nat_coloring] at ih'
          obtain ⟨c', hc'⟩ := ih'
          -- Colors used by neighbors of w₀
          have hneighbor_in_W' : ∀ u ∈ K.neighborFinset w₀, u ≠ w₀ := by
            intro u hu
            rw [SimpleGraph.mem_neighborFinset] at hu
            exact hu.ne.symm
          let neighborColors : Finset ℕ :=
            (K.neighborFinset w₀).image (fun u =>
              if h : u ≠ w₀ then c' ⟨u, h⟩ else 0)
          have hneighborColors_card : neighborColors.card ≤ d := by
            apply Finset.card_image_le.trans hw₀deg
          -- Find a color for w₀ not used by neighbors
          have hnonempty : (Finset.range (d + 1) \ neighborColors).Nonempty := by
            by_contra hempty
            push_neg at hempty
            simp only [Finset.sdiff_eq_empty_iff_subset] at hempty
            have : Finset.card neighborColors ≥ d + 1 := by
              rw [← Finset.card_range (d + 1)]
              exact Finset.card_le_card hempty
            omega
          obtain ⟨color₀, hcolor₀_mem⟩ := hnonempty
          have hcolor₀_range := Finset.mem_range.mp (Finset.mem_sdiff.mp hcolor₀_mem).1
          have hcolor₀_notmem := Finset.mem_sdiff.mp hcolor₀_mem |>.2
          -- Define coloring of K: use c' on W', and color₀ for w₀
          rw [SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
          let color : W → ℕ := fun w => if h : w = w₀ then color₀ else c' ⟨w, h⟩
          have hcoloradj : ∀ u v, K.Adj u v → (SimpleGraph.completeGraph ℕ).Adj (color u) (color v) := by
            intro u v huv
            -- Case analysis: u = w₀, v = w₀, or neither
            by_cases hu : u = w₀
            · -- Case u = w₀: color u = color₀, need color₀ ≠ color v
              simp_rw [hu] at huv ⊢
              simp only [color, ↓reduceDIte]
              have hv_nbr : v ≠ w₀ := huv.ne.symm
              simp only [hv_nbr, ↓reduceDIte]
              -- color₀ ∉ neighborColors, and c' ⟨v, hv_nbr⟩ ∈ neighborColors
              have hmem : c' ⟨v, hv_nbr⟩ ∈ neighborColors := by
                simp only [neighborColors]
                rw [Finset.mem_image]
                refine ⟨v, ?_, ?_⟩
                · rw [SimpleGraph.mem_neighborFinset]
                  exact huv
                · simp [hv_nbr]
              exact fun h => hcolor₀_notmem (h ▸ hmem)
            · by_cases hv : v = w₀
              · -- Case v = w₀: color v = color₀, need color₀ ≠ color u
                simp_rw [hv] at huv ⊢
                simp only [color, ↓reduceDIte]
                have hu_nbr : u ≠ w₀ := huv.ne'.symm
                simp only [hu_nbr, ↓reduceDIte]
                -- color₀ ∉ neighborColors, and c' ⟨u, hu_nbr⟩ ∈ neighborColors
                have hmem : c' ⟨u, hu_nbr⟩ ∈ neighborColors := by
                  simp only [neighborColors]
                  rw [Finset.mem_image]
                  refine ⟨u, ?_, ?_⟩
                  · rw [SimpleGraph.mem_neighborFinset]
                    exact huv.symm
                  · simp [hu_nbr]
                exact fun h => hcolor₀_notmem (h ▸ hmem)
              · -- Case neither equals w₀: use c' validity
                simp only [color, hu, hv, ↓reduceDIte]
                have hadj' : K'.Adj ⟨u, hu⟩ ⟨v, hv⟩ := huv
                exact c'.valid hadj'
          use ⟨color, @hcoloradj⟩
          -- All colors are < d + 1
          intro w
          show color w < d + 1
          simp only [color]
          split_ifs with h
          · exact hcolor₀_range
          · exact hc' ⟨w, h⟩
  · haveI : IsEmpty W := not_nonempty_iff.mp hne
    rw [SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
    use ⟨fun w => isEmptyElim w, by simp⟩
    intro w
    exact isEmptyElim w

/-- **Combined colouring principle.**
Let $P$ partition $V$ into $G$-independent sets, with an index $idx$ constant on
parts.  If in the quotient graph every part is adjacent to at most $d$ parts of
index $≥$ its own, then $G$ is $(d+1)$-colourable. -/
theorem colorable_of_partition_degenerate (G : SimpleGraph V) (P : Setoid V)
    (idx : V → ℕ) (d : ℕ)
    (hindep : ∀ u v, P.r u v → ¬ G.Adj u v)
    (hidx : ∀ u v, P.r u v → idx u = idx v)
    (hdeg : ∀ u, (((quotientGraph G P).neighborFinset (Quotient.mk P u)).filter
      (fun q => ∃ a, Quotient.mk P a = q ∧ idx u ≤ idx a)).card ≤ d) :
    G.Colorable (d + 1) := by
  -- Recipe: descend $idx$ to $idxQ : Quotient P → ℕ$ via $Quotient.lift$.
  -- Build an injective ranking $r q = idxQ q * N + (e q).val$ where
  -- $e : Quotient P ≃ Fin N$ and $N = Fintype.card (Quotient P)$; then $r$
  -- refines $idxQ$ (i.e. $idxQ q < idxQ q' → r q < r q'$), so
  -- ${q' | r q < r q'} ⊆ {q' | idxQ q ≤ idxQ q'}$, and $hdeg$ bounds the
  -- back-degree of $quotientGraph G P$ by $d$.  Apply $colorable_of_backdegree$
  -- to get $(quotientGraph G P).Colorable (d+1)$, then $colorable_of_quotientGraph$.
  -- Define idxQ on quotient
  let idxQ : Quotient P → ℕ := fun q => Quotient.lift idx (by intro u v huv; exact hidx u v huv) q
  -- Let N be the cardinality of the quotient
  let N := Fintype.card (Quotient P)
  -- Handle the case when Quotient P might be empty
  by_cases hne : Nonempty (Quotient P)
  · have hNpos : 0 < N := Fintype.card_pos
    let e : Quotient P ≃ Fin N := Fintype.equivFin _
    -- Define injective ranking r
    let r : Quotient P → ℕ := fun q => idxQ q * N + (e q).val
    -- Show r is injective
    have hr_inj : Function.Injective r := by
      intro q q' heq
      simp only [r] at heq
      have hq_lt : (e q).val < N := (e q).is_lt
      have hq'_lt : (e q').val < N := (e q').is_lt
      have h1 : idxQ q = idxQ q' := by nlinarith
      have h2 : (e q).val = (e q').val := by nlinarith
      exact e.injective (Fin.ext h2)
    -- Show r refines idxQ: if idxQ q < idxQ q' then r q < r q'
    have hr_refines : ∀ q q', idxQ q < idxQ q' → r q < r q' := by
      intro q q' hlt
      simp only [r]
      have hq_lt : (e q).val < N := (e q).is_lt
      have hq'_lt : (e q').val < N := (e q').is_lt
      have key : (idxQ q + 1) * N ≤ idxQ q' * N := by nlinarith
      calc idxQ q * N + (e q).val < idxQ q * N + N := by omega
        _ = (idxQ q + 1) * N := by ring
        _ ≤ idxQ q' * N := key
        _ ≤ idxQ q' * N + (e q').val := by omega
    -- Show back-degree of r is ≤ d
    have hr_deg : ∀ q, Finset.card (Finset.filter (fun q' => r q < r q') ((quotientGraph G P).neighborFinset q)) ≤ d := by
      intro q
      -- Need to lift hdeg to work on Quotient P
      obtain ⟨v, hv⟩ := Quotient.exists_rep q
      have hcard : Finset.card (Finset.filter (fun q' => r q < r q') ((quotientGraph G P).neighborFinset q)) =
                   Finset.card (Finset.filter (fun q' => r (Quotient.mk P v) < r q') ((quotientGraph G P).neighborFinset (Quotient.mk P v))) := by
        rw [hv]
      rw [hcard]
      apply le_trans _ (hdeg v)
      apply Finset.card_le_card
      intro q' hq'
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hq' ⊢
      obtain ⟨hadj, hr_larger⟩ := hq'
      -- We need to show: hadj ∧ ∃ a, ⟦a⟧ = q' ∧ idx v ≤ idx a
      refine ⟨hadj, ?_⟩
      -- From r q < r q' derive idxQ q ≤ idxQ q'
      rw [hv] at hr_larger
      simp only [r] at hr_larger
      -- idxQ (Quotient.mk P v) = idx v by definition
      obtain ⟨a, ha⟩ := Quotient.exists_rep q'
      use a
      constructor
      · exact ha
      · -- Need to show idx v ≤ idx a
        -- From hr_larger: r (Quotient.mk P v) < r q', so idxQ (Quotient.mk P v) ≤ idxQ q'
        have hr_larger' : idxQ (Quotient.mk P v) ≤ idxQ q' := by
          by_contra hlt
          push_neg at hlt
          have hstrict := hr_refines q' (Quotient.mk P v) hlt
          -- hstrict : r q' < r (Quotient.mk P v)
          -- But after substituting hv, hr_larger : r (Quotient.mk P v) < r q'
          -- Contradiction
          rw [← hv] at hr_larger
          simp only [r] at hstrict hr_larger
          linarith
        -- idxQ (Quotient.mk P v) = idx v and idxQ q' = idx a
        have hid_eq1 : idxQ (Quotient.mk P v) = idx v := rfl
        have hid_eq2 : idxQ q' = idx a := by rw [ha.symm]; rfl
        rw [hid_eq1, hid_eq2] at hr_larger'
        exact hr_larger'
    -- Apply colorable_of_backdegree to quotient graph
    have hcolorQ := colorable_of_backdegree (quotientGraph G P) r hr_inj d hr_deg
    -- Pull back coloring to G
    exact colorable_of_quotientGraph G P hindep hcolorQ
  · -- Quotient P is empty, so V is empty
    have hVempty : IsEmpty V := by
      contrapose! hne
      exact ⟨Quotient.mk P hne.some⟩
    rw [SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
    use ⟨fun w => isEmptyElim w, by simp⟩
    intro w
    exact isEmptyElim w

/-- **General back-neighbour counting.**  In the quotient of $G$ by a partition
$P$ whose index $idx$ is constant on parts, the number of quotient-neighbour
parts of $u$'s part having index $≥ idx u$ is at most $T.card$, provided every
$G$-edge $pb$ leaving $u$'s part with $idx u ≤ idx b$ satisfies $g b ∈ T$, and
$g$ separates such $b$'s up to their $P$-class. -/
theorem card_backneighbors_le (G : SimpleGraph V) (P : Setoid V) (idx : V → ℕ)
    (u : V) {β : Type u} (T : Finset β) (g : V → β)
    (hidx_const : ∀ a b, P.r a b → idx a = idx b)
    (hmaps : ∀ p b, Quotient.mk P p = Quotient.mk P u → G.Adj p b → idx u ≤ idx b →
        g b ∈ T)
    (hinj : ∀ p1 b1 p2 b2, Quotient.mk P p1 = Quotient.mk P u → G.Adj p1 b1 →
        idx u ≤ idx b1 → Quotient.mk P p2 = Quotient.mk P u → G.Adj p2 b2 →
        idx u ≤ idx b2 → g b1 = g b2 →
        Quotient.mk P b1 = Quotient.mk P b2) :
    (((quotientGraph G P).neighborFinset (Quotient.mk P u)).filter
      (fun q => ∃ a, Quotient.mk P a = q ∧ idx u ≤ idx a)).card ≤ T.card := by
  set S' := (((quotientGraph G P).neighborFinset (Quotient.mk P u)).filter
    (fun q => ∃ a, Quotient.mk P a = q ∧ idx u ≤ idx a)) with hS'def
  have hchoice : ∀ q ∈ S', ∃ b : V, ∃ p : V, Quotient.mk P p = Quotient.mk P u ∧
      Quotient.mk P b = q ∧ G.Adj p b := by
    intro q hq
    have hmem := (Finset.mem_filter.mp hq).1
    rw [SimpleGraph.mem_neighborFinset] at hmem
    obtain ⟨p, b, hp, hb, hab⟩ := hmem.2
    exact ⟨b, p, hp, hb, hab⟩
  let choiceB : ∀ q, q ∈ S' → V := fun q hq => (hchoice q hq).choose
  let choiceP : ∀ q, q ∈ S' → V := fun q hq => (hchoice q hq).choose_spec.choose
  have hspec : ∀ q (hq : q ∈ S'), Quotient.mk P (choiceP q hq) = Quotient.mk P u ∧
      Quotient.mk P (choiceB q hq) = q ∧ G.Adj (choiceP q hq) (choiceB q hq) :=
    fun q hq => (hchoice q hq).choose_spec.choose_spec
  have hidxb : ∀ q (hq : q ∈ S'), idx u ≤ idx (choiceB q hq) := by
    intro q hq
    obtain ⟨_, a, ha_eq, ha_idx⟩ := Finset.mem_filter.mp hq
    have heq : idx (choiceB q hq) = idx a :=
      hidx_const _ _ (Quotient.exact ((hspec q hq).2.1.trans ha_eq.symm))
    rw [heq]; exact ha_idx
  let f : ∀ q, q ∈ S' → T := fun q hq =>
    ⟨g (choiceB q hq),
      hmaps (choiceP q hq) (choiceB q hq) (hspec q hq).1 (hspec q hq).2.2 (hidxb q hq)⟩
  have hinj_f : ∀ q1 hq1 q2 hq2, f q1 hq1 = f q2 hq2 → q1 = q2 := by
    intro q1 hq1 q2 hq2 hef
    have hg_eq : g (choiceB q1 hq1) = g (choiceB q2 hq2) := Subtype.ext_iff.mp hef
    have hq_eq : Quotient.mk P (choiceB q1 hq1) = Quotient.mk P (choiceB q2 hq2) :=
      hinj (choiceP q1 hq1) (choiceB q1 hq1) (choiceP q2 hq2) (choiceB q2 hq2)
        (hspec q1 hq1).1 (hspec q1 hq1).2.2 (hidxb q1 hq1)
        (hspec q2 hq2).1 (hspec q2 hq2).2.2 (hidxb q2 hq2) hg_eq
    rw [(hspec q1 hq1).2.1, (hspec q2 hq2).2.1] at hq_eq
    exact hq_eq
  let f'' : Quotient P → Option β := fun q => if hq : q ∈ S' then some (f q hq : β) else none
  have hmaps' : ∀ q ∈ S', f'' q ∈ T.image (fun x => some x) := by
    intro q hq; simp [f'', hq]
  have hinj_on : Set.InjOn f'' (S' : Set _) := by
    intro a ha b hb hab
    have ha' : a ∈ S' := ha
    have hb' : b ∈ S' := hb
    simp only [f''] at hab
    rw [dif_pos ha', dif_pos hb'] at hab
    exact hinj_f a ha' b hb' (Subtype.val_inj.mp (Option.some.inj hab))
  calc S'.card = (S'.image f'').card := (Finset.card_image_of_injOn hinj_on).symm
    _ ≤ (T.image (fun x => some x)).card :=
        Finset.card_le_card (Finset.image_subset_iff.mpr hmaps')
    _ = T.card := Finset.card_image_of_injective _ (Option.some_injective _)

end Lax9Proofs
