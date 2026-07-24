import Lax8Proofs.MergeWidthBasic
import Lax8.BoundedMergeWidthLinearNeighborhoodComplexity

/-!
# Linear neighbourhood complexity of bounded merge-width classes

Formalisation of Theorem 1.5 of Bonamy–Geniet: any graph $G$ with radius-2
merge-width at most $k$ has linear neighbourhood complexity.  We prove the
per-graph bound

  $π_G(p) ≤ (k+1) · 2^(k+2) · p$   (for all $p$),

and deduce that every class of bounded merge-width has linear neighbourhood
complexity.

(The paper's constant is $k·2^(k+2)$; we use the very slightly larger
$(k+1)·2^(k+2)$ so that the single argument also covers the degenerate case
$k = 0$ uniformly.)
-/

namespace Lax8Proofs

open Lax8.MergeWidth
open Lax8.NeighborhoodComplexity

open scoped Classical
open Finset

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- The neighbourhood of $v$ within a vertex set $X$ (as used in
$neighborhoodComplexity$). -/
noncomputable def Nb (G : SimpleGraph V) (X : Finset V) (v : V) : Finset V :=
  X.filter (fun u => G.Adj v u)

/-- The vertices adjacent to exactly one of $x$ and $x'$; i.e. the symmetric
difference $N(x) △ N(x')$ of the two neighbourhoods. -/
noncomputable def symmNb (G : SimpleGraph V) (x x' : V) : Finset V :=
  Finset.univ.filter (fun v => G.Adj v x ≠ G.Adj v x')

/-- **From a violation of linearity to an initial obstruction.**
If $π_G(p) > α·p$, there is a set $X$ of size $p$ and a disjoint set $Y$ of
size $> α·p$ whose vertices have pairwise distinct neighbourhoods inside $X$. -/
lemma exists_initial (α p : ℕ) (hviol : α * p < neighborhoodComplexity G p) :
    ∃ X Y : Finset V, Disjoint X Y ∧ X.card = p ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, Nb G X y = Nb G X y' → y = y') ∧
      α * p < Y.card := by
  -- Recipe: $neighborhoodComplexity$ is a $Finset.sup$ over $powersetCard p$.
  -- Use $Finset.lt_sup_iff$ to get $X$ with $X.card = p$ and
  -- $α*p < ((univ \ X).image (Nb G X)).card$.  Let $Y$ be a set of
  -- representatives, one per value of $Nb G X$ on $univ \ X$:
  -- $Y := (((univ \ X).image (Nb G X)).image (fun s => choose a preimage))$.
  -- Then $Y ⊆ univ \ X$ (so $Disjoint X Y$), the map $Nb G X$ is injective on
  -- $Y$, and $Y.card = ((univ \ X).image (Nb G X)).card > α*p$.
  -- Note $neighborhoodComplexity G p$ unfolds to that sup, and
  -- $Nb G X v = X.filter (fun u => G.Adj v u)$.
  unfold neighborhoodComplexity at hviol
  rw [Finset.lt_sup_iff] at hviol
  obtain ⟨X, hXmem, hXgt⟩ := hviol
  -- Define the image set of neighborhoods
  let f := fun v => X.filter fun u => G.Adj v u
  let I := (Finset.univ \ X).image f
  -- For each neighborhood in I, choose a representative vertex from its preimage
  have hex : ∀ s ∈ I, ∃ v ∈ Finset.univ \ X, f v = s := fun s hs => by
    simp only [I, f, Finset.mem_image] at hs
    obtain ⟨v, hv, rfl⟩ := hs
    exact ⟨v, hv, rfl⟩
  -- Use Classical.choose to pick representatives
  choose g hg using hex
  -- Y is the image of the subtype I under g
  let Y : Finset V := Finset.image (fun s : {s // s ∈ I} => g s.val s.prop) (Finset.univ : Finset {s // s ∈ I})
  use X, Y
  refine ⟨?_, ?_, ?_, ?_⟩
  -- Disjoint X Y: Y ⊆ univ \ X
  · rw [Finset.disjoint_left]
    intro y hy hxy
    rw [Finset.mem_image] at hxy
    obtain ⟨s, _, rfl⟩ := hxy
    have hsy := hg s.val s.prop |>.1
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hsy
    exact hsy hy
  -- X.card = p
  · exact (Finset.mem_powersetCard.mp hXmem).2
  -- Nb G X is injective on Y
  · intro y hy y' hy' heq
    rw [Finset.mem_image] at hy hy'
    obtain ⟨⟨s, hs⟩, _, rfl⟩ := hy
    obtain ⟨⟨s', hs'⟩, _, rfl⟩ := hy'
    -- By construction, f (g s hs) = s and f (g s' hs') = s'
    have hfs := hg s hs |>.2
    have hfs' := hg s' hs' |>.2
    simp only [f] at hfs hfs'
    -- Nb G X y = Nb G X y' means f (g s hs) = f (g s' hs'), so s = s'
    have heq' : s = s' := by
      unfold Nb at heq
      rw [hfs, hfs'] at heq
      exact heq
    simp [heq']
  -- Y.card = I.card > α * p
  · -- Y.card = I.card since the map is injective
    rw [show Y = Finset.univ.image (fun s : {s // s ∈ I} => g s.val s.prop) by rfl]
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_univ, Fintype.card_subtype]
      simp only [I]
      convert hXgt using 1
      congr 1
      ext x
      simp [Finset.mem_image, f]
    · intro ⟨s, hs⟩ ⟨s', hs'⟩ heq
      -- If g s hs = g s' hs', then f (g s hs) = f (g s' hs'), so s = s'
      have hfs := hg s hs |>.2
      have hfs' := hg s' hs' |>.2
      simp only [f] at hfs hfs'
      -- From heq, we get f (g s hs) = f (g s' hs'), so s = s'
      have hfeq : g s hs = g s' hs' := heq
      have : (fun v => X.filter fun u => G.Adj v u) (g s hs) = (fun v => X.filter fun u => G.Adj v u) (g s' hs') := by rw [hfeq]
      simp only at this
      rw [hfs, hfs'] at this
      exact Subtype.ext this

/-- **Density increase (Lemma 5.1).**
Given a disjoint pair $(X, Y)$ with $Y$ having pairwise distinct neighbourhoods
in $X$ and $|Y| > α·|X|$, one can shrink it to a pair $(X', Y')$ with the same
properties, still nonempty, and such that moreover any two distinct vertices of
$X'$ have neighbourhoods differing on more than $α$ vertices of $Y'$. -/
lemma exists_dense (α : ℕ) : ∀ n : ℕ, ∀ X Y : Finset V, X.card = n → Disjoint X Y →
    (∀ y ∈ Y, ∀ y' ∈ Y, Nb G X y = Nb G X y' → y = y') → α * X.card < Y.card →
    ∃ X' Y' : Finset V, X' ⊆ X ∧ Disjoint X' Y' ∧
      (∀ y ∈ Y', ∀ y' ∈ Y', Nb G X' y = Nb G X' y' → y = y') ∧
      α * X'.card < Y'.card ∧ (X.Nonempty → X'.Nonempty) ∧
      (∀ x ∈ X', ∀ x' ∈ X', x ≠ x' → α < (Y' ∩ symmNb G x x').card) := by
  -- Recipe: strong induction on $n = X.card$ (use $Nat.strong_induction_on$
  -- or well-founded recursion).  If every distinct pair $x,x' ∈ X$ already has
  -- $α < (Y ∩ symmNb G x x').card$, take $X' = X$, $Y' = Y$.  Otherwise pick a
  -- bad pair $x ≠ x'$ with $(Y ∩ symmNb G x x').card ≤ α$, and recurse on
  -- $X'' = X.erase x'$ and $Y'' = Y \ symmNb G x x'$.
  -- Key facts to maintain:
  -- * $Y''.card ≥ Y.card - (Y ∩ symmNb G x x').card > α*X.card - α = α*X''.card$;
  -- * injectivity over $X''$: if $y, y' ∈ Y''$ (so both agree on $x$ vs $x'$,
  --   i.e. $y, y' ∉ symmNb G x x'$) have $Nb G X'' y = Nb G X'' y'$, then they
  --   also agree at $x'$ (since they agree at $x ∈ X''$ and are outside the
  --   symmetric difference), hence $Nb G X y = Nb G X y'$, so $y = y'$;
  -- * $X''.card = X.card - 1 = n - 1$ and $X.Nonempty → X''.Nonempty$ is used
  --   only when $X.card ≥ 2$ (a bad pair needs two elements).
  intro n X Y hXcard hdisj hinj hYcard
  induction n using Nat.strong_induction_on generalizing X Y with
  | h n ih =>
    -- Check if all pairs are already good
    by_cases hall : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → α < (Y ∩ symmNb G x x').card
    · -- All good: take X' = X, Y' = Y
      use X, Y
      exact ⟨le_refl X, hdisj, hinj, hYcard, fun hne => hne, hall⟩
    · -- There exists a bad pair
      -- Extract the bad pair
      push_neg at hall
      obtain ⟨x, hx, x', hx', hne, hbad⟩ := hall
      -- Take X'' = X.erase x' and Y'' = Y \ symmNb G x x'
      let X'' := X.erase x'
      let Y'' := Y \ symmNb G x x'
      -- Key facts
      have hXsub : X'' ⊆ X := by intro v hv; exact Finset.mem_erase.mp hv |>.2
      have hx''ne : x ∈ X'' := Finset.mem_erase_of_ne_of_mem hne hx
      have hX''ne : X''.Nonempty := ⟨x, hx''ne⟩
      have hXcard'' : X''.card = X.card - 1 := Finset.card_erase_of_mem hx'
      have hx'notin : x' ∉ X'' := fun h => Finset.notMem_erase x' X h
      -- Disjointness
      have hdisj'' : Disjoint X'' Y'' := by
        rw [Finset.disjoint_iff_ne]
        intro v hv w hw hvw
        simp only [X'', Finset.mem_erase] at hv
        simp only [Y'', Finset.mem_sdiff] at hw
        exfalso
        rw [disjoint_iff_inter_eq_empty] at hdisj
        have : v ∈ X ∩ Y := Finset.mem_inter.mpr ⟨hv.2, hvw ▸ hw.1⟩
        rw [hdisj] at this
        contradiction
      -- Cardinality of Y''
      have hYcard'' : Y''.card ≥ Y.card - α := by
        have h1 : Y''.card + (Y ∩ symmNb G x x').card = Y.card := by
          rw [show Y'' = Y \ symmNb G x x' from rfl]
          rw [Finset.card_sdiff_add_card_inter]
        omega
      have hXcard_ge2 : X.card ≥ 2 := by
        have : X.card > 1 := Finset.one_lt_card.2 ⟨x, hx, x', hx', hne⟩
        omega
      -- Injectivity is preserved for Y''
      have hinj'' : ∀ y ∈ Y'', ∀ y' ∈ Y'', Nb G X'' y = Nb G X'' y' → y = y' := by
        intro y hy y' hy' heq
        have hyY : y ∈ Y := Finset.mem_sdiff.mp hy |>.1
        have hy'Y : y' ∈ Y := Finset.mem_sdiff.mp hy' |>.1
        have hynotin : y ∉ symmNb G x x' := Finset.mem_sdiff.mp hy |>.2
        have hy'notin : y' ∉ symmNb G x x' := Finset.mem_sdiff.mp hy' |>.2
        -- x ∈ X'' since x ≠ x'
        have hx_in_X'' : x ∈ X'' := Finset.mem_erase_of_ne_of_mem hne hx
        -- From heq, y and y' agree at x
        have hagen : (G.Adj y x ↔ G.Adj y' x) := by
          simp [Nb] at heq
          have := Finset.ext_iff.mp heq x
          simp at this
          exact this hx_in_X''
        -- From hynotin and hy'notin, they also agree at x'
        simp [symmNb] at hynotin hy'notin
        have hagen' : (G.Adj y x' ↔ G.Adj y' x') := by
          exact hynotin.symm.trans (hagen.trans hy'notin)
        -- Now show Nb G X y = Nb G X y'
        have hNbEq : Nb G X y = Nb G X y' := by
          ext u
          simp [Nb]
          by_cases hux : u ∈ X
          · by_cases hux' : u = x'
            · -- u = x'
              simp [hux', hagen']
            · -- u ∈ X''
              have huX'' : u ∈ X'' := Finset.mem_erase.mpr ⟨hux', hux⟩
              simp [Nb] at heq ⊢
              have := Finset.ext_iff.mp heq u
              simp at this
              exact fun _ => this huX''
          · simp [hux]
        exact hinj y hyY y' hy'Y hNbEq
      -- Apply induction hypothesis
      have hlt : X''.card < n := by omega
      have hYcard''' : α * X''.card < Y''.card := by
        simp only [hXcard'']
        have h1 : Y.card > α * X.card := hYcard
        have h2 : Y.card - α ≥ α * (X.card - 1) + 1 := by
          have hXge1 : X.card ≥ 1 := by omega
          have := Nat.sub_add_cancel (by nlinarith : α ≤ Y.card)
          nlinarith [Nat.sub_add_cancel (by omega : α ≤ Y.card)]
        have h3 : Y''.card ≥ Y.card - α := hYcard''
        omega
      obtain ⟨X', Y', hX'sub, hdisj', hinj', hY'card, hX''ne_imp, hdiff'⟩ := ih (X''.card) hlt X'' Y'' rfl hdisj'' hinj'' hYcard'''
      use X', Y'
      refine ⟨hX'sub.trans hXsub, hdisj', hinj', hY'card, ?_, hdiff'⟩
      intro hXne
      exact hX''ne_imp ⟨x, hx''ne⟩

/-- **Split lemma (Claim 5.2, combinatorial form).**
If $C$ has vertices with pairwise distinct neighbourhoods in $X$ and
$|C| > 2^(k+1)$, then at least $k+1$ vertices of $X$ are neither fully adjacent
nor fully non-adjacent to $C$. -/
lemma exists_split (k : ℕ) (X C : Finset V)
    (hCinj : ∀ c ∈ C, ∀ c' ∈ C, Nb G X c = Nb G X c' → c = c')
    (hC : 2 ^ (k + 1) < C.card) :
    k + 1 ≤ (X.filter (fun x => (∃ c ∈ C, G.Adj x c) ∧ (∃ c ∈ C, ¬ G.Adj x c))).card := by
  -- Recipe: let $S$ be the filtered "split" set.  A vertex $x ∈ X \ S$ is
  -- constant on $C$ (adjacent to all of $C$ or to none).  Hence the map
  -- $C → Finset V$, $c ↦ Nb G S c = S.filter (fun x => G.Adj c x)$ is injective
  -- on $C$: if $Nb G S c = Nb G S c'$, then also $Nb G X c = Nb G X c'$
  -- (they agree on $S$ by assumption and on $X \ S$ since those are constant),
  -- so $c = c'$ by $hCinj$.  Therefore
  -- $C.card ≤ (S.powerset).card = 2 ^ S.card$.  With $2^(k+1) < C.card$ this
  -- gives $2^(k+1) < 2^S.card$, so $k+1 < S.card$, i.e. $k+1 ≤ S.card$.
  -- Let S be the split set
  set S := X.filter (fun x => (∃ c ∈ C, G.Adj x c) ∧ (∃ c ∈ C, ¬ G.Adj x c)) with hSdef

  -- Any two elements of C have the same neighborhood in X iff they have the same neighborhood in S
  -- First prove injectivity of c ↦ Nb G S c
  have hinj_S : ∀ c ∈ C, ∀ c' ∈ C, Nb G S c = Nb G S c' → c = c' := by
    intro c hc c' hc' h_eq
    apply hCinj c hc c' hc'
    -- Need to show Nb G X c = Nb G X c'
    -- They agree on S by h_eq, and on X \ S since those are constant
    ext x
    show x ∈ X.filter (fun u => G.Adj c u) ↔ x ∈ X.filter (fun u => G.Adj c' u)
    by_cases hxS : x ∈ S
    · -- x ∈ S, so c and c' agree on x
      -- Goal: x ∈ X.filter (fun u => G.Adj c u) ↔ x ∈ X.filter (fun u => G.Adj c' u)
      have hxS_in_X : x ∈ X := by
        rw [hSdef] at hxS
        exact Finset.mem_filter.mp hxS |>.1
      have hS_filter : S.filter (fun y => G.Adj c y) = S.filter (fun y => G.Adj c' y) := h_eq
      have hmem : G.Adj c x ↔ G.Adj c' x := by
        have h1 : x ∈ S.filter (fun y => G.Adj c y) ↔ x ∈ S.filter (fun y => G.Adj c' y) := by rw [hS_filter]
        rw [Finset.mem_filter] at hxS h1
        simp at h1
        have hxS' : x ∈ S := by
          rw [hSdef]
          simp only [Finset.mem_filter]
          exact ⟨hxS.1, hxS.2⟩
        exact h1 hxS'
      rw [Finset.mem_filter, Finset.mem_filter]
      exact ⟨fun ⟨_, h⟩ => ⟨hxS_in_X, hmem.mp h⟩, fun ⟨_, h⟩ => ⟨hxS_in_X, hmem.mpr h⟩⟩
    · -- x ∉ S means x is constant on C (either all adjacent or all non-adjacent)
      simp only [hSdef, Finset.mem_filter] at hxS
      by_cases hxX : x ∈ X
      · by_cases hall : ∀ c ∈ C, G.Adj x c
        · have hac := hall c hc
          have hac' := hall c' hc'
          rw [SimpleGraph.adj_comm] at hac hac'
          simp [hxX, hac, hac']
        · push_neg at hall
          have hall' : ∀ c ∈ C, ¬G.Adj x c := by
            intro y hy
            by_contra hadj
            have h1 : ∃ c ∈ C, G.Adj x c := ⟨y, hy, hadj⟩
            exact hxS ⟨hxX, h1, hall⟩
          have hcx : ¬G.Adj x c := hall' c hc
          have hcx' : ¬G.Adj x c' := hall' c' hc'
          rw [SimpleGraph.adj_comm] at hcx hcx'
          simp [hxX, hcx, hcx']
      · simp [hxX]
  -- So C.card ≤ 2^S.card
  have hcard : C.card ≤ 2 ^ S.card := by
    have hinj : Set.InjOn (fun c => Nb G S c) C := by
      intro c hc c' hc' h_eq
      exact hinj_S c hc c' hc' h_eq
    have himage : (C.image (fun c => Nb G S c)).card = C.card := Finset.card_image_of_injOn hinj
    have hsub : C.image (fun c => Nb G S c) ⊆ S.powerset := by
      intro y hy
      simp at hy
      obtain ⟨c, hc, rfl⟩ := hy
      simp [Finset.mem_powerset]
      exact Finset.filter_subset _ _
    calc C.card = (C.image (fun c => Nb G S c)).card := himage.symm
      _ ≤ (S.powerset).card := Finset.card_le_card hsub
      _ = 2 ^ S.card := Finset.card_powerset _
  -- From 2^(k+1) < C.card and C.card ≤ 2^S.card, get k+1 < S.card
  have hk1_lt : k + 1 < S.card := by
    by_contra hle
    push_neg at hle
    have hpow : 2 ^ (k + 1) ≥ 2 ^ S.card := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hle
    linarith
  exact Nat.le_of_lt hk1_lt

/-- The number of accessible parts is bounded by the width (for a valid step). -/
lemma neighborhood_numAccessible_le_width (S : MergeSeq G) (r i : ℕ) (hi2 : 2 ≤ i)
    (hilen : i ≤ S.length) (v : V) : S.numAccessible r i v ≤ S.width r := by
  -- Recipe: $S.width r = (Finset.Icc 2 S.length).sup (fun i => univ.sup (...))$.
  -- Apply $Finset.le_sup$ twice: $i ∈ Finset.Icc 2 S.length$ (from $hi2$,$hilen$)
  -- and $v ∈ Finset.univ$.
  apply le_trans (Finset.le_sup (f := fun v => S.numAccessible r i v) (by simp : v ∈ Finset.univ))
  apply Finset.le_sup (f := fun i => Finset.univ.sup (fun v => S.numAccessible r i v)) (by simp [Finset.mem_Icc, hi2, hilen])

/-- A finset contained in a resolved ball has at most $numAccessible$-many parts. -/
lemma card_image_part_le_numAccessible (S : MergeSeq G) (r i : ℕ) (v : V) (T : Finset V)
    (hT : ∀ u ∈ T, u ∈ resolvedBall (S.resolved i) r v) :
    (T.image (fun u => Quotient.mk (S.part (i - 1)) u)).card ≤ S.numAccessible r i v := by
  -- Recipe: $S.numAccessible r i v$ unfolds to
  -- $Set.ncard ((fun u => Quotient.mk (S.part (i-1)) u) '' resolvedBall ..)$.
  -- The finset image $T.image f$ coerces to $f '' ↑T ⊆ f '' resolvedBall ..$.
  -- Use $Set.ncard_le_ncard$ (the big set is finite: subset of $univ$) and
  -- $Set.ncard_coe_Finset$ to identify $(T.image f).card$ with the $ncard$ of
  -- its coercion.
  have hTset : (T : Set V) ⊆ resolvedBall (S.resolved i) r v := by
    intro u hu
    exact hT u (Finset.mem_coe.mp hu)
  have hfT_subset : (fun u => Quotient.mk (S.part (i - 1)) u) '' (T : Set V) ⊆
      (fun u => Quotient.mk (S.part (i - 1)) u) '' resolvedBall (S.resolved i) r v :=
    Set.image_mono hTset
  have hcard_eq : (T.image (fun u => Quotient.mk (S.part (i - 1)) u)).card =
      Set.ncard ((fun u => Quotient.mk (S.part (i - 1)) u) '' (T : Set V)) := by
    rw [← Set.ncard_coe_finset]
    simp [Finset.coe_image]
  calc (T.image (fun u => Quotient.mk (S.part (i - 1)) u)).card
      = Set.ncard ((fun u => Quotient.mk (S.part (i - 1)) u) '' (T : Set V)) := hcard_eq
    _ ≤ Set.ncard ((fun u => Quotient.mk (S.part (i - 1)) u) '' resolvedBall (S.resolved i) r v) :=
        Set.ncard_le_ncard hfT_subset (Set.toFinite _)
    _ = S.numAccessible r i v := rfl

/-- **The core contradiction.**
A dense obstruction as produced by $exists_dense$ cannot exist in a graph with a
merge sequence of radius-2 width $≤ k$. -/
lemma no_dense_obstruction (k : ℕ) (S : MergeSeq G) (hS : S.width 2 ≤ k)
    (X Y : Finset V) (hdisj : Disjoint X Y) (hX2 : 2 ≤ X.card)
    (hYinj : ∀ y ∈ Y, ∀ y' ∈ Y, Nb G X y = Nb G X y' → y = y')
    (hdiff : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → k * 2 ^ (k + 2) < (Y ∩ symmNb G x x').card) :
    False := by
  classical
  -- Two distinct vertices of $X$.
  obtain ⟨x0, x0', hx0, hx0', hx0ne⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < X.card)
  -- The first step at which two vertices of $X$ are merged.
  set pred : ℕ → Prop := fun i => ∃ a ∈ X, ∃ b ∈ X, a ≠ b ∧ (S.part i).r a b with hpreddef
  have hpredlen : pred S.length :=
    ⟨x0, hx0, x0', hx0', hx0ne, by rw [S.part_length]; trivial⟩
  have hFne : ((Finset.Icc 1 S.length).filter pred).Nonempty :=
    ⟨S.length, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨S.one_le_length, le_refl _⟩, hpredlen⟩⟩
  set i0 := ((Finset.Icc 1 S.length).filter pred).min' hFne with hi0def
  have hi0mem := Finset.min'_mem _ hFne
  rw [Finset.mem_filter, Finset.mem_Icc] at hi0mem
  obtain ⟨⟨hi0_1, hi0_len⟩, x, hx, y, hy, hxyne, hxyrel⟩ := hi0mem
  rw [← hi0def] at hi0_1 hi0_len hxyrel
  -- $i0 ≥ 2$.
  have hi02 : 2 ≤ i0 := by
    rcases Nat.lt_or_ge i0 2 with h | h
    · exfalso
      have h1 : i0 = 1 := by omega
      rw [h1, S.part_one] at hxyrel
      exact hxyne hxyrel
    · exact h
  -- At step $i0 - 1$, distinct vertices of $X$ lie in distinct parts.
  have hi0m1_notpred : ¬ pred (i0 - 1) := by
    intro hp
    have hmem : i0 - 1 ∈ (Finset.Icc 1 S.length).filter pred :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hp⟩
    have := Finset.min'_le _ _ hmem
    omega
  have hDistinct : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → ¬ (S.part (i0 - 1)).r a b := by
    intro a ha b hb hab hr
    exact hi0m1_notpred ⟨a, ha, b, hb, hab, hr⟩
  -- The dense set $A = Y ∩ △(x,y)$.
  have hAcard : k * 2 ^ (k + 2) < (Y ∩ symmNb G x y).card := hdiff x hx y hy hxyne
  set A := Y ∩ symmNb G x y with hAdef
  have hAsubY : A ⊆ Y := Finset.inter_subset_left
  have hAne : ∀ a ∈ A, a ≠ x ∧ a ≠ y := by
    intro a ha
    have haY : a ∈ Y := hAsubY ha
    constructor
    · rintro rfl; exact (Finset.disjoint_left.mp hdisj hx) haY
    · rintro rfl; exact (Finset.disjoint_left.mp hdisj hy) haY
  have hres : ∀ a ∈ A, (S.resolved i0).Adj a x ∨ (S.resolved i0).Adj a y := by
    intro a ha
    have hsymm : G.Adj a x ≠ G.Adj a y := by
      have h := (Finset.mem_inter.mp ha).2
      simpa [symmNb] using h
    exact uniform_resolved S (by omega) hi0_len hxyrel (hAne a ha).1 (hAne a ha).2 hsymm
  -- Split $A$ according to which of $x$, $y$ the resolved pair reaches.
  set Bx := A.filter (fun a => (S.resolved i0).Adj a x) with hBxdef
  set By := A.filter (fun a => (S.resolved i0).Adj a y) with hBydef
  have hcover : A ⊆ Bx ∪ By := by
    intro a ha
    rcases hres a ha with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha, h⟩)
  have hcardsum : A.card ≤ Bx.card + By.card :=
    le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
  set m := 2 ^ (k + 1) with hm
  have hpow2 : 2 ^ (k + 2) = 2 * m := by rw [hm, pow_succ]; ring
  rw [hpow2] at hAcard
  have hmax : k * m < Bx.card ∨ k * m < By.card := by
    by_contra hc
    push_neg at hc
    nlinarith [hcardsum, hAcard, hc.1, hc.2]
  -- The core argument, applied to whichever of $x$, $y$ gets the larger half.
  have core : ∀ z ∈ X, ∀ B : Finset V, B ⊆ Y → (∀ b ∈ B, (S.resolved i0).Adj b z) →
      k * m < B.card → False := by
    intro z hzX B hBY hBadj hBcard
    have hBball : ∀ b ∈ B, b ∈ resolvedBall (S.resolved i0) 2 z := by
      intro b hb
      have hb1 : b ∈ resolvedBall (S.resolved i0) 1 z :=
        mem_resolvedBall_of_adj (S.resolved i0) (le_refl 1) ((hBadj b hb).symm)
      exact resolvedBall_mono (S.resolved i0) (by norm_num) z hb1
    have hpartsB : (B.image (fun u => Quotient.mk (S.part (i0 - 1)) u)).card ≤ k :=
      le_trans (card_image_part_le_numAccessible S 2 i0 z B hBball)
        (le_trans (neighborhood_numAccessible_le_width S 2 i0 hi02 hi0_len z) hS)
    obtain ⟨q, _, hqcard⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := B) (t := B.image (fun u => Quotient.mk (S.part (i0 - 1)) u))
      (f := fun u => Quotient.mk (S.part (i0 - 1)) u) (n := m)
      (fun b hb => Finset.mem_image_of_mem _ hb)
      (lt_of_le_of_lt (Nat.mul_le_mul_right m hpartsB) hBcard)
    set C := {b ∈ B | (fun u => Quotient.mk (S.part (i0 - 1)) u) b = q} with hCdef
    have hCsubB : C ⊆ B := Finset.filter_subset _ _
    have hCY : C ⊆ Y := hCsubB.trans hBY
    have hCrel : ∀ c ∈ C, ∀ c' ∈ C, (S.part (i0 - 1)).r c c' := by
      intro c hc c' hc'
      have e1 : Quotient.mk (S.part (i0 - 1)) c = q := (Finset.mem_filter.mp hc).2
      have e2 : Quotient.mk (S.part (i0 - 1)) c' = q := (Finset.mem_filter.mp hc').2
      exact Quotient.eq.mp (e1.trans e2.symm)
    have hCinj : ∀ c ∈ C, ∀ c' ∈ C, Nb G X c = Nb G X c' → c = c' :=
      fun c hc c' hc' h => hYinj c (hCY hc) c' (hCY hc') h
    have hqcard' : 2 ^ (k + 1) < C.card := hqcard
    have hsplit := exists_split k X C hCinj hqcard'
    set Ssplit := X.filter (fun a => (∃ c ∈ C, G.Adj a c) ∧ (∃ c ∈ C, ¬ G.Adj a c)) with hSdef
    have hSsubX : Ssplit ⊆ X := Finset.filter_subset _ _
    have hSball : ∀ xj ∈ Ssplit, xj ∈ resolvedBall (S.resolved i0) 2 z := by
      intro xj hxj
      have hxjX : xj ∈ X := hSsubX hxj
      obtain ⟨⟨c1, hc1, hadj1⟩, ⟨c2, hc2, hadj2⟩⟩ := (Finset.mem_filter.mp hxj).2
      have hne_xc : ∀ c ∈ C, xj ≠ c := by
        rintro c hcC rfl; exact (Finset.disjoint_left.mp hdisj hxjX) (hCY hcC)
      have hrel12 : (S.part i0).r c1 c2 :=
        Setoid.le_def.mp (S.part_mono (by omega) (by omega) hi0_len) (hCrel c1 hc1 c2 hc2)
      have hdiffadj : G.Adj xj c1 ≠ G.Adj xj c2 := by
        intro h; rw [h] at hadj1; exact hadj2 hadj1
      rcases uniform_resolved S (by omega) hi0_len hrel12 (hne_xc c1 hc1) (hne_xc c2 hc2) hdiffadj
        with h | h
      · exact mem_resolvedBall_two (S.resolved i0) ((hBadj c1 (hCsubB hc1)).symm) h.symm
      · exact mem_resolvedBall_two (S.resolved i0) ((hBadj c2 (hCsubB hc2)).symm) h.symm
    have hginj : Set.InjOn (fun u => Quotient.mk (S.part (i0 - 1)) u) (Ssplit : Set V) := by
      intro a ha b hb hab
      by_contra hne'
      exact hDistinct a (hSsubX (by exact_mod_cast ha)) b (hSsubX (by exact_mod_cast hb)) hne'
        (Quotient.eq.mp hab)
    have hcardimg : (Ssplit.image (fun u => Quotient.mk (S.part (i0 - 1)) u)).card = Ssplit.card :=
      Finset.card_image_of_injOn hginj
    have hle_k : Ssplit.card ≤ k := by
      rw [← hcardimg]
      exact le_trans (card_image_part_le_numAccessible S 2 i0 z Ssplit hSball)
        (le_trans (neighborhood_numAccessible_le_width S 2 i0 hi02 hi0_len z) hS)
    omega
  rcases hmax with h | h
  · exact core x hx Bx ((Finset.filter_subset _ _).trans hAsubY)
      (fun b hb => (Finset.mem_filter.mp hb).2) h
  · exact core y hy By ((Finset.filter_subset _ _).trans hAsubY)
      (fun b hb => (Finset.mem_filter.mp hb).2) h

/-- **Theorem 1.5 (per graph).**
If $G$ has a merge sequence of radius-2 width $≤ k$, then
$π_G(p) ≤ (k+1)·2^(k+2)·p$ for $p ≥ 1$. -/
theorem neighborhoodComplexity_le (k : ℕ) (S : MergeSeq G) (hS : S.width 2 ≤ k)
    (p : ℕ) (hp : 1 ≤ p) : neighborhoodComplexity G p ≤ (k + 1) * 2 ^ (k + 2) * p := by
  by_contra hcon
  push_neg at hcon
  -- Abbreviate the constant.
  set α := (k + 1) * 2 ^ (k + 2) with hα
  have h4 : 4 ≤ 2 ^ (k + 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hα2 : 2 ≤ α := by nlinarith
  -- Get an initial obstruction, then densify it.
  obtain ⟨X0, Y0, hdisj0, hcard0, hinj0, hY0⟩ := exists_initial α p hcon
  have hX0ne : X0.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨X, Y, hXsub, hdisj, hinj, hYcard, hne, hdiff⟩ :=
    exists_dense (G := G) α X0.card X0 Y0 rfl hdisj0 hinj0 (by rw [hcard0]; exact hY0)
  have hXne : X.Nonempty := hne hX0ne
  -- Every element of $Y$ has a distinct neighbourhood in $X$, hence $|Y| ≤ 2^|X|$.
  have hYle : Y.card ≤ 2 ^ X.card := by
    calc Y.card ≤ X.powerset.card :=
          Finset.card_le_card_of_injOn (fun y => Nb G X y)
            (fun y _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _))
            (fun y hy y' hy' h => hinj y hy y' hy' h)
      _ = 2 ^ X.card := Finset.card_powerset X
  -- Deduce $|X| ≥ 2$.
  have hX2 : 2 ≤ X.card := by
    rcases Nat.lt_or_ge X.card 2 with h | h
    · exfalso
      have hc1 : X.card = 1 := by
        have := Finset.card_pos.2 hXne; omega
      rw [hc1] at hYle hYcard
      simp only [pow_one] at hYle
      omega
    · exact h
  -- Contradiction with the merge sequence.
  refine no_dense_obstruction k S hS X Y hdisj hX2 hinj (fun x hx x' hx' hxne => ?_)
  have hle : k * 2 ^ (k + 2) ≤ α := by rw [hα]; nlinarith
  exact lt_of_le_of_lt hle (hdiff x hx x' hx' hxne)

/--
---
conclusion: Lax8.BoundedMergeWidthLinearNeighborhoodComplexity.bounded_mergeWidth_linearNeighborhoodComplexity
---
Theorem 1.5 of Bonamy–Geniet: every graph class of bounded merge-width has
linear neighbourhood complexity.
-/
theorem linearNeighborhoodComplexity_of_boundedMergeWidth
    (C : GraphClass) (h : BoundedMergeWidth C) : LinearNeighborhoodComplexity C := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(f 2 + 1) * 2 ^ (f 2 + 2), ?_⟩
  intro V _ G hG p hp
  obtain ⟨S, hS⟩ := (mergeWidth_le_iff 2 (f 2)).1 (hf G hG 2)
  exact neighborhoodComplexity_le (f 2) S hS p hp

end Lax8Proofs
