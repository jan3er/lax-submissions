import Lax5.AdlerAdler
import Lax5Proofs.QuasiWideness
import Lax5Proofs.BallSwap
import Mathlib.Combinatorics.Pigeonhole

/-!
Adler–Adler, backward direction: nowhere dense graph classes are
monadically dependent.  This discharges the open concept obligation
`Lax5.AdlerAdler.monadicallyDependent_of_nowhereDense`.

Proof layout (uniform quasi-wideness + locality, the deletion
specialization of the flip-breakability argument):

* If `C` transduces all graphs, it produces every powerset bipartite
  graph, so the edge formula `φ` of the transduction *shatters*
  arbitrarily large vertex sets in colored members of `C`: a set `W`
  of images of the left side, and for every Boolean pattern on `W` a
  realizer whose `φ`-trace on `W` is exactly that pattern.
* Uniform quasi-wideness (from nowhere-denseness) finds inside `W`,
  after deleting a set `S` of at most `s` vertices, a subset that is
  pairwise `3^(q+2)`-independent in `G − S`, of any requested size.
* Color every vertex by the rank-`lvl q q` local type of its decorated
  `H`-ball (`H = G − S`; decorations record colors and `S`-adjacency);
  there are at most `t` colors, uniformly in the graph.  A pigeonhole
  gives `s + 4` scattered vertices of one color.
* Realizers for the `s + 2` traces `{first, j-th}` are pairwise
  distinct, so one of them, `v`, avoids `S`.  The ball-swap lemma
  forces `v` to be `3^q`-close in `H` to one of the first two vertices
  and to one of two later ones — two distinct scattered vertices at
  `H`-distance at most `2·3^q < 3^(q+2)`, a contradiction.
-/

namespace Lax5Proofs.AdlerAdler

open FirstOrder Lax5.Transductions Lax5.GraphClasses Lax12.GraphClasses
open Lax5Proofs.LocalTypes Lax5Proofs.EFAgreement Lax5Proofs.BallSwap
open Lax12.UniformQuasiWideness

/-! ### Powerset graphs -/

/-- The powerset bipartite graph: left vertices `Fin d`, right vertices
the Boolean patterns, with `i` adjacent to `s` iff `s i`. -/
def powGraph (d : ℕ) : SimpleGraph (Fin d ⊕ (Fin d → Bool)) where
  Adj x y := match x, y with
    | .inl i, .inr s => s i = true
    | .inr s, .inl i => s i = true
    | _, _ => False
  symm := by rintro (i | s) (i' | s') h <;> first | exact h | exact h.elim
  loopless := ⟨by rintro (i | s) h <;> exact h⟩

/-- A bijection of the powerset graph's vertices with a canonical
`Fin`. -/
noncomputable def psEquiv (d : ℕ) :
    (Fin d ⊕ (Fin d → Bool)) ≃ Fin (d + 2 ^ d) :=
  (Equiv.sumCongr (Equiv.refl _)
    (Fintype.equivFinOfCardEq (by simp))).trans finSumFinEquiv

/-- The powerset bipartite graph on the canonical carrier. -/
noncomputable def powFin (d : ℕ) : SimpleGraph (Fin (d + 2 ^ d)) :=
  SimpleGraph.comap (fun a => (psEquiv d).symm a) (powGraph d)

lemma powFin_adj (d : ℕ) (sb : Fin d → Bool) (i : Fin d) :
    (powFin d).Adj (psEquiv d (Sum.inr sb)) (psEquiv d (Sum.inl i)) ↔
      sb i = true := by
  show (powGraph d).Adj ((psEquiv d).symm (psEquiv d (Sum.inr sb)))
    ((psEquiv d).symm (psEquiv d (Sum.inl i))) ↔ _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact Iff.rfl

/-! ### The theorem -/

/--
---
conclusion: Lax5.AdlerAdler.monadicallyDependent_of_nowhereDense
assumptions:
  - Lax12.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense
---
Nowhere dense graph classes are monadically dependent (Adler–Adler).

# Proof strategy

The quasi-wideness input is not reproved here: uniform quasi-wideness of
a nowhere dense class is assumed from the `sparsity-lectures` submission,
whose nowhere-denseness definition is the very one this statement is
phrased over, so no transport is needed —
`Lax5Proofs.QuasiWideness` only reshapes the conclusion from `Set` to
`Finset`.  Everything below it — shattering, local types, ball swapping
and the pigeonhole — is proved here, as sketched in the module docstring.
-/
theorem monadicallyDependent_of_nowhereDense
    (C : GraphClass)
    (h : Lax12.NowhereDenseClasses.NowhereDense C) :
    Lax5.MonadicDependence.MonadicallyDependent C := by
  classical
  intro hT
  obtain ⟨T, hprod⟩ := hT
  set k := T.colors with hk
  set φ : (withColors Language.graph k).Formula (Fin 2) :=
    T.rel Language.adj with hφ
  set q := qrank φ with hq
  -- uniform quasi-wideness at the swap radius
  obtain ⟨N, s, huqw⟩ := Lax5Proofs.QuasiWideness.uqw_of_nowhereDense C h
    (3 ^ (q + 2))
  -- color count, target sizes
  set t := Fintype.card
    (LType ((Fin k → Bool) × (Fin s → Bool)) (RR q) (lvl q q) 1) with ht
  set m := (t + 1) * (s + 4) with hm
  set d := max (N m) 1 with hd
  -- the transduction produces the powerset graph
  have hps : Lax5.GraphTransductions.structureClass allGraphs (d + 2 ^ d)
      (powFin d).structure := ⟨powFin d, trivial, rfl⟩
  obtain ⟨n, M, hM, colors, f, -, hrel⟩ := hprod _ _ hps
  obtain ⟨G, hG, rfl⟩ := hM
  -- the adjacency formula defines powerset adjacency on the images
  have hadj : ∀ a b : Fin (d + 2 ^ d), (powFin d).Adj a b ↔
      RealizeIn G.structure colors φ ![f a, f b] := by
    intro a b
    have hfv : f ∘ ![a, b] = ![f a, f b] := by
      funext i
      refine Fin.cases rfl (fun i₁ => ?_) i
      exact Fin.cases rfl (fun i₂ => i₂.elim0) i₁
    have := hrel Language.adj ![a, b]
    rwa [hfv] at this
  -- shattering data
  set ι : Fin d → Fin n := fun i => f (psEquiv d (Sum.inl i)) with hι
  set rz : (Fin d → Bool) → Fin n := fun sb => f (psEquiv d (Sum.inr sb))
    with hrz
  have hshatter : ∀ (sb : Fin d → Bool) (i : Fin d),
      RealizeIn G.structure colors φ ![rz sb, ι i] ↔ sb i = true := by
    intro sb i
    exact (hadj _ _).symm.trans (powFin_adj d sb i)
  have hιinj : Function.Injective ι := by
    intro i i' hii
    have h1 := f.injective hii
    have h2 := (psEquiv d).injective h1
    exact Sum.inl.inj h2
  -- run uniform quasi-wideness on the image of the left side
  set A : Finset (Fin n) := Finset.univ.image ι with hA
  have hAcard : N m ≤ A.card := by
    rw [hA, Finset.card_image_of_injective _ hιinj, Finset.card_univ,
      Fintype.card_fin]
    exact le_max_left _ _
  obtain ⟨S, B, hScard, hBsub, hBcard, hBind⟩ := huqw m n G hG A hAcard
  set H : SimpleGraph (Fin n) := deleteVerts G ↑S with hHdef
  have hH : ∀ a b, H.Adj a b ↔ (G.Adj a b ∧ a ∉ S ∧ b ∉ S) := by
    intro a b
    show (G.Adj a b ∧ a ∉ (↑S : Set (Fin n)) ∧ b ∉ (↑S : Set (Fin n))) ↔ _
    simp
  -- scatteredness of B, phrased through WLE
  have hBfar : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → ∀ dd, dd ≤ 3 ^ (q + 2) →
      ¬ WLE H x y dd := by
    intro x hx y hy hne dd hdd ⟨p, hp⟩
    have := hBind (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hne p
    omega
  have hBAS : ∀ x ∈ B, x ∈ A ∧ x ∉ S := by
    intro x hx
    have h1 := hBsub (Finset.mem_coe.mpr hx)
    exact Finset.mem_sdiff.mp (Finset.mem_coe.mp h1)
  have hBnotS : ∀ x ∈ B, x ∉ S := fun x hx => (hBAS x hx).2
  have hBinA : ∀ x ∈ B, x ∈ A := fun x hx => (hBAS x hx).1
  -- a default vertex and the enumeration of S
  have hd1 : 1 ≤ d := le_max_right _ 1
  set w₀ : Fin n := ι ⟨0, hd1⟩ with hw₀
  set senum : Fin s → Fin n := fun i =>
    if hi : (i : ℕ) < S.toList.length then S.toList.get ⟨i, hi⟩ else w₀
    with hsenumdef
  have hsenum : ∀ x ∈ S, ∃ i : Fin s, senum i = x := by
    intro x hx
    obtain ⟨j, hget⟩ := List.mem_iff_get.mp (S.mem_toList.mpr hx)
    have hjs : (j : ℕ) < s := by
      have h1 := j.isLt
      have h2 : S.toList.length = S.card := S.length_toList
      omega
    refine ⟨⟨j, hjs⟩, ?_⟩
    have hj' : ((⟨j, hjs⟩ : Fin s) : ℕ) < S.toList.length := j.isLt
    simp only [hsenumdef, dif_pos hj']
    exact hget
  -- decorated local-type coloring
  set dec : Fin n → (Fin k → Bool) × (Fin s → Bool) := fun x =>
    (fun i => pb (x ∈ colors i), fun i => pb (G.Adj (senum i) x)) with hdec
  set col : Fin n → LType ((Fin k → Bool) × (Fin s → Bool)) (RR q)
      (lvl q q) 1 := fun w => ltype H dec w (RR q) (lvl q q)
      (fun _ : Fin 1 => w) with hcol
  -- a monochromatic scattered subset of size s + 4
  have hpigeon : ∃ cv, s + 4 ≤ (B.filter fun x => col x = cv).card := by
    obtain ⟨cv, _, hcv⟩ :=
      Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (s := B) (t := Finset.univ) (f := col)
        (fun a _ => Finset.mem_univ (col a))
        ⟨col w₀, Finset.mem_univ _⟩ (by
          rw [Finset.card_univ]
          calc Fintype.card _ * (s + 4) = t * (s + 4) := rfl
            _ ≤ (t + 1) * (s + 4) :=
              Nat.mul_le_mul_right _ (Nat.le_succ t)
            _ ≤ B.card := hBcard)
    exact ⟨cv, hcv⟩
  obtain ⟨cv, hcv⟩ := hpigeon
  set B' : Finset (Fin n) := B.filter fun x => col x = cv with hB'
  have hB'B : ∀ x ∈ B', x ∈ B := fun x hx => (Finset.mem_filter.mp hx).1
  have hB'col : ∀ x ∈ B', col x = cv := fun x hx =>
    (Finset.mem_filter.mp hx).2
  -- s + 4 distinct monochromatic scattered vertices
  obtain ⟨g, hg⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin (s + 4)) (s := B') (by simpa using hcv)
  have hgB' : ∀ idx, g idx ∈ B' :=
    fun idx => Finset.mem_coe.mp (hg (Set.mem_range_self idx))
  have hgB : ∀ idx, g idx ∈ B := fun idx => hB'B _ (hgB' idx)
  have hgcol : ∀ idx, col (g idx) = cv := fun idx => hB'col _ (hgB' idx)
  have hgnotS : ∀ idx, g idx ∉ S := fun idx => hBnotS _ (hgB idx)
  -- indices of the chosen vertices inside W
  have hgι : ∀ idx, ∃ i : Fin d, ι i = g idx := by
    intro idx
    have := hBinA _ (hgB idx)
    rw [hA] at this
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp this
    exact ⟨i, hi⟩
  choose iOf hiOf using hgι
  -- distinguished indices
  set idx0 : Fin (s + 4) := ⟨0, by omega⟩ with hidx0
  set idx1 : Fin (s + 4) := ⟨1, by omega⟩ with hidx1
  -- the index of the j-th later vertex
  set cIdx : Fin (s + 2) → Fin (s + 4) := fun j => ⟨(j : ℕ) + 2, by omega⟩
    with hcIdx
  have hcIdx0 : ∀ j, cIdx j ≠ idx0 := by
    intro j hj
    have : (j : ℕ) + 2 = 0 := congrArg Fin.val hj
    omega
  have hcIdx1 : ∀ j, cIdx j ≠ idx1 := by
    intro j hj
    have : (j : ℕ) + 2 = 1 := congrArg Fin.val hj
    omega
  have hidx01 : idx0 ≠ idx1 := by
    intro hj
    have : (0 : ℕ) = 1 := congrArg Fin.val hj
    omega
  have hcIdxinj : ∀ j j', cIdx j = cIdx j' → j = j' := by
    intro j j' hj
    have : (j : ℕ) + 2 = (j' : ℕ) + 2 := congrArg Fin.val hj
    exact Fin.ext (by omega)
  -- realizers for the traces {g idx0, g (cIdx j)}
  set sb : Fin (s + 2) → Fin d → Bool := fun j i =>
    pb (ι i = g idx0 ∨ ι i = g (cIdx j)) with hsb
  set rlz : Fin (s + 2) → Fin n := fun j => rz (sb j) with hrlz
  have htrace : ∀ (j : Fin (s + 2)) (i : Fin d),
      RealizeIn G.structure colors φ ![rlz j, ι i] ↔
        (ι i = g idx0 ∨ ι i = g (cIdx j)) :=
    fun j i => (hshatter (sb j) i).trans pb_iff
  have htrace' : ∀ (j : Fin (s + 2)) (idx : Fin (s + 4)),
      RealizeIn G.structure colors φ ![rlz j, g idx] ↔
        (g idx = g idx0 ∨ g idx = g (cIdx j)) := by
    intro j idx
    have := htrace j (iOf idx)
    rwa [hiOf idx] at this
  -- the realizers are pairwise distinct, so one avoids S
  have hrlz_ne : ∀ j j', j ≠ j' → rlz j ≠ rlz j' := by
    intro j j' hne heq
    have h1 : RealizeIn G.structure colors φ ![rlz j, g (cIdx j)] :=
      (htrace' j (cIdx j)).mpr (Or.inr rfl)
    rw [heq] at h1
    rcases (htrace' j' (cIdx j)).mp h1 with hc | hc
    · exact hcIdx0 j (g.injective hc)
    · exact hne (hcIdxinj _ _ (g.injective hc))
  have hescape : ∃ j, rlz j ∉ S := by
    by_contra hcon
    push_neg at hcon
    have : (Finset.univ.image rlz).card ≤ S.card :=
      Finset.card_le_card (fun x hx => by
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
        exact hcon j)
    rw [Finset.card_image_of_injective _
      (fun j j' hjj => by_contra fun hne => hrlz_ne j j' hne hjj),
      Finset.card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨j₀, hj₀S⟩ := hescape
  -- a second later vertex
  have hi₂ : ∃ i₂ : Fin (s + 2), i₂ ≠ j₀ := by
    rcases Nat.eq_zero_or_pos (j₀ : ℕ) with h0 | h0
    · refine ⟨⟨1, by omega⟩, fun hcon => ?_⟩
      have : (1 : ℕ) = (j₀ : ℕ) := congrArg Fin.val hcon
      omega
    · refine ⟨⟨0, by omega⟩, fun hcon => ?_⟩
      have : (0 : ℕ) = (j₀ : ℕ) := congrArg Fin.val hcon
      omega
  obtain ⟨i₂, hi₂ne⟩ := hi₂
  -- the four truth values
  have hT1 : RealizeIn G.structure colors φ ![rlz j₀, g idx0] :=
    (htrace' j₀ idx0).mpr (Or.inl rfl)
  have hT2 : ¬ RealizeIn G.structure colors φ ![rlz j₀, g idx1] := by
    intro hcon
    rcases (htrace' j₀ idx1).mp hcon with hc | hc
    · exact hidx01 (g.injective hc).symm
    · exact hcIdx1 j₀ (g.injective hc).symm
  have hT3 : RealizeIn G.structure colors φ ![rlz j₀, g (cIdx j₀)] :=
    (htrace' j₀ (cIdx j₀)).mpr (Or.inr rfl)
  have hT4 : ¬ RealizeIn G.structure colors φ ![rlz j₀, g (cIdx i₂)] := by
    intro hcon
    rcases (htrace' j₀ (cIdx i₂)).mp hcon with hc | hc
    · exact hcIdx0 i₂ (g.injective hc)
    · exact hi₂ne (hcIdxinj _ _ (g.injective hc))
  -- the swap lemma turns each disagreement into nearness
  have hswap : ∀ idx idx' : Fin (s + 4), idx ≠ idx' →
      ¬ (RealizeIn G.structure colors φ ![rlz j₀, g idx] ↔
        RealizeIn G.structure colors φ ![rlz j₀, g idx']) →
      WLE H (rlz j₀) (g idx) (3 ^ q) ∨ WLE H (rlz j₀) (g idx') (3 ^ q) := by
    intro idx idx' hne hdis
    by_contra hcon
    push_neg at hcon
    have hgne : g idx ≠ g idx' := fun hcc => hne (g.injective hcc)
    let st : BallSwap.Setting n k q s :=
      { G := G, H := H, colors := colors, S := S, senum := senum
        w₁ := g idx, w₂ := g idx'
        hH := hH, hsenum := hsenum
        hw₁ := hgnotS idx, hw₂ := hgnotS idx'
        hgap := hBfar _ (hgB idx) _ (hgB idx') hgne _ (le_refl _) }
    have hcolor : ltype st.H st.dec st.w₁ (RR q) (lvl q q)
        (fun _ : Fin 1 => st.w₁)
        = ltype st.H st.dec st.w₂ (RR q) (lvl q q)
          (fun _ : Fin 1 => st.w₂) :=
      (hgcol idx).trans (hgcol idx').symm
    exact hdis (BallSwap.swap_agreement st hcolor
      (Or.inr ⟨hcon.1, hcon.2⟩) φ (le_refl q))
  -- both disagreements
  have hdis1 := hswap idx0 idx1 hidx01
    (fun hiff => hT2 (hiff.mp hT1))
  have hdis2 := hswap (cIdx j₀) (cIdx i₂)
    (fun hcc => hi₂ne (hcIdxinj _ _ hcc).symm)
    (fun hiff => hT4 (hiff.mp hT3))
  -- triangle contradiction against scatteredness
  have hfinal : ∀ idx idx' : Fin (s + 4), idx ≠ idx' →
      WLE H (rlz j₀) (g idx) (3 ^ q) → WLE H (rlz j₀) (g idx') (3 ^ q) →
      False := by
    intro idx idx' hne h1 h2
    have hgne : g idx ≠ g idx' := fun hcc => hne (g.injective hcc)
    have hwalk : WLE H (g idx) (g idx') (3 ^ q + 3 ^ q) := h1.symm.trans h2
    refine hBfar _ (hgB idx) _ (hgB idx') hgne _ ?_ hwalk
    have h9 : (3 : ℕ) ^ (q + 2) = 9 * 3 ^ q := by rw [pow_add]; ring
    have := Nat.one_le_pow q 3 (by omega)
    omega
  rcases hdis1 with h1 | h1 <;> rcases hdis2 with h2 | h2
  · exact hfinal idx0 (cIdx j₀) (Ne.symm (hcIdx0 j₀)) h1 h2
  · exact hfinal idx0 (cIdx i₂) (Ne.symm (hcIdx0 i₂)) h1 h2
  · exact hfinal idx1 (cIdx j₀) (Ne.symm (hcIdx1 j₀)) h1 h2
  · exact hfinal idx1 (cIdx i₂) (Ne.symm (hcIdx1 i₂)) h1 h2

end Lax5Proofs.AdlerAdler
