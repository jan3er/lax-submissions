import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
Ramsey's theorem, in the finite unordered form used by the sparsity
pipeline: two colors (clique versus independent set), then an arbitrary
finite list of colors.  Both bounds are purely existential; nothing here
depends on the submission's graph-class encoding.
-/

namespace Lax5Proofs.Ramsey

open SimpleGraph Finset

/-- The complement of an induced subgraph equals the induced subgraph
of the complement. -/
theorem compl_induce_eq {V : Type} {s : Set V} (G : SimpleGraph V) :
    (G.induce s)ᶜ = Gᶜ.induce s := by
  ext ⟨u, hu⟩ ⟨v, hv⟩
  simp only [compl_adj, induce_adj, ne_eq, Subtype.mk.injEq]

/-- Ramsey's theorem (two colors): for any `a b : ℕ` there exists `N` such that
    every graph on at least `N` vertices either contains a clique of size `a` or
    an independent set of size `b`. (Theorem 3.7) -/
theorem ramsey (a b : ℕ) : ∃ N : ℕ,
    ∀ {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
      [DecidableRel G.Adj],
    N ≤ Fintype.card V → ¬G.CliqueFree a ∨ ¬Gᶜ.CliqueFree b := by
  classical
  suffices h : ∀ n a b, a + b = n →
      ∃ N : ℕ, ∀ {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
      N ≤ Fintype.card V → ¬G.CliqueFree a ∨ ¬Gᶜ.CliqueFree b from
    h (a + b) a b rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro a b hab
    -- Base cases: a = 0 or b = 0
    match a, b, hab with
    | 0, _, _ =>
      exact ⟨0, fun _ _ _ => Or.inl not_cliqueFree_zero⟩
    | _, 0, _ =>
      exact ⟨0, fun _ _ _ => Or.inr not_cliqueFree_zero⟩
    | a' + 1, b' + 1, hab =>
      -- IH for (a', b'+1) and (a'+1, b')
      obtain ⟨N1, hN1⟩ := ih _ (by omega) a' (b' + 1) rfl
      obtain ⟨N2, hN2⟩ := ih _ (by omega) (a' + 1) b' rfl
      refine ⟨N1 + N2 + 1,
        fun {V} [DecidableEq V] [Fintype V] G [DecidableRel G.Adj] hcard => ?_⟩
      -- Pick a vertex v
      have hne : 0 < Fintype.card V := by omega
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp hne
      -- Neighbors and non-neighbors of v
      set A := G.neighborFinset v with hA_def
      set B := Finset.univ.erase v \ A with hB_def
      -- A ⊆ univ.erase v (since v is not its own neighbor)
      have hA_sub : A ⊆ Finset.univ.erase v := by
        intro w hw
        rw [Finset.mem_erase]
        exact ⟨(G.ne_of_adj ((G.mem_neighborFinset v w).mp hw)).symm, Finset.mem_univ _⟩
      -- |A| + |B| = |V| - 1
      have hAB : A.card + B.card + 1 = Fintype.card V := by
        have h1 : B ∪ A = Finset.univ.erase v :=
          Finset.sdiff_union_of_subset hA_sub
        have h2 : Disjoint B A := Finset.sdiff_disjoint
        have h3 := Finset.card_union_of_disjoint h2
        have h4 := Finset.card_erase_of_mem (Finset.mem_univ v)
        rw [h1] at h3; rw [Finset.card_univ] at h4
        omega
      -- Pigeonhole: |A| ≥ N1 or |B| ≥ N2
      rcases Nat.lt_or_ge A.card N1 with hAlt | hAge
      · -- Case 2: |A| < N1, so |B| ≥ N2
        have hBge : N2 ≤ B.card := by omega
        have hcB : N2 ≤ Fintype.card ↑(B : Set V) := by
          rw [Fintype.card_of_finset' B (fun x => Iff.rfl)]
          exact hBge
        rcases hN2 (G.induce (↑B : Set V)) hcB with h1 | h2
        · exact Or.inl <| mt
            (SimpleGraph.CliqueFree.comap
              (G := G) (H := G.induce (↑B : Set V))
              (SimpleGraph.Embedding.induce (G := G) (↑B : Set V)).isContained)
            h1
        · have h2' : ¬(Gᶜ.induce (↑B : Set V)).CliqueFree b' := by
            simpa [compl_induce_eq G] using h2
          obtain ⟨t, ht⟩ := Classical.not_forall.mp h2'
          have ht : (Gᶜ.induce (↑B : Set V)).IsNClique b' t := not_not.mp ht
          let t' : Finset V := t.map ⟨Subtype.val, Subtype.val_injective⟩
          have ht_coe : (((⊤ : Subgraph Gᶜ).induce (↑B : Set V)).coe).IsNClique b' t := by
            simpa [SimpleGraph.induce_eq_coe_induce_top] using ht
          have ht' : Gᶜ.IsNClique b' t' := by
            simpa [t'] using
              (SimpleGraph.IsNClique.of_induce
                (G := Gᶜ) (S := (⊤ : Subgraph Gᶜ)) (F := (↑B : Set V)) ht_coe)
          have hv_adj : ∀ w ∈ t', Gᶜ.Adj v w := by
            intro w hw
            rcases Finset.mem_map.mp hw with ⟨x, hx, rfl⟩
            have hxB : x.1 ∈ Finset.univ.erase v \ A := by
              exact hB_def ▸ x.2
            have hxsdiff : x.1 ∈ Finset.univ.erase v ∧ x.1 ∉ A := by
              exact Finset.mem_sdiff.mp hxB
            have hxne : v ≠ x.1 := by
              exact (Finset.mem_erase.mp hxsdiff.1).1.symm
            have hxnotadj : ¬G.Adj v x.1 := by
              intro hvx
              exact hxsdiff.2 ((G.mem_neighborFinset v x.1).2 hvx)
            rw [SimpleGraph.compl_adj]
            exact ⟨hxne, hxnotadj⟩
          exact Or.inr (ht'.insert hv_adj).not_cliqueFree
      · -- Case 1: |A| ≥ N1 — apply IH to G.induce ↑A
        have hcA : N1 ≤ Fintype.card ↑(A : Set V) := by
          rw [Fintype.card_of_finset' A (fun x => Iff.rfl)]
          exact hAge
        rcases hN1 (G.induce (↑A : Set V)) hcA with h1 | h2
        · -- Found a'-clique in induced subgraph — extend with v
          obtain ⟨s, hs⟩ := Classical.not_forall.mp h1
          have hs : (G.induce (↑A : Set V)).IsNClique a' s := not_not.mp hs
          let s' : Finset V := s.map ⟨Subtype.val, Subtype.val_injective⟩
          have hs_coe : (((⊤ : Subgraph G).induce (↑A : Set V)).coe).IsNClique a' s := by
            simpa [SimpleGraph.induce_eq_coe_induce_top] using hs
          have hs' : G.IsNClique a' s' := by
            simpa [s'] using
              (SimpleGraph.IsNClique.of_induce
                (G := G) (S := (⊤ : Subgraph G)) (F := (↑A : Set V)) hs_coe)
          have hv_adj : ∀ w ∈ s', G.Adj v w := by
            intro w hw
            rcases Finset.mem_map.mp hw with ⟨x, hx, rfl⟩
            have hxA : x.1 ∈ G.neighborFinset v := by
              exact x.2
            simpa using (G.mem_neighborFinset v x.1).mp hxA
          exact Or.inl (hs'.insert hv_adj).not_cliqueFree
        · -- Found (b'+1)-independent set — transfer to Gᶜ
          have h2' : ¬(Gᶜ.induce (↑A : Set V)).CliqueFree (b' + 1) := by
            simpa [compl_induce_eq G] using h2
          exact Or.inr <| mt
            (SimpleGraph.CliqueFree.comap
              (G := Gᶜ) (H := Gᶜ.induce (↑A : Set V))
              (SimpleGraph.Embedding.induce (G := Gᶜ) (↑A : Set V)).isContained)
            h2'

/-- Multicolor Ramsey theorem: for any list of natural numbers
    `sizes = [n₁, …, nₖ]`, there exists `N` such that every `k`-coloring of
    edges of a complete graph on at least `N` vertices yields a monochromatic
    clique of size `nᵢ` in color `i`, for some `i`. (Theorem 3.8) -/
theorem multicolor_ramsey (sizes : List ℕ) (hk : sizes ≠ []) :
    ∃ N : ℕ, ∀ {V : Type} [DecidableEq V] [Fintype V],
      N ≤ Fintype.card V →
      ∀ (c : Sym2 V → Fin sizes.length),
        ∃ (i : Fin sizes.length) (S : Finset V),
          sizes.get i ≤ S.card ∧
          (↑S : Set V).Pairwise (fun u v => c s(u, v) = i) := by
  classical
  induction sizes with
  | nil =>
      cases hk rfl
  | cons n rest ih =>
      cases rest with
      | nil =>
          refine ⟨n, ?_⟩
          intro V _ _ hcard c
          refine ⟨⟨0, by simp⟩, Finset.univ, ?_, ?_⟩
          · simpa
          · intro u _ v _ _
            apply Fin.ext
            simp
      | cons m tail =>
          obtain ⟨Nrest, hrest⟩ := ih (by simp)
          obtain ⟨N, hN⟩ := ramsey n Nrest
          refine ⟨N, ?_⟩
          intro V _ _ hcard c
          let G : SimpleGraph V := {
            Adj := fun u v => u ≠ v ∧ c s(u, v) = 0
            symm := by
              intro u v huv
              exact ⟨huv.1.symm, by simpa [Sym2.eq_swap] using huv.2⟩
            loopless := ⟨fun v hv => hv.1 rfl⟩
          }
          letI : DecidableRel G.Adj := fun u v => by
            dsimp [G]
            infer_instance
          rcases hN G hcard with hClique | hCompl
          · let f : (⊤ : SimpleGraph (Fin n)) ↪g G :=
              SimpleGraph.topEmbeddingOfNotCliqueFree hClique
            refine ⟨0, Finset.univ.map f.toEmbedding, ?_, ?_⟩
            · simp
            · intro u hu v hv huv
              rcases Finset.mem_map.mp hu with ⟨a, _, rfl⟩
              rcases Finset.mem_map.mp hv with ⟨b, _, rfl⟩
              have hab : a ≠ b := by
                intro hab
                apply huv
                simp [hab]
              have hadj : G.Adj (f a) (f b) := by
                exact (f.map_adj_iff).2 (by simpa [SimpleGraph.top_adj] using hab)
              exact hadj.2
          · let f : (⊤ : SimpleGraph (Fin Nrest)) ↪g Gᶜ :=
              SimpleGraph.topEmbeddingOfNotCliqueFree hCompl
            let colorRest :
                Fin Nrest → Fin Nrest → Fin ((m :: tail).length) :=
              fun a b =>
                Fin.predAbove (0 : Fin ((m :: tail).length)) (c s(f a, f b))
            have hcolorRest :
                ∀ a b : Fin Nrest, colorRest a b = colorRest b a := by
              intro a b
              unfold colorRest
              rw [Sym2.eq_swap]
            let cRest : Sym2 (Fin Nrest) → Fin (List.length (m :: tail)) :=
              Sym2.lift ⟨colorRest, hcolorRest⟩
            obtain ⟨i, S, hsize, hpair⟩ := hrest (V := Fin Nrest) (by simp) cRest
            refine ⟨i.succ, S.map f.toEmbedding, ?_, ?_⟩
            · simpa using hsize
            · intro u hu v hv huv
              rcases Finset.mem_map.mp hu with ⟨a, ha, rfl⟩
              rcases Finset.mem_map.mp hv with ⟨b, hb, rfl⟩
              have hab : a ≠ b := by
                intro hab
                apply huv
                simp [hab]
              have hpair' : cRest s(a, b) = i := hpair ha hb hab
              have hadjCompl : Gᶜ.Adj (f a) (f b) := by
                exact (f.map_adj_iff).2 (by simpa [SimpleGraph.top_adj] using hab)
              rw [SimpleGraph.compl_adj] at hadjCompl
              have hcolor_ne_zero : c s(f a, f b) ≠ 0 := by
                intro hzero
                exact hadjCompl.2 ⟨hadjCompl.1, hzero⟩
              have hpred :
                  Fin.predAbove (0 : Fin ((m :: tail).length)) (c s(f a, f b)) = i := by
                simpa [cRest, colorRest] using hpair'
              calc
                c s(f a, f b) =
                    Fin.succ (Fin.predAbove (0 : Fin ((m :: tail).length)) (c s(f a, f b))) := by
                      symm
                      exact Fin.succ_predAbove_zero hcolor_ne_zero
                _ = i.succ := by rw [hpred]


end Lax5Proofs.Ramsey
