import Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.NowhereDense.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinorComposition.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.Densification.Full
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor
open Lax5Proofs.Source.Catalog.SparsityLectures.NowhereDense
open Lax5Proofs.Source.Catalog.SparsityLectures.Preliminaries
open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinorComposition
open Classical

namespace Lax5Proofs.Source.Catalog.SparsityLectures.NDSubpolynomialDensity

noncomputable section

private structure MinimumDegreeWitness {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (d : ℕ) where
  W : Type
  instDecEqW : DecidableEq W
  instFintypeW : Fintype W
  instNonemptyW : Nonempty W
  f : W ↪ V
  s : Set V
  hs : s = Set.range f
  hcard : Fintype.card W = s.toFinset.card
  hsdeg : d ≤ (SimpleGraph.comap f G).minDegree
  hsedge : G.edgeFinset.card ≤ (SimpleGraph.comap f G).edgeFinset.card +
    (d - 1) * (Fintype.card V - Fintype.card W)

attribute [instance] MinimumDegreeWitness.instDecEqW
attribute [instance] MinimumDegreeWitness.instFintypeW
attribute [instance] MinimumDegreeWitness.instNonemptyW

private def embeddingRangeEquiv {V W : Type} (f : W ↪ V) : W ≃ Set.range f :=
  { toFun := fun w => ⟨f w, ⟨w, rfl⟩⟩
    invFun := fun v => Classical.choose v.2
    left_inv := by
      intro w
      apply f.injective
      simpa using (Classical.choose_spec (p := fun u : W => f u = f w) ⟨w, rfl⟩)
    right_inv := by
      intro v
      apply Subtype.ext
      simpa using (Classical.choose_spec (p := fun u : W => f u = v.1) v.2) }

private def comapIsoInduceRange {V W : Type} (G : SimpleGraph V) (f : W ↪ V) :
    SimpleGraph.comap f G ≃g G.induce (Set.range f) :=
  { toEquiv := embeddingRangeEquiv f
    map_rel_iff' := by
      intro a b
      constructor <;> intro hab <;> simpa using hab }

private def minimumDegreeWitnessAux (n : ℕ) :
    ∀ {V : Type} [DecidableEq V] [Fintype V] [Nonempty V],
      Fintype.card V = n →
      ∀ (G : SimpleGraph V) (d : ℕ),
        d * Fintype.card V ≤ G.edgeFinset.card →
        MinimumDegreeWitness G d := by
  induction n with
  | zero =>
      intro V _ _ _ hcard G d hEdges
      exfalso
      have : 0 < Fintype.card V := Fintype.card_pos
      rw [hcard] at this
      omega
  | succ n ih =>
      intro V _ _ _ hcard G d hEdges
      letI : DecidableRel G.Adj := Classical.decRel _
      by_cases hd : d ≤ G.minDegree
      · refine
          { W := V
            instDecEqW := inferInstance
            instFintypeW := inferInstance
            instNonemptyW := inferInstance
            f := Function.Embedding.refl V
            s := Set.univ
            hs := by
              ext v
              simp
            hcard := by
              simp
            hsdeg := ?_
            hsedge := ?_ }
        · change d ≤ G.minDegree
          exact hd
        · change G.edgeFinset.card ≤ G.edgeFinset.card +
              (d - 1) * (Fintype.card V - Fintype.card V)
          simp
      · let x : V := Classical.choose G.exists_minimal_degree_vertex
        have hx : G.minDegree = G.degree x := Classical.choose_spec G.exists_minimal_degree_vertex
        have hdeglt : G.degree x < d := by
          have hminlt : G.minDegree < d := lt_of_not_ge hd
          simpa [hx] using hminlt
        cases n with
        | zero =>
            have hcard1 : Fintype.card V = 1 := hcard
            have hdpos : 0 < d := by omega
            have hedgele : G.edgeFinset.card ≤ 0 := by
              calc
                G.edgeFinset.card ≤ (Fintype.card V).choose 2 := G.card_edgeFinset_le_card_choose_two
                _ = 0 := by rw [hcard1]; decide
            have : d * 1 ≤ 0 := by simpa [hcard1] using le_trans hEdges hedgele
            omega
        | succ n' =>
            let s0 : Set V := { y : V | y ≠ x }
            have hcard_s0_raw : Fintype.card s0 = Fintype.card V - 1 := by
              simpa [s0] using (Set.card_ne_eq x)
            have hcard_s0 : Fintype.card s0 = n' + 1 := by
              rw [hcard_s0_raw, hcard]
              omega
            haveI : Nonempty s0 := Fintype.card_pos_iff.mp (by rw [hcard_s0]; exact Nat.succ_pos _)
            have hEdges_s0 : d * Fintype.card s0 ≤ (G.induce s0).edgeFinset.card := by
              have hdeg_le : G.degree x ≤ d := Nat.le_of_lt hdeglt
              have hedge : (G.induce s0).edgeFinset.card = G.edgeFinset.card - G.degree x := by
                have hs0 : s0 = ({x}ᶜ : Set V) := by
                  ext y
                  simp [s0]
                simpa [hs0] using
                  (show (G.induce ({x}ᶜ : Set V)).edgeFinset.card = G.edgeFinset.card - G.degree x by
                    rw [G.card_edgeFinset_induce_compl_singleton x, G.card_edgeFinset_deleteIncidenceSet x])
              calc
                d * Fintype.card s0 = d * (Fintype.card V - 1) := by rw [hcard_s0_raw]
                _ = d * Fintype.card V - d := by rw [Nat.mul_sub, Nat.mul_one]
                _ ≤ G.edgeFinset.card - d := Nat.sub_le_sub_right hEdges d
                _ ≤ G.edgeFinset.card - G.degree x := by omega
                _ = (G.induce s0).edgeFinset.card := hedge.symm
            let w : MinimumDegreeWitness (G.induce s0) d :=
              ih hcard_s0 (G.induce s0) d hEdges_s0
            let f0 : w.W ↪ V :=
              { toFun := fun v => (w.f v).1
                inj' := by
                  intro a b h
                  apply w.f.injective
                  exact Subtype.ext h }
            have hsdeg0 : d ≤ (SimpleGraph.comap f0 G).minDegree := by
              change d ≤ (SimpleGraph.comap w.f (G.induce s0)).minDegree
              exact w.hsdeg
            have hdeg_loss : G.degree x ≤ d - 1 := by omega
            have hedge : (G.induce s0).edgeFinset.card = G.edgeFinset.card - G.degree x := by
              have hs0 : s0 = ({x}ᶜ : Set V) := by
                ext y
                simp [s0]
              simpa [hs0] using
                (show (G.induce ({x}ᶜ : Set V)).edgeFinset.card = G.edgeFinset.card - G.degree x by
                  rw [G.card_edgeFinset_induce_compl_singleton x, G.card_edgeFinset_deleteIncidenceSet x])
            have hcard_W_le_s0 : Fintype.card w.W ≤ Fintype.card s0 := by
              exact Fintype.card_le_of_embedding w.f
            have hcard_s0_succ : Fintype.card s0 + 1 = Fintype.card V := by
              have hone_le : 1 ≤ Fintype.card V := by
                rw [hcard]
                omega
              rw [hcard_s0_raw]
              simpa using (Nat.sub_add_cancel hone_le)
            have hcard_diff :
                Fintype.card s0 - Fintype.card w.W + 1 = Fintype.card V - Fintype.card w.W := by
              calc
                Fintype.card s0 - Fintype.card w.W + 1 = Fintype.card s0 + 1 - Fintype.card w.W := by
                  simpa [Nat.add_comm] using
                    (Nat.sub_add_comm (n := Fintype.card s0) (m := 1)
                      (k := Fintype.card w.W) hcard_W_le_s0).symm
                _ = Fintype.card V - Fintype.card w.W := by rw [hcard_s0_succ]
            have hsedge0 :
                G.edgeFinset.card ≤ (SimpleGraph.comap f0 G).edgeFinset.card +
                  (d - 1) * (Fintype.card V - Fintype.card w.W) := by
              change G.edgeFinset.card ≤
                  (SimpleGraph.comap w.f (G.induce s0)).edgeFinset.card +
                    (d - 1) * (Fintype.card V - Fintype.card w.W)
              calc
                G.edgeFinset.card = (G.induce s0).edgeFinset.card + G.degree x := by
                  rw [hedge, Nat.sub_add_cancel]
                  exact G.degree_le_card_edgeFinset x
                _ ≤ (SimpleGraph.comap w.f (G.induce s0)).edgeFinset.card +
                      (d - 1) * (Fintype.card s0 - Fintype.card w.W) + (d - 1) := by
                  exact add_le_add w.hsedge hdeg_loss
                _ = (SimpleGraph.comap w.f (G.induce s0)).edgeFinset.card +
                      (d - 1) * ((Fintype.card s0 - Fintype.card w.W) + 1) := by
                  rw [Nat.mul_add, Nat.mul_one]
                  ac_rfl
                _ = (SimpleGraph.comap w.f (G.induce s0)).edgeFinset.card +
                      (d - 1) * (Fintype.card V - Fintype.card w.W) := by
                  rw [hcard_diff]
            exact
              { W := w.W
                instDecEqW := w.instDecEqW
                instFintypeW := w.instFintypeW
                instNonemptyW := w.instNonemptyW
                f := f0
                s := Set.range f0
                hs := rfl
                hcard := by
                  rw [Set.toFinset_range]
                  symm
                  simpa using Finset.card_image_of_injective Finset.univ f0.injective
                hsdeg := hsdeg0
                hsedge := hsedge0 }

private theorem exists_inducedSubgraph_minDegree_sq_card
    {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] (G : SimpleGraph V) (d : ℕ)
    (hEdges : d * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ s : Set V, d ≤ (G.induce s).minDegree ∧ Fintype.card V ≤ (Fintype.card s) ^ 2 := by
  letI : DecidableRel G.Adj := Classical.decRel _
  let P : Set V → Prop := fun s =>
    d ≤ (G.induce s).minDegree ∧ Fintype.card V ≤ (Fintype.card s) ^ 2
  change ∃ s : Set V, P s
  by_cases hd0 : d = 0
  · subst d
    refine ⟨Set.univ, by simp, ?_⟩
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    have hpow : Fintype.card V ≤ (Fintype.card V) ^ 2 := by
      calc
        Fintype.card V = 1 * Fintype.card V := by simp
        _ ≤ Fintype.card V * Fintype.card V := by
          exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hpos)
        _ = (Fintype.card V) ^ 2 := by simp [pow_two]
    rw [Fintype.card_setUniv]; exact hpow
  · let w : MinimumDegreeWitness G d :=
      minimumDegreeWitnessAux (Fintype.card V) rfl G d hEdges
    have hcard_s : Fintype.card w.W = Fintype.card w.s := by
      calc
        Fintype.card w.W = w.s.toFinset.card := w.hcard
        _ = Fintype.card w.s := by
          rw [Set.toFinset_card]
    let iso : SimpleGraph.comap w.f G ≃g G.induce w.s := by
      rw [w.hs]
      exact comapIsoInduceRange G w.f
    have hsdeg : d ≤ (G.induce w.s).minDegree := by
      exact iso.minDegree_eq ▸ w.hsdeg
    have hsedge :
        G.edgeFinset.card ≤ (G.induce w.s).edgeFinset.card +
          (d - 1) * (Fintype.card V - Fintype.card w.s) := by
      calc
        G.edgeFinset.card ≤ (SimpleGraph.comap w.f G).edgeFinset.card +
              (d - 1) * (Fintype.card V - Fintype.card w.W) := w.hsedge
        _ = (G.induce w.s).edgeFinset.card +
              (d - 1) * (Fintype.card V - Fintype.card w.s) := by
          rw [iso.card_edgeFinset_eq, hcard_s]
    have hsize : Fintype.card V ≤ (Fintype.card w.s) ^ 2 := by
      by_contra hsbad
      have hslt : (Fintype.card w.s) ^ 2 < Fintype.card V := lt_of_not_ge hsbad
      have hedge_small : (G.induce w.s).edgeFinset.card < Fintype.card V := by
        calc
          (G.induce w.s).edgeFinset.card ≤ (Fintype.card w.s).choose 2 :=
            (G.induce w.s).card_edgeFinset_le_card_choose_two
          _ ≤ (Fintype.card w.s) ^ 2 := Nat.choose_le_pow _ 2
          _ < Fintype.card V := hslt
      have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
      have hcontra : G.edgeFinset.card < d * Fintype.card V := by
        have hsucc : 1 + (d - 1) = d := by
          simpa [Nat.add_comm] using (Nat.succ_pred_eq_of_pos hdpos)
        calc
          G.edgeFinset.card ≤ (G.induce w.s).edgeFinset.card +
                (d - 1) * (Fintype.card V - Fintype.card w.s) := hsedge
          _ < Fintype.card V + (d - 1) * (Fintype.card V - Fintype.card w.s) := by
            exact Nat.add_lt_add_right hedge_small _
          _ ≤ Fintype.card V + (d - 1) * Fintype.card V := by
            exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _
          _ = d * Fintype.card V := by
            calc
              Fintype.card V + (d - 1) * Fintype.card V = (1 + (d - 1)) * Fintype.card V := by
                rw [Nat.add_mul, Nat.one_mul]
              _ = d * Fintype.card V := by rw [hsucc]
      exact (not_lt_of_ge hEdges) hcontra
    exact ⟨w.s, hsdeg, hsize⟩

private theorem isShallowMinor_zero_of_embedding {V W : Type}
    {G : SimpleGraph V} {H : SimpleGraph W} (f : H ↪g G) :
    IsShallowMinor H G 0 := by
  refine ⟨{
    branchSet := fun w => {f w}
    center := fun w => f w
    center_mem := ?_
    branchDisjoint := ?_
    branchRadius := ?_
    branchEdge := ?_ }⟩
  · intro w
    simp
  · intro u v huv
    refine Set.disjoint_left.2 ?_
    intro x hxU hxV
    simp only [Set.mem_singleton_iff] at hxU hxV
    exact huv (f.injective (hxU.symm.trans hxV))
  · intro v x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by simp, ?_⟩
    intro w hw
    simp at hw
    simp [hw]
  · intro u v huv
    exact ⟨f u, by simp, f v, by simp, f.map_rel_iff.mpr huv⟩

private theorem isShallowMinor_mono {V W : Type}
    {H : SimpleGraph W} {G : SimpleGraph V} {d d' : ℕ}
    (hMinor : IsShallowMinor H G d) (hdd' : d ≤ d') :
    IsShallowMinor H G d' := by
  rcases hMinor with ⟨m⟩
  refine ⟨{
    branchSet := m.branchSet
    center := m.center
    center_mem := m.center_mem
    branchDisjoint := m.branchDisjoint
    branchRadius := ?_
    branchEdge := m.branchEdge }⟩
  intro v x hx
  rcases m.branchRadius v x hx with ⟨p, hpPath, hpLen, hpSupp⟩
  exact ⟨p, hpPath, le_trans hpLen hdd', hpSupp⟩

private theorem induced_isShallowMinor_zero {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (s : Set V) :
    IsShallowMinor (G.induce s) G 0 := by
  simpa using
    (isShallowMinor_zero_of_embedding
      (SimpleGraph.Embedding.comap (Function.Embedding.subtype s) G))

private def completeGraphEmbeddingOfLE {m n : ℕ} (hmn : m ≤ n) :
    SimpleGraph.completeGraph (Fin m) ↪g SimpleGraph.completeGraph (Fin n) :=
  SimpleGraph.Embedding.completeGraph (Fin.castLEEmb hmn)

private theorem clique_minor_of_large_card
    {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {t q : ℕ}
    (htCard : Nat.ceil (Real.exp t) ≤ Fintype.card V)
    (hqLog : Real.log ↑(Fintype.card V) ≤ q)
    (hMinor : IsShallowMinor (SimpleGraph.completeGraph (Fin (q + 1))) G 1) :
    IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) G 1 := by
  have hExpLe : Real.exp t ≤ Fintype.card V := by
    calc
      Real.exp t ≤ Nat.ceil (Real.exp t) := by exact_mod_cast Nat.le_ceil (Real.exp t)
      _ ≤ Fintype.card V := by exact_mod_cast htCard
  have htLog : (t : ℝ) ≤ Real.log ↑(Fintype.card V) := by
    have hCardPos : 0 < (Fintype.card V : ℝ) := lt_of_lt_of_le (Real.exp_pos t) hExpLe
    simpa using Real.log_le_log (Real.exp_pos t) hExpLe
  have htq_real : (t : ℝ) ≤ q := le_trans htLog hqLog
  have htq : t ≤ q := by exact_mod_cast htq_real
  exact shallowMinor_trans
    (isShallowMinor_zero_of_embedding
      (completeGraphEmbeddingOfLE (Nat.succ_le_succ htq)))
    hMinor

private theorem not_boostedMinor_of_large_parameter
    {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] {ε : ℝ}
    (hWpos : 0 < (Fintype.card W : ℝ)) (hε58 : (5 : ℝ) / 8 ≤ ε)
    (hEdges : (Fintype.card W : ℝ) ^ (1 + ε + ε ^ (2 : ℕ)) ≤ (H.edgeFinset.card : ℝ)) :
    False := by
  let m : ℝ := Fintype.card W
  have hm_pos : 0 < m := hWpos
  have hm_one_le : 1 ≤ m := by
    have hcard_pos : 0 < Fintype.card W := by
      exact_mod_cast hWpos
    change (1 : ℝ) ≤ (Fintype.card W : ℝ)
    exact_mod_cast (Nat.succ_le_of_lt hcard_pos)
  have hcardUpper : (H.edgeFinset.card : ℝ) ≤ m ^ (2 : ℕ) := by
    calc
      (H.edgeFinset.card : ℝ) ≤ ((Fintype.card W).choose 2 : ℝ) := by
        exact_mod_cast H.card_edgeFinset_le_card_choose_two
      _ ≤ ((Fintype.card W) ^ 2 : ℕ) := by exact_mod_cast Nat.choose_le_pow _ 2
      _ = m ^ (2 : ℕ) := by simp [m]
  have hExpLarge : (2 : ℝ) < 1 + ε + ε ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (ε - (3 : ℝ) / 8)]
  have hLower : m ^ (2 : ℝ) < m ^ (1 + ε + ε ^ (2 : ℕ)) := by
    have hm_one_lt : 1 < m := by
      by_contra hmNotLt
      have hm_le_one : m ≤ 1 := le_of_not_gt hmNotLt
      have hcard_pos : 0 < Fintype.card W := by
        have hm_pos' : 0 < (Fintype.card W : ℝ) := by simpa [m] using hm_pos
        exact_mod_cast hm_pos'
      have hcard_le_one : Fintype.card W ≤ 1 := by
        change (Fintype.card W : ℝ) ≤ 1 at hm_le_one
        exact_mod_cast hm_le_one
      have hcard : Fintype.card W = 1 := by omega
      have hEdgesZero : (H.edgeFinset.card : ℝ) = 0 := by
        have hle0 : (H.edgeFinset.card : ℝ) ≤ 0 := by
          calc
            (H.edgeFinset.card : ℝ) ≤ ((Fintype.card W).choose 2 : ℝ) := by
              exact_mod_cast H.card_edgeFinset_le_card_choose_two
            _ = 0 := by rw [hcard]; norm_num
        linarith
      have : ¬ ((1 : ℝ) ^ (1 + ε + ε ^ (2 : ℕ)) ≤ (H.edgeFinset.card : ℝ)) := by
        simp [hEdgesZero]
      have hEdgesOne : (1 : ℝ) ^ (1 + ε + ε ^ (2 : ℕ)) ≤ (H.edgeFinset.card : ℝ) := by
        simpa [m, hcard] using hEdges
      exact this hEdgesOne
    have := Real.rpow_lt_rpow_of_exponent_lt hm_one_lt hExpLarge
    simpa [Real.rpow_natCast] using this
  have hcardUpper' : (H.edgeFinset.card : ℝ) ≤ m ^ (2 : ℝ) := by
    simpa [Real.rpow_natCast] using hcardUpper
  exact (not_lt_of_ge hcardUpper') (hLower.trans_le hEdges)

private theorem card_le_pow_three_of_boost
    {V W : Type} [Fintype V] [Fintype W] {ε : ℝ}
    (hVpos : 0 < (Fintype.card V : ℝ)) (hε : ε ≤ (2 : ℝ) / 3)
    (hWlo : (Fintype.card V : ℝ) ^ (1 - ε) ≤ (Fintype.card W : ℝ)) :
    (Fintype.card V : ℝ) ≤ (Fintype.card W : ℝ) ^ (3 : ℕ) := by
  let n : ℝ := Fintype.card V
  let m : ℝ := Fintype.card W
  have hExp : (1 : ℝ) / 3 ≤ 1 - ε := by linarith
  have hcalc : n ^ ((1 : ℝ) / 3) ≤ m := by
    calc
      n ^ ((1 : ℝ) / 3) ≤ n ^ (1 - ε) := by
        have hn_one : 1 ≤ n := by
          change (1 : ℝ) ≤ (Fintype.card V : ℝ)
          exact_mod_cast (Nat.succ_le_of_lt (show 0 < Fintype.card V by exact_mod_cast hVpos))
        exact Real.rpow_le_rpow_of_exponent_le hn_one hExp
      _ ≤ m := hWlo
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ n ^ ((1 : ℝ) / 3)) hcalc
    (by positivity : (0 : ℝ) ≤ (3 : ℝ))
  have hn_eq : (n ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) = n := by
    calc
      (n ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) = n ^ (((1 : ℝ) / 3) * 3) := by
        rw [Real.rpow_mul (by positivity : 0 ≤ n)]
      _ = n ^ (1 : ℕ) := by simp
      _ = n := by simp
  calc
    n = (n ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) := hn_eq.symm
    _ ≤ m ^ (3 : ℝ) := hpow
    _ = m ^ (3 : ℕ) := by simp

private theorem le_floor_double {x : ℝ} (hx : 1 ≤ x) :
    x ≤ Nat.floor (2 * x) := by
  have hlt : 2 * x < Nat.floor (2 * x) + 1 := Nat.lt_floor_add_one (2 * x)
  have hx2 : x ≤ 2 * x - 1 := by linarith
  have hle : 2 * x - 1 < Nat.floor (2 * x) := by linarith
  linarith

private theorem rpow_le_floor_rpow_add
    {n a δ : ℝ} (hn : 0 < n) (hn1 : 1 ≤ n) (ha : 0 ≤ a) (hgap : 2 ≤ n ^ δ) :
    n ^ a ≤ Nat.floor (n ^ (a + δ)) := by
  have hxa : 1 ≤ n ^ a := Real.one_le_rpow hn1 ha
  have hdouble : 2 * n ^ a ≤ n ^ (a + δ) := by
    calc
      2 * n ^ a ≤ n ^ δ * n ^ a := by gcongr
      _ = n ^ (a + δ) := by
        rw [mul_comm, ← Real.rpow_add hn]
  have hfloorMono : (Nat.floor (2 * n ^ a) : ℝ) ≤ Nat.floor (n ^ (a + δ)) := by
    exact_mod_cast Nat.floor_mono hdouble
  exact le_trans (le_floor_double hxa) hfloorMono

private theorem le_of_sq_le_sq {m n : ℕ} (h : m ^ 2 ≤ n ^ 2) :
    m ≤ n := by
  exact (Nat.pow_le_pow_iff_left (show (2 : ℕ) ≠ 0 by decide)).1 h

private theorem le_of_pow_six_le_pow_six {m n : ℕ} (h : m ^ 6 ≤ n ^ 6) :
    m ≤ n := by
  exact (Nat.pow_le_pow_iff_left (show (6 : ℕ) ≠ 0 by decide)).1 h

private def iterationDepth : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 * iterationDepth k + 1

private theorem iterationDepth_monotone : Monotone iterationDepth := by
  intro i j hij
  induction hij with
  | refl =>
      rfl
  | @step j hij ih =>
      have hsucc : iterationDepth j ≤ iterationDepth (j + 1) := by
        simp [iterationDepth]
        omega
      exact le_trans ih hsucc

private def sizeSeq (B : ℕ) : ℕ → ℕ
  | 0 => B
  | j + 1 => (sizeSeq B j) ^ 6

private theorem sizeSeq_base_le {B : ℕ} (hB : 1 ≤ B) :
    ∀ j : ℕ, B ≤ sizeSeq B j := by
  intro j
  induction j with
  | zero =>
      simp [sizeSeq]
  | succ j ih =>
      simp [sizeSeq]
      calc
        B ≤ sizeSeq B j := ih
        _ ≤ (sizeSeq B j) ^ 6 := by
          have hpos : 0 < sizeSeq B j := lt_of_lt_of_le (by decide : 0 < 1) (le_trans hB ih)
          simpa using
            (Nat.pow_le_pow_right hpos (show 1 ≤ 6 by decide) :
              (sizeSeq B j) ^ 1 ≤ (sizeSeq B j) ^ 6)

private theorem step_or_clique
    {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (M : ℕ)
    {a δ : ℝ} (ha0 : 0 < a) (ha23 : a ≤ (2 : ℝ) / 3)
    (_hδ : 0 < δ) (hδa : 2 * δ ≤ a ^ (2 : ℕ))
    (hDensify :
      ∀ {W : Type} [DecidableEq W] [Fintype W]
        (H : SimpleGraph W) [DecidableRel H.Adj],
        M ≤ Fintype.card W →
        (∀ v : W, (Fintype.card W : ℝ) ^ a ≤ ↑(H.degree v)) →
        (∃ t : ℕ, Real.log ↑(Fintype.card W) ≤ ↑t ∧
          IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) H 1) ∨
        (∃ (U : Type) (_ : DecidableEq U) (_ : Fintype U)
          (H' : SimpleGraph U) (_ : DecidableRel H'.Adj),
          IsShallowMinor H' H 1 ∧
          (Fintype.card W : ℝ) ^ (1 - a) ≤ ↑(Fintype.card U) ∧
          (Fintype.card U : ℝ) ^ (1 + a + a ^ 2) ≤ ↑(H'.edgeFinset.card)))
    {t0 : ℕ}
    (hMBound : M ^ 2 ≤ Fintype.card V)
    (hCliqueBound : (Nat.ceil (Real.exp t0)) ^ 2 ≤ Fintype.card V)
    (hRound : 2 ≤ (Fintype.card V : ℝ) ^ δ)
    (hDense : (Fintype.card V : ℝ) ^ (1 + a + δ) ≤ (G.edgeFinset.card : ℝ)) :
    IsShallowMinor (SimpleGraph.completeGraph (Fin (t0 + 1))) G 1 ∨
      ((a < (5 : ℝ) / 8) ∧
        ∃ (W : Type) (_ : DecidableEq W) (_ : Fintype W)
          (H : SimpleGraph W) (_ : DecidableRel H.Adj),
          IsShallowMinor H G 1 ∧
          ((Fintype.card V : ℝ) ≤ (Fintype.card W : ℝ) ^ (6 : ℕ)) ∧
          ((Fintype.card W : ℝ) ^ (1 + a + 2 * δ) ≤ (H.edgeFinset.card : ℝ))) := by
  letI : DecidableRel G.Adj := Classical.decRel _
  let n : ℝ := Fintype.card V
  let d : ℕ := Nat.floor (n ^ (a + δ))
  have hn_pos : 0 < n := by
    change (0 : ℝ) < (Fintype.card V : ℝ)
    exact_mod_cast Fintype.card_pos
  have hn_one : 1 ≤ n := by
    change (1 : ℝ) ≤ (Fintype.card V : ℝ)
    exact_mod_cast (Nat.succ_le_of_lt Fintype.card_pos)
  have hdEdgesNat : d * Fintype.card V ≤ G.edgeFinset.card := by
    have hdEdges : (d : ℝ) * n ≤ (G.edgeFinset.card : ℝ) := by
      calc
        (d : ℝ) * n ≤ (n ^ (a + δ)) * n := by
          gcongr
          exact Nat.floor_le (by positivity : 0 ≤ n ^ (a + δ))
        _ = n ^ (1 + a + δ) := by
          calc
            (n ^ (a + δ)) * n = (n ^ (a + δ)) * (n ^ (1 : ℝ)) := by rw [Real.rpow_one]
            _ = n ^ ((a + δ) + 1) := by rw [← Real.rpow_add hn_pos]
            _ = n ^ (1 + a + δ) := by congr 1; ring
        _ ≤ (G.edgeFinset.card : ℝ) := hDense
    have hdEdges' : (d * Fintype.card V : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
      simpa [n] using hdEdges
    exact_mod_cast hdEdges'
  rcases exists_inducedSubgraph_minDegree_sq_card G d hdEdgesNat with ⟨s, hsdeg, hsize⟩
  let S : SimpleGraph s := G.induce s
  have hsCardLe : Fintype.card s ≤ Fintype.card V := by
    exact Fintype.card_le_of_embedding (Function.Embedding.subtype s)
  have hsdegReal : (Fintype.card s : ℝ) ^ a ≤ (S.minDegree : ℝ) := by
    calc
      (Fintype.card s : ℝ) ^ a ≤ n ^ a := by
        exact Real.rpow_le_rpow (by positivity : 0 ≤ (Fintype.card s : ℝ))
          (by
            change (Fintype.card s : ℝ) ≤ (Fintype.card V : ℝ)
            exact_mod_cast hsCardLe) ha0.le
      _ ≤ d := rpow_le_floor_rpow_add hn_pos hn_one ha0.le hRound
      _ ≤ (S.minDegree : ℝ) := by
        change (d : ℝ) ≤ ↑((G.induce s).minDegree)
        exact_mod_cast hsdeg
  have hMcard : M ≤ Fintype.card s := by
    apply le_of_sq_le_sq
    calc
      M ^ 2 ≤ Fintype.card V := hMBound
      _ ≤ (Fintype.card s) ^ 2 := hsize
  have hCliqueCard : Nat.ceil (Real.exp t0) ≤ Fintype.card s := by
    apply le_of_sq_le_sq
    exact le_trans hCliqueBound hsize
  have hStep := hDensify S hMcard (by
    intro v
    have hminle : (S.minDegree : ℝ) ≤ (S.degree v : ℝ) := by
      exact_mod_cast S.minDegree_le_degree v
    exact hsdegReal.trans hminle)
  rcases hStep with ⟨q, hqLog, hqMinor⟩ | ⟨W, hWDec, hWFint, H, hHDec, hMinor, hWlo, hHedges⟩
  · exact Or.inl <|
      shallowMinor_trans
        (clique_minor_of_large_card hCliqueCard hqLog hqMinor)
        (induced_isShallowMinor_zero G s)
  · have hs_pos : 0 < (Fintype.card s : ℝ) := by
      have hs_nat_pos : 0 < Fintype.card s := by
        have hceil_pos : 0 < Nat.ceil (Real.exp t0) := by
          exact Nat.ceil_pos.mpr (Real.exp_pos t0)
        exact lt_of_lt_of_le hceil_pos hCliqueCard
      exact_mod_cast hs_nat_pos
    by_cases hLarge : (5 : ℝ) / 8 ≤ a
    · exfalso
      exact not_boostedMinor_of_large_parameter H (show 0 < (Fintype.card W : ℝ) by
        have hWlo_pos : 0 < (Fintype.card s : ℝ) ^ (1 - a) := Real.rpow_pos_of_pos hs_pos _
        linarith) hLarge hHedges
    · have hSmall : a < (5 : ℝ) / 8 := by linarith
      refine Or.inr ⟨hSmall, W, hWDec, hWFint, H, hHDec, ?_, ?_, ?_⟩
      · exact shallowMinor_trans hMinor (induced_isShallowMinor_zero G s)
      · have hs_le : (Fintype.card s : ℝ) ≤ (Fintype.card W : ℝ) ^ (3 : ℕ) :=
            card_le_pow_three_of_boost (V := s) (W := W) hs_pos ha23 hWlo
        calc
          (Fintype.card V : ℝ) ≤ (Fintype.card s : ℝ) ^ (2 : ℕ) := by exact_mod_cast hsize
          _ ≤ ((Fintype.card W : ℝ) ^ (3 : ℕ)) ^ (2 : ℕ) := by gcongr
          _ = (Fintype.card W : ℝ) ^ (6 : ℕ) := by rw [← pow_mul]
      · have hWone : 1 ≤ (Fintype.card W : ℝ) := by
          have hWlo_pos : 0 < (Fintype.card s : ℝ) ^ (1 - a) := Real.rpow_pos_of_pos hs_pos _
          have hWpos : 0 < (Fintype.card W : ℝ) := lt_of_lt_of_le hWlo_pos hWlo
          have hWnatpos : 0 < Fintype.card W := by
            exact_mod_cast hWpos
          exact_mod_cast (Nat.succ_le_of_lt hWnatpos)
        have hExpLe : 1 + a + 2 * δ ≤ 1 + a + a ^ (2 : ℕ) := by linarith
        exact le_trans (Real.rpow_le_rpow_of_exponent_le hWone hExpLe) hHedges

set_option maxHeartbeats 1000000 in
private theorem nd_subpolynomial_density_depthZero (C : GraphClass) (hC : IsNowhereDense C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ {V : Type} [DecidableEq V] [Fintype V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      C G →
      N ≤ Fintype.card V →
      (G.edgeFinset.card : ℝ) < (Fintype.card V : ℝ) ^ (1 + ε) := by
  by_cases hε1 : 1 ≤ ε
  · refine ⟨2, ?_⟩
    intro V _ _ G _ hG hN
    let n : ℝ := Fintype.card V
    have hcard_two : 2 ≤ Fintype.card V := hN
    have hcard_pos : 0 < Fintype.card V := by omega
    have hn_pos : 0 < n := by
      change (0 : ℝ) < (Fintype.card V : ℝ)
      exact_mod_cast hcard_pos
    have hn_one : 1 ≤ n := by
      change (1 : ℝ) ≤ (Fintype.card V : ℝ)
      exact_mod_cast (Nat.succ_le_of_lt hcard_pos)
    have hEdgesQuad : (G.edgeFinset.card : ℝ) < n ^ (2 : ℝ) := by
      have hchoose : (Fintype.card V).choose 2 < (Fintype.card V) ^ 2 := by
        rw [Nat.choose_two_right]
        have hdiv :
            Fintype.card V * (Fintype.card V - 1) / 2 < Fintype.card V * (Fintype.card V - 1) := by
          have hsub_pos : 0 < Fintype.card V - 1 := by
            omega
          apply Nat.div_lt_self
          · exact Nat.mul_pos hcard_pos hsub_pos
          · decide
        have hmul :
            Fintype.card V * (Fintype.card V - 1) < (Fintype.card V) ^ 2 := by
          rw [pow_two]
          exact Nat.mul_lt_mul_of_pos_left (by omega) hcard_pos
        exact lt_trans hdiv hmul
      calc
        (G.edgeFinset.card : ℝ) ≤ ((Fintype.card V).choose 2 : ℝ) := by
          exact_mod_cast G.card_edgeFinset_le_card_choose_two
        _ < ((Fintype.card V) ^ 2 : ℕ) := by
          exact_mod_cast hchoose
        _ = n ^ (2 : ℝ) := by simp [n]
    have hPow : n ^ (2 : ℝ) ≤ n ^ (1 + ε) := by
      have hExp : (2 : ℝ) ≤ 1 + ε := by linarith
      exact Real.rpow_le_rpow_of_exponent_le hn_one hExp
    exact lt_of_lt_of_le hEdgesQuad hPow
  · have hε_lt_one : ε < 1 := lt_of_not_ge hε1
    let a0 : ℝ := ε / 2
    let δ : ℝ := ε ^ (2 : ℕ) / 32
    have ha0_pos : 0 < a0 := by
      positivity
    have ha0_lt_23 : a0 < (2 : ℝ) / 3 := by
      dsimp [a0]
      nlinarith
    have hδ_pos : 0 < δ := by
      positivity
    have hδa0 : 2 * δ ≤ a0 ^ (2 : ℕ) := by
      dsimp [a0, δ]
      ring_nf
      nlinarith [sq_nonneg ε]
    have ha0δ_le_ε : a0 + δ ≤ ε := by
      dsimp [a0, δ]
      nlinarith
    have ha0_lt_58 : a0 < (5 : ℝ) / 8 := by
      dsimp [a0]
      nlinarith
    have hδ_lt : δ < (1 : ℝ) / 24 := by
      dsimp [δ]
      nlinarith
    have hkExists : ∃ k : ℕ, (5 : ℝ) / 8 ≤ a0 + k * δ := by
      obtain ⟨k, hk⟩ := exists_nat_ge (((5 : ℝ) / 8 - a0) / δ)
      refine ⟨k, ?_⟩
      have hk' : (((5 : ℝ) / 8 - a0) / δ) ≤ (k : ℝ) := by
        exact_mod_cast hk
      have hk'' : (5 : ℝ) / 8 - a0 ≤ (k : ℝ) * δ := (div_le_iff₀ hδ_pos).1 hk'
      linarith
    let k : ℕ := Nat.find hkExists
    have hk_lower : (5 : ℝ) / 8 ≤ a0 + k * δ := Nat.find_spec hkExists
    have hk_pos : 0 < k := by
      refine Nat.pos_iff_ne_zero.mpr ?_
      intro hk0
      have : (5 : ℝ) / 8 ≤ a0 := by
        simpa [k, hk0] using hk_lower
      exact (not_le_of_gt ha0_lt_58) this
    have hk_eq : (k - 1) + 1 = k := by
      omega
    have hk_pred_cast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      have hk_cast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
        exact_mod_cast hk_eq
      linarith
    let a : ℕ → ℝ := fun m => a0 + ((k - m : ℕ) : ℝ) * δ
    have ha_final_large : (5 : ℝ) / 8 ≤ a 0 := by
      simpa [a] using hk_lower
    have ha_final_lt : a 0 < (2 : ℝ) / 3 := by
      have hnot : ¬ ((5 : ℝ) / 8 ≤ a0 + ((k - 1 : ℕ) : ℝ) * δ) := by
        simpa [k] using (Nat.find_min hkExists (Nat.pred_lt (Nat.ne_of_gt hk_pos)))
      have hnot' : ¬ ((5 : ℝ) / 8 ≤ a0 + ((k : ℝ) - 1) * δ) := by
        simpa [hk_pred_cast] using hnot
      have hprev : a0 + ((k : ℝ) - 1) * δ < (5 : ℝ) / 8 := by
        linarith
      have hshift : a 0 = a0 + ((k : ℝ) - 1) * δ + δ := by
        calc
          a 0 = a0 + (k : ℝ) * δ := by simp [a]
          _ = a0 + (((k : ℝ) - 1) + 1) * δ := by ring
          _ = a0 + ((k : ℝ) - 1) * δ + δ := by ring
      linarith
    have ha_ge_a0 : ∀ m : ℕ, a0 ≤ a m := by
      intro m
      dsimp [a]
      have hnonneg : 0 ≤ (((k - m : ℕ) : ℝ) * δ) := by positivity
      linarith
    have ha_pos : ∀ m : ℕ, 0 < a m := by
      intro m
      exact lt_of_lt_of_le ha0_pos (ha_ge_a0 m)
    have ha_le_final : ∀ {m : ℕ}, m ≤ k → a m ≤ a 0 := by
      intro m hm
      calc
        a m = a0 + (((k - m : ℕ) : ℝ) * δ) := by simp [a]
        _ ≤ a0 + (k : ℝ) * δ := by
          gcongr
          exact_mod_cast (Nat.sub_le _ _)
        _ = a 0 := by simp [a]
    have ha_lt_23 : ∀ {m : ℕ}, m ≤ k → a m < (2 : ℝ) / 3 := by
      intro m hm
      exact lt_of_le_of_lt (ha_le_final hm) ha_final_lt
    have hδa : ∀ {m : ℕ}, m ≤ k → 2 * δ ≤ (a m) ^ (2 : ℕ) := by
      intro m hm
      have hsq : a0 ^ (2 : ℕ) ≤ (a m) ^ (2 : ℕ) := by
        nlinarith [ha_ge_a0 m, ha0_pos, ha_pos m]
      exact le_trans hδa0 hsq
    have ha_step : ∀ {m : ℕ}, m + 1 ≤ k → a m = a (m + 1) + δ := by
      intro m hm
      have hnat : k - m = (k - (m + 1)) + 1 := by
        omega
      have hnat_cast : ((k - m : ℕ) : ℝ) = ((k - (m + 1) : ℕ) : ℝ) + 1 := by
        exact_mod_cast hnat
      calc
        a m = a0 + ((k - m : ℕ) : ℝ) * δ := by simp [a]
        _ = a0 + ((((k - (m + 1) : ℕ) : ℝ) + 1) * δ) := by rw [hnat_cast]
        _ = a (m + 1) + δ := by
          simp [a]
          ring
    let MSeq : ℕ → ℕ := fun m =>
      if hm : m ≤ k then
        Classical.choose (Densification.densification (a m) (ha_pos m) (ha_lt_23 hm).le)
      else
        1
    have hDensifySeq :
        ∀ {m : ℕ}, m ≤ k →
          ∀ {W : Type} [DecidableEq W] [Fintype W]
            (H : SimpleGraph W) [DecidableRel H.Adj],
            MSeq m ≤ Fintype.card W →
            (∀ v : W, (Fintype.card W : ℝ) ^ a m ≤ ↑(H.degree v)) →
            (∃ t : ℕ, Real.log ↑(Fintype.card W) ≤ ↑t ∧
              IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) H 1) ∨
            (∃ (U : Type) (_ : DecidableEq U) (_ : Fintype U)
              (H' : SimpleGraph U) (_ : DecidableRel H'.Adj),
              IsShallowMinor H' H 1 ∧
              (Fintype.card W : ℝ) ^ (1 - a m) ≤ ↑(Fintype.card U) ∧
              (Fintype.card U : ℝ) ^ (1 + a m + a m ^ 2) ≤ ↑(H'.edgeFinset.card)) := by
      intro m hm W _ _ H _ hM hdeg
      have hM' :
          Classical.choose (Densification.densification (a m) (ha_pos m) (ha_lt_23 hm).le) ≤
            Fintype.card W := by
        simpa [MSeq, hm] using hM
      exact (Classical.choose_spec
        (Densification.densification (a m) (ha_pos m) (ha_lt_23 hm).le)) H hM' hdeg
    obtain ⟨t, htClique⟩ := hC (iterationDepth (k + 1))
    obtain ⟨Bround, hBround_spec⟩ : ∃ Bround : ℕ, (2 : ℝ) ^ (1 / δ) ≤ Bround := by
      exact exists_nat_ge ((2 : ℝ) ^ (1 / δ))
    let Bcore : ℕ :=
      (Finset.range (k + 1)).sup fun m => (MSeq m) ^ 2
    let B : ℕ :=
      max (max (((Nat.ceil (Real.exp t)) ^ 2)) Bround) Bcore
    let N : ℕ := sizeSeq B k
    have hB_M : ∀ {m : ℕ}, m ≤ k → (MSeq m) ^ 2 ≤ B := by
      intro m hm
      have hm_mem : m ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hm)
      have hsup : (MSeq m) ^ 2 ≤ Bcore := by
        simpa [Bcore] using
          (Finset.le_sup (s := Finset.range (k + 1)) (f := fun j => (MSeq j) ^ 2) hm_mem)
      exact le_trans hsup (le_max_right _ _)
    have hB_clique : (Nat.ceil (Real.exp t)) ^ 2 ≤ B := by
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    have hB_round : Bround ≤ B := by
      exact le_trans (le_max_right _ _) (le_max_left _ _)
    have hB_one : 1 ≤ B := by
      have hposClique : 0 < (Nat.ceil (Real.exp t)) ^ 2 := by
        have hceil_pos : 0 < Nat.ceil (Real.exp t) := Nat.ceil_pos.mpr (Real.exp_pos _)
        exact pow_pos hceil_pos 2
      exact le_trans (Nat.succ_le_of_lt hposClique) hB_clique
    have hSizeBase : ∀ m : ℕ, B ≤ sizeSeq B m := sizeSeq_base_le hB_one
    have hBround_pow : 2 ≤ (Bround : ℝ) ^ δ := by
      have hround_real : (2 : ℝ) ^ (1 / δ) ≤ (Bround : ℝ) := by
        exact_mod_cast hBround_spec
      have htwo : ((2 : ℝ) ^ (1 / δ)) ^ δ = 2 := by
        simpa [one_div] using
          (Real.rpow_inv_rpow (x := (2 : ℝ)) (y := δ) (by positivity) (ne_of_gt hδ_pos))
      calc
        2 = ((2 : ℝ) ^ (1 / δ)) ^ δ := htwo.symm
        _ ≤ (Bround : ℝ) ^ δ := by
          exact Real.rpow_le_rpow
            (by positivity : 0 ≤ (2 : ℝ) ^ (1 / δ)) hround_real hδ_pos.le
    refine ⟨N, ?_⟩
    intro V _ _ G _ hG hN
    let n : ℝ := Fintype.card V
    have hN_one : 1 ≤ N := by
      exact le_trans hB_one (by simpa [N] using hSizeBase k)
    have hcard_pos : 0 < Fintype.card V := lt_of_lt_of_le (by decide : 0 < 1) (le_trans hN_one hN)
    have hn_pos : 0 < n := by
      change (0 : ℝ) < (Fintype.card V : ℝ)
      exact_mod_cast hcard_pos
    have hn_one : 1 ≤ n := by
      change (1 : ℝ) ≤ (Fintype.card V : ℝ)
      exact_mod_cast (Nat.succ_le_of_lt hcard_pos)
    have hCliqueImpossible :
        ∀ m : ℕ, m ≤ k →
          ∀ {W : Type} [DecidableEq W] [Fintype W] (H : SimpleGraph W),
            IsShallowMinor H G (iterationDepth (k - m)) →
            IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) H 1 →
            False := by
      intro m hm W _ _ H hMinor hClique
      have hComp0 :
          IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) G
            (2 * iterationDepth (k - m) * 1 + iterationDepth (k - m) + 1) :=
        shallowMinor_trans hClique hMinor
      have hDepthEq :
          2 * iterationDepth (k - m) * 1 + iterationDepth (k - m) + 1 =
            iterationDepth ((k - m) + 1) := by
        simp [iterationDepth, two_mul]
        omega
      have hComp :
          IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) G
            (iterationDepth ((k - m) + 1)) := hDepthEq ▸ hComp0
      have hComp' :
          IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) G
            (iterationDepth (k + 1)) := by
        apply isShallowMinor_mono hComp
        exact iterationDepth_monotone (by omega)
      exact htClique G hG hComp'
    set_option maxHeartbeats 1000000 in
    have hIter :
        ∀ m : ℕ, m ≤ k →
          ∀ {W : Type} [DecidableEq W] [Fintype W] (H : SimpleGraph W),
            IsShallowMinor H G (iterationDepth (k - m)) →
            sizeSeq B m ≤ Fintype.card W →
            ((Fintype.card W : ℝ) ^ (1 + a m + δ) ≤ (H.edgeFinset.card : ℝ)) →
            False := by
      intro m
      induction m with
      | zero =>
          intro hm W _ _ H hMinor hCard hEdge
          have hCardBase : B ≤ Fintype.card W := by
            simpa [sizeSeq] using hCard
          have hcard_pos_nat : 0 < Fintype.card W := lt_of_lt_of_le (by decide : 0 < 1)
            (le_trans hB_one hCardBase)
          letI : Nonempty W := Fintype.card_pos_iff.mp hcard_pos_nat
          have hRound : 2 ≤ (Fintype.card W : ℝ) ^ δ := by
            have hBround_card : Bround ≤ Fintype.card W := le_trans hB_round hCardBase
            calc
              2 ≤ (Bround : ℝ) ^ δ := hBround_pow
              _ ≤ (Fintype.card W : ℝ) ^ δ := by gcongr
          have hDensifyNow :
              ∀ {U : Type} [DecidableEq U] [Fintype U]
                (H' : SimpleGraph U) [DecidableRel H'.Adj],
                MSeq 0 ≤ Fintype.card U →
                (∀ v : U, (Fintype.card U : ℝ) ^ a 0 ≤ ↑(H'.degree v)) →
                (∃ t : ℕ, Real.log ↑(Fintype.card U) ≤ ↑t ∧
                  IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) H' 1) ∨
                (∃ (U' : Type) (_ : DecidableEq U') (_ : Fintype U')
                  (H'' : SimpleGraph U') (_ : DecidableRel H''.Adj),
                  IsShallowMinor H'' H' 1 ∧
                  (Fintype.card U : ℝ) ^ (1 - a 0) ≤ ↑(Fintype.card U') ∧
                  (Fintype.card U' : ℝ) ^ (1 + a 0 + a 0 ^ 2) ≤ ↑(H''.edgeFinset.card)) := by
            intro U _ _ H' _ hM hdeg
            exact hDensifySeq (m := 0) hm H' hM hdeg
          have hStep := step_or_clique H (MSeq 0)
            (ha_pos 0) (ha_lt_23 hm).le hδ_pos (hδa hm)
            (le_trans (hB_M hm) hCardBase) (le_trans hB_clique hCardBase) hRound hEdge
            (hDensify := hDensifyNow)
          rcases hStep with hClique | hBoost
          · exact hCliqueImpossible 0 hm H hMinor hClique
          · rcases hBoost with ⟨hSmall, W', hWDec, hWFint, H', hHDec, hMinorStep, hCardStep, hEdgeStep⟩
            exact (not_lt_of_ge ha_final_large) (by simpa [a] using hSmall)
      | succ m ih =>
          intro hm W _ _ H hMinor hCard hEdge
          have hm' : m ≤ k := Nat.le_of_succ_le hm
          have hCardBase : B ≤ Fintype.card W := by
            exact le_trans (hSizeBase (m + 1)) hCard
          have hcard_pos_nat : 0 < Fintype.card W := lt_of_lt_of_le (by decide : 0 < 1)
            (le_trans hB_one hCardBase)
          letI : Nonempty W := Fintype.card_pos_iff.mp hcard_pos_nat
          have hRound : 2 ≤ (Fintype.card W : ℝ) ^ δ := by
            have hBround_card : Bround ≤ Fintype.card W := le_trans hB_round hCardBase
            calc
              2 ≤ (Bround : ℝ) ^ δ := hBround_pow
              _ ≤ (Fintype.card W : ℝ) ^ δ := by gcongr
          have hDensifyNow :
              ∀ {U : Type} [DecidableEq U] [Fintype U]
                (H' : SimpleGraph U) [DecidableRel H'.Adj],
                MSeq (m + 1) ≤ Fintype.card U →
                (∀ v : U, (Fintype.card U : ℝ) ^ a (m + 1) ≤ ↑(H'.degree v)) →
                (∃ t : ℕ, Real.log ↑(Fintype.card U) ≤ ↑t ∧
                  IsShallowMinor (SimpleGraph.completeGraph (Fin (t + 1))) H' 1) ∨
                (∃ (U' : Type) (_ : DecidableEq U') (_ : Fintype U')
                  (H'' : SimpleGraph U') (_ : DecidableRel H''.Adj),
                  IsShallowMinor H'' H' 1 ∧
                  (Fintype.card U : ℝ) ^ (1 - a (m + 1)) ≤ ↑(Fintype.card U') ∧
                  (Fintype.card U' : ℝ) ^ (1 + a (m + 1) + a (m + 1) ^ 2) ≤
                    ↑(H''.edgeFinset.card)) := by
            intro U _ _ H' _ hM hdeg
            exact hDensifySeq (m := m + 1) hm H' hM hdeg
          have hStep := step_or_clique H (MSeq (m + 1))
            (ha_pos (m + 1)) (ha_lt_23 hm).le hδ_pos (hδa hm)
            (le_trans (hB_M hm) hCardBase) (le_trans hB_clique hCardBase) hRound hEdge
            (hDensify := hDensifyNow)
          rcases hStep with hClique | hBoost
          · exact hCliqueImpossible (m + 1) hm H hMinor hClique
          · rcases hBoost with ⟨hSmall, W', hWDec, hWFint, H', hHDec, hMinorStep, hCardStep, hEdgeStep⟩
            have hCardStepNat : Fintype.card W ≤ (Fintype.card W') ^ 6 := by
              exact_mod_cast hCardStep
            have hCard' : sizeSeq B m ≤ Fintype.card W' := by
              have hPow : (sizeSeq B m) ^ 6 ≤ (Fintype.card W') ^ 6 := by
                calc
                  (sizeSeq B m) ^ 6 = sizeSeq B (m + 1) := by simp [sizeSeq]
                  _ ≤ Fintype.card W := hCard
                  _ ≤ (Fintype.card W') ^ 6 := hCardStepNat
              exact le_of_pow_six_le_pow_six hPow
            have hMinor' : IsShallowMinor H' G (iterationDepth (k - m)) := by
              have hkm : k - m = (k - (m + 1)) + 1 := by
                omega
              have hComp0 :
                  IsShallowMinor H' G
                    (2 * iterationDepth (k - (m + 1)) * 1 + iterationDepth (k - (m + 1)) + 1) :=
                shallowMinor_trans hMinorStep hMinor
              have hDepthEq :
                  2 * iterationDepth (k - (m + 1)) * 1 + iterationDepth (k - (m + 1)) + 1 =
                    iterationDepth (k - m) := by
                rw [hkm]
                simp [iterationDepth, two_mul]
                omega
              exact hDepthEq ▸ hComp0
            have hEdge' :
                (Fintype.card W' : ℝ) ^ (1 + a m + δ) ≤ (H'.edgeFinset.card : ℝ) := by
              have haeq : a m = a (m + 1) + δ := ha_step hm
              calc
                (Fintype.card W' : ℝ) ^ (1 + a m + δ)
                    = (Fintype.card W' : ℝ) ^ (1 + a (m + 1) + 2 * δ) := by
                        rw [haeq]
                        congr 1
                        ring
                _ ≤ (H'.edgeFinset.card : ℝ) := hEdgeStep
            exact ih hm' H' hMinor' hCard' (by convert hEdge')
    by_contra hDense
    have hInitDense : n ^ (1 + a k + δ) ≤ (G.edgeFinset.card : ℝ) := by
      have hExp : 1 + a k + δ ≤ 1 + ε := by
        simpa [a, add_assoc] using ha0δ_le_ε
      exact le_trans (Real.rpow_le_rpow_of_exponent_le hn_one hExp) (not_lt.mp hDense)
    have hMinor0 : IsShallowMinor G G (iterationDepth (k - k)) := by
      simpa [iterationDepth] using
        (isShallowMinor_zero_of_embedding (SimpleGraph.Embedding.refl (G := G)))
    exact hIter k le_rfl G hMinor0 hN (by convert hInitDense)

/-- Theorem 3.1/ch1: Nowhere dense classes have subpolynomial edge density. -/
theorem nd_subpolynomial_density (C : GraphClass) (hC : IsNowhereDense C)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ {V : Type} [DecidableEq V] [Fintype V]
      (H : SimpleGraph V) [DecidableRel H.Adj],
      (∃ (W : Type) (_ : DecidableEq W) (_ : Fintype W) (G : SimpleGraph W),
        C G ∧ IsShallowMinor H G r) →
      N ≤ Fintype.card V →
      (H.edgeFinset.card : ℝ) < (Fintype.card V : ℝ) ^ (1 + ε) := by
  obtain ⟨N, hN⟩ := nd_subpolynomial_density_depthZero
    (ShallowReduct C r) (nowhereDense_shallowReduct C r hC) ε hε
  refine ⟨N, ?_⟩
  intro V _ _ H _ hHr hCard
  exact hN H hHr hCard

end

end Lax5Proofs.Source.Catalog.SparsityLectures.NDSubpolynomialDensity
