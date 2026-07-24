import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Choose.Basic
import Lax5Proofs.Ramsey
import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowTopologicalMinor.Full

/-!
The bipartite Ramsey lemma of the sparsity lecture notes (Lemma 3.9) and
its iterated form (Lemma 3.10): a large side of a bipartite graph yields
vertices with no common neighbor (outside a small separator), a
1-subdivided clique, or a high-degree vertex / biclique.  Uses the
shallow topological minor models from the ported sparsity development.
-/

namespace Lax5Proofs.BipartiteRamsey

open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowTopologicalMinor

private noncomputable def localNeighborPair
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (b u v : V) (huA : u ∈ A) (hvA : v ∈ A)
    (hub : G.Adj b u) (hvb : G.Adj b v) (huv : u ≠ v) :
    (SimpleGraph.completeGraph ↑(((G.neighborFinset b ∩ A : Finset V) : Set V))).edgeSet := by
  refine ⟨s(⟨u, by simp [huA, hub]⟩, ⟨v, by simp [hvA, hvb]⟩), ?_⟩
  rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
  intro h
  apply huv
  exact Subtype.ext_iff.mp h

private theorem localPairCodeBound
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (d : ℕ)
    {b : V} (hdeg : (G.neighborFinset b ∩ A).card < d) :
    Fintype.card
        ((SimpleGraph.completeGraph ↑(((G.neighborFinset b ∩ A : Finset V) : Set V))).edgeSet) ≤
      Nat.choose (d - 1) 2 := by
  have hcard_eq :
      Fintype.card
          ((SimpleGraph.completeGraph ↑(((G.neighborFinset b ∩ A : Finset V) : Set V))).edgeSet) =
        (G.neighborFinset b ∩ A).card.choose 2 := by
    have hfilter : {a ∈ A | G.Adj b a} = G.neighborFinset b ∩ A := by
      ext x
      simp [and_comm]
    have hfilter_card : {a ∈ A | G.Adj b a}.card = (G.neighborFinset b ∩ A).card := by
      rw [hfilter]
    calc
      Fintype.card
          ((SimpleGraph.completeGraph ↑(((G.neighborFinset b ∩ A : Finset V) : Set V))).edgeSet) =
        {a ∈ A | G.Adj b a}.card.choose 2 := by
          rw [SimpleGraph.card_edgeSet]
          simpa [Fintype.card_of_finset' (G.neighborFinset b ∩ A) (fun x => Iff.rfl)] using
            (SimpleGraph.card_edgeFinset_top_eq_card_choose_two
              (V := ↑(((G.neighborFinset b ∩ A : Finset V) : Set V))))
      _ = (G.neighborFinset b ∩ A).card.choose 2 := by rw [hfilter_card]
  have hle : (G.neighborFinset b ∩ A).card ≤ d - 1 := by
    omega
  calc
    Fintype.card
        ((SimpleGraph.completeGraph ↑(((G.neighborFinset b ∩ A : Finset V) : Set V))).edgeSet) =
      (G.neighborFinset b ∩ A).card.choose 2 := hcard_eq
    _ ≤ Nat.choose (d - 1) 2 := Nat.choose_le_choose 2 hle

private noncomputable def localPairCode
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (d : ℕ)
    (b u v : V) (huA : u ∈ A) (hvA : v ∈ A)
    (hub : G.Adj b u) (hvb : G.Adj b v) (huv : u ≠ v)
    (hdeg : (G.neighborFinset b ∩ A).card < d) :
    Fin (Nat.choose (d - 1) 2) :=
  Fin.castLE (localPairCodeBound G A d hdeg)
    ((Fintype.equivFin
      ((SimpleGraph.completeGraph ↑(((G.neighborFinset b ∩ A : Finset V) : Set V))).edgeSet))
      (localNeighborPair G A b u v huA hvA hub hvb huv))

private theorem localNeighborPair_symm
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (b u v : V) (huA : u ∈ A) (hvA : v ∈ A)
    (hub : G.Adj b u) (hvb : G.Adj b v) (huv : u ≠ v) :
    localNeighborPair G A b u v huA hvA hub hvb huv =
      localNeighborPair G A b v u hvA huA hvb hub huv.symm := by
  apply Subtype.ext
  simp [localNeighborPair, Sym2.eq_swap]

private theorem localPairCode_symm
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (d : ℕ)
    {b u v : V} (huA : u ∈ A) (hvA : v ∈ A)
    (hub : G.Adj b u) (hvb : G.Adj b v) (huv : u ≠ v)
    (hdeg : (G.neighborFinset b ∩ A).card < d) :
    localPairCode G A d b u v huA hvA hub hvb huv hdeg =
      localPairCode G A d b v u hvA huA hvb hub huv.symm hdeg := by
  dsimp [localPairCode]
  rw [localNeighborPair_symm G A b u v huA hvA hub hvb huv]

private theorem localPairCode_injective
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (d : ℕ)
    {b u₁ v₁ u₂ v₂ : V}
    (hu₁A : u₁ ∈ A) (hv₁A : v₁ ∈ A) (hu₂A : u₂ ∈ A) (hv₂A : v₂ ∈ A)
    (hu₁b : G.Adj b u₁) (hv₁b : G.Adj b v₁)
    (hu₂b : G.Adj b u₂) (hv₂b : G.Adj b v₂)
    (huv₁ : u₁ ≠ v₁) (huv₂ : u₂ ≠ v₂)
    (hdeg : (G.neighborFinset b ∩ A).card < d)
    (hcode :
      localPairCode G A d b u₁ v₁ hu₁A hv₁A hu₁b hv₁b huv₁ hdeg =
        localPairCode G A d b u₂ v₂ hu₂A hv₂A hu₂b hv₂b huv₂ hdeg) :
    s(u₁, v₁) = s(u₂, v₂) := by
  dsimp [localPairCode] at hcode
  have hpair_eq :
      localNeighborPair G A b u₁ v₁ hu₁A hv₁A hu₁b hv₁b huv₁ =
        localNeighborPair G A b u₂ v₂ hu₂A hv₂A hu₂b hv₂b huv₂ := by
    apply (Fintype.equivFin
      ((SimpleGraph.completeGraph ↑(((G.neighborFinset b ∩ A : Finset V) : Set V))).edgeSet)).injective
    exact Fin.castLE_injective (localPairCodeBound G A d hdeg) hcode
  simpa [localNeighborPair] using congrArg Subtype.val hpair_eq

private noncomputable def commonNeighborCodes
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (d : ℕ)
    (hdeg : ∀ b : ↑B, (G.neighborFinset b.1 ∩ A).card < d)
    (u v : ↑(A : Set V)) :
    Finset (Fin (Nat.choose (d - 1) 2)) :=
  (B.attach).biUnion fun bw =>
    if huv : u.1 ≠ v.1 ∧ G.Adj bw.1 u.1 ∧ G.Adj bw.1 v.1 then
      {localPairCode G A d bw.1 u.1 v.1 u.2 v.2 huv.2.1 huv.2.2 huv.1 (hdeg bw)}
    else
      ∅

private theorem mem_commonNeighborCodes
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (d : ℕ)
    (hdeg : ∀ b : ↑B, (G.neighborFinset b.1 ∩ A).card < d)
    (u v : ↑(A : Set V)) (x : Fin (Nat.choose (d - 1) 2)) :
    x ∈ commonNeighborCodes G A B d hdeg u v ↔
      ∃ (b : V) (hb : b ∈ B) (huv : u.1 ≠ v.1) (hub : G.Adj b u.1) (hvb : G.Adj b v.1),
        localPairCode G A d b u.1 v.1 u.2 v.2 hub hvb huv (hdeg ⟨b, hb⟩) = x := by
  classical
  unfold commonNeighborCodes
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨b, -, hmem⟩
    by_cases huv : u.1 ≠ v.1 ∧ G.Adj b.1 u.1 ∧ G.Adj b.1 v.1
    · refine ⟨b.1, b.2, huv.1, huv.2.1, huv.2.2, ?_⟩
      have hx : x = localPairCode G A d b.1 u.1 v.1 u.2 v.2
          huv.2.1 huv.2.2 huv.1 (hdeg b) := by
        simpa [huv] using hmem
      exact hx.symm
    · have hfalse : ¬(¬u = v ∧ G.Adj b.1 u.1 ∧ G.Adj b.1 v.1) := by
        simpa using huv
      simp [hfalse] at hmem
  · rintro ⟨b, hb, huv, hub, hvb, hx⟩
    refine ⟨⟨b, hb⟩, by simp, ?_⟩
    simpa [huv, hub, hvb] using hx.symm

private theorem commonNeighborCodes_symm
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (d : ℕ)
    (hdeg : ∀ b : ↑B, (G.neighborFinset b.1 ∩ A).card < d)
    (u v : ↑(A : Set V)) :
    commonNeighborCodes G A B d hdeg u v =
      commonNeighborCodes G A B d hdeg v u := by
  classical
  ext x
  constructor
  · intro hx
    rcases (mem_commonNeighborCodes G A B d hdeg u v x).1 hx with
      ⟨b, hb, huv, hub, hvb, hcode⟩
    refine (mem_commonNeighborCodes G A B d hdeg v u x).2 ?_
    refine ⟨b, hb, huv.symm, hvb, hub, ?_⟩
    exact (localPairCode_symm G A d u.2 v.2 hub hvb huv (hdeg ⟨b, hb⟩)).symm.trans hcode
  · intro hx
    rcases (mem_commonNeighborCodes G A B d hdeg v u x).1 hx with
      ⟨b, hb, huv, hub, hvb, hcode⟩
    refine (mem_commonNeighborCodes G A B d hdeg u v x).2 ?_
    refine ⟨b, hb, huv.symm, hvb, hub, ?_⟩
    exact (localPairCode_symm G A d u.2 v.2 hvb hub huv.symm (hdeg ⟨b, hb⟩)).trans hcode

private noncomputable def edgeColor
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (d : ℕ)
    (hdeg : ∀ b : ↑B, (G.neighborFinset b.1 ∩ A).card < d)
    (u v : ↑(A : Set V)) :
    Fin (Nat.choose (d - 1) 2 + 1) :=
  if hcodes : (commonNeighborCodes G A B d hdeg u v).Nonempty then
    Fin.castLE (Nat.le_succ _) ((commonNeighborCodes G A B d hdeg u v).min' hcodes)
  else
    Fin.last _

private theorem edgeColor_symm
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (d : ℕ)
    (hdeg : ∀ b : ↑B, (G.neighborFinset b.1 ∩ A).card < d)
    (u v : ↑(A : Set V)) :
    edgeColor G A B d hdeg u v = edgeColor G A B d hdeg v u := by
  classical
  simp [edgeColor, commonNeighborCodes_symm]

private theorem exists_commonNeighbor_of_edgeColor_eq
    {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (d : ℕ)
    (hdeg : ∀ b : ↑B, (G.neighborFinset b.1 ∩ A).card < d)
    {u v : ↑(A : Set V)} (huv : u ≠ v) {j : Fin (Nat.choose (d - 1) 2)}
    (hcolor : edgeColor G A B d hdeg u v = Fin.castLE (Nat.le_succ _) j) :
    ∃ (b : V) (hb : b ∈ B) (hub : G.Adj b u.1) (hvb : G.Adj b v.1),
      localPairCode G A d b u.1 v.1 u.2 v.2
        hub hvb (fun h => huv (Subtype.ext h)) (hdeg ⟨b, hb⟩) = j := by
  classical
  let codes := commonNeighborCodes G A B d hdeg u v
  by_cases hcodes : codes.Nonempty
  · have hmin :
        Fin.castLE (Nat.le_succ _) (codes.min' hcodes) =
          Fin.castLE (Nat.le_succ _) j := by
        simpa [edgeColor, codes, hcodes] using hcolor
    have hmin_eq : codes.min' hcodes = j := Fin.castLE_injective _ hmin
    have hmem : j ∈ codes := by
      rw [← hmin_eq]
      exact Finset.min'_mem codes hcodes
    rcases (mem_commonNeighborCodes G A B d hdeg u v j).1 hmem with
      ⟨b, hb, _, hub, hvb, hcode⟩
    exact ⟨b, hb, hub, hvb, hcode⟩
  · have hlast :
        edgeColor G A B d hdeg u v = Fin.last (Nat.choose (d - 1) 2) := by
        simp [edgeColor, codes, hcodes]
    have hne :
        Fin.castLE (Nat.le_succ _) j ≠ Fin.last (Nat.choose (d - 1) 2) := by
      intro h
      have hval := congrArg Fin.val h
      exact Nat.ne_of_lt j.isLt hval
    exact (hne (hcolor.symm.trans hlast)).elim

/-- Lemma 3.9: in a bipartite graph with sides `A` and `B`, if `|A|` is large
    enough (as a function of `m`, `t`, `d`), then at least one of the following
    holds:
    (a) `A` contains `m` vertices with no common neighbor,
    (b) `G` contains a `1`-subdivision of `K_t` with principal vertices in `A`,
    (c) `B` contains a vertex of degree at least `d`. -/
theorem bipartite_ramsey (m t d : ℕ) :
    ∃ N : ℕ, ∀ {V : Type} [DecidableEq V] [Fintype V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (A B : Finset V),
      Disjoint A B →
      (∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) →
      N ≤ A.card →
      (∃ A' : Finset V, A' ⊆ A ∧ m ≤ A'.card ∧
        (↑A' : Set V).Pairwise (fun u v =>
          ∀ w, ¬(G.Adj u w ∧ G.Adj v w))) ∨
      (∃ M : ShallowTopologicalMinorModel
          (SimpleGraph.completeGraph (Fin t)) G 1,
        Set.range M.branchVertex ⊆ ↑A) ∨
      (∃ v ∈ B, d ≤ (G.neighborFinset v ∩ A).card) := by
  classical
  let k := Nat.choose (d - 1) 2
  let sizes : List ℕ := List.replicate k t ++ [m]
  obtain ⟨N, hN⟩ := Ramsey.multicolor_ramsey sizes (by
    simp [sizes])
  refine ⟨N, ?_⟩
  intro V _ _ G _ A B hAB hBip hAcard
  by_cases hbig : ∃ v ∈ B, d ≤ (G.neighborFinset v ∩ A).card
  · exact Or.inr (Or.inr hbig)
  · have hdeg : ∀ b : ↑B, (G.neighborFinset b.1 ∩ A).card < d := by
      intro b
      exact lt_of_not_ge (fun hge => hbig ⟨b.1, b.2, hge⟩)
    have hcA : N ≤ Fintype.card ↑(A : Set V) := by
      rw [Fintype.card_of_finset' A (fun x => Iff.rfl)]
      exact hAcard
    let c0 : Sym2 ↑(A : Set V) → Fin (k + 1) :=
      Sym2.lift ⟨edgeColor G A B d hdeg, edgeColor_symm G A B d hdeg⟩
    let c : Sym2 ↑(A : Set V) → Fin sizes.length :=
      fun e => Fin.cast (by simp [sizes]) (c0 e)
    obtain ⟨i, S, hsize, hpair⟩ := hN (V := ↑(A : Set V)) hcA c
    by_cases hiLast : i.1 = k
    · let lastColor : Fin sizes.length := ⟨k, by simp [sizes]⟩
      have hi_eq_last : i = lastColor := by
        apply Fin.ext
        simp [lastColor, hiLast]
      refine Or.inl ⟨S.map ⟨Subtype.val, Subtype.val_injective⟩, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_map.mp hx with ⟨u, hu, rfl⟩
        exact u.2
      · have hmle : m ≤ S.card := by
          simpa [sizes, hiLast] using hsize
        simpa using hmle
      · intro u hu v hv huv w huw
        rcases Finset.mem_map.mp hu with ⟨u', hu', rfl⟩
        rcases Finset.mem_map.mp hv with ⟨v', hv', rfl⟩
        have huv' : u' ≠ v' := by
          intro h
          apply huv
          exact congrArg Subtype.val h
        have hcolor : c s(u', v') = lastColor := by
          exact (hpair hu' hv' huv').trans hi_eq_last
        have hwB : w ∈ B := by
          rcases hBip u'.1 w huw.1 with ⟨huA, hwB⟩ | ⟨huB, hwA⟩
          · exact hwB
          · exact (Finset.disjoint_left.mp hAB u'.2 huB).elim
        have hcodes_nonempty :
            (commonNeighborCodes G A B d hdeg u' v').Nonempty := by
          refine ⟨localPairCode G A d w u'.1 v'.1 u'.2 v'.2
              (G.symm huw.1) (G.symm huw.2) (fun h => huv' (Subtype.ext h)) (hdeg ⟨w, hwB⟩), ?_⟩
          exact (mem_commonNeighborCodes G A B d hdeg u' v'
            (localPairCode G A d w u'.1 v'.1 u'.2 v'.2
              (G.symm huw.1) (G.symm huw.2) (fun h => huv' (Subtype.ext h)) (hdeg ⟨w, hwB⟩))).2
            ⟨w, hwB, fun h => huv' (Subtype.ext h), G.symm huw.1, G.symm huw.2, rfl⟩
        have hcolor0 : edgeColor G A B d hdeg u' v' = Fin.last k := by
          have hcolor' : c0 s(u', v') = Fin.last k := by
            apply Fin.ext
            simpa [c, sizes, lastColor] using congrArg Fin.val hcolor
          simpa [c0] using hcolor'
        have hnotlast :
            edgeColor G A B d hdeg u' v' ≠ Fin.last k := by
          have hbase :
              Fin.castLE (Nat.le_succ k) ((commonNeighborCodes G A B d hdeg u' v').min' hcodes_nonempty) ≠
                Fin.last k := by
            intro h
            have hval := congrArg Fin.val h
            exact Nat.ne_of_lt ((commonNeighborCodes G A B d hdeg u' v').min' hcodes_nonempty).isLt hval
          simpa [edgeColor, hcodes_nonempty] using hbase
        exact hnotlast hcolor0
    · have hik1 : i.1 < k + 1 := by
          simpa [sizes] using i.isLt
      have hj : i.1 < k := by
          omega
      let j : Fin k := ⟨i.1, hj⟩
      have htle : t ≤ S.card := by
        simpa [sizes, List.get_eq_getElem, hj] using hsize
      obtain ⟨T, hTS, hTcard⟩ : ∃ T : Finset ↑(A : Set V), T ⊆ S ∧ T.card = t := by
        obtain ⟨T, hT⟩ := Finset.powersetCard_nonempty.2 htle
        exact ⟨T, (Finset.mem_powersetCard.mp hT).1, (Finset.mem_powersetCard.mp hT).2⟩
      let f0 : Fin t ↪ ↑(T : Set ↑(A : Set V)) :=
        (Fintype.equivFinOfCardEq
          (α := ↑(T : Set ↑(A : Set V)))
          (by rw [Fintype.card_of_finset' T (fun x => Iff.rfl), hTcard])).symm.toEmbedding
      let f : Fin t ↪ V := {
        toFun x := (f0 x).1.1
        inj' := by
          intro a b hab
          apply f0.inj'
          apply Subtype.ext
          apply Subtype.ext
          exact hab
      }
      have hfA : Set.range f ⊆ ↑A := by
        intro x hx
        rcases hx with ⟨a, rfl⟩
        exact (f0 a).1.2
      have hcolor_edge :
          ∀ a b : Fin t, a ≠ b →
            edgeColor G A B d hdeg ((f0 a).1) ((f0 b).1) = Fin.castLE (Nat.le_succ k) j := by
        intro a b hab
        have hab' : (f0 a).1 ≠ (f0 b).1 := by
          intro h
          apply hab
          exact f0.inj' (Subtype.ext h)
        have haS : (f0 a).1 ∈ S := hTS (f0 a).2
        have hbS : (f0 b).1 ∈ S := hTS (f0 b).2
        have hpair' : c s((f0 a).1, (f0 b).1) = i := hpair haS hbS hab'
        apply Fin.ext
        simpa [c, c0, sizes, j] using congrArg Fin.val hpair'
      have hmid :
          ∀ a b : Fin t, ∀ hab : a ≠ b,
            ∃ (w : V) (hwB : w ∈ B) (hwa : G.Adj w (f a)) (hwb : G.Adj w (f b)),
              localPairCode G A d w (f a) (f b)
                ((f0 a).1).2 ((f0 b).1).2
                hwa hwb
                (fun h => hab (f.injective h)) (hdeg ⟨w, hwB⟩) = j := by
        intro a b hab
        simpa [f] using
          exists_commonNeighbor_of_edgeColor_eq G A B d hdeg
            (u := ((f0 a).1)) (v := ((f0 b).1))
            (fun h => hab (f0.inj' (Subtype.ext h))) (hcolor_edge a b hab)
      let edgeTail : (SimpleGraph.completeGraph (Fin t)).edgeSet → Fin t := fun e => e.1.out.1
      have hedgeTail_mem : ∀ e : (SimpleGraph.completeGraph (Fin t)).edgeSet,
          edgeTail e ∈ (e : Sym2 (Fin t)) := by
        intro e
        exact Sym2.out_fst_mem (e : Sym2 (Fin t))
      let edgeHead : (SimpleGraph.completeGraph (Fin t)).edgeSet → Fin t :=
        fun e => Sym2.Mem.other (hedgeTail_mem e)
      have hedge_ne : ∀ e : (SimpleGraph.completeGraph (Fin t)).edgeSet, edgeTail e ≠ edgeHead e := by
        intro e
        have heMem : s(edgeTail e, edgeHead e) ∈ (SimpleGraph.completeGraph (Fin t)).edgeSet := by
          rw [Sym2.other_spec (hedgeTail_mem e)]
          exact e.2
        have heAdj : (SimpleGraph.completeGraph (Fin t)).Adj (edgeTail e) (edgeHead e) := by
          rw [SimpleGraph.mem_edgeSet] at heMem
          exact heMem
        exact (SimpleGraph.top_adj _ _).mp heAdj
      let edgeMid : (SimpleGraph.completeGraph (Fin t)).edgeSet → V :=
        fun e => (hmid (edgeTail e) (edgeHead e) (hedge_ne e)).choose
      have hedgeMid_memB : ∀ e : (SimpleGraph.completeGraph (Fin t)).edgeSet, edgeMid e ∈ B := by
        intro e
        exact (hmid (edgeTail e) (edgeHead e) (hedge_ne e)).choose_spec.1
      have hedgeMid_adj_tail :
          ∀ e : (SimpleGraph.completeGraph (Fin t)).edgeSet, G.Adj (edgeMid e) (f (edgeTail e)) := by
        intro e
        exact (hmid (edgeTail e) (edgeHead e) (hedge_ne e)).choose_spec.2.1
      have hedgeMid_adj_head :
          ∀ e : (SimpleGraph.completeGraph (Fin t)).edgeSet, G.Adj (edgeMid e) (f (edgeHead e)) := by
        intro e
        exact (hmid (edgeTail e) (edgeHead e) (hedge_ne e)).choose_spec.2.2.1
      have hedgeMid_code :
          ∀ e : (SimpleGraph.completeGraph (Fin t)).edgeSet,
            localPairCode G A d (edgeMid e) (f (edgeTail e)) (f (edgeHead e))
              ((f0 (edgeTail e)).1).2 ((f0 (edgeHead e)).1).2
              (hedgeMid_adj_tail e) (hedgeMid_adj_head e)
              (fun h => hedge_ne e (f.injective h)) (hdeg ⟨edgeMid e, hedgeMid_memB e⟩) = j := by
        intro e
        exact (hmid (edgeTail e) (edgeHead e) (hedge_ne e)).choose_spec.2.2.2
      refine Or.inr (Or.inl ⟨{
        branchVertex := f
        edgeTail := edgeTail
        edgeTail_mem := hedgeTail_mem
        edgePath := fun e =>
          SimpleGraph.Walk.cons (G.symm (hedgeMid_adj_tail e))
            (SimpleGraph.Walk.cons (hedgeMid_adj_head e) SimpleGraph.Walk.nil)
        edgePath_isPath := by
          intro e
          have hfw : f (edgeTail e) ≠ edgeMid e := by
            intro hEq
            exact Finset.disjoint_left.mp hAB (hfA ⟨edgeTail e, rfl⟩) (hEq ▸ hedgeMid_memB e)
          have hff : f (edgeTail e) ≠ f (edgeHead e) := by
            exact fun h => hedge_ne e (f.injective h)
          exact SimpleGraph.Walk.IsPath.cons
            (SimpleGraph.Walk.IsPath.of_adj (hedgeMid_adj_head e))
            (by simp [hfw, hff])
        edgePath_length := by
          intro e
          simp
        edgePath_interior_avoids_branch := by
          intro e x hx htail hhead w
          have hxmid : x = edgeMid e := by
            have hx' : x = edgeMid e ∨ x = f (edgeHead e) := by
              simpa [htail] using hx
            rcases hx' with hx' | hx'
            · exact hx'
            · exact (hhead hx').elim
          intro hEq
          have hbranchA : f w ∈ A := hfA ⟨w, rfl⟩
          have hmidB : edgeMid e ∈ B := hedgeMid_memB e
          have hEq' : edgeMid e = f w := hxmid.symm.trans hEq
          exact Finset.disjoint_left.mp hAB hbranchA (hEq' ▸ hmidB)
        edgePath_interior_disjoint := by
          intro e e' x hne hx hx' htail hhead htail' hhead'
          have hxmid : x = edgeMid e := by
            have hx'' : x = edgeMid e ∨ x = f (edgeHead e) := by
              simpa [htail] using hx
            rcases hx'' with hx'' | hx''
            · exact hx''
            · exact (hhead hx'').elim
          have hxmid' : x = edgeMid e' := by
            have hx'' : x = edgeMid e' ∨ x = f (edgeHead e') := by
              simpa [htail'] using hx'
            rcases hx'' with hx'' | hx''
            · exact hx''
            · exact (hhead' hx'').elim
          have hmidEq : edgeMid e = edgeMid e' := hxmid.symm.trans hxmid'
          let bmid := edgeMid e
          have hbmidB : bmid ∈ B := hedgeMid_memB e
          have htail'_adj : G.Adj bmid (f (edgeTail e')) := by
            simpa [bmid, hmidEq] using hedgeMid_adj_tail e'
          have hhead'_adj : G.Adj bmid (f (edgeHead e')) := by
            simpa [bmid, hmidEq] using hedgeMid_adj_head e'
          have hcodeEq :
              localPairCode G A d bmid (f (edgeTail e)) (f (edgeHead e))
                ((f0 (edgeTail e)).1).2 ((f0 (edgeHead e)).1).2
                (hedgeMid_adj_tail e) (hedgeMid_adj_head e)
                (fun h => hedge_ne e (f.injective h)) (hdeg ⟨bmid, hbmidB⟩) =
              localPairCode G A d bmid (f (edgeTail e')) (f (edgeHead e'))
                ((f0 (edgeTail e')).1).2 ((f0 (edgeHead e')).1).2
                htail'_adj hhead'_adj
                (fun h => hedge_ne e' (f.injective h)) (hdeg ⟨bmid, hbmidB⟩) := by
            calc
              localPairCode G A d bmid (f (edgeTail e)) (f (edgeHead e))
                  ((f0 (edgeTail e)).1).2 ((f0 (edgeHead e)).1).2
                  (hedgeMid_adj_tail e) (hedgeMid_adj_head e)
                  (fun h => hedge_ne e (f.injective h)) (hdeg ⟨bmid, hbmidB⟩) = j := by
                    exact hedgeMid_code e
              _ = localPairCode G A d bmid (f (edgeTail e')) (f (edgeHead e'))
                    ((f0 (edgeTail e')).1).2 ((f0 (edgeHead e')).1).2
                    htail'_adj hhead'_adj
                    (fun h => hedge_ne e' (f.injective h)) (hdeg ⟨bmid, hbmidB⟩) := by
                    simpa [bmid, hmidEq] using (hedgeMid_code e').symm
          have hpairV :
              s(f (edgeTail e), f (edgeHead e)) = s(f (edgeTail e'), f (edgeHead e')) := by
            exact localPairCode_injective G A d
              ((f0 (edgeTail e)).1).2 ((f0 (edgeHead e)).1).2
              ((f0 (edgeTail e')).1).2 ((f0 (edgeHead e')).1).2
              (hedgeMid_adj_tail e) (hedgeMid_adj_head e)
              htail'_adj hhead'_adj
              (fun h => hedge_ne e (f.injective h))
              (fun h => hedge_ne e' (f.injective h))
              (hdeg ⟨bmid, hbmidB⟩) hcodeEq
          have hpairFin :
              s(edgeTail e, edgeHead e) = s(edgeTail e', edgeHead e') := by
            apply (Sym2.map.injective f.injective)
            simpa using hpairV
          have heq : e = e' := by
            apply Subtype.ext
            calc
              (e : Sym2 (Fin t)) = s(edgeTail e, edgeHead e) := by
                symm
                exact Sym2.other_spec (hedgeTail_mem e)
              _ = s(edgeTail e', edgeHead e') := hpairFin
              _ = (e' : Sym2 (Fin t)) := by
                exact Sym2.other_spec (hedgeTail_mem e')
          exact hne heq
      }, hfA⟩)

/-- Recursive bound for the iterative bipartite Ramsey lemma. -/
private noncomputable def R_star : ℕ → ℕ → ℕ → ℕ
  | 0, t, _ => t
  | s + 1, t, m => (bipartite_ramsey m t (R_star s t m)).choose

private noncomputable def topologicalMinorModel_of_subgraph
    {V W : Type} {H : SimpleGraph W} {G G' : SimpleGraph V} {d : ℕ}
    (M : ShallowTopologicalMinorModel H G d)
    (hsub : ∀ {u v}, G.Adj u v → G'.Adj u v) :
    ShallowTopologicalMinorModel H G' d :=
  { branchVertex := M.branchVertex
    edgeTail := M.edgeTail
    edgeTail_mem := M.edgeTail_mem
    edgePath := fun e => by
      let p := M.edgePath e
      have hedge : ∀ e' ∈ p.edges, e' ∈ G'.edgeSet := by
        intro e' he'
        have hmem := SimpleGraph.Walk.edges_subset_edgeSet p he'
        revert hmem
        refine e'.ind ?_
        intro a b hab
        exact show G'.Adj a b by exact hsub hab
      exact p.transfer G' hedge
    edgePath_isPath := by
      intro e
      let p := M.edgePath e
      have hedge : ∀ e' ∈ p.edges, e' ∈ G'.edgeSet := by
        intro e' he'
        have hmem := SimpleGraph.Walk.edges_subset_edgeSet p he'
        revert hmem
        refine e'.ind ?_
        intro a b hab
        exact show G'.Adj a b by exact hsub hab
      simpa [p] using (M.edgePath_isPath e).transfer hedge
    edgePath_length := by
      intro e
      let p := M.edgePath e
      have hedge : ∀ e' ∈ p.edges, e' ∈ G'.edgeSet := by
        intro e' he'
        have hmem := SimpleGraph.Walk.edges_subset_edgeSet p he'
        revert hmem
        refine e'.ind ?_
        intro a b hab
        exact show G'.Adj a b by exact hsub hab
      rw [show ((p.transfer G' hedge)).length = p.length by
        rw [SimpleGraph.Walk.length_transfer]]
      exact M.edgePath_length e
    edgePath_interior_avoids_branch := by
      intro e x hx htail hhead w
      let p := M.edgePath e
      have hedge : ∀ e' ∈ p.edges, e' ∈ G'.edgeSet := by
        intro e' he'
        have hmem := SimpleGraph.Walk.edges_subset_edgeSet p he'
        revert hmem
        refine e'.ind ?_
        intro a b hab
        exact show G'.Adj a b by exact hsub hab
      rw [show (p.transfer G' hedge).support = p.support by
        rw [SimpleGraph.Walk.support_transfer]] at hx
      exact M.edgePath_interior_avoids_branch e hx htail hhead w
    edgePath_interior_disjoint := by
      intro e e' x hne hx hx' htail hhead htail' hhead'
      let p := M.edgePath e
      let p' := M.edgePath e'
      have hedge : ∀ e'' ∈ p.edges, e'' ∈ G'.edgeSet := by
        intro e'' he''
        have hmem := SimpleGraph.Walk.edges_subset_edgeSet p he''
        revert hmem
        refine e''.ind ?_
        intro a b hab
        exact show G'.Adj a b by exact hsub hab
      have hedge' : ∀ e'' ∈ p'.edges, e'' ∈ G'.edgeSet := by
        intro e'' he''
        have hmem := SimpleGraph.Walk.edges_subset_edgeSet p' he''
        revert hmem
        refine e''.ind ?_
        intro a b hab
        exact show G'.Adj a b by exact hsub hab
      rw [show (p.transfer G' hedge).support = p.support by
        rw [SimpleGraph.Walk.support_transfer]] at hx
      rw [show (p'.transfer G' hedge').support = p'.support by
        rw [SimpleGraph.Walk.support_transfer]] at hx'
      exact M.edgePath_interior_disjoint e e' hne hx hx' htail hhead htail' hhead' }

/-- Core induction: with `s` steps remaining and `collected` vertices already
    gathered (each adjacent to all of `A_cur`), produce one of the three
    outcomes of Lemma 3.10. -/
private theorem iterStep (m t : ℕ) :
    ∀ (s : ℕ), ∀ {V : Type} [DecidableEq V] [Fintype V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (A B A_cur collected : Finset V),
      Disjoint A B →
      (∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) →
      A_cur ⊆ A → collected ⊆ B →
      R_star s t m ≤ A_cur.card →
      collected.card + s = t →
      (∀ v ∈ collected, ∀ u ∈ A_cur, G.Adj u v) →
      (∃ (A' S : Finset V),
        A' ⊆ A ∧ S ⊆ B ∧ m ≤ A'.card ∧ S.card < t ∧
        (↑A' : Set V).Pairwise (fun u v =>
          ∀ w, w ∉ (S : Set V) → ¬(G.Adj u w ∧ G.Adj v w))) ∨
      (∃ M : ShallowTopologicalMinorModel
          (SimpleGraph.completeGraph (Fin t)) G 1,
        Set.range M.branchVertex ⊆ ↑A) ∨
      (∃ (X Y : Finset V),
        X ⊆ A ∧ Y ⊆ B ∧ t ≤ X.card ∧ t ≤ Y.card ∧
        ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) := by
  intro s
  induction s with
  | zero =>
    -- Base case: collected has t elements, |A_cur| ≥ t → build K_{t,t}
    intro V _ _ G _ A B A_cur collected _ _ hAcur hCsub hCard hSum hAllAdj
    right; right
    obtain ⟨X, hXsub, hXcard⟩ := Finset.exists_subset_card_eq (show t ≤ A_cur.card from hCard)
    exact ⟨X, collected, hXsub.trans hAcur, hCsub, hXcard.ge,
      (show collected.card = t by omega).ge,
      fun x hx y hy => hAllAdj y hy x (hXsub hx)⟩
  | succ s ih =>
    intro V _ _ G _ A B A_cur collected hAB hBip hAcur hCsub hCard hSum hAllAdj
    -- Restrict G to edges within A_cur ∪ (B \ collected) for bipartiteness
    let B_cur : Finset V := B \ collected
    let Sbip : Finset V := A_cur ∪ B_cur
    let G' : SimpleGraph V :=
      { Adj := fun u v => G.Adj u v ∧ u ∈ Sbip ∧ v ∈ Sbip
        symm := fun _ _ h => ⟨G.symm h.1, h.2.2, h.2.1⟩
        loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩ }
    haveI : DecidableRel G'.Adj := fun u v => inferInstance
    have hDisj' : Disjoint A_cur B_cur := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      exact Finset.disjoint_left.mp hAB (hAcur hx1) (Finset.mem_sdiff.mp hx2).1
    have hBip' : ∀ u v, G'.Adj u v →
        (u ∈ A_cur ∧ v ∈ B_cur) ∨ (u ∈ B_cur ∧ v ∈ A_cur) := by
      intro u v ⟨hAdj, huS, hvS⟩
      rcases hBip u v hAdj with ⟨huA, hvB⟩ | ⟨huB, hvA⟩
      · left; constructor
        · rcases Finset.mem_union.mp huS with h | h
          · exact h
          · exact absurd (Finset.mem_sdiff.mp h).1 (Finset.disjoint_left.mp hAB huA)
        · rcases Finset.mem_union.mp hvS with h | h
          · exact absurd hvB (Finset.disjoint_left.mp hAB (hAcur h))
          · exact h
      · right; constructor
        · rcases Finset.mem_union.mp huS with h | h
          · exact absurd huB (Finset.disjoint_left.mp hAB (hAcur h))
          · exact h
        · rcases Finset.mem_union.mp hvS with h | h
          · exact h
          · exact absurd (Finset.mem_sdiff.mp h).1 (Finset.disjoint_left.mp hAB hvA)
    -- Apply BipartiteRamsey to G' with A_cur, B_cur
    rcases (bipartite_ramsey m t (R_star s t m)).choose_spec
      G' A_cur B_cur hDisj' hBip' hCard with
      ⟨A', hA'sub, hA'card, hA'pair⟩ | ⟨M, hMrange⟩ | ⟨v, hvBcur, hvdeg⟩
    · -- Outcome (a): no common G'-neighbor → (a) with S = collected
      left
      refine ⟨A', collected, hA'sub.trans hAcur, hCsub, hA'card, by omega, ?_⟩
      intro u hu v hv huv w hw ⟨huw, hvw⟩
      have huAcur : u ∈ A_cur := hA'sub hu
      have hvAcur : v ∈ A_cur := hA'sub hv
      have hwB : w ∈ B := by
        rcases hBip u w huw with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h (Finset.disjoint_left.mp hAB (hAcur huAcur))
      have hwBcur : w ∈ B_cur :=
        Finset.mem_sdiff.mpr ⟨hwB, fun h => hw (Finset.mem_coe.mpr h)⟩
      exact hA'pair hu hv huv w
        ⟨⟨huw, Finset.mem_union.mpr (Or.inl huAcur), Finset.mem_union.mpr (Or.inr hwBcur)⟩,
         ⟨hvw, Finset.mem_union.mpr (Or.inl hvAcur), Finset.mem_union.mpr (Or.inr hwBcur)⟩⟩
    · -- Outcome (b): pass the topological minor through unchanged
      right; left
      exact ⟨topologicalMinorModel_of_subgraph M (fun {u v} h => h.1),
        hMrange.trans (Finset.coe_subset.mpr hAcur)⟩
    · -- Outcome (c): high-degree vertex in B_cur → iterate
      have hvB := (Finset.mem_sdiff.mp hvBcur).1
      have hvNotColl := (Finset.mem_sdiff.mp hvBcur).2
      let A_next := A_cur.filter (G.Adj v ·)
      have hAnextCard : R_star s t m ≤ A_next.card := by
        apply le_trans hvdeg
        apply Finset.card_le_card
        intro w hw
        rw [Finset.mem_inter] at hw
        rw [Finset.mem_filter]
        exact ⟨hw.2, (G'.mem_neighborFinset v w |>.mp hw.1).1⟩
      exact ih G A B A_next (insert v collected)
        hAB hBip
        ((Finset.filter_subset _ _).trans hAcur)
        (Finset.insert_subset_iff.mpr ⟨hvB, hCsub⟩)
        hAnextCard
        (by rw [Finset.card_insert_of_notMem hvNotColl]; omega)
        (fun w hw u hu => by
          rcases Finset.mem_insert.mp hw with rfl | hw'
          · exact G.symm (Finset.mem_filter.mp hu).2
          · exact hAllAdj w hw' u (Finset.filter_subset _ _ hu))

/-- Lemma 3.10: iterative version of bipartite Ramsey. In a bipartite graph with
    sides `A` and `B`, if `|A|` is large enough, then at least one of:
    (a) `A` contains `m` vertices and `B` contains a small separator `S` of size
        `< t` such that no two vertices of `A'` have a common neighbor outside `S`,
    (b) `G` contains a `1`-subdivision of `K_t` with principal vertices in `A`,
    (c) `G` contains a complete bipartite subgraph `K_{t,t}`. -/
theorem iterated_bipartite_ramsey (m t : ℕ) :
    ∃ N : ℕ, ∀ {V : Type} [DecidableEq V] [Fintype V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (A B : Finset V),
      Disjoint A B →
      (∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) →
      N ≤ A.card →
      (∃ (A' : Finset V) (S : Finset V),
        A' ⊆ A ∧ S ⊆ B ∧ m ≤ A'.card ∧ S.card < t ∧
        (↑A' : Set V).Pairwise (fun u v =>
          ∀ w, w ∉ (S : Set V) → ¬(G.Adj u w ∧ G.Adj v w))) ∨
      (∃ M : ShallowTopologicalMinorModel
          (SimpleGraph.completeGraph (Fin t)) G 1,
        Set.range M.branchVertex ⊆ ↑A) ∨
      (∃ (X : Finset V) (Y : Finset V),
        X ⊆ A ∧ Y ⊆ B ∧ t ≤ X.card ∧ t ≤ Y.card ∧
        ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) := by
  exact ⟨R_star t t m, fun {V} [_] [_] G [_] A B hAB hBip hCard =>
    iterStep m t t G A B A ∅ hAB hBip Finset.Subset.rfl (Finset.empty_subset _)
      hCard (by simp) (fun _ h => absurd h (Finset.notMem_empty _))⟩

end Lax5Proofs.BipartiteRamsey
