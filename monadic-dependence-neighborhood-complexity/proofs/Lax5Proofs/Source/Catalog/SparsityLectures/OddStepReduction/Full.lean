import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.UniformQuasiWideness.Full

namespace Lax5Proofs.Source.Catalog.SparsityLectures.OddStepReduction

open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor Lax5Proofs.Source.Catalog.SparsityLectures.UniformQuasiWideness

/-- The j-ball of `v` in `G`: vertices reachable by a walk of length ≤ j. -/
private def jBall {V : Type} (G : SimpleGraph V) (j : ℕ) (v : V) : Set V :=
  {u : V | ∃ p : G.Walk v u, p.length ≤ j}

private lemma mem_jBall_self {V : Type} (G : SimpleGraph V) (j : ℕ) (v : V) :
    v ∈ jBall G j v :=
  ⟨.nil, Nat.zero_le _⟩

private lemma jBall_disjoint {V : Type} {G : SimpleGraph V} [DecidableEq V] {j : ℕ}
    {A : Set V} (hA : DistIndependent G (2 * j) A) {a b : V} (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) : Disjoint (jBall G j a) (jBall G j b) :=
  Set.disjoint_left.mpr fun u ⟨pa, hpa⟩ ⟨pb, hpb⟩ =>
    absurd (show (pa.append pb.reverse).length ≤ 2 * j by
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]; omega)
    (Nat.not_le.mpr (hA ha hb hab _))

/-- In a walk of length ≥ j+1, there is an edge at depth j: vertices c, d with
    G.Adj c d, a walk from start to c of length ≤ j, and a walk from d to end
    of length ≤ p.length − j − 1. -/
private lemma walk_crossing_edge {V : Type} {G : SimpleGraph V} [DecidableEq V]
    {u v : V} (p : G.Walk u v) (j : ℕ) (hj : j + 1 ≤ p.length) :
    ∃ c d : V, G.Adj c d ∧
      (∃ q₁ : G.Walk u c, q₁.length ≤ j) ∧
      (∃ q₂ : G.Walk d v, q₂.length + j + 1 ≤ p.length) := by
  induction p generalizing j with
  | nil => simp [SimpleGraph.Walk.length_nil] at hj
  | cons h p' ih =>
    match j with
    | 0 =>
      exact ⟨_, _, h, ⟨.nil, le_refl 0⟩,
        ⟨p', by simp [SimpleGraph.Walk.length_cons]⟩⟩
    | j + 1 =>
      have hj' : j + 1 ≤ p'.length := by
        simp [SimpleGraph.Walk.length_cons] at hj; omega
      obtain ⟨c, d, hadj, ⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩⟩ := ih j hj'
      exact ⟨c, d, hadj,
        ⟨.cons h q₁, by simp [SimpleGraph.Walk.length_cons]; omega⟩,
        ⟨q₂, by simp [SimpleGraph.Walk.length_cons]; omega⟩⟩

/-- Lemma 3.5 (consequence form): given a distance-`2j` independent set `A` in
    `G`, there exists a depth-`j` minor `H` of `G` such that any independent
    set of size `m` in `H` lifts to a distance-`(2j+1)` independent subset of
    `A` of the same size.

    The full statement is an iff (distance-`(2j+1)` independence in `G` ↔
    distance-`1` independence in `H`), but the consequence form suffices for
    the densification argument. -/
theorem oddStepReduction {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (j : ℕ) (A : Finset V)
    (hA : DistIndependent G (2 * j) ↑A) :
    ∃ (W : Type) (_ : DecidableEq W) (_ : Fintype W) (H : SimpleGraph W),
      IsShallowMinor H G j ∧
      A.card ≤ Fintype.card W ∧
      (∀ m : ℕ, (∃ B : Finset W, m ≤ B.card ∧ DistIndependent H 1 ↑B) →
        ∃ B' : Finset V, ↑B' ⊆ ↑A ∧ m ≤ B'.card ∧
          DistIndependent G (2 * j + 1) ↑B') := by
  -- W = subtype of A
  set W := {v : V // v ∈ A} with hW_def
  -- Define H: vertices of A are adjacent in H iff their j-balls have a G-edge between them
  let H : SimpleGraph W :=
    { Adj := fun w₁ w₂ => w₁ ≠ w₂ ∧
        ∃ x ∈ jBall G j w₁.val, ∃ y ∈ jBall G j w₂.val, G.Adj x y
      symm := fun _ _ ⟨hne, x, hx, y, hy, hadj⟩ =>
        ⟨hne.symm, y, hy, x, hx, hadj.symm⟩
      loopless := ⟨fun w h => h.1 rfl⟩ }
  refine ⟨W, inferInstance, inferInstance, H, ?_, ?_, ?_⟩
  -- (1) IsShallowMinor H G j
  · exact ⟨{
      branchSet := fun w => jBall G j w.val
      center := fun w => w.val
      center_mem := fun w => mem_jBall_self G j w.val
      branchDisjoint := fun u v huv =>
        jBall_disjoint hA u.prop v.prop (Subtype.val_injective.ne huv)
      branchRadius := fun w x hx => by
        obtain ⟨q, hq⟩ := hx
        exact ⟨q.bypass, q.bypass_isPath, q.length_bypass_le.trans hq,
          fun z hz => ⟨q.takeUntil z (q.support_bypass_subset hz),
            (q.length_takeUntil_le (q.support_bypass_subset hz)).trans hq⟩⟩
      branchEdge := fun u v hadj => hadj.2
    }⟩
  -- (2) A.card ≤ Fintype.card W
  · exact le_of_eq (Fintype.card_coe A).symm
  -- (3) Lifting property
  · intro m ⟨B, hmB, hBind⟩
    refine ⟨B.map ⟨Subtype.val, Subtype.val_injective⟩, ?_, ?_, ?_⟩
    -- B' ⊆ A
    · intro v hv
      obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hv
      exact w.prop
    -- m ≤ B'.card
    · rw [Finset.card_map]; exact hmB
    -- DistIndependent G (2 * j + 1) B'
    · intro a ha b hb hab
      simp only [Finset.coe_map, Set.mem_image, Function.Embedding.coeFn_mk] at ha hb
      obtain ⟨wa, hwa_mem, rfl⟩ := ha
      obtain ⟨wb, hwb_mem, rfl⟩ := hb
      have hwne : wa ≠ wb := fun h => hab (congrArg Subtype.val h)
      -- wa, wb not adjacent in H (from distance-1 independence of B)
      have hnadj : ¬H.Adj wa wb := by
        intro hadj
        have := hBind (Finset.mem_coe.mpr hwa_mem) (Finset.mem_coe.mpr hwb_mem)
          hwne (.cons hadj .nil)
        simp [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at this
      -- Extract: no G-edge between the j-balls
      have hno_edge : ∀ x ∈ jBall G j wa.val, ∀ y ∈ jBall G j wb.val, ¬G.Adj x y := by
        intro x hx y hy hadj_xy
        exact hnadj ⟨hwne, x, hx, y, hy, hadj_xy⟩
      -- Show any walk has length > 2j + 1
      intro p
      by_contra hle
      push_neg at hle
      by_cases hshort : j + 1 ≤ p.length
      · -- Use crossing edge at depth j
        obtain ⟨c, d, hadj_cd, ⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩⟩ := walk_crossing_edge p j hshort
        exact hno_edge c ⟨q₁, hq₁⟩ d
          ⟨q₂.reverse, by rw [SimpleGraph.Walk.length_reverse]; omega⟩ hadj_cd
      · -- Walk length ≤ j ≤ 2j, contradicts distance-2j independence
        push_neg at hshort
        exact absurd (hA wa.prop wb.prop (Subtype.val_injective.ne hwne) p) (by omega)

end Lax5Proofs.Source.Catalog.SparsityLectures.OddStepReduction
