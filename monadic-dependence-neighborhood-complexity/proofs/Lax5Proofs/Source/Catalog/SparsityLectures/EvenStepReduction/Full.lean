import Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.UniformQuasiWideness.Full

namespace Lax5Proofs.Source.Catalog.SparsityLectures.EvenStepReduction

open Lax5Proofs.Source.Catalog.SparsityLectures.ShallowMinor Lax5Proofs.Source.Catalog.SparsityLectures.UniformQuasiWideness

-- ── Helpers ─────────────────────────────────────────────────────────────

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

/-- Map a walk in `deleteVerts G S` to a walk in `G` of the same length. -/
private def toGWalk {V : Type} {G : SimpleGraph V} {S : Set V}
    {u v : V} (p : (deleteVerts G S).Walk u v) : G.Walk u v :=
  p.map { toFun := id, map_rel' := fun {_ _} h => And.left h }

@[simp] private lemma toGWalk_length {V : Type} {G : SimpleGraph V} {S : Set V}
    {u v : V} (p : (deleteVerts G S).Walk u v) : (toGWalk p).length = p.length :=
  SimpleGraph.Walk.length_map _ _

-- ── Main theorem ────────────────────────────────────────────────────────

theorem evenStepReduction {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (j : ℕ) (A : Finset V)
    (hA : DistIndependent G (2 * j + 1) ↑A) :
    ∃ (W : Type) (_ : DecidableEq W) (_ : Fintype W) (H : SimpleGraph W)
      (AW : Finset W),
      IsShallowMinor H G j ∧
      A.card ≤ AW.card ∧
      (↑AW : Set W).Pairwise (fun u v => ¬H.Adj u v) ∧
      (∀ (S : Finset W) (m : ℕ),
        Disjoint S AW →
        (∃ B : Finset W, B ⊆ AW ∧ m ≤ B.card ∧
          DistIndependent (deleteVerts H ↑S) 2 ↑B) →
        ∃ (S' : Finset V) (B' : Finset V),
          S'.card ≤ S.card ∧ ↑B' ⊆ ↑A ∧ Disjoint B' S' ∧ m ≤ B'.card ∧
          DistIndependent (deleteVerts G ↑S') (2 * (j + 1)) ↑B') := by
  classical
  have hA2j : DistIndependent G (2 * j) ↑A :=
    fun a ha b hb hab p => Nat.lt_of_le_of_lt (by omega) (hA ha hb hab p)
  set W := {v : V // v ∈ A ∨ ∀ a ∈ A, v ∉ jBall G j a} with hW_def
  let branchOf : W → Set V := fun w =>
    if w.val ∈ A then jBall G j w.val else {w.val}
  let H : SimpleGraph W :=
    { Adj := fun w₁ w₂ => w₁ ≠ w₂ ∧
        ∃ x ∈ branchOf w₁, ∃ y ∈ branchOf w₂, G.Adj x y
      symm := fun _ _ ⟨hne, x, hx, y, hy, hadj⟩ =>
        ⟨hne.symm, y, hy, x, hx, hadj.symm⟩
      loopless := ⟨fun w h => h.1 rfl⟩ }
  let aEmb : {v // v ∈ A} ↪ W :=
    { toFun := fun ⟨v, hv⟩ => ⟨v, Or.inl hv⟩
      inj' := fun a b h => Subtype.ext (congrArg (fun w : W => w.val) h) }
  set AW := Finset.univ.map aEmb with hAW_def
  have hAW_mem : ∀ w ∈ AW, w.val ∈ A := by
    intro w hw; obtain ⟨⟨v, hv⟩, _, rfl⟩ := Finset.mem_map.mp hw; exact hv
  have hA_to_AW : ∀ (a : V) (ha : a ∈ A), (⟨a, Or.inl ha⟩ : W) ∈ AW := by
    intro a ha; exact Finset.mem_map.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩
  have hOut : ∀ w : W, w.val ∉ A → ∀ a ∈ A, w.val ∉ jBall G j a := by
    intro w hw; rcases w.prop with h | h; exact absurd h hw; exact h
  have hBrA : ∀ w : W, w.val ∈ A → branchOf w = jBall G j w.val :=
    fun _ h => if_pos h
  have hBrOut : ∀ w : W, w.val ∉ A → branchOf w = {w.val} :=
    fun _ h => if_neg h
  refine ⟨W, inferInstance, inferInstance, H, AW, ?_, ?_, ?_, ?_⟩
  -- ── (1) IsShallowMinor H G j ──
  · refine ⟨⟨branchOf, fun w => w.val, fun w => ?_, fun u v huv => ?_,
        fun w x hx => ?_, fun u v hadj => hadj.2⟩⟩
    · -- center_mem
      by_cases hw : w.val ∈ A
      · rw [hBrA w hw]; exact mem_jBall_self G j w.val
      · simp only [hBrOut w hw, Set.mem_singleton_iff]
    · -- branchDisjoint
      by_cases hu : u.val ∈ A <;> by_cases hv : v.val ∈ A
      · rw [hBrA u hu, hBrA v hv]
        exact jBall_disjoint hA2j hu hv (Subtype.val_injective.ne huv)
      · rw [hBrA u hu, hBrOut v hv]
        exact Set.disjoint_left.mpr fun x hx (hxv : x = v.val) =>
          hOut v hv u.val hu (hxv ▸ hx)
      · rw [hBrOut u hu, hBrA v hv]
        exact Set.disjoint_left.mpr fun x (hx : x = u.val) hxv =>
          hOut u hu v.val hv (hx ▸ hxv)
      · rw [hBrOut u hu, hBrOut v hv]
        exact Set.disjoint_left.mpr fun x (hx : x = u.val) (hxv : x = v.val) =>
          huv (Subtype.ext (hx.symm.trans hxv))
    · -- branchRadius
      by_cases hw : w.val ∈ A
      · rw [hBrA w hw] at hx ⊢
        obtain ⟨q, hq⟩ := hx
        exact ⟨q.bypass, q.bypass_isPath, q.length_bypass_le.trans hq,
          fun z hz => ⟨q.takeUntil z (q.support_bypass_subset hz),
            (q.length_takeUntil_le (q.support_bypass_subset hz)).trans hq⟩⟩
      · rw [hBrOut w hw] at hx ⊢
        subst hx
        exact ⟨.nil, SimpleGraph.Walk.IsPath.nil, Nat.zero_le _,
          fun z hz => by
            simp [SimpleGraph.Walk.support_nil] at hz; exact hz⟩
  -- ── (2) A.card ≤ AW.card ──
  · rw [hAW_def, Finset.card_map, Finset.card_univ, Fintype.card_coe]
  -- ── (3) AW is independent in H ──
  · intro wa hwa wb hwb hwne hadj
    obtain ⟨_, x, hx, y, hy, hxy⟩ := hadj
    have hwa_A := hAW_mem wa hwa; have hwb_A := hAW_mem wb hwb
    rw [hBrA wa hwa_A] at hx; rw [hBrA wb hwb_A] at hy
    obtain ⟨px, hpx⟩ := hx; obtain ⟨py, hpy⟩ := hy
    exact absurd (show (px.append (.cons hxy py.reverse)).length ≤ 2 * j + 1 by
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
          SimpleGraph.Walk.length_reverse]; omega)
      (Nat.not_le.mpr (hA hwa_A hwb_A (Subtype.val_injective.ne hwne) _))
  -- ── (4) Lifting property ──
  · intro S m hDisj ⟨B, hBsub, hmB, hBind⟩
    let valEmb : W ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
    refine ⟨S.map valEmb, B.map valEmb, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_map]
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      exact hAW_mem w (hBsub hw)
    · rw [Finset.disjoint_left]; intro v hv hv'
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨w', hw', heq⟩ := Finset.mem_map.mp hv'
      have := Subtype.val_injective heq; subst this
      exact Finset.disjoint_right.mp hDisj (hBsub hw) hw'
    · rw [Finset.card_map]; exact hmB
    · intro a ha b hb hab
      simp only [Finset.coe_map, Set.mem_image] at ha hb
      obtain ⟨wa, hwa_mem, rfl⟩ := ha
      obtain ⟨wb, hwb_mem, rfl⟩ := hb
      have hwne : wa ≠ wb := fun h => hab (congrArg Subtype.val h)
      have hwa_A := hAW_mem wa (hBsub hwa_mem)
      have hwb_A := hAW_mem wb (hBsub hwb_mem)
      have hwa_nS : wa ∉ (S : Set W) :=
        fun h => Finset.disjoint_right.mp hDisj (hBsub hwa_mem) h
      have hwb_nS : wb ∉ (S : Set W) :=
        fun h => Finset.disjoint_right.mp hDisj (hBsub hwb_mem) h
      set S' := S.map valEmb
      intro p
      by_contra hle; push_neg at hle
      -- Lower bound from hA
      have hp_lb : 2 * j + 2 ≤ p.length := by
        have := hA hwa_A hwb_A (Subtype.val_injective.ne hwne) (toGWalk p)
        simp at this; omega
      -- Apply walk_crossing_edge to p (deleteVerts walk) at depth j
      obtain ⟨c, d, hadj_del, ⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩⟩ :=
        walk_crossing_edge p j (by omega : j + 1 ≤ p.length)
      have hadj_cd : G.Adj c d := hadj_del.1
      have hd_nS' : d ∉ (↑S' : Set V) := hadj_del.2.2
      have hc_ball : c ∈ jBall G j wa.val :=
        ⟨toGWalk q₁, by simp; exact hq₁⟩
      have hq₂_le : q₂.length ≤ j + 1 := by omega
      by_cases hq₂j : q₂.length ≤ j
      · -- Case 1: d ∈ jBall(wb, j) → length-1 H-walk → contradiction
        have hd_ball : d ∈ jBall G j wb.val :=
          ⟨(toGWalk q₂).reverse, by simp; exact hq₂j⟩
        have hH_adj : H.Adj wa wb :=
          ⟨hwne,
           c, show c ∈ branchOf wa by rw [hBrA wa hwa_A]; exact hc_ball,
           d, show d ∈ branchOf wb by rw [hBrA wb hwb_A]; exact hd_ball,
           hadj_cd⟩
        exact absurd (hBind (Finset.mem_coe.mpr hwa_mem) (Finset.mem_coe.mpr hwb_mem)
          hwne (.cons (show (deleteVerts H ↑S).Adj wa wb from ⟨hH_adj, hwa_nS, hwb_nS⟩) .nil))
          (by simp [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil])
      · -- Case 2: q₂.length = j+1 → d outside all jBalls → H-path wa-wd-wb
        push_neg at hq₂j
        have hq₂_eq : q₂.length = j + 1 := by omega
        have hd_outside : ∀ a' ∈ A, d ∉ jBall G j a' := by
          intro a' ha' ⟨pd, hpd⟩
          by_cases haa : wa.val = a'
          · -- d ∈ jBall(wa.val, j). Walk wa.val→d (pd), d→wb.val (q₂). Total ≤ 2j+1.
            subst haa
            have := hA hwa_A hwb_A (Subtype.val_injective.ne hwne)
              (pd.append (toGWalk q₂))
            simp [SimpleGraph.Walk.length_append] at this; omega
          · -- Walk wa.val→c (q₁), edge c→d, walk d→a' (pd.reverse). Total ≤ 2j+1.
            have := hA hwa_A ha' haa
              ((toGWalk q₁).append (.cons hadj_cd pd.reverse))
            simp [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
                SimpleGraph.Walk.length_reverse] at this; omega
        have hd_notA : d ∉ A := fun hd => hd_outside d hd (mem_jBall_self G j d)
        let wd : W := ⟨d, Or.inr hd_outside⟩
        have hwd_nS : wd ∉ (S : Set W) := by
          intro hs
          exact hd_nS' (Finset.mem_coe.mpr
            (Finset.mem_map.mpr ⟨wd, Finset.mem_coe.mp hs, rfl⟩))
        have hH_wa_wd : H.Adj wa wd := by
          refine ⟨fun h => ?_, c, ?_, d, ?_, hadj_cd⟩
          · subst h; exact hd_notA hwa_A
          · rw [hBrA wa hwa_A]; exact hc_ball
          · simp only [hBrOut wd hd_notA, Set.mem_singleton_iff]; rfl
        have hH_wd_wb : H.Adj wd wb := by
          refine ⟨fun h => ?_, d, ?_, ?_⟩
          · subst h; exact hd_notA hwb_A
          · simp only [hBrOut wd hd_notA, Set.mem_singleton_iff]; rfl
          · -- q₂ has length j+1 ≥ 1, extract first step
            match q₂, hq₂_eq with
            | .cons hedge q₂', hlen =>
              refine ⟨_, ?_, hedge.left⟩
              rw [hBrA wb hwb_A]
              exact ⟨(toGWalk q₂').reverse, by
                simp [SimpleGraph.Walk.length_cons] at hlen; simp; omega⟩
        -- length-2 walk wa → wd → wb in deleteVerts H ↑S → contradiction
        exact absurd (hBind (Finset.mem_coe.mpr hwa_mem) (Finset.mem_coe.mpr hwb_mem)
          hwne (.cons ⟨hH_wa_wd, hwa_nS, hwd_nS⟩ (.cons ⟨hH_wd_wb, hwd_nS, hwb_nS⟩ .nil)))
          (by simp [SimpleGraph.Walk.length_cons])

end Lax5Proofs.Source.Catalog.SparsityLectures.EvenStepReduction
