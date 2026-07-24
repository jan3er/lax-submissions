import Mathlib.Tactic
import Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.StrongColoringBoundByAdm.TreeCounting

open Classical

namespace Lax5Proofs.Source.Catalog.SparsityLectures.StrongColoringBoundByAdm

noncomputable section

variable {V : Type*} [DecidableEq V] [Fintype V] [LinearOrder V]

open Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility
open Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers

/-- Every vertex is in its own strong r-reachability set. -/
private theorem self_mem_sreach (G : SimpleGraph V) (r : ℕ) (v : V) :
    v ∈ SReach G r v := by
  refine ⟨le_rfl, ⟨.nil, ?_⟩⟩
  simp

/-- Per-vertex admissibility is at most the global admissibility. -/
private theorem admVertex_le_adm (G : SimpleGraph V) (r : ℕ) (v : V) :
    admVertex G r v ≤ adm G r := by
  unfold adm
  exact Finset.le_sup (f := fun w => admVertex G r w) (by simp)

private theorem sreach_predecessor (G : SimpleGraph V) (r : ℕ) (v u : V)
    (hu : u ∈ SReach G r v) (hne : u ≠ v) :
    u < v ∧ ∃ (u' : V) (p : G.Walk v u'),
      v ≤ u' ∧ G.Adj u' u ∧
      (∀ x ∈ p.support, v ≤ x) ∧ p.length + 1 ≤ r := by
  rcases hu with ⟨hu_le, p, hp_path, hp_len, hp_internal⟩
  have hu_lt : u < v := lt_of_le_of_ne hu_le hne
  have hp_not_nil : ¬ p.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq]
    intro hp_zero
    apply hne
    have huv : v = u := by
      have hv : v = p.getVert p.length := by
        simpa [hp_zero] using p.getVert_zero.symm
      exact hv.trans p.getVert_length
    exact huv.symm
  refine ⟨hu_lt, p.penultimate, p.dropLast, ?_⟩
  refine ⟨?_, p.adj_penultimate hp_not_nil, ?_, ?_⟩
  · by_cases hlen : p.length = 1
    · simp [SimpleGraph.Walk.penultimate, hlen]
    · have hpos : 0 < p.length := Nat.pos_of_ne_zero fun hzero =>
        hp_not_nil (SimpleGraph.Walk.nil_iff_length_eq.mpr hzero)
      have hlt : p.length - 1 < p.length := Nat.sub_lt hpos (by decide)
      exact le_of_lt (hp_internal (p.length - 1) (by omega) hlt)
  · intro x hx
    rcases (SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx) with ⟨n, rfl, hnle⟩
    have hdrop_len : p.dropLast.length = p.length - 1 := by
      simp [SimpleGraph.Walk.dropLast, SimpleGraph.Walk.take_length]
    have htake : p.dropLast.getVert n = p.getVert n := by
      rw [SimpleGraph.Walk.dropLast, SimpleGraph.Walk.take_getVert]
      simp [hdrop_len] at hnle
      simp [Nat.min_eq_right hnle]
    rw [htake]
    by_cases hn : n = 0
    · simp [hn]
    · have hdrop_len' : n ≤ p.length - 1 := by
        simpa [hdrop_len] using hnle
      have hlt : n < p.length := by omega
      exact le_of_lt (hp_internal n (Nat.pos_of_ne_zero hn) hlt)
  · have hlen_drop : p.dropLast.length = p.length - 1 := by
      simp [SimpleGraph.Walk.dropLast, SimpleGraph.Walk.take_length]
    have hpos : 0 < p.length := Nat.pos_of_ne_zero fun hzero =>
      hp_not_nil (SimpleGraph.Walk.nil_iff_length_eq.mpr hzero)
    rw [hlen_drop]
    have hsub : p.length - 1 + 1 = p.length := by
      omega
    rw [hsub]
    exact hp_len

private theorem iterate_root_eq {α : Type*} (par : α → α) {v : α} (hpar_root : par v = v) :
    ∀ m, par^[m] v = v := by
  intro m
  induction m with
  | zero => rfl
  | succ m ihm =>
      rw [Function.iterate_succ_apply]
      simp [hpar_root, ihm]

private theorem above_v_bfs_data (G : SimpleGraph V) (r : ℕ) (v : V) :
    ∃ (d : V → ℕ) (bp : V → V),
      d v = 0 ∧ bp v = v ∧
      (∀ w, v ≤ w → d w ≤ r → w ≠ v →
        v ≤ bp w ∧ G.Adj (bp w) w ∧ d (bp w) + 1 = d w) ∧
      (∀ w (p : G.Walk v w), (∀ x ∈ p.support, v ≤ x) → p.length ≤ r →
        d w ≤ p.length) ∧
      (∀ w, v ≤ w → d w ≤ r →
        ∃ p : G.Walk v w, (∀ x ∈ p.support, v ≤ x) ∧ p.length = d w) := by
  let Good : V → ℕ → Prop := fun w n =>
    ∃ p : G.Walk v w, (∀ x ∈ p.support, v ≤ x) ∧ p.length = n
  let d : V → ℕ := fun w =>
    if h : ∃ n, n ≤ r ∧ Good w n then Nat.find h else r + 1
  have hd_lower : ∀ w (p : G.Walk v w), (∀ x ∈ p.support, v ≤ x) → p.length ≤ r →
      d w ≤ p.length := by
    intro w p hp_support hp_len
    have hgood : ∃ n, n ≤ r ∧ Good w n := ⟨p.length, hp_len, p, hp_support, rfl⟩
    change (if h : ∃ n, n ≤ r ∧ Good w n then Nat.find h else r + 1) ≤ p.length
    rw [dif_pos hgood]
    exact Nat.find_min' hgood ⟨hp_len, p, hp_support, rfl⟩
  have hd_achieve : ∀ w, v ≤ w → d w ≤ r →
      ∃ p : G.Walk v w, (∀ x ∈ p.support, v ≤ x) ∧ p.length = d w := by
    intro w hwv hdwr
    by_cases hgood : ∃ n, n ≤ r ∧ Good w n
    · have hspec := Nat.find_spec hgood
      rcases hspec with ⟨_, p, hp_support, hp_len⟩
      refine ⟨p, hp_support, ?_⟩
      simpa [d, hgood] using hp_len
    · exfalso
      have : r + 1 ≤ r := by
        simp [d, hgood] at hdwr
      omega
  have hd_v : d v = 0 := by
    have hgood : ∃ n, n ≤ r ∧ Good v n :=
      ⟨0, Nat.zero_le _, SimpleGraph.Walk.nil, by simp, rfl⟩
    have hmin : Nat.find hgood ≤ 0 :=
      Nat.find_min' hgood ⟨Nat.zero_le _, SimpleGraph.Walk.nil, by simp, rfl⟩
    change (if h : ∃ n, n ≤ r ∧ Good v n then Nat.find h else r + 1) = 0
    rw [dif_pos hgood]
    exact le_antisymm hmin (Nat.zero_le _)
  let bp : V → V := fun w =>
    if hw : v ≤ w ∧ d w ≤ r ∧ w ≠ v then
      let p := Classical.choose (hd_achieve w hw.1 hw.2.1)
      p.penultimate
    else v
  refine ⟨d, bp, hd_v, ?_, ?_, hd_lower, hd_achieve⟩
  · simp [bp, hd_v]
  · intro w hwv hdwr hwne
    let p : G.Walk v w := Classical.choose (hd_achieve w hwv hdwr)
    have hp_support : ∀ x ∈ p.support, v ≤ x :=
      (Classical.choose_spec (hd_achieve w hwv hdwr)).1
    have hp_len : p.length = d w :=
      (Classical.choose_spec (hd_achieve w hwv hdwr)).2
    have hp_not_nil : ¬ p.Nil := by
      rw [SimpleGraph.Walk.nil_iff_length_eq]
      intro hp_zero
      apply hwne
      have hvw : v = w := by
        have hv : v = p.getVert p.length := by
          simpa [hp_zero] using p.getVert_zero.symm
        exact hv.trans p.getVert_length
      exact hvw.symm
    have hbp_eq : bp w = p.penultimate := by
      simp [bp, hwv, hdwr, hwne, p]
    have hbp_ge : v ≤ bp w := by
      rw [hbp_eq]
      exact hp_support _ (p.getVert_mem_support (p.length - 1))
    have hbp_adj : G.Adj (bp w) w := by
      rw [hbp_eq]
      exact p.adj_penultimate hp_not_nil
    have hdrop_support : ∀ x ∈ p.dropLast.support, v ≤ x := by
      intro x hx
      have hx' : x ∈ p.support := by
        rw [SimpleGraph.Walk.dropLast, SimpleGraph.Walk.take_support_eq_support_take_succ] at hx
        exact List.mem_of_mem_take hx
      exact hp_support x hx'
    have hdrop_len : p.dropLast.length = d w - 1 := by
      rw [SimpleGraph.Walk.dropLast, SimpleGraph.Walk.take_length, hp_len,
        Nat.min_eq_left (Nat.sub_le _ _)]
    have hdw_pos : 0 < d w := by
      rw [← hp_len]
      exact Nat.pos_of_ne_zero fun hzero =>
        hp_not_nil (SimpleGraph.Walk.nil_iff_length_eq.mpr hzero)
    have hd_pred_len : d p.penultimate ≤ p.dropLast.length := by
      exact hd_lower (w := p.penultimate) (p := p.dropLast) hdrop_support
        (by
          rw [hdrop_len]
          exact le_trans (Nat.sub_le _ _) hdwr)
    have hd_pred_le : d (bp w) ≤ d w - 1 := by
      rw [hbp_eq]
      rw [hdrop_len] at hd_pred_len
      exact hd_pred_len
    have hd_pred_succ_le : d (bp w) + 1 ≤ d w := by
      omega
    have hd_pred_le_r : d (bp w) ≤ r := by
      exact le_trans (Nat.le_of_lt (Nat.lt_of_succ_le hd_pred_succ_le)) hdwr
    obtain ⟨q, hq_support, hq_len⟩ := hd_achieve (bp w) hbp_ge hd_pred_le_r
    have hconcat_support : ∀ x ∈ (q.concat hbp_adj).support, v ≤ x := by
      intro x hx
      have hx' : x ∈ q.support ∨ x = w := by
        simpa [SimpleGraph.Walk.support_concat] using hx
      rcases hx' with hxq | rfl
      · exact hq_support x hxq
      · exact hwv
    have hdw_len : d w ≤ (q.concat hbp_adj).length := by
      have hq_concat_len : (q.concat hbp_adj).length ≤ r := by
        rw [SimpleGraph.Walk.length_concat, hq_len]
        exact le_trans hd_pred_succ_le hdwr
      exact hd_lower (w := w) (p := q.concat hbp_adj) hconcat_support hq_concat_len
    have hdw_le : d w ≤ d (bp w) + 1 := by
      simpa [SimpleGraph.Walk.length_concat, hq_len] using hdw_len
    refine ⟨hbp_ge, hbp_adj, ?_⟩
    exact le_antisymm hd_pred_succ_le hdw_le

private theorem exists_walk_to_descendant
    (G : SimpleGraph V) (v : V)
    (S : Finset V) (par : V → V) (dep : V → ℕ)
    (hpar_root : par v = v)
    (hpar_mem : ∀ a ∈ S, par a ∈ S)
    (hpar_dep : ∀ a ∈ S, a ≠ v → dep (par a) + 1 = dep a)
    (hadj : ∀ a ∈ S, a ≠ v → G.Adj (par a) a)
    {a x : V} (haS : a ∈ S) (ha_ne_v : a ≠ v) (hxS : x ∈ S) {n : ℕ}
    (hiter : par^[n] x = a) :
    ∃ q : G.Walk a x,
      q.length = n ∧
      dep a + n = dep x ∧
      ∀ y ∈ q.support, y ∈ S ∧ ∃ m, par^[m] y = a := by
  induction n generalizing x with
  | zero =>
      simp only [Function.iterate_zero, id_eq] at hiter
      subst x
      refine ⟨SimpleGraph.Walk.nil, rfl, by simp, ?_⟩
      intro y hy
      simp at hy
      subst y
      exact ⟨haS, ⟨0, by simp⟩⟩
  | succ n ih =>
      have hx_ne_v : x ≠ v := by
        intro hxv
        subst x
        have : a = v := by
          calc
            a = par^[n.succ] v := hiter.symm
            _ = v := iterate_root_eq par hpar_root _
        exact ha_ne_v this
      have hparxS : par x ∈ S := hpar_mem x hxS
      have hiter' : par^[n] (par x) = a := by
        simpa [Function.iterate_succ_apply] using hiter
      obtain ⟨q, hq_len, hq_dep, hq_support⟩ :=
        ih hparxS hiter'
      have hadjx : G.Adj (par x) x := hadj x hxS hx_ne_v
      have hdep_x : dep (par x) + 1 = dep x := hpar_dep x hxS hx_ne_v
      refine ⟨q.concat hadjx, by simp [hq_len], ?_, ?_⟩
      · omega
      · intro y hy
        have hy' : y ∈ q.support ∨ y = x := by
          simpa [SimpleGraph.Walk.support_concat] using hy
        rcases hy' with hyq | rfl
        · exact hq_support y hyq
        · exact ⟨hxS, ⟨n.succ, hiter⟩⟩

private theorem exists_child_leaf_walk
    (G : SimpleGraph V) (r : ℕ) (v : V)
    (S : Finset V) (par : V → V) (dep : V → ℕ)
    (hpar_root : par v = v)
    (hpar_mem : ∀ a ∈ S, par a ∈ S)
    (hpar_dep : ∀ a ∈ S, a ≠ v → dep (par a) + 1 = dep a)
    (hdep_le : ∀ a ∈ S, dep a ≤ r)
    (hadj : ∀ a ∈ S, a ≠ v → G.Adj (par a) a)
    (w c u : V)
    (hc : c ∈ treeChildren S par w)
    (huS : u ∈ S)
    (hdesc : ∃ n, par^[n] u = c) :
    ∃ q : G.Walk w u,
      q.length ≤ r ∧
      ∀ y ∈ q.support, y = w ∨ y ∈ S ∧ ∃ m, par^[m] y = c := by
  rcases Finset.mem_filter.mp hc with ⟨hcS, hchild⟩
  rcases hchild with ⟨hparc, hc_ne_w⟩
  have hc_ne_v : c ≠ v := by
    intro hcv
    subst c
    exact hc_ne_w (hpar_root.symm.trans hparc)
  obtain ⟨n, hn⟩ := hdesc
  obtain ⟨q, hq_len, hq_dep, hq_support⟩ :=
    exists_walk_to_descendant G v S par dep hpar_root hpar_mem hpar_dep hadj
      hcS hc_ne_v huS hn
  have hwc : G.Adj w c := by
    simpa [hparc] using hadj c hcS hc_ne_v
  have hdep_c : dep w + 1 = dep c := by
    simpa [hparc] using hpar_dep c hcS hc_ne_v
  refine ⟨SimpleGraph.Walk.cons hwc q, ?_, ?_⟩
  · have hdep_u := hdep_le u huS
    simp [hq_len]
    omega
  · intro y hy
    have hy' : y = w ∨ y ∈ q.support := by
      simpa [SimpleGraph.Walk.support_cons] using hy
    rcases hy' with rfl | hyq
    · exact Or.inl rfl
    · exact Or.inr (hq_support y hyq)

set_option linter.unusedSectionVars false in
private theorem iterate_depth_eq
    (S : Finset V) (par : V → V) (dep : V → ℕ) (v : V)
    (hpar_root : par v = v)
    (hpar_mem : ∀ a ∈ S, par a ∈ S)
    (hpar_dep : ∀ a ∈ S, a ≠ v → dep (par a) + 1 = dep a)
    {a x : V} (_haS : a ∈ S) (ha_ne_v : a ≠ v) (hxS : x ∈ S) {n : ℕ}
    (hiter : par^[n] x = a) :
    dep a + n = dep x := by
  induction n generalizing x with
  | zero =>
      simp only [Function.iterate_zero, id_eq] at hiter
      subst x
      omega
  | succ n ih =>
      have hx_ne_v : x ≠ v := by
        intro hxv
        subst x
        have : a = v := by
          calc
            a = par^[n.succ] v := hiter.symm
            _ = v := iterate_root_eq par hpar_root _
        exact ha_ne_v this
      have hparxS : par x ∈ S := hpar_mem x hxS
      have hiter' : par^[n] (par x) = a := by
        simpa [Function.iterate_succ_apply] using hiter
      have hdep_x : dep (par x) + 1 = dep x := hpar_dep x hxS hx_ne_v
      have hrec := ih hparxS hiter'
      omega

private theorem descendants_of_distinct_children_disjoint
    (S : Finset V) (par : V → V) (dep : V → ℕ) (v : V)
    (hpar_root : par v = v)
    (hpar_mem : ∀ a ∈ S, par a ∈ S)
    (hpar_dep : ∀ a ∈ S, a ≠ v → dep (par a) + 1 = dep a) :
    ∀ a ∈ S, ∀ c₁ ∈ treeChildren S par a, ∀ c₂ ∈ treeChildren S par a,
      c₁ ≠ c₂ → ∀ x ∈ S, (∃ n, par^[n] x = c₁) → ¬∃ m, par^[m] x = c₂ := by
  intro a haS c₁ hc₁ c₂ hc₂ hc_ne x hxS hx₁ hx₂
  rcases hx₁ with ⟨n, hn⟩
  rcases hx₂ with ⟨m, hm⟩
  have hc₁S : c₁ ∈ S := (Finset.mem_filter.mp hc₁).1
  have hc₂S : c₂ ∈ S := (Finset.mem_filter.mp hc₂).1
  have hpar₁ : par c₁ = a := (Finset.mem_filter.mp hc₁).2.1
  have hpar₂ : par c₂ = a := (Finset.mem_filter.mp hc₂).2.1
  have hc₁_ne_v : c₁ ≠ v := by
    intro hc₁v
    have : c₁ = a := by
      calc
        c₁ = v := hc₁v
        _ = par v := hpar_root.symm
        _ = a := by simpa [hc₁v] using hpar₁
    exact (Finset.mem_filter.mp hc₁).2.2 this
  have hc₂_ne_v : c₂ ≠ v := by
    intro hc₂v
    have : c₂ = a := by
      calc
        c₂ = v := hc₂v
        _ = par v := hpar_root.symm
        _ = a := by simpa [hc₂v] using hpar₂
    exact (Finset.mem_filter.mp hc₂).2.2 this
  have hdep₁ : dep a + 1 = dep c₁ := by
    simpa [hpar₁] using hpar_dep c₁ hc₁S hc₁_ne_v
  have hdep₂ : dep a + 1 = dep c₂ := by
    simpa [hpar₂] using hpar_dep c₂ hc₂S hc₂_ne_v
  have hdepth₁ :=
    iterate_depth_eq S par dep v hpar_root hpar_mem hpar_dep hc₁S hc₁_ne_v hxS hn
  have hdepth₂ :=
    iterate_depth_eq S par dep v hpar_root hpar_mem hpar_dep hc₂S hc₂_ne_v hxS hm
  have hnm : n = m := by omega
  subst hnm
  exact hc_ne (hn.symm.trans hm)

private theorem succ_card_treeChildren_le_admVertex
    (G : SimpleGraph V) (r : ℕ) (v : V)
    (S : Finset V) (par : V → V) (dep : V → ℕ)
    (hpar_root : par v = v)
    (hpar_mem : ∀ a ∈ S, par a ∈ S)
    (hpar_dep : ∀ a ∈ S, a ≠ v → dep (par a) + 1 = dep a)
    (hdep_le : ∀ a ∈ S, dep a ≤ r)
    (habove : ∀ a ∈ S, a ∉ (SReach G r v \ {v}).toFinset → v ≤ a)
    (hadj : ∀ a ∈ S, a ≠ v → G.Adj (par a) a)
    (hreach : ∀ a ∈ S, a ≠ v →
      ∃ u ∈ (SReach G r v \ {v}).toFinset, u ∈ S ∧ ∃ n, par^[n] u = a)
    (hleaf : ∀ u ∈ (SReach G r v \ {v}).toFinset, u ∈ S →
      ∀ b ∈ S, par b ≠ u ∨ b = u)
    (hdisjoint : ∀ a ∈ S, ∀ c₁ ∈ treeChildren S par a, ∀ c₂ ∈ treeChildren S par a,
      c₁ ≠ c₂ → ∀ x ∈ S, (∃ n, par^[n] x = c₁) → ¬∃ m, par^[m] x = c₂)
    (w : V) (hw : w ∈ S) :
    (treeChildren S par w).card + 1 ≤ admVertex G r w := by
  classical
  let children : Finset V := treeChildren S par w
  let child : Fin children.card → V := fun i => (children.equivFin.symm i).1
  have hchild_mem : ∀ i, child i ∈ children := by
    intro i
    exact (children.equivFin.symm i).2
  have hchild_data : ∀ i, child i ∈ S ∧ par (child i) = w ∧ child i ≠ w := by
    intro i
    rcases Finset.mem_filter.mp (hchild_mem i) with ⟨hS, hpred⟩
    exact ⟨hS, hpred.1, hpred.2⟩
  have hchild_ne_v : ∀ i, child i ≠ v := by
    intro i
    rcases hchild_data i with ⟨hcS, hparc, hc_ne_w⟩
    intro hcv
    have hcw : child i = w := by
      calc
        child i = v := hcv
        _ = par v := hpar_root.symm
        _ = w := by simpa [hcv] using hparc
    exact hc_ne_w hcw
  have hleaf_data : ∀ i : Fin children.card,
      ∃ u : V, u ∈ (SReach G r v \ {v}).toFinset ∧ u ∈ S ∧ ∃ n, par^[n] u = child i := by
    intro i
    rcases hchild_data i with ⟨hcS, _, _⟩
    exact hreach (child i) hcS (hchild_ne_v i)
  let leaf : Fin children.card → V := fun i => Classical.choose (hleaf_data i)
  have hleaf_mem : ∀ i, leaf i ∈ (SReach G r v \ {v}).toFinset := by
    intro i
    exact (Classical.choose_spec (hleaf_data i)).1
  have hleaf_S : ∀ i, leaf i ∈ S := by
    intro i
    exact (Classical.choose_spec (hleaf_data i)).2.1
  have hleaf_desc : ∀ i, ∃ n, par^[n] (leaf i) = child i := by
    intro i
    exact (Classical.choose_spec (hleaf_data i)).2.2
  have hraw_data : ∀ i, ∃ q : G.Walk w (leaf i),
      q.length ≤ r ∧
      ∀ y ∈ q.support, y = w ∨ y ∈ S ∧ ∃ m, par^[m] y = child i := by
    intro i
    exact exists_child_leaf_walk G r v S par dep hpar_root hpar_mem hpar_dep
      hdep_le hadj w (child i) (leaf i) (hchild_mem i) (hleaf_S i) (hleaf_desc i)
  let raw : ∀ i, G.Walk w (leaf i) := fun i => Classical.choose (hraw_data i)
  have hraw_len : ∀ i, (raw i).length ≤ r := by
    intro i
    exact (Classical.choose_spec (hraw_data i)).1
  have hraw_support : ∀ i y, y ∈ (raw i).support → y = w ∨ y ∈ S ∧ ∃ m, par^[m] y = child i := by
    intro i y hy
    exact (Classical.choose_spec (hraw_data i)).2 y hy
  let paths : Fin children.card → (u : V) × G.Walk w u :=
    fun i => ⟨leaf i, (raw i).bypass⟩
  have hpaths : IsAdmFamily G r w paths := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      have hleaf_set : leaf i ∈ SReach G r v \ {v} := by
        simpa using hleaf_mem i
      simp only [Set.mem_diff, Set.mem_singleton_iff] at hleaf_set
      have hleaf_lt_v : leaf i < v := lt_of_le_of_ne hleaf_set.1.1 hleaf_set.2
      have hw_not_sreach : w ∉ (SReach G r v \ {v}).toFinset := by
        intro hw_sreach
        rcases hchild_data i with ⟨hcS, hparc, hc_ne_w⟩
        rcases hleaf w hw_sreach hw (child i) hcS with hpar_ne | hcw
        · exact hpar_ne hparc
        · exact hc_ne_w hcw
      have hvw : v ≤ w := habove w hw hw_not_sreach
      exact lt_of_lt_of_le hleaf_lt_v hvw
    · intro i
      simpa [paths] using (raw i).bypass_isPath
    · intro i
      exact le_trans (SimpleGraph.Walk.length_bypass_le (raw i)) (hraw_len i)
    · intro i j hij x hxi hxj
      by_cases hxw : x = w
      · exact hxw
      · have hxi_raw : x ∈ (raw i).support := by
          exact SimpleGraph.Walk.support_bypass_subset (raw i) (by simpa [paths] using hxi)
        have hxj_raw : x ∈ (raw j).support := by
          exact SimpleGraph.Walk.support_bypass_subset (raw j) (by simpa [paths] using hxj)
        have hxi_desc : x ∈ S ∧ ∃ n, par^[n] x = child i := by
          rcases hraw_support i x hxi_raw with rfl | hx
          · exact (hxw rfl).elim
          · exact hx
        have hxj_desc : x ∈ S ∧ ∃ n, par^[n] x = child j := by
          rcases hraw_support j x hxj_raw with rfl | hx
          · exact (hxw rfl).elim
          · exact hx
        have hchild_ne : child i ≠ child j := by
          intro hEq
          apply hij
          apply children.equivFin.symm.injective
          exact Subtype.ext hEq
        exact False.elim <|
          (hdisjoint w hw (child i) (hchild_mem i) (child j) (hchild_mem j)
            hchild_ne x hxi_desc.1 hxi_desc.2) hxj_desc.2
  have hw_not_child : w ∉ children := by
    intro hw_child
    rcases Finset.mem_filter.mp hw_child with ⟨_, hpred⟩
    exact hpred.2 rfl
  have hcard_lt : children.card < Fintype.card V := by
    simpa [children] using
      (Fintype.card_subtype_lt (p := fun x : V => x ∈ children) (x := w) hw_not_child)
  unfold admVertex
  have hsup : children.card ≤
      Finset.sup (Finset.range (Fintype.card V)) (fun k =>
        if ∃ paths : Fin k → (u : V) × G.Walk w u, IsAdmFamily G r w paths
        then k else 0) := by
    have hfamily : ∃ ps : Fin children.card → (u : V) × G.Walk w u, IsAdmFamily G r w ps :=
      ⟨paths, hpaths⟩
    have hmem : children.card ∈ Finset.range (Fintype.card V) :=
      Finset.mem_range.mpr hcard_lt
    simpa [if_pos hfamily] using
      (Finset.le_sup (f := fun k =>
        if ∃ paths : Fin k → (u : V) × G.Walk w u, IsAdmFamily G r w paths
        then k else 0) hmem)
  have hsup' : (treeChildren S par w).card ≤
      Finset.sup (Finset.range (Fintype.card V)) (fun k =>
        if ∃ paths : Fin k → (u : V) × G.Walk w u, IsAdmFamily G r w paths
        then k else 0) := by
    simpa [children] using hsup
  omega

private theorem tree_branching_le_adm
    (G : SimpleGraph V) (r : ℕ) (v : V) (k : ℕ)
    (hk : adm G r = k + 1)
    (S : Finset V) (par : V → V) (dep : V → ℕ)
    (hpar_root : par v = v)
    (hpar_mem : ∀ a ∈ S, par a ∈ S)
    (hpar_dep : ∀ a ∈ S, a ≠ v → dep (par a) + 1 = dep a)
    (hdep_le : ∀ a ∈ S, dep a ≤ r)
    (habove : ∀ a ∈ S, a ∉ (SReach G r v \ {v}).toFinset → v ≤ a)
    (hadj : ∀ a ∈ S, a ≠ v → G.Adj (par a) a)
    (hreach : ∀ a ∈ S, a ≠ v →
      ∃ u ∈ (SReach G r v \ {v}).toFinset, u ∈ S ∧ ∃ n, par^[n] u = a)
    (hleaf : ∀ u ∈ (SReach G r v \ {v}).toFinset, u ∈ S →
      ∀ b ∈ S, par b ≠ u ∨ b = u)
    (hdisjoint : ∀ a ∈ S, ∀ c₁ ∈ treeChildren S par a, ∀ c₂ ∈ treeChildren S par a,
      c₁ ≠ c₂ → ∀ x ∈ S, (∃ n, par^[n] x = c₁) → ¬∃ m, par^[m] x = c₂)
    (w : V) (hw : w ∈ S) :
    (treeChildren S par w).card ≤ k := by
  have hlocal : (treeChildren S par w).card + 1 ≤ admVertex G r w :=
    succ_card_treeChildren_le_admVertex G r v S par dep hpar_root
      hpar_mem hpar_dep hdep_le habove hadj hreach hleaf
      hdisjoint w hw
  have hglobal : admVertex G r w ≤ k + 1 := by
    simpa [hk] using admVertex_le_adm G r w
  omega

private theorem exists_tree_covering_sreach (G : SimpleGraph V) (r : ℕ) (v : V) :
    ∃ (S : Finset V) (par : V → V) (dep : V → ℕ),
      v ∈ S ∧
      par v = v ∧
      (∀ a ∈ S, par a ∈ S) ∧
      (∀ a ∈ S, a ≠ v → dep (par a) + 1 = dep a) ∧
      dep v = 0 ∧
      (∀ a ∈ S, dep a ≤ r) ∧
      (∀ a ∈ S, (treeChildren S par a).card ≤ adm G r - 1) ∧
      (SReach G r v \ {v}).toFinset ⊆ treeLeaves S par v := by
  classical
  obtain ⟨d, bp, hd_v, hbp_v, hbp_step, hd_lower, _⟩ := above_v_bfs_data G r v
  let SR : Finset V := (SReach G r v \ {v}).toFinset
  have hSR_lt_mem : ∀ {u}, u ∈ SR → u < v ∧ u ∈ SReach G r v := by
    intro u hu
    have hu_set : u ∈ SReach G r v \ ({v} : Set V) := by
      simpa [SR] using hu
    have hu_diff : u ∈ SReach G r v ∧ u ≠ v := by
      simpa [Set.mem_diff, Set.mem_singleton_iff] using hu_set
    have hu_le : u ≤ v := by
      exact (show u ≤ v ∧ ∃ p : G.Walk v u, p.IsPath ∧ p.length ≤ r ∧
        ∀ i : ℕ, 0 < i → i < p.length → v < p.getVert i from by
        simpa [SReach] using hu_diff.1).1
    exact ⟨lt_of_le_of_ne hu_le hu_diff.2, hu_diff.1⟩
  have hnot_SR_of_ge : ∀ {a}, v ≤ a → a ∉ SR := by
    intro a ha_ge haSR
    exact (not_lt_of_ge ha_ge) (hSR_lt_mem haSR).1
  have hpred_exists : ∀ u, u ∈ SR → ∃ u', v ≤ u' ∧ G.Adj u' u ∧ d u' + 1 ≤ r := by
    intro u hu
    have hu_mem : u ∈ SReach G r v := (hSR_lt_mem hu).2
    have hu_ne : u ≠ v := (hSR_lt_mem hu).1.ne
    rcases sreach_predecessor G r v u hu_mem hu_ne with
      ⟨_, u', p, hu'_ge, hu'_adj, hp_support, hp_len⟩
    have hd_u' : d u' ≤ p.length := hd_lower u' p hp_support (by omega)
    refine ⟨u', hu'_ge, hu'_adj, ?_⟩
    omega
  let pred : V → V := fun u =>
    if hu : u ∈ SR then Classical.choose (hpred_exists u hu) else v
  have hpred_spec : ∀ {u}, u ∈ SR → v ≤ pred u ∧ G.Adj (pred u) u ∧ d (pred u) + 1 ≤ r := by
    intro u hu
    simp [pred, hu]
    exact Classical.choose_spec (hpred_exists u hu)
  let Useful : V → Prop := fun a =>
    a = v ∨ ∃ u ∈ SR, ∃ n, bp^[n] (pred u) = a
  let S : Finset V := (Finset.univ.filter Useful) ∪ SR
  let par : V → V := fun a => if a ∈ SR then pred a else bp a
  let dep : V → ℕ := fun a => if a ∈ SR then d (pred a) + 1 else d a
  have huseful_memS : ∀ {a}, Useful a → a ∈ S := by
    intro a ha
    exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_filter.mpr ⟨by simp, ha⟩
  have hSR_memS : ∀ {u}, u ∈ SR → u ∈ S := by
    intro u hu
    exact Finset.mem_union.mpr <| Or.inr hu
  have huseful_of_memS_notSR : ∀ {a}, a ∈ S → a ∉ SR → Useful a := by
    intro a haS ha_notSR
    rcases Finset.mem_union.mp haS with haU | haSR
    · exact (Finset.mem_filter.mp haU).2
    · exact False.elim (ha_notSR haSR)
  have hpar_eq_bp_of_ge : ∀ {a}, v ≤ a → par a = bp a := by
    intro a ha_ge
    simp [par, hnot_SR_of_ge ha_ge]
  have hdep_eq_d_of_ge : ∀ {a}, v ≤ a → dep a = d a := by
    intro a ha_ge
    simp [dep, hnot_SR_of_ge ha_ge]
  have hpred_useful : ∀ {u}, u ∈ SR → Useful (pred u) := by
    intro u hu
    right
    exact ⟨u, hu, 0, rfl⟩
  have hbp_preserves_bounds : ∀ {a}, v ≤ a → d a ≤ r → v ≤ bp a ∧ d (bp a) ≤ r := by
    intro a ha_ge hda
    by_cases ha_v : a = v
    · subst a
      simp [hbp_v, hd_v]
    · rcases hbp_step a ha_ge hda ha_v with ⟨hbp_ge, _, hbp_dep⟩
      refine ⟨hbp_ge, ?_⟩
      omega
  have hbp_iter_bounds : ∀ {u}, u ∈ SR → ∀ n, v ≤ bp^[n] (pred u) ∧ d (bp^[n] (pred u)) ≤ r := by
    intro u hu n
    induction n with
    | zero =>
        rcases hpred_spec hu with ⟨hpred_ge, _, hpred_bound⟩
        refine ⟨by simpa using hpred_ge, ?_⟩
        have hd_pred : d (pred u) ≤ r := by
          omega
        simpa using hd_pred
    | succ n ih =>
        simpa [Function.iterate_succ_apply'] using hbp_preserves_bounds ih.1 ih.2
  have huseful_bounds : ∀ {a}, Useful a → v ≤ a ∧ d a ≤ r := by
    intro a ha
    rcases ha with rfl | ⟨u, hu, n, rfl⟩
    · simp [hd_v]
    · exact hbp_iter_bounds hu n
  have huseful_bp : ∀ {a}, Useful a → Useful (bp a) := by
    intro a ha
    rcases ha with rfl | ⟨u, hu, n, rfl⟩
    · left
      simp [hbp_v]
    · right
      refine ⟨u, hu, n.succ, ?_⟩
      simp [Function.iterate_succ_apply']
  have hroot_mem : v ∈ S := huseful_memS <| Or.inl rfl
  have hv_not_SR : v ∉ SR := hnot_SR_of_ge le_rfl
  have hpar_root : par v = v := by
    simp [par, hv_not_SR, hbp_v]
  have hpar_mem : ∀ a ∈ S, par a ∈ S := by
    intro a haS
    by_cases haSR : a ∈ SR
    · simpa [par, haSR] using huseful_memS (hpred_useful haSR)
    · have haUseful : Useful a := huseful_of_memS_notSR haS haSR
      have hbpUseful : Useful (bp a) := huseful_bp haUseful
      simpa [par, haSR] using huseful_memS hbpUseful
  have hpar_dep : ∀ a ∈ S, a ≠ v → dep (par a) + 1 = dep a := by
    intro a haS ha_ne_v
    by_cases haSR : a ∈ SR
    · have hpred_ge : v ≤ pred a := (hpred_spec haSR).1
      have hpred_notSR : pred a ∉ SR := hnot_SR_of_ge hpred_ge
      simp [par, dep, haSR, hpred_notSR]
    · have haUseful : Useful a := huseful_of_memS_notSR haS haSR
      have ha_bounds := huseful_bounds haUseful
      rcases hbp_step a ha_bounds.1 ha_bounds.2 ha_ne_v with ⟨hbp_ge, _, hbp_dep⟩
      have hbp_notSR : bp a ∉ SR := hnot_SR_of_ge hbp_ge
      simp [par, dep, haSR, hbp_notSR, hbp_dep]
  have hdep_root : dep v = 0 := by
    simp [dep, hv_not_SR, hd_v]
  have hdep_le : ∀ a ∈ S, dep a ≤ r := by
    intro a haS
    by_cases haSR : a ∈ SR
    · simpa [dep, haSR] using (hpred_spec haSR).2.2
    · have haUseful : Useful a := huseful_of_memS_notSR haS haSR
      simpa [dep, haSR] using (huseful_bounds haUseful).2
  have habove : ∀ a ∈ S, a ∉ SR → v ≤ a := by
    intro a haS ha_notSR
    exact (huseful_bounds (huseful_of_memS_notSR haS ha_notSR)).1
  have hadj : ∀ a ∈ S, a ≠ v → G.Adj (par a) a := by
    intro a haS ha_ne_v
    by_cases haSR : a ∈ SR
    · simpa [par, haSR] using (hpred_spec haSR).2.1
    · have haUseful : Useful a := huseful_of_memS_notSR haS haSR
      have ha_bounds := huseful_bounds haUseful
      rcases hbp_step a ha_bounds.1 ha_bounds.2 ha_ne_v with ⟨_, hbp_adj, _⟩
      simpa [par, haSR] using hbp_adj
  have hpar_above : ∀ {a}, a ∈ S → v ≤ par a := by
    intro a haS
    by_cases haSR : a ∈ SR
    · simpa [par, haSR] using (hpred_spec haSR).1
    · have haUseful : Useful a := huseful_of_memS_notSR haS haSR
      have hbpUseful : Useful (bp a) := huseful_bp haUseful
      simpa [par, haSR] using (huseful_bounds hbpUseful).1
  have hpar_iter_pred : ∀ {u}, u ∈ SR → ∀ n, par^[n.succ] u = bp^[n] (pred u) := by
    intro u hu n
    induction n with
    | zero =>
        simp [par, hu]
    | succ n ih =>
        have hge : v ≤ bp^[n] (pred u) := (hbp_iter_bounds hu n).1
        calc
          par^[n.succ.succ] u = par (par^[n.succ] u) := by
            rw [Function.iterate_succ_apply']
          _ = par (bp^[n] (pred u)) := by
            rw [ih]
          _ = bp (bp^[n] (pred u)) := by
            simpa using (hpar_eq_bp_of_ge hge)
          _ = bp^[n.succ] (pred u) := by
            rw [Function.iterate_succ_apply']
  have hreach : ∀ a ∈ S, a ≠ v →
      ∃ u ∈ SR, u ∈ S ∧ ∃ n, par^[n] u = a := by
    intro a haS ha_ne_v
    by_cases haSR : a ∈ SR
    · refine ⟨a, haSR, hSR_memS haSR, 0, by simp⟩
    · have haUseful : Useful a := huseful_of_memS_notSR haS haSR
      rcases haUseful with hEq | ⟨u, hu, n, hn⟩
      · exact False.elim (ha_ne_v hEq)
      · refine ⟨u, hu, hSR_memS hu, n.succ, ?_⟩
        exact (hpar_iter_pred hu n).trans hn
  have hleaf : ∀ u ∈ SR, u ∈ S →
      ∀ b ∈ S, par b ≠ u ∨ b = u := by
    intro u hu _ b hbS
    left
    intro hparb
    have : v ≤ u := by
      simpa [hparb] using hpar_above hbS
    exact (not_lt_of_ge this) (hSR_lt_mem hu).1
  have hdisjoint :
      ∀ a ∈ S, ∀ c₁ ∈ treeChildren S par a, ∀ c₂ ∈ treeChildren S par a,
        c₁ ≠ c₂ → ∀ x ∈ S, (∃ n, par^[n] x = c₁) → ¬∃ m, par^[m] x = c₂ :=
    descendants_of_distinct_children_disjoint S par dep v hpar_root hpar_mem hpar_dep
  have hadm_ge : 1 ≤ adm G r := by
    calc
      1 ≤ admVertex G r v := by
        unfold admVertex
        omega
      _ ≤ adm G r := admVertex_le_adm G r v
  have hk : adm G r = (adm G r - 1) + 1 := by
    omega
  have hbranch : ∀ a ∈ S, (treeChildren S par a).card ≤ adm G r - 1 := by
    intro a haS
    exact tree_branching_le_adm G r v (adm G r - 1) hk S par dep hpar_root
      hpar_mem hpar_dep hdep_le habove hadj hreach hleaf hdisjoint a haS
  have hleaf_cover : SR ⊆ treeLeaves S par v := by
    intro u hu
    have huS : u ∈ S := hSR_memS hu
    have hu_ne_v : u ≠ v := (hSR_lt_mem hu).1.ne
    have hchild_empty : treeChildren S par u = ∅ := by
      ext b
      constructor
      · intro hb
        rcases Finset.mem_filter.mp hb with ⟨hbS, hchild⟩
        rcases hleaf u hu huS b hbS with hpar_ne | hbu
        · exact (hpar_ne hchild.1).elim
        · exact (hchild.2 hbu).elim
      · intro hb
        simp at hb
    rw [treeLeaves]
    exact Finset.mem_filter.mpr ⟨huS, ⟨hu_ne_v, by simp [hchild_empty]⟩⟩
  refine ⟨S, par, dep, hroot_mem, hpar_root, hpar_mem, hpar_dep, hdep_root,
    hdep_le, hbranch, ?_⟩
  simpa [SR] using hleaf_cover

private theorem ncard_sreach_sdiff_le_pow (G : SimpleGraph V) (r : ℕ) (v : V) :
    (SReach G r v \ {v}).ncard ≤ (adm G r - 1) ^ r := by
  obtain ⟨S, par, dep, hroot_mem, hpar_root, hpar_mem, hpar_dep,
    hdep_root, hdep_le, hbranch, hleaf_cover⟩ :=
    exists_tree_covering_sreach G r v
  have hbound := card_treeLeaves_le_pow S v par dep r (adm G r - 1)
    hroot_mem hpar_root hpar_mem hpar_dep hdep_root hdep_le hbranch
  calc (SReach G r v \ {v}).ncard
      = (SReach G r v \ {v}).toFinset.card := Set.ncard_eq_toFinset_card' _
    _ ≤ (treeLeaves S par v).card := Finset.card_le_card hleaf_cover
    _ ≤ (adm G r - 1) ^ r := hbound

end

noncomputable section

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Lemma 2.5: the strong r-coloring number is bounded by a power of the
    r-admissibility. -/
theorem scol_le_one_add_adm_sub_one_pow (G : SimpleGraph V) (r : ℕ) :
    Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers.scol G r ≤
      1 + (Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility.adm G r - 1) ^ r := by
  classical
  unfold Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers.scol
  apply Finset.sup_le
  intro v _
  have h1 := Set.ncard_diff_singleton_add_one (self_mem_sreach G r v) (Set.toFinite _)
  have h2 := ncard_sreach_sdiff_le_pow G r v
  omega

end

end Lax5Proofs.Source.Catalog.SparsityLectures.StrongColoringBoundByAdm
