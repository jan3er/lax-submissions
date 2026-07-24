import Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers.Full
import Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility.Full
import Mathlib.Tactic

open Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers

namespace Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumberOrdering

variable {V : Type*} [Fintype V] [LinearOrder V]

open Classical

noncomputable section

open Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility

/-- Every vertex is in its own weak r-reachability set. -/
private theorem self_mem_wreach (G : SimpleGraph V) (r : ℕ) (v : V) :
    v ∈ WReach G r v := by
  refine ⟨le_rfl, ⟨.nil, ?_⟩⟩
  simp

/-- Every vertex is in its own strong r-reachability set. -/
private theorem self_mem_sreach (G : SimpleGraph V) (r : ℕ) (v : V) :
    v ∈ SReach G r v := by
  refine ⟨le_rfl, ⟨.nil, ?_⟩⟩
  simp

private def sreachStep (G : SimpleGraph V) (r : ℕ) (v : V) : Finset V :=
  (SReach G r v \ {v}).toFinset

private def strongLayer (G : SimpleGraph V) (r : ℕ) (v : V) : ℕ → Finset V
  | 0 => {v}
  | n + 1 => (strongLayer G r v n).biUnion (sreachStep G r)

private def strongLayersUpTo (G : SimpleGraph V) (r : ℕ) (v : V) : Finset V :=
  (Finset.range r).biUnion fun n => strongLayer G r v (n + 1)

private theorem sreachStep_card_le_scol_sub_one (G : SimpleGraph V) (r : ℕ) (v : V) :
    (sreachStep G r v).card ≤ scol G r - 1 := by
  have hscol : (SReach G r v).ncard ≤ scol G r := by
    unfold scol
    exact Finset.le_sup (f := fun w => (SReach G r w).ncard) (by simp)
  have hself := Set.ncard_diff_singleton_add_one (self_mem_sreach G r v) (Set.toFinite _)
  have hcard : (sreachStep G r v).card + 1 = (SReach G r v).ncard := by
    simpa [sreachStep, Set.ncard_eq_toFinset_card' _] using hself
  omega

private theorem strongLayer_card_le_pow (G : SimpleGraph V) (r : ℕ) (v : V) :
    ∀ n, (strongLayer G r v n).card ≤ (scol G r - 1) ^ n
  | 0 => by simp [strongLayer]
  | n + 1 => by
      calc
        (strongLayer G r v (n + 1)).card
            ≤ (strongLayer G r v n).card * (scol G r - 1) := by
              simp [strongLayer]
              exact Finset.card_biUnion_le_card_mul _ _ _ (by
                intro w hw
                exact sreachStep_card_le_scol_sub_one G r w)
        _ ≤ (scol G r - 1) ^ n * (scol G r - 1) :=
          Nat.mul_le_mul_right (scol G r - 1) (strongLayer_card_le_pow G r v n)
        _ = (scol G r - 1) ^ (n + 1) := by rw [Nat.pow_succ]

private theorem strongLayersUpTo_card_le_sum (G : SimpleGraph V) (r : ℕ) (v : V) :
    (strongLayersUpTo G r v).card ≤
      Finset.sum (Finset.range r) (fun n => (scol G r - 1) ^ (n + 1)) := by
  unfold strongLayersUpTo
  refine le_trans Finset.card_biUnion_le ?_
  exact Finset.sum_le_sum fun n hn => strongLayer_card_le_pow G r v (n + 1)

private theorem sum_pow_succ_le_mul_pow (k r : ℕ) :
    Finset.sum (Finset.range r) (fun n => k ^ (n + 1)) ≤ r * k ^ r := by
  by_cases hk : k = 0
  · subst hk
    simp
  · have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk)
    calc
      Finset.sum (Finset.range r) (fun n => k ^ (n + 1))
          ≤ Finset.sum (Finset.range r) (fun _ => k ^ r) := by
              refine Finset.sum_le_sum ?_
              intro n hn
              exact pow_le_pow_right' hk1 (Nat.succ_le_of_lt (Finset.mem_range.mp hn))
      _ = r * k ^ r := by simp

private theorem exists_strongLayer_of_weak_witness
    (G : SimpleGraph V) (r : ℕ) {v u : V} (p : G.Walk v u)
    (hp_path : p.IsPath) (hp_len : p.length ≤ r) (hu_le : u ≤ v)
    (hp_internal : ∀ i : ℕ, 0 < i → i < p.length → u < p.getVert i) :
    ∃ t ≤ p.length, u ∈ strongLayer G r v t := by
  let P : ℕ → Prop := fun n =>
    ∀ (v u : V) (p : G.Walk v u),
      p.IsPath →
      p.length = n →
      n ≤ r →
      u ≤ v →
      (∀ i : ℕ, 0 < i → i < p.length → u < p.getVert i) →
      ∃ t ≤ n, u ∈ strongLayer G r v t
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih v u p hp_path hlen hn_le_r hu_le hp_internal
    by_cases huv : u = v
    · subst u
      refine ⟨0, Nat.zero_le _, ?_⟩
      simp [strongLayer]
    · have hp_not_nil : ¬ p.Nil := by
        rw [SimpleGraph.Walk.nil_iff_length_eq]
        intro hp_zero
        apply huv
        have hv : v = p.getVert p.length := by
          simpa [hp_zero] using p.getVert_zero.symm
        exact (hv.trans p.getVert_length).symm
      let S : Finset V := p.dropLast.support.toFinset
      have hv_mem_S : v ∈ S := by
        have hv : p.dropLast.getVert 0 ∈ p.dropLast.support := p.dropLast.getVert_mem_support 0
        simpa [S] using hv
      have hS_nonempty : S.Nonempty := ⟨v, hv_mem_S⟩
      let w : V := S.min' hS_nonempty
      have hw_mem_S : w ∈ S := by
        exact Finset.min'_mem S hS_nonempty
      have hw_drop_support : w ∈ p.dropLast.support := by
        simpa [S] using hw_mem_S
      have hw_le_v : w ≤ v := Finset.min'_le S v hv_mem_S
      rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw_drop_support with
        ⟨i, hget_drop, hi_le_drop⟩
      have hdrop_len : p.dropLast.length = p.length - 1 := by
        simp [SimpleGraph.Walk.dropLast, SimpleGraph.Walk.take_length]
      have hi_lt : i < p.length := by
        rw [hdrop_len] at hi_le_drop
        have hpos : 0 < p.length := Nat.pos_of_ne_zero fun hzero =>
          hp_not_nil (SimpleGraph.Walk.nil_iff_length_eq.mpr hzero)
        exact lt_of_le_of_lt hi_le_drop (Nat.sub_lt hpos (by decide))
      have hi_le : i ≤ p.length := le_of_lt hi_lt
      have hget : p.getVert i = w := by
        have hdrop_eq : p.dropLast.getVert i = p.getVert i := by
          rw [SimpleGraph.Walk.dropLast, SimpleGraph.Walk.take_getVert]
          rw [hdrop_len] at hi_le_drop
          simp [Nat.min_eq_right hi_le_drop]
        exact hdrop_eq.symm.trans hget_drop
      let q : G.Walk v w := (p.take i).copy rfl (by simpa [Nat.min_eq_left hi_le, hget])
      have hq_path : q.IsPath := by
        simpa [q] using hp_path.take i
      have hq_len : q.length = i := by
        simp [q, SimpleGraph.Walk.take_length, Nat.min_eq_left hi_le]
      have hq_len_le_r : q.length ≤ r := by
        rw [hq_len]
        have hi_le_n : i ≤ n := by simpa [hlen] using le_of_lt hi_lt
        exact le_trans hi_le_n hn_le_r
      have hq_internal : ∀ j : ℕ, 0 < j → j < q.length → w < q.getVert j := by
        intro j hj0 hjq
        have hj_lt_i : j < i := by simpa [hq_len] using hjq
        have hj_le_p : j ≤ p.length := le_trans (le_of_lt hj_lt_i) hi_le
        have hj_le_drop : j ≤ p.dropLast.length := by
          rw [hdrop_len]
          omega
        have hj_mem_S : p.getVert j ∈ S := by
          have hj_mem : p.dropLast.getVert j ∈ p.dropLast.support := p.dropLast.getVert_mem_support j
          have hj_eq : p.dropLast.getVert j = p.getVert j := by
            rw [SimpleGraph.Walk.dropLast, SimpleGraph.Walk.take_getVert]
            rw [hdrop_len] at hj_le_drop
            simp [Nat.min_eq_right hj_le_drop]
          simpa [S, hj_eq] using hj_mem
        have hw_le : w ≤ p.getVert j := Finset.min'_le S _ hj_mem_S
        have hw_ne : w ≠ p.getVert j := by
          intro hw_eq
          have hij : i = j := hp_path.getVert_injOn hi_le hj_le_p (by rw [hget, hw_eq])
          omega
        have hw_lt : w < p.getVert j := lt_of_le_of_ne hw_le hw_ne
        simpa [q, SimpleGraph.Walk.take_getVert, Nat.min_eq_right (le_of_lt hj_lt_i)] using hw_lt
      have hw_mem_wreach : w ∈ WReach G r v := by
        refine ⟨hw_le_v, q, hq_path, hq_len_le_r, hq_internal⟩
      let s : G.Walk w u := (p.drop i).copy (by simpa [Nat.min_eq_left hi_le, hget]) rfl
      have hs_path : s.IsPath := by
        simpa [s] using hp_path.drop i
      have hs_len : s.length ≤ r := by
        simp [s, SimpleGraph.Walk.drop_length]
        omega
      have hu_lt_w : u < w := by
        by_cases hi0 : i = 0
        · have hw_eq : v = w := by simpa [hi0] using hget
          simpa [hw_eq] using lt_of_le_of_ne hu_le huv
        · simpa [hget] using hp_internal i (Nat.pos_of_ne_zero hi0) hi_lt
      have hu_step : u ∈ sreachStep G r w := by
        have hs_internal : ∀ j : ℕ, 0 < j → j < s.length → w < s.getVert j := by
          intro j hj0 hjs
          have hij_le : i + j ≤ p.length := by
            have hjs' : j ≤ p.length - i := by
              simp [s, SimpleGraph.Walk.drop_length] at hjs
              exact le_of_lt hjs
            simpa [Nat.add_comm] using Nat.add_le_of_le_sub hi_le hjs'
          have hij_lt : i + j < p.length := by
            have hjs' : j < p.length - i := by simpa [s, SimpleGraph.Walk.drop_length] using hjs
            omega
          have hij_le_drop : i + j ≤ p.dropLast.length := by
            rw [hdrop_len]
            omega
          have hij_mem_S : p.getVert (i + j) ∈ S := by
            have hij_mem : p.dropLast.getVert (i + j) ∈ p.dropLast.support :=
              p.dropLast.getVert_mem_support (i + j)
            have hij_eq : p.dropLast.getVert (i + j) = p.getVert (i + j) := by
              rw [SimpleGraph.Walk.dropLast, SimpleGraph.Walk.take_getVert]
              rw [hdrop_len] at hij_le_drop
              simp [Nat.min_eq_right hij_le_drop]
            simpa [S, hij_eq] using hij_mem
          have hw_le : w ≤ p.getVert (i + j) := Finset.min'_le S _ hij_mem_S
          have hw_ne : w ≠ p.getVert (i + j) := by
            intro hw_eq
            have hij : i = i + j := hp_path.getVert_injOn hi_le (le_of_lt hij_lt) (by rw [hget, hw_eq])
            omega
          have hw_lt : w < p.getVert (i + j) := lt_of_le_of_ne hw_le hw_ne
          simpa [s, SimpleGraph.Walk.drop_getVert, Nat.min_eq_left hij_le] using hw_lt
        have hu_mem_sreach : u ∈ SReach G r w := by
          refine ⟨le_of_lt hu_lt_w, s, hs_path, hs_len, hs_internal⟩
        simp [sreachStep, hu_mem_sreach, hu_lt_w.ne]
      obtain ⟨t, ht_le, hw_layer⟩ :=
        let hi_le_r : i ≤ r := by
          have hi_le_n : i ≤ n := by simpa [hlen] using le_of_lt hi_lt
          exact le_trans hi_le_n hn_le_r
        ih i (by
          rw [← hlen]
          exact hi_lt) v w q hq_path hq_len hi_le_r hw_le_v hq_internal
      have ht_succ_le : t + 1 ≤ n := by
        omega
      refine ⟨t + 1, ht_succ_le, ?_⟩
      exact Finset.mem_biUnion.mpr ⟨w, hw_layer, hu_step⟩
  exact hP p.length v u p hp_path rfl hp_len hu_le hp_internal

private theorem ncard_wreach_sdiff_le_mul_pow (G : SimpleGraph V) (r : ℕ) (v : V) :
    (WReach G r v \ {v}).ncard ≤ r * (scol G r - 1) ^ r := by
  have hcover : (WReach G r v \ {v}).toFinset ⊆ strongLayersUpTo G r v := by
    intro u hu
    have hu_set : u ∈ WReach G r v \ {v} := by
      simpa using hu
    simp only [Set.mem_diff, Set.mem_singleton_iff] at hu_set
    rcases hu_set with ⟨huW, hu_not_v⟩
    rcases huW with ⟨hu_le, p, hp_path, hp_len, hp_internal⟩
    obtain ⟨t, ht_le, hu_layer⟩ :=
      exists_strongLayer_of_weak_witness G r p hp_path hp_len hu_le hp_internal
    have ht_ne_zero : t ≠ 0 := by
      intro ht0
      have : u = v := by simpa [strongLayer, ht0] using hu_layer
      exact hu_not_v (by simpa using this)
    rcases Nat.exists_eq_succ_of_ne_zero ht_ne_zero with ⟨n, rfl⟩
    have hn_lt_r : n < r := by omega
    exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr hn_lt_r, hu_layer⟩
  calc
    (WReach G r v \ {v}).ncard = (WReach G r v \ {v}).toFinset.card := by
      exact Set.ncard_eq_toFinset_card' (WReach G r v \ {v})
    _ ≤ (strongLayersUpTo G r v).card := Finset.card_le_card hcover
    _ ≤ Finset.sum (Finset.range r) (fun n => (scol G r - 1) ^ (n + 1)) :=
      strongLayersUpTo_card_le_sum G r v
    _ ≤ r * (scol G r - 1) ^ r :=
      sum_pow_succ_le_mul_pow (scol G r - 1) r

private theorem exists_sreach_vertex_on_path
    (G : SimpleGraph V) (r : ℕ) {v u : V} (p : G.Walk v u)
    (hp_path : p.IsPath) (hp_len : p.length ≤ r) (hu_lt : u < v) :
    ∃ w, w ∈ SReach G r v \ {v} ∧ w ∈ p.support := by
  have hp_pos : 0 < p.length := by
    by_contra h
    have hzero : p.length = 0 := by omega
    have huv : u = v := by
      calc
        u = p.getVert p.length := by simpa using p.getVert_length.symm
        _ = v := by simpa [hzero] using p.getVert_zero
    exact hu_lt.ne huv
  let P : ℕ → Prop := fun i => 0 < i ∧ p.getVert i ≤ v
  have hP : ∃ i, P i := ⟨p.length, hp_pos, by simpa using le_of_lt hu_lt⟩
  let i := Nat.find hP
  have hi_pos : 0 < i := (Nat.find_spec hP).1
  have hi_le_v : p.getVert i ≤ v := (Nat.find_spec hP).2
  have hi_le_len : i ≤ p.length := Nat.find_min' hP ⟨hp_pos, by simpa using le_of_lt hu_lt⟩
  have hbefore : ∀ j : ℕ, 0 < j → j < i → v < p.getVert j := by
    intro j hj0 hji
    have hnot : ¬ p.getVert j ≤ v := by
      intro hj_le
      have hfind : i ≤ j := Nat.find_min' hP ⟨hj0, hj_le⟩
      exact Nat.not_le_of_gt hji hfind
    exact lt_of_not_ge hnot
  let q : G.Walk v (p.getVert i) := p.take i
  have hq_path : q.IsPath := by
    simpa [q] using hp_path.take i
  have hq_len_eq : q.length = i := by
    rw [show q = p.take i by rfl, SimpleGraph.Walk.take_length]
    simp [Nat.min_eq_left hi_le_len]
  have hq_len : q.length ≤ r := by
    rw [hq_len_eq]
    exact le_trans hi_le_len hp_len
  have hq_internal : ∀ j : ℕ, 0 < j → j < q.length → v < q.getVert j := by
    intro j hj0 hjq
    rw [show q = p.take i by rfl, SimpleGraph.Walk.take_length] at hjq
    have hji : j < i := by
      simp [Nat.min_eq_left hi_le_len] at hjq
      exact hjq
    rw [show q = p.take i by rfl, SimpleGraph.Walk.take_getVert]
    simp [Nat.min_eq_right (le_of_lt hji)]
    exact hbefore j hj0 hji
  have hq_ne_v : p.getVert i ≠ v := by
    intro hEq
    have : i = 0 := (hp_path.getVert_eq_start_iff hi_le_len).mp hEq
    exact Nat.ne_of_gt hi_pos this
  refine ⟨p.getVert i, ?_, p.getVert_mem_support i⟩
  refine ⟨?_, by simpa using hq_ne_v⟩
  exact ⟨hi_le_v, q, hq_path, hq_len, hq_internal⟩

private theorem adm_family_card_le_sreach_sdiff
    (G : SimpleGraph V) (r : ℕ) (v : V) {k : ℕ}
    (paths : Fin k → (u : V) × G.Walk v u) (hpaths : IsAdmFamily G r v paths) :
    k ≤ (SReach G r v \ {v}).ncard := by
  classical
  let pick : Fin k → V := fun i =>
    Classical.choose <|
      exists_sreach_vertex_on_path G r (paths i).2 (hpaths.isPath i) (hpaths.length_le i)
        (hpaths.target_lt i)
  have hpick_mem : ∀ i, pick i ∈ SReach G r v \ {v} := by
    intro i
    exact (Classical.choose_spec <|
      exists_sreach_vertex_on_path G r (paths i).2 (hpaths.isPath i) (hpaths.length_le i)
        (hpaths.target_lt i)).1
  have hpick_support : ∀ i, pick i ∈ (paths i).2.support := by
    intro i
    exact (Classical.choose_spec <|
      exists_sreach_vertex_on_path G r (paths i).2 (hpaths.isPath i) (hpaths.length_le i)
        (hpaths.target_lt i)).2
  have hpick_inj : Function.Injective pick := by
    intro i j hij
    by_contra hij'
    have hsupport_j : pick i ∈ (paths j).2.support := by
      rw [hij]
      exact hpick_support j
    have hv :
        pick i = v := hpaths.disjoint i j hij' (pick i) (hpick_support i) hsupport_j
    have hnotv : pick i ≠ v := by
      have hmem := hpick_mem i
      simpa only [Set.mem_diff, Set.mem_singleton_iff] using hmem.2
    exact hnotv hv
  have hcard :
      (Finset.univ.image pick).card = k := by
    simpa using Finset.card_image_of_injective (s := Finset.univ) hpick_inj
  have hsubset :
      Finset.univ.image pick ⊆ (SReach G r v \ {v}).toFinset := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨i, -, rfl⟩
    simpa using hpick_mem i
  calc
    k = (Finset.univ.image pick).card := hcard.symm
    _ ≤ (SReach G r v \ {v}).toFinset.card := Finset.card_le_card hsubset
    _ = (SReach G r v \ {v}).ncard := (Set.ncard_eq_toFinset_card' _).symm

private theorem admVertex_le_sreach_ncard (G : SimpleGraph V) (r : ℕ) (v : V) :
    Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility.admVertex G r v ≤ (SReach G r v).ncard := by
  unfold Lax5Proofs.Source.Catalog.SparsityLectures.Admissibility.admVertex
  have hsup :
      Finset.sup (Finset.range (Fintype.card V)) (fun k =>
        if ∃ (paths : Fin k → (u : V) × G.Walk v u), IsAdmFamily G r v paths
        then k else 0) ≤ (SReach G r v \ {v}).ncard := by
    apply Finset.sup_le
    intro k hk
    by_cases hkfam : ∃ (paths : Fin k → (u : V) × G.Walk v u), IsAdmFamily G r v paths
    · rcases hkfam with ⟨paths, hpaths⟩
      have hktrue : ∃ (paths : Fin k → (u : V) × G.Walk v u), IsAdmFamily G r v paths :=
        ⟨paths, hpaths⟩
      simpa [if_pos hktrue] using
        adm_family_card_le_sreach_sdiff G r v paths hpaths
    · simp [hkfam]
  have hself := Set.ncard_diff_singleton_add_one (self_mem_sreach G r v) (Set.toFinite _)
  omega

/-- Proposition 2.4 (first part): adm_r ≤ scol_r. -/
theorem adm_le_scol (G : SimpleGraph V) (r : ℕ) :
    adm G r ≤ scol G r := by
  unfold adm scol
  apply Finset.sup_le
  intro v hv
  exact le_trans (admVertex_le_sreach_ncard G r v)
    (Finset.le_sup (f := fun w => (SReach G r w).ncard) (by simp [hv]))

/-- Proposition 2.4 (second part): scol_r ≤ wcol_r. -/
theorem scol_le_wcol (G : SimpleGraph V) (r : ℕ) :
    scol G r ≤ wcol G r := by
  unfold scol wcol
  apply Finset.sup_le
  intro v _
  apply le_trans _ (Finset.le_sup (f := fun v =>
    (Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers.WReach G r v).ncard) (by simp : v ∈ Finset.univ))
  apply Set.ncard_le_ncard
  · intro u hu
    simp only [Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers.SReach, Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumbers.WReach,
      Set.mem_setOf_eq] at *
    obtain ⟨huv, p, hp, hlen, hint⟩ := hu
    exact ⟨huv, p, hp, hlen, fun i hi1 hi2 => lt_of_le_of_lt huv (hint i hi1 hi2)⟩
  · exact Set.toFinite _

/-- Lemma 2.6: wcol_r ≤ 1 + r · (scol_r - 1)^r. -/
theorem wcol_le_of_scol (G : SimpleGraph V) (r : ℕ) :
    wcol G r ≤ 1 + r * (scol G r - 1) ^ r := by
  unfold wcol
  apply Finset.sup_le
  intro v _
  have h1 := Set.ncard_diff_singleton_add_one (self_mem_wreach G r v) (Set.toFinite _)
  have h2 := ncard_wreach_sdiff_le_mul_pow G r v
  omega

end

end Lax5Proofs.Source.Catalog.SparsityLectures.ColoringNumberOrdering
