import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic

namespace Lax5Proofs.Source.Catalog.SparsityLectures.StrongColoringBoundByAdm

variable {α : Type*} [DecidableEq α]

/-- Children of `a` in the tree: elements of `S` whose parent is `a`,
    excluding `a` itself. -/
def treeChildren (S : Finset α) (parent : α → α) (a : α) : Finset α :=
  S.filter fun b => parent b = a ∧ b ≠ a

/-- Non-root leaves of the tree: elements of `S` distinct from `root`
    that have no proper children. The root is excluded because when it
    has no children, counting it would break the `k ^ r` bound for `r ≥ 1`. -/
def treeLeaves (S : Finset α) (parent : α → α) (root : α) : Finset α :=
  S.filter fun a => a ≠ root ∧ (treeChildren S parent a).card = 0

/-- In a rooted tree represented by a parent function on a finset, if every
vertex has depth at most `r` and at most `k` children, then the number of
non-root leaves is at most `k ^ r`. -/
theorem card_treeLeaves_le_pow
    (S : Finset α) (root : α) (parent : α → α) (depth : α → ℕ) (r k : ℕ)
    (hroot : root ∈ S)
    (hparent_root : parent root = root)
    (hparent_mem : ∀ a ∈ S, parent a ∈ S)
    (hparent_depth : ∀ a ∈ S, a ≠ root → depth (parent a) + 1 = depth a)
    (hdepth_root : depth root = 0)
    (hdepth_le : ∀ a ∈ S, depth a ≤ r)
    (hbranch : ∀ a ∈ S, (treeChildren S parent a).card ≤ k) :
    (treeLeaves S parent root).card ≤ k ^ r := by
  classical
  induction r generalizing S root parent depth k with
  | zero =>
      have hleaf_empty : treeLeaves S parent root = ∅ := by
        ext a
        constructor
        · intro ha
          rcases Finset.mem_filter.mp ha with ⟨haS, haLeaf⟩
          rcases haLeaf with ⟨ha_root, _⟩
          have hdepth_eq := hparent_depth a haS ha_root
          have hdepth_bound := hdepth_le a haS
          omega
        · intro ha
          simp at ha
      simp [hleaf_empty]
  | succ r ih =>
      set children : Finset α := treeChildren S parent root with hchildren
      set subtree : α → Finset α := fun c =>
        S.filter fun a => ∃ n, (parent^[n]) a = c with hsubtree
      set parent' : α → α → α := fun c a => if a = c then c else parent a with hparent'
      set branch : α → Finset α := fun c =>
        (treeLeaves S parent root).filter fun a => a ∈ subtree c with hbranchDef
      have hchildren_card : children.card ≤ k := by
        simpa [hchildren] using hbranch root hroot
      have hiterate_mem : ∀ n {a : α}, a ∈ S → (parent^[n]) a ∈ S := by
        intro n
        induction n with
        | zero =>
            intro a ha
            simpa using ha
        | succ n ihn =>
            intro a ha
            rw [Function.iterate_succ_apply]
            exact ihn (hparent_mem a ha)
      have hroot_iter : ∀ n, (parent^[n]) root = root := by
        intro n
        induction n with
        | zero => rfl
        | succ n ihn =>
            rw [Function.iterate_succ_apply]
            simpa [hparent_root] using ihn
      have hsubtree_ne_root :
          ∀ {c a : α}, c ∈ children → a ∈ subtree c → a ≠ root := by
        intro c a hc haSub
        rcases Finset.mem_filter.mp hc with ⟨_, hpredc⟩
        rcases hpredc with ⟨_, hc_root⟩
        rw [hsubtree] at haSub
        rcases Finset.mem_filter.mp haSub with ⟨_, ⟨n, hn⟩⟩
        intro ha_root
        subst a
        have : root = c := by
          simpa [hroot_iter n] using hn
        exact hc_root this.symm
      have hsubtree_children_subset :
          ∀ c a, treeChildren (subtree c) (parent' c) a ⊆ treeChildren S parent a := by
        intro c a b hb
        rw [treeChildren] at hb ⊢
        rcases Finset.mem_filter.mp hb with ⟨hbSub, hpredb⟩
        rcases hpredb with ⟨hparb, hbne⟩
        rw [hsubtree] at hbSub
        rcases Finset.mem_filter.mp hbSub with ⟨hbS, _⟩
        have hb_ne_c : b ≠ c := by
          intro hbc
          subst b
          have : c = a := by
            simpa [hparent'] using hparb
          exact hbne this
        have hpar : parent b = a := by
          simpa [hparent', hb_ne_c] using hparb
        exact Finset.mem_filter.mpr ⟨hbS, ⟨hpar, hbne⟩⟩
      have hsubtree_root_has_child :
          ∀ {c a : α}, c ∈ children → a ∈ subtree c → a ≠ c →
            (treeChildren (subtree c) (parent' c) c).card ≠ 0 := by
        intro c a hc haSub ha_ne_c
        rcases Finset.mem_filter.mp hc with ⟨_, hpredc⟩
        rcases hpredc with ⟨hparc, hc_root⟩
        rw [hsubtree] at haSub
        rcases Finset.mem_filter.mp haSub with ⟨haS, ⟨n, hn⟩⟩
        have hn_ne_zero : n ≠ 0 := by
          intro hn0
          subst n
          simp only [Function.iterate_zero, id_eq] at hn
          exact ha_ne_c hn
        rcases Nat.exists_eq_succ_of_ne_zero hn_ne_zero with ⟨m, rfl⟩
        let b := (parent^[m]) a
        have hpb : parent b = c := by
          dsimp [b]
          simpa [Function.iterate_succ_apply'] using hn
        have hb_mem_sub : b ∈ subtree c := by
          rw [hsubtree]
          refine Finset.mem_filter.mpr ?_
          refine ⟨hiterate_mem m haS, ⟨1, ?_⟩⟩
          simp [b, hpb]
        have hb_ne_c : b ≠ c := by
          intro hbc
          have : root = c := by
            simpa [hparc, b, hbc] using hpb
          exact hc_root this.symm
        have hb_child : b ∈ treeChildren (subtree c) (parent' c) c := by
          rw [treeChildren]
          refine Finset.mem_filter.mpr ?_
          refine ⟨hb_mem_sub, ?_⟩
          constructor
          · simpa [hparent', hb_ne_c] using hpb
          · exact hb_ne_c
        exact Finset.card_ne_zero.mpr ⟨b, hb_child⟩
      have hdesc_child :
          ∀ n a, depth a = n → a ∈ S → a ≠ root → ∃ c ∈ children, a ∈ subtree c := by
        intro n
        induction n with
        | zero =>
            intro a hdeptha haS ha_root
            have hdepth_eq := hparent_depth a haS ha_root
            omega
        | succ n ihn =>
            intro a hdeptha haS ha_root
            by_cases hpar : parent a = root
            · refine ⟨a, ?_, ?_⟩
              · rw [hchildren, treeChildren]
                exact Finset.mem_filter.mpr ⟨haS, ⟨hpar, ha_root⟩⟩
              · rw [hsubtree]
                exact Finset.mem_filter.mpr ⟨haS, by refine ⟨0, ?_⟩; simp⟩
            · have hparentS : parent a ∈ S := hparent_mem a haS
              have hdepth_parent : depth (parent a) = n := by
                have hdepth_eq := hparent_depth a haS ha_root
                omega
              rcases ihn (parent a) hdepth_parent hparentS hpar with ⟨c, hc, hparentSub⟩
              refine ⟨c, hc, ?_⟩
              rw [hsubtree] at hparentSub ⊢
              rcases Finset.mem_filter.mp hparentSub with ⟨_, ⟨m, hm⟩⟩
              refine Finset.mem_filter.mpr ⟨haS, ⟨m.succ, ?_⟩⟩
              simpa [Function.iterate_succ_apply] using hm
      have hsubtree_bound :
          ∀ c ∈ children, (treeLeaves (subtree c) (parent' c) c).card ≤ k ^ r := by
        intro c hc
        rcases Finset.mem_filter.mp hc with ⟨hcS, hpredc⟩
        rcases hpredc with ⟨hparc, hc_root⟩
        have hc_sub : c ∈ subtree c := by
          rw [hsubtree]
          exact Finset.mem_filter.mpr ⟨hcS, by refine ⟨0, ?_⟩; simp⟩
        have hdepth_c : depth c = 1 := by
          have hdepth_eq := hparent_depth c hcS hc_root
          rw [hparc, hdepth_root] at hdepth_eq
          omega
        have hparent_mem_sub :
            ∀ a ∈ subtree c, parent' c a ∈ subtree c := by
          intro a haSub
          by_cases hac : a = c
          · subst a
            simpa [hparent'] using hc_sub
          · rw [hsubtree] at haSub
            rcases Finset.mem_filter.mp haSub with ⟨haS, ⟨n, hn⟩⟩
            have hn_ne_zero : n ≠ 0 := by
              intro hn0
              subst n
              simp only [Function.iterate_zero, id_eq] at hn
              exact hac hn
            rcases Nat.exists_eq_succ_of_ne_zero hn_ne_zero with ⟨m, rfl⟩
            rw [hsubtree]
            refine Finset.mem_filter.mpr ?_
            refine ⟨by simpa [hparent', hac] using hparent_mem a haS, ⟨m, ?_⟩⟩
            simpa [hparent', hac, Function.iterate_succ_apply] using hn
        have hparent_depth_sub :
            ∀ a ∈ subtree c, a ≠ c → (depth (parent' c a) - 1) + 1 = depth a - 1 := by
          intro a haSub ha_ne_c
          rw [hsubtree] at haSub
          rcases Finset.mem_filter.mp haSub with ⟨haS, _⟩
          have ha_root : a ≠ root := hsubtree_ne_root hc (by simpa [hsubtree] using haSub)
          have hdepth_eq := hparent_depth a haS ha_root
          have hparent_sub : parent a ∈ subtree c := by
            have : parent' c a ∈ subtree c :=
              hparent_mem_sub a (by simpa [hsubtree] using haSub)
            simpa [hparent', ha_ne_c] using this
          have hparent_root : parent a ≠ root := hsubtree_ne_root hc hparent_sub
          have hparent_depth_eq := hparent_depth (parent a) (hparent_mem a haS) hparent_root
          have : parent' c a = parent a := by
            simp [hparent', ha_ne_c]
          rw [this]
          omega
        have hdepth_le_sub :
            ∀ a ∈ subtree c, depth a - 1 ≤ r := by
          intro a haSub
          rw [hsubtree] at haSub
          rcases Finset.mem_filter.mp haSub with ⟨haS, _⟩
          have hdepth_bound := hdepth_le a haS
          by_cases hac : a = c
          · subst a
            omega
          · have ha_root : a ≠ root := hsubtree_ne_root hc (by simpa [hsubtree] using haSub)
            have hdepth_eq := hparent_depth a haS ha_root
            omega
        have hbranch_sub :
            ∀ a ∈ subtree c, (treeChildren (subtree c) (parent' c) a).card ≤ k := by
          intro a haSub
          exact le_trans (Finset.card_le_card (hsubtree_children_subset c a))
            (hbranch a (by
              rw [hsubtree] at haSub
              exact (Finset.mem_filter.mp haSub).1))
        exact ih (subtree c) c (parent' c) (fun a => depth a - 1) k
          hc_sub
          (by simp [hparent'])
          hparent_mem_sub
          hparent_depth_sub
          (by simp [hdepth_c])
          hdepth_le_sub
          hbranch_sub
      have hbranch_card :
          ∀ c ∈ children, (branch c).card ≤ k ^ r := by
        intro c hc
        by_cases hcleaf : (treeChildren S parent c).card = 0
        · have hsingle : branch c ⊆ ({c} : Finset α) := by
            intro a ha
            rw [hbranchDef] at ha
            rcases Finset.mem_filter.mp ha with ⟨haLeaf, haSub⟩
            by_cases hac : a = c
            · simp [hac]
            · have hnonzero :=
                hsubtree_root_has_child hc haSub hac
              have hsubset :=
                hsubtree_children_subset c c
              have : (treeChildren S parent c).card ≠ 0 := by
                intro hzero
                have hle0 : (treeChildren (subtree c) (parent' c) c).card ≤ 0 := by
                  exact le_trans (Finset.card_le_card hsubset) (by simp [hzero])
                exact hnonzero (Nat.eq_zero_of_le_zero hle0)
              exact (this hcleaf).elim
          have hk_pos : 0 < k := by
            have : 1 ≤ children.card := Finset.one_le_card.mpr ⟨c, hc⟩
            have hk_one : 1 ≤ k := le_trans this hchildren_card
            omega
          calc
            (branch c).card ≤ ({c} : Finset α).card := Finset.card_le_card hsingle
            _ = 1 := by simp
            _ ≤ k ^ r := Nat.one_le_pow _ _ hk_pos
        · have hsubset_branch :
            branch c ⊆ treeLeaves (subtree c) (parent' c) c := by
              intro a ha
              rw [hbranchDef] at ha
              rcases Finset.mem_filter.mp ha with ⟨haLeaf, haSub⟩
              rcases Finset.mem_filter.mp haLeaf with ⟨haS, hleafPred⟩
              rcases hleafPred with ⟨ha_root, hleaf_card⟩
              have ha_ne_c : a ≠ c := by
                intro hac
                subst a
                exact hcleaf hleaf_card
              have hleaf_sub :
                  (treeChildren (subtree c) (parent' c) a).card = 0 := by
                apply Nat.eq_zero_of_le_zero
                refine le_trans (Finset.card_le_card (hsubtree_children_subset c a)) ?_
                simp [hleaf_card]
              rw [treeLeaves]
              exact Finset.mem_filter.mpr ⟨haSub, ⟨ha_ne_c, hleaf_sub⟩⟩
          exact le_trans (Finset.card_le_card hsubset_branch) (hsubtree_bound c hc)
      have hleaf_subset :
          treeLeaves S parent root ⊆ children.biUnion branch := by
        intro a haLeaf
        rcases Finset.mem_filter.mp haLeaf with ⟨haS, hleafPred⟩
        rcases hleafPred with ⟨ha_root, _⟩
        have hdeptha := hdepth_le a haS
        rcases hdesc_child (depth a) a rfl haS ha_root with ⟨c, hc, haSub⟩
        rw [Finset.mem_biUnion]
        exact ⟨c, hc, by
          rw [hbranchDef]
          exact Finset.mem_filter.mpr ⟨haLeaf, haSub⟩⟩
      calc
        (treeLeaves S parent root).card ≤ (children.biUnion branch).card :=
          Finset.card_le_card hleaf_subset
        _ ≤ ∑ c ∈ children, (branch c).card := Finset.card_biUnion_le
        _ ≤ ∑ c ∈ children, k ^ r := by
          gcongr with c hc
          exact hbranch_card c hc
        _ = children.card * k ^ r := by simp
        _ ≤ k * k ^ r := by gcongr
        _ = k ^ (Nat.succ r) := by simp [Nat.pow_succ, Nat.mul_comm]

end Lax5Proofs.Source.Catalog.SparsityLectures.StrongColoringBoundByAdm
