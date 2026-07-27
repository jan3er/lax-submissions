import Lax12.ColoringNumbers
import Lax12.Admissibility
import Lax12Proofs.OrderedParameters
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Data.Finset.Sort

/-!
The bridge between the ordered parameters of the submitted concepts,
which minimize over vertex permutations of `Fin n` and are stated with
walks, and those of the ported sparsity development, which are stated for
a fixed `LinearOrder` instance and with paths.

Every permutation induces a linear order (`orderOfPerm`) and every linear
order on `Fin n` induces its rank permutation (`rankPerm`); under both,
comparison of positions and comparison in the order agree.  The
reachability sets and admissible families then include into each other in
the evident way: a path is a walk, and a walk bypasses to a path with a
smaller support.  Since the concept parameters are infima over
permutations, one inclusion suffices per comparison.

Throughout, a bare `≤` or `<` between vertices of `Fin m` is the
canonical order — it compares *positions* — while the supplied order is
always written `@LE.le _ ord.toLE`, so that the two never get confused
inside a `letI := ord` block.
-/

namespace Lax12Proofs.OrderBridge

open Lax12.ColoringNumbers Lax12.Admissibility
open Lax12Proofs.OrderedParameters

/-! ### Orders and permutations -/

/-- A type copy used to keep a supplied order distinct from the canonical
order on `Fin m` while constructing ranks. -/
private structure OrderedCopy (m : ℕ) where
  /-- The underlying vertex. -/
  val : Fin m
deriving Fintype

private def orderedCopyEquiv (m : ℕ) : OrderedCopy m ≃ Fin m where
  toFun := OrderedCopy.val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

/-- The rank permutation associated with a finite linear order: it sends
a vertex to its position in the order. -/
def rankPerm {m : ℕ} (ord : LinearOrder (Fin m)) : Equiv.Perm (Fin m) := by
  letI := ord
  letI : LinearOrder (OrderedCopy m) :=
    LinearOrder.lift' OrderedCopy.val fun x y h => by cases x; cases y; simp_all
  let e := Fintype.orderIsoFinOfCardEq (k := m) (OrderedCopy m) (by
    rw [Fintype.card_congr (orderedCopyEquiv m)]
    exact Fintype.card_fin m)
  exact (orderedCopyEquiv m).symm.trans e.symm.toEquiv

/-- Positions under the rank permutation compare exactly as the order
does. -/
theorem rankPerm_le_iff {m : ℕ} (ord : LinearOrder (Fin m)) (x y : Fin m) :
    rankPerm ord x ≤ rankPerm ord y ↔ @LE.le (Fin m) ord.toLE x y := by
  letI := ord
  letI : LinearOrder (OrderedCopy m) :=
    LinearOrder.lift' OrderedCopy.val fun a b h => by cases a; cases b; simp_all
  let e := Fintype.orderIsoFinOfCardEq (k := m) (OrderedCopy m) (by
    rw [Fintype.card_congr (orderedCopyEquiv m)]
    exact Fintype.card_fin m)
  constructor
  · intro h
    have h' : e.symm (⟨x⟩ : OrderedCopy m) ≤ e.symm ⟨y⟩ := h
    exact e.symm.le_iff_le.1 h'
  · intro h
    have h' : (⟨x⟩ : OrderedCopy m) ≤ ⟨y⟩ := h
    exact e.symm.le_iff_le.2 h'

/-- Positions under the rank permutation compare exactly as the order
does. -/
theorem rankPerm_lt_iff {m : ℕ} (ord : LinearOrder (Fin m)) (x y : Fin m) :
    rankPerm ord x < rankPerm ord y ↔ @LT.lt (Fin m) ord.toLT x y := by
  constructor
  · intro h
    refine @lt_of_le_of_ne (Fin m) ord.toPartialOrder x y
      ((rankPerm_le_iff ord x y).1 h.le) fun hc => ?_
    exact absurd (congrArg (rankPerm ord) hc) h.ne
  · intro h
    refine lt_of_le_of_ne ((rankPerm_le_iff ord x y).2
      (@le_of_lt (Fin m) ord.toPartialOrder.toPreorder x y h)) fun hc => ?_
    have hxy : x = y := (rankPerm ord).injective hc
    rw [hxy] at h
    exact absurd h (@lt_irrefl (Fin m) ord.toPartialOrder.toPreorder y)

/-- The linear order induced by a vertex permutation: a vertex precedes
another when its position does. -/
@[reducible] def orderOfPerm {m : ℕ} (π : Equiv.Perm (Fin m)) : LinearOrder (Fin m) :=
  LinearOrder.lift' π π.injective

theorem orderOfPerm_le_iff {m : ℕ} (π : Equiv.Perm (Fin m)) (x y : Fin m) :
    @LE.le (Fin m) (orderOfPerm π).toLE x y ↔ π x ≤ π y := Iff.rfl

theorem orderOfPerm_lt_iff {m : ℕ} (π : Equiv.Perm (Fin m)) (x y : Fin m) :
    @LT.lt (Fin m) (orderOfPerm π).toLT x y ↔ π x < π y := Iff.rfl

/-! ### Reachability sets -/

section Reach

variable {m : ℕ} (H : SimpleGraph (Fin m)) (r : ℕ)

/-- Walk-based weak reachability is contained in the path-based weak
reachability of the ported development, for the rank permutation of the
given order. -/
theorem wreach_subset_WReach (ord : LinearOrder (Fin m)) (v : Fin m) :
    letI := ord
    wreach H (rankPerm ord) r v ⊆ WReach H r v := by
  letI := ord
  rintro u ⟨w, hwLen, hwMin⟩
  refine ⟨(rankPerm_le_iff ord u v).1 (hwMin v w.start_mem_support),
    ⟨w.toPath, w.toPath.property, ?_, ?_⟩⟩
  · exact (SimpleGraph.Walk.length_bypass_le w).trans hwLen
  · intro i hi0 hiLen
    have hmemWalk : w.toPath.val.getVert i ∈ w.support :=
      w.support_toPath_subset (w.toPath.val.getVert_mem_support i)
    have hne : rankPerm ord u ≠ rankPerm ord (w.toPath.val.getVert i) := by
      intro hEq
      have hu : u = w.toPath.val.getVert i := (rankPerm ord).injective hEq
      have hiEq := (w.toPath.property.getVert_eq_end_iff (Nat.le_of_lt hiLen)).mp hu.symm
      omega
    exact (rankPerm_lt_iff ord _ _).1 (lt_of_le_of_ne (hwMin _ hmemWalk) hne)

/-- Walk-based strong reachability is contained in the path-based strong
reachability of the ported development, for the rank permutation of the
given order. -/
theorem sreach_subset_SReach (ord : LinearOrder (Fin m)) (v : Fin m) :
    letI := ord
    sreach H (rankPerm ord) r v ⊆ SReach H r v := by
  letI := ord
  rintro u ⟨huv, w, hwLen, hwMin⟩
  refine ⟨(rankPerm_le_iff ord u v).1 huv, ⟨w.toPath, w.toPath.property, ?_, ?_⟩⟩
  · exact (SimpleGraph.Walk.length_bypass_le w).trans hwLen
  · intro i hi0 hiLen
    have hmemWalk : w.toPath.val.getVert i ∈ w.support :=
      w.support_toPath_subset (w.toPath.val.getVert_mem_support i)
    have hnev : w.toPath.val.getVert i ≠ v := by
      intro hEq
      have := (w.toPath.property.getVert_eq_start_iff (Nat.le_of_lt hiLen)).mp hEq
      omega
    have hneu : w.toPath.val.getVert i ≠ u := by
      intro hEq
      have := (w.toPath.property.getVert_eq_end_iff (Nat.le_of_lt hiLen)).mp hEq
      omega
    exact (rankPerm_lt_iff ord _ _).1 (hwMin _ hmemWalk hnev hneu)

/-- Path-based strong reachability of the ported development is contained
in the walk-based strong reachability for the permutation of the given
order. -/
theorem SReach_subset_sreach (π : Equiv.Perm (Fin m)) (v : Fin m) :
    letI := orderOfPerm π
    SReach H r v ⊆ sreach H π r v := by
  letI := orderOfPerm π
  rintro u ⟨huv, p, _, hlen, hint⟩
  refine ⟨(orderOfPerm_le_iff π u v).1 huv, p, hlen, ?_⟩
  intro y hy hyv hyu
  obtain ⟨i, rfl, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hy
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact absurd p.getVert_zero hyv
  · rcases Nat.lt_or_ge i p.length with hlt | hge
    · exact (orderOfPerm_lt_iff π _ _).1 (hint i hi0 hlt)
    · exact absurd (le_antisymm hi hge ▸ p.getVert_length) hyu

end Reach

/-! ### Coloring numbers -/

/-- The concept weak coloring number is at most the ported one, for the
rank permutation of any order. -/
theorem wcol_le_catalog {m : ℕ} (ord : LinearOrder (Fin m))
    (H : SimpleGraph (Fin m)) (r : ℕ) :
    letI := ord
    Lax12.ColoringNumbers.wcol H r ≤ Lax12Proofs.OrderedParameters.wcol H r := by
  letI := ord
  refine Nat.sInf_le (⟨rankPerm ord, fun v => ?_⟩ :
    ∃ π : Equiv.Perm (Fin m), ∀ v, (wreach H π r v).ncard ≤
      Lax12Proofs.OrderedParameters.wcol H r)
  calc (wreach H (rankPerm ord) r v).ncard
      ≤ (WReach H r v).ncard := Set.ncard_le_ncard (wreach_subset_WReach H r ord v)
    _ ≤ Lax12Proofs.OrderedParameters.wcol H r := by
        unfold Lax12Proofs.OrderedParameters.wcol
        exact Finset.le_sup (f := fun x => (WReach H r x).ncard) (Finset.mem_univ v)

/-- The concept strong coloring number is at most the ported one, for the
rank permutation of any order. -/
theorem scol_le_catalog {m : ℕ} (ord : LinearOrder (Fin m))
    (H : SimpleGraph (Fin m)) (r : ℕ) :
    letI := ord
    Lax12.ColoringNumbers.scol H r ≤ Lax12Proofs.OrderedParameters.scol H r := by
  letI := ord
  refine Nat.sInf_le (⟨rankPerm ord, fun v => ?_⟩ :
    ∃ π : Equiv.Perm (Fin m), ∀ v, (sreach H π r v).ncard ≤
      Lax12Proofs.OrderedParameters.scol H r)
  calc (sreach H (rankPerm ord) r v).ncard
      ≤ (SReach H r v).ncard := Set.ncard_le_ncard (sreach_subset_SReach H r ord v)
    _ ≤ Lax12Proofs.OrderedParameters.scol H r := by
        unfold Lax12Proofs.OrderedParameters.scol
        exact Finset.le_sup (f := fun x => (SReach H r x).ncard) (Finset.mem_univ v)

/-- The ported strong coloring number under the order of a permutation is
at most any bound achieved by that permutation in the concept sense. -/
theorem catalog_scol_le {m : ℕ} (π : Equiv.Perm (Fin m))
    (H : SimpleGraph (Fin m)) (r k : ℕ)
    (hk : ∀ v, (sreach H π r v).ncard ≤ k) :
    letI := orderOfPerm π
    Lax12Proofs.OrderedParameters.scol H r ≤ k := by
  letI := orderOfPerm π
  unfold Lax12Proofs.OrderedParameters.scol
  refine Finset.sup_le fun v _ => ?_
  exact le_trans
    (Set.ncard_le_ncard (SReach_subset_sreach H r π v) (Set.toFinite _)) (hk v)

/-- The set of achievable strong-coloring bounds is nonempty. -/
theorem exists_scol_bound {m : ℕ} (H : SimpleGraph (Fin m)) (r : ℕ) :
    {k | ∃ π : Equiv.Perm (Fin m), ∀ v, (sreach H π r v).ncard ≤ k}.Nonempty := by
  refine ⟨m, 1, fun v => ?_⟩
  have h := Set.ncard_le_ncard (Set.subset_univ (sreach H 1 r v)) Set.finite_univ
  simpa [Set.ncard_univ] using h

/-! ### Admissible families -/

section Adm

variable {m : ℕ} {G : SimpleGraph (Fin m)}

/-- The endpoints of an admissible family are pairwise distinct. -/
theorem admFamily_target_injective {π : Equiv.Perm (Fin m)} {r k : ℕ} {v : Fin m}
    (F : AdmFamily G π r k v) : Function.Injective F.target := by
  intro i j hij
  by_contra hne
  have h1 : F.target i ∈ (F.path i).support := (F.path i).end_mem_support
  have h2 : F.target i ∈ (F.path j).support := by
    rw [hij]; exact (F.path j).end_mem_support
  have hv : F.target i = v := F.meet_eq i j hne _ h1 h2
  have hlt := F.target_lt i
  rw [hv] at hlt
  exact absurd hlt (lt_irrefl (π v))

/-- An admissible family of `k` walks forces `k < m`: its endpoints are
`k` distinct vertices, none of them the root. -/
theorem admFamily_card_lt {π : Equiv.Perm (Fin m)} {r k : ℕ} {v : Fin m}
    (F : AdmFamily G π r k v) : k < m := by
  have hnm : Fintype.card (Fin k) < Fintype.card (Fin m) := by
    refine Fintype.card_lt_of_injective_of_notMem F.target
      (admFamily_target_injective F) (b := v) ?_
    rintro ⟨i, hi⟩
    have hlt := F.target_lt i
    rw [hi] at hlt
    exact absurd hlt (lt_irrefl (π v))
  simpa using hnm

/-- Any concept admissible family bounds the ported admissibility of its
root from below. -/
theorem le_admVertex_of_admFamily {ord : LinearOrder (Fin m)} {r k : ℕ} {v : Fin m}
    (F : AdmFamily G (rankPerm ord) r k v) :
    letI := ord
    k + 1 ≤ admVertex G r v := by
  classical
  letI := ord
  have hk : k < m := admFamily_card_lt F
  have hex : ∃ paths : Fin k → (u : Fin m) × G.Walk v u, IsAdmFamily G r v paths := by
    refine ⟨fun i => ⟨F.target i, (F.path i).bypass⟩, ?_, ?_, ?_, ?_⟩
    · exact fun i => (rankPerm_lt_iff ord _ _).1 (F.target_lt i)
    · exact fun i => SimpleGraph.Walk.bypass_isPath _
    · exact fun i => (SimpleGraph.Walk.length_bypass_le _).trans (F.length_le i)
    · intro i j hij y hy hy'
      exact F.meet_eq i j hij y ((F.path i).support_bypass_subset hy)
        ((F.path j).support_bypass_subset hy')
  have hmem : k ∈ Finset.range (Fintype.card (Fin m)) := by simpa using hk
  have hsup : (fun k' => if ∃ paths : Fin k' → (u : Fin m) × G.Walk v u,
        IsAdmFamily G r v paths then k' else 0) k ≤
      Finset.sup (Finset.range (Fintype.card (Fin m)))
        (fun k' => if ∃ paths : Fin k' → (u : Fin m) × G.Walk v u,
          IsAdmFamily G r v paths then k' else 0) :=
    Finset.le_sup (f := fun k' => if ∃ paths : Fin k' → (u : Fin m) × G.Walk v u,
      IsAdmFamily G r v paths then k' else 0) hmem
  have hsup2 : k ≤ Finset.sup (Finset.range (Fintype.card (Fin m)))
      (fun k' => if ∃ paths : Fin k' → (u : Fin m) × G.Walk v u,
        IsAdmFamily G r v paths then k' else 0) :=
    le_trans (le_of_eq (if_pos hex).symm) hsup
  unfold admVertex
  omega

/-- The set of achievable admissibility bounds is nonempty. -/
theorem exists_adm_bound (G : SimpleGraph (Fin m)) (r : ℕ) :
    {k | HasAdmAtMost G r k}.Nonempty :=
  ⟨m + 1, 1, fun _ _ hj => Nat.succ_le_succ (le_of_lt (admFamily_card_lt hj.some))⟩

/-- The ported admissibility under the order of a permutation is at most
any bound achieved by that permutation in the concept sense. -/
theorem catalog_adm_le {π : Equiv.Perm (Fin m)} (G : SimpleGraph (Fin m)) (r k : ℕ)
    (hk : ∀ (v : Fin m) (j : ℕ), Nonempty (AdmFamily G π r j v) → j + 1 ≤ k) :
    letI := orderOfPerm π
    Lax12Proofs.OrderedParameters.adm G r ≤ k := by
  classical
  letI := orderOfPerm π
  unfold Lax12Proofs.OrderedParameters.adm
  refine Finset.sup_le fun v _ => ?_
  have h1 : 1 ≤ k := by
    have hemp : Nonempty (AdmFamily G π r 0 v) :=
      ⟨{ target := fun i => i.elim0
         path := fun i => i.elim0
         target_lt := fun i => i.elim0
         length_le := fun i => i.elim0
         meet_eq := fun i => i.elim0 }⟩
    simpa using hk v 0 hemp
  have h2 : Finset.sup (Finset.range (Fintype.card (Fin m)))
      (fun k' => if ∃ paths : Fin k' → (u : Fin m) × G.Walk v u,
        IsAdmFamily G r v paths then k' else 0) ≤ k - 1 := by
    refine Finset.sup_le fun k' _ => ?_
    by_cases hex : ∃ paths : Fin k' → (u : Fin m) × G.Walk v u, IsAdmFamily G r v paths
    · rw [if_pos hex]
      obtain ⟨paths, hpaths⟩ := hex
      have hfam : Nonempty (AdmFamily G π r k' v) :=
        ⟨{ target := fun i => (paths i).1
           path := fun i => (paths i).2
           target_lt := fun i => (orderOfPerm_lt_iff π _ _).1 (hpaths.target_lt i)
           length_le := fun i => hpaths.length_le i
           meet_eq := fun i j hij y hy hy' => hpaths.disjoint i j hij y hy hy' }⟩
      have := hk v k' hfam
      omega
    · rw [if_neg hex]; exact Nat.zero_le _
  unfold admVertex
  omega

/-- Admissibility is monotone in the radius: an admissible family at
radius `r` is one at radius `r + 1`, so the set of achievable bounds
shrinks. -/
theorem adm_le_adm_succ (G : SimpleGraph (Fin m)) (r : ℕ) :
    Lax12.Admissibility.adm G r ≤ Lax12.Admissibility.adm G (r + 1) := by
  refine Nat.sInf_le ?_
  obtain ⟨π, hπ⟩ : HasAdmAtMost G (r + 1) (Lax12.Admissibility.adm G (r + 1)) :=
    Nat.sInf_mem (exists_adm_bound G (r + 1))
  refine ⟨π, fun v j hj => ?_⟩
  obtain ⟨F⟩ := hj
  exact hπ v j ⟨{ target := F.target
                  path := F.path
                  target_lt := F.target_lt
                  length_le := fun i => (F.length_le i).trans (Nat.le_succ r)
                  meet_eq := F.meet_eq }⟩

end Adm

end Lax12Proofs.OrderBridge
