import Mathlib.Data.Finset.Interval
import Mathlib.Data.List.GetD
import Lax13Proofs.Refine.Asymptotics.OneDimensionalOperations

/-!
# Pure union-find theory

This file ports the pure union-find development from
`maxhaslbeck/Sepreftime@c1c987b45ec886d289ba215768182ac87b82f20d` and its
AFP partial-equivalence-relation dependency.  Recursive partial functions in
the source are represented by finite-fuel evaluators.  Their public wrappers
choose the unique result of a successful finite run; off `ufaInvar` their
fallback values have no advertised meaning.

Source table (all selected rows):

| source | range | disposition |
|---|---:|---|
| `Partial_Equivalence_Relation.thy` | 11--31 | landed: `PartEquiv`, `partEquivRefl`, `partEquivSymm`, `partEquivTrans`; trans/sym variants are private helpers |
| same | 33--39 | private proof helpers: symmetric closure and its reflexive-transitive closure are subsumed by direct `Set` proofs |
| same | 41--75 | landed: `perUnion`, `perUnionPartEquiv`, `perUnionCompare`, `perUnionSame`, `perUnionComm`, `perUnionDomain`; class-disjoint/domain helpers are private |
| `UnionFind.thy` | 8--40 | landed: `Per`, `perInit`, `perCompare`, `perInitNat`, `perInitOfNatRange`, `perInitPartEquiv`, `perInitSelf`, `perUnionImpl`, `perUnionRelated`, `partEquivRefl` |
| same | 42--59 | landed: `perSupsetRel`, `perSupsetRelDomain`, `perSupsetCompare`, `perSupsetUnion` |
| `Union_Find_Time.thy` | 20--116 | landed: private `repOfFuel`, `repOf`, `ufaInvar`, `ufaInvarD`, source equations, induction, root/bound/idempotence/update/index |
| same | 117--147 | landed: `ufaAlpha`, `ufaAlphaPartEquiv`, `ufaAlphaLength`, `ufaAlphaDomain`, `ufaAlphaRefl`, `ufaAlphaLengthEq` |
| same | 148--331 | landed: init/find, `ufaUnion` invariant/representative/correctness, `ufaCompress` invariant/correctness |
| same | 333--389 | landed: `heightOfFuel`, `heightOf`, `heightOfStep`, `hOf`, `rankInvar`, `rankAtRootLeLength`, `heightOfRoot` |
| same | 394--510 | landed: `heightOfCompress`, `heightOfUnionOnPath`, `heightOfUnionOffPath`, `heightOfUnion` |
| same | 512--564 | private proof helpers: the three generic `Max` lemmas, `Suc_h_of`, `MAXIMUM_Un`, and max monotonicity are subsumed by `Finset.sup` laws; landed source alternative form as `hOf` itself |
| same | 568--647 | landed: `hOfUnionUntouched`, `hOfUnionId`, `hOfUnionTouched`, `heightOfLeHOf`, `heightPowLeLength` |
| same | 813--828 | landed: `heightUb`, `heightUbThetaLog`, `heightOfLeHeightUb` |
-/

open Set Filter
open scoped Topology

namespace Lax13Proofs.Refine.Iicf.UnionFind

open Asymptotics
open Lax13Proofs.Refine.Asymptotics1D

set_option autoImplicit true

/-! ## Partial equivalence relations -/

abbrev Per (α : Type*) := Set (α × α)

def PartEquiv (R : Per α) : Prop :=
  Symmetric (fun x y => (x, y) ∈ R) ∧
    ∀ ⦃x y z⦄, (x, y) ∈ R → (y, z) ∈ R → (x, z) ∈ R

theorem partEquivRefl (hR : PartEquiv R) (hxy : (x, y) ∈ R) :
    (x, x) ∈ R ∧ (y, y) ∈ R := by
  constructor
  · exact hR.2 hxy (hR.1 hxy)
  · exact hR.2 (hR.1 hxy) hxy

theorem partEquivSymm (hR : PartEquiv R) (hxy : (x, y) ∈ R) : (y, x) ∈ R :=
  hR.1 hxy

theorem partEquivTrans (hR : PartEquiv R) (hxy : (x, y) ∈ R)
    (hyz : (y, z) ∈ R) : (x, z) ∈ R :=
  hR.2 hxy hyz

private theorem partEquivTransSymm (hR : PartEquiv R)
    (hab : (a, b) ∈ R) (hcb : (c, b) ∈ R) : (a, c) ∈ R :=
  hR.2 hab (hR.1 hcb)

def perUnion (R : Per α) (a b : α) : Per α :=
  {p | p ∈ R ∨ ((p.1, a) ∈ R ∧ (p.2, b) ∈ R) ∨
    ((p.2, a) ∈ R ∧ (p.1, b) ∈ R)}

theorem perUnionPartEquiv (hR : PartEquiv R) : PartEquiv (perUnion R a b) := by
  constructor
  · intro x y hxy
    rcases hxy with hxy | hxy | hxy
    · exact Or.inl (hR.1 hxy)
    · exact Or.inr (Or.inr hxy)
    · exact Or.inr (Or.inl hxy)
  · intro x y z hxy hyz
    simp only [perUnion, mem_setOf_eq] at hxy hyz ⊢
    rcases hxy with hxy | hxy | hxy <;> rcases hyz with hyz | hyz | hyz
    · exact Or.inl (hR.2 hxy hyz)
    · exact Or.inr (Or.inl ⟨hR.2 hxy hyz.1, hyz.2⟩)
    · exact Or.inr (Or.inr ⟨hyz.1, hR.2 hxy hyz.2⟩)
    · exact Or.inr (Or.inl ⟨hxy.1, hR.2 (hR.1 hyz) hxy.2⟩)
    · exact Or.inr (Or.inl ⟨hxy.1, hyz.2⟩)
    · exact Or.inl (partEquivTransSymm hR hxy.1 hyz.1)
    · exact Or.inr (Or.inr ⟨hR.2 (hR.1 hyz) hxy.1, hxy.2⟩)
    · exact Or.inl (partEquivTransSymm hR hxy.2 hyz.2)
    · exact Or.inr (Or.inr ⟨hyz.1, hxy.2⟩)

theorem perUnionCompare (hR : PartEquiv R) (hij : (i, j) ∈ R) :
    perUnion R i j = R := by
  ext x
  rcases x with ⟨x, y⟩
  simp only [perUnion, mem_setOf_eq]
  constructor
  · rintro (hxy | ⟨hxi, hyj⟩ | ⟨hyj, hxi⟩)
    · exact hxy
    · exact hR.2 hxi (hR.2 hij (hR.1 hyj))
    · exact hR.2 hxi (hR.2 (hR.1 hij) (hR.1 hyj))
  · exact fun h => Or.inl h

@[simp] theorem perUnionSame (hR : PartEquiv R) : perUnion R i i = R := by
  by_cases hi : ∃ x, (i, x) ∈ R
  · obtain ⟨x, hix⟩ := hi
    exact perUnionCompare hR (partEquivRefl hR hix).1
  · ext p
    rcases p with ⟨x, y⟩
    simp only [perUnion, mem_setOf_eq]
    constructor
    · rintro (h | ⟨hxi, _⟩ | ⟨_, hxi⟩)
      · exact h
      · exact False.elim (hi ⟨x, hR.1 hxi⟩)
      · exact False.elim (hi ⟨x, hR.1 hxi⟩)
    · exact fun h => Or.inl h

@[simp] theorem perUnionComm : perUnion R i j = perUnion R j i := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [perUnion, mem_setOf_eq]
  tauto

def relDomain (R : Per α) : Set α := {x | ∃ y, (x, y) ∈ R}

@[simp] theorem perUnionDomain : relDomain (perUnion R i j) = relDomain R := by
  ext x
  simp only [relDomain, mem_setOf_eq, perUnion]
  constructor
  · rintro ⟨y, h | h | h⟩
    · exact ⟨y, h⟩
    · exact ⟨i, h.1⟩
    · exact ⟨j, h.2⟩
  · rintro ⟨y, h⟩
    exact ⟨y, Or.inl h⟩

private def relClass (R : Per α) (i : α) : Set α := {x | (i, x) ∈ R}

/-- AFP `per_classes_dj` (line 70). -/
private theorem perClassesDisjoint (hR : PartEquiv R) (hij : (i, j) ∉ R) :
    relClass R i ∩ relClass R j = ∅ := by
  ext x
  constructor
  · rintro ⟨hix, hjx⟩
    exact False.elim (hij (partEquivTransSymm hR hix hjx))
  · simp

/-- AFP `per_class_in_dom` (line 74). -/
private theorem perClassInDomain (hR : PartEquiv R) : relClass R i ⊆ relDomain R := by
  intro x hix
  exact ⟨i, hR.1 hix⟩

def perInit (D : Set α) : Per α := {p | p.1 = p.2 ∧ p.1 ∈ D}
def perCompare (R : Per α) (a b : α) : Prop := (a, b) ∈ R
def perInitNat (n : ℕ) : Per ℕ := {p | p.1 = p.2 ∧ p.1 < n}

theorem perInitOfNatRange : perInit {i : ℕ | i < n} = perInitNat n := rfl

theorem perInitPartEquiv : PartEquiv (perInit D) := by
  constructor
  · intro x y h
    change x = y ∧ x ∈ D at h
    change y = x ∧ y ∈ D
    exact ⟨h.1.symm, by rw [← h.1]; exact h.2⟩
  · intro x y z hxy hyz
    exact ⟨hxy.1.trans hyz.1, hxy.2⟩

theorem perInitSelf (h : (a, b) ∈ perInit D) : a = b := by
  exact h.1

theorem perUnionImpl (h : (i, j) ∈ R) : (i, j) ∈ perUnion R a b :=
  Or.inl h

theorem perUnionRelated (hR : PartEquiv R) (ha : a ∈ relDomain R)
    (hb : b ∈ relDomain R) : (a, b) ∈ perUnion R a b := by
  obtain ⟨a', ha'⟩ := ha
  obtain ⟨b', hb'⟩ := hb
  exact Or.inr (Or.inl ⟨(partEquivRefl hR ha').1, (partEquivRefl hR hb').1⟩)

private def domainSquare (D : Set α) : Set (α × α) := {p | p.1 ∈ D ∧ p.2 ∈ D}

private def diagonal : Set (α × α) := {p | p.1 = p.2}

/-- Source `per_supset_rel` (`UnionFind.thy:42--44`), literally: restriction
to the smaller domain equals the smaller PER, and everything outside it is
diagonal. -/
def perSupsetRel (p₁ p₂ : Per α) : Prop :=
  p₁ ∩ domainSquare (relDomain p₂) = p₂ ∧
    p₁ \ domainSquare (relDomain p₂) ⊆ diagonal

theorem perSupsetRelDomain (h : perSupsetRel p₁ p₂) : relDomain p₂ ⊆ relDomain p₁ := by
  intro x hx
  obtain ⟨y, hxy⟩ := hx
  have hp : (x, y) ∈ p₁ ∩ domainSquare (relDomain p₂) := by
    rw [h.1]
    exact hxy
  exact ⟨y, hp.1⟩

theorem perSupsetCompare (h : perSupsetRel p₁ p₂) (hx : x ∈ relDomain p₂)
    (hy : y ∈ relDomain p₂) : perCompare p₁ x y ↔ perCompare p₂ x y :=
  calc
    (x, y) ∈ p₁ ↔ (x, y) ∈ p₁ ∩ domainSquare (relDomain p₂) := by
      simp [domainSquare, hx, hy]
    _ ↔ (x, y) ∈ p₂ := by rw [h.1]

theorem perSupsetUnion (h : perSupsetRel p₁ p₂) (hx : x ∈ relDomain p₂)
    (hy : y ∈ relDomain p₂) :
    perSupsetRel (perUnion p₁ x y) (perUnion p₂ x y) := by
  constructor
  · rw [perUnionDomain]
    ext p
    rcases p with ⟨a, b⟩
    simp only [mem_inter_iff, perUnion, mem_setOf_eq, domainSquare]
    constructor
    · rintro ⟨hab | ⟨hax, hby⟩ | ⟨hbx, hay⟩, ha, hb⟩
      · exact Or.inl ((perSupsetCompare h ha hb).1 hab)
      · exact Or.inr (Or.inl
          ⟨(perSupsetCompare h ha hx).1 hax, (perSupsetCompare h hb hy).1 hby⟩)
      · exact Or.inr (Or.inr
          ⟨(perSupsetCompare h hb hx).1 hbx, (perSupsetCompare h ha hy).1 hay⟩)
    · intro hab
      have ha : a ∈ relDomain p₂ := by
        rcases hab with hab | ⟨hax, _⟩ | ⟨_, hay⟩
        · exact ⟨b, hab⟩
        · exact ⟨x, hax⟩
        · exact ⟨y, hay⟩
      have hb : b ∈ relDomain p₂ := by
        rcases hab with hab | ⟨_, hby⟩ | ⟨hbx, _⟩
        · have hp : (a, b) ∈ p₁ ∩ domainSquare (relDomain p₂) := by
            rw [h.1]
            exact hab
          exact hp.2.2
        · exact ⟨y, hby⟩
        · exact ⟨x, hbx⟩
      refine ⟨?_, ha, hb⟩
      rcases hab with hab | ⟨hax, hby⟩ | ⟨hbx, hay⟩
      · exact Or.inl ((perSupsetCompare h ha hb).2 hab)
      · exact Or.inr (Or.inl
          ⟨(perSupsetCompare h ha hx).2 hax, (perSupsetCompare h hb hy).2 hby⟩)
      · exact Or.inr (Or.inr
          ⟨(perSupsetCompare h hb hx).2 hbx, (perSupsetCompare h ha hy).2 hay⟩)
  · rintro ⟨a, b⟩ ⟨hab, hout⟩
    change a = b
    have hout' : a ∉ relDomain p₂ ∨ b ∉ relDomain p₂ := by
      rw [perUnionDomain] at hout
      change ¬(a ∈ relDomain p₂ ∧ b ∈ relDomain p₂) at hout
      tauto
    rcases hab with hab | ⟨hax, hby⟩ | ⟨hbx, hay⟩
    · simpa [diagonal] using h.2 ⟨hab, by
        change ¬(a ∈ relDomain p₂ ∧ b ∈ relDomain p₂)
        tauto⟩
    · rcases hout' with ha | hb
      · have haxDiag : a = x := h.2 ⟨hax, by simp [domainSquare, ha]⟩
        exact False.elim (ha (haxDiag ▸ hx))
      · have hbyDiag : b = y := h.2 ⟨hby, by simp [domainSquare, hb]⟩
        exact False.elim (hb (hbyDiag ▸ hy))
    · rcases hout' with ha | hb
      · have hayDiag : a = y := h.2 ⟨hay, by simp [domainSquare, ha]⟩
        exact False.elim (ha (hayDiag ▸ hy))
      · have hbxDiag : b = x := h.2 ⟨hbx, by simp [domainSquare, hb]⟩
        exact False.elim (hb (hbxDiag ▸ hx))

/-! ## Finite-fuel representatives -/

private def repOfFuel (l : List ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, i =>
      if hi : i < l.length then
        let p := l[i]
        if p = i then some i else repOfFuel l fuel p
      else none

private theorem repOfFuel_succ_of_some (h : repOfFuel l fuel i = some r) :
    repOfFuel l (fuel + 1) i = some r := by
  induction fuel generalizing i with
  | zero => simp [repOfFuel] at h
  | succ fuel ih =>
      rw [repOfFuel] at h ⊢
      by_cases hi : i < l.length
      · simp only [dif_pos hi]
        by_cases hp : l[i] = i
        · simp [hp] at h ⊢
          exact h.2
        · simp only [hp, if_false] at h ⊢
          exact ih (by simpa [hi] using h)
      · simp [hi] at h

private theorem repOfFuel_add_of_some (h : repOfFuel l fuel i = some r) (k : ℕ) :
    repOfFuel l (fuel + k) i = some r := by
  induction k with
  | zero => simpa
  | succ k ih =>
      rw [Nat.add_succ]
      exact repOfFuel_succ_of_some ih

private theorem repOfFuel_unique (h₁ : repOfFuel l f₁ i = some r₁)
    (h₂ : repOfFuel l f₂ i = some r₂) : r₁ = r₂ := by
  have h₁' := repOfFuel_add_of_some h₁ f₂
  have h₂' := repOfFuel_add_of_some h₂ f₁
  rw [Nat.add_comm] at h₂'
  rw [h₁'] at h₂'
  exact Option.some.inj h₂'

noncomputable def repOf (l : List ℕ) (i : ℕ) : ℕ :=
  by
    classical
    exact if h : ∃ r fuel, repOfFuel l fuel i = some r then Classical.choose h else i

private theorem repOf_eq_of_fuel (h : repOfFuel l fuel i = some r) : repOf l i = r := by
  classical
  let hex : ∃ r fuel, repOfFuel l fuel i = some r := ⟨r, fuel, h⟩
  rw [repOf, dif_pos hex]
  obtain ⟨fuel', hr'⟩ := Classical.choose_spec hex
  exact repOfFuel_unique hr' h

def ufaInvar (l : List ℕ) : Prop :=
  ∀ i, i < l.length → l[i]! < l.length ∧ ∃ r fuel, repOfFuel l fuel i = some r

theorem ufaInvarD (h : ufaInvar l) (hi : i < l.length) :
    l[i]! < l.length ∧ ∃ r fuel, repOfFuel l fuel i = some r :=
  h i hi

private theorem repOfFuel_result (h : repOfFuel l fuel i = some r) :
    r < l.length ∧ l[r]! = r := by
  induction fuel generalizing i with
  | zero => simp [repOfFuel] at h
  | succ fuel ih =>
      simp only [repOfFuel] at h
      split at h
      · split at h
        · have hir : i = r := Option.some.inj h
          subst r
          constructor
          · assumption
          · rw [getElem!_pos]
            assumption
        · exact ih h
      · contradiction

theorem repOfRefl (hI : ufaInvar l) (hi : i < l.length) (hroot : l[i]! = i) :
    repOf l i = i := by
  obtain ⟨r, fuel, hrun⟩ := (hI i hi).2
  have hroot' : l[i] = i := by
    rw [getElem!_pos] at hroot
    exact hroot
  have hrootRun : repOfFuel l 1 i = some i := by simp [repOfFuel, hi, hroot']
  rw [repOf_eq_of_fuel hrun, repOfFuel_unique hrun hrootRun]

theorem repOfStep (hI : ufaInvar l) (hi : i < l.length) (hne : l[i]! ≠ i) :
    repOf l i = repOf l l[i]! := by
  have hne' : l[i] ≠ i := by
    rw [getElem!_pos] at hne
    exact hne
  obtain ⟨r, fuel, hfuel⟩ := (hI i hi).2
  cases fuel with
  | zero => simp [repOfFuel] at hfuel
  | succ fuel =>
      have hchild : repOfFuel l fuel l[i]! = some r := by
        simpa [repOfFuel, hi, hne'] using hfuel
      exact (repOf_eq_of_fuel hfuel).trans (repOf_eq_of_fuel hchild).symm

theorem repOfInduct {P : List ℕ → ℕ → Prop} (hI : ufaInvar l) (hi : i < l.length)
    (base : ∀ i, ufaInvar l → i < l.length → l[i]! = i → P l i)
    (step : ∀ i, ufaInvar l → i < l.length → l[i]! ≠ i → P l l[i]! → P l i) :
    P l i := by
  obtain ⟨r, fuel, hfuel⟩ := (hI i hi).2
  have aux : ∀ fuel i r, repOfFuel l fuel i = some r → i < l.length → P l i := by
    intro fuel
    induction fuel with
    | zero => intro i r h; simp [repOfFuel] at h
    | succ fuel ih =>
        intro i r h hi
        by_cases hroot : l[i]! = i
        · exact base i hI hi hroot
        · apply step i hI hi hroot
          apply ih l[i]! r
          · have hroot' : l[i] ≠ i := by
              rw [getElem!_pos] at hroot
              exact hroot
            simpa [repOfFuel, hi, hroot'] using h
          · exact (hI i hi).1
  exact aux fuel i r hfuel hi

theorem repOfRoot (hI : ufaInvar l) (hi : i < l.length) : l[repOf l i]! = repOf l i := by
  obtain ⟨r, fuel, h⟩ := (hI i hi).2
  rw [repOf_eq_of_fuel h]
  exact (repOfFuel_result h).2

theorem repOfBound (hI : ufaInvar l) (hi : i < l.length) : repOf l i < l.length := by
  obtain ⟨r, fuel, h⟩ := (hI i hi).2
  rw [repOf_eq_of_fuel h]
  exact (repOfFuel_result h).1

theorem repOfIdem (hI : ufaInvar l) (hi : i < l.length) :
    repOf l (repOf l i) = repOf l i :=
  repOfRefl hI (repOfBound hI hi) (repOfRoot hI hi)

theorem repOfRootUpdate (hI : ufaInvar l) (hx : x < l.length) (hi : i < l.length) :
    repOf (l.set (repOf l x) (repOf l x)) i = repOf l i := by
  have _terminatesAtI := (hI i hi).2
  have hset : l.set (repOf l x) (repOf l x) = l := by
    apply List.ext_getElem
    · simp
    · intro j hj₁ hj₂
      by_cases hj : j = repOf l x
      · subst j
        rw [List.getElem_set, if_pos rfl]
        have hr := repOfRoot hI hx
        rw [getElem!_pos] at hr
        exact hr.symm
      · rw [List.getElem_set, if_neg (Ne.symm hj)]
  rw [hset]

theorem repOfIndex (hI : ufaInvar l) (hi : i < l.length) :
    repOf l l[i]! = repOf l i := by
  by_cases hroot : l[i]! = i
  · simp [hroot]
  · exact (repOfStep hI hi hroot).symm

/-! ## PER abstraction -/

def ufaAlpha (l : List ℕ) : Per ℕ :=
  {p | p.1 < l.length ∧ p.2 < l.length ∧ repOf l p.1 = repOf l p.2}

theorem ufaAlphaPartEquiv : PartEquiv (ufaAlpha l) := by
  constructor
  · intro x y h
    exact ⟨h.2.1, h.1, h.2.2.symm⟩
  · intro x y z hxy hyz
    exact ⟨hxy.1, hyz.2.1, hxy.2.2.trans hyz.2.2⟩

theorem ufaAlphaLength (h : (x, y) ∈ ufaAlpha l) : x < l.length ∧ y < l.length :=
  ⟨h.1, h.2.1⟩

@[simp] theorem ufaAlphaDomain : relDomain (ufaAlpha l) = Set.Iio l.length := by
  ext x
  constructor
  · rintro ⟨y, h⟩
    exact h.1
  · intro hx
    exact ⟨x, hx, hx, rfl⟩

@[simp] theorem ufaAlphaRefl : (i, i) ∈ ufaAlpha l ↔ i < l.length := by
  simp [ufaAlpha]

theorem ufaAlphaLengthEq (h : ufaAlpha l = ufaAlpha l') : l.length = l'.length := by
  apply le_antisymm
  · by_contra hn
    have hi : l'.length < l.length := Nat.lt_of_not_ge hn
    have : (l'.length, l'.length) ∈ ufaAlpha l := ufaAlphaRefl.2 hi
    rw [h] at this
    exact (ufaAlphaRefl.1 this).false
  · by_contra hn
    have hi : l.length < l'.length := Nat.lt_of_not_ge hn
    have : (l.length, l.length) ∈ ufaAlpha l' := ufaAlphaRefl.2 hi
    rw [← h] at this
    exact (ufaAlphaRefl.1 this).false

/-! ## Pure list operations -/

private theorem repOfFuel_root (hi : i < l.length) (hroot : l[i]! = i) :
    repOfFuel l 1 i = some i := by
  have hroot' : l[i] = i := by rw [getElem!_pos] at hroot; exact hroot
  simp [repOfFuel, hi, hroot']

private theorem repOfFuel_step (hi : i < l.length) (hne : l[i]! ≠ i)
    (hnext : repOfFuel l fuel l[i]! = some r) :
    repOfFuel l (fuel + 1) i = some r := by
  have hne' : l[i] ≠ i := by rw [getElem!_pos] at hne; exact hne
  simpa [repOfFuel, hi, hne'] using hnext

theorem ufaInitInvar (n : ℕ) : ufaInvar (List.range n) := by
  intro i hi
  have hget : (List.range n)[i]! = i := by
    rw [getElem!_pos]
    exact List.getElem_range hi
  refine ⟨by simpa [hget] using hi, i, 1, ?_⟩
  exact repOfFuel_root hi hget

theorem ufaInitCorrect (n : ℕ) : ufaAlpha (List.range n) = perInitNat n := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [ufaAlpha, perInitNat, mem_setOf_eq, List.length_range]
  constructor
  · rintro ⟨hx, hy, hrep⟩
    rw [repOfRefl (ufaInitInvar n) (by simpa using hx)
        (by rw [getElem!_pos]; exact List.getElem_range (by simpa using hx)),
      repOfRefl (ufaInitInvar n) (by simpa using hy)
        (by rw [getElem!_pos]; exact List.getElem_range (by simpa using hy))] at hrep
    exact ⟨hrep, hx⟩
  · rintro ⟨rfl, hx⟩
    exact ⟨hx, hx, rfl⟩

theorem ufaFindCorrect (hI : ufaInvar l) (hx : x < l.length) (hy : y < l.length) :
    repOf l x = repOf l y ↔ (x, y) ∈ ufaAlpha l := by
  have _meaningfulRepresentative := (hI x hx).2
  simp [ufaAlpha, hx, hy]

noncomputable def ufaUnion (l : List ℕ) (x y : ℕ) : List ℕ :=
  l.set (repOf l x) (repOf l y)

private theorem ufaUnion_get_root (hI : ufaInvar l) (hx : x < l.length)
    :
    (ufaUnion l x y)[repOf l x]! = repOf l y := by
  simp [ufaUnion, repOfBound hI hx]

private theorem ufaUnion_get_ne (hi : i < l.length) (hne : i ≠ repOf l x) :
    (ufaUnion l x y)[i]! = l[i]! := by
  simp [ufaUnion, hi, Ne.symm hne]

theorem ufaUnionInvar (hI : ufaInvar l) (hx : x < l.length) (hy : y < l.length) :
    ufaInvar (ufaUnion l x y) := by
  intro i hi'
  have hi : i < l.length := by simpa [ufaUnion] using hi'
  constructor
  · by_cases hir : i = repOf l x
    · subst i
      rw [ufaUnion_get_root hI hx]
      simpa [ufaUnion] using repOfBound hI hy
    · rw [ufaUnion_get_ne hi hir]
      simpa [ufaUnion] using (hI i hi).1
  · apply repOfInduct hI hi
    · intro i _ hi hroot
      by_cases hir : i = repOf l x
      · subst i
        by_cases hxy : repOf l x = repOf l y
        · refine ⟨repOf l x, 1, repOfFuel_root (by simpa [ufaUnion] using hi) ?_⟩
          simpa [hxy] using ufaUnion_get_root hI hx
        · refine ⟨repOf l y, 2, ?_⟩
          apply repOfFuel_step (by simpa [ufaUnion] using hi)
          · simpa [ufaUnion_get_root hI hx] using Ne.symm hxy
          · rw [ufaUnion_get_root hI hx]
            apply repOfFuel_root (by simpa [ufaUnion] using repOfBound hI hy)
            rw [ufaUnion_get_ne (repOfBound hI hy) (Ne.symm hxy)]
            exact repOfRoot hI hy
      · exact ⟨i, 1, repOfFuel_root (by simpa [ufaUnion] using hi)
          (by rw [ufaUnion_get_ne hi hir]; exact hroot)⟩
    · intro i _ hi hne ih
      have hir : i ≠ repOf l x := by
        intro hir
        subst i
        exact hne (repOfRoot hI hx)
      obtain ⟨r, fuel, hfuel⟩ := ih
      refine ⟨r, fuel + 1, ?_⟩
      rw [← ufaUnion_get_ne (y := y) hi hir] at hfuel
      exact repOfFuel_step (by simpa [ufaUnion] using hi)
        (by rw [ufaUnion_get_ne hi hir]; exact hne) hfuel

theorem ufaUnionRep (hI : ufaInvar l) (hx : x < l.length) (hy : y < l.length)
    (hi : i < l.length) :
    repOf (ufaUnion l x y) i =
      if repOf l i = repOf l x then repOf l y else repOf l i := by
  apply repOfInduct hI hi
  · intro i _ hi hroot
    have hri : repOf l i = i := repOfRefl hI hi hroot
    by_cases hir : i = repOf l x
    · subst i
      simp only [hri]
      by_cases hxy : repOf l x = repOf l y
      · rw [← hxy]
        apply repOfRefl (ufaUnionInvar hI hx hy) (by simpa [ufaUnion] using hi)
        simpa [hxy] using ufaUnion_get_root hI hx
      · rw [repOfStep (ufaUnionInvar hI hx hy) (by simpa [ufaUnion] using hi)
          (by simpa [ufaUnion_get_root hI hx] using Ne.symm hxy)]
        rw [ufaUnion_get_root hI hx]
        apply repOfRefl (ufaUnionInvar hI hx hy) (by simpa [ufaUnion] using repOfBound hI hy)
        rw [ufaUnion_get_ne (repOfBound hI hy) (Ne.symm hxy)]
        exact repOfRoot hI hy
    · rw [if_neg (by simpa [hri] using hir)]
      rw [repOfRefl (ufaUnionInvar hI hx hy) (by simpa [ufaUnion] using hi)]
      · exact hri.symm
      · rw [ufaUnion_get_ne hi hir]
        exact hroot
  · intro i _ hi hne ih
    have hir : i ≠ repOf l x := by
      intro hir
      subst i
      exact hne (repOfRoot hI hx)
    rw [repOfStep (ufaUnionInvar hI hx hy) (by simpa [ufaUnion] using hi)]
    · rw [ufaUnion_get_ne hi hir, ih, repOfIndex hI hi]
    · rw [ufaUnion_get_ne hi hir]
      exact hne

theorem ufaUnionCorrect (hI : ufaInvar l) (hx : x < l.length) (hy : y < l.length) :
    ufaAlpha (ufaUnion l x y) = perUnion (ufaAlpha l) x y := by
  ext p
  rcases p with ⟨i, j⟩
  simp only [ufaAlpha, perUnion, mem_setOf_eq, ufaUnion, List.length_set]
  constructor
  · rintro ⟨hi, hj, hu⟩
    change repOf (ufaUnion l x y) i = repOf (ufaUnion l x y) j at hu
    rw [ufaUnionRep hI hx hy hi, ufaUnionRep hI hx hy hj] at hu
    by_cases hiR : repOf l i = repOf l x
    · by_cases hjR : repOf l j = repOf l x
      · exact Or.inl ⟨hi, hj, hiR.trans hjR.symm⟩
      · rw [if_pos hiR, if_neg hjR] at hu
        exact Or.inr (Or.inl ⟨⟨hi, hx, hiR⟩, hj, hy, hu.symm⟩)
    · by_cases hjR : repOf l j = repOf l x
      · rw [if_neg hiR, if_pos hjR] at hu
        exact Or.inr (Or.inr ⟨⟨hj, hx, hjR⟩, hi, hy, hu⟩)
      · rw [if_neg hiR, if_neg hjR] at hu
        exact Or.inl ⟨hi, hj, hu⟩
  · rintro (hij | hxy | hyx)
    · obtain ⟨hi, hj, hij⟩ := hij
      refine ⟨hi, hj, ?_⟩
      change repOf (ufaUnion l x y) i = repOf (ufaUnion l x y) j
      rw [ufaUnionRep hI hx hy hi, ufaUnionRep hI hx hy hj]
      by_cases hiR : repOf l i = repOf l x
      · rw [if_pos hiR, if_pos (hij ▸ hiR)]
      · rw [if_neg hiR, if_neg (by simpa [hij] using hiR), hij]
    · obtain ⟨⟨hi, _, hiR⟩, hj, _, hjY⟩ := hxy
      refine ⟨hi, hj, ?_⟩
      change repOf (ufaUnion l x y) i = repOf (ufaUnion l x y) j
      rw [ufaUnionRep hI hx hy hi, ufaUnionRep hI hx hy hj, if_pos hiR]
      by_cases hYX : repOf l y = repOf l x
      · rw [if_pos (hjY.trans hYX)]
      · rw [if_neg (by intro h; exact hYX (hjY.symm.trans h)), hjY]
    · obtain ⟨⟨hj, _, hjR⟩, hi, _, hiY⟩ := hyx
      refine ⟨hi, hj, ?_⟩
      change repOf (ufaUnion l x y) i = repOf (ufaUnion l x y) j
      rw [ufaUnionRep hI hx hy hi, ufaUnionRep hI hx hy hj, if_pos hjR]
      by_cases hYX : repOf l y = repOf l x
      · rw [if_pos (hiY.trans hYX)]
      · rw [if_neg (by intro h; exact hYX (hiY.symm.trans h)), hiY]

noncomputable def ufaCompress (l : List ℕ) (x : ℕ) : List ℕ := l.set x (repOf l x)

private theorem ufaCompress_get_eq (hx : x < l.length) :
    (ufaCompress l x)[x]! = repOf l x := by simp [ufaCompress, hx]

private theorem ufaCompress_get_ne (hi : i < l.length) (hne : i ≠ x) :
    (ufaCompress l x)[i]! = l[i]! := by simp [ufaCompress, hi, Ne.symm hne]

theorem ufaCompressInvar (hI : ufaInvar l) (hx : x < l.length) :
    ufaInvar (ufaCompress l x) := by
  intro i hi'
  have hi : i < l.length := by simpa [ufaCompress] using hi'
  constructor
  · by_cases hix : i = x
    · subst i
      rw [ufaCompress_get_eq hx]
      simpa [ufaCompress] using repOfBound hI hx
    · rw [ufaCompress_get_ne hi hix]
      simpa [ufaCompress] using (hI i hi).1
  · apply repOfInduct hI hi
    · intro i _ hi hroot
      by_cases hix : i = x
      · subst i
        have hr : repOf l x = x := repOfRefl hI hx hroot
        exact ⟨x, 1, repOfFuel_root (by simpa [ufaCompress] using hx)
          (by rw [ufaCompress_get_eq hx, hr])⟩
      · exact ⟨i, 1, repOfFuel_root (by simpa [ufaCompress] using hi)
          (by rw [ufaCompress_get_ne hi hix]; exact hroot)⟩
    · intro i _ hi hne ih
      by_cases hix : i = x
      · subst i
        have hrne : repOf l x ≠ x := by
          intro hr
          have := repOfRoot hI hx
          rw [hr] at this
          exact hne this
        refine ⟨repOf l x, 2, repOfFuel_step (by simpa [ufaCompress] using hx) ?_ ?_⟩
        · rw [ufaCompress_get_eq hx]
          exact hrne
        · rw [ufaCompress_get_eq hx]
          apply repOfFuel_root (by simpa [ufaCompress] using repOfBound hI hx)
          rw [ufaCompress_get_ne (repOfBound hI hx) hrne]
          exact repOfRoot hI hx
      · obtain ⟨r, fuel, hfuel⟩ := ih
        rw [← ufaCompress_get_ne (x := x) hi hix] at hfuel
        exact ⟨r, fuel + 1, repOfFuel_step (by simpa [ufaCompress] using hi)
          (by rw [ufaCompress_get_ne hi hix]; exact hne) hfuel⟩

private theorem ufaCompressRep (hI : ufaInvar l) (hx : x < l.length)
    (hi : i < l.length) : repOf (ufaCompress l x) i = repOf l i := by
  apply repOfInduct hI hi
  · intro i _ hi hroot
    by_cases hix : i = x
    · subst i
      have hr : repOf l x = x := repOfRefl hI hx hroot
      rw [repOfRefl (ufaCompressInvar hI hx) (by simpa [ufaCompress] using hx)]
      · exact hr.symm
      · rw [ufaCompress_get_eq hx]
        exact hr
    · rw [repOfRefl (ufaCompressInvar hI hx) (by simpa [ufaCompress] using hi)]
      · exact (repOfRefl hI hi hroot).symm
      · rw [ufaCompress_get_ne hi hix]
        exact hroot
  · intro i _ hi hne ih
    by_cases hix : i = x
    · subst i
      have hrne : repOf l x ≠ x := by
        intro hr
        have := repOfRoot hI hx
        rw [hr] at this
        exact hne this
      rw [repOfStep (ufaCompressInvar hI hx) (by simpa [ufaCompress] using hx)]
      · rw [ufaCompress_get_eq hx]
        apply repOfRefl (ufaCompressInvar hI hx)
        · simpa [ufaCompress] using repOfBound hI hx
        · rw [ufaCompress_get_ne (repOfBound hI hx) hrne]
          exact repOfRoot hI hx
      · rw [ufaCompress_get_eq hx]
        exact hrne
    · rw [repOfStep (ufaCompressInvar hI hx) (by simpa [ufaCompress] using hi)]
      · rw [ufaCompress_get_ne hi hix, ih, repOfIndex hI hi]
      · rw [ufaCompress_get_ne hi hix]
        exact hne

theorem ufaCompressCorrect (hI : ufaInvar l) (hx : x < l.length) :
    ufaAlpha (ufaCompress l x) = ufaAlpha l := by
  ext p
  rcases p with ⟨i, j⟩
  simp only [ufaAlpha, mem_setOf_eq, ufaCompress, List.length_set]
  change i < l.length ∧ j < l.length ∧ repOf (ufaCompress l x) i = repOf (ufaCompress l x) j ↔ _
  constructor <;> rintro ⟨hi, hj, hrep⟩
  · rw [ufaCompressRep hI hx hi, ufaCompressRep hI hx hj] at hrep
    exact ⟨hi, hj, hrep⟩
  · refine ⟨hi, hj, ?_⟩
    rw [ufaCompressRep hI hx hi, ufaCompressRep hI hx hj]
    exact hrep

/-! ## Height and rank bounds -/

private def heightOfFuel (l : List ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, i =>
      if hi : i < l.length then
        if l[i] = i then some 0 else (heightOfFuel l fuel l[i]).map Nat.succ
      else none

private theorem heightOfFuel_unique
    (h₁ : heightOfFuel l f₁ i = some n₁) (h₂ : heightOfFuel l f₂ i = some n₂) :
    n₁ = n₂ := by
  induction f₁ generalizing f₂ i n₁ n₂ with
  | zero => simp [heightOfFuel] at h₁
  | succ f₁ ih =>
      cases f₂ with
      | zero => simp [heightOfFuel] at h₂
      | succ f₂ =>
          simp only [heightOfFuel] at h₁ h₂
          split at h₁
          next hi =>
            split at h₁
            next hroot =>
              simp only [Option.some.injEq] at h₁
              subst n₁
              simp [hi, hroot] at h₂
              exact h₂
            next hroot =>
              simp only [Option.map_eq_some_iff] at h₁
              obtain ⟨m₁, hm₁, rfl⟩ := h₁
              simp [hi, hroot] at h₂
              obtain ⟨m₂, hm₂, hsucc⟩ := h₂
              calc
                m₁.succ = m₂.succ := congrArg Nat.succ (ih hm₁ hm₂)
                _ = n₂ := by simpa using hsucc
          next hi => simp [hi] at h₁

private theorem heightOfFuel_of_repOfFuel
    (h : repOfFuel l fuel i = some r) : ∃ n, heightOfFuel l fuel i = some n := by
  induction fuel generalizing i with
  | zero => simp [repOfFuel] at h
  | succ fuel ih =>
      simp only [repOfFuel] at h
      split at h
      next hi =>
        split at h
        next hroot => exact ⟨0, by simp [heightOfFuel, hi, hroot]⟩
        next hroot =>
          obtain ⟨n, hn⟩ := ih h
          exact ⟨n + 1, by simp [heightOfFuel, hi, hroot, hn]⟩
      next hi => contradiction

noncomputable def heightOf (l : List ℕ) (i : ℕ) : ℕ :=
  by
    classical
    exact if h : ∃ n fuel, heightOfFuel l fuel i = some n then Classical.choose h else 0

private theorem heightOf_eq_of_fuel (h : heightOfFuel l fuel i = some n) :
    heightOf l i = n := by
  classical
  let hex : ∃ n fuel, heightOfFuel l fuel i = some n := ⟨n, fuel, h⟩
  rw [heightOf, dif_pos hex]
  obtain ⟨fuel', hn'⟩ := Classical.choose_spec hex
  exact heightOfFuel_unique hn' h

theorem heightOfRoot (hI : ufaInvar l) (hi : i < l.length) (hroot : l[i]! = i) :
    heightOf l i = 0 := by
  have hroot' : l[i] = i := by rw [getElem!_pos] at hroot; exact hroot
  apply heightOf_eq_of_fuel (fuel := 1)
  rw [heightOfFuel]
  simp [hi, hroot']

theorem heightOfStep (hI : ufaInvar l) (hi : i < l.length) (hne : l[i]! ≠ i) :
    heightOf l i = Nat.succ (heightOf l l[i]!) := by
  have hne' : l[i] ≠ i := by rw [getElem!_pos] at hne; exact hne
  obtain ⟨r, fuel, hrun⟩ := (hI i hi).2
  cases fuel with
  | zero => simp [repOfFuel] at hrun
  | succ fuel =>
      have hchildRep : repOfFuel l fuel l[i]! = some r := by
        simpa [repOfFuel, hi, hne'] using hrun
      obtain ⟨n, hn⟩ := heightOfFuel_of_repOfFuel hchildRep
      have hn' : heightOfFuel l fuel l[i] = some n := by
        simpa [getElem!_pos, hi] using hn
      have hparent : heightOfFuel l (fuel + 1) i = some (n + 1) := by
        simp [heightOfFuel, hi, hne', hn']
      rw [heightOf_eq_of_fuel hparent, heightOf_eq_of_fuel hn]

/-- Maximum height among the vertices represented by `i`.  The source uses
`Max` of a finite set; `Finset.sup` gives the same value and totalizes the
empty component at zero. -/
noncomputable def hOf (l : List ℕ) (i : ℕ) : ℕ :=
  (Finset.range l.length).sup fun j => if repOf l j = i then heightOf l j else 0

def rankInvar (l ranks : List ℕ) : Prop :=
  l.length = ranks.length ∧
    (Finset.range l.length).sum (fun i => if l[i]! = i then ranks[i]! else 0) = l.length ∧
    ∀ i, i < l.length → l[i]! = i → 2 ^ hOf l i ≤ ranks[i]!

theorem rankAtRootLeLength (hR : rankInvar l ranks) (hI : ufaInvar l)
    (hi : i < l.length) : ranks[repOf l i]! ≤ l.length := by
  let r := repOf l i
  have hr : r < l.length := repOfBound hI hi
  have hroot : l[r]! = r := repOfRoot hI hi
  have hle : (if l[r]! = r then ranks[r]! else 0) ≤
      (Finset.range l.length).sum (fun j => if l[j]! = j then ranks[j]! else 0) := by
    exact Finset.single_le_sum (s := Finset.range l.length)
      (f := fun j => if l[j]! = j then ranks[j]! else 0)
      (fun _ _ => Nat.zero_le _) (by simpa using hr)
  rw [hR.2.1] at hle
  simpa [r, hroot] using hle

theorem heightOfLeHOf (hi : i < l.length) : heightOf l i ≤ hOf l (repOf l i) := by
  unfold hOf
  have h := Finset.le_sup (s := Finset.range l.length) (f := fun j =>
    if repOf l j = repOf l i then heightOf l j else 0) (show i ∈ Finset.range l.length by
      simpa using hi)
  simpa using h

private theorem hOf_le {l : List ℕ} {i b : ℕ}
    (h : ∀ j, j < l.length → repOf l j = i → heightOf l j ≤ b) : hOf l i ≤ b := by
  unfold hOf
  apply Finset.sup_le
  intro j hj
  simp only [Finset.mem_range] at hj
  split
  · exact h j hj (by assumption)
  · exact Nat.zero_le _

theorem heightOfCompress (hI : ufaInvar l) (hi : i < l.length) (hj : j < l.length) :
    heightOf (ufaCompress l j) i ≤ heightOf l i := by
  apply repOfInduct hI hi
  · intro i _ hi hroot
    have hold : heightOf l i = 0 := heightOfRoot hI hi hroot
    have hroot' : (ufaCompress l j)[i]! = i := by
      by_cases hij : i = j
      · subst i
        rw [ufaCompress_get_eq hj, repOfRefl hI hj hroot]
      · rw [ufaCompress_get_ne hi hij]
        exact hroot
    have hnew : heightOf (ufaCompress l j) i = 0 :=
      heightOfRoot (ufaCompressInvar hI hj) (by simpa [ufaCompress] using hi) hroot'
    omega
  · intro i _ hi hne ih
    have hold := heightOfStep hI hi hne
    by_cases hij : i = j
    · subst i
      have hrne : repOf l j ≠ j := by
        intro hr
        have hroot := repOfRoot hI hj
        rw [hr] at hroot
        exact hne hroot
      have hnewStep := heightOfStep (ufaCompressInvar hI hj)
        (by simpa [ufaCompress] using hj) (by
          rw [ufaCompress_get_eq hj]
          exact hrne)
      have hnewRoot : heightOf (ufaCompress l j) (repOf l j) = 0 := by
        apply heightOfRoot (ufaCompressInvar hI hj)
        · simpa [ufaCompress] using repOfBound hI hj
        · rw [ufaCompress_get_ne (repOfBound hI hj) hrne]
          exact repOfRoot hI hj
      rw [ufaCompress_get_eq hj, hnewRoot] at hnewStep
      omega
    · have hnewStep := heightOfStep (ufaCompressInvar hI hj)
        (by simpa [ufaCompress] using hi) (by
          rw [ufaCompress_get_ne hi hij]
          exact hne)
      rw [ufaCompress_get_ne hi hij] at hnewStep
      omega

theorem heightOfUnionOnPath (hI : ufaInvar l) (hi : i < l.length)
    (hx : x < l.length) (hy : y < l.length) (hpath : repOf l i = repOf l x) :
    heightOf (ufaUnion l x y) i ≤ Nat.succ (heightOf l i) := by
  revert hpath
  apply repOfInduct hI hi
  · intro i _ hi hroot
    intro hpath
    have hri : repOf l i = i := repOfRefl hI hi hroot
    have hold : heightOf l i = 0 := heightOfRoot hI hi hroot
    by_cases hir : i = repOf l x
    · subst i
      by_cases hxy : repOf l x = repOf l y
      · have hnewRoot : (ufaUnion l x y)[repOf l x]! = repOf l x := by
          rw [ufaUnion_get_root hI hx, ← hxy]
        have hnew := heightOfRoot (ufaUnionInvar hI hx hy)
          (by simpa [ufaUnion] using repOfBound hI hx) hnewRoot
        omega
      · have hstep := heightOfStep (ufaUnionInvar hI hx hy)
          (by simpa [ufaUnion] using repOfBound hI hx) (by
            rw [ufaUnion_get_root hI hx]
            exact Ne.symm hxy)
        have hrootY : heightOf (ufaUnion l x y) (repOf l y) = 0 := by
          apply heightOfRoot (ufaUnionInvar hI hx hy)
          · simpa [ufaUnion] using repOfBound hI hy
          · rw [ufaUnion_get_ne (repOfBound hI hy) (Ne.symm hxy)]
            exact repOfRoot hI hy
        rw [ufaUnion_get_root hI hx, hrootY] at hstep
        omega
    · have hnewRoot : (ufaUnion l x y)[i]! = i := by
        rw [ufaUnion_get_ne hi hir]
        exact hroot
      have hnew := heightOfRoot (ufaUnionInvar hI hx hy)
        (by simpa [ufaUnion] using hi) hnewRoot
      omega
  · intro i _ hi hne ih
    intro hpath
    have hir : i ≠ repOf l x := by
      intro hir
      subst i
      exact hne (repOfRoot hI hx)
    have hnewStep := heightOfStep (ufaUnionInvar hI hx hy)
      (by simpa [ufaUnion] using hi) (by
        rw [ufaUnion_get_ne hi hir]
        exact hne)
    have holdStep := heightOfStep hI hi hne
    rw [ufaUnion_get_ne hi hir] at hnewStep
    have hchildPath : repOf l l[i]! = repOf l x := by
      rw [repOfIndex hI hi]
      exact hpath
    have hchild := ih hchildPath
    omega

theorem heightOfUnionOffPath (hI : ufaInvar l) (hi : i < l.length)
    (hx : x < l.length) (hy : y < l.length) (hoff : repOf l i ≠ repOf l x) :
    heightOf (ufaUnion l x y) i = heightOf l i := by
  revert hoff
  apply repOfInduct hI hi
  · intro i _ hi hroot
    intro hoff
    have hri : repOf l i = i := repOfRefl hI hi hroot
    have hir : i ≠ repOf l x := by simpa [hri] using hoff
    apply (heightOfRoot (ufaUnionInvar hI hx hy) (by simpa [ufaUnion] using hi) (by
      rw [ufaUnion_get_ne hi hir]
      exact hroot)).trans
    exact (heightOfRoot hI hi hroot).symm
  · intro i _ hi hne ih
    intro hoff
    have hir : i ≠ repOf l x := by
      intro hir
      subst i
      exact hne (repOfRoot hI hx)
    have hnewStep := heightOfStep (ufaUnionInvar hI hx hy)
      (by simpa [ufaUnion] using hi) (by
        rw [ufaUnion_get_ne hi hir]
        exact hne)
    have holdStep := heightOfStep hI hi hne
    rw [ufaUnion_get_ne hi hir] at hnewStep
    have hchildOff : repOf l l[i]! ≠ repOf l x := by
      rw [repOfIndex hI hi]
      exact hoff
    rw [hnewStep, holdStep, ih hchildOff]

theorem heightOfUnion (hI : ufaInvar l) (hi : i < l.length)
    (hx : x < l.length) (hy : y < l.length) :
    heightOf (ufaUnion l x y) i ≤ Nat.succ (heightOf l i) := by
  by_cases hpath : repOf l i = repOf l x
  · exact heightOfUnionOnPath hI hi hx hy hpath
  · rw [heightOfUnionOffPath hI hi hx hy hpath]
    omega

theorem hOfCompress (hI : ufaInvar l) (hj : j < l.length) :
    hOf (ufaCompress l j) i ≤ hOf l i := by
  apply hOf_le
  intro k hk hrep
  have hk' : k < l.length := by simpa [ufaCompress] using hk
  have hrep' : repOf l k = i := by
    rw [ufaCompressRep hI hj hk'] at hrep
    exact hrep
  exact (heightOfCompress hI hk' hj).trans (hrep' ▸ heightOfLeHOf hk')

theorem hOfUnionUntouched (hI : ufaInvar l) (hx : x < l.length) (hy : y < l.length)
    (hi : i < l.length) (hroot : l[i]! = i)
    (hix : i ≠ repOf l x) (hiy : i ≠ repOf l y) :
    hOf (ufaUnion l x y) i = hOf l i := by
  unfold hOf
  rw [show (ufaUnion l x y).length = l.length by simp [ufaUnion]]
  apply Finset.sup_congr rfl
  intro j hj
  have hj' : j < l.length := by simpa using hj
  rw [ufaUnionRep hI hx hy hj']
  by_cases hjx : repOf l j = repOf l x
  · rw [if_pos hjx]
    have hji : repOf l j ≠ i := by intro h; exact hix (h.symm.trans hjx)
    simp [Ne.symm hiy, hji]
  · rw [if_neg hjx, heightOfUnionOffPath hI hj' hx hy hjx]

theorem hOfUnionId (hI : ufaInvar l) (hx : x < l.length) (hy : y < l.length)
    (hi : i < l.length) (hroot : repOf l i = i) (hiy : i = repOf l y)
    (hxy : repOf l y = repOf l x) :
    hOf (ufaUnion l x y) i = hOf l i := by
  have hu : ufaUnion l x y = l := by
    unfold ufaUnion
    apply List.ext_getElem
    · simp
    · intro j hj₁ hj₂
      by_cases hj : j = repOf l x
      · subst j
        rw [List.getElem_set, if_pos rfl]
        have hr := repOfRoot hI hx
        rw [getElem!_pos] at hr
        · exact hxy.trans hr.symm
        · exact repOfBound hI hx
      · rw [List.getElem_set, if_neg (Ne.symm hj)]
  rw [hu]

theorem hOfUnionTouched (hI : ufaInvar l) (hx : x < l.length) (hy : y < l.length)
    (hi : i < l.length) (hroot : repOf l i = i) (hiy : i = repOf l y)
    (hxy : repOf l y ≠ repOf l x) :
    hOf (ufaUnion l x y) i ≤
      max (hOf l (repOf l y)) (Nat.succ (hOf l (repOf l x))) := by
  apply hOf_le
  intro j hj hrep
  have hj' : j < l.length := by simpa [ufaUnion] using hj
  have hrep' := hrep
  rw [ufaUnionRep hI hx hy hj'] at hrep'
  by_cases hjx : repOf l j = repOf l x
  · have hheight := heightOfUnionOnPath hI hj' hx hy hjx
    have hold := heightOfLeHOf hj'
    rw [hjx] at hold
    exact hheight.trans ((Nat.succ_le_succ hold).trans (le_max_right _ _))
  · rw [if_neg hjx] at hrep'
    have hheight := heightOfUnionOffPath hI hj' hx hy hjx
    have hold := heightOfLeHOf hj'
    rw [hrep', hiy] at hold
    rw [hheight]
    exact hold.trans (le_max_left _ _)

theorem heightPowLeLength (hR : rankInvar l ranks) (hI : ufaInvar l)
    (hi : i < l.length) : 2 ^ heightOf l i ≤ l.length := by
  have hh : heightOf l i ≤ hOf l (repOf l i) := heightOfLeHOf hi
  have hp : 2 ^ heightOf l i ≤ 2 ^ hOf l (repOf l i) :=
    Nat.pow_le_pow_right (by omega) hh
  have hrank : 2 ^ hOf l (repOf l i) ≤ ranks[repOf l i]! :=
    hR.2.2 (repOf l i) (repOfBound hI hi) (repOfRoot hI hi)
  exact hp.trans (hrank.trans (rankAtRootLeLength hR hI hi))

noncomputable def heightUb (n : ℕ) : ℕ := ⌈Real.logb 2 (n : ℝ)⌉₊

theorem heightUbThetaLog :
    (fun n : ℕ => ((heightUb n : ℕ) : ℝ)) =Θ[atTop]
      fun n => Real.log (n : ℝ) := by
  simpa [heightUb] using
    (abcdLog (a := 0) (b := 1) (c := 1) (d := 0) (by positivity) (by norm_num)
      (by norm_num) (by omega))

theorem heightOfLeHeightUb (hR : rankInvar l ranks) (hI : ufaInvar l)
    (hi : i < l.length) : heightOf l i ≤ heightUb l.length := by
  have hp := heightPowLeLength hR hI hi
  have hnpos : 0 < (l.length : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hi)
  have hrealPow : (2 : ℝ) ^ (heightOf l i : ℝ) ≤ (l.length : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hp
  have hlog : (heightOf l i : ℝ) ≤ Real.logb 2 (l.length : ℝ) :=
    (Real.le_logb_iff_rpow_le (b := 2) (by norm_num) hnpos).2 hrealPow
  have hceil := hlog.trans (Nat.le_ceil (Real.logb 2 (l.length : ℝ)))
  have hnat : heightOf l i ≤ ⌈Real.logb 2 (l.length : ℝ)⌉₊ := by
    exact_mod_cast hceil
  exact hnat

/-! ## Executable sanity probes for the authored totalization -/

private example : heightOf [0] 0 = 0 :=
  heightOf_eq_of_fuel (show heightOfFuel [0] 1 0 = some 0 by decide)

private example : heightOf [0, 0, 1] 2 = 2 :=
  heightOf_eq_of_fuel (show heightOfFuel [0, 0, 1] 3 2 = some 2 by decide)

private example : heightOf [0, 0, 0] 2 = 1 :=
  heightOf_eq_of_fuel (show heightOfFuel [0, 0, 0] 2 2 = some 1 by decide)

private example : repOf [0] 0 = 0 :=
  repOf_eq_of_fuel (show repOfFuel [0] 1 0 = some 0 by decide)

private example : repOf [0, 0] 1 = 0 :=
  repOf_eq_of_fuel (show repOfFuel [0, 0] 2 1 = some 0 by decide)

private example : repOf [0, 0, 1] 2 = 0 :=
  repOf_eq_of_fuel (show repOfFuel [0, 0, 1] 3 2 = some 0 by decide)

private example : ufaCompress [0, 0, 1] 2 = [0, 0, 0] := by
  have hr : repOf [0, 0, 1] 2 = 0 :=
    repOf_eq_of_fuel (show repOfFuel [0, 0, 1] 3 2 = some 0 by decide)
  simp [ufaCompress, hr]

private example : ufaUnion [0, 1] 0 1 = [1, 1] := by
  have hx : repOf [0, 1] 0 = 0 :=
    repOf_eq_of_fuel (show repOfFuel [0, 1] 1 0 = some 0 by decide)
  have hy : repOf [0, 1] 1 = 1 :=
    repOf_eq_of_fuel (show repOfFuel [0, 1] 1 1 = some 1 by decide)
  simp [ufaUnion, hx, hy]

private example : ufaUnion [0, 1] 1 0 = [0, 0] := by
  have hx : repOf [0, 1] 1 = 1 :=
    repOf_eq_of_fuel (show repOfFuel [0, 1] 1 1 = some 1 by decide)
  have hy : repOf [0, 1] 0 = 0 :=
    repOf_eq_of_fuel (show repOfFuel [0, 1] 1 0 = some 0 by decide)
  simp [ufaUnion, hx, hy]

/-! ## Kernel-three guards for the completed boundary -/

/-- info: 'Lax13Proofs.Refine.Iicf.UnionFind.perSupsetUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms perSupsetUnion

/-- info: 'Lax13Proofs.Refine.Iicf.UnionFind.repOfStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms repOfStep

/-- info: 'Lax13Proofs.Refine.Iicf.UnionFind.ufaUnionCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ufaUnionCorrect

/-- info: 'Lax13Proofs.Refine.Iicf.UnionFind.ufaCompressCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ufaCompressCorrect

/-- info: 'Lax13Proofs.Refine.Iicf.UnionFind.heightOfUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms heightOfUnion

/-- info: 'Lax13Proofs.Refine.Iicf.UnionFind.heightOfLeHeightUb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms heightOfLeHeightUb

end Lax13Proofs.Refine.Iicf.UnionFind
