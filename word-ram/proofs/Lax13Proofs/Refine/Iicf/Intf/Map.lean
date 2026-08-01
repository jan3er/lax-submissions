import Lax13Proofs.Refine.Iicf.Intf.Set

/-!
# Map interface

Source-faithful interface leaf for `IICF/Intf/IICF_Map.thy` at
`isabelle_llvm_time` commit `42dd7f5`.  Maps are partial functions
`κ → Option ν`; this layer contains their relation and abstract operations,
but no concrete map implementation.

## Source table

| Source item | Lean item | Accounting |
|---|---|---|
| `map_rel` | `mapRel` | pointwise `K → optionRel V`, concrete support in `Domain K`, abstract support in `Range K` |
| `bi_total_map_rel_eq` | `mapRel_eq_funRel_of_biTotal` | both key-totality hypotheses retained |
| `map_rel_Id` | `mapRel_diagonal` | diagonal relation preserved |
| `map_rel_empty{1,2}_simp` | `mapRel_empty_left/right` | both directions retained |
| `map_rel_obtain{1,2}` | `mapRel_obtain_right/left` | witnesses and key/value relations retained |
| `param_dom` | `mapRel_dom` | result uses the shared bidirectional `setRel` |
| `map_empty` | `op_map_empty` | cost-silent `returnT` |
| `map_is_empty` | `op_map_is_empty` | cost-silent `returnT` |
| `map_update` | `op_map_update` | `SingleValued K` and its converse |
| `map_delete` | `op_map_delete` | `SingleValued K` and its converse |
| `map_lookup` | `op_map_lookup` | returns `Option` under `optionRel V` |
| `map_the_lookup` | `op_map_the_lookup` | paired input, non-`None` precondition, unique zero-cost specification |
| `map_contains_key` | `op_map_contains_key` | domain membership Boolean |
| `pat_map_*` | no separate declarations | Isabelle term-pattern rewrites are represented by explicit `op_map_*` definitions and registrations |
| `map_custom_empty` locale | no separate locale | a concrete custom empty registers directly against `op_map_empty` with `sepref_decl_impl` |

The source contains an alternative `map_rel` with value-range support
constraints inside a comment.  Those constraints are intentionally not
added here: the active source definition constrains keys only.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

variable {κ κ' ν ν' : Type}

/-! ## Map relation -/

/-- Keys at which a partial map is defined, the source's `dom`. -/
def mapDom (m : κ → Option ν) : Set κ := {k | m k ≠ none}

@[simp] theorem mem_mapDom_iff {m : κ → Option ν} {k : κ} :
    k ∈ mapDom m ↔ m k ≠ none := Iff.rfl

/-- The source's relation `Domain`. -/
def relationDomain (R : Set (κ × κ')) : Set κ := {k | ∃ l, (k, l) ∈ R}

/-- The source's relation `Range`. -/
def relationRange (R : Set (κ × κ')) : Set κ' := {l | ∃ k, (k, l) ∈ R}

/-- Every concrete/left key has an abstract/right mate. -/
def LeftTotal (R : Set (κ × κ')) : Prop := ∀ k, ∃ l, (k, l) ∈ R

/-- Every abstract/right key has a concrete/left mate. -/
def RightTotal (R : Set (κ × κ')) : Prop := ∀ l, ∃ k, (k, l) ∈ R

/-- Active source definition of `⟨K,V⟩map_rel`. -/
def mapRel (K : Set (κ × κ')) (V : Set (ν × ν')) :
    Set ((κ → Option ν) × (κ' → Option ν')) :=
  {p | (p.1, p.2) ∈ K →ᵣ optionRel V ∧
    mapDom p.1 ⊆ relationDomain K ∧ mapDom p.2 ⊆ relationRange K}

@[simp] theorem mem_mapRel_iff {K : Set (κ × κ')} {V : Set (ν × ν')}
    {m : κ → Option ν} {n : κ' → Option ν'} :
    (m, n) ∈ mapRel K V ↔
      (m, n) ∈ K →ᵣ optionRel V ∧
      mapDom m ⊆ relationDomain K ∧ mapDom n ⊆ relationRange K := Iff.rfl

theorem optionRel_none_iff {V : Set (ν × ν')} {x : Option ν} {y : Option ν'}
    (h : (x, y) ∈ optionRel V) : (x = none) = (y = none) := by
  apply propext
  cases x <;> cases y <;> simp_all

theorem optionRel_obtain_right {V : Set (ν × ν')} {x : Option ν} {w : ν'}
    (h : (x, some w) ∈ optionRel V) :
    ∃ v, x = some v ∧ (v, w) ∈ V := by
  cases x with
  | none => simp at h
  | some v => exact ⟨v, rfl, mem_optionRel_some_some.mp h⟩

theorem optionRel_obtain_left {V : Set (ν × ν')} {v : ν} {y : Option ν'}
    (h : (some v, y) ∈ optionRel V) :
    ∃ w, y = some w ∧ (v, w) ∈ V := by
  cases y with
  | none => simp at h
  | some w => exact ⟨w, rfl, mem_optionRel_some_some.mp h⟩

theorem optionRel_diagonal_refl (x : Option ν) :
    (x, x) ∈ optionRel (Set.diagonal ν) := by
  cases x with
  | none => exact mem_optionRel_none_none
  | some v => exact mem_optionRel_some_some.mpr rfl

/-- Under bi-total keys the support clauses are automatic. -/
theorem mapRel_eq_funRel_of_biTotal (K : Set (κ × κ')) (V : Set (ν × ν'))
    (hL : LeftTotal K) (hR : RightTotal K) :
    mapRel K V = (K →ᵣ optionRel V) := by
  apply Set.Subset.antisymm
  · rintro ⟨m, n⟩ h
    exact h.1
  · rintro ⟨m, n⟩ h
    exact ⟨h, fun k _ => hL k, fun l _ => hR l⟩

/-- Source `map_rel_Id`. -/
@[simp] theorem mapRel_diagonal :
    mapRel (Set.diagonal κ) (Set.diagonal ν) = Set.diagonal (κ → Option ν) := by
  apply Set.Subset.antisymm
  · rintro ⟨m, n⟩ h
    change m = n
    funext k
    have ho := h.1 k k (show (k, k) ∈ Set.diagonal κ from rfl)
    cases hm : m k <;> cases hn : n k <;> simp_all
  · rintro ⟨m, n⟩ h
    change m = n at h
    subst n
    refine ⟨?_, ?_, ?_⟩
    · intro k l hkl
      change k = l at hkl
      subst l
      exact optionRel_diagonal_refl (m k)
    · intro k _
      exact ⟨k, rfl⟩
    · intro k _
      exact ⟨k, rfl⟩

/-- Empty partial map. -/
def mapEmpty : κ → Option ν := fun _ => none

theorem mapRel_empty (K : Set (κ × κ')) (V : Set (ν × ν')) :
    ((mapEmpty : κ → Option ν), (mapEmpty : κ' → Option ν')) ∈ mapRel K V := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ _
    exact mem_optionRel_none_none
  · intro k hk
    exact absurd rfl hk
  · intro l hl
    exact absurd rfl hl

/-- Source `map_rel_empty1_simp`. -/
theorem mapRel_empty_left {K : Set (κ × κ')} {V : Set (ν × ν')}
    {n : κ' → Option ν'} :
    (((mapEmpty : κ → Option ν), n) ∈ mapRel K V) = (n = mapEmpty) := by
  apply propext
  constructor
  · intro h
    funext l
    by_cases hn : n l = none
    · exact hn
    · obtain ⟨k, hk⟩ := h.2.2 hn
      exact (optionRel_none_iff (h.1 k l hk)).mp rfl
  · rintro rfl
    exact mapRel_empty K V

/-- Source `map_rel_empty2_simp`. -/
theorem mapRel_empty_right {K : Set (κ × κ')} {V : Set (ν × ν')}
    {m : κ → Option ν} :
    ((m, (mapEmpty : κ' → Option ν')) ∈ mapRel K V) = (m = mapEmpty) := by
  apply propext
  constructor
  · intro h
    funext k
    by_cases hm : m k = none
    · exact hm
    · obtain ⟨l, hk⟩ := h.2.1 hm
      exact (optionRel_none_iff (h.1 k l hk)).mpr rfl
  · rintro rfl
    exact mapRel_empty K V

/-- Source `map_rel_obtain1`: obtain a concrete entry from an abstract one. -/
theorem mapRel_obtain_right {K : Set (κ × κ')} {V : Set (ν × ν')}
    {m : κ → Option ν} {n : κ' → Option ν'}
    (hmn : (m, n) ∈ mapRel K V) {l : κ'} {w : ν'} (hn : n l = some w) :
    ∃ k v, m k = some v ∧ (k, l) ∈ K ∧ (v, w) ∈ V := by
  have hl : l ∈ mapDom n := by simp [mapDom, hn]
  obtain ⟨k, hk⟩ := hmn.2.2 hl
  obtain ⟨v, hmv, hvw⟩ := optionRel_obtain_right (by simpa [hn] using hmn.1 k l hk)
  exact ⟨k, v, hmv, hk, hvw⟩

/-- Source `map_rel_obtain2`: obtain an abstract entry from a concrete one. -/
theorem mapRel_obtain_left {K : Set (κ × κ')} {V : Set (ν × ν')}
    {m : κ → Option ν} {n : κ' → Option ν'}
    (hmn : (m, n) ∈ mapRel K V) {k : κ} {v : ν} (hm : m k = some v) :
    ∃ l w, n l = some w ∧ (k, l) ∈ K ∧ (v, w) ∈ V := by
  have hkdom : k ∈ mapDom m := by simp [mapDom, hm]
  obtain ⟨l, hk⟩ := hmn.2.1 hkdom
  obtain ⟨w, hnw, hvw⟩ := optionRel_obtain_left (by simpa [hm] using hmn.1 k l hk)
  exact ⟨l, w, hnw, hk, hvw⟩

/-- Source `param_dom`. -/
theorem mapRel_dom {K : Set (κ × κ')} {V : Set (ν × ν')}
    {m : κ → Option ν} {n : κ' → Option ν'} (hmn : (m, n) ∈ mapRel K V) :
    (mapDom m, mapDom n) ∈ setRel K := by
  constructor
  · intro k hk
    cases hm : m k with
    | none => exact absurd hm hk
    | some v =>
        obtain ⟨l, w, hn, hkl, -⟩ := mapRel_obtain_left hmn hm
        exact ⟨l, by simp [mapDom, hn], hkl⟩
  · intro l hl
    cases hn : n l with
    | none => exact absurd hn hl
    | some w =>
        obtain ⟨k, v, hm, hkl, -⟩ := mapRel_obtain_right hmn hn
        exact ⟨k, by simp [mapDom, hm], hkl⟩

/-! ## Preservation by the two mutating abstract operations -/

noncomputable def mapUpdate (m : κ → Option ν) (k : κ) (v : ν) : κ → Option ν := by
  classical
  exact Function.update m k (some v)

noncomputable def mapDelete (m : κ → Option ν) (k : κ) : κ → Option ν := by
  classical
  exact Function.update m k none

theorem mapRel_update {K : Set (κ × κ')} {V : Set (ν × ν')}
    (hK : SingleValued K) (hKc : SingleValued (relConverse K))
    {k : κ} {l : κ'} (hkl : (k, l) ∈ K) {v : ν} {w : ν'} (hvw : (v, w) ∈ V)
    {m : κ → Option ν} {n : κ' → Option ν'} (hmn : (m, n) ∈ mapRel K V) :
    (mapUpdate m k v, mapUpdate n l w) ∈ mapRel K V := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x = k
    · subst x
      have hy : y = l := hK k y l hxy hkl
      subst y
      simpa [mapUpdate] using (mem_optionRel_some_some.mpr hvw)
    · have hy : y ≠ l := by
        intro hyl
        subst y
        exact hx (hKc l x k hxy hkl)
      simpa [mapUpdate, Function.update_of_ne hx, Function.update_of_ne hy] using
        hmn.1 x y hxy
  · intro x hx
    by_cases hxk : x = k
    · subst x
      exact ⟨l, hkl⟩
    · apply hmn.2.1
      simpa [mapDom, mapUpdate, Function.update_of_ne hxk] using hx
  · intro y hy
    by_cases hyl : y = l
    · subst y
      exact ⟨k, hkl⟩
    · apply hmn.2.2
      simpa [mapDom, mapUpdate, Function.update_of_ne hyl] using hy

theorem mapRel_delete {K : Set (κ × κ')} {V : Set (ν × ν')}
    (hK : SingleValued K) (hKc : SingleValued (relConverse K))
    {k : κ} {l : κ'} (hkl : (k, l) ∈ K)
    {m : κ → Option ν} {n : κ' → Option ν'} (hmn : (m, n) ∈ mapRel K V) :
    (mapDelete m k, mapDelete n l) ∈ mapRel K V := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x = k
    · subst x
      have hy : y = l := hK k y l hxy hkl
      subst y
      simp [mapDelete]
    · have hy : y ≠ l := by
        intro hyl
        subst y
        exact hx (hKc l x k hxy hkl)
      simpa [mapDelete, Function.update_of_ne hx, Function.update_of_ne hy] using
        hmn.1 x y hxy
  · intro x hx
    by_cases hxk : x = k
    · subst x
      simp [mapDom, mapDelete] at hx
    · apply hmn.2.1
      simpa [mapDom, mapDelete, Function.update_of_ne hxk] using hx
  · intro y hy
    by_cases hyl : y = l
    · subst y
      simp [mapDom, mapDelete] at hy
    · apply hmn.2.2
      simpa [mapDom, mapDelete, Function.update_of_ne hyl] using hy

theorem mapRel_lookup {K : Set (κ × κ')} {V : Set (ν × ν')}
    {k : κ} {l : κ'} (hkl : (k, l) ∈ K)
    {m : κ → Option ν} {n : κ' → Option ν'} (hmn : (m, n) ∈ mapRel K V) :
    (m k, n l) ∈ optionRel V := hmn.1 k l hkl

theorem mapRel_contains {K : Set (κ × κ')} {V : Set (ν × ν')}
    {k : κ} {l : κ'} (hkl : (k, l) ∈ K)
    {m : κ → Option ν} {n : κ' → Option ν'} (hmn : (m, n) ∈ mapRel K V) :
    (k ∈ mapDom m) = (l ∈ mapDom n) := by
  exact congrArg Not (optionRel_none_iff (mapRel_lookup hkl hmn))

theorem optionSpec_eq_returnT {o : Option ν} {v : ν} (h : o = some v) :
    NRest.spec (fun x => o = some x) (fun _ => (0 : ECost)) = NRest.returnT v := by
  subst o
  rw [NRest.spec, NRest.returnT, NRest.rest_inj_iff]
  funext x
  by_cases hx : x = v
  · subst x
    simp [NRest.single]
  · have hne : some v ≠ some x := fun h => hx (Option.some.inj h).symm
    simp [NRest.single, hx, hne]

/-! ## Nominal interface and relation inference -/

sepref_decl_intf (κ, ν) MapI is κ → Option ν

@[intf_of_rel] theorem mapRel_intf (K : Set (κ × κ')) (V : Set (ν × ν')) :
    intfOfRel (mapRel K V) (MapI κ' ν') := trivial

#guard_rel_interface (mapRel (Set.diagonal ℕ) (Set.diagonal Bool)) is MapI ℕ Bool

/-! ## Seven source operations -/

sepref_decl_op map_empty (κ ν : Type) : NRest (κ → Option ν) ECost :=
    NRest.returnT mapEmpty
  interface := ∀ κ ν : Type, NRest (MapI κ ν) ECost
  precondition := True
  parametricity : ∀ {κ' ν' : Type} (K : Set (κ × κ')) (V : Set (ν × ν')),
      (op_map_empty κ ν, op_map_empty κ' ν') ∈ NRest.nrestRel (mapRel K V) := by
    intro κ' ν' K V
    exact NRest.param_returnT (mapRel_empty K V)

sepref_decl_op map_is_empty (κ ν : Type) : (κ → Option ν) → NRest Bool ECost :=
    fun m => NRest.returnT (propBool (m = mapEmpty))
  interface := ∀ κ ν : Type, MapI κ ν → NRest Bool ECost
  precondition := fun _ : κ → Option ν => True
  parametricity : ∀ {κ' ν' : Type} (K : Set (κ × κ')) (V : Set (ν × ν')),
      ((op_map_is_empty κ ν, op_map_is_empty κ' ν') ∈
        fref (fun _ : κ' → Option ν' => True) (mapRel K V)
          (fun _ => NRest.nrestRel (Set.diagonal Bool))) := by
    intro κ' ν' K V m n _ hmn
    have h : (m = mapEmpty) = (n = mapEmpty) := by
      apply propext
      constructor
      · rintro rfl
        exact mapRel_empty_left.mp hmn
      · rintro rfl
        exact mapRel_empty_right.mp hmn
    exact NRest.param_returnT (propBool_congr h)

sepref_decl_op map_update (κ ν : Type) : κ → ν → (κ → Option ν) → NRest (κ → Option ν) ECost :=
    fun k v m => NRest.returnT (mapUpdate m k v)
  interface := ∀ κ ν : Type, κ → ν → MapI κ ν → NRest (MapI κ ν) ECost
  precondition := fun _ : κ => fun _ : ν => fun _ : κ → Option ν => True
  parametricity : ∀ {κ' ν' : Type} (K : Set (κ × κ')) (V : Set (ν × ν')),
      SingleValued K → SingleValued (relConverse K) →
      ((op_map_update κ ν, op_map_update κ' ν') ∈
        fref (fun _ : κ' => True) K
          (fun _ => V →ᵣ mapRel K V →ᵣ NRest.nrestRel (mapRel K V))) := by
    intro κ' ν' K V hK hKc k l _ hkl v w hvw m n hmn
    exact NRest.param_returnT (mapRel_update hK hKc hkl hvw hmn)

sepref_decl_op map_delete (κ ν : Type) : κ → (κ → Option ν) → NRest (κ → Option ν) ECost :=
    fun k m => NRest.returnT (mapDelete m k)
  interface := ∀ κ ν : Type, κ → MapI κ ν → NRest (MapI κ ν) ECost
  precondition := fun _ : κ => fun _ : κ → Option ν => True
  parametricity : ∀ {κ' ν' : Type} (K : Set (κ × κ')) (V : Set (ν × ν')),
      SingleValued K → SingleValued (relConverse K) →
      ((op_map_delete κ ν, op_map_delete κ' ν') ∈
        fref (fun _ : κ' => True) K
          (fun _ => mapRel K V →ᵣ NRest.nrestRel (mapRel K V))) := by
    intro κ' ν' K V hK hKc k l _ hkl m n hmn
    exact NRest.param_returnT (mapRel_delete hK hKc hkl hmn)

sepref_decl_op map_lookup (κ ν : Type) : κ → (κ → Option ν) → NRest (Option ν) ECost :=
    fun k m => NRest.returnT (m k)
  interface := ∀ κ ν : Type, κ → MapI κ ν → NRest (Option ν) ECost
  precondition := fun _ : κ => fun _ : κ → Option ν => True
  parametricity : ∀ {κ' ν' : Type} (K : Set (κ × κ')) (V : Set (ν × ν')),
      ((op_map_lookup κ ν, op_map_lookup κ' ν') ∈
        fref (fun _ : κ' => True) K
          (fun _ => mapRel K V →ᵣ NRest.nrestRel (optionRel V))) := by
    intro κ' ν' K V k l _ hkl m n hmn
    exact NRest.param_returnT (mapRel_lookup hkl hmn)

sepref_decl_op map_the_lookup (κ ν : Type) :
    (κ × (κ → Option ν)) → NRest ν ECost :=
    fun p => NRest.bindT (NRest.assert (p.2 p.1 ≠ none)) fun _ =>
      NRest.spec (fun v => p.2 p.1 = some v) (fun _ => 0)
  interface := ∀ κ ν : Type, (κ × MapI κ ν) → NRest ν ECost
  precondition := fun p : κ × (κ → Option ν) => p.2 p.1 ≠ none
  parametricity : ∀ {κ' ν' : Type} (K : Set (κ × κ')) (V : Set (ν × ν')),
      ((op_map_the_lookup κ ν, op_map_the_lookup κ' ν') ∈
        fref (fun p : κ' × (κ' → Option ν') => p.2 p.1 ≠ none)
          (K ×ᵣ mapRel K V) (fun _ => NRest.nrestRel V)) := by
    intro κ' ν' K V p q hq hpq
    obtain ⟨hkl, hmn⟩ := hpq
    have hopt := mapRel_lookup hkl hmn
    have hp : p.2 p.1 ≠ none := by
      intro hpnone
      exact hq ((optionRel_none_iff hopt).mp hpnone)
    cases hpv : p.2 p.1 with
    | none => exact absurd hpv hp
    | some v =>
      obtain ⟨w, hqw, hvw⟩ := optionRel_obtain_left (by simpa [hpv] using hopt)
      simp only [op_map_the_lookup, NRest.assert_pos hp, NRest.assert_pos hq,
        NRest.returnT_bindT]
      rw [optionSpec_eq_returnT hpv, optionSpec_eq_returnT hqw]
      exact NRest.param_returnT hvw

sepref_decl_op map_contains_key (κ ν : Type) : κ → (κ → Option ν) → NRest Bool ECost :=
    fun k m => NRest.returnT (propBool (k ∈ mapDom m))
  interface := ∀ κ ν : Type, κ → MapI κ ν → NRest Bool ECost
  precondition := fun _ : κ => fun _ : κ → Option ν => True
  parametricity : ∀ {κ' ν' : Type} (K : Set (κ × κ')) (V : Set (ν × ν')),
      ((op_map_contains_key κ ν, op_map_contains_key κ' ν') ∈
        fref (fun _ : κ' => True) K
          (fun _ => mapRel K V →ᵣ NRest.nrestRel (Set.diagonal Bool))) := by
    intro κ' ν' K V k l _ hkl m n hmn
    exact NRest.param_returnT (propBool_congr (mapRel_contains hkl hmn))

/-! ## Source-shaped diagonal, registration, and database gates -/

private theorem diagonal_converse_singleValued_map :
    SingleValued (relConverse (Set.diagonal ℕ)) := by
  rintro b a a' hba hba'
  change a = b at hba
  change a' = b at hba'
  exact hba.trans hba'.symm

private example :
    (op_map_empty ℕ Bool, op_map_empty ℕ Bool) ∈
      NRest.nrestRel (mapRel (Set.diagonal ℕ) (Set.diagonal Bool)) :=
  op_map_empty_fref ℕ Bool (Set.diagonal ℕ) (Set.diagonal Bool)

private example :
    (op_map_is_empty ℕ Bool, op_map_is_empty ℕ Bool) ∈
      fref (fun _ : ℕ → Option Bool => True)
        (mapRel (Set.diagonal ℕ) (Set.diagonal Bool))
        (fun _ => NRest.nrestRel (Set.diagonal Bool)) :=
  op_map_is_empty_fref ℕ Bool (Set.diagonal ℕ) (Set.diagonal Bool)

private example :
    (op_map_update ℕ Bool, op_map_update ℕ Bool) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => Set.diagonal Bool →ᵣ
          mapRel (Set.diagonal ℕ) (Set.diagonal Bool) →ᵣ
            NRest.nrestRel (mapRel (Set.diagonal ℕ) (Set.diagonal Bool))) :=
  op_map_update_fref ℕ Bool (Set.diagonal ℕ) (Set.diagonal Bool)
    singleValued_diagonal diagonal_converse_singleValued_map

private example :
    (op_map_delete ℕ Bool, op_map_delete ℕ Bool) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => mapRel (Set.diagonal ℕ) (Set.diagonal Bool) →ᵣ
          NRest.nrestRel (mapRel (Set.diagonal ℕ) (Set.diagonal Bool))) :=
  op_map_delete_fref ℕ Bool (Set.diagonal ℕ) (Set.diagonal Bool)
    singleValued_diagonal diagonal_converse_singleValued_map

private example :
    (op_map_lookup ℕ Bool, op_map_lookup ℕ Bool) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => mapRel (Set.diagonal ℕ) (Set.diagonal Bool) →ᵣ
          NRest.nrestRel (optionRel (Set.diagonal Bool))) :=
  op_map_lookup_fref ℕ Bool (Set.diagonal ℕ) (Set.diagonal Bool)

private example :
    (op_map_the_lookup ℕ Bool, op_map_the_lookup ℕ Bool) ∈
      fref (fun p : ℕ × (ℕ → Option Bool) => p.2 p.1 ≠ none)
        (Set.diagonal ℕ ×ᵣ mapRel (Set.diagonal ℕ) (Set.diagonal Bool))
        (fun _ => NRest.nrestRel (Set.diagonal Bool)) :=
  op_map_the_lookup_fref ℕ Bool (Set.diagonal ℕ) (Set.diagonal Bool)

private example :
    (op_map_contains_key ℕ Bool, op_map_contains_key ℕ Bool) ∈
      fref (fun _ : ℕ => True) (Set.diagonal ℕ)
        (fun _ => mapRel (Set.diagonal ℕ) (Set.diagonal Bool) →ᵣ
          NRest.nrestRel (Set.diagonal Bool)) :=
  op_map_contains_key_fref ℕ Bool (Set.diagonal ℕ) (Set.diagonal Bool)

example : op_map_empty ℕ Bool ::ᵢ NRest (MapI ℕ Bool) ECost :=
  op_map_empty_registration_itype
example : op_map_is_empty ℕ Bool ::ᵢ (MapI ℕ Bool → NRest Bool ECost) :=
  op_map_is_empty_registration_itype
example : op_map_update ℕ Bool ::ᵢ
    (ℕ → Bool → MapI ℕ Bool → NRest (MapI ℕ Bool) ECost) :=
  op_map_update_registration_itype
example : op_map_delete ℕ Bool ::ᵢ
    (ℕ → MapI ℕ Bool → NRest (MapI ℕ Bool) ECost) :=
  op_map_delete_registration_itype
example : op_map_lookup ℕ Bool ::ᵢ
    (ℕ → MapI ℕ Bool → NRest (Option Bool) ECost) :=
  op_map_lookup_registration_itype
example : op_map_the_lookup ℕ Bool ::ᵢ
    ((ℕ × MapI ℕ Bool) → NRest Bool ECost) :=
  op_map_the_lookup_registration_itype
example : op_map_contains_key ℕ Bool ::ᵢ
    (ℕ → MapI ℕ Bool → NRest Bool ECost) :=
  op_map_contains_key_registration_itype

run_cmd do
  let rules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``op_map_empty_fref, ``op_map_is_empty_fref, ``op_map_update_fref,
      ``op_map_delete_fref, ``op_map_lookup_fref, ``op_map_the_lookup_fref,
      ``op_map_contains_key_fref] do
    unless rules.contains n do
      throwError "map interface gate: missing parametricity rule {n}"

/-! ## Kernel-three guards -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.mapRel_diagonal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapRel_diagonal

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.mapRel_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mapRel_update

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.op_map_the_lookup_fref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms op_map_the_lookup_fref

end Lax13Proofs.Refine.Sepref.Iicf
