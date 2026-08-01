import Lax13Proofs.Refine.Iicf.Intf.Map
import Lax13Proofs.Refine.Iicf.Intf.PrioBag

/-!
# Priority-map interface

Source-faithful semantic leaf for `IICF/Intf/IICF_Prio_Map.thy` at
`isabelle_llvm_time` commit `42dd7f5`.

The source starts with a small TODO-labelled automation bridge.  The Lean
port exposes the useful uncurry and `returnT` relation lemmas directly and
derives ordinary parametric forms of the three inherited map operations;
there is no synthetic rewrite bundle or fake automation layer.
-/

namespace Lax13Proofs.Refine.Sepref.Iicf

open Lax13Proofs.Refine
open Ir NRest

variable {α β γ δ ε ζ : Type}
variable {κ κ' ν ν' ρ : Type}

/-! ## Source conversion helpers -/

theorem uncurry_funRel_iff {A : Set (α × β)} {B : Set (γ × δ)}
    {R : Set (ε × ζ)} {f : α → γ → ε} {g : β → δ → ζ} :
    (Function.uncurry f, Function.uncurry g) ∈ (A ×ᵣ B) →ᵣ R ↔
      (f, g) ∈ A →ᵣ B →ᵣ R := by
  constructor
  · intro h a b hab c d hcd
    exact h (a, c) (b, d) ⟨hab, hcd⟩
  · intro h ac bd hacbd
    exact h ac.1 bd.1 hacbd.1 ac.2 bd.2 hacbd.2

theorem unit_funRel_iff {R : Set (α × β)} {x : α} {y : β} :
    ((fun _ : Unit => x), (fun _ : Unit => y)) ∈
        Set.diagonal Unit →ᵣ R ↔
      (x, y) ∈ R := by
  constructor
  · intro h
    exact h () () rfl
  · intro h _ _ hunit
    change () = () at hunit
    exact h

/-- Idiomatic NRest form of the source's `RETURN_rel_conv0` introduction
direction.  NRest's program relation is refinement-oriented, so conversion
helpers are deliberately stated as sound lifts rather than global simp
equivalences. -/
theorem returnT_rel {R : Set (α × β)} {x : α} {y : β}
    (h : (x, y) ∈ R) :
    ((NRest.returnT x : NRest α ECost), NRest.returnT y) ∈
      NRest.nrestRel R :=
  NRest.param_returnT h

theorem returnT_funRel₁ {A : Set (α × β)} {R : Set (γ × δ)}
    {f : α → γ} {g : β → δ} (h : (f, g) ∈ A →ᵣ R) :
    ((fun x => (NRest.returnT (f x) : NRest γ ECost)),
      fun y => NRest.returnT (g y)) ∈ A →ᵣ NRest.nrestRel R := by
  intro x y hxy
  exact NRest.param_returnT (h x y hxy)

theorem returnT_funRel₂ {A : Set (α × β)} {B : Set (γ × δ)}
    {R : Set (ε × ζ)} {f : α → γ → ε} {g : β → δ → ζ}
    (h : (f, g) ∈ A →ᵣ B →ᵣ R) :
    ((fun x y => (NRest.returnT (f x y) : NRest ε ECost)),
      fun x y => NRest.returnT (g x y)) ∈
        A →ᵣ B →ᵣ NRest.nrestRel R := by
  intro x y hxy u v huv
  exact NRest.param_returnT (h x y hxy u v huv)

theorem returnT_funRel₃ {A : Set (α × β)} {B : Set (γ × δ)}
    {C : Set (ε × ζ)} {R : Set (κ × κ')}
    {f : α → γ → ε → κ} {g : β → δ → ζ → κ'}
    (h : (f, g) ∈ A →ᵣ B →ᵣ C →ᵣ R) :
    ((fun x y z => (NRest.returnT (f x y z) : NRest κ ECost)),
      fun x y z => NRest.returnT (g x y z)) ∈
        A →ᵣ B →ᵣ C →ᵣ NRest.nrestRel R := by
  intro x y hxy u v huv s t hst
  exact NRest.param_returnT (h x y hxy u v huv s t hst)

/-! The source obtains these three facts through its TODO-labelled rewrite
bundle.  Here they are transparent corollaries of the checked map frefs. -/

theorem param_op_map_update {K : Set (κ × κ')} {V : Set (ν × ν')}
    (hK : SingleValued K) (hKc : SingleValued (relConverse K)) :
    (op_map_update κ ν, op_map_update κ' ν') ∈
      K →ᵣ V →ᵣ mapRel K V →ᵣ NRest.nrestRel (mapRel K V) := by
  intro k l hkl v w hvw m n hmn
  exact op_map_update_fref κ ν K V hK hKc k l trivial hkl v w hvw m n hmn

theorem param_op_map_delete {K : Set (κ × κ')} {V : Set (ν × ν')}
    (hK : SingleValued K) (hKc : SingleValued (relConverse K)) :
    (op_map_delete κ ν, op_map_delete κ' ν') ∈
      K →ᵣ mapRel K V →ᵣ NRest.nrestRel (mapRel K V) := by
  intro k l hkl m n hmn
  exact op_map_delete_fref κ ν K V hK hKc k l trivial hkl m n hmn

theorem param_op_map_is_empty {K : Set (κ × κ')} {V : Set (ν × ν')} :
    (op_map_is_empty κ ν, op_map_is_empty κ' ν') ∈
      mapRel K V →ᵣ NRest.nrestRel (Set.diagonal Bool) := by
  intro m n hmn
  exact op_map_is_empty_fref κ ν K V m n trivial hmn

/-! ## Preconditions and their transport -/

def decreaseKeyPre [LE ρ] (prio : ν → ρ)
    (p : (κ × ν) × (κ → Option ν)) : Prop :=
  p.1.1 ∈ mapDom p.2 ∧
    ∀ old, p.2 p.1.1 = some old → prio p.1.2 ≤ prio old

def increaseKeyPre [LE ρ] (prio : ν → ρ)
    (p : (κ × ν) × (κ → Option ν)) : Prop :=
  p.1.1 ∈ mapDom p.2 ∧
    ∀ old, p.2 p.1.1 = some old → prio old ≤ prio p.1.2

theorem mapRel_nonempty_iff {K : Set (κ × κ')} {V : Set (ν × ν')}
    {m : κ → Option ν} {n : κ' → Option ν'} (hmn : (m, n) ∈ mapRel K V) :
    (m ≠ mapEmpty) = (n ≠ mapEmpty) := by
  apply propext
  constructor
  · intro hm hn0
    exact hm (mapRel_empty_right.mp (hn0 ▸ hmn))
  · intro hn hm0
    exact hn (mapRel_empty_left.mp (hm0 ▸ hmn))

private theorem decreaseKeyPre_transport [LinearOrder ρ]
    {K : Set (κ × κ')} {V : Set (ν × ν)}
    (hK : SingleValued K) (hV : IsBelowId V) (prio : ν → ρ)
    {p : (κ × ν) × (κ → Option ν)}
    {q : (κ' × ν) × (κ' → Option ν)}
    (hpq : (p, q) ∈ (K ×ᵣ V) ×ᵣ mapRel K V)
    (hq : decreaseKeyPre prio q) : decreaseKeyPre prio p := by
  obtain ⟨⟨hkl, hvw⟩, hmn⟩ := hpq
  have hdom := mapRel_contains hkl hmn
  refine ⟨hdom.mpr hq.1, ?_⟩
  intro old hmold
  obtain ⟨l', wold, hnold, hkl', hvold⟩ := mapRel_obtain_left hmn hmold
  have hl : l' = q.1.1 := hK p.1.1 l' q.1.1 hkl' hkl
  subst l'
  have hnew : p.1.2 = q.1.2 := hV hvw
  have hold : old = wold := hV hvold
  rw [hnew, hold]
  exact hq.2 wold hnold

private theorem increaseKeyPre_transport [LinearOrder ρ]
    {K : Set (κ × κ')} {V : Set (ν × ν)}
    (hK : SingleValued K) (hV : IsBelowId V) (prio : ν → ρ)
    {p : (κ × ν) × (κ → Option ν)}
    {q : (κ' × ν) × (κ' → Option ν)}
    (hpq : (p, q) ∈ (K ×ᵣ V) ×ᵣ mapRel K V)
    (hq : increaseKeyPre prio q) : increaseKeyPre prio p := by
  obtain ⟨⟨hkl, hvw⟩, hmn⟩ := hpq
  have hdom := mapRel_contains hkl hmn
  refine ⟨hdom.mpr hq.1, ?_⟩
  intro old hmold
  obtain ⟨l', wold, hnold, hkl', hvold⟩ := mapRel_obtain_left hmn hmold
  have hl : l' = q.1.1 := hK p.1.1 l' q.1.1 hkl' hkl
  subst l'
  have hnew : p.1.2 = q.1.2 := hV hvw
  have hold : old = wold := hV hvold
  simpa [hnew, hold] using hq.2 wold hnold

/-! ## Priority-map semantic operations -/

noncomputable def prioMapPeekMin [LinearOrder ρ] (prio : ν → ρ)
    (m : κ → Option ν) : NRest (κ × ν) ECost :=
  NRest.spec
    (fun p => m p.1 = some p.2 ∧
      ∀ k v, m k = some v → prio p.2 ≤ prio v)
    (fun _ => 0)

noncomputable def prioMapPopMin [LinearOrder ρ] (prio : ν → ρ)
    (m : κ → Option ν) : NRest ((κ × ν) × (κ → Option ν)) ECost :=
  NRest.spec
    (fun p => m p.1.1 = some p.1.2 ∧
      p.2 = mapDelete m p.1.1 ∧
      ∀ k v, m k = some v → prio p.1.2 ≤ prio v)
    (fun _ => 0)

theorem prioMapPeekMin_param [LinearOrder ρ]
    {K : Set (κ × κ')} {V : Set (ν × ν)}
    (hV : IsBelowId V) (prio : ν → ρ) :
    (prioMapPeekMin (κ := κ) prio, prioMapPeekMin (κ := κ') prio) ∈
      mapRel K V →ᵣ NRest.nrestRel (K ×ᵣ V) := by
  intro m n hmn
  unfold prioMapPeekMin
  apply NRest.nrestRel_of_le
  apply NRest.rest_refines_concFun'
  intro X hX p hp
  have hX' := NRest.rest_inj_iff.mp hX
  subst X
  rcases p with ⟨k, v⟩
  have hpost : m k = some v ∧
      ∀ k' v', m k' = some v' → prio v ≤ prio v' := by
    simpa using hp
  obtain ⟨l, w, hn, hkl, hvw⟩ := mapRel_obtain_left hmn hpost.1
  have hright : n l = some w ∧
      ∀ l' w', n l' = some w' → prio w ≤ prio w' := by
    refine ⟨hn, ?_⟩
    intro l' w' hn'
    obtain ⟨k', v', hm', -, hvw'⟩ := mapRel_obtain_right hmn hn'
    have hv : v = w := hV hvw
    have hv' : v' = w' := hV hvw'
    simpa [hv, hv'] using hpost.2 k' v' hm'
  refine ⟨(l, w), ⟨hkl, hvw⟩, ?_⟩
  simp only [if_pos hpost, if_pos hright]
  exact le_rfl

theorem prioMapPopMin_param [LinearOrder ρ]
    {K : Set (κ × κ')} {V : Set (ν × ν)}
    (hK : SingleValued K) (hKc : SingleValued (relConverse K))
    (hV : IsBelowId V) (prio : ν → ρ) :
    (prioMapPopMin (κ := κ) prio, prioMapPopMin (κ := κ') prio) ∈
      mapRel K V →ᵣ NRest.nrestRel ((K ×ᵣ V) ×ᵣ mapRel K V) := by
  intro m n hmn
  unfold prioMapPopMin
  apply NRest.nrestRel_of_le
  apply NRest.rest_refines_concFun'
  intro X hX p hp
  have hX' := NRest.rest_inj_iff.mp hX
  subst X
  rcases p with ⟨⟨k, v⟩, mr⟩
  have hpost : m k = some v ∧ mr = mapDelete m k ∧
      ∀ k' v', m k' = some v' → prio v ≤ prio v' := by
    simpa using hp
  obtain ⟨l, w, hn, hkl, hvw⟩ := mapRel_obtain_left hmn hpost.1
  have hright : n l = some w ∧ mapDelete n l = mapDelete n l ∧
      ∀ l' w', n l' = some w' → prio w ≤ prio w' := by
    refine ⟨hn, rfl, ?_⟩
    intro l' w' hn'
    obtain ⟨k', v', hm', -, hvw'⟩ := mapRel_obtain_right hmn hn'
    have hv : v = w := hV hvw
    have hv' : v' = w' := hV hvw'
    simpa [hv, hv'] using hpost.2.2 k' v' hm'
  refine ⟨((l, w), mapDelete n l), ⟨⟨hkl, hvw⟩, ?_⟩, ?_⟩
  · simpa [hpost.2.1] using mapRel_delete hK hKc hkl hmn
  · simp only [if_pos hpost, if_pos hright]
    exact le_rfl

/-! ## Seven additional interface operations -/

sepref_decl_op map_update_new (κ ν : Type) :
    ((κ × ν) × (κ → Option ν)) → NRest (κ → Option ν) ECost :=
    fun p => NRest.returnT (mapUpdate p.2 p.1.1 p.1.2)
  interface := ∀ κ ν : Type,
    ((κ × ν) × MapI κ ν) → NRest (MapI κ ν) ECost
  precondition := fun p : (κ × ν) × (κ → Option ν) => p.1.1 ∉ mapDom p.2
  parametricity : ∀ {κ' ν' : Type} (K : Set (κ × κ')) (V : Set (ν × ν')),
      SingleValued K → SingleValued (relConverse K) →
      ((op_map_update_new κ ν, op_map_update_new κ' ν') ∈
        fref (fun q : (κ' × ν') × (κ' → Option ν') => q.1.1 ∉ mapDom q.2)
          ((K ×ᵣ V) ×ᵣ mapRel K V)
          (fun _ => NRest.nrestRel (mapRel K V))) := by
    intro κ' ν' K V hK hKc p q hq hpq
    obtain ⟨⟨hkl, hvw⟩, hmn⟩ := hpq
    have hdom := mapRel_contains hkl hmn
    have hp : p.1.1 ∉ mapDom p.2 := fun hk => hq (hdom.mp hk)
    exact NRest.param_returnT (mapRel_update hK hKc hkl hvw hmn)

sepref_decl_op map_update_ex (κ ν : Type) :
    ((κ × ν) × (κ → Option ν)) → NRest (κ → Option ν) ECost :=
    fun p => NRest.returnT (mapUpdate p.2 p.1.1 p.1.2)
  interface := ∀ κ ν : Type,
    ((κ × ν) × MapI κ ν) → NRest (MapI κ ν) ECost
  precondition := fun p : (κ × ν) × (κ → Option ν) => p.1.1 ∈ mapDom p.2
  parametricity : ∀ {κ' ν' : Type} (K : Set (κ × κ')) (V : Set (ν × ν')),
      SingleValued K → SingleValued (relConverse K) →
      ((op_map_update_ex κ ν, op_map_update_ex κ' ν') ∈
        fref (fun q : (κ' × ν') × (κ' → Option ν') => q.1.1 ∈ mapDom q.2)
          ((K ×ᵣ V) ×ᵣ mapRel K V)
          (fun _ => NRest.nrestRel (mapRel K V))) := by
    intro κ' ν' K V hK hKc p q hq hpq
    obtain ⟨⟨hkl, hvw⟩, hmn⟩ := hpq
    have hp : p.1.1 ∈ mapDom p.2 := (mapRel_contains hkl hmn).mpr hq
    exact NRest.param_returnT (mapRel_update hK hKc hkl hvw hmn)

sepref_decl_op map_delete_ex (κ ν : Type) :
    (κ × (κ → Option ν)) → NRest (κ → Option ν) ECost :=
    fun p => NRest.returnT (mapDelete p.2 p.1)
  interface := ∀ κ ν : Type,
    (κ × MapI κ ν) → NRest (MapI κ ν) ECost
  precondition := fun p : κ × (κ → Option ν) => p.1 ∈ mapDom p.2
  parametricity : ∀ {κ' ν' : Type} (K : Set (κ × κ')) (V : Set (ν × ν')),
      SingleValued K → SingleValued (relConverse K) →
      ((op_map_delete_ex κ ν, op_map_delete_ex κ' ν') ∈
        fref (fun q : κ' × (κ' → Option ν') => q.1 ∈ mapDom q.2)
          (K ×ᵣ mapRel K V) (fun _ => NRest.nrestRel (mapRel K V))) := by
    intro κ' ν' K V hK hKc p q hq hpq
    obtain ⟨hkl, hmn⟩ := hpq
    have hp : p.1 ∈ mapDom p.2 := (mapRel_contains hkl hmn).mpr hq
    exact NRest.param_returnT (mapRel_delete hK hKc hkl hmn)

sepref_decl_op pm_decrease_key (κ ν ρ : Type) [LinearOrder ρ]
    (prio : ν → ρ) :
    ((κ × ν) × (κ → Option ν)) → NRest (κ → Option ν) ECost :=
    fun p => NRest.returnT (mapUpdate p.2 p.1.1 p.1.2)
  interface := ∀ κ ν ρ : Type, [LinearOrder ρ] → (ν → ρ) →
    ((κ × ν) × MapI κ ν) → NRest (MapI κ ν) ECost
  precondition := fun p : (κ × ν) × (κ → Option ν) => decreaseKeyPre prio p
  parametricity : ∀ {κ' : Type} (K : Set (κ × κ')) (V : Set (ν × ν)),
      SingleValued K → SingleValued (relConverse K) → IsBelowId V →
      ((op_pm_decrease_key κ ν ρ prio, op_pm_decrease_key κ' ν ρ prio) ∈
        fref (fun q : (κ' × ν) × (κ' → Option ν) => decreaseKeyPre prio q)
          ((K ×ᵣ V) ×ᵣ mapRel K V)
          (fun _ => NRest.nrestRel (mapRel K V))) := by
    intro κ' K V hK hKc hV p q hq hpq
    have hp := decreaseKeyPre_transport hK hV prio hpq hq
    obtain ⟨⟨hkl, hvw⟩, hmn⟩ := hpq
    exact NRest.param_returnT (mapRel_update hK hKc hkl hvw hmn)

sepref_decl_op pm_increase_key (κ ν ρ : Type) [LinearOrder ρ]
    (prio : ν → ρ) :
    ((κ × ν) × (κ → Option ν)) → NRest (κ → Option ν) ECost :=
    fun p => NRest.returnT (mapUpdate p.2 p.1.1 p.1.2)
  interface := ∀ κ ν ρ : Type, [LinearOrder ρ] → (ν → ρ) →
    ((κ × ν) × MapI κ ν) → NRest (MapI κ ν) ECost
  precondition := fun p : (κ × ν) × (κ → Option ν) => increaseKeyPre prio p
  parametricity : ∀ {κ' : Type} (K : Set (κ × κ')) (V : Set (ν × ν)),
      SingleValued K → SingleValued (relConverse K) → IsBelowId V →
      ((op_pm_increase_key κ ν ρ prio, op_pm_increase_key κ' ν ρ prio) ∈
        fref (fun q : (κ' × ν) × (κ' → Option ν) => increaseKeyPre prio q)
          ((K ×ᵣ V) ×ᵣ mapRel K V)
          (fun _ => NRest.nrestRel (mapRel K V))) := by
    intro κ' K V hK hKc hV p q hq hpq
    have hp := increaseKeyPre_transport hK hV prio hpq hq
    obtain ⟨⟨hkl, hvw⟩, hmn⟩ := hpq
    exact NRest.param_returnT (mapRel_update hK hKc hkl hvw hmn)

sepref_decl_op pm_peek_min (κ ν ρ : Type) [LinearOrder ρ]
    (prio : ν → ρ) :
    (κ → Option ν) → NRest (κ × ν) ECost :=
    prioMapPeekMin prio
  interface := ∀ κ ν ρ : Type, [LinearOrder ρ] → (ν → ρ) →
    MapI κ ν → NRest (κ × ν) ECost
  precondition := fun m : κ → Option ν => m ≠ mapEmpty
  parametricity : ∀ {κ' : Type} (K : Set (κ × κ')) (V : Set (ν × ν)),
      IsBelowId V →
      ((op_pm_peek_min κ ν ρ prio, op_pm_peek_min κ' ν ρ prio) ∈
        fref (fun n : κ' → Option ν => n ≠ mapEmpty) (mapRel K V)
          (fun _ => NRest.nrestRel (K ×ᵣ V))) := by
    intro κ' K V hV m n hn hmn
    have hm : m ≠ mapEmpty := (mapRel_nonempty_iff hmn).mpr hn
    exact prioMapPeekMin_param hV prio m n hmn

sepref_decl_op pm_pop_min (κ ν ρ : Type) [LinearOrder ρ]
    (prio : ν → ρ) :
    (κ → Option ν) → NRest ((κ × ν) × (κ → Option ν)) ECost :=
    prioMapPopMin prio
  interface := ∀ κ ν ρ : Type, [LinearOrder ρ] → (ν → ρ) →
    MapI κ ν → NRest ((κ × ν) × MapI κ ν) ECost
  precondition := fun m : κ → Option ν => m ≠ mapEmpty
  parametricity : ∀ {κ' : Type} (K : Set (κ × κ')) (V : Set (ν × ν)),
      SingleValued K → SingleValued (relConverse K) → IsBelowId V →
      ((op_pm_pop_min κ ν ρ prio, op_pm_pop_min κ' ν ρ prio) ∈
        fref (fun n : κ' → Option ν => n ≠ mapEmpty) (mapRel K V)
          (fun _ => NRest.nrestRel ((K ×ᵣ V) ×ᵣ mapRel K V))) := by
    intro κ' K V hK hKc hV m n hn hmn
    have hm : m ≠ mapEmpty := (mapRel_nonempty_iff hmn).mpr hn
    exact prioMapPopMin_param hK hKc hV prio m n hmn

/-! ## Generic, proper-below-id, diagonal, registration, and DB gates -/

private def zeroRel : Set (ℕ × ℕ) :=
  {p | p.1 = 0 ∧ p.2 = 0}

private theorem zeroRel_singleValued : SingleValued zeroRel := by
  rintro a b b' ⟨-, hb⟩ ⟨-, hb'⟩
  exact hb.trans hb'.symm

private theorem zeroRel_converse_singleValued :
    SingleValued (relConverse zeroRel) := by
  rintro b a a' ⟨ha, -⟩ ⟨ha', -⟩
  exact ha.trans ha'.symm

private theorem zeroRel_belowId : IsBelowId zeroRel := by
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  change a = b
  exact ha.trans hb.symm

private theorem diagonal_converse_singleValued_prioMap :
    SingleValued (relConverse (Set.diagonal ℕ)) := by
  rintro b a a' hba hba'
  change a = b at hba
  change a' = b at hba'
  exact hba.trans hba'.symm

private example (prio : ℕ → ℕ) :
    ((op_pm_decrease_key ℕ ℕ ℕ prio, op_pm_decrease_key ℕ ℕ ℕ prio) ∈
      fref (fun q : (ℕ × ℕ) × (ℕ → Option ℕ) => decreaseKeyPre prio q)
        ((zeroRel ×ᵣ zeroRel) ×ᵣ mapRel zeroRel zeroRel)
        (fun _ => NRest.nrestRel (mapRel zeroRel zeroRel))) :=
  op_pm_decrease_key_fref ℕ ℕ ℕ prio zeroRel zeroRel
    zeroRel_singleValued zeroRel_converse_singleValued zeroRel_belowId

private example (prio : ℕ → ℕ) :
    ((op_pm_increase_key ℕ ℕ ℕ prio, op_pm_increase_key ℕ ℕ ℕ prio) ∈
      fref (fun q : (ℕ × ℕ) × (ℕ → Option ℕ) => increaseKeyPre prio q)
        ((zeroRel ×ᵣ zeroRel) ×ᵣ mapRel zeroRel zeroRel)
        (fun _ => NRest.nrestRel (mapRel zeroRel zeroRel))) :=
  op_pm_increase_key_fref ℕ ℕ ℕ prio zeroRel zeroRel
    zeroRel_singleValued zeroRel_converse_singleValued zeroRel_belowId

private example (prio : ℕ → ℕ) :
    ((op_pm_peek_min ℕ ℕ ℕ prio, op_pm_peek_min ℕ ℕ ℕ prio) ∈
      fref (fun n : ℕ → Option ℕ => n ≠ mapEmpty)
        (mapRel zeroRel zeroRel) (fun _ => NRest.nrestRel (zeroRel ×ᵣ zeroRel))) :=
  op_pm_peek_min_fref ℕ ℕ ℕ prio zeroRel zeroRel zeroRel_belowId

private example (prio : ℕ → ℕ) :
    ((op_pm_pop_min ℕ ℕ ℕ prio, op_pm_pop_min ℕ ℕ ℕ prio) ∈
      fref (fun n : ℕ → Option ℕ => n ≠ mapEmpty)
        (mapRel zeroRel zeroRel)
        (fun _ => NRest.nrestRel
          ((zeroRel ×ᵣ zeroRel) ×ᵣ mapRel zeroRel zeroRel))) :=
  op_pm_pop_min_fref ℕ ℕ ℕ prio zeroRel zeroRel
    zeroRel_singleValued zeroRel_converse_singleValued zeroRel_belowId

private example :
    (op_map_update_new ℕ Bool, op_map_update_new ℕ Bool) ∈
      fref (fun q : (ℕ × Bool) × (ℕ → Option Bool) => q.1.1 ∉ mapDom q.2)
        ((Set.diagonal ℕ ×ᵣ Set.diagonal Bool) ×ᵣ
          mapRel (Set.diagonal ℕ) (Set.diagonal Bool))
        (fun _ => NRest.nrestRel
          (mapRel (Set.diagonal ℕ) (Set.diagonal Bool))) :=
  op_map_update_new_fref ℕ Bool (Set.diagonal ℕ) (Set.diagonal Bool)
    singleValued_diagonal diagonal_converse_singleValued_prioMap

private example :
    (op_map_update_ex ℕ Bool, op_map_update_ex ℕ Bool) ∈
      fref (fun q : (ℕ × Bool) × (ℕ → Option Bool) => q.1.1 ∈ mapDom q.2)
        ((Set.diagonal ℕ ×ᵣ Set.diagonal Bool) ×ᵣ
          mapRel (Set.diagonal ℕ) (Set.diagonal Bool))
        (fun _ => NRest.nrestRel
          (mapRel (Set.diagonal ℕ) (Set.diagonal Bool))) :=
  op_map_update_ex_fref ℕ Bool (Set.diagonal ℕ) (Set.diagonal Bool)
    singleValued_diagonal diagonal_converse_singleValued_prioMap

private example :
    (op_map_delete_ex ℕ Bool, op_map_delete_ex ℕ Bool) ∈
      fref (fun q : ℕ × (ℕ → Option Bool) => q.1 ∈ mapDom q.2)
        (Set.diagonal ℕ ×ᵣ mapRel (Set.diagonal ℕ) (Set.diagonal Bool))
        (fun _ => NRest.nrestRel
          (mapRel (Set.diagonal ℕ) (Set.diagonal Bool))) :=
  op_map_delete_ex_fref ℕ Bool (Set.diagonal ℕ) (Set.diagonal Bool)
    singleValued_diagonal diagonal_converse_singleValued_prioMap

private example (prio : ℕ → ℕ) :
    ((op_pm_decrease_key ℕ ℕ ℕ prio, op_pm_decrease_key ℕ ℕ ℕ prio) ∈
      fref (fun q : (ℕ × ℕ) × (ℕ → Option ℕ) => decreaseKeyPre prio q)
        ((Set.diagonal ℕ ×ᵣ Set.diagonal ℕ) ×ᵣ
          mapRel (Set.diagonal ℕ) (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel
          (mapRel (Set.diagonal ℕ) (Set.diagonal ℕ)))) :=
  op_pm_decrease_key_fref ℕ ℕ ℕ prio (Set.diagonal ℕ) (Set.diagonal ℕ)
    singleValued_diagonal diagonal_converse_singleValued_prioMap fun _ h => h

private example (prio : ℕ → ℕ) :
    ((op_pm_increase_key ℕ ℕ ℕ prio, op_pm_increase_key ℕ ℕ ℕ prio) ∈
      fref (fun q : (ℕ × ℕ) × (ℕ → Option ℕ) => increaseKeyPre prio q)
        ((Set.diagonal ℕ ×ᵣ Set.diagonal ℕ) ×ᵣ
          mapRel (Set.diagonal ℕ) (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel
          (mapRel (Set.diagonal ℕ) (Set.diagonal ℕ)))) :=
  op_pm_increase_key_fref ℕ ℕ ℕ prio (Set.diagonal ℕ) (Set.diagonal ℕ)
    singleValued_diagonal diagonal_converse_singleValued_prioMap fun _ h => h

private example (prio : ℕ → ℕ) :
    ((op_pm_peek_min ℕ ℕ ℕ prio, op_pm_peek_min ℕ ℕ ℕ prio) ∈
      fref (fun n : ℕ → Option ℕ => n ≠ mapEmpty)
        (mapRel (Set.diagonal ℕ) (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel (Set.diagonal ℕ ×ᵣ Set.diagonal ℕ))) :=
  op_pm_peek_min_fref ℕ ℕ ℕ prio (Set.diagonal ℕ) (Set.diagonal ℕ) fun _ h => h

private example (prio : ℕ → ℕ) :
    ((op_pm_pop_min ℕ ℕ ℕ prio, op_pm_pop_min ℕ ℕ ℕ prio) ∈
      fref (fun n : ℕ → Option ℕ => n ≠ mapEmpty)
        (mapRel (Set.diagonal ℕ) (Set.diagonal ℕ))
        (fun _ => NRest.nrestRel
          ((Set.diagonal ℕ ×ᵣ Set.diagonal ℕ) ×ᵣ
            mapRel (Set.diagonal ℕ) (Set.diagonal ℕ)))) :=
  op_pm_pop_min_fref ℕ ℕ ℕ prio (Set.diagonal ℕ) (Set.diagonal ℕ)
    singleValued_diagonal diagonal_converse_singleValued_prioMap fun _ h => h

example : op_map_update_new ::ᵢ
    ((κ ν : Type) → (κ × ν) × MapI κ ν → NRest (MapI κ ν) ECost) :=
  op_map_update_new_registration_itype

example : op_map_update_ex ::ᵢ
    ((κ ν : Type) → (κ × ν) × MapI κ ν → NRest (MapI κ ν) ECost) :=
  op_map_update_ex_registration_itype

example : op_map_delete_ex ::ᵢ
    ((κ ν : Type) → κ × MapI κ ν → NRest (MapI κ ν) ECost) :=
  op_map_delete_ex_registration_itype

example : op_pm_decrease_key ::ᵢ
    ((κ ν ρ : Type) → [LinearOrder ρ] → (ν → ρ) →
      (κ × ν) × MapI κ ν → NRest (MapI κ ν) ECost) :=
  op_pm_decrease_key_registration_itype

example : op_pm_increase_key ::ᵢ
    ((κ ν ρ : Type) → [LinearOrder ρ] → (ν → ρ) →
      (κ × ν) × MapI κ ν → NRest (MapI κ ν) ECost) :=
  op_pm_increase_key_registration_itype

example : op_pm_peek_min ::ᵢ
    ((κ ν ρ : Type) → [LinearOrder ρ] → (ν → ρ) →
      MapI κ ν → NRest (κ × ν) ECost) :=
  op_pm_peek_min_registration_itype

example : op_pm_pop_min ::ᵢ
    ((κ ν ρ : Type) → [LinearOrder ρ] → (ν → ρ) →
      MapI κ ν → NRest ((κ × ν) × MapI κ ν) ECost) :=
  op_pm_pop_min_registration_itype

run_cmd do
  let rules ← Lean.Elab.Command.liftCoreM <| Lean.labelled `sepref_fref_thms
  for n in #[``op_map_update_new_fref, ``op_map_update_ex_fref,
      ``op_map_delete_ex_fref, ``op_pm_decrease_key_fref,
      ``op_pm_increase_key_fref, ``op_pm_peek_min_fref,
      ``op_pm_pop_min_fref] do
    unless rules.contains n do
      throwError "priority-map interface gate: missing parametricity rule {n}"

/-! ## Kernel-three guards -/

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.param_op_map_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms param_op_map_update

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.prioMapPopMin_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prioMapPopMin_param

/-- info: 'Lax13Proofs.Refine.Sepref.Iicf.op_pm_pop_min_fref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms op_pm_pop_min_fref

end Lax13Proofs.Refine.Sepref.Iicf
