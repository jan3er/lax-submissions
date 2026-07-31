import Lax13Proofs.Refine.Sepref.Rules

/-!
Flattening laws for iterated dependent signature composition.

There is a small but important trap here.  In
`hrrCompDep T₂ (hrrCompDep T₁ S U₁) U₂`, the intermediate argument
witness indexes `U₁`.  Composing `T₁` with `T₂` and `U₁` with `U₂`
independently forgets that this must be the *same* witness.  The flat form
below therefore keeps the four local witnesses in one residue and guards
the base assertion by all four relational facts at once.

The final section compiles both sides of this design decision: a two-layer
introduction/elimination gate for the sound flat form, and a counterexample
to independent relational composition.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir

/-! ## A correlated local residue -/

/-- The witnesses hidden by two nested `hrrCompDep` layers. -/
structure HrrCompDepResidue (α₀ α₁ β₀ β₁ : Type) where
  midArg : α₁
  sourceArg : α₀
  midResult : β₁
  sourceResult : β₀

/-- All relational facts in a two-layer residue.  Keeping them in one
predicate is what preserves the correlation through `midArg`. -/
def HrrCompDepResidue.Valid {α₀ α₁ α₂ β₀ β₁ β₂ : Type}
    (T₁ : Set (α₀ × α₁)) (T₂ : Set (α₁ × α₂))
    (U₁ : α₁ → Set (β₀ × β₁)) (U₂ : α₂ → Set (β₁ × β₂))
    (x : α₂) (a : β₂) (r : HrrCompDepResidue α₀ α₁ β₀ β₁) : Prop :=
  (r.sourceArg, r.midArg) ∈ T₁ ∧
  (r.midArg, x) ∈ T₂ ∧
  (r.sourceResult, r.midResult) ∈ U₁ r.midArg ∧
  (r.midResult, a) ∈ U₂ x

/-- A single-existential normal form for two dependent composition layers. -/
def hrrCompDepFlat {α₀ α₁ α₂ β₀ β₁ β₂ κa κb : Type}
    (T₁ : Set (α₀ × α₁)) (T₂ : Set (α₁ × α₂))
    (S : α₀ → κa → β₀ → κb → Assn)
    (U₁ : α₁ → Set (β₀ × β₁)) (U₂ : α₂ → Set (β₁ × β₂)) :
    α₂ → κa → β₂ → κb → Assn :=
  fun x y a c =>
    sepEx (fun r : HrrCompDepResidue α₀ α₁ β₀ β₁ =>
      predLift (r.Valid T₁ T₂ U₁ U₂ x a) ∗ S r.sourceArg y r.sourceResult c)

/-- Introduce the flat form from the base assertion and four local facts. -/
theorem hrrCompDepFlat_I {α₀ α₁ α₂ β₀ β₁ β₂ κa κb : Type}
    {T₁ : Set (α₀ × α₁)} {T₂ : Set (α₁ × α₂)}
    {S : α₀ → κa → β₀ → κb → Assn}
    {U₁ : α₁ → Set (β₀ × β₁)} {U₂ : α₂ → Set (β₁ × β₂)}
    {x : α₂} {y : κa} {a : β₂} {c : κb}
    {b₀ : α₀} {b₁ : α₁} {rb₀ : β₀} {rb₁ : β₁}
    (hT₁ : (b₀, b₁) ∈ T₁) (hT₂ : (b₁, x) ∈ T₂)
    (hU₁ : (rb₀, rb₁) ∈ U₁ b₁) (hU₂ : (rb₁, a) ∈ U₂ x) :
    S b₀ y rb₀ c ⊢ hrrCompDepFlat T₁ T₂ S U₁ U₂ x y a c :=
  fun _ hp =>
    ⟨⟨b₁, b₀, rb₁, rb₀⟩, predLift_sepConj_iff.2 ⟨⟨hT₁, hT₂, hU₁, hU₂⟩, hp⟩⟩

/-- Eliminate the flat form with one callback; consumers never open any of
the nested separation existentials themselves. -/
theorem hrrCompDepFlat_E {α₀ α₁ α₂ β₀ β₁ β₂ κa κb : Type}
    {T₁ : Set (α₀ × α₁)} {T₂ : Set (α₁ × α₂)}
    {S : α₀ → κa → β₀ → κb → Assn}
    {U₁ : α₁ → Set (β₀ × β₁)} {U₂ : α₂ → Set (β₁ × β₂)}
    {x : α₂} {y : κa} {a : β₂} {c : κb} {P : Assn}
    (h : ∀ r : HrrCompDepResidue α₀ α₁ β₀ β₁,
      r.Valid T₁ T₂ U₁ U₂ x a → S r.sourceArg y r.sourceResult c ⊢ P) :
    hrrCompDepFlat T₁ T₂ S U₁ U₂ x y a c ⊢ P := by
  rintro hp ⟨r, hr⟩
  obtain ⟨hvalid, hS⟩ := predLift_sepConj_iff.1 hr
  exact h r hvalid hp hS

/-! ## Flattening the nested form -/

theorem hrrCompDep_nested_entails_flat
    {α₀ α₁ α₂ β₀ β₁ β₂ κa κb : Type}
    {T₁ : Set (α₀ × α₁)} {T₂ : Set (α₁ × α₂)}
    {S : α₀ → κa → β₀ → κb → Assn}
    {U₁ : α₁ → Set (β₀ × β₁)} {U₂ : α₂ → Set (β₁ × β₂)}
    {x : α₂} {y : κa} {a : β₂} {c : κb} :
    hrrCompDep T₂ (hrrCompDep T₁ S U₁) U₂ x y a c ⊢
      hrrCompDepFlat T₁ T₂ S U₁ U₂ x y a c := by
  rintro hp ⟨b₁, hb₁⟩
  obtain ⟨hT₂, hb₁⟩ := predLift_sepConj_iff.1 hb₁
  obtain ⟨rb₁, hrb₁⟩ := hb₁
  obtain ⟨hU₂, hinner⟩ := sepConj_predLift_iff.1 hrb₁
  obtain ⟨b₀, hb₀⟩ := hinner
  obtain ⟨hT₁, hb₀⟩ := predLift_sepConj_iff.1 hb₀
  obtain ⟨rb₀, hrb₀⟩ := hb₀
  obtain ⟨hU₁, hS⟩ := sepConj_predLift_iff.1 hrb₀
  exact hrrCompDepFlat_I hT₁ hT₂ hU₁ hU₂ hp hS

theorem hrrCompDep_flat_entails_nested
    {α₀ α₁ α₂ β₀ β₁ β₂ κa κb : Type}
    {T₁ : Set (α₀ × α₁)} {T₂ : Set (α₁ × α₂)}
    {S : α₀ → κa → β₀ → κb → Assn}
    {U₁ : α₁ → Set (β₀ × β₁)} {U₂ : α₂ → Set (β₁ × β₂)}
    {x : α₂} {y : κa} {a : β₂} {c : κb} :
    hrrCompDepFlat T₁ T₂ S U₁ U₂ x y a c ⊢
      hrrCompDep T₂ (hrrCompDep T₁ S U₁) U₂ x y a c := by
  refine hrrCompDepFlat_E fun r hr => ?_
  obtain ⟨hT₁, hT₂, hU₁, hU₂⟩ := hr
  exact entails_trans (hrrCompDep_I hT₁ hU₁) (hrrCompDep_I hT₂ hU₂)

/-- The normalization law used by iterated and loop composition. -/
theorem hrrCompDep_flatten
    {α₀ α₁ α₂ β₀ β₁ β₂ κa κb : Type}
    (T₁ : Set (α₀ × α₁)) (T₂ : Set (α₁ × α₂))
    (S : α₀ → κa → β₀ → κb → Assn)
    (U₁ : α₁ → Set (β₀ × β₁)) (U₂ : α₂ → Set (β₁ × β₂)) :
    hrrCompDep T₂ (hrrCompDep T₁ S U₁) U₂ = hrrCompDepFlat T₁ T₂ S U₁ U₂ := by
  funext x y a c hp
  exact propext ⟨hrrCompDep_nested_entails_flat hp,
    hrrCompDep_flat_entails_nested hp⟩

/-- Eliminate a nested composition through the flat residue interface. -/
theorem hrrCompDep_nested_E
    {α₀ α₁ α₂ β₀ β₁ β₂ κa κb : Type}
    {T₁ : Set (α₀ × α₁)} {T₂ : Set (α₁ × α₂)}
    {S : α₀ → κa → β₀ → κb → Assn}
    {U₁ : α₁ → Set (β₀ × β₁)} {U₂ : α₂ → Set (β₁ × β₂)}
    {x : α₂} {y : κa} {a : β₂} {c : κb} {P : Assn}
    (h : ∀ r : HrrCompDepResidue α₀ α₁ β₀ β₁,
      r.Valid T₁ T₂ U₁ U₂ x a → S r.sourceArg y r.sourceResult c ⊢ P) :
    hrrCompDep T₂ (hrrCompDep T₁ S U₁) U₂ x y a c ⊢ P :=
  entails_trans hrrCompDep_nested_entails_flat (hrrCompDepFlat_E h)

/-! ## A two-layer consumer gate -/

private def flatGateT₁ : Set (Bool × Bool) := Set.diagonal Bool
private def flatGateT₂ : Set (Bool × Unit) := {p | p = (false, ())}
private def flatGateU₁ : Bool → Set (ℕ × ℕ) := fun _ => Set.diagonal ℕ
private def flatGateU₂ : Unit → Set (ℕ × ℕ) := fun _ => Set.diagonal ℕ
private def flatGateS : Bool → Unit → ℕ → String → Assn := fun _ _ => natAssn

/-- A concrete two-layer composition is introduced and eliminated through
the residue rules.  Neither direction unfolds a nested `sepEx`. -/
theorem hrrCompDep_twoLayer_gate :
    hrrCompDep flatGateT₂ (hrrCompDep flatGateT₁ flatGateS flatGateU₁) flatGateU₂
        () () 7 "gate" = natAssn 7 "gate" := by
  funext hp
  apply propext
  constructor
  · exact hrrCompDep_nested_E (fun r hr => by
      obtain ⟨_, _, hU₁, hU₂⟩ := hr
      have h₀₁ : r.sourceResult = r.midResult := hU₁
      have h₁₂ : r.midResult = 7 := hU₂
      simpa only [flatGateS, h₀₁, h₁₂] using
        (entails_refl (natAssn 7 "gate"))) hp
  · have hi : natAssn 7 "gate" ⊢
        hrrCompDepFlat flatGateT₁ flatGateT₂ flatGateS flatGateU₁ flatGateU₂
          () () 7 "gate" :=
      hrrCompDepFlat_I (T₁ := flatGateT₁) (T₂ := flatGateT₂) (S := flatGateS)
        (U₁ := flatGateU₁) (U₂ := flatGateU₂) (x := ()) (y := ()) (a := 7) (c := "gate")
        (b₀ := false) (b₁ := false) (rb₀ := 7) (rb₁ := 7)
        (rfl : (false, false) ∈ flatGateT₁) (rfl : (false, ()) ∈ flatGateT₂)
        (rfl : (7, 7) ∈ flatGateU₁ false) (rfl : (7, 7) ∈ flatGateU₂ ())
    exact (entails_trans hi hrrCompDep_flat_entails_nested) hp

/-! ## Why the residue may not be split -/

namespace IndependentCompositionCounterexample

def T₁ : Set (Bool × Bool) := Set.diagonal Bool
def T₂ : Set (Bool × Unit) := Set.univ
def U₁ : Bool → Set (ℕ × ℕ) := fun b => if b then Set.diagonal ℕ else ∅
def U₂ : Unit → Set (ℕ × ℕ) := fun _ => Set.diagonal ℕ
def S : Bool → Unit → ℕ → Unit → Assn :=
  fun b _ _ _ => if b then sepFalse else emp

/-- The tempting independent composition of the argument relations. -/
def naiveT : Set (Bool × Unit) :=
  {p | ∃ mid, (p.1, mid) ∈ T₁ ∧ (mid, p.2) ∈ T₂}

/-- The equally tempting output composition.  Its `mid` witness is local,
so nothing forces it to equal the witness selected by `naiveT`. -/
def naiveU (x : Unit) : Set (ℕ × ℕ) :=
  {p | ∃ mid rb₁, (mid, x) ∈ T₂ ∧
    (p.1, rb₁) ∈ U₁ mid ∧ (rb₁, p.2) ∈ U₂ x}

/-- Independent relational composition is strictly too weak: its input
side can choose `false`, while its output side chooses `true`.  The nested
form shares that Boolean and is therefore unsatisfiable in this model. -/
theorem naive_independent_flattening_is_false :
    ¬ (hrrCompDep T₂ (hrrCompDep T₁ S U₁) U₂ =
      hrrCompDep naiveT S naiveU) := by
  have hnested : ¬ (hrrCompDep T₂ (hrrCompDep T₁ S U₁) U₂
      () () 0 () (0 : AState)) := by
    rintro ⟨b₁, hb₁⟩
    obtain ⟨_, hb₁⟩ := predLift_sepConj_iff.1 hb₁
    obtain ⟨rb₁, hrb₁⟩ := hb₁
    obtain ⟨_, hinner⟩ := sepConj_predLift_iff.1 hrb₁
    obtain ⟨b₀, hb₀⟩ := hinner
    obtain ⟨hT₁, hb₀⟩ := predLift_sepConj_iff.1 hb₀
    obtain ⟨rb₀, hrb₀⟩ := hb₀
    obtain ⟨hU₁, hS⟩ := sepConj_predLift_iff.1 hrb₀
    have hb : b₀ = b₁ := hT₁
    subst b₀
    cases b₁ with
    | false => simp [U₁] at hU₁
    | true => simpa [S] using hS
  have hnaive : hrrCompDep naiveT S naiveU () () 0 () (0 : AState) := by
    apply hrrCompDep_I (b := false) (rb := 0)
      (show (false, ()) ∈ naiveT from ⟨false, rfl, trivial⟩)
      (show (0, 0) ∈ naiveU () from ⟨true, 0, trivial, rfl, rfl⟩)
    rfl
  intro heq
  apply hnested
  rw [heq]
  exact hnaive

end IndependentCompositionCounterexample

end Lax13Proofs.Refine.Sepref
