import Lax13Proofs.Refine.Sepref.Rules

/-!
# Sepref signature normalization and composition

Source pin: `isabelle_llvm_time` commit `42dd7f5`,
`thys/sepref/Sepref_Rules.thy`, especially `comp_PRE` and its rules
(source lines 1046--1157), the `to_hnr` / `to_hfref` converters
(lines 1368--1585 and 1979--1985), and the `FCOMP` attribute
(lines 1990--2135 and 2314).

This is the source-shaped P1.A core around the judgments already ported in
`Rules.lean`.  The following deviations are deliberate.

* Isabelle's `to_hnr` and `to_hfref` are theorem-rewriting ML attributes.
  Lean's `hfref` is definitionally its quantified `hnRefine` proposition,
  so `to_hnr` and `to_hfref` below are transparent theorem converters.  They
  preserve the source workflow without hiding the resulting signature behind
  metaprogram state.
* Isabelle's `FCOMP` attribute inspects an input theorem and runs several
  normalization collections.  `FCOMP` below is a typed theorem entry point:
  elaboration infers the intermediate program and relations, and the two
  identity-composition simp lemmas perform the normalization needed by the
  current κ/name-parametric judgment.  `FCOMP_sv` is the usual source route
  that discharges `attainsSup` through single-valued result relations.
* The source's final `hfref_compI_PRE` puts `nofailT (h x)` in the guard of
  `comp_PRE`; this is retained exactly.  It is essential because `hnRefine`
  is vacuous for `fail`, and is not simplified away by the composition API.

The concrete half of `hfref` remains `κa → κb × Com`, per P4/D-m in
`Rules.lean`; conversion therefore keeps both the argument name and the
chosen destination name explicit.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## Preconditions and structural rules -/

/-- The source's `comp_PRE R P Q S`: when `S x` matters, both the outer
precondition and every relation-indexed inner precondition must hold. -/
def compPRE {α β : Type} (R : Set (β × α)) (P : α → Prop)
    (Q : α → β → Prop) (S : α → Prop) : α → Prop :=
  fun x => S x → P x ∧ ∀ y, (y, x) ∈ R → Q x y

@[simp] theorem compPRE_apply {α β : Type} (R : Set (β × α))
    (P : α → Prop) (Q : α → β → Prop) (S : α → Prop) (x : α) :
    compPRE R P Q S x ↔ (S x → P x ∧ ∀ y, (y, x) ∈ R → Q x y) :=
  Iff.rfl

/-- Source `comp_PRE_cong`, expressed with Lean's propositional equality.
The inner predicate need only agree where the composed precondition can be
observed. -/
@[congr] theorem compPRE_congr {α β : Type}
    {R R' : Set (β × α)} {P P' S S' : α → Prop}
    {Q Q' : α → β → Prop}
    (hR : R = R') (hP : ∀ x, P x ↔ P' x) (hS : ∀ x, S x ↔ S' x)
    (hQ : ∀ x y, P x → (y, x) ∈ R → S' x → (Q x y ↔ Q' x y)) :
    compPRE R P Q S = compPRE R' P' Q' S' := by
  subst R'
  funext x
  apply propext
  constructor
  · intro h hs'
    have hs : S x := (hS x).mpr hs'
    obtain ⟨hp, hq⟩ := h hs
    refine ⟨(hP x).mp hp, fun y hy => ?_⟩
    exact (hQ x y hp hy hs').mp (hq y hy)
  · intro h hs
    have hs' : S' x := (hS x).mp hs
    obtain ⟨hp', hq'⟩ := h hs'
    have hp : P x := (hP x).mpr hp'
    refine ⟨hp, fun y hy => ?_⟩
    exact (hQ x y hp hy hs').mpr (hq' y hy)

/-- Source `PRE_D1`. -/
theorem PRE_D1 {α β : Type} {R : Set (β × α)} {P Q S : α → Prop} {x : α} :
    Q x ∧ P x → compPRE R Q (fun x _ => P x) S x := by
  rintro ⟨hQ, hP⟩ _
  exact ⟨hQ, fun _ _ => hP⟩

/-- Source `PRE_D2`. -/
theorem PRE_D2 {α β : Type} {R : Set (β × α)} {P : α → β → Prop}
    {Q S : α → Prop} {x : α} :
    Q x ∧ (∀ y, (y, x) ∈ R → S x → P x y) → compPRE R Q P S x := by
  rintro ⟨hQ, hP⟩ hS
  exact ⟨hQ, fun y hy => hP y hy hS⟩

/-- Source `fref_weaken_pre`. -/
theorem fref_weaken_pre {α β γ δ : Type} {P P' : δ → Prop}
    {R : Set (γ × δ)} {S : δ → Set (β × α)}
    {f : γ → β} {g : δ → α}
    (hpre : ∀ x, P x → P' x) (h : (f, g) ∈ fref P' R S) :
    (f, g) ∈ fref P R S :=
  fun x y hP hR => h x y (hpre y hP) hR

/-- Source `hfref_cons`: weaken the logical precondition and input assertion,
and strengthen the output and result assertions. -/
theorem hfref_cons {α β κa κb : Type} {P P' : α → Prop}
    {RS RS' : (α → κa → Assn) × (α → κa → Assn)}
    {S S' : α → κa → β → κb → Assn}
    {f : κa → κb × Com} {g : α → NRest β ECost}
    (h : (f, g) ∈ hfref P RS S)
    (hpre : ∀ x, P' x → P x)
    (hin : ∀ x y, RS'.1 x y ⊢ RS.1 x y)
    (hout : ∀ x y, RS.2 x y ⊢ RS'.2 x y)
    (hres : ∀ x y a c, P' x → S x y a c ⊢ S' x y a c) :
    (f, g) ∈ hfref P' RS' S' := by
  intro c a hP'
  exact hnRefine_cons (h c a (hpre a hP')) (hin a c) (hout a c)
    (fun x y => hres a c x y hP')

/-- Source `hfref_weaken_pre`. -/
theorem hfref_weaken_pre {α β κa κb : Type} {P P' : α → Prop}
    {RS : (α → κa → Assn) × (α → κa → Assn)}
    {S : α → κa → β → κb → Assn}
    {f : κa → κb × Com} {g : α → NRest β ECost}
    (hpre : ∀ x, P x → P' x) (h : (f, g) ∈ hfref P' RS S) :
    (f, g) ∈ hfref P RS S :=
  fun c a hP => h c a (hpre a hP)

/-- Source `hfref_weaken_pre_nofail`: the old precondition is only needed
when the abstract computation is non-failing. -/
theorem hfref_weaken_pre_nofail {α β κa κb : Type} {P : α → Prop}
    {RS : (α → κa → Assn) × (α → κa → Assn)}
    {S : α → κa → β → κb → Assn}
    {f : κa → κb × Com} {g : α → NRest β ECost}
    (h : (f, g) ∈ hfref P RS S) :
    (f, g) ∈ hfref (fun x => g x |>.nofailT → P x) RS S := by
  intro c a hpre hnf
  exact h c a (hpre hnf) hnf

/-- Source `fref_PRE_D1`. -/
theorem fref_PRE_D1 {α β γ δ ε : Type} {P Q X : δ → Prop}
    {S1 : Set (ε × δ)} {R : Set (γ × δ)} {S : δ → Set (β × α)}
    {f : γ → β} {h : δ → α}
    (hr : (f, h) ∈ fref (compPRE S1 Q (fun x _ => P x) X) R S) :
    (f, h) ∈ fref (fun x => Q x ∧ P x) R S :=
  fref_weaken_pre (fun _ => PRE_D1) hr

/-- Source `fref_PRE_D2`. -/
theorem fref_PRE_D2 {α β γ δ ε : Type} {P : δ → ε → Prop}
    {Q X : δ → Prop} {S1 : Set (ε × δ)} {R : Set (γ × δ)}
    {S : δ → Set (β × α)} {f : γ → β} {h : δ → α}
    (hr : (f, h) ∈ fref (compPRE S1 Q P X) R S) :
    (f, h) ∈ fref
      (fun x => Q x ∧ ∀ y, (y, x) ∈ S1 → X x → P x y) R S :=
  fref_weaken_pre (fun _ => PRE_D2) hr

/-- Source `hfref_PRE_D1`. -/
theorem hfref_PRE_D1 {α β γ κa κb : Type} {P Q X : α → Prop}
    {S1 : Set (γ × α)} {RS : (α → κa → Assn) × (α → κa → Assn)}
    {S : α → κa → β → κb → Assn}
    {f : κa → κb × Com} {h : α → NRest β ECost}
    (hr : (f, h) ∈ hfref (compPRE S1 Q (fun x _ => P x) X) RS S) :
    (f, h) ∈ hfref (fun x => Q x ∧ P x) RS S :=
  hfref_weaken_pre (fun _ => PRE_D1) hr

/-- Source `hfref_PRE_D2`. -/
theorem hfref_PRE_D2 {α β γ κa κb : Type} {P : α → γ → Prop}
    {Q X : α → Prop} {S1 : Set (γ × α)}
    {RS : (α → κa → Assn) × (α → κa → Assn)}
    {S : α → κa → β → κb → Assn}
    {f : κa → κb × Com} {h : α → NRest β ECost}
    (hr : (f, h) ∈ hfref (compPRE S1 Q P X) RS S) :
    (f, h) ∈ hfref
      (fun x => Q x ∧ ∀ y, (y, x) ∈ S1 → X x → P x y) RS S :=
  hfref_weaken_pre (fun _ => PRE_D2) hr

/-! The source's `rr_comp` selects between a non-dependent optimization and
this dependent union.  Lean has no HOL `undefined`, so, as for `hrrCompDep`
in `Rules.lean`, we expose the always-sound dependent form directly. -/

/-- The dependent branch of source `rr_comp`. -/
def rrComp {α α' β β' γ : Type} (T : Set (α × α'))
    (R : α → Set (β × β')) (S : α' → Set (β' × γ)) (x : α') :
    Set (β × γ) :=
  {p | ∃ y, (y, x) ∈ T ∧ p ∈ relComp (R y) (S x)}

@[simp] theorem mem_rrComp {α α' β β' γ : Type} {T : Set (α × α')}
    {R : α → Set (β × β')} {S : α' → Set (β' × γ)}
    {x : α'} {c : β} {a : γ} :
    (c, a) ∈ rrComp T R S x ↔
      ∃ y, (y, x) ∈ T ∧ ∃ b, (c, b) ∈ R y ∧ (b, a) ∈ S x :=
  Iff.rfl

/-- Source `fref_compI_PRE`, using the dependent branch of `rr_comp`.
This is bounded by the repository's existing `relComp` API and requires no
new relation algebra. -/
theorem fref_compI_PRE {α α' β β' γ γ' : Type}
    {P : α → Prop} {Q : α' → Prop}
    {R1 : Set (γ × α)} {R2 : α → Set (β × β')}
    {S1 : Set (α × α')} {S2 : α' → Set (β' × γ')}
    {f : γ → β} {g : α → β'} {h : α' → γ'}
    (hA : (f, g) ∈ fref P R1 R2)
    (hB : (g, h) ∈ fref Q S1 S2) :
    (f, h) ∈ fref (compPRE S1 Q (fun _ y => P y) (fun _ => True))
      (relComp R1 S1) (rrComp S1 R2 S2) := by
  intro c a hpre hca
  obtain ⟨y, hcy, hya⟩ := hca
  have hp := hpre trivial
  refine ⟨y, hya, g y, hA c y (hp.2 y hya) hcy, ?_⟩
  exact hB y a hp.1 hya

/-! ## Signature conversion -/

/-- Lean equivalent of the source's `to_hnr`: expose one instantiated
`hnRefine` rule from an `hfref` signature. -/
theorem to_hnr {α β κa κb : Type} {P : α → Prop}
    {RS : (α → κa → Assn) × (α → κa → Assn)}
    {S : α → κa → β → κb → Assn}
    {f : κa → κb × Com} {g : α → NRest β ECost}
    (h : (f, g) ∈ hfref P RS S) {c : κa} {a : α} (hP : P a) :
    hnRefine (RS.1 a c) (f c).2 (RS.2 a c) (f c).1 (S a c) (g a) :=
  h c a hP

/-- Lean equivalent of the source's `to_hfref`: package a family of
`hnRefine` rules as one normalized signature theorem. -/
theorem to_hfref {α β κa κb : Type} {P : α → Prop}
    {RS : (α → κa → Assn) × (α → κa → Assn)}
    {S : α → κa → β → κb → Assn}
    {f : κa → κb × Com} {g : α → NRest β ECost}
    (h : ∀ (c : κa) (a : α), P a →
      hnRefine (RS.1 a c) (f c).2 (RS.2 a c) (f c).1 (S a c) (g a)) :
    (f, g) ∈ hfref P RS S :=
  h

/-! ## `FCOMP` -/

/-- Source-shaped composition before the final nofail guard is inserted. -/
theorem hfref_compI_PRE_aux {α α' β β' κa κb : Type}
    {P : α → Prop} {Q : α' → Prop}
    {RR' : (α → κa → Assn) × (α → κa → Assn)} {A : β → κb → Assn}
    {T : Set (α × α')} {U : α' → Set (β × β')}
    {f : κa → κb × Com} {g : α → NRest β ECost}
    {h : α' → NRest β' ECost}
    (hA : (f, g) ∈ hfref P RR' (fun _ _ => A))
    (hB : (g, h) ∈ fref Q T (fun x => NRest.nrestRel (U x)))
    (SC : ∀ b1 a1, attainsSup (g b1) (h a1) (U a1)) :
    (f, h) ∈ hfref (compPRE T Q (fun _ y => P y) (fun _ => True))
      (hrpComp RR' T) (hrrCompND A U) := by
  apply hfref_weaken_pre (h := hfcomp hA hB SC)
  intro x hx
  exact hx trivial

/-- Source `hfref_compI_PRE`: composition with the exact precondition
intersection used by the `FCOMP` attribute. -/
theorem hfref_compI_PRE {α α' β β' κa κb : Type}
    {P : α → Prop} {Q : α' → Prop}
    {RR' : (α → κa → Assn) × (α → κa → Assn)} {A : β → κb → Assn}
    {T : Set (α × α')} {U : α' → Set (β × β')}
    {f : κa → κb × Com} {g : α → NRest β ECost}
    {h : α' → NRest β' ECost}
    (hA : (f, g) ∈ hfref P RR' (fun _ _ => A))
    (hB : (g, h) ∈ fref Q T (fun x => NRest.nrestRel (U x)))
    (SC : ∀ b1 a1, attainsSup (g b1) (h a1) (U a1)) :
    (f, h) ∈ hfref
      (compPRE T Q (fun _ y => P y) (fun x => (h x).nofailT))
      (hrpComp RR' T) (hrrCompND A U) := by
  have hc := hfref_weaken_pre_nofail (hfref_compI_PRE_aux hA hB SC)
  simpa only [compPRE_apply, true_implies] using hc

/-- Typed Lean entry point corresponding to the source's `FCOMP` attribute.
No caller needs to apply `hfcomp` manually. -/
theorem FCOMP {α α' β β' κa κb : Type}
    {P : α → Prop} {Q : α' → Prop}
    {RR' : (α → κa → Assn) × (α → κa → Assn)} {A : β → κb → Assn}
    {T : Set (α × α')} {U : α' → Set (β × β')}
    {f : κa → κb × Com} {g : α → NRest β ECost}
    {h : α' → NRest β' ECost}
    (hA : (f, g) ∈ hfref P RR' (fun _ _ => A))
    (hB : (g, h) ∈ fref Q T (fun x => NRest.nrestRel (U x)))
    (SC : ∀ b1 a1, attainsSup (g b1) (h a1) (U a1)) :
    (f, h) ∈ hfref
      (compPRE T Q (fun _ y => P y) (fun x => (h x).nofailT))
      (hrpComp RR' T) (hrrCompND A U) :=
  hfref_compI_PRE hA hB SC

/-- `FCOMP` with the source's standard single-valued discharge. -/
theorem FCOMP_sv {α α' β β' κa κb : Type}
    {P : α → Prop} {Q : α' → Prop}
    {RR' : (α → κa → Assn) × (α → κa → Assn)} {A : β → κb → Assn}
    {T : Set (α × α')} {U : α' → Set (β × β')}
    {f : κa → κb × Com} {g : α → NRest β ECost}
    {h : α' → NRest β' ECost}
    (hA : (f, g) ∈ hfref P RR' (fun _ _ => A))
    (hB : (g, h) ∈ fref Q T (fun x => NRest.nrestRel (U x)))
    (SV : ∀ a1, SingleValued (U a1)) :
    (f, h) ∈ hfref
      (compPRE T Q (fun _ y => P y) (fun x => (h x).nofailT))
      (hrpComp RR' T) (hrrCompND A U) :=
  FCOMP hA hB fun _ a1 => attains_sup_sv (SV a1)

/-- Dependent-result counterpart of `hfref_compI_PRE`, over the existing
`hfcomp_dep` judgment. -/
theorem hfref_compI_PRE_dep {α α' β β' κa κb : Type}
    {P : α → Prop} {Q : α' → Prop}
    {RR' : (α → κa → Assn) × (α → κa → Assn)}
    {S : α → κa → β → κb → Assn}
    {T : Set (α × α')} {U : α' → Set (β × β')}
    {f : κa → κb × Com} {g : α → NRest β ECost}
    {h : α' → NRest β' ECost}
    (hA : (f, g) ∈ hfref P RR' S)
    (hB : (g, h) ∈ fref Q T (fun x => NRest.nrestRel (U x)))
    (SC : ∀ b1 a1, attainsSup (g b1) (h a1) (U a1)) :
    (f, h) ∈ hfref
      (compPRE T Q (fun _ y => P y) (fun x => (h x).nofailT))
      (hrpComp RR' T) (hrrCompDep T S U) := by
  have hc := hfref_weaken_pre_nofail (hfcomp_dep hA hB SC)
  simpa only [compPRE_apply, true_implies] using hc

/-- Typed dependent-result composition entry point. -/
theorem FCOMP_dep {α α' β β' κa κb : Type}
    {P : α → Prop} {Q : α' → Prop}
    {RR' : (α → κa → Assn) × (α → κa → Assn)}
    {S : α → κa → β → κb → Assn}
    {T : Set (α × α')} {U : α' → Set (β × β')}
    {f : κa → κb × Com} {g : α → NRest β ECost}
    {h : α' → NRest β' ECost}
    (hA : (f, g) ∈ hfref P RR' S)
    (hB : (g, h) ∈ fref Q T (fun x => NRest.nrestRel (U x)))
    (SC : ∀ b1 a1, attainsSup (g b1) (h a1) (U a1)) :
    (f, h) ∈ hfref
      (compPRE T Q (fun _ y => P y) (fun x => (h x).nofailT))
      (hrpComp RR' T) (hrrCompDep T S U) :=
  hfref_compI_PRE_dep hA hB SC

/-- `FCOMP_dep` with the standard single-valued discharge. -/
theorem FCOMP_dep_sv {α α' β β' κa κb : Type}
    {P : α → Prop} {Q : α' → Prop}
    {RR' : (α → κa → Assn) × (α → κa → Assn)}
    {S : α → κa → β → κb → Assn}
    {T : Set (α × α')} {U : α' → Set (β × β')}
    {f : κa → κb × Com} {g : α → NRest β ECost}
    {h : α' → NRest β' ECost}
    (hA : (f, g) ∈ hfref P RR' S)
    (hB : (g, h) ∈ fref Q T (fun x => NRest.nrestRel (U x)))
    (SV : ∀ a1, SingleValued (U a1)) :
    (f, h) ∈ hfref
      (compPRE T Q (fun _ y => P y) (fun x => (h x).nofailT))
      (hrpComp RR' T) (hrrCompDep T S U) :=
  FCOMP_dep hA hB fun _ a1 => attains_sup_sv (SV a1)

/-- Normalization used after composing an argument signature through the
identity relation. -/
@[simp] theorem hrpComp_diagonal {α κ : Type}
    (RS : (α → κ → Assn) × (α → κ → Assn)) :
    hrpComp RS (Set.diagonal α) = RS := by
  cases RS
  simp [hrpComp]

/-- Normalization used after composing a non-dependent result assertion
through the identity relation. -/
@[simp] theorem hrrCompND_diagonal {α β κa κb : Type}
    (A : β → κb → Assn) :
    (hrrCompND A (fun _ : α => Set.diagonal β) :
      α → κa → β → κb → Assn) = fun _ _ => A := by
  funext x y a c
  show hrComp A (Set.diagonal β) a c = A a c
  rw [hr_comp_Id2]

/-! ## Gate: refute before prove, then exercise the full API -/

namespace SignatureGate

/-- Falsification control: dropping the outer precondition from `compPRE`
would make this proposition true. -/
example : ¬ compPRE (Set.diagonal Bool) (fun _ => False)
    (fun _ _ => True) (fun _ => True) true := by
  simp [compPRE]

/-- Falsification control: dropping the relation-indexed preconditions would
make this proposition true. -/
example : ¬ compPRE (Set.univ : Set (Bool × Unit)) (fun _ => True)
    (fun _ y => y = false) (fun _ => True) () := by
  intro h
  have hf := (h trivial).2 true trivial
  simp at hf

def signatureConstFun : String → String × Com := fun _ => ("x", .const "x" 7)

def signatureRS :
    (Unit → String → Assn) × (Unit → String → Assn) :=
  ((fun _ _ => ¤¤Currency.const 1 ∗ junkCell "x"),
    (fun _ _ => (□ : Assn)))

/-- Raw `hnRefine` rule, used to exercise `to_hfref`. -/
theorem signature_hnr (c : String) :
    hnRefine (signatureRS.1 () c) (signatureConstFun c).2
      (signatureRS.2 () c) (signatureConstFun c).1 natAssn
      (NRest.returnT 7 : NRest ℕ ECost) := by
  exact hnr_const "x" 7

/-- First conversion direction: raw hnr family to one `hfref` signature. -/
theorem signature_hfref :
    (signatureConstFun, fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)) ∈
      hfref (fun _ : Unit => True) signatureRS (fun _ _ => natAssn) := by
  apply to_hfref
  intro c _ _
  exact signature_hnr c

/-- Pure/NRest identity relator used by the composition gate. -/
theorem signature_fref :
    ((fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)),
      (fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost))) ∈
      fref (fun _ : Unit => True) (Set.diagonal Unit)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  intro x y _ _
  exact NRest.nrestRel_of_le (le_of_eq (NRest.concFun_diagonal _).symm)

/-- Acceptance gate: compose a signature through a pure/NRest relation by
`FCOMP_sv`, never by applying `hfcomp`, and normalize back to the original
identity signature. -/
theorem signature_fcomp :
    (signatureConstFun, fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)) ∈
      hfref (fun _ : Unit => True) signatureRS (fun _ _ => natAssn) := by
  have h := FCOMP_sv signature_hfref signature_fref
    (fun _ => singleValued_diagonal)
  simpa [compPRE] using h

/-- Second conversion direction: consume the normalized composed signature as
an instantiated `hnRefine` rule. -/
theorem signature_hnr_roundtrip (c : String) :
    hnRefine (signatureRS.1 () c) (signatureConstFun c).2
      (signatureRS.2 () c) (signatureConstFun c).1 natAssn
      (NRest.returnT 7 : NRest ℕ ECost) :=
  to_hnr signature_fcomp (c := c) (a := ()) trivial

/-! ### Non-Unit/dependent gate -/

def boolResult : Bool → String → ℕ → String → Assn :=
  fun b _ n c => natAssn (n + cond b 0 1) c

def boolRS :
    (Bool → String → Assn) × (Bool → String → Assn) :=
  ((fun _ _ => ¤¤Currency.const 1 ∗ junkCell "x"),
    (fun _ _ => (□ : Assn)))

/-- A genuinely Bool-indexed signature: its result assertion is only the
ordinary `natAssn` on the `true` branch. -/
theorem bool_hfref :
    (signatureConstFun, fun _ : Bool => (NRest.returnT 7 : NRest ℕ ECost)) ∈
      hfref (fun b : Bool => b = true) boolRS boolResult := by
  rintro c b rfl
  exact hnr_const "x" 7

theorem bool_fref :
    ((fun _ : Bool => (NRest.returnT 7 : NRest ℕ ECost)),
      (fun _ : Bool => (NRest.returnT 7 : NRest ℕ ECost))) ∈
      fref (fun _ : Bool => True) (Set.diagonal Bool)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  intro x y _ _
  exact NRest.nrestRel_of_le (le_of_eq (NRest.concFun_diagonal _).symm)

/-- Bool-indexed acceptance for the dependent wrapper. -/
theorem bool_fcomp_dep :
    (signatureConstFun, fun _ : Bool => (NRest.returnT 7 : NRest ℕ ECost)) ∈
      hfref
        (compPRE (Set.diagonal Bool) (fun _ => True)
          (fun _ y => y = true)
          (fun _ => (NRest.returnT 7 : NRest ℕ ECost).nofailT))
        (hrpComp boolRS (Set.diagonal Bool))
        (hrrCompDep (Set.diagonal Bool) boolResult
          (fun _ => Set.diagonal ℕ)) :=
  FCOMP_dep_sv bool_hfref bool_fref (fun _ => singleValued_diagonal)

/-! ### A fixed hnr instance is not a signature -/

def fixedInstanceFun : Bool → String × Com :=
  fun _ => ("x", .const "x" 7)

def fixedInstanceRS :
    (Unit → Bool → Assn) × (Unit → Bool → Assn) :=
  ((fun _ c =>
      (if c then ¤¤Currency.skip 1 else ¤¤Currency.const 1) ∗ junkCell "x"),
    (fun _ _ => (□ : Assn)))

/-- The selected `false` instance is a valid `hnRefine` theorem. -/
theorem fixed_instance_hnr :
    hnRefine (fixedInstanceRS.1 () false) (fixedInstanceFun false).2
      (fixedInstanceRS.2 () false) (fixedInstanceFun false).1 natAssn
      (NRest.returnT 7 : NRest ℕ ECost) := by
  simpa [fixedInstanceRS, fixedInstanceFun] using hnr_const "x" 7

/-- The same family is not an `hfref`: its `true` instance offers a skip
credit to a const instruction, the concrete counterexample already proved by
`Gate.hnr_const_wrong_currency`. -/
theorem fixed_instance_not_hfref :
    ¬ ((fixedInstanceFun,
        fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)) ∈
      hfref (fun _ : Unit => True) fixedInstanceRS (fun _ _ => natAssn)) := by
  intro h
  apply Gate.hnr_const_wrong_currency
  simpa [fixedInstanceRS, fixedInstanceFun] using h true () trivial

/-- Concrete negative theorem: possessing one fixed hnr instance cannot imply
the universally name-parametric `hfref` signature. -/
theorem fixed_hnr_cannot_imply_hfref :
    ¬ (hnRefine (fixedInstanceRS.1 () false) (fixedInstanceFun false).2
          (fixedInstanceRS.2 () false) (fixedInstanceFun false).1 natAssn
          (NRest.returnT 7 : NRest ℕ ECost) →
        ((fixedInstanceFun,
          fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)) ∈
        hfref (fun _ : Unit => True) fixedInstanceRS (fun _ _ => natAssn))) := by
  intro h
  exact fixed_instance_not_hfref (h fixed_instance_hnr)

end SignatureGate

end Lax13Proofs.Refine.Sepref
