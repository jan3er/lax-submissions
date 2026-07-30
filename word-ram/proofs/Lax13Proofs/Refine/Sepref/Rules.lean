import Lax13Proofs.Refine.Sepref.Basic
import Lax13Proofs.Refine.NREST.DataRefinement

/-!
`fref` / `hfref` / `hr_comp` / `FCOMP`: the port of the composition layer
of `thys/sepref/Sepref_Rules.thy` at the pin of `Basic.lean`'s header
(`isabelle_llvm_time` @ `42dd7f5`). Extracts:
`plans/word-ram/refinement-tower/p4-sepref-extracts.md` §1 (`fref`,
`hfref`, `hfcomp`) and `p4-sepref-deep-extracts.md` §4 (`hr_comp`,
`hrp_comp`, `hrr_comp`, `attains_sup`). Where the extract was ambiguous
the fetched `Sepref_Rules.thy` was the authority (`hnr_comp` ~l. 826,
`hnr_comp1_aux` ~l. 913, `hfcomp` ~l. 929).

Relations are `Set (concrete × abstract)` throughout, per design record
fidelity note F3 and P2's convention.

## Supervisor decisions in force

P4/D-a … P4/D-g are quoted in `Basic.lean`'s header and are not repeated;
`hnRefine`'s destination parameter (P4/D-a) is what shapes `hfref` here.

## This file's judgment calls

**P4/D-m — a concrete function is a name-to-(destination, program) map.**
The source's `hfref` relates a pair
`('ai ⇒ 'bi llM) × ('a ⇒ ('b,_) nrest)`: the concrete side is a *shallow
function* from an argument value to a monadic computation. Our concrete
side is a statement in a three-address IR, so it is parameterized by the
*names* it reads and it writes its result to a name it chooses. The port
therefore takes the concrete side to be `f : κa → κb × Com` — "given the
argument cells, here is the destination cell and the program that fills
it" — and cashes it out through `hnRefine (…) (f c).2 (…) (f c).1 (…)`.
This is the shape the brief proposed; it is adopted unchanged. Fallback if
wave C's translate wants argument *lists*: `κa` is a type parameter, so
`κa := List String` or a product needs no change to any lemma here.

**P4/D-n — `hrr_comp`'s `if non_dep2 R1` is split into two definitions.**
The source writes one constant with a case distinction on
`non_dep2 R1` (`∀a b. R1 a b = R1 undefined undefined`), whose `then`
branch mentions `R1 undefined undefined` — an application of HOL's
`undefined`, which Lean has no counterpart for without an `Inhabited`
assumption on a type that carries none. So:
* `hrrCompND A U` is the source's `then` branch, i.e. exactly the value of
  the source's `hrr_comp_nondep` lemma;
* `hrrCompDep T S U` is the source's `else` branch, verbatim.
`hrrCompDep_entails_ND` / `hrrCompND_entails_Dep` prove the two are
inter-entailable at a non-dependent `S`, the second under the side
condition `∃ b, (b, x) ∈ T` — which is the *entire* content of the
source's case distinction, made explicit. `hfcomp` below is proved at
`hrrCompND`, which is what the acceptance programs use (their result
relations are non-dependent). **Backlog:** `hfcomp` at `hrrCompDep`; the
missing step is `hnr_comp`'s second `subgoal` (source ~l. 878–900), which
threads a second `b1` witness through the postcondition.

**P4/D-o — `FCOMP` is lemma content only.** The source exposes composition
as an Isabelle `attribute_setup` (`Sepref_Rules.fcomp_attrib`) that
rewrites a theorem in place. That is wave C metaprogramming; this file
ports `hfcomp`, the lemma the attribute applies, and nothing of the
attribute itself.

**P4/D-p — `attains_sup`'s `r ∈ dom M` is `M r ≠ ⊥`.** P1's cost
functions are `α → WithBot ECost` rather than partial maps, so the
source's domain membership is bottom-avoidance. Mechanical.

## Deliberate absences

* `hr_comp_precise`, `hr_comp_the_pure`, `hr_comp_assoc`,
  `hr_comp_prod_conv`: not needed by `hfcomp` and not by wave B; they are
  one-line `hrComp` unfoldings when a consumer appears.
* `one_time_attains_sup` and the `attains_sup_mop_*` family: they rest on
  the source's `one_time` predicate, which P1 did not port.
* `hnr_comp` in its full `Γ`-carrying form: `hfcomp` only ever uses it at
  `Γ = Γ' = □` (the source's own `hnr_comp1_aux`), so the frame-carrying
  generalization is left to whoever needs it; `hnRefine_frame'` recovers
  it in one step.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## 1. `fref` — pure function refinement (extracts §1) -/

/-- The source's `fref`, `[P]⇩f⇩d R → S`. -/
def fref {α β γ δ : Type} (P : δ → Prop) (R : Set (γ × δ)) (S : δ → Set (β × α)) :
    Set ((γ → β) × (δ → α)) :=
  {fg | ∀ (x : γ) (y : δ), P y → (x, y) ∈ R → (fg.1 x, fg.2 y) ∈ S y}

@[simp] theorem mem_fref_iff {α β γ δ : Type} {P : δ → Prop} {R : Set (γ × δ)}
    {S : δ → Set (β × α)} {fg : (γ → β) × (δ → α)} :
    fg ∈ fref P R S ↔ ∀ (x : γ) (y : δ), P y → (x, y) ∈ R → (fg.1 x, fg.2 y) ∈ S y :=
  Iff.rfl

/-- The source's `freft`, `R →⇩f⇩d S`. -/
abbrev freft {α β γ δ : Type} (R : Set (γ × δ)) (S : δ → Set (β × α)) :
    Set ((γ → β) × (δ → α)) := fref (fun _ => True) R S

/-- The source's `freftnd`, `R →⇩f S`. -/
abbrev freftnd {α β γ δ : Type} (R : Set (γ × δ)) (S : Set (β × α)) :
    Set ((γ → β) × (δ → α)) := fref (fun _ => True) R (fun _ => S)

/-- The source's `frefnd`, `[P]⇩f R → S`. -/
abbrev frefnd {α β γ δ : Type} (P : δ → Prop) (R : Set (γ × δ)) (S : Set (β × α)) :
    Set ((γ → β) × (δ → α)) := fref P R (fun _ => S)

/-! ## 2. `hr_comp` — assertion/relation composition (deep-extracts §4) -/

/-- The source's `hr_comp R1 R2 a c ≡ EXS b. R1 b c ** ↑((b,a)∈R2)`. -/
def hrComp {α β κ : Type} (R1 : β → κ → Assn) (R2 : Set (β × α)) : α → κ → Assn :=
  fun a c => ∃ᵃ b, R1 b c ∗ ⌜(b, a) ∈ R2⌝

@[simp] theorem hrComp_def {α β κ : Type} (R1 : β → κ → Assn) (R2 : Set (β × α)) (a : α)
    (c : κ) : hrComp R1 R2 a c = ∃ᵃ b, R1 b c ∗ ⌜(b, a) ∈ R2⌝ := rfl

/-- The source's `hrp_comp`. -/
def hrpComp {α δ κb κc : Type} (RR' : (δ → κb → Assn) × (δ → κc → Assn)) (S : Set (δ × α)) :
    (α → κb → Assn) × (α → κc → Assn) := (hrComp RR'.1 S, hrComp RR'.2 S)

/-- The source's `hrr_comp` at a non-dependent result assertion — the
value of its `hrr_comp_nondep` lemma (P4/D-n). -/
def hrrCompND {α β β' κa κb : Type} (A : β → κb → Assn) (U : α → Set (β × β')) :
    α → κa → β' → κb → Assn := fun x _ a c => hrComp A (U x) a c

/-- The source's `hrr_comp`, `else` branch, verbatim (P4/D-n). -/
def hrrCompDep {α α' β β' κa κb : Type} (T : Set (α × α'))
    (S : α → κa → β → κb → Assn) (U : α' → Set (β × β')) :
    α' → κa → β' → κb → Assn :=
  fun x y a c => ∃ᵃ b, ⌜(b, x) ∈ T⌝ ∗ hrComp (S b y) (U x) a c

/-- The source's `hr_compI`. -/
theorem hr_compI {α β κ : Type} {R1 : β → κ → Assn} {R2 : Set (β × α)} {a : α} {b : β} {c : κ}
    (h : (b, a) ∈ R2) : R1 b c ⊢ hrComp R1 R2 a c := by
  intro hh hp
  refine ⟨b, ?_⟩
  have : (R1 b c ∗ □) hh := by rwa [sepConj_emp]
  rwa [← predLift_of_true h] at this

/-- The source's `hr_comp_Id1`: composing with the identity assertion is
composing nothing. -/
@[simp] theorem hr_comp_Id1 {α β : Type} (R : Set (β × α)) :
    hrComp (pureAssn (Set.diagonal β)) R = pureAssn R := by
  funext a c
  funext hh
  refine propext ⟨?_, ?_⟩
  · rintro ⟨b, hb⟩
    obtain ⟨hbR, hcb, h0⟩ := sepConj_predLift_iff.1 hb
    have hcb' : c = b := hcb
    subst hcb'
    exact ⟨hbR, h0⟩
  · rintro ⟨hc, h0⟩
    exact ⟨c, sepConj_predLift_iff.2 ⟨hc, rfl, h0⟩⟩

/-- The source's `hr_comp_Id2`. -/
@[simp] theorem hr_comp_Id2 {α κ : Type} (R : α → κ → Assn) :
    hrComp R (Set.diagonal α) = R := by
  funext a c
  funext hh
  refine propext ⟨?_, ?_⟩
  · rintro ⟨b, hb⟩
    obtain ⟨hba, hR⟩ := sepConj_predLift_iff.1 hb
    have hba' : b = a := hba
    subst hba'
    exact hR
  · intro hp
    exact ⟨a, sepConj_predLift_iff.2 ⟨rfl, hp⟩⟩

/-- The source's `hrr_comp_nondep`, as a definitional identity (P4/D-n). -/
theorem hrr_comp_nondep {α β β' κa κb : Type} (A : β → κb → Assn) (U : α → Set (β × β')) :
    (hrrCompND A U : α → κa → β' → κb → Assn) = fun x _ => hrComp A (U x) := rfl

/-- One half of the source's `if non_dep2 …` (P4/D-n): the dependent form
always implies the non-dependent one. -/
theorem hrrCompDep_entails_ND {α α' β β' κa κb : Type} (T : Set (α × α'))
    (A : β → κb → Assn) (U : α' → Set (β × β')) (x : α') (y : κa) (a : β') (c : κb) :
    hrrCompDep T (fun _ _ => A) U x y a c ⊢ (hrrCompND A U : α' → κa → β' → κb → Assn) x y a c := by
  rintro _ ⟨b, hb⟩
  exact (predLift_sepConj_iff.1 hb).2

/-- The other half, under the source's implicit side condition. -/
theorem hrrCompND_entails_Dep {α α' β β' κa κb : Type} {T : Set (α × α')}
    {A : β → κb → Assn} {U : α' → Set (β × β')} {x : α'} {y : κa} {a : β'} {c : κb} {b : α}
    (hb : (b, x) ∈ T) :
    (hrrCompND A U : α' → κa → β' → κb → Assn) x y a c ⊢ hrrCompDep T (fun _ _ => A) U x y a c :=
  fun _ hp => ⟨b, predLift_sepConj_iff.2 ⟨hb, hp⟩⟩

/-! ## 3. `attains_sup` (deep-extracts §4, P4/D-p) -/

/-- The source's `attains_sup`: the supremum the data refinement takes on
the concrete side is *attained*, so a concrete cost is bounded by *some*
single abstract cost rather than only by their supremum. -/
def attainsSup {β β' : Type} (m : NRest β ECost) (m' : NRest β' ECost)
    (RR : Set (β × β')) : Prop :=
  ∀ (r : β) (M' : β' → WithBot ECost) (M : β → WithBot ECost),
    m = .rest M → m' = .rest M' → M r ≠ ⊥ → (∃ a, (r, a) ∈ RR) →
      sSup {u : WithBot ECost | ∃ a, (r, a) ∈ RR ∧ u = M' a} ∈
        {u : WithBot ECost | ∃ a, (r, a) ∈ RR ∧ u = M' a}

/-- The source's `single_valued_SupinSup`. -/
theorem singleValued_sSup_mem {β β' : Type} {RR : Set (β × β')}
    (hsv : SingleValued RR) (M' : β' → WithBot ECost) {r : β} (h : ∃ a, (r, a) ∈ RR) :
    sSup {u : WithBot ECost | ∃ a, (r, a) ∈ RR ∧ u = M' a} ∈
      {u : WithBot ECost | ∃ a, (r, a) ∈ RR ∧ u = M' a} := by
  obtain ⟨a, ha⟩ := h
  have hset : {u : WithBot ECost | ∃ a, (r, a) ∈ RR ∧ u = M' a} = {M' a} := by
    ext u
    refine ⟨?_, ?_⟩
    · rintro ⟨a', ha', rfl⟩
      rw [hsv r a' a ha' ha]
      rfl
    · rintro rfl
      exact ⟨a, ha, rfl⟩
  rw [hset, sSup_singleton]
  rfl

/-- The source's `attains_sup_sv`. -/
theorem attains_sup_sv {β β' : Type} {m : NRest β ECost} {m' : NRest β' ECost}
    {RR : Set (β × β')} (hsv : SingleValued RR) : attainsSup m m' RR :=
  fun _ M' _ _ _ _ h => singleValued_sSup_mem hsv M' h

/-- The source's `aux'` / `aux_attains_sup`: under `attainsSup`, a data
refinement bounds each concrete cost by one abstract cost. -/
theorem aux_attains_sup {β β' : Type} {M : β → WithBot ECost} {M' : β' → WithBot ECost}
    {RR : Set (β × β')} {r : β} {cr : ECost}
    (has : attainsSup (NRest.rest M) (NRest.rest M') RR)
    (hle : NRest.rest M ≤ NRest.concFun RR (NRest.rest M'))
    (hcr : (cr : WithBot ECost) ≤ M r) :
    ∃ r', (r, r') ∈ RR ∧ M r ≤ M' r' := by
  rw [NRest.concFun_rest, NRest.rest_le_rest_iff] at hle
  have hlr : M r ≤ sSup {u : WithBot ECost | ∃ a, (r, a) ∈ RR ∧ u = M' a} := hle r
  have hne : M r ≠ ⊥ := by
    intro hbot
    rw [hbot, le_bot_iff] at hcr
    exact WithBot.coe_ne_bot hcr
  have hex : ∃ a, (r, a) ∈ RR := by
    by_contra hno
    refine hne (le_bot_iff.1 (le_trans hlr (sSup_le ?_)))
    rintro u ⟨a, ha, rfl⟩
    exact absurd ⟨a, ha⟩ hno
  obtain ⟨r', hr', hsup⟩ := has r M' M rfl rfl hne hex
  exact ⟨r', hr', hsup ▸ hlr⟩

/-! ## 4. `hfref` (extracts §1, P4/D-a + P4/D-m) -/

/-- The source's `hfref`, `[P]⇩a⇩d RS → T`, with the concrete side a
name-to-(destination, program) map (P4/D-m). -/
def hfref {α β κa κb : Type} (P : α → Prop)
    (RS : (α → κa → Assn) × (α → κa → Assn))
    (T : α → κa → β → κb → Assn) :
    Set ((κa → κb × Com) × (α → NRest β ECost)) :=
  {fg | ∀ (c : κa) (a : α), P a →
    hnRefine (RS.1 a c) (fg.1 c).2 (RS.2 a c) (fg.1 c).1 (T a c) (fg.2 a)}

@[simp] theorem mem_hfref_iff {α β κa κb : Type} {P : α → Prop}
    {RS : (α → κa → Assn) × (α → κa → Assn)} {T : α → κa → β → κb → Assn}
    {fg : (κa → κb × Com) × (α → NRest β ECost)} :
    fg ∈ hfref P RS T ↔ ∀ (c : κa) (a : α), P a →
      hnRefine (RS.1 a c) (fg.1 c).2 (RS.2 a c) (fg.1 c).1 (T a c) (fg.2 a) := Iff.rfl

/-- The source's `hfrefnd`, `[P]⇩a RS → T`. -/
abbrev hfrefnd {α β κa κb : Type} (P : α → Prop)
    (RS : (α → κa → Assn) × (α → κa → Assn)) (T : β → κb → Assn) :
    Set ((κa → κb × Com) × (α → NRest β ECost)) := hfref P RS (fun _ _ => T)

/-- The source's `hfreft`, `RS →⇩a⇩d T`. -/
abbrev hfreft {α β κa κb : Type} (RS : (α → κa → Assn) × (α → κa → Assn))
    (T : α → κa → β → κb → Assn) : Set ((κa → κb × Com) × (α → NRest β ECost)) :=
  hfref (fun _ => True) RS T

/-- The source's `hfreftnd`, `RS →⇩a T`. -/
abbrev hfreftnd {α β κa κb : Type} (RS : (α → κa → Assn) × (α → κa → Assn))
    (T : β → κb → Assn) : Set ((κa → κb × Com) × (α → NRest β ECost)) :=
  hfref (fun _ => True) RS (fun _ _ => T)

/-! ## 5. `hfcomp` — the content of the `FCOMP` attribute (P4/D-o)

The source's chain is `hnr_comp` → `hnr_comp1_aux` → `hfcomp`. At
`Γ = Γ' = □` (which is all `hfcomp` uses) the first two collapse into one
step, so the proof below is `hnr_comp`'s first `subgoal` inlined: open the
`hrComp` existential in the precondition, read off the witness `b1`, run
the concrete rule at `b1`, and move the result across `U a1` with
`aux_attains_sup`. -/

/-- The source's `hfcomp`, at non-dependent result relations (P4/D-n). -/
theorem hfcomp {α α' β β' κa κb : Type} {P : α → Prop} {Q : α' → Prop}
    {RR' : (α → κa → Assn) × (α → κa → Assn)} {A : β → κb → Assn}
    {T : Set (α × α')} {U : α' → Set (β × β')}
    {f : κa → κb × Com} {g : α → NRest β ECost} {h : α' → NRest β' ECost}
    (hA : (f, g) ∈ hfref P RR' (fun _ _ => A))
    (hB : (g, h) ∈ fref Q T (fun x => NRest.nrestRel (U x)))
    (SC : ∀ (b1 : α) (a1 : α'), attainsSup (g b1) (h a1) (U a1)) :
    (f, h) ∈ hfref (fun a => Q a ∧ ∀ a', (a', a) ∈ T → P a')
      (hrpComp RR' T) (hrrCompND A U) := by
  intro c a1 hQP
  obtain ⟨hQ, hP⟩ := hQP
  intro _ M F s cr hm hs
  have hm' : h a1 = NRest.rest M := hm
  -- (1) read the abstract witness `b1` out of the composed precondition.
  rw [show (hrpComp RR' T).1 = hrComp RR'.1 T from rfl, hrComp_def, sepEx_sepConj] at hs
  obtain ⟨b1, hb1⟩ := hs
  have hperm : ((RR'.1 b1 c ∗ ⌜(b1, a1) ∈ T⌝) ∗ F)
      = ((⌜(b1, a1) ∈ T⌝ : Assn) ∗ (RR'.1 b1 c ∗ F)) := by ac_rfl
  rw [hperm] at hb1
  obtain ⟨hT, hs'⟩ := predLift_sepConj_iff.1 hb1
  -- (2) the pure step, at `b1`.
  have hgh : (g b1, h a1) ∈ NRest.nrestRel (U a1) := hB b1 a1 hQ hT
  have hgle : g b1 ≤ NRest.concFun (U a1) (NRest.rest M) := by
    have hx := NRest.nrestRel_le hgh
    rwa [hm'] at hx
  cases hgb : g b1 with
  | fail =>
    rw [hgb, NRest.concFun_rest] at hgle
    exact absurd hgle (NRest.not_fail_le_rest _)
  | rest Mb =>
    -- (3) the concrete step, at `b1`.
    obtain ⟨rb, C, hC, w⟩ := hnRefineD (F := F) (hA c b1 (hP b1 hT)) hgb hs'
    -- (4) move the result across `U a1`.
    have has : attainsSup (NRest.rest Mb) (NRest.rest M) (U a1) := by
      have hx := SC b1 a1
      rwa [hgb, hm'] at hx
    obtain ⟨ra, hra, hMle⟩ :=
      aux_attains_sup (cr := C) has (by rwa [hgb] at hgle) hC
    refine ⟨ra, C, le_trans hC hMle, wp_mono_ir (fun _ q hq => ?_) w⟩
    show irSTATE (hrComp RR'.2 T a1 c ∗ hrrCompND A U a1 c ra (f c).1 ∗ F ∗ GC) q
    refine start_entailsE hq
      (conj_entails_mono (hr_compI hT) (conj_entails_mono (hr_compI hra) (entails_refl (F ∗ GC))))

/-- The source's `hfcomp` under `single_valued`, the discharge route
`attains_sup_sv` provides. -/
theorem hfcomp_sv {α α' β β' κa κb : Type} {P : α → Prop} {Q : α' → Prop}
    {RR' : (α → κa → Assn) × (α → κa → Assn)} {A : β → κb → Assn}
    {T : Set (α × α')} {U : α' → Set (β × β')}
    {f : κa → κb × Com} {g : α → NRest β ECost} {h : α' → NRest β' ECost}
    (hA : (f, g) ∈ hfref P RR' (fun _ _ => A))
    (hB : (g, h) ∈ fref Q T (fun x => NRest.nrestRel (U x)))
    (SV : ∀ a1 : α', SingleValued (U a1)) :
    (f, h) ∈ hfref (fun a => Q a ∧ ∀ a', (a', a) ∈ T → P a')
      (hrpComp RR' T) (hrrCompND A U) :=
  hfcomp hA hB fun _ a1 => attains_sup_sv (SV a1)

/-! ## 6. Gate (refute-before-prove)

The composition layer is exercised on the `const` rule of `Basic.lean`
composed with the identity data refinement, plus one negative control on
`attainsSup`'s side condition. -/

namespace Gate

/-- `hnr_const` packaged as an `hfref` fact: for any argument cell, write
the literal `7` into the cell `"x"`. -/
def constFun : String → String × Com := fun _ => ("x", .const "x" 7)

/-- Its `hfref` statement: the argument's assertion is a junk cell and the
credits, and the result assertion is `natAssn` (P4/D-m's shape). -/
theorem const_hfref :
    (constFun, fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)) ∈
      hfref (fun _ : Unit => True)
        ((fun _ (_ : String) => ¤¤Currency.const 1 ∗ junkCell "x"),
          (fun _ (_ : String) => (□ : Assn)))
        (fun _ _ => natAssn) :=
  fun _ _ _ => hnr_const "x" 7

/-- The identity data refinement, as an `fref` fact. -/
theorem const_fref :
    ((fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)),
      (fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost))) ∈
      fref (fun _ : Unit => True) (Set.diagonal Unit)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  intro x y _ _
  exact NRest.nrestRel_of_le (le_of_eq (NRest.concFun_diagonal _).symm)

/-- Positive control: `hfcomp` composes the two, with `attainsSup`
discharged through `attains_sup_sv`. -/
theorem const_hfcomp :
    (constFun, fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)) ∈
      hfref (fun a => True ∧ ∀ a', (a', a) ∈ Set.diagonal Unit → True)
        (hrpComp
          ((fun _ (_ : String) => ¤¤Currency.const 1 ∗ junkCell "x"),
            (fun _ (_ : String) => (□ : Assn))) (Set.diagonal Unit))
        (hrrCompND natAssn (fun _ : Unit => Set.diagonal ℕ)) :=
  hfcomp_sv const_hfref const_fref fun _ => singleValued_diagonal

/-- Reading the composed rule back: at the identity relations it is the
uncomposed one, because `hr_comp_Id2` collapses both sides. -/
example :
    (hrrCompND natAssn (fun _ : Unit => Set.diagonal ℕ) : Unit → String → ℕ → String → Assn)
      = fun _ _ => natAssn := by
  funext x y a c
  show hrComp natAssn (Set.diagonal ℕ) a c = natAssn a c
  rw [hr_comp_Id2]

/-- **Negative control 1 — composition does not change the value.**
Composing with the identity relation cannot turn ownership of `3` into a
claim about `4`. -/
theorem hrComp_wrong_value :
    ¬ (natAssn 3 "x" ⊢ hrComp natAssn (Set.diagonal ℕ) 4 "x") := by
  intro hent
  have h0 : natAssn 3 "x" ((Cells.single "x" (3 : Val), 0), (0 : ECost)) := ⟨⟨rfl, rfl⟩, rfl⟩
  have h1 := hent _ h0
  rw [hr_comp_Id2 natAssn] at h1
  have h2 : Cells.single "x" (3 : Val) = Cells.single "x" (4 : Val) := h1.1.1
  have h3 := congrFun h2 "x"
  simp [Cells.single] at h3

/-- **Negative control 2 — `attains_sup_sv`'s hypothesis has content.**
`Set.univ` on a two-element abstract type is not single-valued, so the
`attainsSup` side condition of `hfcomp` cannot be discharged that way. -/
theorem not_singleValued_univ : ¬ SingleValued (Set.univ : Set (Unit × Bool)) := by
  intro h
  exact absurd (h () true false trivial trivial) (by decide)

end Gate

end Lax13Proofs.Refine.Sepref
