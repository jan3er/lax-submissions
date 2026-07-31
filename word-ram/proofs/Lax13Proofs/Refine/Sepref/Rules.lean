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
source's case distinction, made explicit. The source's single `hfcomp`
therefore becomes two theorems, one per branch: `hfcomp` at `hrrCompND`
(what the acceptance programs use — their result relations are
non-dependent) and `hfcomp_dep` at `hrrCompDep`, the port of `hnr_comp`'s
second `subgoal` (source ~l. 878–900), which threads a second `b1`
witness through the postcondition. Both are proved; the backlog is
closed. Note `hfcomp_dep` needs no hypothesis on `S` at all, so the
source's `non_dep2` test is a convenience (a tidier postcondition when
`S` happens to be constant), not a soundness side condition — splitting
the constant loses nothing.

**P4/D-o — `FCOMP` was lemma content only in this module.** The source
exposes composition as an Isabelle `attribute_setup`
(`Sepref_Rules.fcomp_attrib`) that rewrites a theorem in place. This file
ports the underlying `hfcomp` calculus. Tower-expansion P1.A subsequently
adds the source precondition/conversion layer in `Signature.lean`, the
goal-directed `sepref_fcomp` frontend in `SignatureTool.lean`, and its
normalization laws in `SignatureNorm.lean`; keeping that machinery in
satellite modules avoids a cycle through this calculus module.

**P4/D-p — `attains_sup`'s `r ∈ dom M` is `M r ≠ ⊥`.** P1's cost
functions are `α → WithBot ECost` rather than partial maps, so the
source's domain membership is bottom-avoidance. Mechanical.

**P4/D-q — `hnRefine_hrrCompDep_pre` is an addition, not a port.** The
source has no elimination lemma for a `hrr_comp` assertion appearing as
the *next* step's precondition: Isabelle's `sepref` automation opens the
two existentials inline, inside whatever tactic script consumes the rule.
A Lean consumer has no such script, so §5b names the elimination once —
`hnr_pre_ex_conv` / `hnr_pre_pure_conv` twice over, handing the consumer
both the `T`-witness and the `U`-witness. Nothing about it is a deviation
from the source's *content*; it exists because the source's proof text is
not a reusable object here. `const_dep_bind` is its consumer test.

## Deliberate absences

* The source-supported `hr_comp_the_pure`, `hr_comp_assoc`, and
  `hr_comp_prod_conv` laws live in tower-expansion P1.A's
  `SignatureNorm.lean`; the source's `hr_comp_precise` text is commented
  out and therefore intentionally has no exported theorem here.
* Iterated dependent composition is normalized by the correlated-residue
  law `hrrCompDep_flatten` in `SignatureFlatten.lean`. The residue is
  essential: independently composing the input and output relations is
  refutable because it forgets that both layers share the same witness.
* The source's `one_time`, `one_time_attains_sup`, and
  `attains_sup_mop_{return,spec}` family is now ported in
  tower-expansion P1.A's `SignatureNorm.lean`.
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
step, so the proofs below are `hnr_comp`'s two `subgoal`s inlined: open
the `hrComp` existential in the precondition, read off the witness `b1`,
run the concrete rule at `b1`, and move the result across `U a1` with
`aux_attains_sup`. `hfcomp` is the first `subgoal` (non-dependent result
relation), `hfcomp_dep` the second (P4/D-n). -/

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

/-- The dependent counterpart of `hr_compI`: the introduction rule the
source's second `subgoal` performs inline as two `exI`s (a witness `b` for
the `T`-conjunct, then `hr_compI`'s witness). -/
theorem hrrCompDep_I {α α' β β' κa κb : Type} {T : Set (α × α')}
    {S : α → κa → β → κb → Assn} {U : α' → Set (β × β')}
    {x : α'} {y : κa} {a : β'} {c : κb} {b : α} {rb : β}
    (hT : (b, x) ∈ T) (hU : (rb, a) ∈ U x) :
    S b y rb c ⊢ hrrCompDep T S U x y a c :=
  fun _ hp => ⟨b, predLift_sepConj_iff.2 ⟨hT, hr_compI hU _ hp⟩⟩

/-- The source's `hfcomp` at a *dependent* result relation (P4/D-n): the
same chain, with `hnr_comp`'s second `subgoal` (source ~l. 878–900) in
place of the first. The only difference from `hfcomp` is the last step —
the postcondition now carries the abstract witness `b1` a second time,
through `hrrCompDep`'s `⌜(b1, a1) ∈ T⌝` conjunct. -/
theorem hfcomp_dep {α α' β β' κa κb : Type} {P : α → Prop} {Q : α' → Prop}
    {RR' : (α → κa → Assn) × (α → κa → Assn)} {S : α → κa → β → κb → Assn}
    {T : Set (α × α')} {U : α' → Set (β × β')}
    {f : κa → κb × Com} {g : α → NRest β ECost} {h : α' → NRest β' ECost}
    (hA : (f, g) ∈ hfref P RR' S)
    (hB : (g, h) ∈ fref Q T (fun x => NRest.nrestRel (U x)))
    (SC : ∀ (b1 : α) (a1 : α'), attainsSup (g b1) (h a1) (U a1)) :
    (f, h) ∈ hfref (fun a => Q a ∧ ∀ a', (a', a) ∈ T → P a')
      (hrpComp RR' T) (hrrCompDep T S U) := by
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
    show irSTATE (hrComp RR'.2 T a1 c ∗ hrrCompDep T S U a1 c ra (f c).1 ∗ F ∗ GC) q
    refine start_entailsE hq
      (conj_entails_mono (hr_compI hT)
        (conj_entails_mono (hrrCompDep_I hT hra) (entails_refl (F ∗ GC))))

/-- `hfcomp_dep` under `single_valued`, mirroring `hfcomp_sv`. -/
theorem hfcomp_dep_sv {α α' β β' κa κb : Type} {P : α → Prop} {Q : α' → Prop}
    {RR' : (α → κa → Assn) × (α → κa → Assn)} {S : α → κa → β → κb → Assn}
    {T : Set (α × α')} {U : α' → Set (β × β')}
    {f : κa → κb × Com} {g : α → NRest β ECost} {h : α' → NRest β' ECost}
    (hA : (f, g) ∈ hfref P RR' S)
    (hB : (g, h) ∈ fref Q T (fun x => NRest.nrestRel (U x)))
    (SV : ∀ a1 : α', SingleValued (U a1)) :
    (f, h) ∈ hfref (fun a => Q a ∧ ∀ a', (a', a) ∈ T → P a')
      (hrpComp RR' T) (hrrCompDep T S U) :=
  hfcomp_dep hA hB fun _ a1 => attains_sup_sv (SV a1)

/-! ## 5b. The frame-carrying `hnr_comp` at a dependent `S`

`hfcomp_dep` uses `hnr_comp` only at `Γ = Γ' = □`. A *bind* context does
not: there the composed step runs with the rest of the ownership in the
frame, and the frame sits inside the hypothesis (`R1 b1 c1 ∗ Γ`), so it
cannot be recovered from the `□` case by `hnRefine_frame'` — the frame
would have to be removed from a hypothesis, not added to a conclusion.
(This retracts the file's earlier deliberate-absences note, which claimed
`hnRefine_frame'` recovered the frame-carrying form in one step. It does
not.) The source's `hnr_comp` (l. 826) is therefore ported in full. The
proof is `hfcomp_dep`'s with one extra re-association: the `ac_rfl`
permutation now has to move `Γ` next to `R1 b1 c1` as well. -/

/-- The source's `hnr_comp` (l. 826) at a dependent result relation, with
the frame `Γ` / `Γ'` carried. Quantifier structure is the source's:
Isabelle's `⋀` binds fresh, so `hR` ranges over all `c1'` and `hS` / `hPQ`
over all `a1'` even though the conclusion fixes `c1` / `a1`, while `SC`
ranges over `b1` only. `hfref` and `fref` supply exactly those shapes. -/
theorem hnr_comp_dep {α α' β β' κa κb : Type} {P : α → Prop} {Q : α' → Prop}
    {R1 R1p : α → κa → Assn} {Γ Γ' : Assn} {S : α → κa → β → κb → Assn}
    {T : Set (α × α')} {U : α' → Set (β × β')}
    {c : κa → κb × Com} {g : α → NRest β ECost} {h : α' → NRest β' ECost}
    {c1 : κa} {a1 : α'}
    (hR : ∀ (b1 : α) (c1' : κa), P b1 →
      hnRefine (R1 b1 c1' ∗ Γ) (c c1').2 (R1p b1 c1' ∗ Γ') (c c1').1 (S b1 c1') (g b1))
    (hS : ∀ (a1' : α') (b1 : α), Q a1' → (b1, a1') ∈ T →
      (g b1, h a1') ∈ NRest.nrestRel (U a1'))
    (hPQ : ∀ (a1' : α') (b1 : α), Q a1' → (b1, a1') ∈ T → P b1)
    (hQ : Q a1)
    (SC : ∀ b1 : α, attainsSup (g b1) (h a1) (U a1)) :
    hnRefine (hrComp R1 T a1 c1 ∗ Γ) (c c1).2 (hrComp R1p T a1 c1 ∗ Γ')
      (c c1).1 (hrrCompDep T S U a1 c1) (h a1) := by
  intro _ M F s cr hm hs
  have hm' : h a1 = NRest.rest M := hm
  -- (1) read the abstract witness `b1` out of the composed precondition.
  rw [sepConj_assoc, hrComp_def, sepEx_sepConj] at hs
  obtain ⟨b1, hb1⟩ := hs
  have hperm : ((R1 b1 c1 ∗ ⌜(b1, a1) ∈ T⌝) ∗ (Γ ∗ F))
      = ((⌜(b1, a1) ∈ T⌝ : Assn) ∗ ((R1 b1 c1 ∗ Γ) ∗ F)) := by ac_rfl
  rw [hperm] at hb1
  obtain ⟨hT, hs'⟩ := predLift_sepConj_iff.1 hb1
  -- (2) the pure step, at `b1`.
  have hgle : g b1 ≤ NRest.concFun (U a1) (NRest.rest M) := by
    have hx := NRest.nrestRel_le (hS a1 b1 hQ hT)
    rwa [hm'] at hx
  cases hgb : g b1 with
  | fail =>
    rw [hgb, NRest.concFun_rest] at hgle
    exact absurd hgle (NRest.not_fail_le_rest _)
  | rest Mb =>
    -- (3) the concrete step, at `b1`, under the carried frame.
    obtain ⟨rb, C, hC, w⟩ := hnRefineD (F := F) (hR b1 c1 (hPQ a1 b1 hQ hT)) hgb hs'
    -- (4) move the result across `U a1`.
    have has : attainsSup (NRest.rest Mb) (NRest.rest M) (U a1) := by
      have hx := SC b1
      rwa [hgb, hm'] at hx
    obtain ⟨ra, hra, hMle⟩ :=
      aux_attains_sup (cr := C) has (by rwa [hgb] at hgle) hC
    refine ⟨ra, C, le_trans hC hMle, wp_mono_ir (fun _ q hq => ?_) w⟩
    show irSTATE ((hrComp R1p T a1 c1 ∗ Γ') ∗ hrrCompDep T S U a1 c1 ra (c c1).1 ∗ F ∗ GC) q
    refine start_entailsE hq
      (conj_entails_mono (conj_entails_mono (hr_compI hT) (entails_refl Γ'))
        (conj_entails_mono (hrrCompDep_I hT hra) (entails_refl (F ∗ GC))))

/-- The elimination rule the bind context needs on the *other* side: a
`hrrCompDep` postcondition arriving as the next step's precondition is
opened by `hnr_pre_ex_conv` / `hnr_pre_pure_conv` twice — once for the
`T`-witness `b`, once for `hrComp`'s `U`-witness `rb` — handing the
consumer both memberships. -/
theorem hnRefine_hrrCompDep_pre {α α' β β' κa κb κ γ : Type}
    {T : Set (α × α')} {S : α → κa → β → κb → Assn} {U : α' → Set (β × β')}
    {x : α'} {y : κa} {a : β'} {cc : κb} {Γ₁ Γ' : Assn} {prog : Com} {d : κ}
    {R : γ → κ → Assn} {m : NRest γ ECost}
    (hk : ∀ (b : α) (rb : β), (b, x) ∈ T → (rb, a) ∈ U x →
      hnRefine (S b y rb cc ∗ Γ₁) prog Γ' d R m) :
    hnRefine (hrrCompDep T S U x y a cc ∗ Γ₁) prog Γ' d R m := by
  show hnRefine ((∃ᵃ b, ⌜(b, x) ∈ T⌝ ∗ hrComp (S b y) (U x) a cc) ∗ Γ₁) prog Γ' d R m
  rw [sepEx_sepConj]
  refine hnr_pre_ex_conv.2 fun b => ?_
  rw [sepConj_assoc]
  refine hnr_pre_pure_conv.2 fun hb => ?_
  show hnRefine ((∃ᵃ rb, S b y rb cc ∗ ⌜(rb, a) ∈ U x⌝) ∗ Γ₁) prog Γ' d R m
  rw [sepEx_sepConj]
  refine hnr_pre_ex_conv.2 fun rb => ?_
  have hperm : ((S b y rb cc ∗ ⌜(rb, a) ∈ U x⌝) ∗ Γ₁)
      = ((⌜(rb, a) ∈ U x⌝ : Assn) ∗ (S b y rb cc ∗ Γ₁)) := by ac_rfl
  rw [hperm]
  exact hnr_pre_pure_conv.2 fun hrb => hk b rb hb hrb

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

/-! ### Dependent composition (`hfcomp_dep`)

A genuinely dependent first rule: the abstract argument is a `Bool` and the
result assertion shifts with it, so `hrrCompDep`'s `⌜(b, x) ∈ T⌝` conjunct
is doing real work. -/

/-- The dependent result assertion: at `true` it is `natAssn`, at `false`
it claims the result cell holds one *more* than the abstract value. -/
def depS : Bool → String → ℕ → String → Assn :=
  fun b _ a c => natAssn (a + cond b 0 1) c

/-- The argument relation admitting only `true`. -/
def depT : Set (Bool × Unit) := {p | p.1 = true}

/-- The concrete rule of `Basic.lean` read at the dependent shape: it is
available exactly under the precondition `b = true`, where `depS` is
`natAssn`. -/
theorem const_hfref_dep :
    (constFun, fun _ : Bool => (NRest.returnT 7 : NRest ℕ ECost)) ∈
      hfref (fun b : Bool => b = true)
        ((fun _ (_ : String) => ¤¤Currency.const 1 ∗ junkCell "x"),
          (fun _ (_ : String) => (□ : Assn)))
        depS := by
  rintro c b rfl
  exact hnr_const "x" 7

/-- The pure step across `depT`. -/
theorem const_fref_dep :
    ((fun _ : Bool => (NRest.returnT 7 : NRest ℕ ECost)),
      (fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost))) ∈
      fref (fun _ : Unit => True) depT (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  intro x y _ _
  exact NRest.nrestRel_of_le (le_of_eq (NRest.concFun_diagonal _).symm)

/-- Positive control: `hfcomp_dep` composes the two end to end, at a
result relation that is *not* of the form `fun _ _ => A`. -/
theorem const_hfcomp_dep :
    (constFun, fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)) ∈
      hfref (fun a => True ∧ ∀ a', (a', a) ∈ depT → a' = true)
        (hrpComp
          ((fun _ (_ : String) => ¤¤Currency.const 1 ∗ junkCell "x"),
            (fun _ (_ : String) => (□ : Assn))) depT)
        (hrrCompDep depT depS (fun _ : Unit => Set.diagonal ℕ)) :=
  hfcomp_dep_sv const_hfref_dep const_fref_dep fun _ => singleValued_diagonal

/-- **Negative control 3 — the dependent postcondition genuinely carries
the `⌜(b, x) ∈ T⌝` witness.** Ownership produced at the *unrelated*
abstract argument `false` does not entail the composed postcondition:
`depT` forces `b = true`, and `depS true` claims a different value. -/
theorem hrrCompDep_needs_witness :
    ¬ (depS false "x" 3 "x" ⊢
        hrrCompDep depT depS (fun _ : Unit => Set.diagonal ℕ) () "x" 3 "x") := by
  intro hent
  have h0 : depS false "x" 3 "x" ((Cells.single "x" (4 : Val), 0), (0 : ECost)) :=
    ⟨⟨rfl, rfl⟩, rfl⟩
  obtain ⟨b, hb⟩ := hent _ h0
  obtain ⟨hbT, hb'⟩ := predLift_sepConj_iff.1 hb
  have hbtrue : b = true := hbT
  subst hbtrue
  rw [hr_comp_Id2 (depS true "x")] at hb'
  have h2 : Cells.single "x" (4 : Val) = Cells.single "x" (3 : Val) := hb'.1.1
  have h3 := congrFun h2 "x"
  simp [Cells.single] at h3

/-! #### The bind-shape probe

`hnr_comp_dep` at the `const` rule with the *second* step's ownership
carried in `Γ`, sequenced with `hnr_seq`, the second step opening the
`hrrCompDep` assertion with `hnRefine_hrrCompDep_pre`. -/

/-- The precondition of the composed first step (its own resources, plus
the second step's carried in the frame). -/
def depPre : Bool → String → Assn := fun _ _ => ¤¤Currency.const 1 ∗ junkCell "x"

/-- Its postcondition side. -/
def depPost : Bool → String → Assn := fun _ _ => (□ : Assn)

/-- The frame the composed step carries: the second step's resources. -/
def depFrame : Assn := ¤¤Currency.const 1 ∗ junkCell "y"

/-- Step 1: the composed *dependent* rule, with a nonempty frame — the
shape `hfcomp_dep` cannot produce, since its `Γ` is `□`. -/
theorem const_hnr_comp_dep :
    hnRefine (hrComp depPre depT () "x" ∗ depFrame) (constFun "x").2
      (hrComp depPost depT () "x" ∗ depFrame) (constFun "x").1
      (hrrCompDep depT depS (fun _ : Unit => Set.diagonal ℕ) () "x")
      (NRest.returnT 7 : NRest ℕ ECost) := by
  refine hnr_comp_dep (P := fun b : Bool => b = true) (Q := fun _ : Unit => True)
    (g := fun _ : Bool => (NRest.returnT 7 : NRest ℕ ECost))
    (h := fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)) ?_ ?_ ?_ trivial ?_
  · rintro b1 c1' rfl
    exact hnRefine_frame' (hnr_const "x" 7)
  · intro _ _ _ _
    exact NRest.nrestRel_of_le (le_of_eq (NRest.concFun_diagonal _).symm)
  · intro _ _ _ hb
    exact hb
  · intro _
    exact attains_sup_sv singleValued_diagonal

/-- Step 1 then step 2, sequenced. The second step's precondition *is* the
dependent composed assertion; `hnRefine_hrrCompDep_pre` opens it, the
`depT` witness pins `b = true`, the `U` witness pins the value, and the
ordinary `const` rule then runs framed by what was learned. This is the
compiled witness that dependent composition survives a bind. -/
theorem const_dep_bind :
    hnRefine (hrComp depPre depT () "x" ∗ depFrame)
      ((constFun "x").2.seq (Com.const "y" 5))
      (junkCell "x" ∗ hrComp depPost depT () "x") "y" natAssn
      ((NRest.returnT 7 : NRest ℕ ECost).bindT fun _ =>
        (NRest.returnT 5 : NRest ℕ ECost)) := by
  refine hnr_seq const_hnr_comp_dep fun a _ => ?_
  refine hnRefine_hrrCompDep_pre fun b rb hb hrb => ?_
  have hbt : b = true := hb
  subst hbt
  have hrba : rb = a := hrb
  subst hrba
  show hnRefine (natAssn rb "x" ∗ (hrComp depPost depT () "x" ∗ depFrame))
    (Com.const "y" 5) _ "y" natAssn (NRest.returnT 5)
  refine hnRefine_cons
    (hnRefine_frame'' (F := natAssn rb "x" ∗ hrComp depPost depT () "x") (hnr_const "y" 5))
    (fun _ hh => ?_) (fun _ hh => ?_) (fun _ _ => entails_refl _)
  · exact (show natAssn rb "x" ∗ (hrComp depPost depT () "x" ∗ depFrame)
      = (natAssn rb "x" ∗ hrComp depPost depT () "x") ∗ depFrame by ac_rfl) ▸ hh
  · rw [sepConj_emp] at hh
    exact conj_entails_mono (natAssn_entails_junkCell rb "x")
      (entails_refl (hrComp depPost depT () "x")) _ hh

/-- **Negative control 4 — the eliminator's `T`-witness is informative.**
The composed assertion pins `b = true`, so a consumer that guessed the
other branch gets nothing: the `false` reading is not entailed. -/
theorem hrrCompDep_pins_witness :
    ¬ (hrrCompDep depT depS (fun _ : Unit => Set.diagonal ℕ) () "x" 3 "x" ⊢
        depS false "x" 3 "x") := by
  intro hent
  have h0 : hrrCompDep depT depS (fun _ : Unit => Set.diagonal ℕ) () "x" 3 "x"
      ((Cells.single "x" (3 : Val), 0), (0 : ECost)) :=
    ⟨true, predLift_sepConj_iff.2 ⟨rfl, hr_compI (rfl : (3 : ℕ) = 3) _ ⟨⟨rfl, rfl⟩, rfl⟩⟩⟩
  have h1 := hent _ h0
  have h2 : Cells.single "x" (3 : Val) = Cells.single "x" (4 : Val) := h1.1.1
  have h3 := congrFun h2 "x"
  simp [Cells.single] at h3

/-- The other half of that refutation, isolating *which* conjunct fails:
drop `⌜(b, x) ∈ T⌝` from `hrrCompDep` and the same entailment becomes
provable, with `b := false`. So the witness is exactly the content of
`hnr_comp`'s second `subgoal`. -/
theorem depS_entails_witnessless :
    depS false "x" 3 "x" ⊢ sepEx (fun b : Bool => hrComp (depS b "x") (Set.diagonal ℕ) 3 "x") :=
  fun _ hp => ⟨false, hr_compI (rfl : (3 : ℕ) = 3) _ hp⟩

end Gate

end Lax13Proofs.Refine.Sepref
