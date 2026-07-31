import Lax13Proofs.Refine.Sepref.SignatureNorm

/-!
# Goal-directed signature composition

This module supplies the smallest honest Lean counterpart of the source's
`FCOMP` theorem attribute.  The source attribute accepts either an `hfref`
rule or a generalized `hn_refine` rule as its left input, composes it with a
pure `fref` rule, and then runs normalization and side-condition solvers.

Lean's current `hfref` has a concrete side of type `κa → κb × Com`; its
generalized hnr form is therefore exactly the family accepted by `to_hfref`.
`sepref_fcomp A B` below tries both representations and both result shapes:
non-dependent assertions use `FCOMP`, while dependent assertions use
`FCOMP_dep`.  It intentionally leaves the `attainsSup` premise as the next
goal.  This makes the cost-refinement obligation visible rather than hiding a
possibly inapplicable single-valuedness argument in metaprogramming.

This is bounded frontend plumbing, not an arbitrary global theorem normalizer:
both source composition branches are present, while strict normalization is
limited to the source-supported assertion/product/pure/identity laws.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest
open Lean Elab Meta Tactic

/-! ## Bounded relation normal forms used by checked FCOMP -/

/-- Source `Id O R = R`, in the repository's concrete-first spelling. -/
@[simp] theorem relComp_diagonal_left {α β : Type} (R : Set (β × α)) :
    relComp (Set.diagonal β) R = R := by
  ext p
  constructor
  · rintro ⟨b, hpb, hb⟩
    have hpb' : p.1 = b := hpb
    rw [← hpb'] at hb
    exact hb
  · intro hp
    exact ⟨p.1, rfl, hp⟩

/-- Source `R O Id = R`. -/
@[simp] theorem relComp_diagonal_right {α β : Type} (R : Set (β × α)) :
    relComp R (Set.diagonal α) = R := by
  ext p
  constructor
  · rintro ⟨a, ha, hEq⟩
    have hEq' : a = p.2 := hEq
    rw [hEq'] at ha
    exact ha
  · intro hp
    exact ⟨p.2, hp, rfl⟩

/-- The source's non-dependent `rr_comp` branch at an identity argument
relation.  Unlike an unconditional dependent-to-nondependent rewrite, this
retains the required identity witness and is sound for every fiber. -/
@[simp] theorem rrComp_diagonal_const {α β β' γ : Type}
    (R : Set (β × β')) (S : Set (β' × γ)) (x : α) :
    rrComp (Set.diagonal α) (fun _ => R) (fun _ => S) x = relComp R S := by
  ext p
  constructor
  · rintro ⟨y, hEq, b, hbR, hbS⟩
    have hEq' : y = x := hEq
    subst y
    exact ⟨b, hbR, hbS⟩
  · rintro ⟨b, hbR, hbS⟩
    exact ⟨x, rfl, b, hbR, hbS⟩

/-! ## Frontend -/

/-- Compose a heap-refinement rule with a pure/NREST refinement rule.

The left term may prove either an `hfref` signature or its fully generalized
`hnRefine` family.  The target determines whether the non-dependent or
dependent composition theorem is selected.  On success the tactic leaves the
source's `attainsSup` side condition as an ordinary goal.
-/
macro "sepref_fcomp " hA:term ", " hB:term : tactic =>
  `(tactic|
    first
    | refine FCOMP $hA $hB ?_
    | refine FCOMP (to_hfref $hA) $hB ?_
    | refine FCOMP_dep $hA $hB ?_
    | refine FCOMP_dep (to_hfref $hA) $hB ?_
    | exact fref_compI_PRE $hA $hB
    | fail "sepref_fcomp: expected an hfref rule or a fully generalized hnRefine family, followed by a compatible pure fref rule")

/-- Identity-normalized heap composition.  Packaging normalization as a
theorem is what lets checked mode expose `SC` as an ordinary goal: a `simpa`
term containing `?_` would instead ask the simplifier to synthesize it. -/
theorem FCOMP_diagonal {α β κa κb : Type}
    {P Q : α → Prop}
    {RR' : (α → κa → Assn) × (α → κa → Assn)}
    {A : β → κb → Assn}
    {f : κa → κb × Com} {g h : α → NRest β ECost}
    (hA : (f, g) ∈ hfref P RR' (fun _ _ => A))
    (hB : (g, h) ∈ fref Q (Set.diagonal α)
      (fun _ => NRest.nrestRel (Set.diagonal β)))
    (SC : ∀ b1 a1, attainsSup (g b1) (h a1) (Set.diagonal β)) :
    (f, h) ∈ hfref
      (compPRE (Set.diagonal α) Q (fun _ y => P y)
        (fun x => (h x).nofailT)) RR' (fun _ _ => A) := by
  simpa only [hrpComp_diagonal, hrrCompND_diagonal] using FCOMP hA hB SC

/-! ### Strict post-checking

The source attribute has a checked mode which rejects composition constructors
left after its supported normalizer.  Generic dependent composition needs
those constructors as an honest public result, so `sepref_fcomp` above stays
general.  Strict callers use the checker and normalized frontend below. -/

/-- Find the first source composition constructor in an expression. -/
private partial def firstFCompArtifact? : Expr → Option Name
  | .const n _ =>
      if n == ``hrComp || n == ``hrpComp || n == ``hrrCompND ||
          n == ``hrrCompDep || n == ``relComp || n == ``rrComp then
        some n
      else none
  | .app f a => firstFCompArtifact? f <|> firstFCompArtifact? a
  | .lam _ t b _ => firstFCompArtifact? t <|> firstFCompArtifact? b
  | .forallE _ t b _ => firstFCompArtifact? t <|> firstFCompArtifact? b
  | .letE _ t v b _ =>
      firstFCompArtifact? t <|> firstFCompArtifact? v <|> firstFCompArtifact? b
  | .mdata _ b => firstFCompArtifact? b
  | .proj _ _ b => firstFCompArtifact? b
  | _ => none

/-- Deterministic counterpart of the source's `check_fcomp_result`: inspect
the original target, before composition replaces it by an `attainsSup` side
goal, and reject any artifact the strict normalizer should have removed. -/
elab "sepref_fcomp_check_target" : tactic => do
  let g ← Tactic.getMainGoal
  let target ← instantiateMVars (← g.getType)
  match firstFCompArtifact? target with
  | some n =>
      throwError "sepref_fcomp_checked: unsupported composition artifact remains after normalization: {n}"
  | none => pure ()

/-- Normalize the actual target with exactly the source-supported laws in
`SignatureNorm` plus the bounded identity laws above.  This proof-preserving
target change is also the normalized copy inspected by the post-check. -/
macro "sepref_fcomp_normalize_target" : tactic =>
  `(tactic| try simp only [hrpComp_diagonal, hrrCompND_diagonal,
    hrpComp, hrrCompND, hr_comp_Id1, hr_comp_Id2, hr_comp_pure,
    hr_comp_prod_conv, hr_comp_assoc, relComp_diagonal_left,
    relComp_diagonal_right, rrComp_diagonal_const, NRest.nrestRel_comp])

/-- Checked identity/simp-normalizing mode.  The post-check runs after the
goal has been changed to its supported normal form and before a successful
branch leaves its visible side condition. -/
macro "sepref_fcomp_checked " hA:term ", " hB:term : tactic =>
  `(tactic|
    (sepref_fcomp_normalize_target;
     sepref_fcomp_check_target;
     first
     | refine FCOMP_diagonal $hA $hB ?_
     | refine FCOMP_diagonal (to_hfref $hA) $hB ?_
     | convert FCOMP $hA $hB ?_ using 1 <;>
         simp [compPRE, hrpComp, hrrCompND, hr_comp_assoc]
     | convert FCOMP (to_hfref $hA) $hB ?_ using 1 <;>
         simp [compPRE, hrpComp, hrrCompND, hr_comp_assoc]
     | convert FCOMP_dep $hA $hB ?_ using 1 <;>
         simp [compPRE, hrpComp, hrrCompND, hr_comp_assoc]
     | convert FCOMP_dep (to_hfref $hA) $hB ?_ using 1 <;>
         simp [compPRE, hrpComp, hrrCompND, hr_comp_assoc]
     | simpa [compPRE] using fref_compI_PRE $hA $hB
     | fail "sepref_fcomp_checked: inputs are incompatible or supported normalization did not remove every composition artifact"))

/-! ## Compiled frontend gates -/

namespace SignatureToolGate

open SignatureGate

/-- Direct `hfref` dispatch.  The final line is deliberately separate: it is
the visible residual produced by the frontend. -/
theorem direct_hfref_frontend :
    (signatureConstFun, fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)) ∈
      hfref
        (compPRE (Set.diagonal Unit) (fun _ => True) (fun _ _ => True)
          (fun x => ((fun _ : Unit =>
            (NRest.returnT 7 : NRest ℕ ECost)) x).nofailT))
        (hrpComp signatureRS (Set.diagonal Unit))
        (hrrCompND natAssn (fun _ : Unit => Set.diagonal ℕ)) := by
  sepref_fcomp signature_hfref, signature_fref
  exact fun _ _ => attains_sup_sv singleValued_diagonal

/-- Strict identity normalization removes `hrpComp`, `hrrCompND`, and the
guarded composed precondition before the source-style post-check. -/
theorem checked_identity_frontend :
    (signatureConstFun, fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)) ∈
      hfref
        (compPRE (Set.diagonal Unit) (fun _ => True) (fun _ _ => True)
          (fun x => ((fun _ : Unit =>
            (NRest.returnT 7 : NRest ℕ ECost)) x).nofailT))
        signatureRS (fun _ _ => natAssn) := by
  sepref_fcomp_checked signature_hfref, signature_fref
  exact fun _ _ => attains_sup_sv singleValued_diagonal

/-- The raw hnr family shape accepted by the converter branch. -/
theorem signature_hnr_family :
    ∀ (c : String) (a : Unit), True →
      hnRefine (signatureRS.1 a c) (signatureConstFun c).2
        (signatureRS.2 a c) (signatureConstFun c).1 natAssn
        (NRest.returnT 7 : NRest ℕ ECost) := by
  intro c a _
  cases a
  exact signature_hnr c

/-- The frontend itself, rather than an explicit call to `to_hfref`, converts
the generalized hnr family before composition. -/
theorem converted_hnr_frontend :
    (signatureConstFun, fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)) ∈
      hfref
        (compPRE (Set.diagonal Unit) (fun _ => True) (fun _ _ => True)
          (fun x => ((fun _ : Unit =>
            (NRest.returnT 7 : NRest ℕ ECost)) x).nofailT))
        (hrpComp signatureRS (Set.diagonal Unit))
        (hrrCompND natAssn (fun _ : Unit => Set.diagonal ℕ)) := by
  sepref_fcomp signature_hnr_family, signature_fref
  exact fun _ _ => attains_sup_sv singleValued_diagonal

/-- A genuinely dependent target selects `FCOMP_dep`, retaining the argument
witness in the result assertion. -/
theorem dependent_frontend :
    (Gate.constFun, fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)) ∈
      hfref
        (compPRE Gate.depT (fun _ : Unit => True)
          (fun _ b => b = true)
          (fun x => ((fun _ : Unit =>
            (NRest.returnT 7 : NRest ℕ ECost)) x).nofailT))
        (hrpComp
          ((fun _ (_ : String) => ¤¤Currency.const 1 ∗ junkCell "x"),
            (fun _ (_ : String) => (□ : Assn))) Gate.depT)
        (hrrCompDep Gate.depT Gate.depS
          (fun _ : Unit => Set.diagonal ℕ)) := by
  sepref_fcomp Gate.const_hfref_dep, Gate.const_fref_dep
  exact fun _ _ => attains_sup_sv singleValued_diagonal

/-- The source's second dispatch branch: pure `fref` followed by pure `fref`.
There is no `attainsSup` residual on this branch. -/
theorem pure_fref_frontend :
    ((fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)),
      (fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost))) ∈
      fref
        (compPRE (Set.diagonal Unit) (fun _ => True)
          (fun _ _ => True) (fun _ => True))
        (relComp (Set.diagonal Unit) (Set.diagonal Unit))
        (rrComp (Set.diagonal Unit)
          (fun _ => NRest.nrestRel (Set.diagonal ℕ))
          (fun _ => NRest.nrestRel (Set.diagonal ℕ))) := by
  sepref_fcomp signature_fref, signature_fref

set_option linter.unnecessarySimpa false in
/-- Checked pure composition reaches the source identity normal form for both
the argument relation and the NREST result relation. -/
theorem checked_pure_fref_frontend :
    ((fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)),
      (fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost))) ∈
      fref (fun _ : Unit => True) (Set.diagonal Unit)
        (fun _ => NRest.nrestRel (Set.diagonal ℕ)) := by
  sepref_fcomp_checked signature_fref, signature_fref

/-- Strict mode deterministically rejects a generic dependent residue which
the supported source normal forms cannot eliminate.  General mode remains the
correct interface for this result and proves the goal immediately afterward. -/
example :
    (Gate.constFun, fun _ : Unit => (NRest.returnT 7 : NRest ℕ ECost)) ∈
      hfref
        (compPRE Gate.depT (fun _ : Unit => True)
          (fun _ b => b = true)
          (fun x => ((fun _ : Unit =>
            (NRest.returnT 7 : NRest ℕ ECost)) x).nofailT))
        (hrpComp
          ((fun _ (_ : String) => ¤¤Currency.const 1 ∗ junkCell "x"),
            (fun _ (_ : String) => (□ : Assn))) Gate.depT)
        (hrrCompDep Gate.depT Gate.depS
          (fun _ : Unit => Set.diagonal ℕ)) := by
  fail_if_success
    sepref_fcomp_checked Gate.const_hfref_dep, Gate.const_fref_dep
  exact dependent_frontend

/-- The strict post-check itself rejects a raw assertion-composition target,
even though the underlying identity law can prove it. -/
example :
    (hrrCompND natAssn (fun _ : Unit => Set.diagonal ℕ) :
      Unit → String → ℕ → String → Assn) = fun _ _ => natAssn := by
  fail_if_success
    sepref_fcomp_check_target
  exact hrrCompND_diagonal natAssn

/-- Artifact rejection: a heap theorem cannot be mistaken for the pure
second rule.  `fail_if_success` makes rejection itself part of compilation. -/
example : True := by
  fail_if_success
    sepref_fcomp signature_fref, signature_hfref
  trivial

/-- A fixed hnr instance is not a generalized family and must not be silently
packaged as an `hfref` theorem. -/
example : True := by
  fail_if_success
    sepref_fcomp (signature_hnr "x"), signature_fref
  trivial

end SignatureToolGate

end Lax13Proofs.Refine.Sepref
