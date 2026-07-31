import Lax13Proofs.Refine.NREST.Foreach
import Lax13Proofs.Refine.Sepref.Tool
import Lax13Proofs.Refine.Sepref.Definition

/-!
# Sepref lowering for currency-vector member iteration

This is tower-expansion P2.A's authored `Sepref_Foreach` adaptation
(ledger E5).  The source rule architecture is preserved: an abstract
`nfoldli` rule is discharged by a lower-level iterator implementation and
then lifted through `hnRefine_ref`.  The concrete acceptance iterator is a
masked index walk over a member array; the carrier is framed read-only and
never supplies the loop bound.
-/

namespace Lax13Proofs.Refine.Sepref

open NRest Ir

/-! ## Source-shaped bridge rule -/

/-- Sepref iteration bridge: once an iterator implementation refines an
abstract `nfoldli`, its compiled `hnRefine` theorem is a theorem for that
fold.  This is the Lean rendering of the source's iterator hnr-rule
conclusion; concrete iterator interfaces supply `LOWER`. -/
theorem hnr_nfoldli_lower {α σ κ : Type} {Γ Γ' : Assn} {c : Com} {d : κ}
    {R : σ → κ → Assn} {impl : NRest σ ECost} {xs : List α}
    {ctd : σ → Bool} {f : α → σ → NRest σ ECost} {s : σ} {overhead : ECost}
    (HNR : hnRefine Γ c Γ' d R impl)
    (LOWER : impl ≤ consume (nfoldli ctd f xs s) overhead) :
    hnRefine Γ c Γ' d R (consume (nfoldli ctd f xs s) overhead) :=
  hnRefine_ref HNR LOWER

/-! ## Masked member walk -/

abbrev MemberWalkState := ℕ × ℕ

/-- The only loop bound is the supplied member count.  Callers establish
`kend = members.length`; the carrier length is never an argument here. -/
def memberBf (kend : ℕ) (s : MemberWalkState) : Bool :=
  decide (s.1 < kend)

/-- One compiled member visit: two reads, two additions, and the tuple
assembly. -/
def memberStepCost : ECost :=
  irUnit Currency.aget + irUnit Currency.aget + irUnit Currency.add +
    irUnit Currency.add + irUnit Currency.skip

/-- Local normalization for a deterministic charged operation. -/
theorem bindT_member_unit {α β : Type} (x : α) (κ : ECost)
    (f : α → NRest β ECost) :
    bindT (consume (returnT x) κ) f = consume (f x) κ := by
  rw [NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.returnT_bindT]

/-- Pure state transformer mirrored by `memberF`. -/
def memberStep (members carrier : List ℕ) (s : MemberWalkState) : MemberWalkState :=
  (1 + s.1, carrier[members[s.1]!]! + s.2)

/-- Read member `k`, read that carrier cell, accumulate it, and advance.
The carrier is queried only at the selected member. -/
noncomputable def memberF (members carrier : List ℕ) (s : MemberWalkState) :
    NRest MemberWalkState ECost :=
  bindT (mopAget members s.1) fun u =>
    bindT (mopAget carrier u) fun w =>
      bindT (mopBinop .add s.2 w) fun acc =>
        bindT (mopBinop .add s.1 1) fun k => mopPair k acc

/-- Exact cost of one safe masked member visit. -/
theorem memberF_eq (members carrier : List ℕ) (s : MemberWalkState)
    (hk : s.1 < members.length) (hu : members[s.1]! < carrier.length) :
    memberF members carrier s =
      consume (returnT (memberStep members carrier s)) memberStepCost := by
  simp only [memberF, mopAget_def, mopBinop_def, mopPair_def,
    assert_pos hk, assert_pos hu, returnT_bindT, bindT_member_unit, consume_consume,
    memberStep, memberStepCost, Imp.Bop.apply_add, binopCurrency_add]
  congr 1
  all_goals abel

/-- The concrete masked walk used by P2's acceptance gate. -/
noncomputable def memberWalk (members carrier : List ℕ) (kend : ℕ) (s₀ : MemberWalkState) :
    NRest MemberWalkState ECost :=
  irWhileIT (fun _ => True) (memberBf kend) (memberF members carrier) s₀

/-! ## Synthesis -/

/--
info: sepref_synth Lax13Proofs.Refine.Sepref.memberWalkSynth:
  Com.while (Cond.lt (Operand.cell "k") (Operand.cell "kend"))
    ((Com.aget "u" "members" "k").seq
      ((Com.aget "w" "carrier" "u").seq
        ((Com.binop Imp.Bop.add "acc" "acc" "w").seq ((Com.binop Imp.Bop.add "k" "k" "one").seq Com.skip))))
-/
#guard_msgs in
sepref_synth memberWalkSynth (members carrier : List ℕ) (kend : ℕ) (s₀ : MemberWalkState) :
  hnRefine
    (hnCtxt (natAssn ×ₐ natAssn) s₀ ("k", "acc") ∗
      hnCtxt arrayAssn members "members" ∗ hnCtxt arrayAssn carrier "carrier" ∗
      hnCtxt natAssn kend "kend" ∗
      hnCtxt natAssn 1 "one" ∗ junkCell "u" ∗ junkCell "w")
    _ _ ("k", "acc") (natAssn ×ₐ natAssn) (memberWalk members carrier kend s₀)

/-! ## Compiled carrier-blindness gate -/

namespace MemberWalkGate

def members : List ℕ := [7, 91]

def carrier : List ℕ := (List.replicate 100 0).set 7 3 |>.set 91 5

def totalCost : ECost := 2 • memberStepCost + 3 • irUnit Currency.«while»

/-- The abstract member-list fold: there is one `memberStepCost` vector per
member, and no reference to the carrier length. -/
noncomputable def abstractWalk : NRest MemberWalkState ECost :=
  nfoldli (fun _ => true)
    (fun u s => consume (returnT (s.1 + 1, s.2 + carrier[u]!)) memberStepCost)
    members (0, 0)

theorem abstractWalk_exact :
    abstractWalk = consume (returnT (2, 8)) (2 • memberStepCost) := by
  simpa [abstractWalk, members, carrier, NRest.foldState] using
    NRest.nfoldli_consume_exact members
      (fun (u : ℕ) (s : MemberWalkState) => (s.1 + 1, s.2 + carrier[u]!))
      memberStepCost (0, 0)

/-- The synthesized index loop is exactly the abstract `nfoldli` plus its
three guard evaluations.  This is P2.A's concrete lowering witness. -/
theorem memberWalk_exact :
    memberWalk members carrier 2 (0, 0) =
      consume abstractWalk (3 • irUnit Currency.«while») := by
  have hk0 : (0 : ℕ) < members.length := by decide
  have hu0 : members[0]! < carrier.length := by decide
  have hk1 : (memberStep members carrier (0, 0)).1 < members.length := by decide
  have hu1 : members[(memberStep members carrier (0, 0)).1]! < carrier.length := by
    decide
  rw [memberWalk, irWhileIT_of_true trivial (by decide),
    memberF_eq members carrier (0, 0) hk0 hu0, bindT_member_unit]
  rw [irWhileIT_of_true trivial (by decide),
    memberF_eq members carrier (memberStep members carrier (0, 0)) hk1 hu1,
    bindT_member_unit]
  rw [irWhileIT_of_false trivial (by decide), abstractWalk_exact]
  simp only [memberStep, members, carrier, consume_consume]
  congr 1
  all_goals first | rfl | (simp only [succ_nsmul]; abel)

/-- The generated program's judgment, lifted through the source-shaped hnr
bridge to the abstract member-list fold. -/
theorem compiled_abstract_walk :
    hnRefine
      (hnCtxt (natAssn ×ₐ natAssn) ((0, 0) : MemberWalkState) ("k", "acc") ∗
        hnCtxt arrayAssn members "members" ∗ hnCtxt arrayAssn carrier "carrier" ∗
        hnCtxt natAssn 2 "kend" ∗ hnCtxt natAssn 1 "one" ∗
        junkCell "u" ∗ junkCell "w")
      memberWalkSynth_impl
      (hnCtxt arrayAssn members "members" ∗ hnCtxt arrayAssn carrier "carrier" ∗
        hnCtxt natAssn 2 "kend" ∗ hnCtxt natAssn 1 "one" ∗
        junkCell "u" ∗ junkCell "w")
      ("k", "acc") (natAssn ×ₐ natAssn)
      (consume abstractWalk (3 • irUnit Currency.«while»)) := by
  exact hnr_nfoldli_lower (memberWalkSynth members carrier 2 (0, 0))
    (le_of_eq memberWalk_exact)

-- The loop bound and generated condition mention `members`, never `carrier`.
#guard members.length = 2
#guard carrier.length = 100
#guard memberWalkSynth_impl =
  Com.while (Cond.lt (Operand.cell "k") (Operand.cell "kend"))
    ((Com.aget "u" "members" "k").seq
      ((Com.aget "w" "carrier" "u").seq
        ((Com.binop Imp.Bop.add "acc" "acc" "w").seq
          ((Com.binop Imp.Bop.add "k" "k" "one").seq Com.skip))))
#guard totalCost.toFun Currency.aget = 4
#guard totalCost.toFun Currency.add = 4
#guard totalCost.toFun Currency.skip = 2
#guard totalCost.toFun Currency.«while» = 3

/-- info: 'Lax13Proofs.Refine.Sepref.memberWalkSynth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms memberWalkSynth

/--
info: 'Lax13Proofs.Refine.Sepref.MemberWalkGate.compiled_abstract_walk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms compiled_abstract_walk


end MemberWalkGate

end Lax13Proofs.Refine.Sepref
