import Lax3Proofs.Refine.ElimSynth6
import Lax13Proofs.Refine.Sepref.Register
import Lax13Proofs.Refine.Iicf.Basic

/-!
# ND-MC rebase E-elim.1 — the elimination engine as one `Com`, and the
spec-shaped leaf

Kills tower-ledger E43's obstructions (2) and (3):

* **(2)** the elimination engine's five passes (degree, buckets,
  elimination, offsets, fill) had no single synthesized `Com`. §1–§4
  close 2B/D-a (the degree pass's outer loop, recorded in
  `ElimSynth.lean` §4.1 as one invocation away after tool wave T1) and
  hand-compose the five landed syntheses into **one** `hnRefine` against
  `ElimSynth6.elimProgram`'s own `NRest` text, by `hnr_seq` — never a
  whole-engine re-synthesis, which is wave S's determinism cliff
  (`OrderSigProbe` §4/§7).
* **(3)** `OrderSynth.hnr_mop_elim` pins its eleven-component entry
  state, so a phase calling the engine twice cannot match on the second
  call. §6 registers `hnr_mop_elim_spec`, whose abstract program is
  `NRest.spec (OrderSynth.ElimPost n W) …` — **no entry-state tuple**:
  the six pure-scratch arrays enter as owned-length-only conjuncts
  (`scr`, §0) and the five output arrays enter at whatever values the
  caller holds, their lengths exactly `ElimPost`'s five length clauses,
  which is what makes the second call's entry dischargeable from the
  first call's postcondition. The engine builds its own zero state
  (three fills and the counter constants are *inside* the `Com`), which
  is `ElimSynth.lean` §"How the re-zeroing defect class dies"
  made machine-real: `elimRezeroCom` has no counterpart because the
  engine itself produces the `List.replicate _ 0` its loops enter at.
  §7 is the twice-call test and the pinned-leaf refusal control.

Carried debts, untouched: E1 (amortized transport,
`ElimSynth3.lean:429–447`), E2 (correctness transport), E3 (BRefine
nested-while). Costs stay carrier-class this wave; the member-driven
interior is the next wave.
-/

namespace Lax3Proofs.Refine.ElimSynth7

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref
open Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax13Proofs.Refine.BfsQ (cu iter)
open Lax3Proofs.Refine.ElimSynth hiding mopSucc mopSucc_eq mopKeep mopKeep_eq

/-! ## 1. 2B/D-a closed — the degree pass's outer loop, synthesized

`ElimSynth` §4.1 measured the two-loop degree pass as not translating at
4 000 000 heartbeats and recorded it "one `sepref_synth` invocation away
when the translate driver is repaired". Tool wave T1 repaired it (the
identical shape — outer loop, inner loop mid-body, a two-armed `aset`
branch on a state array — is `fillSynth`, which now translates). This is
that one invocation. The index cell is `"di"`, not `"i"`, because the
bucket pass's landed synthesis owns `"i"` and the engine composition
needs both alive at once. -/

set_option maxHeartbeats 4000000 in
sepref_synth degPassSynth (n : ℕ) (off tgt alv : List ℕ) (deg₀ : List ℕ) (i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (deg₀, i₀) ("deg", "di") ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
      hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "dj" ∗ junkCell "dip" ∗ junkCell "djend" ∗ junkCell "dc" ∗
      junkCell "du" ∗ junkCell "dau" ∗ junkCell "dai")
    _ _ ("deg", "di") (arrayAssn ×ₐ natAssn)
    (ElimSynth.degPass n off tgt alv (deg₀, i₀))

-- The synthesized degree pass, pinned: `RamElim.degRow` with the landed
-- inner scan (`degScanSynth_impl`'s text at the `d`-prefixed cells)
-- sitting mid-body, and the dead-vertex `else` writing the zero cell.
#guard degPassSynth_impl =
  Com.while (Cond.lt (Operand.cell "di") (Operand.cell "n"))
    ((Com.aget "dj" "off" "di").seq
      ((Com.binop Lax13Proofs.Imp.Bop.add "dip" "di" "one").seq
        ((Com.aget "djend" "off" "dip").seq
          ((Com.const "dc" 0).seq
            (Com.skip.seq
              ((Com.while (Cond.lt (Operand.cell "dj") (Operand.cell "djend"))
                    ((Com.aget "du" "tgt" "dj").seq
                      ((Com.aget "dau" "alv" "du").seq
                        ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "dau"))
                              (Com.binop Lax13Proofs.Imp.Bop.add "dc" "dc" "one")
                              (Com.binop Lax13Proofs.Imp.Bop.add "dc" "dc" "zero")).seq
                          ((Com.binop Lax13Proofs.Imp.Bop.add "dj" "dj" "one").seq Com.skip))))).seq
                ((Com.aget "du" "alv" "di").seq
                  ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "du")) (Com.aset "deg" "di" "dc")
                        (Com.aset "deg" "di" "zero")).seq
                    ((Com.binop Lax13Proofs.Imp.Bop.add "di" "di" "one").seq Com.skip)))))))))

-- **Negative control on the pin**: the dead-vertex arm really writes,
-- so a program with a `skip` there is a different program.
#guard degPassSynth_impl ≠
  Com.while (Cond.lt (Operand.cell "di") (Operand.cell "n"))
    ((Com.aget "dj" "off" "di").seq
      ((Com.binop Lax13Proofs.Imp.Bop.add "dip" "di" "one").seq
        ((Com.aget "djend" "off" "dip").seq
          ((Com.const "dc" 0).seq
            (Com.skip.seq
              ((Com.while (Cond.lt (Operand.cell "dj") (Operand.cell "djend"))
                    ((Com.aget "du" "tgt" "dj").seq
                      ((Com.aget "dau" "alv" "du").seq
                        ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "dau"))
                              (Com.binop Lax13Proofs.Imp.Bop.add "dc" "dc" "one")
                              (Com.binop Lax13Proofs.Imp.Bop.add "dc" "dc" "zero")).seq
                          ((Com.binop Lax13Proofs.Imp.Bop.add "dj" "dj" "one").seq Com.skip))))).seq
                ((Com.aget "du" "alv" "di").seq
                  ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "du")) (Com.aset "deg" "di" "dc")
                        Com.skip).seq
                    ((Com.binop Lax13Proofs.Imp.Bop.add "di" "di" "one").seq Com.skip)))))))))

/-! ## 2. The offset and fill passes at engine-composable cells

`offSynth`/`fillSynth` are landed at index cells the composition cannot
reuse: `offSynth`'s state is `("ioff","ifl","s","i")` and `fillSynth`'s
`("itg","ifl","i")`, but `"i"` exits the bucket pass holding `n` while
each later pass's `NRest` text enters its loop at the literal `0`, and
no abstract operation exists at that seam to pay for a reset. The same
two programs are therefore synthesized once more at fresh index cells
(`"os"`, `"oi"`, `"fi"`), the S-wave re-synthesis idiom
(`OrderSigProbe` §2) without the anchors — the landed theorems stay the
named statements at the landed cells, and these are the same programs
cell-renamed. -/

set_option maxHeartbeats 1000000 in
sepref_synth offSynth7 (n : ℕ) (idg ioff₀ ifl₀ : List ℕ) (s₀ i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (ioff₀, ifl₀, s₀, i₀) ("ioff", "ifl", "os", "oi") ∗
      hnCtxt arrayAssn idg "idg" ∗ hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "odi" ∗ junkCell "oip")
    _ _ ("ioff", "ifl", "os", "oi")
    (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (ElimSynth2.offPass n idg (ioff₀, ifl₀, s₀, i₀))

set_option maxHeartbeats 4000000 in
sepref_synth fillSynth7 (n : ℕ) (off tgt alv rnk : List ℕ) (itg₀ ifl₀ : List ℕ) (i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ natAssn) (itg₀, ifl₀, i₀)
      ("itg", "ifl", "fi") ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
      hnCtxt arrayAssn alv "alv" ∗ hnCtxt arrayAssn rnk "rnk" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "fai" ∗ junkCell "fri" ∗ junkCell "fj" ∗ junkCell "fip" ∗ junkCell "fjend" ∗
      junkCell "fu" ∗ junkCell "fau" ∗ junkCell "fru" ∗ junkCell "fp")
    _ _ ("itg", "ifl", "fi") (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
    (ElimSynth2.fillPass n off tgt alv rnk (itg₀, ifl₀, i₀))

/-! ## 3. The scratch-building leaves — a fill and a copy at symbolic
cells

The spec-shaped engine (§5) builds its own zero state: `elm`, `bh` and
`ioff` are zero-filled *inside* the `Com`, and the engine's second
output copy (`ioff` doubled into `iof2`, because `elimOutOf` names the
offsets twice and one machine cell cannot be owned twice) runs at the
end. Both are `OrderSynth`'s pass programs; the rules are re-synthesized
here at symbolic cell names (the S idiom) so one synthesis serves every
instantiation. `zcopy` is registered — the twice-call test's tail pass
consumes an engine output through it. -/

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
sepref_synth zfill (a i v cnt one : String) (N w : ℕ) (A₀ : List ℕ) (i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) (a, i) ∗
      hnCtxt natAssn w v ∗ hnCtxt natAssn N cnt ∗ hnCtxt natAssn 1 one)
    _ _ (a, i) (arrayAssn ×ₐ natAssn)
    (OrderSynth.fillPass N w (A₀, i₀))

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
sepref_synth zcopy (d i s cnt one u : String) (N : ℕ) (src A₀ : List ℕ) (i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (A₀, i₀) (d, i) ∗
      hnCtxt arrayAssn src s ∗ hnCtxt natAssn N cnt ∗ hnCtxt natAssn 1 one ∗
      junkCell u)
    _ _ (d, i) (arrayAssn ×ₐ natAssn)
    (OrderSynth.copyPass N src (A₀, i₀))

attribute [sepref_fr_rules] zcopy

/-! ## 4. Composition kit

Three small pieces the hand composition needs and the house does not
have yet: a guard-carrying *map* rule (a trailing `returnT (g a)` is a
pure repackaging and costs no instruction — `hnr_return_pass` would
charge a `skip` the abstract text never pays), the characterization of a
result bound against a `spec` program (what makes the second engine
call's entry lengths dischargeable from the first call's postcondition),
and `ElimPost` restated as an `Iff.rfl` so `simp_all` can open it. -/

section Kit

variable {α β : Type} {κ κ' : Type}

/-- `hnr_seq` at a pure repackaging tail: `bindT m (fun a => returnT (g a))`
is realized by `c` alone — the repackaging is a re-reading of the cells
the run already left, chosen by the entailment. The guard is `hnr_seq`'s,
so the entailment may consult what `m`'s results satisfy. -/
theorem hnr_map {Γ Γ₁ Γ' : Assn} {c : Com} {x : κ'} {d : κ}
    {Rh : α → κ' → Assn} {R : β → κ → Assn} {m : NRest α ECost} {g : α → β}
    (D1 : hnRefine Γ c Γ₁ x Rh m)
    (himp : ∀ a : α, (NRest.returnT a : NRest α ECost) ≤ m →
      (hnCtxt Rh a x ∗ Γ₁) ⊢ (Γ' ∗ hnCtxt R (g a) d)) :
    hnRefine Γ c Γ' d R (m.bindT fun a => NRest.returnT (g a)) := by
  intro _ M F s cr hm hs
  cases hmm : m with
  | fail =>
    rw [hmm, NRest.bindT_fail] at hm
    exact absurd hm (NRest.fail_ne_rest M)
  | rest Mm =>
    obtain ⟨ra, Ca, hCa, w1⟩ := hnRefineD D1 hmm hs
    have hne : Mm ra ≠ ⊥ := by
      intro hbot
      rw [hbot, le_bot_iff] at hCa
      exact WithBot.coe_ne_bot hCa
    obtain ⟨Car, hCar⟩ := WithBot.ne_bot_iff_exists.1 hne
    have hCaCar : Ca ≤ Car := by
      rw [← hCar, WithBot.coe_le_coe] at hCa
      exact hCa
    have hret : (NRest.returnT ra : NRest α ECost) ≤ m := by
      rw [hmm]; exact returnT_le_rest_of_coe_le hCa
    have hmemle : (NRest.returnT (g ra) : NRest β ECost).consume Car ≤ NRest.rest M := by
      rw [← hm, hmm, NRest.bindT_rest]
      exact le_sSup ⟨ra, Car, hCar.symm, rfl⟩
    have hMg : ((Ca : ECost) : WithBot ECost) ≤ M (g ra) := by
      rw [NRest.consume_returnT, NRest.rest_le_rest_iff] at hmemle
      have h := hmemle (g ra)
      rw [NRest.single_self] at h
      exact le_trans (WithBot.coe_le_coe.2 hCaCar) h
    refine ⟨g ra, Ca, hMg, wp_mono_ir (fun _ p hp => ?_) w1⟩
    have hent := himp ra hret
    have hperm : (Γ₁ ∗ Rh ra x ∗ F ∗ GC) = ((hnCtxt Rh ra x ∗ Γ₁) ∗ (F ∗ GC)) := by
      simp only [hnCtxt_def]
      ac_rfl
    have hp' : irSTATE ((hnCtxt Rh ra x ∗ Γ₁) ∗ (F ∗ GC)) p := by
      rw [← hperm]; exact hp
    have hp'' : irSTATE ((Γ' ∗ hnCtxt R (g ra) d) ∗ (F ∗ GC)) p :=
      start_entailsE hp' (sepConj_mono_left hent)
    show irSTATE (Γ' ∗ R (g ra) d ∗ F ∗ GC) p
    have he : (Γ' ∗ R (g ra) d ∗ F ∗ GC) = ((Γ' ∗ hnCtxt R (g ra) d) ∗ (F ∗ GC)) := by
      simp only [hnCtxt_def]
      ac_rfl
    rw [he]
    exact hp''

/-- A result bound against a `spec` satisfies the spec's postcondition.
`@[simp]`, in the form the tool's `simp_all` fallback meets it (the
`bind_ref_tag` wrapper is itself a simp-unfold), so a rule premise about
the *second* engine call's entry is dischargeable from the first call's
`bind_ref_tag` hypothesis. -/
@[simp] theorem returnT_le_spec_iff {a : α} {P : α → Prop} {t : α → ECost} :
    (NRest.returnT a : NRest α ECost) ≤ NRest.spec P t ↔ P a := by
  rw [NRest.spec, returnT_le_rest_iff]
  constructor
  · intro h
    by_contra hP
    rw [if_neg hP, le_bot_iff] at h
    exact WithBot.coe_ne_bot (by rw [← WithBot.coe_zero] at h; exact h)
  · intro hP
    rw [if_pos hP, ← WithBot.coe_zero, WithBot.coe_le_coe]
    exact ACost.le_def.2 fun _ => by simp

/-- …and at the tagged spelling. -/
@[simp] theorem bind_ref_tag_spec_iff {a : α} {P : α → Prop} {t : α → ECost} :
    bind_ref_tag a (NRest.spec P t) ↔ P a := returnT_le_spec_iff

/-- `ElimPost`, opened — the shape `simp_all` consumes. -/
@[simp] theorem elimPost_iff {n W : ℕ} {e : OrderSynth.ElimOut} :
    OrderSynth.ElimPost n W e ↔
      (e.1.length = n ∧ e.2.1.length = n ∧ e.2.2.1.length = n + 1 ∧
        e.2.2.2.1.length = n + 1 ∧ e.2.2.2.2.length = W ∧
        (∀ v < n, e.1[v]! < n) ∧ (∀ v < n, ∀ w < n, e.1[v]! = e.1[w]! → v = w)) :=
  Iff.rfl

end Kit

/-! ## 5. The engine as ONE `Com` — E43 obstruction (2) closed

The five landed pass syntheses, composed by `hnr_seq` against
`ElimSynth6.elimProgram`'s own `NRest` text. The route is the E39/E40
house pattern — composition by name, never a whole-engine re-synthesis:
every pass boundary here has a produced-value destination, which is
exactly wave S's determinism cliff, and `hnr_seq` threads those values
by hand instead of asking the matcher to choose them. -/

section Engine

open Lax13Proofs.Reasoning (arrOf)
open Lax13Proofs.Refine.Sepref.Iicf (junkArrayOfLen arrayAssn_entails_junkArrayOfLen'
  entails_of_eq)

/-- What the composed engine hands back of `elimOutOf`'s five components:
the four *distinct* ones, each in the cell the run left it in. (The
third and fourth components of `elimOutOf` are the same offsets list;
one machine cell cannot be owned twice, so the doubled component is the
spec leaf's job — §6 copies it into its own array.) -/
def elimOutAssn : OrderSynth.ElimOut → String × String × String × String → Assn :=
  fun eo k => hnCtxt arrayAssn eo.1 k.1 ∗ hnCtxt arrayAssn eo.2.1 k.2.1 ∗
    hnCtxt arrayAssn eo.2.2.2.1 k.2.2.1 ∗ hnCtxt arrayAssn eo.2.2.2.2 k.2.2.2

theorem elimOutAssn_def (eo : OrderSynth.ElimOut) (k : String × String × String × String) :
    elimOutAssn eo k = hnCtxt arrayAssn eo.1 k.1 ∗ hnCtxt arrayAssn eo.2.1 k.2.1 ∗
      hnCtxt arrayAssn eo.2.2.2.1 k.2.2.1 ∗ hnCtxt arrayAssn eo.2.2.2.2 k.2.2.2 := rfl

/-- **The elimination engine, one `Com`**: the five passes in the
program's order — degree, buckets, elimination, offsets, fill. -/
def elimEngineCom : Com :=
  degPassSynth_impl.seq (Lax3Proofs.Refine.ElimSynth2.buckSynth_impl.seq
    (Lax3Proofs.Refine.ElimSynth3.elimSynth_impl.seq
      (offSynth7_impl.seq fillSynth7_impl)))

/-- `elimProgram`, flattened along the monad laws: the five passes in a
single `bindT` chain with one pure repackaging tail. -/
theorem elimProgram_flat (n : ℕ) (off tgt alv : List ℕ)
    (deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀ : List ℕ) :
    ElimSynth6.elimProgram n off tgt alv deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀
      = NRest.bindT (ElimSynth.degPass n off tgt alv (deg₀, 0)) (fun dd =>
          NRest.bindT (ElimSynth2.buckPass n dd.1 (bh₀, bv₀, bn₀, 1, 0)) (fun b =>
            NRest.bindT (ElimSynth3.elimLoop n off tgt alv
                (dd.1, elm₀, rnk₀, idg₀, b.1, b.2.1, b.2.2.1, n + 1, 0, 0, 0)) (fun e =>
              NRest.bindT (ElimSynth2.offPass n e.2.2.2.1 (ioff₀, ifl₀, 0, 0)) (fun o =>
                NRest.bindT (ElimSynth2.fillPass n off tgt alv e.2.2.1 (itg₀, o.2.1, 0))
                  (fun f => NRest.returnT (ElimSynth6.elimOutOf (e, o, f))))))) := by
  simp only [ElimSynth6.elimProgram, ElimSynth6.elimEngine5, ElimSynth5.elimEngine,
    NRest.bindT_assoc_acost, NRest.returnT_bindT]

/-- `hnRefine_frame` with the entailment in `FRAME` form, so the frame
metavariable is `fri`'s to instantiate. -/
theorem hnRefine_frame_fri {α κ : Type} {P P' Q' F : Assn} {c : Com} {d : κ}
    {R : α → κ → Assn} {m : NRest α ECost}
    (hnr : hnRefine P' c Q' d R m) (hF : Ir.FRAME P P' F) :
    hnRefine P c (Q' ∗ F) d R m :=
  hnRefine_frame hnr hF

set_option maxHeartbeats 4000000 in
/-- **The engine as one `Com`, one `hnRefine` — E43 obstruction (2)
closed.** Against `elimProgram`'s own text, at `RamElim.Implements`'s
input surface, the composed program runs the five passes and leaves the
four distinct `elimOutOf` components in their cells, everything else at
junk of its recorded length. -/
theorem elimEngineCom_hnr {n ns W : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}
    (hcsr : RamElim.CsrSimple G ns O T) (hW : ns ≤ W)
    (deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀ : List ℕ)
    (hdeg : deg₀.length = n) (helm : elm₀.length = n) (helm0 : ∀ v < n, elm₀[v]! = 0)
    (hrnk : rnk₀.length = n) (hidg : idg₀.length = n)
    (hbh : bh₀.length = n + 1) (hbh0 : ∀ j ≤ n, bh₀[j]! = 0)
    (hbv : bv₀.length = n + W + 1) (hbn : bn₀.length = n + W + 1)
    (hio : ioff₀.length = n + 1) (hio0 : ioff₀[0]! = 0) (hifl : ifl₀.length = n)
    (hitg : itg₀.length = W) :
    hnRefine
      (hnCtxt (arrayAssn ×ₐ natAssn) (deg₀, 0) ("deg", "di") ∗
        hnCtxt arrayAssn (arrOf (n + 1) O) "off" ∗ hnCtxt arrayAssn (arrOf ns T) "tgt" ∗
        hnCtxt arrayAssn (arrOf n M) "alv" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        junkCell "dj" ∗ junkCell "dip" ∗ junkCell "djend" ∗ junkCell "dc" ∗
        junkCell "du" ∗ junkCell "dau" ∗ junkCell "dai" ∗
        hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
          (bh₀, bv₀, bn₀, 1, 0) ("bh", "bv", "bn", "sp", "i") ∗
        junkCell "d" ∗ junkCell "bhd" ∗
        hnCtxt arrayAssn elm₀ "elm" ∗ hnCtxt arrayAssn rnk₀ "rnk" ∗
        hnCtxt arrayAssn idg₀ "idg" ∗
        hnCtxt natAssn 0 "cnt" ∗ hnCtxt natAssn 0 "mind" ∗ hnCtxt natAssn 0 "kmax" ∗
        junkCell "bhm" ∗ junkCell "w" ∗ junkCell "bnp" ∗ junkCell "ew" ∗ junkCell "dw" ∗
        junkCell "nm" ∗ junkCell "rw" ∗ junkCell "dk" ∗ junkCell "aw" ∗ junkCell "j" ∗
        junkCell "wp" ∗ junkCell "jend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗
        junkCell "dv" ∗
        hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn) (ioff₀, ifl₀, 0, 0)
          ("ioff", "ifl", "os", "oi") ∗
        junkCell "odi" ∗ junkCell "oip" ∗
        hnCtxt arrayAssn itg₀ "itg" ∗ hnCtxt natAssn 0 "fi" ∗
        junkCell "fai" ∗ junkCell "fri" ∗ junkCell "fj" ∗ junkCell "fip" ∗
        junkCell "fjend" ∗ junkCell "fu" ∗ junkCell "fau" ∗ junkCell "fru" ∗ junkCell "fp")
      elimEngineCom
      (hnCtxt arrayAssn (arrOf (n + 1) O) "off" ∗ hnCtxt arrayAssn (arrOf ns T) "tgt" ∗
        hnCtxt arrayAssn (arrOf n M) "alv" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        junkArrayOfLen n "deg" ∗ junkArrayOfLen n "elm" ∗ junkArrayOfLen (n + 1) "bh" ∗
        junkArrayOfLen (n + W + 1) "bv" ∗ junkArrayOfLen (n + W + 1) "bn" ∗
        junkArrayOfLen n "ifl" ∗
        junkCell "di" ∗ junkCell "sp" ∗ junkCell "i" ∗ junkCell "cnt" ∗ junkCell "mind" ∗
        junkCell "kmax" ∗ junkCell "os" ∗ junkCell "oi" ∗ junkCell "fi" ∗
        junkCell "dj" ∗ junkCell "dip" ∗ junkCell "djend" ∗ junkCell "dc" ∗
        junkCell "du" ∗ junkCell "dau" ∗ junkCell "dai" ∗ junkCell "d" ∗ junkCell "bhd" ∗
        junkCell "bhm" ∗ junkCell "w" ∗ junkCell "bnp" ∗ junkCell "ew" ∗ junkCell "dw" ∗
        junkCell "nm" ∗ junkCell "rw" ∗ junkCell "dk" ∗ junkCell "aw" ∗ junkCell "j" ∗
        junkCell "wp" ∗ junkCell "jend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗
        junkCell "dv" ∗ junkCell "odi" ∗ junkCell "oip" ∗
        junkCell "fai" ∗ junkCell "fri" ∗ junkCell "fj" ∗ junkCell "fip" ∗
        junkCell "fjend" ∗ junkCell "fu" ∗ junkCell "fau" ∗ junkCell "fru" ∗ junkCell "fp")
      ("rnk", "idg", "ioff", "itg") elimOutAssn
      (ElimSynth6.elimProgram n (arrOf (n + 1) O) (arrOf ns T) (arrOf n M)
        deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀) := by
  rw [elimProgram_flat]
  unfold elimEngineCom
  -- ── Seam 1: the degree pass ──
  refine hnr_seq (hnRefine_frame_fri
    (degPassSynth n (arrOf (n + 1) O) (arrOf ns T) (arrOf n M) deg₀ 0) (by fri))
    (fun dd hgd => ?_)
  obtain ⟨dd1, dd2⟩ := dd
  have hd := ElimSynth.res_spec_of_le
    (degPass_adeg hcsr deg₀ hdeg) hgd
  -- ── Seam 2: the bucket build ──
  refine hnr_seq (hnRefine_frame_fri
    (ElimSynth2.buckSynth n dd1 bh₀ bv₀ bn₀ 1 0) (by fri)) (fun b hgb => ?_)
  obtain ⟨b1, b2, b3, b4, b5⟩ := b
  have hdlt : ∀ v < n, dd1[v]! < n := fun v hv => by
    rw [hd.2 v hv, RamElim.adeg_eq hv]
    exact RamElim.card_nbrsIn_lt _ _
  have hbF := ElimSynth.res_spec_of_le
    (ElimSynth2.buckPass_spec (W := W) hd.1 hdlt hbh hbh0 hbv hbn) hgb
  obtain ⟨hbF1, hbF2, hbF3, hbF4, hbF5, hbuck⟩ := hbF
  subst hbF4
  -- ── Seam 3: the elimination loop ──
  have hin : ElimSynth4.EIn n ns W G (arrOf (n + 1) O) (arrOf ns T) (arrOf n M) :=
    ElimSynth5.eIn_arrOf hcsr hW
  have hdegA : ∀ v < n, dd1[v]! = RamElim.adeg G (ElimSynth2.larr (arrOf n M)) v :=
    fun v hv => by rw [hd.2 v hv]; exact ElimSynth5.adeg_arrOf
  have hls : ElimSynth4.lsOf n b1 b3 = n := hbuck.ls_eq.symm
  have hI0 : ElimSynth4.ElimI n ns W G (arrOf (n + 1) O) (arrOf ns T) (arrOf n M)
      (dd1, elm₀, rnk₀, idg₀, b1, b2, b3, n + 1, 0, 0, 0) := by
    refine ⟨hd.1, helm, hrnk, hidg, hbF1, hbF2, hbF3, ?_, ?_, hdlt, ?_, ?_,
      Nat.zero_le n, Nat.zero_le n⟩
    · exact RamElim.Elim.init (fun v hv => by simpa using helm0 v hv)
        (fun v => by
          show dd1[(v : ℕ)]! = _
          rw [hdegA (v : ℕ) v.isLt, RamElim.adeg_eq v.isLt])
    · show RamElim.Buck n n (ElimSynth2.larr elm₀) (ElimSynth2.larr dd1)
        (ElimSynth2.larr b1) (ElimSynth2.larr b2) (ElimSynth2.larr b3) (n + 1)
        (ElimSynth4.lsOf n b1 b3)
      rw [hls]
      exact hbuck.weaken _
    · show n + 1 ≤ n + 1 + ElimSynth4.scOf n (ElimSynth2.larr (arrOf (n + 1) O))
        (ElimSynth2.larr (arrOf n M)) elm₀
      omega
    · show ElimSynth4.lsOf n b1 b3 + 1 ≤ n + 1
      rw [hls]
  refine hnr_seq (hnRefine_frame_fri
    (ElimSynth3.elimSynth n (arrOf (n + 1) O) (arrOf ns T) (arrOf n M)
      dd1 elm₀ rnk₀ idg₀ b1 b2 b3 (n + 1) 0 0 0) (by fri)) (fun e hge => ?_)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := e
  have hEI := ElimSynth.res_spec_of_le
    (ElimSynth5.elimLoop_le hin
      (ElimSynth5.elimV n ns (arrOf (n + 1) O) (arrOf n M)
        (dd1, elm₀, rnk₀, idg₀, b1, b2, b3, n + 1, 0, 0, 0) + 1)
      (dd1, elm₀, rnk₀, idg₀, b1, b2, b3, n + 1, 0, 0, 0) hI0 (Nat.lt_succ_self _)) hge
  have hans : ElimSynth5.ElimAnswer n ns G (arrOf n M)
      (e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11) :=
    ElimSynth5.elimExit hin hEI.1 hEI.2
  -- ── Seam 4: the offset pass ──
  refine hnr_seq (hnRefine_frame_fri (offSynth7 n e4 ioff₀ ifl₀ 0 0) (by fri))
    (fun o hgo => ?_)
  obtain ⟨o1, o2, o3, o4⟩ := o
  have hoF := ElimSynth.res_spec_of_le
    (ElimSynth2.offPass_spec hEI.1.idgLen hio hio0 hifl) hgo
  -- ── Seam 5: the fill pass, and the repackaging tail ──
  refine hnr_map (hnRefine_frame_fri
    (fillSynth7 n (arrOf (n + 1) O) (arrOf ns T) (arrOf n M) e3 itg₀ o2 0) (by fri))
    (fun f hgf => ?_)
  obtain ⟨f1, f2, f3⟩ := f
  have hfF := ElimSynth.res_spec_of_le
    (ElimSynth6.fillPass_spec hin hans hitg hoF.2.1 (fun v hv => hoF.2.2.2 v hv)) hgf
  -- the final entailment: everything into its resting place
  refine entails_trans (Q :=
      (hnCtxt arrayAssn (arrOf (n + 1) O) "off" ∗ hnCtxt arrayAssn (arrOf ns T) "tgt" ∗
        hnCtxt arrayAssn (arrOf n M) "alv" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        hnCtxt arrayAssn e1 "deg" ∗ hnCtxt arrayAssn e2 "elm" ∗
        hnCtxt arrayAssn e5 "bh" ∗ hnCtxt arrayAssn e6 "bv" ∗ hnCtxt arrayAssn e7 "bn" ∗
        hnCtxt arrayAssn f2 "ifl" ∗
        junkCell "di" ∗ junkCell "sp" ∗ junkCell "i" ∗ junkCell "cnt" ∗ junkCell "mind" ∗
        junkCell "kmax" ∗ junkCell "os" ∗ junkCell "oi" ∗ junkCell "fi" ∗
        junkCell "dj" ∗ junkCell "dip" ∗ junkCell "djend" ∗ junkCell "dc" ∗
        junkCell "du" ∗ junkCell "dau" ∗ junkCell "dai" ∗ junkCell "d" ∗ junkCell "bhd" ∗
        junkCell "bhm" ∗ junkCell "w" ∗ junkCell "bnp" ∗ junkCell "ew" ∗ junkCell "dw" ∗
        junkCell "nm" ∗ junkCell "rw" ∗ junkCell "dk" ∗ junkCell "aw" ∗ junkCell "j" ∗
        junkCell "wp" ∗ junkCell "jend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗
        junkCell "dv" ∗ junkCell "odi" ∗ junkCell "oip" ∗
        junkCell "fai" ∗ junkCell "fri" ∗ junkCell "fj" ∗ junkCell "fip" ∗
        junkCell "fjend" ∗ junkCell "fu" ∗ junkCell "fau" ∗ junkCell "fru" ∗
        junkCell "fp") ∗
      (hnCtxt arrayAssn e3 "rnk" ∗ hnCtxt arrayAssn e4 "idg" ∗
        hnCtxt arrayAssn o1 "ioff" ∗ hnCtxt arrayAssn f1 "itg"))
    (by fri) ?_
  refine conj_entails_mono ?_ (entails_of_eq rfl)
  refine conj_entails_mono (entails_refl _) ?_
  refine conj_entails_mono (entails_refl _) ?_
  refine conj_entails_mono (entails_refl _) ?_
  refine conj_entails_mono (entails_refl _) ?_
  refine conj_entails_mono (entails_refl _) ?_
  refine conj_entails_mono (entails_refl _) ?_
  refine conj_entails_mono
    (arrayAssn_entails_junkArrayOfLen' e1 "deg" hEI.1.degLen) ?_
  refine conj_entails_mono
    (arrayAssn_entails_junkArrayOfLen' e2 "elm" hEI.1.elmLen) ?_
  refine conj_entails_mono
    (arrayAssn_entails_junkArrayOfLen' e5 "bh" hEI.1.bhLen) ?_
  refine conj_entails_mono
    (arrayAssn_entails_junkArrayOfLen' e6 "bv" hEI.1.bvLen) ?_
  refine conj_entails_mono
    (arrayAssn_entails_junkArrayOfLen' e7 "bn" hEI.1.bnLen) ?_
  exact conj_entails_mono
    (arrayAssn_entails_junkArrayOfLen' f2 "ifl" hfF.2) (entails_refl _)

end Engine

/-! ## 6. The spec-shaped leaf — E43 obstruction (3) closed

The engine, entry-state-free. The abstract program is
`NRest.spec (OrderSynth.ElimPost n W) …` — no entry tuple, so a phase's
second call is the same text as its first. The machine side earns that:
the `Com` *builds its own zero state* (three fills and thirteen counter
constants sit inside it, which is `ElimSynth.lean`'s "the engine itself
produced the `List.replicate _ 0`" made machine-real — `elimRezeroCom`
has no counterpart because there is nothing outside the engine to
re-zero), and doubles the offsets into `iof2` because `elimOutOf` names
them twice and one cell cannot be owned twice.

The ownership discipline of the rule (what kills obstruction (3)):

* the six **pure-scratch** arrays (`deg elm bh bv bn ifl`) enter *and
  leave* as `junkArrayOfLen` — owned, length known, contents free — so
  the second call's entry is the first call's exit verbatim;
* the five **output** arrays (`rnk idg iof2 ioff itg`) enter at whatever
  values the caller holds, with their lengths as rule premises — and
  those lengths are exactly `ElimPost`'s five length clauses, so at the
  second call the tool discharges them from the first call's
  `bind_ref_tag` hypothesis (`bind_ref_tag_spec_iff`).

Carried debts, untouched: E1 (amortized transport), E2 (correctness
transport), E3 (BRefine nested-while). -/

section SpecLeaf

open Lax13Proofs.Reasoning (arrOf)
open Lax13Proofs.Refine.Sepref.Iicf (junkArrayOfLen arrayAssn_entails_junkArrayOfLen'
  hnRefine_junkArrayOfLen)

/-- The fill loop at symbolic cells — `zfill`'s program. -/
def zfillCom (a i v cnt one : String) : Com :=
  Com.while (Cond.lt (Operand.cell i) (Operand.cell cnt))
    ((Com.aset a i v).seq ((Com.binop Lax13Proofs.Imp.Bop.add i i one).seq Com.skip))

/-- The copy loop at symbolic cells — `zcopy`'s program. -/
def zcopyCom (d i s cnt one u : String) : Com :=
  Com.while (Cond.lt (Operand.cell i) (Operand.cell cnt))
    ((Com.aget u s i).seq
      ((Com.aset d i u).seq ((Com.binop Lax13Proofs.Imp.Bop.add i i one).seq Com.skip)))

/-- **The spec-shaped engine's program**: thirteen counter constants,
the three scratch-building fills, the five passes, the offsets doubled
into `iof2`. -/
def elimSpecCom : Com :=
  (Com.const "di" 0).seq ((Com.const "i" 0).seq ((Com.const "sp" 1).seq
    ((Com.const "cnt" 0).seq ((Com.const "mind" 0).seq ((Com.const "kmax" 0).seq
      ((Com.const "os" 0).seq ((Com.const "oi" 0).seq ((Com.const "fi" 0).seq
        ((Com.const "zi1" 0).seq ((Com.const "zi2" 0).seq ((Com.const "zi3" 0).seq
          ((Com.const "ci" 0).seq
            ((zfillCom "elm" "zi1" "zero" "n" "one").seq
              ((zfillCom "bh" "zi2" "zero" "n1" "one").seq
                ((zfillCom "ioff" "zi3" "zero" "n1" "one").seq
                  (elimEngineCom.seq
                    (zcopyCom "iof2" "ci" "ioff" "n1" "one" "cu")))))))))))))))))

/-- The abstract program the leaf's `hnRefine` is composed against: the
counter constants, the fills, `elimProgram` at the freshly built zero
state, the copy, the repackaging. -/
noncomputable def elimSpecProg (n : ℕ) (off tgt alv : List ℕ)
    (deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀ iof2₀ : List ℕ) :
    NRest OrderSynth.ElimOut ECost :=
  NRest.bindT (mopConstN 0) fun _ => NRest.bindT (mopConstN 0) fun _ =>
  NRest.bindT (mopConstN 1) fun _ => NRest.bindT (mopConstN 0) fun _ =>
  NRest.bindT (mopConstN 0) fun _ => NRest.bindT (mopConstN 0) fun _ =>
  NRest.bindT (mopConstN 0) fun _ => NRest.bindT (mopConstN 0) fun _ =>
  NRest.bindT (mopConstN 0) fun _ => NRest.bindT (mopConstN 0) fun _ =>
  NRest.bindT (mopConstN 0) fun _ => NRest.bindT (mopConstN 0) fun _ =>
  NRest.bindT (mopConstN 0) fun _ =>
  NRest.bindT (OrderSynth.fillPass n 0 (elm₀, 0)) fun ze =>
  NRest.bindT (OrderSynth.fillPass (n + 1) 0 (bh₀, 0)) fun zb =>
  NRest.bindT (OrderSynth.fillPass (n + 1) 0 (ioff₀, 0)) fun zo =>
  NRest.bindT (ElimSynth6.elimProgram n off tgt alv
      deg₀ ze.1 rnk₀ idg₀ zb.1 bv₀ bn₀ zo.1 ifl₀ itg₀) fun r =>
  NRest.bindT (OrderSynth.copyPass (n + 1) r.2.2.2.1 (iof2₀, 0)) fun cb =>
  NRest.returnT (r.1, r.2.1, cb.1, r.2.2.2.1, r.2.2.2.2)

/-- The leaf's price: the constants, the three fills, `engineC5`, the
copy. -/
noncomputable def elimSpecC (n ns : ℕ) : ACost String ℕ :=
  cu Currency.const + (cu Currency.const + (cu Currency.const + (cu Currency.const +
    (cu Currency.const + (cu Currency.const + (cu Currency.const + (cu Currency.const +
      (cu Currency.const + (cu Currency.const + (cu Currency.const + (cu Currency.const +
        (cu Currency.const + (OrderSynth.pfC n + (OrderSynth.pfC (n + 1) +
          (OrderSynth.pfC (n + 1) + (ElimSynth6.engineC5 n ns +
            OrderSynth.pcC (n + 1)))))))))))))))))

/-- The bound on `mopConstN`: one `const` unit, any result. -/
theorem mopConstN_le (v : ℕ) :
    mopConstN v ≤ NRest.spec (fun _ : ℕ => True)
      (fun _ => liftACost (cu Currency.const)) :=
  consume_returnT_le_spec trivial (le_of_eq (BfsQ.liftACost_cu Currency.const).symm)

/-- **The spec-shaped program meets `ElimPost` at `elimSpecC`.** Only
*lengths* of the eleven arrays are assumed — the zero state the five
passes need is built by the program itself. -/
theorem elimSpecProg_le {n ns W : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}
    (hcsr : RamElim.CsrSimple G ns O T) (hW : ns ≤ W)
    {deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀ iof2₀ : List ℕ}
    (hdeg : deg₀.length = n) (helm : elm₀.length = n)
    (hrnk : rnk₀.length = n) (hidg : idg₀.length = n)
    (hbh : bh₀.length = n + 1) (hbv : bv₀.length = n + W + 1)
    (hbn : bn₀.length = n + W + 1) (hio : ioff₀.length = n + 1)
    (hifl : ifl₀.length = n) (hitg : itg₀.length = W) (hio2 : iof2₀.length = n + 1) :
    elimSpecProg n (arrOf (n + 1) O) (arrOf ns T) (arrOf n M)
        deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀ iof2₀
      ≤ NRest.spec (OrderSynth.ElimPost n W)
          (fun _ => liftACost (elimSpecC n ns)) := by
  rw [elimSpecProg, elimSpecC]
  refine ElimSynth5.seqA_le (mopConstN_le 0) fun _ _ => ?_
  refine ElimSynth5.seqA_le (mopConstN_le 0) fun _ _ => ?_
  refine ElimSynth5.seqA_le (mopConstN_le 1) fun _ _ => ?_
  refine ElimSynth5.seqA_le (mopConstN_le 0) fun _ _ => ?_
  refine ElimSynth5.seqA_le (mopConstN_le 0) fun _ _ => ?_
  refine ElimSynth5.seqA_le (mopConstN_le 0) fun _ _ => ?_
  refine ElimSynth5.seqA_le (mopConstN_le 0) fun _ _ => ?_
  refine ElimSynth5.seqA_le (mopConstN_le 0) fun _ _ => ?_
  refine ElimSynth5.seqA_le (mopConstN_le 0) fun _ _ => ?_
  refine ElimSynth5.seqA_le (mopConstN_le 0) fun _ _ => ?_
  refine ElimSynth5.seqA_le (mopConstN_le 0) fun _ _ => ?_
  refine ElimSynth5.seqA_le (mopConstN_le 0) fun _ _ => ?_
  refine ElimSynth5.seqA_le (mopConstN_le 0) fun _ _ => ?_
  refine ElimSynth5.seqA_le (OrderSynth.fillPass_spec helm le_rfl) fun ze hze => ?_
  refine ElimSynth5.seqA_le (OrderSynth.fillPass_spec hbh le_rfl) fun zb hzb => ?_
  refine ElimSynth5.seqA_le (OrderSynth.fillPass_spec hio le_rfl) fun zo hzo => ?_
  have helm0' : ∀ v < n, ze.1[v]! = 0 := fun v hv => by rw [hze.2 v, if_pos hv]
  have hbh0' : ∀ j ≤ n, zb.1[j]! = 0 := fun j hj => by
    rw [hzb.2 j, if_pos (by omega)]
  have hio0' : zo.1[0]! = 0 := by rw [hzo.2 0, if_pos (by omega)]
  refine ElimSynth5.seqA_le (ElimSynth6.elimPost_of_engine hcsr hW hdeg hze.1 helm0'
    hrnk hidg hzb.1 hbh0' hbv hbn hzo.1 hio0' hifl hitg) fun r hr => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
  exact ElimSynth5.bindA_ret
    (OrderSynth.copyPass_spec hio2 le_rfl (le_of_eq h4.symm))
    fun cb hcb => ⟨h1, h2, hcb.1, h4, h5, h6, h7⟩

/-- The leaf's price, cashed. -/
def elimSpecK (n ns : ℕ) : ℕ := 384 * n + 168 * ns + 126

theorem cash_elimSpecC (n ns : ℕ) :
    Codegen.cash (elimSpecC n ns) = elimSpecK n ns := by
  rw [elimSpecC]
  simp only [Codegen.cash_add, OrderSynth.cash_pcC, OrderSynth.cash_pfC,
    ElimSynth6.cash_engine5Budget,
    show Codegen.cash (cu Currency.const) = 2 from by decide +kernel]
  rw [ElimSynth6.engineK5, elimSpecK]
  ring

-- **The number, pinned at the demo's size, against `engineK5`.** The
-- spec-shaped leaf's setup (thirteen constants, three fills, one copy)
-- rides on top of the five passes: carrier-class, same coefficient
-- shape, strictly above `engineK5` — recorded, not hidden.
#guard elimSpecK 5 10 = 3726
#guard ElimSynth6.engineK5 5 10 = 3390
#guard ¬ (elimSpecK 5 10 ≤ ElimSynth6.engineK5 5 10)
#guard elimSpecK 5 10 ≤ 2 * ElimSynth6.engineK5 5 10

/-- `hnCtxt` at `elimOutAssn`, opened for the frame solver: the engine's
result bundle is its four array conjuncts. -/
theorem hnCtxt_elimOutAssn (eo : OrderSynth.ElimOut)
    (k : String × String × String × String) :
    hnCtxt elimOutAssn eo k = hnCtxt arrayAssn eo.1 k.1 ∗ hnCtxt arrayAssn eo.2.1 k.2.1 ∗
      hnCtxt arrayAssn eo.2.2.2.1 k.2.2.1 ∗ hnCtxt arrayAssn eo.2.2.2.2 k.2.2.2 := rfl

attribute [fri_prepare_simps] hnCtxt_elimOutAssn

set_option maxHeartbeats 4000000 in
/-- The spec-shaped engine against its own program text, at explicit
entry arrays — *lengths only*, no zero conditions: the `Com` builds its
zero state itself. -/
theorem elimSpecCom_hnr {n ns W : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}
    (hcsr : RamElim.CsrSimple G ns O T) (hW : ns ≤ W)
    (deg₀ elm₀ bh₀ bv₀ bn₀ ifl₀ rnk₀ idg₀ ioff₀ itg₀ iof2₀ : List ℕ)
    (hdeg : deg₀.length = n) (helm : elm₀.length = n)
    (hbh : bh₀.length = n + 1) (hbv : bv₀.length = n + W + 1)
    (hbn : bn₀.length = n + W + 1) (hifl : ifl₀.length = n)
    (hrnk : rnk₀.length = n) (hidg : idg₀.length = n) (hio : ioff₀.length = n + 1)
    (hitg : itg₀.length = W) (hio2 : iof2₀.length = n + 1) :
    hnRefine
      (hnCtxt arrayAssn deg₀ "deg" ∗ hnCtxt arrayAssn elm₀ "elm" ∗
        hnCtxt arrayAssn bh₀ "bh" ∗ hnCtxt arrayAssn bv₀ "bv" ∗
        hnCtxt arrayAssn bn₀ "bn" ∗ hnCtxt arrayAssn ifl₀ "ifl" ∗
        hnCtxt arrayAssn rnk₀ "rnk" ∗ hnCtxt arrayAssn idg₀ "idg" ∗
        hnCtxt arrayAssn ioff₀ "ioff" ∗ hnCtxt arrayAssn itg₀ "itg" ∗
        hnCtxt arrayAssn iof2₀ "iof2" ∗
        hnCtxt arrayAssn (arrOf (n + 1) O) "off" ∗ hnCtxt arrayAssn (arrOf ns T) "tgt" ∗
        hnCtxt arrayAssn (arrOf n M) "alv" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn (n + 1) "n1" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        junkCell "di" ∗ junkCell "i" ∗ junkCell "sp" ∗ junkCell "cnt" ∗ junkCell "mind" ∗
        junkCell "kmax" ∗ junkCell "os" ∗ junkCell "oi" ∗ junkCell "fi" ∗
        junkCell "zi1" ∗ junkCell "zi2" ∗ junkCell "zi3" ∗ junkCell "ci" ∗ junkCell "cu" ∗
        junkCell "dj" ∗ junkCell "dip" ∗ junkCell "djend" ∗ junkCell "dc" ∗
        junkCell "du" ∗ junkCell "dau" ∗ junkCell "dai" ∗ junkCell "d" ∗ junkCell "bhd" ∗
        junkCell "bhm" ∗ junkCell "w" ∗ junkCell "bnp" ∗ junkCell "ew" ∗ junkCell "dw" ∗
        junkCell "nm" ∗ junkCell "rw" ∗ junkCell "dk" ∗ junkCell "aw" ∗ junkCell "j" ∗
        junkCell "wp" ∗ junkCell "jend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗
        junkCell "dv" ∗ junkCell "odi" ∗ junkCell "oip" ∗
        junkCell "fai" ∗ junkCell "fri" ∗ junkCell "fj" ∗ junkCell "fip" ∗
        junkCell "fjend" ∗ junkCell "fu" ∗ junkCell "fau" ∗ junkCell "fru" ∗ junkCell "fp")
      elimSpecCom
      (hnCtxt arrayAssn (arrOf (n + 1) O) "off" ∗ hnCtxt arrayAssn (arrOf ns T) "tgt" ∗
        hnCtxt arrayAssn (arrOf n M) "alv" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn (n + 1) "n1" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        junkArrayOfLen n "deg" ∗ junkArrayOfLen n "elm" ∗ junkArrayOfLen (n + 1) "bh" ∗
        junkArrayOfLen (n + W + 1) "bv" ∗ junkArrayOfLen (n + W + 1) "bn" ∗
        junkArrayOfLen n "ifl" ∗
        junkCell "di" ∗ junkCell "i" ∗ junkCell "sp" ∗ junkCell "cnt" ∗ junkCell "mind" ∗
        junkCell "kmax" ∗ junkCell "os" ∗ junkCell "oi" ∗ junkCell "fi" ∗
        junkCell "zi1" ∗ junkCell "zi2" ∗ junkCell "zi3" ∗ junkCell "ci" ∗ junkCell "cu" ∗
        junkCell "dj" ∗ junkCell "dip" ∗ junkCell "djend" ∗ junkCell "dc" ∗
        junkCell "du" ∗ junkCell "dau" ∗ junkCell "dai" ∗ junkCell "d" ∗ junkCell "bhd" ∗
        junkCell "bhm" ∗ junkCell "w" ∗ junkCell "bnp" ∗ junkCell "ew" ∗ junkCell "dw" ∗
        junkCell "nm" ∗ junkCell "rw" ∗ junkCell "dk" ∗ junkCell "aw" ∗ junkCell "j" ∗
        junkCell "wp" ∗ junkCell "jend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗
        junkCell "dv" ∗ junkCell "odi" ∗ junkCell "oip" ∗
        junkCell "fai" ∗ junkCell "fri" ∗ junkCell "fj" ∗ junkCell "fip" ∗
        junkCell "fjend" ∗ junkCell "fu" ∗ junkCell "fau" ∗ junkCell "fru" ∗ junkCell "fp")
      ("rnk", "idg", "iof2", "ioff", "itg")
      (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn)
      (elimSpecProg n (arrOf (n + 1) O) (arrOf ns T) (arrOf n M)
        deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ ioff₀ ifl₀ itg₀ iof2₀) := by
  rw [elimSpecProg]
  unfold elimSpecCom zfillCom zcopyCom
  refine hnr_seq (hnRefine_frame_fri (hnr_mop_constN "di" 0) (by fri)) (fun z hz => ?_)
  obtain rfl : z = 0 := bind_ref_tag_pin hz
  refine hnr_seq (hnRefine_frame_fri (hnr_mop_constN "i" 0) (by fri)) (fun z hz => ?_)
  obtain rfl : z = 0 := bind_ref_tag_pin hz
  refine hnr_seq (hnRefine_frame_fri (hnr_mop_constN "sp" 1) (by fri)) (fun z hz => ?_)
  obtain rfl : z = 1 := bind_ref_tag_pin hz
  refine hnr_seq (hnRefine_frame_fri (hnr_mop_constN "cnt" 0) (by fri)) (fun z hz => ?_)
  obtain rfl : z = 0 := bind_ref_tag_pin hz
  refine hnr_seq (hnRefine_frame_fri (hnr_mop_constN "mind" 0) (by fri)) (fun z hz => ?_)
  obtain rfl : z = 0 := bind_ref_tag_pin hz
  refine hnr_seq (hnRefine_frame_fri (hnr_mop_constN "kmax" 0) (by fri)) (fun z hz => ?_)
  obtain rfl : z = 0 := bind_ref_tag_pin hz
  refine hnr_seq (hnRefine_frame_fri (hnr_mop_constN "os" 0) (by fri)) (fun z hz => ?_)
  obtain rfl : z = 0 := bind_ref_tag_pin hz
  refine hnr_seq (hnRefine_frame_fri (hnr_mop_constN "oi" 0) (by fri)) (fun z hz => ?_)
  obtain rfl : z = 0 := bind_ref_tag_pin hz
  refine hnr_seq (hnRefine_frame_fri (hnr_mop_constN "fi" 0) (by fri)) (fun z hz => ?_)
  obtain rfl : z = 0 := bind_ref_tag_pin hz
  refine hnr_seq (hnRefine_frame_fri (hnr_mop_constN "zi1" 0) (by fri)) (fun z hz => ?_)
  obtain rfl : z = 0 := bind_ref_tag_pin hz
  refine hnr_seq (hnRefine_frame_fri (hnr_mop_constN "zi2" 0) (by fri)) (fun z hz => ?_)
  obtain rfl : z = 0 := bind_ref_tag_pin hz
  refine hnr_seq (hnRefine_frame_fri (hnr_mop_constN "zi3" 0) (by fri)) (fun z hz => ?_)
  obtain rfl : z = 0 := bind_ref_tag_pin hz
  refine hnr_seq (hnRefine_frame_fri (hnr_mop_constN "ci" 0) (by fri)) (fun z hz => ?_)
  obtain rfl : z = 0 := bind_ref_tag_pin hz
  refine hnr_seq (hnRefine_frame_fri (zfill "elm" "zi1" "zero" "n" "one" n 0 elm₀ 0)
    (by fri)) (fun ze hgz1 => ?_)
  obtain ⟨ze1, ze2⟩ := ze
  have hzeF := ElimSynth.res_spec_of_le (OrderSynth.fillPass_spec helm le_rfl) hgz1
  refine hnr_seq (hnRefine_frame_fri (zfill "bh" "zi2" "zero" "n1" "one" (n + 1) 0 bh₀ 0)
    (by fri)) (fun zb hgz2 => ?_)
  obtain ⟨zb1, zb2⟩ := zb
  have hzbF := ElimSynth.res_spec_of_le (OrderSynth.fillPass_spec hbh le_rfl) hgz2
  refine hnr_seq (hnRefine_frame_fri (zfill "ioff" "zi3" "zero" "n1" "one" (n + 1) 0 ioff₀ 0)
    (by fri)) (fun zo hgz3 => ?_)
  obtain ⟨zo1, zo2⟩ := zo
  have hzoF := ElimSynth.res_spec_of_le (OrderSynth.fillPass_spec hio le_rfl) hgz3
  have helm0' : ∀ v < n, ze1[v]! = 0 := fun v hv => by
    have h := hzeF.2 v
    rwa [if_pos hv] at h
  have hbh0' : ∀ j ≤ n, zb1[j]! = 0 := fun j hj => by
    have h := hzbF.2 j
    rwa [if_pos (show j < n + 1 by omega)] at h
  have hio0' : zo1[0]! = 0 := by
    have h := hzoF.2 0
    rwa [if_pos (show 0 < n + 1 by omega)] at h
  refine hnr_seq (hnRefine_frame_fri
    (elimEngineCom_hnr hcsr hW deg₀ ze1 rnk₀ idg₀ zb1 bv₀ bn₀ zo1 ifl₀ itg₀
      hdeg hzeF.1 helm0' hrnk hidg hzbF.1 hbh0' hbv hbn hzoF.1 hio0' hifl hitg)
    (by fri)) (fun r hgr => ?_)
  obtain ⟨r1, r2, r3, r4, r5⟩ := r
  have hrP := ElimSynth.res_spec_of_le
    (ElimSynth6.elimPost_of_engine hcsr hW hdeg hzeF.1 helm0' hrnk hidg hzbF.1 hbh0'
      hbv hbn hzoF.1 hio0' hifl hitg) hgr
  refine hnr_map (hnRefine_frame_fri
    (zcopy "iof2" "ci" "ioff" "n1" "one" "cu" (n + 1) r4 iof2₀ 0) (by fri))
    (fun cb hgc => ?_)
  obtain ⟨cb1, cb2⟩ := cb
  fri

/-! ### The junk-array openers

`Iicf.hnRefine_junkArrayOfLen` opens a `junkArrayOfLen` at the *head* of
the precondition; the leaf's six sit nested one deeper each. Five
positional variants, each a reassociation away from the head form. -/

section Openers

open Lax13Proofs.Refine.Sepref.Iicf (junkArrayOfLen hnRefine_junkArrayOfLen entails_of_eq)

variable {α κ : Type} {Γ Γ' : Assn} {c : Com} {d : κ} {R : α → κ → Assn}
  {m : NRest α ECost} {L : ℕ} {a : String}

theorem hnr_scr1 {A1 : Assn}
    (h : ∀ xs : List ℕ, xs.length = L →
      hnRefine (A1 ∗ (arrayAssn xs a ∗ Γ)) c Γ' d R m) :
    hnRefine (A1 ∗ (junkArrayOfLen L a ∗ Γ)) c Γ' d R m := by
  refine hnRefine_cons_pre
    (hnRefine_junkArrayOfLen (Γ := A1 ∗ Γ) fun xs hxs =>
      hnRefine_cons_pre (h xs hxs) (entails_of_eq (by ac_rfl)))
    (entails_of_eq (by ac_rfl))

theorem hnr_scr2 {A1 A2 : Assn}
    (h : ∀ xs : List ℕ, xs.length = L →
      hnRefine (A1 ∗ (A2 ∗ (arrayAssn xs a ∗ Γ))) c Γ' d R m) :
    hnRefine (A1 ∗ (A2 ∗ (junkArrayOfLen L a ∗ Γ))) c Γ' d R m := by
  refine hnRefine_cons_pre
    (hnr_scr1 (A1 := A1 ∗ A2) (Γ := Γ) (L := L) (a := a) fun xs hxs =>
      hnRefine_cons_pre (h xs hxs) (entails_of_eq (by ac_rfl)))
    (entails_of_eq (by ac_rfl))

theorem hnr_scr3 {A1 A2 A3 : Assn}
    (h : ∀ xs : List ℕ, xs.length = L →
      hnRefine (A1 ∗ (A2 ∗ (A3 ∗ (arrayAssn xs a ∗ Γ)))) c Γ' d R m) :
    hnRefine (A1 ∗ (A2 ∗ (A3 ∗ (junkArrayOfLen L a ∗ Γ)))) c Γ' d R m := by
  refine hnRefine_cons_pre
    (hnr_scr1 (A1 := A1 ∗ A2 ∗ A3) (Γ := Γ) (L := L) (a := a) fun xs hxs =>
      hnRefine_cons_pre (h xs hxs) (entails_of_eq (by ac_rfl)))
    (entails_of_eq (by ac_rfl))

theorem hnr_scr4 {A1 A2 A3 A4 : Assn}
    (h : ∀ xs : List ℕ, xs.length = L →
      hnRefine (A1 ∗ (A2 ∗ (A3 ∗ (A4 ∗ (arrayAssn xs a ∗ Γ))))) c Γ' d R m) :
    hnRefine (A1 ∗ (A2 ∗ (A3 ∗ (A4 ∗ (junkArrayOfLen L a ∗ Γ))))) c Γ' d R m := by
  refine hnRefine_cons_pre
    (hnr_scr1 (A1 := A1 ∗ A2 ∗ A3 ∗ A4) (Γ := Γ) (L := L) (a := a) fun xs hxs =>
      hnRefine_cons_pre (h xs hxs) (entails_of_eq (by ac_rfl)))
    (entails_of_eq (by ac_rfl))

theorem hnr_scr5 {A1 A2 A3 A4 A5 : Assn}
    (h : ∀ xs : List ℕ, xs.length = L →
      hnRefine (A1 ∗ (A2 ∗ (A3 ∗ (A4 ∗ (A5 ∗ (arrayAssn xs a ∗ Γ)))))) c Γ' d R m) :
    hnRefine (A1 ∗ (A2 ∗ (A3 ∗ (A4 ∗ (A5 ∗ (junkArrayOfLen L a ∗ Γ)))))) c Γ' d R m := by
  refine hnRefine_cons_pre
    (hnr_scr1 (A1 := A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5) (Γ := Γ) (L := L) (a := a) fun xs hxs =>
      hnRefine_cons_pre (h xs hxs) (entails_of_eq (by ac_rfl)))
    (entails_of_eq (by ac_rfl))

end Openers

set_option maxHeartbeats 1000000 in
/-- **THE SPEC-SHAPED ENGINE LEAF — E43 obstruction (3) closed.**

The abstract program binds **no entry state**: it is the bare
specification. The six pure-scratch arrays are owned as
`junkArrayOfLen` — identical in the pre and the post, so a second call
matches the first call's exit verbatim — and the five output arrays
enter at the caller's values with their lengths as premises, which are
exactly `ElimPost`'s five length clauses of the previous call. -/
@[sepref_fr_rules]
theorem hnr_mop_elim_spec (n ns W : ℕ) (G : SimpleGraph (Fin n)) (O T M : ℕ → ℕ)
    (hcsr : RamElim.CsrSimple G ns O T) (hW : ns ≤ W)
    (rnk₀ idg₀ ioff₀ itg₀ iof2₀ : List ℕ)
    (hrnk : rnk₀.length = n) (hidg : idg₀.length = n) (hio : ioff₀.length = n + 1)
    (hitg : itg₀.length = W) (hio2 : iof2₀.length = n + 1) :
    hnRefine
      (junkArrayOfLen n "deg" ∗ junkArrayOfLen n "elm" ∗ junkArrayOfLen (n + 1) "bh" ∗
        junkArrayOfLen (n + W + 1) "bv" ∗ junkArrayOfLen (n + W + 1) "bn" ∗
        junkArrayOfLen n "ifl" ∗
        hnCtxt arrayAssn rnk₀ "rnk" ∗ hnCtxt arrayAssn idg₀ "idg" ∗
        hnCtxt arrayAssn ioff₀ "ioff" ∗ hnCtxt arrayAssn itg₀ "itg" ∗
        hnCtxt arrayAssn iof2₀ "iof2" ∗
        hnCtxt arrayAssn (arrOf (n + 1) O) "off" ∗ hnCtxt arrayAssn (arrOf ns T) "tgt" ∗
        hnCtxt arrayAssn (arrOf n M) "alv" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn (n + 1) "n1" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        junkCell "di" ∗ junkCell "i" ∗ junkCell "sp" ∗ junkCell "cnt" ∗ junkCell "mind" ∗
        junkCell "kmax" ∗ junkCell "os" ∗ junkCell "oi" ∗ junkCell "fi" ∗
        junkCell "zi1" ∗ junkCell "zi2" ∗ junkCell "zi3" ∗ junkCell "ci" ∗ junkCell "cu" ∗
        junkCell "dj" ∗ junkCell "dip" ∗ junkCell "djend" ∗ junkCell "dc" ∗
        junkCell "du" ∗ junkCell "dau" ∗ junkCell "dai" ∗ junkCell "d" ∗ junkCell "bhd" ∗
        junkCell "bhm" ∗ junkCell "w" ∗ junkCell "bnp" ∗ junkCell "ew" ∗ junkCell "dw" ∗
        junkCell "nm" ∗ junkCell "rw" ∗ junkCell "dk" ∗ junkCell "aw" ∗ junkCell "j" ∗
        junkCell "wp" ∗ junkCell "jend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗
        junkCell "dv" ∗ junkCell "odi" ∗ junkCell "oip" ∗
        junkCell "fai" ∗ junkCell "fri" ∗ junkCell "fj" ∗ junkCell "fip" ∗
        junkCell "fjend" ∗ junkCell "fu" ∗ junkCell "fau" ∗ junkCell "fru" ∗ junkCell "fp")
      elimSpecCom
      (hnCtxt arrayAssn (arrOf (n + 1) O) "off" ∗ hnCtxt arrayAssn (arrOf ns T) "tgt" ∗
        hnCtxt arrayAssn (arrOf n M) "alv" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn (n + 1) "n1" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        junkArrayOfLen n "deg" ∗ junkArrayOfLen n "elm" ∗ junkArrayOfLen (n + 1) "bh" ∗
        junkArrayOfLen (n + W + 1) "bv" ∗ junkArrayOfLen (n + W + 1) "bn" ∗
        junkArrayOfLen n "ifl" ∗
        junkCell "di" ∗ junkCell "i" ∗ junkCell "sp" ∗ junkCell "cnt" ∗ junkCell "mind" ∗
        junkCell "kmax" ∗ junkCell "os" ∗ junkCell "oi" ∗ junkCell "fi" ∗
        junkCell "zi1" ∗ junkCell "zi2" ∗ junkCell "zi3" ∗ junkCell "ci" ∗ junkCell "cu" ∗
        junkCell "dj" ∗ junkCell "dip" ∗ junkCell "djend" ∗ junkCell "dc" ∗
        junkCell "du" ∗ junkCell "dau" ∗ junkCell "dai" ∗ junkCell "d" ∗ junkCell "bhd" ∗
        junkCell "bhm" ∗ junkCell "w" ∗ junkCell "bnp" ∗ junkCell "ew" ∗ junkCell "dw" ∗
        junkCell "nm" ∗ junkCell "rw" ∗ junkCell "dk" ∗ junkCell "aw" ∗ junkCell "j" ∗
        junkCell "wp" ∗ junkCell "jend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗
        junkCell "dv" ∗ junkCell "odi" ∗ junkCell "oip" ∗
        junkCell "fai" ∗ junkCell "fri" ∗ junkCell "fj" ∗ junkCell "fip" ∗
        junkCell "fjend" ∗ junkCell "fu" ∗ junkCell "fau" ∗ junkCell "fru" ∗ junkCell "fp")
      ("rnk", "idg", "iof2", "ioff", "itg")
      (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn)
      (NRest.spec (OrderSynth.ElimPost n W) (fun _ => liftACost (elimSpecC n ns))) := by
  refine Lax13Proofs.Refine.Sepref.Iicf.hnRefine_junkArrayOfLen fun deg₀ hdeg => ?_
  refine hnr_scr1 fun elm₀ helm => ?_
  refine hnr_scr2 fun bh₀ hbh => ?_
  refine hnr_scr3 fun bv₀ hbv => ?_
  refine hnr_scr4 fun bn₀ hbn => ?_
  refine hnr_scr5 fun ifl₀ hifl => ?_
  exact hnRefine_ref
    (elimSpecCom_hnr hcsr hW deg₀ elm₀ bh₀ bv₀ bn₀ ifl₀ rnk₀ idg₀ ioff₀ itg₀ iof2₀
      hdeg helm hbh hbv hbn hifl hrnk hidg hio hitg hio2)
    (elimSpecProg_le hcsr hW hdeg helm hrnk hidg hbh hbv hbn hio hifl hitg hio2)

end SpecLeaf

/-! ## 7. The twice-call test, and the pinned leaf's refusal

The acceptance shape: two engine calls in `orderPhase0`'s pass-4 /
pass-12 positions — same abstract text both times, since the spec binds
no entry — with a pass after the second call reading its result (the
pass-13 shape, here through the registered copy leaf). The negative
control is the same two-call shape through the landed pinned
`OrderSynth.hnr_mop_elim`: after the first call the eleven cells hold
the first call's exit state, the second call's pinned entry cannot
match, and the tool refuses — E43 obstruction (3), compiled. -/

section TwiceCall

open Lax13Proofs.Reasoning (arrOf)
open Lax13Proofs.Refine.Sepref.Iicf (junkArrayOfLen)

-- **The leaf's result bundle is consumable** — the copy leaf reads the
-- rank component of an engine result owned as the leaf's five-way
-- product, through the T1 lazy pair split.
set_option maxHeartbeats 1000000 in
sepref_synth elimOutConsume (n : ℕ) (v : OrderSynth.ElimOut) (ord₀ : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn) v
      ("rnk", "idg", "iof2", "ioff", "itg") ∗
      hnCtxt (arrayAssn ×ₐ natAssn) (ord₀, 0) ("ord", "zz") ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗ junkCell "zu")
    _ _ ("ord", "zz") (arrayAssn ×ₐ natAssn)
    (OrderSynth.copyPass n v.1 (ord₀, 0))

-- **Residual, located and carried** (not this wave's interior): with a
-- *third* pass appended after the two calls (`copyPass src₀ → ord`, the
-- pass-13 shape), the tool's frame matcher returns no pairing for the
-- tail pass's five conjuncts even though every one has a direct
-- counterpart in the post-two-calls context — the two leaf applications
-- themselves both fire (their sub-envelopes succeed), and the same tail
-- pass at the same conjuncts synthesizes standalone (`elimOutConsume`
-- above). Matcher-level, needs `sepref_dbg` tracing at the third
-- application; parked for the member-driven interior wave.
set_option maxHeartbeats 8000000 in
sepref_synth twiceElimSynth (n ns W : ℕ) (G : SimpleGraph (Fin n)) (O T M : ℕ → ℕ)
    (hcsr : RamElim.CsrSimple G ns O T) (hW : ns ≤ W)
    (rnk₀ idg₀ ioff₀ itg₀ iof2₀ : List ℕ)
    (hrnk : rnk₀.length = n) (hidg : idg₀.length = n) (hio : ioff₀.length = n + 1)
    (hitg : itg₀.length = W) (hio2 : iof2₀.length = n + 1) :
  hnRefine
    (junkCell "zu" ∗
      junkArrayOfLen n "deg" ∗ junkArrayOfLen n "elm" ∗ junkArrayOfLen (n + 1) "bh" ∗
      junkArrayOfLen (n + W + 1) "bv" ∗ junkArrayOfLen (n + W + 1) "bn" ∗
      junkArrayOfLen n "ifl" ∗
      hnCtxt arrayAssn rnk₀ "rnk" ∗ hnCtxt arrayAssn idg₀ "idg" ∗
      hnCtxt arrayAssn ioff₀ "ioff" ∗ hnCtxt arrayAssn itg₀ "itg" ∗
      hnCtxt arrayAssn iof2₀ "iof2" ∗
      hnCtxt arrayAssn (arrOf (n + 1) O) "off" ∗ hnCtxt arrayAssn (arrOf ns T) "tgt" ∗
      hnCtxt arrayAssn (arrOf n M) "alv" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn (n + 1) "n1" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "di" ∗ junkCell "i" ∗ junkCell "sp" ∗ junkCell "cnt" ∗ junkCell "mind" ∗
      junkCell "kmax" ∗ junkCell "os" ∗ junkCell "oi" ∗ junkCell "fi" ∗
      junkCell "zi1" ∗ junkCell "zi2" ∗ junkCell "zi3" ∗ junkCell "ci" ∗ junkCell "cu" ∗
      junkCell "dj" ∗ junkCell "dip" ∗ junkCell "djend" ∗ junkCell "dc" ∗
      junkCell "du" ∗ junkCell "dau" ∗ junkCell "dai" ∗ junkCell "d" ∗ junkCell "bhd" ∗
      junkCell "bhm" ∗ junkCell "w" ∗ junkCell "bnp" ∗ junkCell "ew" ∗ junkCell "dw" ∗
      junkCell "nm" ∗ junkCell "rw" ∗ junkCell "dk" ∗ junkCell "aw" ∗ junkCell "j" ∗
      junkCell "wp" ∗ junkCell "jend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗
      junkCell "dv" ∗ junkCell "odi" ∗ junkCell "oip" ∗
      junkCell "fai" ∗ junkCell "fri" ∗ junkCell "fj" ∗ junkCell "fip" ∗
      junkCell "fjend" ∗ junkCell "fu" ∗ junkCell "fau" ∗ junkCell "fru" ∗ junkCell "fp")
    _ _ ("rnk", "idg", "iof2", "ioff", "itg")
    (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn)
    (NRest.bindT (NRest.spec (OrderSynth.ElimPost n W)
        (fun _ => liftACost (elimSpecC n ns))) fun _ =>
      (NRest.spec (OrderSynth.ElimPost n W)
        (fun _ => liftACost (elimSpecC n ns)) : NRest OrderSynth.ElimOut ECost))

-- **The program, pinned**: the spec-shaped engine twice — the same
-- `Com` both times, which is the whole point: the second call's entry
-- is the first call's exit, matched with no re-zeroing debt.
#guard twiceElimSynth_impl = elimSpecCom.seq elimSpecCom

set_option maxHeartbeats 1000000 in
set_option linter.unreachableTactic false in
set_option linter.unusedVariables false in
/-- **The refusal, compiled — E43 obstruction (3).** The same two-call
shape through the landed pinned leaf `OrderSynth.hnr_mop_elim`: the
second call's entry tuple is pinned to the first call's, the cells hold
the first call's *exit* state, and the tool cannot match. -/
example (n : ℕ) (off tgt alv deg₀ elm₀ rnk₀ idg₀ bh₀ bv₀ bn₀ : List ℕ)
    (sp₀ cnt₀ mind₀ kmax₀ : ℕ) : True := by
  fail_if_success
    (have : hnRefine
        (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
              arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn)
            (deg₀, elm₀, rnk₀, idg₀, bh₀, bv₀, bn₀, sp₀, cnt₀, mind₀, kmax₀)
            ("deg", "elm", "rnk", "idg", "bh", "bv", "bn", "sp", "cnt", "mind", "kmax") ∗
          hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
          hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
          hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
          junkCell "bhm" ∗ junkCell "w" ∗ junkCell "bnp" ∗ junkCell "ew" ∗ junkCell "dw" ∗
          junkCell "nm" ∗ junkCell "rw" ∗ junkCell "dk" ∗ junkCell "aw" ∗ junkCell "j" ∗
          junkCell "wp" ∗ junkCell "jend" ∗ junkCell "u" ∗ junkCell "au" ∗ junkCell "eu" ∗
          junkCell "dv" ∗ junkCell "du" ∗ junkCell "bhd")
        Com.skip (□ : Assn)
        ("deg", "elm", "rnk", "idg", "bh", "bv", "bn", "sp", "cnt", "mind", "kmax")
        (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
          arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn)
        (NRest.bindT (OrderSynth.mopElim n off tgt alv
            (deg₀, elm₀, rnk₀, idg₀, bh₀, bv₀, bn₀, sp₀, cnt₀, mind₀, kmax₀)) fun _ =>
          OrderSynth.mopElim n off tgt alv
            (deg₀, elm₀, rnk₀, idg₀, bh₀, bv₀, bn₀, sp₀, cnt₀, mind₀, kmax₀)) := by
      sepref)
  trivial

end TwiceCall

/-! ## 8. Program size, and the axioms -/

section Size

/-- The number of `Com` nodes in a program (wave S's measure, restated
locally per the campaign's shared-file rule). -/
def comSize : Com → ℕ
  | .skip => 1
  | .const _ _ => 1
  | .copy _ _ => 1
  | .binop _ _ _ _ => 1
  | .aget _ _ _ => 1
  | .aset _ _ _ => 1
  | .seq c d => 1 + comSize c + comSize d
  | .ite _ c d => 1 + comSize c + comSize d
  | .while _ c => 1 + comSize c

end Size

-- The engine's five passes as one program; the spec-shaped leaf adds
-- its thirteen constants, three fills and the offsets copy; the
-- twice-call is the leaf's program twice and one `seq` node.
#guard comSize degPassSynth_impl = 33
#guard comSize elimEngineCom = 333
#guard comSize elimSpecCom = 389
#guard comSize twiceElimSynth_impl = 779
#guard comSize twiceElimSynth_impl = 2 * comSize elimSpecCom + 1

#print axioms degPassSynth
#print axioms elimEngineCom_hnr
#print axioms elimSpecProg_le
#print axioms hnr_mop_elim_spec
#print axioms twiceElimSynth

end Lax3Proofs.Refine.ElimSynth7
