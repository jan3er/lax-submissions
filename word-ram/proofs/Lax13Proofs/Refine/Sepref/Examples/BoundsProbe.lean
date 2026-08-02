import Lax13Proofs.Refine.Sepref.Bounds
import Lax13Proofs.Refine.Examples.BfsQ

/-!
# The T2 probe: a two-level bounds pass, and the pinned bind

ND-MC rebase tool wave T2, acceptance file. Two exercises, both on
word-ram-local replicas so that no ND-MC file is touched:

**§1–§3 — the counting-pass shape, bounded through both levels.**
`AugmentSynth` §4's `cntPass` — outer loop over vertices, inner slot
scan *in the middle* of the body, the scan's result feeding the
operations after it — is the shape every two-level engine pass has,
and the one no `BRefine` derivation could reach before T2/D-b
(AugmentSynth §10 gap 3, ElimSynth3 §5 E3). The synthesized `Com` is
replicated here cell-for-cell (renamed `p*`), and its bounds pass is
derived end to end: the inner body and the mask-shape replica are
`brefine`-emitted (T2/D-d), the inner loop enters through
`BRefine.while_seq` (T2/D-b), the scratch cells are `junkCell`
conjuncts consumed directly by the junk rules (T2/D-c) — no tuple
existential anywhere — and the whole judgment is cashed to an
`Ir.bpre` witness at a concrete store, cross-checked by running the
program on the IR's own evaluator.

**The amortized budget.** The counting pass increments a cell per
slot, so no per-cell bound is loop-invariant; what is invariant is the
*budget* `O[k] + (slots still to scan) ≤ W` — one clause, threaded
through both levels (outer: slots of the remaining rows,
`doff[n] - doff[i]`; inner: `doff[n] - j`), and the `pc := pc + 1`
creation site spends one unit of it. This is the P0.2 prediction at
the two-level shape: ≈ 1 side condition per creation site, each
discharged from the abstract invariant, 0 `Ir.State` predicates.

**§4 — the pinned bind (T2/D-e acceptance).** The R2D/D-b reproducer,
word-ram-local: a leaf rule demanding a *literal* `0` in a cell, bound
behind an in-place zeroing op. Before the translate fix this stalled
("no rule translates … under … `hnCtxt natAssn a✝ "phd"`"); now the
`bind_ref_tag` constant normalization pins the bound value and the
leaf fires. The emitted `Com` is `#guard`-pinned.

**Measurement (T2/D-d, the DB emission gap).** The mask-pass body —
`AugmentSynth.alv_body_brefine`, 27 hand lines of
`BRefine.perm/frame/pre_pure` — is re-done here as `pm_body` in **9**
lines (−67%); the seven-op prefix-shape class (`pfΓ`'s `pstep_*`
family, ~150 lines per engine) reduces the same way: each op is one
database hit, and the only hand lines left are the invariant facts.
-/

namespace Lax13Proofs.Refine.Sepref.BoundsProbe

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Sepref.WordSpike
open Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax13Proofs.Refine.BfsQ (get!_set)
open Lax13Proofs.Imp (Bop)

/-! ## 1. The counting-pass shape, replicated

`AugmentSynth.cntPassSynth_impl`, cell-for-cell at `p*` names: the row
bounds are loaded (`pjo`, `pend`), the slot scan bumps `poff[dtg[j]+1]`,
the vertex counter advances. -/

/-- The inner slot scan's body. -/
def pbInnerBody : Com :=
  (Com.aget "pu" "ptg" "pjo").seq
    ((Com.binop .add "pup" "pu" "pone").seq
      ((Com.aget "pc" "poff" "pup").seq
        ((Com.binop .add "pc" "pc" "pone").seq
          ((Com.aset "poff" "pup" "pc").seq
            ((Com.binop .add "pjo" "pjo" "pone").seq Com.skip)))))

/-- The outer body: load the row bounds, scan, advance. -/
def pbBody : Com :=
  (Com.aget "pjo" "pdoff" "pi").seq
    ((Com.binop .add "pip" "pi" "pone").seq
      ((Com.aget "pend" "pdoff" "pip").seq
        (Com.skip.seq
          ((Com.while (Cond.lt (Operand.cell "pjo") (Operand.cell "pend"))
              pbInnerBody).seq
            ((Com.binop .add "pi" "pi" "pone").seq Com.skip)))))

/-- The whole two-level pass. -/
def pbCom : Com :=
  Com.while (Cond.lt (Operand.cell "pi") (Operand.cell "pn")) pbBody

/-! ## 2. The bounds pass -/

/-- The block structure's shape, plus the word budget: `W` bounds every
count plus the slots still to scan, and the small quantities fit. -/
def PbShape (n W B : ℕ) (doff dtg : List ℕ) : Prop :=
  doff.length = n + 1 ∧ (∀ j, j ≤ n → doff[j]! ≤ doff[n]!) ∧
    (∀ i, i < n → doff[i]! ≤ doff[i + 1]!) ∧ doff[n]! ≤ dtg.length ∧
    (∀ p, p < dtg.length → dtg[p]! < n) ∧ n + 1 < B ∧ W < B ∧ dtg.length < B

/-- The outer loop's assertion: the count array and the vertex counter,
the block structure, the constants — and every scratch cell as a
**junk conjunct** (T2/D-c; no tuple existential). -/
def pbΓ (n : ℕ) (doff dtg : List ℕ) : List ℕ × ℕ → Assn := fun t =>
  arrayAssn t.1 "poff" ∗ natAssn t.2 "pi" ∗ arrayAssn doff "pdoff" ∗
    arrayAssn dtg "ptg" ∗ natAssn n "pn" ∗ natAssn 1 "pone" ∗ junkCell "pjo" ∗
    junkCell "pip" ∗ junkCell "pend" ∗ junkCell "pu" ∗ junkCell "pup" ∗ junkCell "pc"

/-- The outer invariant: the amortized budget, at the remaining rows. -/
def pbI (n W : ℕ) (doff : List ℕ) : List ℕ × ℕ → Prop := fun t =>
  t.2 ≤ n ∧ t.1.length = n + 1 ∧
    ∀ k, k < n + 1 → t.1[k]! + (doff[n]! - doff[t.2]!) ≤ W

/-- The inner loop's assertion: its own state (`poff`, `pjo`), the row
end it reads, the constants, and its scratch as junk. -/
def pbInΓ (n : ℕ) (doff dtg : List ℕ) (jend : ℕ) : List ℕ × ℕ → Assn := fun u =>
  arrayAssn u.1 "poff" ∗ natAssn u.2 "pjo" ∗ natAssn jend "pend" ∗
    arrayAssn doff "pdoff" ∗ arrayAssn dtg "ptg" ∗ natAssn n "pn" ∗
    natAssn 1 "pone" ∗ junkCell "pu" ∗ junkCell "pup" ∗ junkCell "pc"

/-- The inner invariant: the same budget, at the remaining slots. -/
def pbInI (n W jend : ℕ) (doff dtg : List ℕ) : List ℕ × ℕ → Prop := fun u =>
  u.2 ≤ jend ∧ jend ≤ dtg.length ∧ jend ≤ doff[n]! ∧ u.1.length = n + 1 ∧
    ∀ k, k < n + 1 → u.1[k]! + (doff[n]! - u.2) ≤ W

/-! ### The guard agreements (one lemma per loop, `BRefine.while_*`'s
`hg`) -/

theorem pbΓ_pi {n : ℕ} {doff dtg : List ℕ} {t : List ℕ × ℕ} {F : Assn} {s : Ir.State}
    {cr : ECost} (h : irSTATE (pbΓ n doff dtg t ∗ F) (s, cr)) : s.vars "pi" = some t.2 :=
  natAssn_vars (F := arrayAssn t.1 "poff" ∗ arrayAssn doff "pdoff" ∗
    arrayAssn dtg "ptg" ∗ natAssn n "pn" ∗ natAssn 1 "pone" ∗ junkCell "pjo" ∗
    junkCell "pip" ∗ junkCell "pend" ∗ junkCell "pu" ∗ junkCell "pup" ∗
    junkCell "pc" ∗ F) (irSTATE_cong (by simp only [pbΓ]; ac_rfl) h)

theorem pbΓ_pn {n : ℕ} {doff dtg : List ℕ} {t : List ℕ × ℕ} {F : Assn} {s : Ir.State}
    {cr : ECost} (h : irSTATE (pbΓ n doff dtg t ∗ F) (s, cr)) : s.vars "pn" = some n :=
  natAssn_vars (F := arrayAssn t.1 "poff" ∗ natAssn t.2 "pi" ∗
    arrayAssn doff "pdoff" ∗ arrayAssn dtg "ptg" ∗ natAssn 1 "pone" ∗ junkCell "pjo" ∗
    junkCell "pip" ∗ junkCell "pend" ∗ junkCell "pu" ∗ junkCell "pup" ∗
    junkCell "pc" ∗ F) (irSTATE_cong (by simp only [pbΓ]; ac_rfl) h)

theorem pb_guard {n W : ℕ} {doff dtg : List ℕ} (t : List ℕ × ℕ) (F : Assn)
    (s : Ir.State) (cr : ECost) (r : Bool) (_ : pbI n W doff t)
    (hs : irSTATE (pbΓ n doff dtg t ∗ F) (s, cr))
    (hev : (Cond.lt (Operand.cell "pi") (Operand.cell "pn")).eval s = some r) :
    decide (t.2 < n) = r := by
  obtain ⟨a, b, ha, hb, rfl⟩ := WordSpike.BoundsGate.eval_lt_cells hev
  rw [pbΓ_pi hs] at ha
  rw [pbΓ_pn hs] at hb
  rw [Option.some.inj ha, Option.some.inj hb]

theorem pbInΓ_pjo {n jend : ℕ} {doff dtg : List ℕ} {u : List ℕ × ℕ} {F : Assn}
    {s : Ir.State} {cr : ECost} (h : irSTATE (pbInΓ n doff dtg jend u ∗ F) (s, cr)) :
    s.vars "pjo" = some u.2 :=
  natAssn_vars (F := arrayAssn u.1 "poff" ∗ natAssn jend "pend" ∗
    arrayAssn doff "pdoff" ∗ arrayAssn dtg "ptg" ∗ natAssn n "pn" ∗ natAssn 1 "pone" ∗
    junkCell "pu" ∗ junkCell "pup" ∗ junkCell "pc" ∗ F)
    (irSTATE_cong (by simp only [pbInΓ]; ac_rfl) h)

theorem pbInΓ_pend {n jend : ℕ} {doff dtg : List ℕ} {u : List ℕ × ℕ} {F : Assn}
    {s : Ir.State} {cr : ECost} (h : irSTATE (pbInΓ n doff dtg jend u ∗ F) (s, cr)) :
    s.vars "pend" = some jend :=
  natAssn_vars (F := arrayAssn u.1 "poff" ∗ natAssn u.2 "pjo" ∗
    arrayAssn doff "pdoff" ∗ arrayAssn dtg "ptg" ∗ natAssn n "pn" ∗ natAssn 1 "pone" ∗
    junkCell "pu" ∗ junkCell "pup" ∗ junkCell "pc" ∗ F)
    (irSTATE_cong (by simp only [pbInΓ]; ac_rfl) h)

theorem pbIn_guard {n W jend : ℕ} {doff dtg : List ℕ} (u : List ℕ × ℕ) (F : Assn)
    (s : Ir.State) (cr : ECost) (r : Bool) (_ : pbInI n W jend doff dtg u)
    (hs : irSTATE (pbInΓ n doff dtg jend u ∗ F) (s, cr))
    (hev : (Cond.lt (Operand.cell "pjo") (Operand.cell "pend")).eval s = some r) :
    decide (u.2 < jend) = r := by
  obtain ⟨a, b, ha, hb, rfl⟩ := WordSpike.BoundsGate.eval_lt_cells hev
  rw [pbInΓ_pjo hs] at ha
  rw [pbInΓ_pend hs] at hb
  rw [Option.some.inj ha, Option.some.inj hb]

/-! ### The inner body, driver-emitted

Six operations, three creation sites; the three `have`s below are the
side conditions, each discharged from the invariant's budget or the
shape, and `brefine` picks them up by `assumption`. The close weakens
the scratch back to junk (`fri`, whose rule base already carries
`natAssn_entails_junkCell`) and re-enters the loop assertion. -/

theorem pb_inner_body {B n W jend : ℕ} {doff dtg : List ℕ}
    (hsh : PbShape n W B doff dtg) (u : List ℕ × ℕ)
    (hI : pbInI n W jend doff dtg u) (hbf : decide (u.2 < jend) = true) :
    BRefine B (pbInΓ n doff dtg jend u) pbInnerBody
      (LoopAssn (pbInI n W jend doff dtg) (pbInΓ n doff dtg jend)) := by
  obtain ⟨hle, hjt, hjd, hlen, hbud⟩ := hI
  obtain ⟨hdl, hmn, hm1, hdt, hlt, hnB, hWB, htB⟩ := hsh
  have hult : u.2 < jend := of_decide_eq_true hbf
  have hut : u.2 < dtg.length := by omega
  have hdu : dtg[u.2]! < n := hlt u.2 hut
  have h1 : dtg[u.2]! + 1 < B := by omega
  have h2 : u.1[dtg[u.2]! + 1]! + 1 < B := by
    have := hbud (dtg[u.2]! + 1) (by omega)
    omega
  have h3 : u.2 + 1 < B := by omega
  simp only [pbInnerBody, pbInΓ]
  brefine
  refine entails_trans ?_ (loopAssn_intro
    (t := (u.1.set (Bop.apply .add dtg[u.2]! 1)
        (Bop.apply .add (u.1[Bop.apply .add dtg[u.2]! 1]!) 1),
      Bop.apply .add u.2 1)) ?_)
  · show _ ⊢ pbInΓ n doff dtg jend _
    simp only [pbInΓ]
    fri
  · simp only [pbInI, Bop.apply_add]
    refine ⟨by omega, hjt, hjd, by simp [hlen], ?_⟩
    intro k hk
    have hkk : dtg[u.2]! + 1 < u.1.length := by omega
    rw [get!_set _ _ _ _ hkk]
    have hbk := hbud k hk
    have hbkk := hbud (dtg[u.2]! + 1) (by omega)
    by_cases hke : k = dtg[u.2]! + 1
    · rw [if_pos hke]
      omega
    · rw [if_neg hke]
      omega

/-! ### The outer body: the driver up to the loop, `while_seq` through
it (T2/D-b), the driver after it. -/

theorem pb_body {B n W : ℕ} {doff dtg : List ℕ} (hsh : PbShape n W B doff dtg)
    (t : List ℕ × ℕ) (hI : pbI n W doff t) (hbf : decide (t.2 < n) = true) :
    BRefine B (pbΓ n doff dtg t) pbBody (LoopAssn (pbI n W doff) (pbΓ n doff dtg)) := by
  obtain ⟨hin, hlen, hbud⟩ := hI
  obtain ⟨hdl, hmn, hm1, hdt, hlt, hnB, hWB, htB⟩ := id hsh
  have hilt : t.2 < n := of_decide_eq_true hbf
  have hip : t.2 + 1 < B := by omega
  simp only [pbBody, pbΓ]
  brefine
  refine BRefine.while_seq (bf := fun u : List ℕ × ℕ =>
      decide (u.2 < doff[Bop.apply .add t.2 1]!))
    (I := pbInI n W (doff[Bop.apply .add t.2 1]!) doff dtg)
    (Γ := pbInΓ n doff dtg (doff[Bop.apply .add t.2 1]!))
    (D := natAssn (Bop.apply .add t.2 1) "pip" ∗ natAssn t.2 "pi")
    WordSpike.BoundsGate.litLt_lt_cells (fun u F s cr r hIu hs hev => pbIn_guard u F s cr r hIu hs hev)
    (fun u hIu hbfu => pb_inner_body hsh u hIu hbfu) ?_ ?_
  · -- entering the scan: the outer budget is the row-entry budget
    refine entails_trans (entails_of_eq (?_ : _ = pbInΓ n doff dtg
        (doff[Bop.apply .add t.2 1]!) (t.1, doff[t.2]!) ∗
        (natAssn (Bop.apply .add t.2 1) "pip" ∗ natAssn t.2 "pi"))) ?_
    · simp only [pbInΓ]
      ac_rfl
    · refine sepConj_mono_left (loopAssn_intro ?_)
      have hmono : doff[t.2]! ≤ doff[t.2 + 1]! := hm1 t.2 hilt
      have htop : doff[t.2 + 1]! ≤ doff[n]! := hmn (t.2 + 1) (by omega)
      refine ⟨?_, ?_, ?_, hlen, ?_⟩
      · show doff[t.2]! ≤ doff[Bop.apply .add t.2 1]!
        rw [Bop.apply_add]
        exact hmono
      · show doff[Bop.apply .add t.2 1]! ≤ dtg.length
        rw [Bop.apply_add]
        omega
      · show doff[Bop.apply .add t.2 1]! ≤ doff[n]!
        rw [Bop.apply_add]
        exact htop
      · exact fun k hk => hbud k hk
  · -- after the scan: the exit state's budget is the next row's
    rintro u ⟨hle, hjt, hjd, hlen', hbud'⟩ hbfu
    have hend : u.2 = doff[Bop.apply .add t.2 1]! := by
      have := of_decide_eq_false hbfu
      omega
    have hip' : Bop.apply .add t.2 1 < B := by rw [Bop.apply_add]; omega
    simp only [pbInΓ]
    brefine
    refine entails_trans ?_ (loopAssn_intro
      (t := (u.1, Bop.apply .add t.2 1)) ?_)
    · show _ ⊢ pbΓ n doff dtg _
      simp only [pbΓ]
      fri
    · refine ⟨by rw [Bop.apply_add]; omega, hlen', ?_⟩
      intro k hk
      have := hbud' k hk
      rw [← hend]
      omega

/-- **The two-level bounds pass** (T2/D-b end to end): the counting-pass
shape, at its own loop assertion. -/
theorem pb_brefine {B n W : ℕ} {doff dtg : List ℕ} (hsh : PbShape n W B doff dtg) :
    BRefine B (LoopAssn (pbI n W doff) (pbΓ n doff dtg)) pbCom
      (LoopAssn (pbI n W doff) (pbΓ n doff dtg)) := by
  rw [pbCom]
  exact BRefine.while_guard (bf := fun t : List ℕ × ℕ => decide (t.2 < n))
    WordSpike.BoundsGate.litLt_lt_cells
    (fun t F s cr r hIt hs hev => pb_guard t F s cr r hIt hs hev)
    (fun t hIt hbf => pb_body hsh t hIt hbf)
    (fun t hIt _ => loopAssn_intro hIt)

/-! ## 3. The end-to-end gate: a concrete store

`n = 2`, `doff = [0,1,2]`, `dtg = [1,0]`, `W = 2`, `B = 100`: the
judgment is cashed to `Ir.bpre` at the store, the program is *run* by
the IR's own evaluator against the expected counts, and the negative
control pins that it really counts. -/

section Gate

def pbState : Ir.State :=
  Ir.State.ofPairs
    [("pi", 0), ("pn", 2), ("pone", 1), ("pjo", 0), ("pip", 0), ("pend", 0),
      ("pu", 0), ("pup", 0), ("pc", 0)]
    [("poff", [0, 0, 0]), ("pdoff", [0, 1, 2]), ("ptg", [1, 0])]

def pbOwn : Assn :=
  arrayAssn [0, 0, 0] "poff" ∗ natAssn 0 "pi" ∗ arrayAssn [0, 1, 2] "pdoff" ∗
    arrayAssn [1, 0] "ptg" ∗ natAssn 2 "pn" ∗ natAssn 1 "pone" ∗ natAssn 0 "pjo" ∗
    natAssn 0 "pip" ∗ natAssn 0 "pend" ∗ natAssn 0 "pu" ∗ natAssn 0 "pup" ∗
    natAssn 0 "pc"

def pbFrame : Assn :=
  EXACT ((vcells pbState |>.erase "pi" |>.erase "pn" |>.erase "pone" |>.erase "pjo"
      |>.erase "pip" |>.erase "pend" |>.erase "pu" |>.erase "pup" |>.erase "pc",
    acells pbState |>.erase "poff" |>.erase "pdoff" |>.erase "ptg",
    hcells pbState), 0)

theorem pb_shape : PbShape 2 2 100 [0, 1, 2] [1, 0] := by
  unfold PbShape
  decide

theorem pbOwn_holds : irSTATE (pbOwn ∗ pbFrame) (pbState, 0) := by
  show (pbOwn ∗ pbFrame) ((vcells pbState, acells pbState, hcells pbState), 0)
  simp only [pbOwn, natAssn_def, arrayAssn_def, sepConj_assoc]
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  exact Ir.ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩

theorem pbState_bound : Ir.StateBound 100 pbState :=
  Codegen.stateBound_ofPairs (by decide) (by decide)

theorem pb_entry : pbOwn ⊢ LoopAssn (pbI 2 2 [0, 1, 2]) (pbΓ 2 [0, 1, 2] [1, 0]) := by
  refine entails_trans ?_ (loopAssn_intro (t := ([0, 0, 0], 0)) ?_)
  · show _ ⊢ pbΓ 2 [0, 1, 2] [1, 0] ([0, 0, 0], 0)
    simp only [pbOwn, pbΓ]
    fri
  · exact ⟨by omega, by decide, by decide⟩

/-- **The bounds witness, through two loop levels, at a concrete
store.** -/
theorem pb_bpre : Ir.bpre 100 pbCom (fun _ => True) pbState :=
  bpre_of_BRefine (F := pbFrame) (pb_brefine pb_shape)
    (start_entailsE pbOwn_holds (sepConj_mono_left pb_entry)) pbState_bound

/-- The program, run: `dtg = [1,0]` has one slot naming `1` and one
naming `0`, so the counts land at `poff = [0,1,1]`. -/
def gPb : Option (List ℕ) :=
  (Ir.evalFuel 400 pbCom pbState).bind fun p => p.1.arrs "poff"

#guard gPb = some [0, 1, 1]

/--
error: Expression
  decide (gPb = some [0, 0, 0])
did not evaluate to `true`
-/
#guard_msgs in
#guard gPb = some [0, 0, 0]

/-! ### Axioms -/

/-- info: 'Lax13Proofs.Refine.Sepref.BoundsProbe.pb_bpre' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms pb_bpre

end Gate

/-! ## 3b. The mask-pass shape, driver-emitted (the measurement)

`AugmentSynth.alv_body_brefine` — the cheapest existing consumer
shape — is 27 hand lines (two `BRefine.perm` blocks with spelled-out
permutations, one `pre_pure`, one close). The same body at the same
assertion shape, `brefine`-emitted: **9 lines**, all of them invariant
content. -/

section Mask

def pmΓ (n : ℕ) : List ℕ × ℕ → Assn := fun t =>
  arrayAssn t.1 "pmv" ∗ natAssn t.2 "pmi" ∗ natAssn n "pn" ∗ natAssn 1 "pone"

def pmI (n : ℕ) : List ℕ × ℕ → Prop := fun t => t.2 ≤ n

def pmBody : Com :=
  (Com.aset "pmv" "pmi" "pone").seq
    ((Com.binop .add "pmi" "pmi" "pone").seq Com.skip)

theorem pm_body {B n : ℕ} (hnB : n < B) (t : List ℕ × ℕ) (_ : pmI n t)
    (hbf : decide (t.2 < n) = true) :
    BRefine B (pmΓ n t) pmBody (LoopAssn (pmI n) (pmΓ n)) := by
  have hlt : t.2 < n := of_decide_eq_true hbf
  have hb : t.2 + 1 < B := by omega
  simp only [pmBody, pmΓ]
  brefine
  refine entails_trans (entails_of_eq
    (?_ : _ = pmΓ n (t.1.set t.2 1, Bop.apply .add t.2 1))) (loopAssn_intro ?_)
  · simp only [pmΓ]
    ac_rfl
  · simp only [pmI, Bop.apply_add]
    omega

end Mask

/-! ## 4. The pinned bind (T2/D-e acceptance)

The R2D/D-b reproducer, word-ram-local: `mopZeroP` zeroes a cell in
place (`irreducible`, so only all-transparency unfolding sees its
constant), and the leaf's rule demands the *literal* `0` in that cell.
Binding the two used to stall at an opaque bound value; the constant
normalization pins it, and the leaf fires. -/

section Pin

/-- `x := x * z` with `z` holding zero: in-place zeroing (the
`CoverSynth.mopZeroIn` shape, replicated). -/
noncomputable def mopZeroP (m : ℕ) : NRest ℕ ECost := mopBinop .mul m 0

theorem mopZeroP_eq (m : ℕ) : mopZeroP m = mopBinop .mul m 0 := rfl

@[sepref_fr_rules]
theorem hnr_mop_zeroP (x z : String) (m : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn 0 z) (.binop .mul x x z)
      (hnCtxt natAssn 0 z) x natAssn (mopZeroP m) := by
  rw [mopZeroP_eq]; exact hnr_mop_binop_self .mul x z m 0

attribute [irreducible] mopZeroP

/-- The leaf: its rule demands `hnCtxt natAssn 0 "phd"` — a literal
zero, as `ScatterSynth.hnr_mop_bfs`'s entry conditions do. -/
noncomputable def mopLeafP : NRest ℕ ECost := mopCopy 0

theorem mopLeafP_eq : mopLeafP = mopCopy 0 := rfl

@[sepref_fr_rules]
theorem hnr_mop_leafP :
    hnRefine (junkCell "pt" ∗ hnCtxt natAssn 0 "phd") (.copy "pt" "phd")
      (hnCtxt natAssn 0 "phd") "pt" natAssn mopLeafP := by
  rw [mopLeafP_eq]; exact hnr_mop_copy "pt" "phd" 0

attribute [irreducible] mopLeafP

set_option maxHeartbeats 400000 in
sepref_synth pinProbe (h₀ : ℕ) :
  hnRefine (hnCtxt natAssn h₀ "phd" ∗ hnCtxt natAssn 0 "pz" ∗ junkCell "pt")
    _ _ "pt" natAssn (NRest.bindT (mopZeroP h₀) fun _ => mopLeafP)

-- The emitted program, pinned: the zeroing, then the leaf — which can
-- only have fired at the *pinned* value of the bind.
#guard pinProbe_impl = (Com.binop .mul "phd" "phd" "pz").seq (Com.copy "pt" "phd")

end Pin

end Lax13Proofs.Refine.Sepref.BoundsProbe
