import Lax13Proofs.Refine.Sepref.Tool
import Lax13Proofs.Refine.Sepref.Definition

/-!
# T1 PROBE ARTIFACT — the P2/2B/D-a reproducers

Telemetry, not capital: staged reproducers for the outer-loop
translation stall found by the ND-MC rebase satellite 2B (ElimSynth).
This file is deleted or trimmed to a gate once the fix lands.

Stages:
- **R1** — a branch whose two arms both `mopAset` into an array that is
  a component of the ENCLOSING loop's state (no inner loop).
- **R2** — an inner loop sitting mid-body: ops consume its result tuple
  afterwards (no branch).
- **R3** — the full `degRowF` shape (both together), copied from
  ElimSynth's degree pass.

Every synthesis below is `#sepref_synth` (report-only).
-/

namespace Lax13Proofs.Refine.T1Probe

open Lax13Proofs.Refine.Sepref
open Lax13Proofs.Refine NRest Ir

/-! ## Local ops (the 2B restatements, verbatim) -/

noncomputable def mopSucc (m : ℕ) : NRest ℕ ECost := mopBinop .add m 1

theorem mopSucc_eq (m : ℕ) : mopSucc m = mopBinop .add m 1 := rfl

@[sepref_fr_rules]
theorem hnr_mop_succ (x z : String) (m : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn 1 z) (.binop .add x x z)
      (hnCtxt natAssn 1 z) x natAssn (mopSucc m) := by
  rw [mopSucc_eq]; exact hnr_mop_binop_self .add x z m 1

attribute [irreducible] mopSucc

noncomputable def mopKeep (m : ℕ) : NRest ℕ ECost := mopBinop .add m 0

theorem mopKeep_eq (m : ℕ) : mopKeep m = mopBinop .add m 0 := rfl

@[sepref_fr_rules]
theorem hnr_mop_keep (x z : String) (m : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn 0 z) (.binop .add x x z)
      (hnCtxt natAssn 0 z) x natAssn (mopKeep m) := by
  rw [mopKeep_eq]; exact hnr_mop_binop_self .add x z m 0

attribute [irreducible] mopKeep

/-! ## R1 — branch-aset into the enclosing loop's state array -/

def r1Bf (n : ℕ) : List ℕ × ℕ → Bool := fun s => decide (s.2 < n)

noncomputable def r1F (alv : List ℕ) : List ℕ × ℕ → NRest (List ℕ × ℕ) ECost := fun s =>
  bindT (mopAget alv s.2) fun ai =>
    bindT (irIf (decide (0 < ai)) (mopAset s.1 s.2 ai) (mopAset s.1 s.2 0)) fun D =>
      bindT (mopSucc s.2) fun i => mopPair D i

noncomputable def r1 (n : ℕ) (alv : List ℕ) (s₀ : List ℕ × ℕ) : NRest (List ℕ × ℕ) ECost :=
  irWhileIT (fun s => r1Bf n s = true → s.2 < alv.length ∧ s.2 < s.1.length) (r1Bf n)
    (r1F alv) s₀

set_option maxHeartbeats 1000000 in
#sepref_synth (n : ℕ) (alv deg₀ : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (deg₀, 0) ("deg", "i") ∗
      junkCell "ai" ∗ hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero")
    _ _ ("deg", "i") (arrayAssn ×ₐ natAssn)
    (r1 n alv (deg₀, 0))

/-! ## R2 — inner loop mid-body, result consumed afterwards -/

def r2InBf (e : ℕ) : ℕ × ℕ → Bool := fun t => decide (t.2 < e)

noncomputable def r2InF (alv : List ℕ) : ℕ × ℕ → NRest (ℕ × ℕ) ECost := fun t =>
  bindT (mopAget alv t.2) fun au =>
    bindT (irIf (decide (0 < au)) (mopSucc t.1) (mopKeep t.1)) fun c =>
      bindT (mopSucc t.2) fun j => mopPair c j

noncomputable def r2Scan (alv : List ℕ) (e : ℕ) (z : ℕ × ℕ) : NRest (ℕ × ℕ) ECost :=
  irWhileIT (fun t => r2InBf e t = true → t.2 < alv.length) (r2InBf e) (r2InF alv) z

def r2Bf (n : ℕ) : List ℕ × ℕ → Bool := fun s => decide (s.2 < n)

/-- Outer body: read a bound, run the scan, then CONSUME the scan's
result tuple (an unconditional `aset` of `r.1`, no branch), bump. -/
noncomputable def r2F (off alv : List ℕ) : List ℕ × ℕ → NRest (List ℕ × ℕ) ECost := fun s =>
  bindT (mopAget off s.2) fun e =>
    bindT (mopConstN 0) fun c0 =>
      bindT (mopConstN 0) fun j0 =>
        bindT (mopPair c0 j0) fun z0 =>
          bindT (r2Scan alv e z0) fun r =>
            bindT (mopAset s.1 s.2 r.1) fun D =>
              bindT (mopSucc s.2) fun i => mopPair D i

noncomputable def r2 (n : ℕ) (off alv : List ℕ) (s₀ : List ℕ × ℕ) :
    NRest (List ℕ × ℕ) ECost :=
  irWhileIT (fun s => r2Bf n s = true → s.2 < off.length ∧ s.2 < s.1.length) (r2Bf n)
    (r2F off alv) s₀

set_option maxHeartbeats 1000000 in
#sepref_synth (n : ℕ) (off alv deg₀ : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (deg₀, 0) ("deg", "i") ∗
      junkCell "e" ∗ junkCell "c0" ∗ junkCell "j0" ∗ junkCell "au" ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero")
    _ _ ("deg", "i") (arrayAssn ×ₐ natAssn)
    (r2 n off alv (deg₀, 0))

/-! ## R3a — R2 plus ONLY the branch: arms `r.1` vs `0` -/

noncomputable def r3aF (off alv : List ℕ) : List ℕ × ℕ → NRest (List ℕ × ℕ) ECost := fun s =>
  bindT (mopAget off s.2) fun e =>
    bindT (mopConstN 0) fun c0 =>
      bindT (mopConstN 0) fun j0 =>
        bindT (mopPair c0 j0) fun z0 =>
          bindT (r2Scan alv e z0) fun r =>
            bindT (mopAget alv s.2) fun ai =>
              bindT (irIf (decide (0 < ai)) (mopAset s.1 s.2 r.1) (mopAset s.1 s.2 0))
                fun D => bindT (mopSucc s.2) fun i => mopPair D i

noncomputable def r3a (n : ℕ) (off alv : List ℕ) (s₀ : List ℕ × ℕ) :
    NRest (List ℕ × ℕ) ECost :=
  irWhileIT (fun s => r2Bf n s = true → s.2 < off.length ∧ s.2 < s.1.length) (r2Bf n)
    (r3aF off alv) s₀

set_option maxHeartbeats 400000 in
#sepref_synth (n : ℕ) (off alv deg₀ : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (deg₀, 0) ("deg", "i") ∗
      junkCell "e" ∗ junkCell "c0" ∗ junkCell "j0" ∗ junkCell "au" ∗ junkCell "ai" ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero")
    _ _ ("deg", "i") (arrayAssn ×ₐ natAssn)
    (r3a n off alv (deg₀, 0))

/-! ## R3 — the full `degRowF` shape (2B's stalling goal, verbatim
modulo names): second offset read via a fresh binop, and the branch's
`then` arm consuming the inner result's PROJECTION `r.1` while the
`else` arm writes a constant. -/

noncomputable def r3F (off alv : List ℕ) : List ℕ × ℕ → NRest (List ℕ × ℕ) ECost := fun s =>
  bindT (mopAget off s.2) fun j0 =>
    bindT (mopBinop .add s.2 1) fun i1 =>
      bindT (mopAget off i1) fun jend =>
        bindT (mopConstN 0) fun c0 =>
          bindT (mopPair c0 j0) fun z0 =>
            bindT (r2Scan alv jend z0) fun r =>
              bindT (mopAget alv s.2) fun ai =>
                bindT (irIf (decide (0 < ai)) (mopAset s.1 s.2 r.1) (mopAset s.1 s.2 0))
                  fun D => bindT (mopSucc s.2) fun i => mopPair D i

noncomputable def r3 (n : ℕ) (off alv : List ℕ) (s₀ : List ℕ × ℕ) :
    NRest (List ℕ × ℕ) ECost :=
  irWhileIT (fun s => r2Bf n s = true → s.2 + 1 < off.length ∧ s.2 < s.1.length) (r2Bf n)
    (r3F off alv) s₀

set_option maxHeartbeats 1000000 in
sepref_synth r3Loop (n : ℕ) (off alv deg₀ : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (deg₀, 0) ("deg", "i") ∗
      junkCell "j0" ∗ junkCell "i1" ∗ junkCell "jend" ∗ junkCell "c0" ∗ junkCell "au" ∗
      junkCell "ai" ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero")
    _ _ ("deg", "i") (arrayAssn ×ₐ natAssn)
    (r3 n off alv (deg₀, 0))

#print axioms r3Loop

/- No new reasoning rule was introduced by T1/D-a or T1/D-b — both are
`rfl` respellings routed through existing congruence machinery, so the
falsification surface is the existing gates (CombRules' merge negative
controls, SepSolver's no-match controls), all of which stay compiled
under the new prepare set; the full-package build is the check. The
positive pins above (R1, R2, R3a as reports; `r3Loop` compiled) are the
D-a acceptance. -/

/-! ## W11 — the wide-state measure (scope item 5)

ElimSynth's elimination loop carries 7 arrays + 4 scalars; this is that
width as a synthetic loop (body: one read, one cross-array write, one
counter bump, then the 10-`mopPair` state rebuild). What is measured is
whether the 11-deep `prodAssn` chain breaks the matcher or merely
crawls. -/

abbrev W11St := List ℕ × List ℕ × List ℕ × List ℕ × List ℕ × List ℕ × List ℕ × ℕ × ℕ × ℕ × ℕ

def w11K1 (s : W11St) : ℕ := s.2.2.2.2.2.2.2.1

def w11Bf (n : ℕ) : W11St → Bool := fun s => decide (w11K1 s < n)

noncomputable def w11F : W11St → NRest W11St ECost := fun s =>
  bindT (mopAget s.1 (w11K1 s)) fun v =>
    bindT (mopAset s.2.1 (w11K1 s) v) fun b2 =>
      bindT (mopSucc (w11K1 s)) fun k1 =>
        bindT (mopPair s.2.2.2.2.2.2.2.2.2.1 s.2.2.2.2.2.2.2.2.2.2) fun p34 =>
          bindT (mopPair s.2.2.2.2.2.2.2.2.1 p34) fun p234 =>
            bindT (mopPair k1 p234) fun pk =>
              bindT (mopPair s.2.2.2.2.2.2.1 pk) fun p7 =>
                bindT (mopPair s.2.2.2.2.2.1 p7) fun p6 =>
                  bindT (mopPair s.2.2.2.2.1 p6) fun p5 =>
                    bindT (mopPair s.2.2.2.1 p5) fun p4 =>
                      bindT (mopPair s.2.2.1 p4) fun p3 =>
                        bindT (mopPair b2 p3) fun p2 =>
                          mopPair s.1 p2

noncomputable def w11 (n : ℕ) (s₀ : W11St) : NRest W11St ECost :=
  irWhileIT (fun s => w11Bf n s = true →
      w11K1 s < s.1.length ∧ w11K1 s < s.2.1.length) (w11Bf n) w11F s₀

set_option maxHeartbeats 2000000 in
#sepref_synth (n : ℕ) (a1 a2 a3 a4 a5 a6 a7 : List ℕ) (k2 k3 k4 : ℕ) :
  hnRefine
    (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
        arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn)
      (a1, a2, a3, a4, a5, a6, a7, 0, k2, k3, k4)
      ("a1", "a2", "a3", "a4", "a5", "a6", "a7", "k1", "k2", "k3", "k4") ∗
      junkCell "v" ∗ hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one")
    _ _ ("a1", "a2", "a3", "a4", "a5", "a6", "a7", "k1", "k2", "k3", "k4")
    (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
      arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn)
    (w11 n (a1, a2, a3, a4, a5, a6, a7, 0, k2, k3, k4))

end Lax13Proofs.Refine.T1Probe
