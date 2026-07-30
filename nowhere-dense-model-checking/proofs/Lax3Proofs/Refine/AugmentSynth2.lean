import Lax3Proofs.Refine.AugmentSynth

/-!
# ND-MC rebase P2 / wave 2C′ — the out-fill, derived

Satellite 2C (`Refine/AugmentSynth.lean`) derived three of the
augmentation round's passes — the counting pass, the prefix pass and the
mask — and left the two that *write* as computable twins
(`Refine/AugmentTwins.lean`). This file derives the first of those, the
**out-fill** (`RamAugment.outFill`), through the tower: abstract `NRest`
program, correctness, cost, synthesized `Com`, gate.

With it, **phase 1 of the round — `RamAugment.outPass`, the counting
sort of the in-lists — is complete through the tower**: §2.1 runs the
three synthesized programs one after another and gets `RamAugment.Demo`'s
own out-lists.

## Scope (wave 2E, mid-wave)

The wave's other two items — the fraternity build and the whole-round
assembly — were **cancelled mid-wave** when wave 2E established that at
`R = 0` the driver's augmentation fold is `Com.skip`: the round never
executes on the C0 path, `RamDriverAugment.implements` stays as retained
capital consumed by the frozen driver assembly, and a tower re-derivation
of the round has no C0 consumer. What is here is therefore *capital for a
future `R > 0` wave*, and §5 says exactly what such a wave would still
need. Nothing downstream depends on this file.

## What the correctness statement is

Each pass is proved to compute its **twin** — the ordinary `List`
function `AugmentTwins` differential-tests against `RamAugment.Demo`'s
own reported numbers and against `TgtCoupling`'s K₁,₄ witness. The
refinement carries the fold equality (§0) and the arithmetic content
lives with the twin, where there is no cost algebra in the way. On top of
it `filPass_spec` proves the fill's own non-obvious fact — the pointer of
`u` advances by exactly the out-degree of `u`, `bumpCnt dtg 0 m (u+1)`,
which is the *same* count `AugmentSynth.cntPass_spec` leaves in `ooff`.
That coupling is what makes the fill safe: it is the only reason
`otg[ofl[u]] := i` is in range.
-/

namespace Lax3Proofs.Refine.AugmentSynth2

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Sepref.WordSpike
open Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest Lax13Proofs.Refine.Codegen
open Lax13Proofs.Refine.BfsQ (cu iter irWhile_exit get!_set liftACost_cu)
open Lax3Proofs.Refine.AugmentTwins
open Lax3Proofs.Refine.AugmentSynth

/-! ## 0. The twins' arithmetic

Every pass below is proved to compute its twin — the `List` function
`Refine/AugmentTwins.lean` differential-tests against `RamAugment.Demo`
and against `TgtCoupling`'s K₁,₄ witness. That is the *whole* of the
correctness statement of a `foldl`: the refinement carries the fold
equality and nothing else, and every arithmetic fact a pass needs (an
index is in range, a pointer has not run off its block) is proved once,
here, about the twin — where there is no cost algebra in the way.

The two block-structure facts the section needs are `slotsIn`'s own
recursion and `AugmentSynth.bumpCnt`, the count of slots naming a
vertex, which is landed capital (§4.2 there). -/

section Twins

/-- The slots of a block, one more. -/
theorem slotsIn_succ {a b : ℕ} (h : a ≤ b) : slotsIn a (b + 1) = slotsIn a b ++ [b] := by
  simp only [slotsIn, show b + 1 - a = (b - a) + 1 by omega, List.range_succ,
    List.map_append, List.map_cons, List.map_nil]
  rw [show a + (b - a) = b by omega]

theorem slotsIn_self (a : ℕ) : slotsIn a a = [] := by simp [slotsIn]

/-- The fill's step on the pointer array alone: the slot `p` names a
vertex, whose fill pointer moves one on. -/
def gStep (dtg : List ℕ) (F : List ℕ) (p : ℕ) : List ℕ :=
  F.set dtg[p]! (F[dtg[p]!]! + 1)

/-- The fill's step on the twin's state, exactly `AugmentTwins`'s. -/
def fStep (dtg : List ℕ) (i : ℕ) (s : List ℕ × List ℕ) (p : ℕ) : List ℕ × List ℕ :=
  (s.1.set s.2[dtg[p]!]! i, gStep dtg s.2 p)

/-- One vertex's turn. -/
def fRow (doff dtg : List ℕ) (s : List ℕ × List ℕ) (i : ℕ) : List ℕ × List ℕ :=
  (slotsIn doff[i]! doff[i + 1]!).foldl (fStep dtg i) s

/-- …and the whole fill, which is `AugmentTwins.outFillTw` verbatim. -/
def fFold (n : ℕ) (doff dtg : List ℕ) (s : List ℕ × List ℕ) : List ℕ × List ℕ :=
  (List.range n).foldl (fRow doff dtg) s

theorem fFold_eq_outFillTw (n m : ℕ) (doff dtg ofl₀ : List ℕ) :
    fFold n doff dtg (List.replicate m 0, ofl₀) = outFillTw n m doff dtg ofl₀ := rfl

/-- The pointers do not see the target array. -/
theorem foldl_fStep_snd (dtg : List ℕ) (i : ℕ) (l : List ℕ) (Y : List ℕ × List ℕ) :
    (l.foldl (fStep dtg i) Y).2 = l.foldl (gStep dtg) Y.2 := by
  induction l generalizing Y with
  | nil => rfl
  | cons p l ih => simpa [fStep] using ih (fStep dtg i Y p)

theorem foldl_fStep_fst_len (dtg : List ℕ) (i : ℕ) (l : List ℕ) (Y : List ℕ × List ℕ) :
    (l.foldl (fStep dtg i) Y).1.length = Y.1.length := by
  induction l generalizing Y with
  | nil => rfl
  | cons p l ih => simpa [fStep] using ih (fStep dtg i Y p)

theorem foldl_gStep_len (dtg : List ℕ) (l : List ℕ) (F : List ℕ) :
    (l.foldl (gStep dtg) F).length = F.length := by
  induction l generalizing F with
  | nil => rfl
  | cons p l ih => simpa [gStep] using ih (F.set dtg[p]! (F[dtg[p]!]! + 1))

/-- **What the fill pointers carry.** After the slots `[0, b)` have been
filled, the pointer of `u` has moved on by the number of those slots
that name `u` — `bumpCnt dtg 0 b (u+1)`, the out-degree fact of
`AugmentSynth` §4.2 read at the other end. -/
theorem foldl_gStep_get {n : ℕ} {dtg : List ℕ} {base : ℕ → ℕ} :
    ∀ {a b : ℕ} {F : List ℕ}, a ≤ b → F.length = n →
      (∀ p, p < b → dtg[p]! < n) →
      (∀ u, u < n → F[u]! = base u + bumpCnt dtg 0 a (u + 1)) →
      ∀ u, u < n → ((slotsIn a b).foldl (gStep dtg) F)[u]! = base u + bumpCnt dtg 0 b (u + 1) := by
  intro a b
  induction b with
  | zero =>
    intro F hab _ _ hF u hu
    obtain rfl : a = 0 := by omega
    rw [slotsIn_self]
    exact hF u hu
  | succ b ih =>
    intro F hab hlen hlt hF u hu
    rcases Nat.lt_or_ge b a with hba | hba
    · obtain rfl : a = b + 1 := by omega
      rw [slotsIn_self]
      exact hF u hu
    · rw [slotsIn_succ hba, List.foldl_append]
      have hkey := ih hba hlen (fun p hp => hlt p (by omega)) hF
      set F' := (slotsIn a b).foldl (gStep dtg) F with hF'
      have hlen' : F'.length = n := by rw [hF', foldl_gStep_len, hlen]
      have hb : dtg[b]! < n := hlt b (by omega)
      have hbl : dtg[b]! < F'.length := by omega
      show (gStep dtg F' b)[u]! = _
      rw [gStep, get!_set _ _ _ _ hbl, bumpCnt_succ dtg (Nat.zero_le b)]
      by_cases hub : u = dtg[b]!
      · rw [if_pos (by omega), if_pos (by omega), hub, hkey _ hb]
        omega
      · rw [if_neg (by omega), if_neg (by omega), hkey u hu]
        omega

end Twins

/-! ## 1. The out-fill (`RamAugment.outFill`) -/

section Fill

/-- The loop state of both of the fill's loops: the out-target array,
the fill pointers, an index. -/
abbrev FSt : Type := List ℕ × List ℕ × ℕ

def filBf (jend : ℕ) : FSt → Bool := fun s => decide (s.2.2 < jend)

/-- What one slot needs: the slot is in the in-target array, the vertex
it names has a fill pointer, and that pointer is a slot. -/
def filSlotP (T : List ℕ) : FSt → Prop := fun s =>
  s.2.2 < T.length ∧ T[s.2.2]! < s.2.1.length ∧ s.2.1[T[s.2.2]!]! < s.1.length

/-- One slot: read the source, read its fill pointer, write the arc,
bump the pointer. -/
noncomputable def filF (i : ℕ) (T : List ℕ) : FSt → NRest FSt ECost := fun s =>
  bindT (mopAget T s.2.2) fun u =>
    bindT (mopAget s.2.1 u) fun f =>
      bindT (mopAset s.1 f i) fun OT =>
        bindT (BfsQSynth.mopSucc f) fun f1 =>
          bindT (mopAset s.2.1 u f1) fun FL =>
            bindT (BfsQSynth.mopSucc s.2.2) fun p => BfsQ.pack3 OT FL p

/-- The scan of one in-block. -/
noncomputable def filScan (i : ℕ) (T : List ℕ) (jend : ℕ) (s₀ : FSt) : NRest FSt ECost :=
  irWhileIT (fun s => filBf jend s = true → filSlotP T s) (filBf jend) (filF i T) s₀

/-- The step, as a function. -/
def filSlot (i : ℕ) (T : List ℕ) : FSt → FSt := fun s =>
  (s.1.set s.2.1[T[s.2.2]!]! i, s.2.1.set T[s.2.2]! (s.2.1[T[s.2.2]!]! + 1), s.2.2 + 1)

def filRowBf (n : ℕ) : FSt → Bool := fun s => decide (s.2.2 < n)

def filRowP (n : ℕ) (doff dtg : List ℕ) : FSt → Prop := fun s =>
  CShape n doff dtg ∧ s.2.1.length = n ∧ s.2.2 < n

/-- One vertex's row: the block bounds, then the scan, then the counter. -/
noncomputable def filRowF (doff dtg : List ℕ) : FSt → NRest FSt ECost := fun s =>
  bindT (mopAget doff s.2.2) fun j0 =>
    bindT (mopBinop .add s.2.2 1) fun ip =>
      bindT (mopAget doff ip) fun jend =>
        bindT (BfsQ.pack3 s.1 s.2.1 j0) fun z0 =>
          bindT (filScan s.2.2 dtg jend z0) fun r =>
            bindT (BfsQSynth.mopSucc s.2.2) fun i => BfsQ.pack3 r.1 r.2.1 i

/-- **The fill pass.** -/
noncomputable def filPass (n : ℕ) (doff dtg : List ℕ) (s₀ : FSt) : NRest FSt ECost :=
  irWhileIT (fun s => filRowBf n s = true → filRowP n doff dtg s) (filRowBf n)
    (filRowF doff dtg) s₀

/-! ### 1.1 One slot, priced -/

/-- One slot: two reads, the arc, the bump, the pointer, the index, the
triple. -/
def filC : ACost String ℕ :=
  cu Currency.aget + cu Currency.aget + cu Currency.aset + cu (binopCurrency .add)
    + cu Currency.aset + cu (binopCurrency .add) + cu Currency.skip + cu Currency.skip

theorem filF_le (i : ℕ) (T : List ℕ) (s : FSt) (h : filSlotP T s) :
    filF i T s ≤ NRest.consume (NRest.returnT (filSlot i T s)) (liftACost filC) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine le_of_eq ?_
  simp only [filF, BfsQ.pack3, BfsQSynth.mopSucc_eq, mopAget_def, mopAset_def, mopBinop_def,
    mopPair_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h3,
    NRest.returnT_bindT, bindT_unitT, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, filC, liftACost_add, liftACost_cu,
    filSlot]
  congr 1
  ac_rfl

/-! ### 1.2 The scan of one in-block -/

theorem filScan_le {Inv : FSt → Prop} (i : ℕ) (T : List ℕ) (jend : ℕ)
    (hs : ∀ t : FSt, Inv t → filBf jend t = true → filSlotP T t ∧ Inv (filSlot i T t)) :
    ∀ (fuel : ℕ) (s : FSt), Inv s → jend - s.2.2 ≤ fuel →
      filScan i T jend s
        ≤ NRest.spec (fun t : FSt => Inv t ∧ jend ≤ t.2.2)
            (fun _ => liftACost ((jend - s.2.2) • iter filC + cu Currency.«while»)) := by
  have exit : ∀ s : FSt, Inv s → jend ≤ s.2.2 →
      filScan i T jend s
        ≤ NRest.spec (fun t : FSt => Inv t ∧ jend ≤ t.2.2)
            (fun _ => liftACost ((jend - s.2.2) • iter filC + cu Currency.«while»)) := by
    intro s hI hk
    have hb : filBf jend s = false := by simp only [filBf, decide_eq_false_iff_not]; omega
    simp only [filScan, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨hI, hk⟩ ?_
    rw [show jend - s.2.2 = 0 by omega]
    simp
  intro fuel
  induction fuel with
  | zero => intro s hI hf; exact exit s hI (by omega)
  | succ fuel ih =>
    intro s hI hf
    by_cases hb : s.2.2 < jend
    · have hbt : filBf jend s = true := by simp [filBf, hb]
      obtain ⟨hPs, hInv'⟩ := hs s hI hbt
      have hIs : filBf jend s = true → filSlotP T s := fun _ => hPs
      have hk' : (filSlot i T s).2.2 = s.2.2 + 1 := rfl
      have hih := ih (filSlot i T s) hInv' (by rw [hk']; omega)
      rw [hk'] at hih
      have hcost : irUnit Currency.«while»
          + (liftACost filC + liftACost ((jend - (s.2.2 + 1)) • iter filC + cu Currency.«while»))
          = liftACost ((jend - s.2.2) • iter filC + cu Currency.«while») := by
        rw [show jend - s.2.2 = (jend - (s.2.2 + 1)) + 1 by omega, succ_nsmul]
        simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
        ac_rfl
      calc filScan i T jend s
          = NRest.consume (NRest.bindT (filF i T s) fun s' => filScan i T jend s')
              (irUnit Currency.«while») := by
            simp only [filScan]; rw [irWhileIT_of_true hIs hbt]
        _ ≤ NRest.consume (NRest.bindT
              (NRest.consume (NRest.returnT (filSlot i T s)) (liftACost filC))
              fun s' => filScan i T jend s') (irUnit Currency.«while») :=
            NRest.consume_mono (NRest.bindT_mono (filF_le i T s hPs) fun _ => le_rfl) le_rfl
        _ = NRest.consume (NRest.consume (filScan i T jend (filSlot i T s)) (liftACost filC))
              (irUnit Currency.«while») := by rw [bindT_unitT]
        _ ≤ _ := by
            rw [← hcost]
            exact NRest.consume_mono (NRest.consume_mono hih le_rfl) le_rfl |>.trans
              (le_of_eq (by rw [Sepref.consume_spec, Sepref.consume_spec]))
    · exact exit s hI (by omega)

/-! ### 1.3 The row, and the pass

The one thing the fill has to be told and the count does not: that the
pointers it is handed leave **room** — the pointer of `u` plus the
number of slots naming `u` is still inside the target array. That is
exactly what the prefix pass (`AugmentSynth` §3) leaves, and it is the
whole of the fill's safety: nothing else keeps `otg[ofl[u]] := i` in
range. -/

/-- What the fill is handed: the in-block structure, the pointers at
their block starts, and room for every arc. -/
def FPre (n m : ℕ) (doff dtg OT₀ ofl₀ : List ℕ) : Prop :=
  CShape n doff dtg ∧ doff[0]! = 0 ∧ doff[n]! = m ∧ ofl₀.length = n ∧
    m ≤ OT₀.length ∧ ∀ u, u < n → ofl₀[u]! + bumpCnt dtg 0 m (u + 1) ≤ m

theorem bumpCnt_le (T : List ℕ) {a b : ℕ} (hab : a ≤ b) (k : ℕ) :
    bumpCnt T 0 a k ≤ bumpCnt T 0 b k := by
  rw [← bumpCnt_add T (Nat.zero_le a) hab k]; omega

theorem slotsIn_append {a b : ℕ} (hab : a ≤ b) :
    ∀ {c : ℕ}, b ≤ c → slotsIn a b ++ slotsIn b c = slotsIn a c := by
  intro c
  induction c with
  | zero =>
    intro h
    obtain rfl : b = 0 := by omega
    obtain rfl : a = 0 := by omega
    simp [slotsIn_self]
  | succ c ih =>
    intro h
    rcases Nat.lt_or_ge c b with hcb | hcb
    · obtain rfl : b = c + 1 := by omega
      rw [slotsIn_self, List.append_nil]
    · rw [slotsIn_succ hcb, slotsIn_succ (le_trans hab hcb), ← List.append_assoc, ih hcb]

/-- **The rows tile the target array.** The pointer array after `i`
whole rows is the pointer array after the slots `[doff[0], doff[i])` —
which is what makes the fill's invariant a statement about *one*
counter, the global slot index, and not about a pair of them. -/
theorem foldl_fRow_snd {n : ℕ} {doff dtg : List ℕ} (hsh : CShape n doff dtg)
    (Y : List ℕ × List ℕ) :
    ∀ i, i ≤ n → ((List.range i).foldl (fRow doff dtg) Y).2
      = (slotsIn doff[0]! doff[i]!).foldl (gStep dtg) Y.2 := by
  intro i
  induction i with
  | zero => intro _; rw [List.range_zero, List.foldl_nil, slotsIn_self, List.foldl_nil]
  | succ i ih =>
    intro hi
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, fRow,
      foldl_fStep_snd, ih (by omega), ← List.foldl_append,
      slotsIn_append (hsh.mono' (Nat.zero_le i) (by omega)) (hsh.2.1 i (by omega))]

theorem foldl_fRow_fst_len (doff dtg : List ℕ) (Y : List ℕ × List ℕ) (i : ℕ) :
    ((List.range i).foldl (fRow doff dtg) Y).1.length = Y.1.length := by
  induction i with
  | zero => rfl
  | succ i ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      fRow, foldl_fStep_fst_len, ih]

/-- One row, everything outside the scan — including the scan loop's own
entry test. -/
def filRowC : ACost String ℕ :=
  cu Currency.aget + cu (binopCurrency .add) + cu Currency.aget + cu Currency.skip
    + cu Currency.skip + cu Currency.«while» + cu (binopCurrency .add) + cu Currency.skip
    + cu Currency.skip

theorem filRowF_le {n m : ℕ} {doff dtg OT₀ ofl₀ : List ℕ}
    (hpre : FPre n m doff dtg OT₀ ofl₀)
    (s : FSt) (hlen : s.1.length = OT₀.length) (hi : s.2.2 < n)
    (hsnd : s.2.1 = (slotsIn 0 doff[s.2.2]!).foldl (gStep dtg) ofl₀) :
    filRowF doff dtg s
      ≤ NRest.spec
          (fun t : FSt => t.1.length = OT₀.length ∧ t.2.2 = s.2.2 + 1 ∧
            (t.1, t.2.1) = fRow doff dtg (s.1, s.2.1) s.2.2)
          (fun _ => liftACost (filRowC + (doff[s.2.2 + 1]! - doff[s.2.2]!) • iter filC)) := by
  obtain ⟨hsh, hd0, hdn, hfl, hmOT, hroom⟩ := hpre
  have hdlen : doff.length = n + 1 := hsh.1
  have h0 : s.2.2 < doff.length := by omega
  have h1 : s.2.2 + 1 < doff.length := by omega
  have hmono : doff[s.2.2]! ≤ doff[s.2.2 + 1]! := hsh.2.1 _ hi
  have hrow : doff[s.2.2 + 1]! ≤ dtg.length :=
    le_trans (hsh.mono' (show s.2.2 + 1 ≤ n by omega) le_rfl) hsh.2.2.1
  have htop : doff[s.2.2 + 1]! ≤ m := by rw [← hdn]; exact hsh.mono' (by omega) le_rfl
  have hbot : 0 ≤ doff[s.2.2]! := Nat.zero_le _
  -- the scan's invariant: the state is the twin's partial fold
  set Inv : FSt → Prop := fun z => doff[s.2.2]! ≤ z.2.2 ∧ z.2.2 ≤ doff[s.2.2 + 1]! ∧
    (z.1, z.2.1) = (slotsIn doff[s.2.2]! z.2.2).foldl (fStep dtg s.2.2) (s.1, s.2.1) with hInv
  have hglob : ∀ z : FSt, Inv z → z.2.1 = (slotsIn 0 z.2.2).foldl (gStep dtg) ofl₀ := by
    rintro z ⟨hz1, -, hz3⟩
    have h2 : z.2.1 = (slotsIn doff[s.2.2]! z.2.2).foldl (gStep dtg) s.2.1 := by
      rw [show z.2.1 = (z.1, z.2.1).2 from rfl, hz3, foldl_fStep_snd]
    rw [h2, hsnd, ← List.foldl_append, slotsIn_append hbot hz1]
  have hs : ∀ z : FSt, Inv z → filBf doff[s.2.2 + 1]! z = true →
      filSlotP dtg z ∧ Inv (filSlot s.2.2 dtg z) := by
    intro z hI hzb
    obtain ⟨hz1, hz2, hz3⟩ := id hI
    have hzlt : z.2.2 < doff[s.2.2 + 1]! := by simpa [filBf] using hzb
    have hzt : z.2.2 < dtg.length := by omega
    have hu : dtg[z.2.2]! < n := hsh.2.2.2 _ hzt
    have hzsnd : z.2.1 = (slotsIn 0 z.2.2).foldl (gStep dtg) ofl₀ := hglob z hI
    have hzlen : z.2.1.length = n := by rw [hzsnd, foldl_gStep_len, hfl]
    have hz1len : z.1.length = OT₀.length := by
      rw [show z.1 = (z.1, z.2.1).1 from rfl, hz3, foldl_fStep_fst_len, hlen]
    -- the pointer of the vertex the slot names, in closed form
    have hptr : z.2.1[dtg[z.2.2]!]! = ofl₀[dtg[z.2.2]!]! + bumpCnt dtg 0 z.2.2 (dtg[z.2.2]! + 1) := by
      rw [hzsnd]
      refine foldl_gStep_get (base := fun u => ofl₀[u]!) (Nat.zero_le _) hfl
        (fun p hp => hsh.2.2.2 p (by omega)) (fun u _ => ?_) _ hu
      rw [bumpCnt_self, Nat.add_zero]
    have hbump : bumpCnt dtg 0 z.2.2 (dtg[z.2.2]! + 1) + 1
        ≤ bumpCnt dtg 0 m (dtg[z.2.2]! + 1) := by
      have hsucc := bumpCnt_succ dtg (Nat.zero_le z.2.2) (dtg[z.2.2]! + 1)
      rw [if_pos rfl] at hsucc
      rw [← hsucc]
      exact bumpCnt_le dtg (by omega) _
    have hroom' := hroom _ hu
    have hlt : z.2.1[dtg[z.2.2]!]! < z.1.length := by rw [hptr, hz1len]; omega
    refine ⟨⟨hzt, by omega, hlt⟩, ?_, ?_, ?_⟩
    · show doff[s.2.2]! ≤ z.2.2 + 1
      omega
    · show z.2.2 + 1 ≤ doff[s.2.2 + 1]!
      omega
    · show ((filSlot s.2.2 dtg z).1, (filSlot s.2.2 dtg z).2.1)
        = (slotsIn doff[s.2.2]! (z.2.2 + 1)).foldl (fStep dtg s.2.2) (s.1, s.2.1)
      rw [slotsIn_succ hz1, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hz3]
      rfl
  have hstart : Inv (s.1, s.2.1, doff[s.2.2]!) := by
    refine ⟨le_rfl, hmono, ?_⟩
    show ((s.1, s.2.1, doff[s.2.2]!).1, (s.1, s.2.1, doff[s.2.2]!).2.1)
      = (slotsIn doff[s.2.2]! doff[s.2.2]!).foldl (fStep dtg s.2.2) (s.1, s.2.1)
    rw [slotsIn_self, List.foldl_nil]
  have hscan := filScan_le (Inv := Inv) s.2.2 dtg doff[s.2.2 + 1]! hs
    (doff[s.2.2 + 1]! - doff[s.2.2]!) (s.1, s.2.1, doff[s.2.2]!) hstart (by simp)
  have hK : ∀ r : FSt, (Inv r ∧ doff[s.2.2 + 1]! ≤ r.2.2) →
      NRest.consume (NRest.returnT ((r.1, r.2.1, s.2.2 + 1) : FSt))
          (irUnit (binopCurrency .add) + (irUnit Currency.skip + irUnit Currency.skip))
        ≤ NRest.spec
            (fun t : FSt => t.1.length = OT₀.length ∧ t.2.2 = s.2.2 + 1 ∧
              (t.1, t.2.1) = fRow doff dtg (s.1, s.2.1) s.2.2)
            (fun _ => irUnit (binopCurrency .add)
              + (irUnit Currency.skip + irUnit Currency.skip)) := by
    rintro r ⟨hIr, hdone⟩
    have hrend : r.2.2 = doff[s.2.2 + 1]! := by omega
    obtain ⟨-, -, hr3⟩ := hIr
    refine consume_returnT_le_spec ⟨?_, rfl, ?_⟩ le_rfl
    · rw [show r.1 = (r.1, r.2.1).1 from rfl, hr3, foldl_fStep_fst_len, hlen]
    · show (r.1, r.2.1) = fRow doff dtg (s.1, s.2.1) s.2.2
      rw [hr3, hrend, fRow]
  simp only [filRowF, BfsQ.pack3, BfsQSynth.mopSucc_eq, mopAget_def, mopBinop_def, mopPair_def,
    NRest.assert_pos h0, NRest.assert_pos h1, NRest.returnT_bindT,
    NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, NRest.bindT_assoc_acost]
  refine le_trans (NRest.consume_mono
    (le_trans (NRest.bindT_mono hscan fun _ => le_rfl) (bindT_spec_le _ _ _ _ _ hK)) le_rfl)
    (le_of_eq ?_)
  rw [Sepref.consume_spec]
  refine congrArg (NRest.spec _) (funext fun _ => ?_)
  simp only [filRowC, iter, liftACost_add, liftACost_nsmul, liftACost_cu, binopCurrency_add]
  ac_rfl

/-- **The fill pass, bounded.** Two currencies, as the counting pass:
one row-cost per vertex still to visit and one slot-cost per slot still
to fill. The second is bounded because the rows *tile* the target array
— `foldl_fRow_snd` is that tiling. -/
theorem filPass_le {n m : ℕ} {doff dtg OT₀ ofl₀ : List ℕ}
    (hpre : FPre n m doff dtg OT₀ ofl₀) :
    ∀ (fuel : ℕ) (s : FSt), s.2.2 ≤ n → n - s.2.2 ≤ fuel →
      (s.1, s.2.1) = (List.range s.2.2).foldl (fRow doff dtg) (OT₀, ofl₀) →
      filPass n doff dtg s
        ≤ NRest.spec
            (fun t : FSt => t.1.length = OT₀.length ∧
              (t.1, t.2.1) = fFold n doff dtg (OT₀, ofl₀))
            (fun _ => liftACost (E2 (iter filRowC) (iter filC) (n - s.2.2)
              (doff[n]! - doff[s.2.2]!) + cu Currency.«while»)) := by
  have hsh : CShape n doff dtg := hpre.1
  have hd0 : doff[0]! = 0 := hpre.2.1
  have exit : ∀ s : FSt, n ≤ s.2.2 → s.2.2 ≤ n →
      (s.1, s.2.1) = (List.range s.2.2).foldl (fRow doff dtg) (OT₀, ofl₀) →
      filPass n doff dtg s
        ≤ NRest.spec
            (fun t : FSt => t.1.length = OT₀.length ∧
              (t.1, t.2.1) = fFold n doff dtg (OT₀, ofl₀))
            (fun _ => liftACost (E2 (iter filRowC) (iter filC) (n - s.2.2)
              (doff[n]! - doff[s.2.2]!) + cu Currency.«while»)) := by
    intro s hge hle hall
    have hb : filRowBf n s = false := by simp only [filRowBf, decide_eq_false_iff_not]; omega
    obtain rfl : s.2.2 = n := by omega
    simp only [filPass, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨?_, hall⟩ ?_
    · rw [show s.1 = (s.1, s.2.1).1 from rfl, hall, foldl_fRow_fst_len]
    · rw [liftACost_add, liftACost_cu, add_comm]
      exact cost_le_add _ _
  intro fuel
  induction fuel with
  | zero => intro s hle hf hall; exact exit s (by omega) hle hall
  | succ fuel ih =>
    intro s hle hf hall
    by_cases hb : s.2.2 < n
    · have hlen : s.1.length = OT₀.length := by
        rw [show s.1 = (s.1, s.2.1).1 from rfl, hall, foldl_fRow_fst_len]
      have hsnd : s.2.1 = (slotsIn 0 doff[s.2.2]!).foldl (gStep dtg) ofl₀ := by
        rw [show s.2.1 = (s.1, s.2.1).2 from rfl, hall,
          foldl_fRow_snd hsh (OT₀, ofl₀) s.2.2 (by omega), hd0]
      have hIs : filRowBf n s = true → filRowP n doff dtg s := fun _ =>
        ⟨hsh, by rw [hsnd, foldl_gStep_len, hpre.2.2.2.1], hb⟩
      have hbt : filRowBf n s = true := by simp [filRowBf, hb]
      have hmono : doff[s.2.2]! ≤ doff[s.2.2 + 1]! := hsh.2.1 _ hb
      have htop : doff[s.2.2 + 1]! ≤ doff[n]! := hsh.mono' (by omega) le_rfl
      have hcont : ∀ t : FSt, (t.1.length = OT₀.length ∧ t.2.2 = s.2.2 + 1 ∧
            (t.1, t.2.1) = fRow doff dtg (s.1, s.2.1) s.2.2) →
          filPass n doff dtg t
            ≤ NRest.spec
                (fun t' : FSt => t'.1.length = OT₀.length ∧
                  (t'.1, t'.2.1) = fFold n doff dtg (OT₀, ofl₀))
                (fun _ => liftACost (E2 (iter filRowC) (iter filC) (n - (s.2.2 + 1))
                  (doff[n]! - doff[s.2.2 + 1]!) + cu Currency.«while»)) := by
        rintro t ⟨-, hti, htval⟩
        refine le_trans (ih t (by omega) (by omega) ?_) (le_of_eq ?_)
        · rw [htval, hti, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
            ← hall]
        · rw [hti]
      have hcost : irUnit Currency.«while»
          + (liftACost (filRowC + (doff[s.2.2 + 1]! - doff[s.2.2]!) • iter filC)
            + liftACost (E2 (iter filRowC) (iter filC) (n - (s.2.2 + 1))
                (doff[n]! - doff[s.2.2 + 1]!) + cu Currency.«while»))
          = liftACost (E2 (iter filRowC) (iter filC) (n - s.2.2)
              (doff[n]! - doff[s.2.2]!) + cu Currency.«while») := by
        rw [show n - s.2.2 = (n - (s.2.2 + 1)) + 1 by omega,
          show doff[n]! - doff[s.2.2]!
            = (doff[n]! - doff[s.2.2 + 1]!) + (doff[s.2.2 + 1]! - doff[s.2.2]!) by omega,
          E2_split]
        simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
        ac_rfl
      calc filPass n doff dtg s
            = NRest.consume (NRest.bindT (filRowF doff dtg s)
                fun t => filPass n doff dtg t) (irUnit Currency.«while») := by
              simp only [filPass]; rw [irWhileIT_of_true hIs hbt]
        _ ≤ NRest.consume (NRest.spec _ (fun _ =>
              liftACost (filRowC + (doff[s.2.2 + 1]! - doff[s.2.2]!) • iter filC)
              + liftACost (E2 (iter filRowC) (iter filC) (n - (s.2.2 + 1))
                  (doff[n]! - doff[s.2.2 + 1]!) + cu Currency.«while»)))
              (irUnit Currency.«while») :=
            NRest.consume_mono
              (le_trans (NRest.bindT_mono (filRowF_le hpre s hlen hb hsnd) fun _ => le_rfl)
                (bindT_spec_le _ _ _ _ _ hcont)) le_rfl
        _ = _ := by rw [Sepref.consume_spec, ← hcost]
    · exact exit s (by omega) hle hall

/-- **The fill pass, run from the start.** It computes the twin, and its
fill pointers end where the prefix pass says they should: the pointer of
`u` has advanced by the out-degree of `u` — `bumpCnt dtg 0 m (u+1)`, the
same count `cntPass_spec` leaves in `ooff`. -/
theorem filPass_spec {n m : ℕ} {doff dtg OT₀ ofl₀ : List ℕ}
    (hpre : FPre n m doff dtg OT₀ ofl₀) :
    filPass n doff dtg (OT₀, ofl₀, 0)
      ≤ NRest.spec
          (fun t : FSt => t.1.length = OT₀.length ∧
            (t.1, t.2.1) = fFold n doff dtg (OT₀, ofl₀) ∧
            ∀ u, u < n → t.2.1[u]! = ofl₀[u]! + bumpCnt dtg 0 m (u + 1))
          (fun _ => liftACost (E2 (iter filRowC) (iter filC) n m + cu Currency.«while»)) := by
  obtain ⟨hsh, hd0, hdn, hfl, hmOT, hroom⟩ := hpre
  have hstart : ((OT₀, ofl₀, (0 : ℕ)).1, (OT₀, ofl₀, (0 : ℕ)).2.1)
      = (List.range (OT₀, ofl₀, (0 : ℕ)).2.2).foldl (fRow doff dtg) (OT₀, ofl₀) := by
    rw [show (OT₀, ofl₀, (0 : ℕ)).2.2 = 0 from rfl, List.range_zero, List.foldl_nil]
  refine le_trans
    (filPass_le (m := m) ⟨hsh, hd0, hdn, hfl, hmOT, hroom⟩ n (OT₀, ofl₀, 0)
      (Nat.zero_le n) (by simp) hstart) ?_
  refine spec_mono (fun t ht => ⟨ht.1, ht.2, fun u hu => ?_⟩)
    (fun _ _ => le_of_eq (by rw [hd0, hdn]; simp))
  have h2 : t.2.1 = (slotsIn doff[0]! doff[n]!).foldl (gStep dtg) ofl₀ := by
    rw [show t.2.1 = (t.1, t.2.1).2 from rfl, ht.2, fFold, foldl_fRow_snd hsh (OT₀, ofl₀) n le_rfl]
  rw [h2, hd0, hdn]
  refine foldl_gStep_get (base := fun u => ofl₀[u]!) (Nat.zero_le _) hfl
    (fun p hp => hsh.2.2.2 p (by
      have : doff[n]! ≤ dtg.length := hsh.2.2.1
      omega)) (fun u _ => by rw [bumpCnt_self, Nat.add_zero]) u hu

/-- …and at the array the round hands it — `otg` zeroed to the arc count
— that twin is `AugmentTwins.outFillTw`, which `AugmentTwins` §1.3
differential-tests against `RamAugment.Demo`'s own out-lists. -/
theorem filPass_twin {n m : ℕ} {doff dtg ofl₀ : List ℕ}
    (hpre : FPre n m doff dtg (List.replicate m 0) ofl₀) :
    filPass n doff dtg (List.replicate m 0, ofl₀, 0)
      ≤ NRest.spec
          (fun t : FSt => t.1.length = m ∧
            (t.1, t.2.1) = outFillTw n m doff dtg ofl₀ ∧
            ∀ u, u < n → t.2.1[u]! = ofl₀[u]! + bumpCnt dtg 0 m (u + 1))
          (fun _ => liftACost (E2 (iter filRowC) (iter filC) n m + cu Currency.«while»)) := by
  refine le_trans (filPass_spec hpre) (spec_mono (fun t ht => ?_) (fun _ _ => le_rfl))
  refine ⟨by rw [ht.1, List.length_replicate], ?_, ht.2.2⟩
  rw [ht.2.1, fFold_eq_outFillTw]

set_option maxHeartbeats 1000000 in
sepref_synth filPassSynth (n : ℕ) (doff dtg otg₀ ofl₀ : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ natAssn) (otg₀, ofl₀, 0)
        ("otg", ("ofl", "agi")) ∗
      hnCtxt arrayAssn doff "doff" ∗ hnCtxt arrayAssn dtg "dtg" ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "agjo" ∗ junkCell "agip" ∗ junkCell "agend" ∗
      junkCell "agu" ∗ junkCell "agf")
    _ _ ("otg", ("ofl", "agi")) (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
    (filPass n doff dtg (otg₀, ofl₀, 0))

end Fill

/-! ## 2. Gate (ledger D4, refute before prove)

The *synthesized* fill is run by `Ir/Semantics.lean`'s own evaluator on
`RamAugment.Demo`'s orientation, on the two-witness orientation and on
the K₁,₄ witness, and what it leaves in `otg`/`ofl` is checked against
`AugmentTwins`'s twin — which `AugmentTwins` §1.3 already checks against
`RamAugment.Demo`'s own reported out-lists. §2.1 closes the chain: the
three synthesized passes of phase 1, run one after another, reproduce
`outPassTw`. Every positive check carries a negative control. -/

section Gate

/-- The fill's store: eight scalars, four arrays. -/
def filState (n m : ℕ) (doff dtg ofl₀ : List ℕ) : Ir.State :=
  Ir.State.ofPairs
    [("agi", 0), ("n", n), ("one", 1), ("agjo", 0), ("agip", 0), ("agend", 0),
      ("agu", 0), ("agf", 0)]
    [("otg", List.replicate m 0), ("ofl", ofl₀), ("doff", doff), ("dtg", dtg)]

def gFill (n m : ℕ) (doff dtg ofl₀ : List ℕ) : Option (List ℕ × List ℕ) :=
  (Ir.evalFuel 4000 filPassSynth_impl (filState n m doff dtg ofl₀)).bind fun p =>
    (p.1.arrs "otg").bind fun T => (p.1.arrs "ofl").map fun F => (T, F)

-- **The fill agrees with its twin** on the demo orientation …
#guard gFill 4 4 dOff dTgt [0, 2, 3, 4] = some (outFillTw 4 4 dOff dTgt [0, 2, 3, 4])
-- … at the value `RamAugment.Demo`'s out-lists have: `1 2 | 2 | 3 |`,
-- with every fill pointer left at its block's end
#guard gFill 4 4 dOff dTgt [0, 2, 3, 4] = some ([1, 2, 2, 3], [2, 3, 4, 4])
-- … on the doubly-witnessed pair …
#guard gFill 4 4 wOff wTgt [0, 2, 4, 4] = some (outFillTw 4 4 wOff wTgt [0, 2, 4, 4])
-- … and on the K₁,₄ witness, where all four arcs are the centre's
#guard gFill 5 4 starOff starTgt [0, 0, 1, 2, 3]
  = some (outFillTw 5 4 starOff starTgt [0, 0, 1, 2, 3])
#guard gFill 5 4 starOff starTgt [0, 0, 1, 2, 3] = some ([0, 0, 0, 0], [0, 1, 2, 3, 4])

-- **The negative controls.** The fill writes the *source* of each arc,
-- not its target …
/--
error: Expression
  decide (gFill 4 4 dOff dTgt [0, 2, 3, 4] = some ([0, 0, 1, 2], [2, 3, 4, 4]))
did not evaluate to `true`
-/
#guard_msgs in
#guard gFill 4 4 dOff dTgt [0, 2, 3, 4] = some ([0, 0, 1, 2], [2, 3, 4, 4])

-- … and it really moves the pointers: the entry pointers are refuted.
/--
error: Expression
  decide (gFill 4 4 dOff dTgt [0, 2, 3, 4] = some ([1, 2, 2, 3], [0, 2, 3, 4]))
did not evaluate to `true`
-/
#guard_msgs in
#guard gFill 4 4 dOff dTgt [0, 2, 3, 4] = some ([1, 2, 2, 3], [0, 2, 3, 4])

/-! ### 2.1 Phase 1, end to end

`cntPassSynth_impl`, then `prefSynth_impl`, then `filPassSynth_impl` —
the three synthesized programs of `RamAugment.outPass`, glued by hand
outside the tool (the `Spec`-level shape of `AugmentSynth` §5.1, one
pass longer). What comes out is `outPassTw`, and `outPassTw` is what
`RamAugment.Demo` reports. -/

def gOutFill (n m : ℕ) (doff dtg : List ℕ) : Option (List ℕ × List ℕ) :=
  (AugmentSynth.gOutPass n doff dtg).bind fun p => gFill n m doff dtg p.2

-- **The whole out-list build, synthesized, on the demo orientation**:
-- the offsets `0 2 3 4 4` and the targets `1 2 2 3` — `RamAugment.Demo`'s
-- own out-lists.
#guard ((AugmentSynth.gOutPass 4 dOff dTgt).map fun p => p.1,
    (gOutFill 4 4 dOff dTgt).map fun p => p.1)
  = (some (outPassTw 4 4 dOff dTgt).1, some (outPassTw 4 4 dOff dTgt).2)
#guard (gOutFill 4 4 dOff dTgt).map (fun p => p.1) = some [1, 2, 2, 3]
#guard (gOutFill 4 4 wOff wTgt).map (fun p => p.1) = some (outPassTw 4 4 wOff wTgt).2
#guard (gOutFill 5 4 starOff starTgt).map (fun p => p.1)
  = some (outPassTw 5 4 starOff starTgt).2

-- **The negative control**: the chain is not the identity on `otg`.
/--
error: Expression
  decide (Option.map (fun p => p.1) (gOutFill 4 4 dOff dTgt) = some [0, 0, 0, 0])
did not evaluate to `true`
-/
#guard_msgs in
#guard (gOutFill 4 4 dOff dTgt).map (fun p => p.1) = some [0, 0, 0, 0]

end Gate

/-! ## 3. The cost, computed -/

section Cost

/-- **The fill's cost**: `26·n + 26·m + 4` IMP+ time units, two
currencies — one per vertex and one per *slot* — against the baseline's
`21·m + 20·n + 8` (`RamDriverAugment.outFill_run`). Touched-only: `m`
is `doff[n]`, the arcs, and no array is swept. -/
def filK (n m : ℕ) : ℕ := 26 * n + 26 * m + 4

theorem ecash_filTotal (n m : ℕ) :
    ecash (liftACost (E2 (iter filRowC) (iter filC) n m + cu Currency.«while»))
      = (filK n m : ℕ∞) := by
  rw [E2, BfsQSynth.ecash_liftACost, Codegen.cash_add, Codegen.cash_add,
    BfsQSynth.cash_nsmul, BfsQSynth.cash_nsmul,
    show Codegen.cash (iter filRowC) = 26 from by decide +kernel,
    show Codegen.cash (iter filC) = 26 from by decide +kernel,
    show Codegen.cash (cu Currency.«while») = 4 from by decide +kernel, filK]
  push_cast
  ring

end Cost

/-! ## 4. Telemetry (wave 2C′)

* **Synthesis wall clock**, warm build: `filPassSynth` — two loops, the
  inner one mid-body, a **three**-component loop state carrying two
  arrays, and the outer loop's own counter cell read from inside the
  inner body (`aset "otg" "agf" "agi"`) — **first run, no bespoke tactic
  work, no hand-written frame clause, no `LOOP_VARIANT`, no copy of the
  counter into a scratch cell**. The whole module elaborates in ≈9 s.

  That last point is the wave's one tool measurement: 2C's F2 predicted
  that a value owned by the *outer* loop's state tuple would not be
  readable from a rule fired inside the *inner* loop. Post-T1 it is —
  T1/D-b normalizes the pair context to components and `fri` matches the
  counter conjunct straight out of the frame. So the fill needed no
  `mopCopy` idiom, and 2C's §10 gap 4 is confirmed closed at a second,
  independent instance (the first is `T1FriProbe.cntThenPref`).

* **Cost, computed** (`decide +kernel` from the per-iteration account,
  not tuned):

  | pass | tower | baseline (`RamDriverAugment`) | ratio |
  |---|---|---|---|
  | out-fill | `filK n m = 26·n + 26·m + 4` | `21·m + 20·n + 8` | ≈1.25 |

  Two currencies, one per vertex and one per *slot*: `m` is `doff[n]`,
  the arcs, so the pass is charged touched-only and no array is swept.
  With 2C's three passes, phase 1 of the round costs
  `cntK n m + prefK n + filK n m = 80·n + 52·m + 12` against the
  baseline's `42·m + 63·n + 24` (`RamDriverAugment.outPass_run`).

* **Bounds pass**: **not** done, and the reason is 2C's §10 gap 3
  unchanged — `BRefine.while` proves a loop at its own loop assertion,
  and no rule frames an inner loop's assertion inside an outer body. The
  fill has exactly the counting pass's two-level shape, so it inherits
  exactly that debt; no new one. (Neither pass's `Spec` export can be
  built until the rule exists, which is why this file stops at
  `filPass_spec` — an `NRest` bound — where the mask pass of 2C reaches
  `Reasoning.Spec`.)

* **Refuted before proved.** §2 runs the *synthesized* fill on
  `RamAugment.Demo`'s orientation, on the two-witness orientation and on
  the K₁,₄ witness, checking `otg` **and** `ofl` against the twin and
  against the demo's own out-lists, with two pinned negative controls
  (the arc's *target* written instead of its source; the pointers left
  unmoved) and one more on the three-pass chain. The
  `omega`-through-`Ir.Val` trap did not fire (every side condition is on
  ℕ-typed abstract values); every scratch cell is `"ag"`-prefixed and
  digit-free (P1/B-f) and is consumed in the order it is written.

* **Integration notes.** Cells written: `"agi"`, `"agjo"`, `"agip"`,
  `"agend"`, `"agu"`, `"agf"`. Cells read only: `"n"`, `"one"`. Arrays:
  `"otg"` (written), `"ofl"` (written), `"doff"`/`"dtg"` (read) — the
  baseline's names verbatim, since those are the integration surface
  (R2C/D-c). The entry store pins every scratch cell at zero and
  `"one"` at one (P7/D-bp). Six of the eight cells are 2C's own, so the
  count pass and the fill share their scratch space; only `"agf"` is new
  and only `"agc"`/`"agup"` of 2C's are unused here.

## 5. What a future `R > 0` wave would still need

The round is five phases (`RamAugment.augCom`). After this file:

1. `outPass` — **complete** (2C's `cntPassSynth`/`prefSynth`, this
   file's `filPassSynth`); glued at `Spec` level, §2.1.
2. `fratPass` — **not started.** The twins are landed and tested
   (`AugmentTwins.fratRowTw`/`fratCountTw`/`fratSlotsTw`, with
   `stamp_matters` showing the dedup is load-bearing and
   `fratSlotsTw_star` identifying the twin's answer with
   `TgtCoupling.csrSlots (fratGraph starOr)`), and the shape is known:
   an outer loop over vertices whose body runs **two** double loops (the
   stamped emit and the clearing walk) over the same block pair, with a
   guard whose arms write the *inner* loop's state — the configuration
   that already synthesizes (`ElimSynth2`). Its cost is not a tiling:
   the inner scan runs `∑_k indeg(otg[k])` times, so the honest bound is
   per-vertex rows × per-slot middle × a uniform `d` on the innermost,
   which needs `D.InDegLE d` as a hypothesis and gives `m·d` slot-work.
   The `fratFill` twin is the same walk writing `tgt`.
3. `alvSet` — **complete** (2C §2, exported to `Reasoning.Spec` with the
   `arrOf` bridge: `AugmentSynth.alvCom_spec_arrOf`).
4. `elimCom` — the engine; satellites 2B/2B′ have four phases derived.
   It fires as a leaf (`hnr_bind`), and since T1 the pass that reads what
   it wrote no longer stalls (`T1FriProbe.bfsThenSweep`).
5. `asmPass` — **not started**, and the heaviest: two stamp arrays,
   three enumerations, a rank comparison and a nested guard, with
   `AugPre`'s `sta`/`std`/`ste` live at once. Its correctness is
   `RamAugment.inN_augOr_eq`, landed capital.

Two things stand between the passes and a round-level export in the
vocabulary `RamDriverAugment.implements` consumes
(`RamAugment.Implements`, i.e. a `Spec B (AugPre …) augCom (AugMem …)
(augCost n W)`):

* the **`BRefine` nested-loop rule** (2C §10 gap 3) — without it no
  two-level pass reaches `Reasoning.Spec` at all, so phases 1 and 2 stop
  at `NRest` bounds;
* the **bridge from the list layer to the `Blocks`/`InCsr` layer** —
  every phase-run lemma of `RamDriverAugment` (`outPass_run`,
  `fratPass_run`, `asmPass_run`) states its postcondition in Finset
  vocabulary (`ScatInv`, `CsrSimple (fratGraph D)`), while the tower's
  passes state theirs about `List`s and `bumpCnt`. `slotCnt_out_eq`'s
  content is already `bumpCnt` + `cntPass_spec` (2C's R2C/D-a), which is
  the model for the rest of that bridge. -/

/-! ## 6. Axioms -/

/-- info: 'Lax3Proofs.Refine.AugmentSynth2.filPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms filPass_spec

/-- info: 'Lax3Proofs.Refine.AugmentSynth2.filPass_twin' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms filPass_twin

/-- info: 'Lax3Proofs.Refine.AugmentSynth2.filPassSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms filPassSynth

/-- info: 'Lax3Proofs.Refine.AugmentSynth2.ecash_filTotal' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ecash_filTotal

end Lax3Proofs.Refine.AugmentSynth2
