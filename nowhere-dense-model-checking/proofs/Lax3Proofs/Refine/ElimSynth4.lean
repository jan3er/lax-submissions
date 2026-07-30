import Lax3Proofs.Refine.ElimSynth3

/-!
# P2 wave 2B″ — the elimination engine's exports

Waves 2B/2B′ left three named debts (`ElimSynth3` §5, `ElimSynth2`
§4.3). This wave carries the elimination loop's **layer** work through:
the row scan is walked end to end, the turn's four prices are exact,
and the one turn that is not a straight-line block is put into the
normal form the scan's bound threads into. §5 says precisely what of
E1/E2 is left and what mechanism each remaining step is.

* §1 — the price of a slot of the row scan of an extraction.
* §2 — the engine's data read as `RamElim`'s functions: `lsOf` and
  `scOf`, the `ls`/`sc` cells 2B′/D-a dropped, and the input surface.
* §3 — the row scan, walked against `RamElim.hit` (debt E2's inner
  half, debt E1's slot term).
* §4 — the elimination loop: the loop rule a four-case body needs, the
  invariant in `RamElim.Elim`/`RamElim.Buck` vocabulary, the four
  turns' prices, and the extraction's normal form.
* §5 — what is landed and what is not.
* §6 — axioms.

## House traps observed

`omega` is blind through a tuple projection — every arithmetic clause
of a structure over `DS`/`ES` needs its `show`. `decide +kernel` for
the cashed constants. Never `simp [Codegen.embed]`.
-/

namespace Lax3Proofs.Refine.ElimSynth4

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax13Proofs.Refine.Codegen
open Lax13Proofs.Refine.BfsQ (Shape cu iter irWhile_exit get!_set res_of_le liftACost_cu)
open Lax3Proofs.Refine.ElimSynth hiding mopSucc mopSucc_eq mopKeep mopKeep_eq
open Lax3Proofs.Refine.ElimSynth2
open Lax3Proofs.Refine.ElimSynth3

/-! ## 1. The row scan of an extraction -/

section RowScan

/-- What every slot of the row scan pays: the target and the mask read,
the outer branch, the arms of the branch (`pack5d`) and the index bump
with its `pack6`. -/
def decC0 : ACost String ℕ := cu Currency.aget + cu Currency.aget + cu Currency.ite
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.add
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip

/-- …a slot whose target is alive pays the elimination flag and the
inner branch on top… -/
def decC1 : ACost String ℕ := decC0 + (cu Currency.aget + cu Currency.ite)

/-- …and the slot that really decrements pays the degree read, the
subtraction, the three bucket writes, the head read and the pointer
bump. -/
def decC : ACost String ℕ := decC1 + (cu Currency.aget + cu Currency.sub
  + cu Currency.aset + cu Currency.aget + cu Currency.aset + cu Currency.aset
  + cu Currency.aset + cu Currency.add)

theorem decF_le (tgt alv elm : List ℕ) (s : DS) (h : decP tgt alv elm s) :
    decF tgt alv elm s
      ≤ NRest.consume (NRest.returnT (decStep tgt alv elm s)) (liftACost decC) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have base1 : liftACost decC1 ≤ liftACost decC := by
    rw [decC, liftACost_add]; exact cost_le_add _ _
  have base : liftACost decC0 ≤ liftACost decC :=
    le_trans (by rw [decC1, liftACost_add]; exact cost_le_add _ _) base1
  by_cases hb1 : 0 < alv[tgt[s.2.2.2.2.2]!]!
  · by_cases hb2 : elm[tgt[s.2.2.2.2.2]!]! < 1
    · refine le_of_eq ?_
      simp only [decF, decStep, pack5d, pack6, mopAget_def, mopAset_def, mopSucc_eq,
        mopBinop_def, mopPair_def, irIf_def, NRest.assert_pos h1, NRest.assert_pos h2,
        NRest.assert_pos h3, NRest.assert_pos h4, NRest.assert_pos h5,
        NRest.assert_pos h6, NRest.assert_pos h7, NRest.returnT_bindT,
        NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
        Lax13Proofs.Imp.Bop.apply_add, Lax13Proofs.Imp.Bop.apply_sub, binopCurrency_add,
        binopCurrency_sub, decide_eq_true_eq, if_pos hb1, if_pos hb2, decC, decC1, decC0,
        liftACost_add, liftACost_cu]
      congr 1
      ac_rfl
    · simp only [decF, decStep, pack5d, pack6, mopAget_def, mopSucc_eq, mopBinop_def,
        mopPair_def, irIf_def, NRest.assert_pos h1, NRest.assert_pos h2,
        NRest.assert_pos h3, NRest.returnT_bindT,
        NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
        Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, decide_eq_true_eq, if_pos hb1,
        if_neg hb2]
      refine NRest.consume_mono le_rfl (le_trans (le_of_eq ?_) base1)
      simp only [decC1, decC0, liftACost_add, liftACost_cu]
      ac_rfl
  · simp only [decF, decStep, pack5d, pack6, mopAget_def, mopSucc_eq, mopBinop_def,
      mopPair_def, irIf_def, NRest.assert_pos h1, NRest.assert_pos h2,
      NRest.returnT_bindT, NRest.bindT_consume NRest.addSupContinuousB_acost,
      NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add,
      decide_eq_true_eq, if_neg hb1]
    refine NRest.consume_mono le_rfl (le_trans (le_of_eq ?_) base)
    simp only [decC0, liftACost_add, liftACost_cu]
    ac_rfl

end RowScan

/-! ## 2. The engine's data, read as `RamElim`'s functions -/

section Data

open Lax13Proofs.Reasoning.Lib (upd upd_self upd_of_ne)

/-- The length of a block, in `RamElim`'s cost vocabulary. -/
abbrev rowLen (O : ℕ → ℕ) (v : ℕ) : ℕ := Lax13Proofs.Reasoning.Lib.Csr.rowLen O v

/-- **The slots the buckets hold**, as a function of the two bucket
arrays — `Buck.ls_eq` read as a definition, which is what 2B′/D-a's
dropping of the `ls` cell makes it. -/
def lsOf (n : ℕ) (bh bn : List ℕ) : ℕ :=
  ∑ d ∈ Finset.range (n + 1), (RamElim.chain (larr bn) (larr bh d)).length

/-- **The slots the run has already scanned**, as a function of the
elimination flags — `RamElim.scanned` weighed by the row lengths. -/
def scOf (n : ℕ) (O M : ℕ → ℕ) (elm : List ℕ) : ℕ :=
  ∑ v ∈ RamElim.scanned n (larr elm) M, rowLen O v

/-- The read-only inputs of the engine, at the list layer. -/
structure EIn (n ns W : ℕ) (G : SimpleGraph (Fin n)) (off tgt alv : List ℕ) : Prop where
  /-- The block structure lists each neighbour once. -/
  csr : RamElim.CsrSimple G ns (larr off) (larr tgt)
  /-- The scratch is at least as wide as the block structure. -/
  wide : ns ≤ W
  /-- …and the three arrays are at their lengths. -/
  offLen : off.length = n + 1
  tgtLen : tgt.length = ns
  alvLen : alv.length = n

theorem EIn.scOf_le {n ns W : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv : List ℕ}
    (h : EIn n ns W G off tgt alv) (elm : List ℕ) :
    scOf n (larr off) (larr alv) elm ≤ ns :=
  h.csr.csr.sum_rowLen_le (fun _ hv => (RamElim.mem_scanned.1 hv).1)

end Data

/-! ## 3. The row scan, walked

Debt E2's inner half: the scan of the row of the vertex being taken,
against `RamElim.hit`. What it leaves is `Elim.extract`'s two
hypotheses, by `RamElim.extract_of_scan`, which is consumed. -/

section ScanWalk

open Lax13Proofs.Reasoning.Lib (upd upd_self upd_of_ne)

/-- The invariant of the row scan of an extraction: the arrays at their
lengths, `Buck` on the buckets, and the degrees the extraction started
with decremented at exactly the surviving neighbours the scan has
already passed. -/
structure DecI (n ns W : ℕ) (G : SimpleGraph (Fin n)) (off tgt alv elm : List ℕ)
    (D₀ : ℕ → ℕ) (w sc₀ ls₀ : ℕ) (s : DS) : Prop where
  /-- The degrees, at their length. -/
  degLen : s.1.length = n
  /-- The bucket heads, at theirs. -/
  bhLen : s.2.1.length = n + 1
  /-- The arena's vertex column. -/
  bvLen : s.2.2.1.length = n + W + 1
  /-- The arena's link column. -/
  bnLen : s.2.2.2.1.length = n + W + 1
  /-- The buckets, with the slot count read off them. -/
  buck : RamElim.Buck n n (larr elm) (larr s.1) (larr s.2.1) (larr s.2.2.1)
    (larr s.2.2.2.1) s.2.2.2.2.1 (lsOf n s.2.1 s.2.2.2.1)
  /-- Every degree is a vertex number. -/
  degLt : ∀ u < n, s.1[u]! < n
  /-- A neighbour the scan has passed has lost one. -/
  hitDec : ∀ u < n, RamElim.hit (larr off) (larr tgt) (larr alv) (larr elm) w s.2.2.2.2.2 u →
    s.1[u]! = D₀ u - 1
  /-- And nothing else has moved. -/
  hitKeep : ∀ u < n, ¬ RamElim.hit (larr off) (larr tgt) (larr alv) (larr elm) w s.2.2.2.2.2 u →
    s.1[u]! = D₀ u
  /-- The index is inside the row. -/
  jlo : off[w]! ≤ s.2.2.2.2.2
  /-- …at both ends. -/
  jhi : s.2.2.2.2.2 ≤ off[w + 1]!
  /-- **The arena never overflows**: one slot per vertex and one per
  slot scanned, the row's own slots pre-charged. -/
  spSc : s.2.2.2.2.1 + (off[w + 1]! - s.2.2.2.2.2) ≤ n + 1 + sc₀
  /-- The buckets gain at most one slot per slot passed. -/
  lsAcc : lsOf n s.2.1 s.2.2.2.1 ≤ ls₀ + (s.2.2.2.2.2 - off[w]!)
  /-- And the arena always has room for the sentinel. -/
  lsSp : lsOf n s.2.1 s.2.2.2.1 + 1 ≤ s.2.2.2.2.1

variable {n ns W : ℕ} {G : SimpleGraph (Fin n)} {off tgt alv elm : List ℕ}
  {D₀ : ℕ → ℕ} {w sc₀ ls₀ : ℕ}

/-- Everything one slot of the scan reads is in range. -/
theorem decI_range (hin : EIn n ns W G off tgt alv) (hw : w < n)
    (helm : elm.length = n) (hsc : sc₀ ≤ ns) {s : DS}
    (hI : DecI n ns W G off tgt alv elm D₀ w sc₀ ls₀ s)
    (hb : decBf off[w + 1]! s = true) : decP tgt alv elm s := by
  have hjlt : s.2.2.2.2.2 < off[w + 1]! := by simpa [decBf] using hb
  have hns : off[w + 1]! ≤ ns := hin.csr.csr.le_ns (show w + 1 ≤ n by omega)
  have hun : tgt[s.2.2.2.2.2]! < n := hin.csr.csr.target_lt' hw hjlt
  have hdu := hI.degLt _ hun
  have hspb := hI.spSc
  have hwide := hin.wide
  refine ⟨by rw [hin.tgtLen]; omega, by rw [hin.alvLen]; exact hun,
    by rw [helm]; exact hun, by rw [hI.degLen]; exact hun,
    by rw [hI.bhLen]; omega, by rw [hI.bvLen]; omega, by rw [hI.bnLen]; omega⟩

/-- **One slot of the scan preserves the invariant.** The three paths:
a dead target and an eliminated one are passed over, a surviving one
loses a degree and is pushed into its new bucket, which is
`Buck.push`. -/
theorem decI_step (hin : EIn n ns W G off tgt alv) (hw : w < n)
    (helm : elm.length = n) (hsc : sc₀ ≤ ns) {s : DS}
    (hI : DecI n ns W G off tgt alv elm D₀ w sc₀ ls₀ s)
    (hb : decBf off[w + 1]! s = true) :
    DecI n ns W G off tgt alv elm D₀ w sc₀ ls₀ (decStep tgt alv elm s) := by
  have hjlt : s.2.2.2.2.2 < off[w + 1]! := by simpa [decBf] using hb
  have hun : tgt[s.2.2.2.2.2]! < n := hin.csr.csr.target_lt' hw hjlt
  have hnothit : ¬ RamElim.hit (larr off) (larr tgt) (larr alv) (larr elm) w
      s.2.2.2.2.2 tgt[s.2.2.2.2.2]! :=
    RamElim.not_hit_self hin.csr hw hI.jlo hjlt
  have hjlo := hI.jlo
  have hjhi := hI.jhi
  have hspb := hI.spSc
  have hwide := hin.wide
  have hsplt : s.2.2.2.2.1 < n + W + 1 := by omega
  have hdeglen : tgt[s.2.2.2.2.2]! < s.1.length := by rw [hI.degLen]; exact hun
  by_cases hb1 : 0 < alv[tgt[s.2.2.2.2.2]!]!
  · by_cases hb2 : elm[tgt[s.2.2.2.2.2]!]! < 1
    · -- a surviving neighbour: the decrement, and the push into its new bucket
      have hstep : decStep tgt alv elm s =
          (s.1.set tgt[s.2.2.2.2.2]! (s.1[tgt[s.2.2.2.2.2]!]! - 1),
            s.2.1.set (s.1[tgt[s.2.2.2.2.2]!]! - 1) s.2.2.2.2.1,
            s.2.2.1.set s.2.2.2.2.1 tgt[s.2.2.2.2.2]!,
            s.2.2.2.1.set s.2.2.2.2.1 s.2.1[s.1[tgt[s.2.2.2.2.2]!]! - 1]!,
            s.2.2.2.2.1 + 1, s.2.2.2.2.2 + 1) := by
        simp only [decStep]; rw [if_pos hb1, if_pos hb2]
      have hEu : larr elm tgt[s.2.2.2.2.2]! = 0 := by simp only [larr_apply]; omega
      have hMu : larr alv tgt[s.2.2.2.2.2]! ≠ 0 := by simp only [larr_apply]; omega
      have hhitself : RamElim.hit (larr off) (larr tgt) (larr alv) (larr elm) w
          (s.2.2.2.2.2 + 1) tgt[s.2.2.2.2.2]! := ⟨hEu, hMu, s.2.2.2.2.2, hjlo, by omega, rfl⟩
      have hDu := hI.degLt _ hun
      have hD' : ∀ v < n,
          upd (larr s.1) tgt[s.2.2.2.2.2]! (s.1[tgt[s.2.2.2.2.2]!]! - 1) v ≤ n := by
        intro v hv
        by_cases hvu : v = tgt[s.2.2.2.2.2]!
        · rw [hvu, upd_self]; omega
        · rw [upd_of_ne _ hvu]; have := hI.degLt v hv; simp only [larr_apply]; omega
      have hpush := hI.buck.push
        (D' := upd (larr s.1) tgt[s.2.2.2.2.2]! (s.1[tgt[s.2.2.2.2.2]!]! - 1))
        (x := tgt[s.2.2.2.2.2]!) (d := s.1[tgt[s.2.2.2.2.2]!]! - 1) (m' := n)
        hun (by omega) (upd_self ..) (fun v hv => upd_of_ne _ hv) hD' (fun v hv _ => hv)
      have hl1 : larr (s.1.set tgt[s.2.2.2.2.2]! (s.1[tgt[s.2.2.2.2.2]!]! - 1))
          = upd (larr s.1) tgt[s.2.2.2.2.2]! (s.1[tgt[s.2.2.2.2.2]!]! - 1) :=
        larr_set hdeglen _
      have hl2 : larr (s.2.1.set (s.1[tgt[s.2.2.2.2.2]!]! - 1) s.2.2.2.2.1)
          = upd (larr s.2.1) (s.1[tgt[s.2.2.2.2.2]!]! - 1) s.2.2.2.2.1 :=
        larr_set (by rw [hI.bhLen]; omega) _
      have hl3 : larr (s.2.2.1.set s.2.2.2.2.1 tgt[s.2.2.2.2.2]!)
          = upd (larr s.2.2.1) s.2.2.2.2.1 tgt[s.2.2.2.2.2]! :=
        larr_set (by rw [hI.bvLen]; exact hsplt) _
      have hl4 : larr (s.2.2.2.1.set s.2.2.2.2.1 s.2.1[s.1[tgt[s.2.2.2.2.2]!]! - 1]!)
          = upd (larr s.2.2.2.1) s.2.2.2.2.1 (larr s.2.1 (s.1[tgt[s.2.2.2.2.2]!]! - 1)) :=
        larr_set (by rw [hI.bnLen]; exact hsplt) _
      have hlsnew : lsOf n (s.2.1.set (s.1[tgt[s.2.2.2.2.2]!]! - 1) s.2.2.2.2.1)
            (s.2.2.2.1.set s.2.2.2.2.1 s.2.1[s.1[tgt[s.2.2.2.2.2]!]! - 1]!)
          = lsOf n s.2.1 s.2.2.2.1 + 1 := by
        rw [lsOf, hl2, hl4]; exact hpush.ls_eq.symm
      rw [hstep]
      refine ⟨by simpa using hI.degLen, by simpa using hI.bhLen, by simpa using hI.bvLen,
        by simpa using hI.bnLen, ?_, ?_, ?_, ?_,
        by show off[w]! ≤ s.2.2.2.2.2 + 1; omega,
        by show s.2.2.2.2.2 + 1 ≤ off[w + 1]!; omega,
        by show s.2.2.2.2.1 + 1 + (off[w + 1]! - (s.2.2.2.2.2 + 1)) ≤ n + 1 + sc₀; omega,
        ?_, ?_⟩
      · show RamElim.Buck n n (larr elm) _ _ _ _ (s.2.2.2.2.1 + 1) _
        rw [hlsnew, hl1, hl2, hl3, hl4]
        exact hpush
      · intro v hv
        rw [get!_set _ _ _ _ hdeglen]
        by_cases hvu : v = tgt[s.2.2.2.2.2]!
        · rw [if_pos hvu]; omega
        · rw [if_neg hvu]; exact hI.degLt v hv
      · intro v hv hh
        rw [get!_set _ _ _ _ hdeglen]
        rcases RamElim.hit_succ hh with hh' | ⟨hveq, -, -⟩
        · have hvne : v ≠ tgt[s.2.2.2.2.2]! := by rintro rfl; exact hnothit hh'
          rw [if_neg hvne]; exact hI.hitDec v hv hh'
        · have hveq' : v = tgt[s.2.2.2.2.2]! := hveq
          rw [if_pos hveq', hveq', hI.hitKeep _ hun hnothit]
      · intro v hv hnh
        have hvne : v ≠ tgt[s.2.2.2.2.2]! := by rintro rfl; exact hnh hhitself
        rw [get!_set _ _ _ _ hdeglen, if_neg hvne]
        exact hI.hitKeep v hv (fun hc => hnh (RamElim.hit_mono hc))
      · show lsOf n (s.2.1.set _ _) (s.2.2.2.1.set _ _) ≤ ls₀ + (s.2.2.2.2.2 + 1 - off[w]!)
        rw [hlsnew]; have := hI.lsAcc; omega
      · show lsOf n (s.2.1.set _ _) (s.2.2.2.1.set _ _) + 1 ≤ s.2.2.2.2.1 + 1
        rw [hlsnew]; have := hI.lsSp; omega
    · -- an eliminated neighbour is passed over
      have hstep : decStep tgt alv elm s =
          (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2 + 1) := by
        simp only [decStep]; rw [if_pos hb1, if_neg hb2]
      have hEu : larr elm tgt[s.2.2.2.2.2]! ≠ 0 := by simp only [larr_apply]; omega
      rw [hstep]
      refine ⟨hI.degLen, hI.bhLen, hI.bvLen, hI.bnLen, hI.buck, hI.degLt, ?_, ?_,
        by show off[w]! ≤ s.2.2.2.2.2 + 1; omega,
        by show s.2.2.2.2.2 + 1 ≤ off[w + 1]!; omega,
        by show s.2.2.2.2.1 + (off[w + 1]! - (s.2.2.2.2.2 + 1)) ≤ n + 1 + sc₀; omega,
        by show lsOf n s.2.1 s.2.2.2.1 ≤ ls₀ + (s.2.2.2.2.2 + 1 - off[w]!)
           have := hI.lsAcc; omega,
        hI.lsSp⟩
      · intro v hv hh
        rcases RamElim.hit_succ hh with hh' | ⟨hveq, hE0, -⟩
        · exact hI.hitDec v hv hh'
        · exact absurd (show larr elm tgt[s.2.2.2.2.2]! = 0 from
            (show tgt[s.2.2.2.2.2]! = v from hveq.symm) ▸ hE0) hEu
      · exact fun v hv hnh => hI.hitKeep v hv (fun hc => hnh (RamElim.hit_mono hc))
  · -- a dead neighbour is passed over
    have hstep : decStep tgt alv elm s =
        (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2 + 1) := by
      simp only [decStep]; rw [if_neg hb1]
    have hMu : larr alv tgt[s.2.2.2.2.2]! = 0 := by simp only [larr_apply]; omega
    rw [hstep]
    refine ⟨hI.degLen, hI.bhLen, hI.bvLen, hI.bnLen, hI.buck, hI.degLt, ?_, ?_,
      by show off[w]! ≤ s.2.2.2.2.2 + 1; omega,
      by show s.2.2.2.2.2 + 1 ≤ off[w + 1]!; omega,
      by show s.2.2.2.2.1 + (off[w + 1]! - (s.2.2.2.2.2 + 1)) ≤ n + 1 + sc₀; omega,
      by show lsOf n s.2.1 s.2.2.2.1 ≤ ls₀ + (s.2.2.2.2.2 + 1 - off[w]!)
         have := hI.lsAcc; omega,
      hI.lsSp⟩
    · intro v hv hh
      rcases RamElim.hit_succ hh with hh' | ⟨hveq, -, hM0⟩
      · exact hI.hitDec v hv hh'
      · exact absurd (show larr alv v = 0 from
          (show v = tgt[s.2.2.2.2.2]! from hveq) ▸ hMu) hM0
    · exact fun v hv hnh => hI.hitKeep v hv (fun hc => hnh (RamElim.hit_mono hc))

/-- Every path of a slot moves the index on by one. -/
theorem decStep_snd (tgt alv elm : List ℕ) (s : DS) :
    (decStep tgt alv elm s).2.2.2.2.2 = s.2.2.2.2.2 + 1 := by
  by_cases h1 : 0 < alv[tgt[s.2.2.2.2.2]!]!
  · by_cases h2 : elm[tgt[s.2.2.2.2.2]!]! < 1
    · simp only [decStep]; rw [if_pos h1, if_pos h2]
    · simp only [decStep]; rw [if_pos h1, if_neg h2]
  · simp only [decStep]; rw [if_neg h1]

/-- **The row of the vertex being eliminated, scanned.** What it leaves
at the end of the row is `Elim.extract`'s two hypotheses, through
`RamElim.extract_of_scan`; what it costs is one `decC` per slot. -/
theorem decScan_le (hin : EIn n ns W G off tgt alv) (hw : w < n)
    (helm : elm.length = n) (hsc : sc₀ ≤ ns) :
    ∀ (fuel : ℕ) (s : DS), DecI n ns W G off tgt alv elm D₀ w sc₀ ls₀ s →
      off[w + 1]! - s.2.2.2.2.2 < fuel →
      decScan tgt alv elm off[w + 1]! s
        ≤ NRest.spec
            (fun t : DS => DecI n ns W G off tgt alv elm D₀ w sc₀ ls₀ t ∧
              t.2.2.2.2.2 = off[w + 1]!)
            (fun _ => liftACost ((off[w + 1]! - s.2.2.2.2.2) • iter decC
              + cu Currency.«while»)) := by
  have key := while_pot_le (P := decP tgt alv elm)
    (I := fun t => DecI n ns W G off tgt alv elm D₀ w sc₀ ls₀ t)
    (bf := decBf off[w + 1]!) (f := decF tgt alv elm)
    (V := fun t : DS => off[w + 1]! - t.2.2.2.2.2)
    (Φ := fun t : DS => (off[w + 1]! - t.2.2.2.2.2) • iter decC)
    (Φ' := fun t : DS => (off[w + 1]! - (t.2.2.2.2.2 + 1)) • iter decC)
    (C := fun _ => decC)
    (fun _ h hb => decI_range hin hw helm hsc h hb)
    (fun s h hb => by
      have hj : s.2.2.2.2.2 < off[w + 1]! := by simpa [decBf] using hb
      refine step_spec (s := s) (x := decStep tgt alv elm s) (C := fun _ => decC)
        (Φ := fun t : DS => (off[w + 1]! - t.2.2.2.2.2) • iter decC)
        (Φ' := fun t : DS => (off[w + 1]! - (t.2.2.2.2.2 + 1)) • iter decC)
        (V := fun t : DS => off[w + 1]! - t.2.2.2.2.2)
        (decF_le tgt alv elm s (decI_range hin hw helm hsc h hb))
        (decI_step hin hw helm hsc h hb) ?_ ?_
      · show off[w + 1]! - (decStep tgt alv elm s).2.2.2.2.2 < off[w + 1]! - s.2.2.2.2.2
        rw [decStep_snd]; omega
      · show (off[w + 1]! - (decStep tgt alv elm s).2.2.2.2.2) • iter decC
          ≤ (off[w + 1]! - (s.2.2.2.2.2 + 1)) • iter decC
        rw [decStep_snd])
    (fun s _ hb => by
      have hj : s.2.2.2.2.2 < off[w + 1]! := by simpa [decBf] using hb
      show iter decC + (off[w + 1]! - (s.2.2.2.2.2 + 1)) • iter decC
        ≤ (off[w + 1]! - s.2.2.2.2.2) • iter decC
      rw [show off[w + 1]! - s.2.2.2.2.2 = (off[w + 1]! - (s.2.2.2.2.2 + 1)) + 1 by omega,
        succ_nsmul]
      exact le_of_eq (by ac_rfl))
  intro fuel s hI hf
  refine le_trans (key fuel s hI hf) (spec_mono ?_ (fun _ _ => le_rfl))
  rintro t ⟨hIt, hbf⟩
  have hnb : ¬ t.2.2.2.2.2 < off[w + 1]! := by simpa [decBf] using hbf
  exact ⟨hIt, by have := hIt.jhi; omega⟩

end ScanWalk

/-! ## 4. The elimination loop -/

section Loop

open Lax13Proofs.Reasoning.Lib (upd upd_self upd_of_ne)

/-! ### 4.1 One loop lemma more: the price chosen per state

`ElimSynth2.while_pot_le` asks for **one** `C` and **one** `Φ'` given
uniformly in the state. The elimination turn branches into four cases
of four different prices, and the price of an extraction depends on the
length of the row it scans; so the loop rule it needs is the same one
with the two chosen per state. -/

theorem while_pot_le' {σ : Type} {P I : σ → Prop} {bf : σ → Bool} {f : σ → NRest σ ECost}
    {V : σ → ℕ} {Φ : σ → ACost String ℕ}
    (hP : ∀ s, I s → bf s = true → P s)
    (hstep : ∀ s, I s → bf s = true → ∃ C Φ' : ACost String ℕ,
      f s ≤ NRest.spec (fun t => I t ∧ V t < V s ∧ Φ t ≤ Φ') (fun _ => liftACost C) ∧
      iter C + Φ' ≤ Φ s) :
    ∀ (fuel : ℕ) (s : σ), I s → V s < fuel →
      irWhileIT (fun t => bf t = true → P t) bf f s
        ≤ NRest.spec (fun t => I t ∧ bf t = false)
            (fun _ => liftACost (Φ s + cu Currency.«while»)) := by
  classical
  have hex : ∀ s : σ, ∃ p : ACost String ℕ × ACost String ℕ, I s → bf s = true →
      f s ≤ NRest.spec (fun t => I t ∧ V t < V s ∧ Φ t ≤ p.2) (fun _ => liftACost p.1) ∧
      iter p.1 + p.2 ≤ Φ s := by
    intro s
    by_cases h : I s ∧ bf s = true
    · obtain ⟨C, Φ', h1, h2⟩ := hstep s h.1 h.2
      exact ⟨(C, Φ'), fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨(0, 0), fun hI hb => absurd ⟨hI, hb⟩ h⟩
  choose p hp using hex
  exact while_pot_le (C := fun s => (p s).1) (Φ' := fun s => (p s).2) hP
    (fun s hI hb => (hp s hI hb).1) (fun s hI hb => (hp s hI hb).2)

/-! ### 4.2 The invariant, in `RamElim`'s vocabulary

`RamElim.ElimSt` at the list layer, minus the `ls` and `sc` cells that
2B′/D-a drops: both are *functions* of the state, `lsOf` off the bucket
arrays and `scOf` off the elimination flags. -/

/-- What holds of the eleven components at every point of the
elimination. -/
structure ElimI (n ns W : ℕ) (G : SimpleGraph (Fin n)) (off tgt alv : List ℕ)
    (e : ES) : Prop where
  /-- The degrees. -/
  degLen : e.1.length = n
  /-- The elimination flags. -/
  elmLen : e.2.1.length = n
  /-- The ranks. -/
  rnkLen : e.2.2.1.length = n
  /-- The extraction degrees. -/
  idgLen : e.2.2.2.1.length = n
  /-- The bucket heads. -/
  bhLen : e.2.2.2.2.1.length = n + 1
  /-- The arena's vertex column. -/
  bvLen : e.2.2.2.2.2.1.length = n + W + 1
  /-- The arena's link column. -/
  bnLen : e.2.2.2.2.2.2.1.length = n + W + 1
  /-- **`RamElim.Elim` on the nose**: the whole mathematics of the
  elimination, consumed. -/
  elim : RamElim.Elim G (larr alv) (larr e.2.1) (larr e.1) (larr e.2.2.1) (larr e.2.2.2.1)
    e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2
  /-- …and `RamElim.Buck` on the buckets. -/
  buck : RamElim.Buck n n (larr e.2.1) (larr e.1) (larr e.2.2.2.2.1) (larr e.2.2.2.2.2.1)
    (larr e.2.2.2.2.2.2.1) e.2.2.2.2.2.2.2.1 (lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1)
  /-- Every degree is a vertex number. -/
  degLt : ∀ u < n, e.1[u]! < n
  /-- **The arena never overflows**: one slot per vertex and one per
  slot already scanned. -/
  spSc : e.2.2.2.2.2.2.2.1 ≤ n + 1 + scOf n (larr off) (larr alv) e.2.1
  /-- …and always has room for the sentinel. -/
  lsSp : lsOf n e.2.2.2.2.1 e.2.2.2.2.2.2.1 + 1 ≤ e.2.2.2.2.2.2.2.1
  /-- The pointer is a degree. -/
  mindLe : e.2.2.2.2.2.2.2.2.2.1 ≤ n
  /-- And the bound is one too. -/
  kmaxLe : e.2.2.2.2.2.2.2.2.2.2 ≤ n

/-! ### 4.3 The two turns that do not touch the row

A pointer bump and a stale pop are straight-line blocks: one result
each, so their prices are exact. -/

/-- **The pointer moves up over an empty bucket.** -/
def bumpStep : ES → ES := fun e =>
  (e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1, e.2.2.2.2.2.1, e.2.2.2.2.2.2.1,
    e.2.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.2.2.1 + 1,
    e.2.2.2.2.2.2.2.2.2.2)

/-- **The head slot of the bucket the pointer names is dropped.** -/
def staleStep : ES → ES := fun e =>
  (e.1, e.2.1, e.2.2.1, e.2.2.2.1,
    e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.1[e.2.2.2.2.1[e.2.2.2.2.2.2.2.2.2.1]!]!,
    e.2.2.2.2.2.1, e.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.2.1,
    e.2.2.2.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.2.2.2)

/-- What a pointer bump pays: the head read, the branch, the bump and
the eleven-component tuple. -/
def bumpC : ACost String ℕ := cu Currency.aget + cu Currency.ite + cu Currency.add
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip + cu Currency.skip

/-- What a stale pop pays: the head, the slot's vertex and link, the
head write, the flag and degree tests, and the tuple. -/
def staleC : ACost String ℕ := cu Currency.aget + cu Currency.ite + cu Currency.aget
  + cu Currency.aget + cu Currency.aset + cu Currency.aget + cu Currency.ite
  + cu Currency.aget + cu Currency.ite
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip + cu Currency.skip

theorem elimTurnF_bump_le (n : ℕ) (off tgt alv : List ℕ) (e : ES)
    (hbh : e.2.2.2.2.2.2.2.2.2.1 < e.2.2.2.2.1.length)
    (hbhm : e.2.2.2.2.1[e.2.2.2.2.2.2.2.2.2.1]! = 0) :
    elimTurnF n off tgt alv e
      ≤ NRest.consume (NRest.returnT (bumpStep e)) (liftACost bumpC) := by
  refine le_of_eq ?_
  simp only [elimTurnF, bumpStep, pack11, mopAget_def, mopSucc_eq, mopBinop_def,
    mopPair_def, irIf_def, NRest.assert_pos hbh, NRest.returnT_bindT,
    NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, hbhm, decide_eq_true_eq,
    if_pos, bumpC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

theorem elimTurnF_stale_le (n : ℕ) (off tgt alv : List ℕ) (e : ES)
    (hbh : e.2.2.2.2.2.2.2.2.2.1 < e.2.2.2.2.1.length)
    (hbhm : e.2.2.2.2.1[e.2.2.2.2.2.2.2.2.2.1]! ≠ 0)
    (hbv : e.2.2.2.2.1[e.2.2.2.2.2.2.2.2.2.1]! < e.2.2.2.2.2.1.length)
    (hbn : e.2.2.2.2.1[e.2.2.2.2.2.2.2.2.2.1]! < e.2.2.2.2.2.2.1.length)
    (helm : e.2.2.2.2.2.1[e.2.2.2.2.1[e.2.2.2.2.2.2.2.2.2.1]!]! < e.2.1.length)
    (hdeg : e.2.2.2.2.2.1[e.2.2.2.2.1[e.2.2.2.2.2.2.2.2.2.1]!]! < e.1.length)
    (hstale : ¬ (e.2.1[e.2.2.2.2.2.1[e.2.2.2.2.1[e.2.2.2.2.2.2.2.2.2.1]!]!]! = 0 ∧
      e.1[e.2.2.2.2.2.1[e.2.2.2.2.1[e.2.2.2.2.2.2.2.2.2.1]!]!]!
        = e.2.2.2.2.2.2.2.2.2.1)) :
    elimTurnF n off tgt alv e
      ≤ NRest.consume (NRest.returnT (staleStep e)) (liftACost staleC) := by
  have hbase : liftACost (cu Currency.aget + cu Currency.ite + cu Currency.aget
      + cu Currency.aget + cu Currency.aset + cu Currency.aget + cu Currency.ite
      + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
      + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
      + cu Currency.skip + cu Currency.skip) ≤ liftACost staleC := by
    simp only [staleC, liftACost_add, liftACost_cu]
    refine le_trans (cost_le_add _ (irUnit Currency.aget + irUnit Currency.ite))
      (le_of_eq ?_)
    ac_rfl
  by_cases hew : e.2.1[e.2.2.2.2.2.1[e.2.2.2.2.1[e.2.2.2.2.2.2.2.2.2.1]!]!]! < 1
  · have hdw : e.1[e.2.2.2.2.2.1[e.2.2.2.2.1[e.2.2.2.2.2.2.2.2.2.1]!]!]!
        ≠ e.2.2.2.2.2.2.2.2.2.1 := fun hc => hstale ⟨by omega, hc⟩
    refine le_of_eq ?_
    simp only [elimTurnF, staleStep, pack11, mopAget_def, mopAset_def, mopPair_def,
      irIf_def, NRest.assert_pos hbh, NRest.assert_pos hbv, NRest.assert_pos hbn,
      NRest.assert_pos helm, NRest.assert_pos hdeg, NRest.returnT_bindT,
      NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
      decide_eq_true_eq, if_neg hbhm, if_pos hew, if_neg hdw, staleC, liftACost_add,
      liftACost_cu]
    congr 1
    ac_rfl
  · simp only [elimTurnF, staleStep, pack11, mopAget_def, mopAset_def, mopPair_def,
      irIf_def, NRest.assert_pos hbh, NRest.assert_pos hbv, NRest.assert_pos hbn,
      NRest.assert_pos helm, NRest.returnT_bindT,
      NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
      decide_eq_true_eq, if_neg hbhm, if_neg hew]
    refine NRest.consume_mono le_rfl (le_trans (le_of_eq ?_) hbase)
    simp only [liftACost_add, liftACost_cu]
    ac_rfl

/-! ### 4.4 The extraction

The one turn whose price is not a constant: it scans a row, so it is
the only body of the engine that is not a straight-line block. What it
*is* is a straight-line prefix, one `decScan`, and a straight-line
suffix — and `IrLoop.bindT_consume_right` is what says the suffix's
charges come out in front, which is the normal form `decScan_le` can
then be threaded into. -/

/-- The head slot of the bucket the pointer names. -/
abbrev slotOf (e : ES) : ℕ := e.2.2.2.2.1[e.2.2.2.2.2.2.2.2.2.1]!

/-- The vertex that slot holds. -/
abbrev vtxOf (e : ES) : ℕ := e.2.2.2.2.2.1[slotOf e]!

/-- The state the row scan of an extraction starts in: the popped
bucket heads, the arena, and the index at the top of the row. -/
def takeScan0 (off : List ℕ) (e : ES) : DS :=
  (e.1, e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.1[slotOf e]!,
    e.2.2.2.2.2.1, e.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.1, off[vtxOf e]!)

/-- The state an extraction leaves, as a function of what its row scan
returns: the flag, the rank and the extraction degree stamped, the
counter up, the pointer down and the bound raised — `kmax + (mind −
kmax)` being `max kmax mind` without a branch (2B′/D-b). -/
def takeState (n : ℕ) (e : ES) (r : DS) : ES :=
  (r.1, e.2.1.set (vtxOf e) 1,
    e.2.2.1.set (vtxOf e) (n - 1 - e.2.2.2.2.2.2.2.2.1),
    e.2.2.2.1.set (vtxOf e) e.2.2.2.2.2.2.2.2.2.1,
    r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1,
    e.2.2.2.2.2.2.2.2.1 + 1, e.2.2.2.2.2.2.2.2.2.1 - 1,
    e.2.2.2.2.2.2.2.2.2.2 + (e.2.2.2.2.2.2.2.2.2.1 - e.2.2.2.2.2.2.2.2.2.2))

/-- What an extraction pays outside its row scan: eight reads, four
writes, four branches, three bumps, four subtractions and the three
tuples. -/
def takeC0 : ACost String ℕ :=
  cu Currency.aget + cu Currency.aget + cu Currency.aget + cu Currency.aget
  + cu Currency.aget + cu Currency.aget + cu Currency.aget + cu Currency.aget
  + cu Currency.aset + cu Currency.aset + cu Currency.aset + cu Currency.aset
  + cu Currency.ite + cu Currency.ite + cu Currency.ite + cu Currency.ite
  + cu Currency.add + cu Currency.add + cu Currency.add
  + cu Currency.sub + cu Currency.sub + cu Currency.sub + cu Currency.sub
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip + cu Currency.skip + cu Currency.skip

/-- **The extraction, in normal form.** -/
theorem elimTurnF_take_eq (n : ℕ) (off tgt alv : List ℕ) (e : ES)
    (hbh : e.2.2.2.2.2.2.2.2.2.1 < e.2.2.2.2.1.length)
    (hbv : slotOf e < e.2.2.2.2.2.1.length)
    (hbn : slotOf e < e.2.2.2.2.2.2.1.length)
    (helm : vtxOf e < e.2.1.length) (hdeg : vtxOf e < e.1.length)
    (hrnk : vtxOf e < e.2.2.1.length) (hidg : vtxOf e < e.2.2.2.1.length)
    (halv : vtxOf e < alv.length)
    (hoff : vtxOf e < off.length) (hoff' : vtxOf e + 1 < off.length)
    (hslot : ¬ slotOf e = 0)
    (hew : e.2.1[vtxOf e]! < 1) (hdw : e.1[vtxOf e]! = e.2.2.2.2.2.2.2.2.2.1)
    (haw : 0 < alv[vtxOf e]!) :
    elimTurnF n off tgt alv e
      = NRest.consume
          (NRest.bindT
            (decScan tgt alv (e.2.1.set (vtxOf e) 1) off[vtxOf e + 1]!
              (takeScan0 off e))
            (fun r => NRest.returnT (takeState n e r)))
          (liftACost takeC0) := by
  simp only [elimTurnF, elimVertexF, takeState, takeScan0, slotOf, vtxOf, pack11, pack6,
    pack5d, mopAget_def, mopAset_def, mopSucc_eq, mopPred_eq, mopAddIn_eq, mopBinop_def,
    mopPair_def, irIf_def, NRest.assert_pos hbh, NRest.assert_pos hbv,
    NRest.assert_pos hbn, NRest.assert_pos helm, NRest.assert_pos hdeg,
    NRest.assert_pos hrnk, NRest.assert_pos hidg, NRest.assert_pos halv,
    NRest.assert_pos hoff, NRest.assert_pos hoff', NRest.returnT_bindT,
    NRest.bindT_assoc_acost, NRest.bindT_consume NRest.addSupContinuousB_acost,
    bindT_consume_right NRest.addSupContinuousB_acost,
    NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, Lax13Proofs.Imp.Bop.apply_sub,
    binopCurrency_add, binopCurrency_sub, decide_eq_true_eq, if_neg hslot, if_pos hew,
    if_pos hdw, if_pos haw, takeC0, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

/-- What an extraction on a **dead** vertex pays: the same, minus the
row load, the scan's own exit test and the two tuples the load
assembles. A dead vertex is isolated in the arena, so its row is never
looked at. -/
def deadC : ACost String ℕ :=
  cu Currency.aget + cu Currency.aget + cu Currency.aget + cu Currency.aget
  + cu Currency.aget + cu Currency.aget
  + cu Currency.aset + cu Currency.aset + cu Currency.aset + cu Currency.aset
  + cu Currency.ite + cu Currency.ite + cu Currency.ite + cu Currency.ite
  + cu Currency.add + cu Currency.add
  + cu Currency.sub + cu Currency.sub + cu Currency.sub + cu Currency.sub
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip
  + cu Currency.skip + cu Currency.skip

/-- **The extraction of a dead vertex**, whose row is not scanned: a
straight-line block, so its price is exact. -/
theorem elimTurnF_takeDead_le (n : ℕ) (off tgt alv : List ℕ) (e : ES)
    (hbh : e.2.2.2.2.2.2.2.2.2.1 < e.2.2.2.2.1.length)
    (hbv : slotOf e < e.2.2.2.2.2.1.length)
    (hbn : slotOf e < e.2.2.2.2.2.2.1.length)
    (helm : vtxOf e < e.2.1.length) (hdeg : vtxOf e < e.1.length)
    (hrnk : vtxOf e < e.2.2.1.length) (hidg : vtxOf e < e.2.2.2.1.length)
    (halv : vtxOf e < alv.length)
    (hslot : ¬ slotOf e = 0)
    (hew : e.2.1[vtxOf e]! < 1) (hdw : e.1[vtxOf e]! = e.2.2.2.2.2.2.2.2.2.1)
    (haw : ¬ 0 < alv[vtxOf e]!) :
    elimTurnF n off tgt alv e
      ≤ NRest.consume (NRest.returnT (takeState n e (takeScan0 off e)))
          (liftACost deadC) := by
  refine le_of_eq ?_
  simp only [elimTurnF, elimVertexF, takeState, takeScan0, slotOf, vtxOf, pack11, pack6,
    pack5d, mopAget_def, mopAset_def, mopSucc_eq, mopPred_eq, mopAddIn_eq, mopBinop_def,
    mopPair_def, irIf_def, NRest.assert_pos hbh, NRest.assert_pos hbv,
    NRest.assert_pos hbn, NRest.assert_pos helm, NRest.assert_pos hdeg,
    NRest.assert_pos hrnk, NRest.assert_pos hidg, NRest.assert_pos halv,
    NRest.returnT_bindT, NRest.bindT_assoc_acost,
    NRest.bindT_consume NRest.addSupContinuousB_acost,
    bindT_consume_right NRest.addSupContinuousB_acost,
    NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, Lax13Proofs.Imp.Bop.apply_sub,
    binopCurrency_add, binopCurrency_sub, decide_eq_true_eq, if_neg hslot, if_pos hew,
    if_pos hdw, if_neg haw, deadC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

/-! ### 4.6 Refute before prove — the four steps against the golden twin

The three step functions above (`bumpStep`, `staleStep`, `takeState`)
are **authored**: nothing yet proves them right, since `ElimI`'s
preservation is the part of E2 this wave leaves open. So they are
falsified first, in the standing practice's form: a turn dispatched to
the case its guards name is checked, state by state, against 2B's
computable twin `ElimSynth.elimTurnTw` — which is itself guard-checked
against `RamElim.Demo`'s runs of the *compiled machine program*. -/

section Refute

/-- The twin's eleven-field state, flattened onto the loop's eleven
components. -/
def eflat (e : ElimSynth.ESt) : ES :=
  (e.deg, e.elm, e.rnk, e.idg, e.bk.1, e.bk.2.1, e.bk.2.2.1, e.bk.2.2.2, e.cnt, e.mind,
    e.kmax)

/-- **2B″/D-a — eleven components outrun `DecidableEq`.** Instance
search for the product's decidable equality gives up at eight, so the
differential test compares the eleven components by hand. -/
def esEq (a b : ES) : Bool :=
  (a.1 == b.1) && (a.2.1 == b.2.1) && (a.2.2.1 == b.2.2.1) && (a.2.2.2.1 == b.2.2.2.1)
    && (a.2.2.2.2.1 == b.2.2.2.2.1) && (a.2.2.2.2.2.1 == b.2.2.2.2.2.1)
    && (a.2.2.2.2.2.2.1 == b.2.2.2.2.2.2.1) && (a.2.2.2.2.2.2.2.1 == b.2.2.2.2.2.2.2.1)
    && (a.2.2.2.2.2.2.2.2.1 == b.2.2.2.2.2.2.2.2.1)
    && (a.2.2.2.2.2.2.2.2.2.1 == b.2.2.2.2.2.2.2.2.2.1)
    && (a.2.2.2.2.2.2.2.2.2.2 == b.2.2.2.2.2.2.2.2.2.2)

/-- The row scan of an extraction, as a fuelled function of `decStep` —
the twin of `decScan`, which is what the differential test can run. -/
def decRun (tgt alv elm : List ℕ) (jend : ℕ) : ℕ → DS → DS
  | 0, s => s
  | fuel + 1, s =>
    if s.2.2.2.2.2 < jend then decRun tgt alv elm jend fuel (decStep tgt alv elm s) else s

/-- **One turn, dispatched to the case its guards name** — the four
cases of §4.3–§4.4 assembled into the function `elimTurnF` is claimed
to compute. -/
def turnStep (n : ℕ) (off tgt alv : List ℕ) (e : ES) : ES :=
  if slotOf e = 0 then bumpStep e
  else if e.2.1[vtxOf e]! < 1 ∧ e.1[vtxOf e]! = e.2.2.2.2.2.2.2.2.2.1 then
    if 0 < alv[vtxOf e]! then
      takeState n e (decRun tgt alv (e.2.1.set (vtxOf e) 1) off[vtxOf e + 1]!
        (off[vtxOf e + 1]! - off[vtxOf e]!) (takeScan0 off e))
    else takeState n e (takeScan0 off e)
  else staleStep e

/-- The demo's degrees and buckets, from 2B's twins: the state the
elimination loop starts in. -/
def demoE0 (a2 : ℕ) : ElimSynth.ESt :=
  let deg := (ElimSynth.initDegTw 5 demoOff demoTgt (demoAlv a2) 30
    (List.replicate 5 0, 0)).1
  let b := (ElimSynth.initBuckTw 5 deg 30
    ((List.replicate 6 0, List.replicate 16 0, List.replicate 16 0, 1), 0)).1
  ⟨deg, List.replicate 5 0, List.replicate 5 0, List.replicate 5 0, b, 0, 0, 0⟩

/-- The twin's run, turn by turn, stopping where the loop's own guard
does. -/
def demoRun (a2 : ℕ) : ℕ → ElimSynth.ESt
  | 0 => demoE0 a2
  | k + 1 =>
    let e := demoRun a2 k
    if e.cnt < 5 then ElimSynth.elimTurnTw 5 demoOff demoTgt (demoAlv a2) e else e

/-- The turn under test agrees with the twin at the `k`-th state. -/
def turnAgrees (a2 k : ℕ) : Bool :=
  let e := demoRun a2 k
  if e.cnt < 5 then
    esEq (turnStep 5 demoOff demoTgt (demoAlv a2) (eflat e))
      (eflat (ElimSynth.elimTurnTw 5 demoOff demoTgt (demoAlv a2) e))
  else true

-- **The differential test.** Every turn of the demo's run, at both
-- masks: mask on, the triangle-plus-path; mask off at `2`, which
-- breaks the arena in two and leaves `2` isolated. **All four cases
-- are exercised**: mask `1` runs bump·take·bump·take·bump·bump·take·
-- take·take, and mask `0` runs dead·bump·take·take·bump·stale·take·
-- take — so the dead extraction and the stale pop, which the masked
-- arena is what produces, are both covered.
#guard (List.range 34).all (turnAgrees 1)
#guard (List.range 34).all (turnAgrees 0)

-- …and the run really does reach the exit, with the answers 2B
-- guard-checked against the compiled machine program.
#guard (demoRun 1 34).cnt = 5
#guard (demoRun 1 34).rnk = [0, 1, 2, 3, 4]
#guard (demoRun 1 34).kmax = 2
#guard (demoRun 0 34).rnk = [0, 1, 4, 2, 3]
#guard (demoRun 0 34).kmax = 1

/-! #### Negative controls

Two transpositions the authored steps could plausibly have made, each
one a different engine. -/

/-- The rank stamped **upwards** instead of down: the engine's ranks
count down from `n − 1`, and a run that counted up is a different
ranking. -/
def takeStateWrongR (_n : ℕ) (e : ES) (r : DS) : ES :=
  (r.1, e.2.1.set (vtxOf e) 1, e.2.2.1.set (vtxOf e) e.2.2.2.2.2.2.2.2.1,
    e.2.2.2.1.set (vtxOf e) e.2.2.2.2.2.2.2.2.2.1,
    r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1,
    e.2.2.2.2.2.2.2.2.1 + 1, e.2.2.2.2.2.2.2.2.2.1 - 1,
    e.2.2.2.2.2.2.2.2.2.2 + (e.2.2.2.2.2.2.2.2.2.1 - e.2.2.2.2.2.2.2.2.2.2))

/-- The stale pop that writes the head **before** it reads the link —
the transposition 2B's `pushTwWrong` exhibits, on the popping side. -/
def staleStepWrong : ES → ES := fun e =>
  (e.1, e.2.1, e.2.2.1, e.2.2.2.1,
    e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.1[(e.2.2.2.2.1.set e.2.2.2.2.2.2.2.2.2.1 0)[e.2.2.2.2.2.2.2.2.2.1]!]!,
    e.2.2.2.2.2.1, e.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.2.1,
    e.2.2.2.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.2.2.2)

/-- The turn with one of the two transpositions in it. -/
def turnStepWrong (rankUp : Bool) (n : ℕ) (off tgt alv : List ℕ) (e : ES) : ES :=
  if slotOf e = 0 then bumpStep e
  else if e.2.1[vtxOf e]! < 1 ∧ e.1[vtxOf e]! = e.2.2.2.2.2.2.2.2.2.1 then
    if rankUp then
      (if 0 < alv[vtxOf e]! then
        takeStateWrongR n e (decRun tgt alv (e.2.1.set (vtxOf e) 1) off[vtxOf e + 1]!
          (off[vtxOf e + 1]! - off[vtxOf e]!) (takeScan0 off e))
      else takeStateWrongR n e (takeScan0 off e))
    else turnStep n off tgt alv e
  else if rankUp then staleStep e else staleStepWrong e

/-- The wrong turn parts from the twin at the `k`-th state. -/
def turnParts (rankUp : Bool) (a2 k : ℕ) : Bool :=
  let e := demoRun a2 k
  if e.cnt < 5 then
    esEq (turnStepWrong rankUp 5 demoOff demoTgt (demoAlv a2) (eflat e))
      (eflat (ElimSynth.elimTurnTw 5 demoOff demoTgt (demoAlv a2) e))
  else true

-- **Both controls are caught** inside the run — the rank at either
-- mask, the pop at mask `0`, which is the only one of the two runs
-- that reaches a stale slot.
#guard ¬ (List.range 34).all (turnParts true 1)
#guard ¬ (List.range 34).all (turnParts false 0)
#guard (List.range 34).all (turnParts false 1)

end Refute

/-! ### 4.5 The four prices, cashed

The constants are **computed** from the per-turn accounts by `decide
+kernel`, not tuned. They are what the potential of `RamElim`'s own
walk — `40 · (n + 1 − mind) + 40 · ls + 100 · (ns − sc) + 80 · (n −
cnt)` — is denominated in at this layer. -/

/-- A pointer bump, iteration included: the first term of the potential
(`RamElim.Pot`'s `40`). -/
theorem cash_bumpC : Codegen.cash (iter bumpC) = 25 := by decide +kernel

/-- A stale pop: the second term (`RamElim.Pot`'s `40`). -/
theorem cash_staleC : Codegen.cash (iter staleC) = 44 := by decide +kernel

/-- One slot of a row scan: the third term is this plus the second
(`RamElim.Pot`'s `100`). -/
theorem cash_decC : Codegen.cash (iter decC) = 60 := by decide +kernel

/-- An extraction outside its scan, the scan's exit test included: the
fourth term is this plus the first (`RamElim.Pot`'s `80`). -/
theorem cash_takeC : Codegen.cash (iter (takeC0 + cu Currency.«while»)) = 107 := by
  decide +kernel

/-- An extraction on a dead vertex, which the fourth term also has to
cover. -/
theorem cash_deadC : Codegen.cash (iter deadC) = 88 := by decide +kernel

-- The four coefficients of the potential, and the elimination loop's
-- budget they add up to: `A₁ = 25`, `A₂ = 44`, `A₃ = 60 + 44 = 104`,
-- `A₄ = 107 + 25 = 132`, so `(n+1)·A₁ + ns·A₃ + n·A₄ + 4`, that is
-- `157 n + 104 ns + 29`, against `RamElim.elimLoop_spec`'s hand-walked
-- `160 n + 100 ns + 52`. The two are within a percent of each other at
-- the demo's size — the state-as-resource `skip`s of 2B′/F-a are paid
-- once per turn here and the machine's `ls` bookkeeping is not.
#guard 60 + 44 = 104
#guard 107 + 25 = 132
#guard 88 ≤ 44 + 132
#guard 25 * (5 + 1) + 104 * 10 + 132 * 5 + 4 = 1854
#guard 160 * 5 + 100 * 10 + 52 = 1852
#guard 25 * (5 + 1) + 104 * 10 + 132 * 5 + 4 = 157 * 5 + 104 * 10 + 29

end Loop

/-! ## 5. What is landed and what is not (2B″)

**Debt E2's inner half — paid.** The row scan of an extraction is
walked: `DecI` is `RamElim.DecInv` at the list layer, `decI_step` is
its three paths (`Buck.push` for a surviving neighbour, nothing for an
eliminated or a dead one) and `decScan_le` runs it to the end of the
row. What it leaves at `j = off[w+1]` is exactly the pair of
hypotheses `RamElim.extract_of_scan` consumes, so `Elim.extract` is one
step away. `RamElim.Elim`, `RamElim.Buck` and `RamElim.hit` are
consumed throughout, never re-proved.

**Debt E1's slot term — paid.** `decC` is the exact price of a slot
(`cash (iter decC) = 56`), and `decScan_le` charges `rowLen` of them.

**The turn's four prices — paid.** `elimTurnF_bump_le`,
`elimTurnF_stale_le` and `elimTurnF_takeDead_le` are exact one-result
bounds; `elimTurnF_take_eq` puts the one turn that is *not* a
straight-line block into the normal form
`consume (bindT (decScan …) (returnT ∘ takeState)) takeC0`, which is
the shape `decScan_le` threads into by `bindT_spec_le`. That
normalization — a nested `while` inside a branch inside a body — was
the structural unknown of this wave; `Sepref.bindT_consume_right` is
what carries the suffix's charges out in front.

**The loop rule the four cases need — landed.** `while_pot_le'` is
`ElimSynth2.while_pot_le` with the price and the continuation's bound
chosen *per state*: the elimination turn branches into four cases of
four different prices, and the price of an extraction depends on the
row it scans, so the uniform `(C := …) (Φ' := …)` of 2B′ cannot state
it.

**Refute before prove — done for the authored steps.** `bumpStep`,
`staleStep` and `takeState` are authored, and `ElimI`'s preservation is
exactly what this wave does not prove; so §4.6 falsifies them first,
turn by turn against 2B's guard-checked twin `ElimSynth.elimTurnTw`, at
both masks and over all four cases, with two negative controls (the
rank stamped upwards, the pop that writes the head before it reads the
link). Both controls part from the twin inside the run; the steps
themselves agree at every turn. So what is left of E2 is the *proof*
that the invariant survives, not the question of what the steps are.

**What is left of E1/E2.** Three things, all of them now mechanical:

1. `ElimI`'s preservation across the four cases — `Elim.bump` with
   `Buck.no_deg` for the pointer, `Buck.pop` for the two pops, and
   `Elim.extract` with `extract_of_scan` for the extraction. `ElimI`
   is stated above and every hypothesis those four lemmas ask for is a
   clause of it.
2. The amortization, in `while_pot_le'`'s form, out of the potential
   `A₁ · (n + 1 − mind) + A₂ · ls + A₃ · (ns − sc) + A₄ · (n − cnt)`
   with `A₁ = iter bumpC` (25), `A₂ = iter staleC` (44),
   `A₃ = iter decC + A₂` (104)
   and `A₄ = iter (takeC0 + cu «while») + A₁` (132) — the four inequalities
   the cases need are then `iter bumpC ≤ A₁`, `iter staleC ≤ A₂`,
   `iter deadC ≤ A₂ + A₄` and, for a live extraction with a row of `L`
   slots and `p ≤ L` pushes, `L · iter decC + p · A₂ ≤ A₂ + L · A₃`,
   each true by construction. `lsOf` and `scOf` are the `ls`/`sc` the
   potential reads off the state (2B′/D-a); `DecI.lsAcc` is the
   `p ≤ L` the fourth needs.
3. The exit reading — `RamElim.elimExit_read`'s list-layer twin, which
   is `Elim.cert`, `Elim.taken` and **`Elim.rank_lt`** read off `ElimI`
   at `cnt = n`. The rank bound is a clause of the invariant from the
   start, so nothing has to be re-run to recover it.

**Debt F1 — not started.** The fill pass's `InCsr` walk
(`ElimSynth2` §4.3) is untouched by this wave.

**The whole-engine export — not stated.** It needs E1/E2's exit reading
and F1; with them, its five phases are `ElimSynth.degPass_adeg`,
`ElimSynth2.buckPass_spec`, the elimination loop's export,
`ElimSynth2.offPass_spec` and the fill's, and its cost is
`36n+23ns+4`, `31n+4`, the loop's budget, `28n+4` and the fill's. -/

/-! ## 6. Axioms -/

/-- info: 'Lax3Proofs.Refine.ElimSynth4.decScan_le' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms decScan_le

/-- info: 'Lax3Proofs.Refine.ElimSynth4.elimTurnF_take_eq' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms elimTurnF_take_eq

/-- info: 'Lax3Proofs.Refine.ElimSynth4.while_pot_le'' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms while_pot_le'

/-- info: 'Lax3Proofs.Refine.ElimSynth4.decI_step' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms decI_step

/-- info: 'Lax3Proofs.Refine.ElimSynth4.elimTurnF_takeDead_le' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms elimTurnF_takeDead_le

end Lax3Proofs.Refine.ElimSynth4
