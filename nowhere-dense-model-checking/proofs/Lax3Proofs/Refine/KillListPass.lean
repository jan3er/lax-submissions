import Lax3Proofs.Refine.KillPass
import Lax3Proofs.TgtWidenProbe
import Lax3Proofs.Refine.G2ExistsRevalidation

/-!
**The kill list, walked** — wave R1.8-T3-flip, scope (a).

`RamDriver.killListCom` is the program: the turn's kill set, enumerated
**once each** into `klName j` and counted into `kkName j`, by the same
guarded walk of the padded batch buffer as `RamDriver.killCom`, with a
membership scan of the already-emitted prefix as the dedupe. This file
proves its walk; the threading into `clusterCom` (the `KillListStep`
surface, the frames, the turn charge) is the wave's next checkpoint.

# Why a list, and why the dedupe is load-bearing

The atom pass's kill walk
(`Refine.ScatterDeadFold.sum_bit_eq_ncard_inter`) sums child-table bits
over an enumeration of the kill set, and its `hinj` hypothesis is
repetition-freeness: a repeated entry counts a kill twice. The buffer
cannot serve directly — the padding repeats its first entry, and
`RamDriverCluster.ClusterWa` pins only the buffer's *range* — and
strengthening the landed padding would move `EnumStep`'s postcondition.
§0 compiles both halves of that: the deduped walk reports the kill set's
size, and the same walk with the scan dropped emits a duplicate.

# The two walks

§1 is the inner scan: `kf` ends holding whether the probed value occurs
in the emitted prefix, an accumulating invariant over `kt`. §2 is the
buffer loop: the emitted prefix is, at every counter value, a
repetition-free sound-and-complete enumeration of the guard-passing
entries already passed — the four clauses `sum_bit_eq_ncard_inter`
consumes, quantified at the counter and closed at `mb`.

# Cost

`killListCost mb = (20·mb + 64)·mb + 8`: **carrier-blind** — `n` does
not occur — and quadratic in the buffer's width `mb`, the formula-sized
`ℓ · (2·cap + 1)`, which is the design's accepted `O(mb²)` dedupe class
(§6 (a)). The charge rides the turn's own size slot as the kill pass's
does (F-4); §0 measures the instance and pins the moved absorption
constant in both directions, and the Σ interface closes at the moved
constant (`killList_interface_closes`) — the closure is indifferent,
which is F-4's disposition.
-/

namespace Lax3Proofs.Refine.KillListPass

open Lax3Proofs.RamDriver
open Lax3Proofs.Refine.KillPass (waCell)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {n : ℕ}

/-! ### §0 The compiled gates: the dedupe is load-bearing, and the cost

The instrument is `TgtWidenProbe.execC`, as in `Refine.DeadRowProbe` §5.
The arena: a three-entry buffer `7, 91, 7` — the padding's repeated
first entry — with both vertices alive and in the cluster. -/

section Probes

open Lax3Proofs.TgtWidenProbe (execC pB pF PSt)

/-- The same walk with the dedupe scan dropped: every guard-passing
entry is appended. This is the program the refutation runs. -/
def naiveKlCom (mb j : ℕ) : Com :=
  .seq (.assign (kkName j) (.lit 0))
    (.seq (.assign "kk" (.lit 0))
      (.while (.lt (.var "kk") (.lit mb))
        (.seq (.assign "kv" (.get "wa" (.var "kk")))
          (.seq (.ite (.lt (.lit 0)
                  (.mul (.get (alvName j) (.var "kv")) (.get (cluName j) (.var "kv"))))
                  (.seq (.store (klName j) (.var (kkName j)) (.var "kv"))
                    (.assign (kkName j) (.add (.var (kkName j)) (.lit 1))))
                  .skip)
            (.assign "kk" (.add (.var "kk") (.lit 1)))))))

/-- The turn context: buffer `7, 91, 7` (the repeated entry is the
padding's), both vertices alive and in the cluster, the list holding
junk. -/
def klSt (n : ℕ) : PSt :=
  { vars := []
    arrs := [("wa", [7, 91, 7]),
             (alvName 0, ((List.replicate n 0).set 7 1).set 91 1),
             (cluName 0, ((List.replicate n 0).set 7 1).set 91 1),
             (klName 0, [9, 9, 9])] }

-- the pass completes on every instance measured
#guard (execC pB pF (killListCom 3 0) (klSt 100)).1.isOk
#guard (execC pB pF (naiveKlCom 3 0) (klSt 100)).1.isOk

-- **the deduped walk reports the kill set**: two distinct kills among
-- three guard hits, and the emitted prefix lists each once
#guard (execC pB pF (killListCom 3 0) (klSt 100)).1.scalar (kkName 0) = 2
#guard (execC pB pF (killListCom 3 0) (klSt 100)).1.cell (klName 0) 0 = 7
#guard (execC pB pF (killListCom 3 0) (klSt 100)).1.cell (klName 0) 1 = 91
#guard (execC pB pF (killListCom 3 0) (klSt 100)).1.cell (klName 0) 2 = 9

-- **the refutation**: the scan-free walk emits the repeated entry
-- twice — its count is the guard-hit count, not the kill count, and a
-- bit sum over its prefix double-counts vertex `7`. The dedupe is
-- load-bearing, not bookkeeping.
#guard (execC pB pF (naiveKlCom 3 0) (klSt 100)).1.scalar (kkName 0) = 3
#guard (execC pB pF (naiveKlCom 3 0) (klSt 100)).1.cell (klName 0) 0 = 7
#guard (execC pB pF (naiveKlCom 3 0) (klSt 100)).1.cell (klName 0) 2 = 7

-- **carrier-blind**: equal clocks at carriers 100 and 200 — the walk
-- reads the buffer and the two mask cells at its entries, never the
-- carrier
#guard (execC pB pF (killListCom 3 0) (klSt 100)).2 =
  (execC pB pF (killListCom 3 0) (klSt 200)).2

/-- The measured clock of the probe instance: three guard hits, two
appends, one scan hit. -/
def klc : ℕ := (execC pB pF (killListCom 3 0) (klSt 100)).2

/-- **The moved turn coefficient.** `Refine.DeadRowProbe`'s closure runs
at `ct = 284 = 200 + 84` — BlockLeaves' measured leaf plus the kill
pass's measured write — and the `#guard` there is an exact fit, so the
kill list's charge cannot ride under the same constant: `ct` moves, by
exactly the measured instance. Both directions are pinned below, and
`killList_interface_closes` is the Σ interface at the moved constant —
indifferent, which is design §7's F-4 disposition. -/
def ctKL : ℕ := 284 + klc

-- the absorption at the empty block, in both directions: the moved
-- constant covers the three measured passes, and nothing more
#guard 200 + 84 + klc ≤ ctKL * (0 + 1)
#guard ctKL * (0 + 1) ≤ 200 + 84 + klc

/-- **The Σ interface closes at the moved constant** —
`Refine.DeadRowProbe.deadRow_interface_closes` at `ct = ctKL` in place
of `284`, same slots otherwise: the closure is indifferent to the turn
coefficient's value (F-4), so absorbing the kill list moves a number
and no interface. -/
theorem killList_interface_closes (Cb : ℕ) :
    ∃ Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ,
      (∀ j w m, m ≤ w →
        Lax3Proofs.Refine.G2ExistsRevalidation.phaseMR 68 12 0 m ≤ Ko j w) ∧
      (∀ j w m, m ≤ w →
        Lax3Proofs.Refine.G2ExistsRevalidation.phaseMR 68 12 0 m ≤ Kc j w) ∧
      (∀ j w m, m ≤ w →
        Lax3Proofs.Refine.G2ExistsRevalidation.phaseMR 0 12 0 m ≤ Kd j w) ∧
      (∀ w, Cb * (w + 1) ≤ Kl 3 w) ∧
      (∀ j, Monotone (Kl j)) ∧
      (∀ j < 3, ∀ s : ℕ,
        Lax3Proofs.Refine.G2CostProbe.turnCostSizeA ctKL (10 ^ 4) s (Kl (j + 1) s) ≤
          Ks j s) ∧
      (∀ j < 3, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
        (∑ c ∈ Finset.range t, bs c) ≤ 8 * (w + 1) →
        Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
          ≤ Kl j w) ∧
      (∀ w, Kl 0 w ≤
        (3 * Lax3Proofs.Refine.G2ExistsRevalidation.g2M 68 12 68 12 0 12 0 ctKL (10 ^ 4) 8 +
          Cb) * (8 + 1) ^ 3 * (w + 1)) :=
  Lax3Proofs.Refine.G2ExistsRevalidation.g2m_exists 3 8 Cb 0 68 12 68 12 0 12 ctKL (10 ^ 4)
    (fun _ => 10 ^ 4) (fun _ _ => le_rfl)

end Probes

/-! ### §0b The names

The pass's two products against the fixed scratch and the arrays it
reads — character arithmetic, as everywhere in the driver. -/

theorem kkName_ne_kk (j : ℕ) : kkName j ≠ "kk" := by simp [kkName, String.ext_iff]

theorem kkName_ne_kv (j : ℕ) : kkName j ≠ "kv" := by simp [kkName, String.ext_iff]

theorem kkName_ne_kf (j : ℕ) : kkName j ≠ "kf" := by simp [kkName, String.ext_iff]

theorem kkName_ne_kt (j : ℕ) : kkName j ≠ "kt" := by simp [kkName, String.ext_iff]

theorem wa_ne_klName (j : ℕ) : "wa" ≠ klName j := by simp [klName, String.ext_iff]

theorem alvName_ne_klName (j j' : ℕ) : alvName j ≠ klName j' := by
  simp [alvName, klName, String.ext_iff]

theorem cluName_ne_klName (j j' : ℕ) : cluName j ≠ klName j' := by
  simp [cluName, klName, String.ext_iff]

/-! ### §1 The inner scan

The membership test: `kf` accumulates whether the probed value `kv`
occurs in the emitted prefix `kl[0 .. kkName j)`. The invariant is the
verdict at the scan counter; the exit reads it at the whole prefix. -/

/-- The scan, named — the inner `while` of `RamDriver.killListCom`. -/
def scanCom (j : ℕ) : Com :=
  .while (.lt (.var "kt") (.var (kkName j)))
    (.seq (.ite (.eq (.get (klName j) (.var "kt")) (.var "kv"))
            (.assign "kf" (.lit 1)) .skip)
      (.assign "kt" (.add (.var "kt") (.lit 1))))
/-- What the scan carries: the list and the count as the outer walk
holds them, the probed value, and the verdict at the counter. -/
def ScanInv (mb j : ℕ) (kl : ℕ → ℕ) (kq u : ℕ) (σ : Env) : Prop :=
  σ.arrs (klName j) = arrOf mb kl ∧ σ.vars (kkName j) = kq ∧ σ.vars "kv" = u ∧
    σ.vars "kt" ≤ kq ∧ σ.vars "kf" ≤ 1 ∧
    (σ.vars "kf" ≠ 0 ↔ ∃ e, e < σ.vars "kt" ∧ kl e = u)

/-- **One scan step**: read the cell at the counter, set the flag on a
hit, bump the counter. -/
theorem scanTurn_spec {B mb j kq u : ℕ} {kl : ℕ → ℕ}
    (hB : 1 < B) (hn : n < B) (hmbB : mb < B) (hkq : kq ≤ mb) (hu : u < B)
    (hkln : ∀ e, e < kq → kl e < n) :
    Spec B (fun σ => ScanInv mb j kl kq u σ ∧
        (Cond.lt (.var "kt") (.var (kkName j))).evalB B σ = some true)
      (.seq (.ite (.eq (.get (klName j) (.var "kt")) (.var "kv"))
              (.assign "kf" (.lit 1)) .skip)
        (.assign "kt" (.add (.var "kt") (.lit 1))))
      (fun σ σ' => ScanInv mb j kl kq u σ' ∧
        kq - σ'.vars "kt" < kq - σ.vars "kt") 16 := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hkl, hkk, hkv, htle, hkf1, hkf⟩, hcond⟩ := hσ
  have hktB : σ.vars "kt" < B := by omega
  have hkt : σ.vars "kt" < kq := by
    rw [evalB_condLt (evalB_var hktB) (evalB_var (by rw [hkk]; omega))] at hcond
    simp only [Option.some.injEq, decide_eq_true_eq] at hcond
    rw [hkk] at hcond
    exact hcond
  have hcell : kl (σ.vars "kt") < n := hkln _ hkt
  -- the guard: the cell at the counter against the probed value
  have hkvv : (Expr.var "kv").evalB B σ = some u := by
    rw [← hkv]
    exact evalB_var (by rw [hkv]; exact hu)
  have hguard : (Cond.eq (.get (klName j) (.var "kt")) (.var "kv")).evalB B σ =
      some (kl (σ.vars "kt") == u) := by
    refine evalB_condEq (evalB_get (evalB_var hktB) ?_ (by omega)) hkvv
    rw [hkl]
    exact getElem?_arrOf kl (by omega)
  -- the counter bump, off whichever branch ran
  have hstep : ∀ τ : Env, τ.vars "kt" = σ.vars "kt" →
      Run B (.assign "kt" (.add (.var "kt") (.lit 1))) τ
        (τ.setVar "kt" (σ.vars "kt" + 1)) 4 := by
    intro τ hτ
    refine (Run.assign (B := B) (x := "kt") (σ := τ)
      (evalB_bin (evalB_var (by rw [hτ]; exact hktB)) (evalB_lit (by omega)) ?_)).congr ?_
      |>.mono (by simp)
    · simp only [Bop.apply_add, hτ]; omega
    · rw [hτ]; simp only [Bop.apply_add]
  by_cases hhit : kl (σ.vars "kt") = u
  · -- a hit: the flag is set
    have hr₁ := Run.assign (B := B) (x := "kf") (σ := σ) (evalB_lit hB)
    have hr₂ := hstep (σ.setVar "kf" 1) (by rw [vars_setVar, if_neg (by decide)])
    have hkf' : ((σ.setVar "kf" 1).setVar "kt" (σ.vars "kt" + 1)).vars "kf" = 1 := by
      rw [vars_setVar, if_neg (by decide), vars_setVar, if_pos rfl]
    have hkt' : ((σ.setVar "kf" 1).setVar "kt" (σ.vars "kt" + 1)).vars "kt"
        = σ.vars "kt" + 1 := by
      rw [vars_setVar, if_pos rfl]
    refine ⟨(σ.setVar "kf" 1).setVar "kt" (σ.vars "kt" + 1), _,
      (Run.ite_true (by rw [hguard, hhit]; simp) hr₁).seq hr₂,
      by simp only [size_condEq, size_get, size_var, size_lit]; omega,
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [hkt']; omega⟩
    · simp only [arrs_setVar]; exact hkl
    · rw [vars_setVar, if_neg (kkName_ne_kt j), vars_setVar, if_neg (kkName_ne_kf j)]
      exact hkk
    · rw [vars_setVar, if_neg (by decide), vars_setVar, if_neg (by decide)]; exact hkv
    · rw [hkt']; omega
    · rw [hkf']
    · rw [hkf', hkt']
      exact ⟨fun _ => ⟨σ.vars "kt", by omega, hhit⟩, fun _ => by omega⟩
  · -- a miss: the flag survives, the counter moves
    have hr₂ := hstep σ rfl
    have hkf' : (σ.setVar "kt" (σ.vars "kt" + 1)).vars "kf" = σ.vars "kf" := by
      rw [vars_setVar, if_neg (by decide)]
    have hkt' : (σ.setVar "kt" (σ.vars "kt" + 1)).vars "kt" = σ.vars "kt" + 1 := by
      rw [vars_setVar, if_pos rfl]
    refine ⟨σ.setVar "kt" (σ.vars "kt" + 1), _,
      (Run.ite_false (by rw [hguard]; simp [hhit]) Run.skip).seq hr₂,
      by simp only [size_condEq, size_get, size_var, size_lit]; omega,
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [hkt']; omega⟩
    · simp only [arrs_setVar]; exact hkl
    · rw [vars_setVar, if_neg (kkName_ne_kt j)]; exact hkk
    · rw [vars_setVar, if_neg (by decide)]; exact hkv
    · rw [hkt']; omega
    · rw [hkf']; exact hkf1
    · rw [hkf', hkt', hkf]
      constructor
      · rintro ⟨e, he, hee⟩; exact ⟨e, by omega, hee⟩
      · rintro ⟨e, he, hee⟩
        refine ⟨e, ?_, hee⟩
        rcases Nat.lt_or_ge e (σ.vars "kt") with h | h
        · exact h
        · exact absurd hee (by rw [show e = σ.vars "kt" from by omega]; exact hhit)

/-- **The scan, walked**: at the exit the flag is the membership verdict
of the probed value in the whole emitted prefix. -/
theorem scan_spec {B mb j kq u : ℕ} {kl : ℕ → ℕ}
    (hB : 1 < B) (hn : n < B) (hmbB : mb < B) (hkq : kq ≤ mb) (hu : u < B)
    (hkln : ∀ e, e < kq → kl e < n) :
    Spec B (fun σ => ScanInv mb j kl kq u σ)
      (scanCom j)
      (fun _ σ' => ScanInv mb j kl kq u σ' ∧ σ'.vars "kt" = kq ∧
        (σ'.vars "kf" ≠ 0 ↔ ∃ e, e < kq ∧ kl e = u))
      (20 * mb + 4) := by
  refine ((Spec.while_count (B := B) (P := ScanInv mb j kl kq u)
    (ScanInv mb j kl kq u) (fun τ => kq - τ.vars "kt") 16
    (fun τ hτ => ⟨_, evalB_condLt (evalB_var (by have := hτ.2.2.2.1; omega))
      (evalB_var (by rw [hτ.2.1]; omega))⟩)
    (scanTurn_spec hB hn hmbB hkq hu hkln)
    (fun _ hτ => hτ)
    (fun τ hτ => by
      simp only [size_condLt, size_var]
      have h1 : kq - τ.vars "kt" ≤ mb := by omega
      omega)).post ?_)
  intro σ σ' hP h
  obtain ⟨hI, hfalse⟩ := h
  have hktB : σ'.vars "kt" < B := by have := hI.2.2.2.1; omega
  rw [evalB_condLt (evalB_var hktB) (evalB_var (by rw [hI.2.1]; omega))] at hfalse
  simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hfalse
  rw [hI.2.1] at hfalse
  have hkt : σ'.vars "kt" = kq := by have := hI.2.2.2.1; omega
  exact ⟨hI, hkt, by rw [hI.2.2.2.2.2, hkt]⟩

/-! ### §2 The buffer loop

The accumulating invariant: at counter `kk`, the emitted prefix is a
repetition-free sound-and-complete enumeration of the guard-passing
entries among the first `kk` buffer slots — the four clauses of
`Refine.ScatterDeadFold.sum_bit_eq_ncard_inter`, at the counter. -/

/-- What the kill-list loop carries. -/
def KLInv (mb j : ℕ) (M Xa : ℕ → ℕ) {n : ℕ} (w : Fin mb → Fin n) (σ : Env) : Prop :=
  σ.arrs "wa" = arrOf mb (waCell mb w) ∧
    σ.arrs (alvName j) = arrOf n M ∧ σ.arrs (cluName j) = arrOf n Xa ∧
    σ.vars "kk" ≤ mb ∧
    ∃ kl kq : _, σ.arrs (klName j) = arrOf mb kl ∧ σ.vars (kkName j) = kq ∧
      kq ≤ σ.vars "kk" ∧
      (∀ e, e < kq → kl e < n) ∧
      (∀ e₁, e₁ < kq → ∀ e₂, e₂ < kq → kl e₁ = kl e₂ → e₁ = e₂) ∧
      (∀ e, e < kq → M (kl e) ≠ 0 ∧ Xa (kl e) ≠ 0 ∧
        ∃ p : Fin mb, (p : ℕ) < σ.vars "kk" ∧ (w p : ℕ) = kl e) ∧
      (∀ p : Fin mb, (p : ℕ) < σ.vars "kk" → M (w p : ℕ) ≠ 0 → Xa (w p : ℕ) ≠ 0 →
        ∃ e, e < kq ∧ kl e = (w p : ℕ))

/-- The cost of one turn of the buffer loop: the entry read, the guard,
the scan at its widest, the append, the counter. -/
def klTurnCost (mb : ℕ) : ℕ := 20 * mb + 60

/-- The cost of the whole pass: **carrier-blind**, quadratic in the
buffer's width — the design's accepted `O(mb²)` dedupe class. -/
def killListCost (mb : ℕ) : ℕ := (klTurnCost mb + 4) * mb + 8

/-- **One turn of the buffer loop.** The entry is read; if it is alive
and in the cluster, the scan decides whether it was already emitted, and
it is appended exactly when it was not. -/
theorem klTurn_spec {B mb j : ℕ} {M Xa : ℕ → ℕ} {w : Fin mb → Fin n}
    (hB : 1 < B) (hn : n < B) (hmbB : mb < B)
    (hMB : ∀ z < n, M z < B) (hXa1 : ∀ z < n, Xa z ≤ 1) :
    Spec B (fun σ => KLInv mb j M Xa w σ ∧
        (Cond.lt (.var "kk") (.lit mb)).evalB B σ = some true)
      (.seq (.assign "kv" (.get "wa" (.var "kk")))
        (.seq (.ite (.lt (.lit 0)
                (.mul (.get (alvName j) (.var "kv")) (.get (cluName j) (.var "kv"))))
                (.seq (.assign "kf" (.lit 0))
                  (.seq (.assign "kt" (.lit 0))
                    (.seq (scanCom j)
                      (.ite (.eq (.var "kf") (.lit 0))
                        (.seq (.store (klName j) (.var (kkName j)) (.var "kv"))
                          (.assign (kkName j) (.add (.var (kkName j)) (.lit 1))))
                        .skip))))
                .skip)
          (.assign "kk" (.add (.var "kk") (.lit 1)))))
      (fun σ σ' => KLInv mb j M Xa w σ' ∧
        mb - σ'.vars "kk" < mb - σ.vars "kk")
      (klTurnCost mb) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hwa, halv, hclu, hkkle, kl, kq, hkl, hkkq, hqle, hkln, hinj, hsound, hcomp⟩,
    hcond⟩ := hσ
  have hkkB : σ.vars "kk" < B := by omega
  have hkk : σ.vars "kk" < mb := by
    rw [evalB_condLt (evalB_var hkkB) (evalB_lit hmbB)] at hcond
    simpa using hcond
  set p₀ : Fin mb := ⟨σ.vars "kk", hkk⟩ with hp₀
  set u : Fin n := w p₀ with hu
  have hp₀val : (p₀ : ℕ) = σ.vars "kk" := rfl
  have huB : (u : ℕ) < B := by have := u.isLt; omega
  -- the entry
  have hgetwa : (Expr.get "wa" (.var "kk")).evalB B σ = some (u : ℕ) := by
    refine evalB_get (evalB_var hkkB) ?_ huB
    rw [hwa, getElem?_arrOf _ hkk, waCell, dif_pos hkk]
  have hr₁ := Run.assign (B := B) (x := "kv") (σ := σ) hgetwa
  set σ₁ := σ.setVar "kv" (u : ℕ) with hσ₁
  have hkv₁ : σ₁.vars "kv" = (u : ℕ) := by rw [hσ₁, vars_setVar, if_pos rfl]
  have harrs₁ : ∀ a, σ₁.arrs a = σ.arrs a := fun a => by rw [hσ₁, arrs_setVar]
  -- the guard
  have hguard : (Cond.lt (.lit 0)
      (.mul (.get (alvName j) (.var "kv")) (.get (cluName j) (.var "kv")))).evalB B σ₁ =
      some (decide (0 < M (u : ℕ) * Xa (u : ℕ))) := by
    refine evalB_condLt (evalB_lit (by omega)) (evalB_bin ?_ ?_ ?_)
    · exact evalB_get (evalB_var (by rw [hkv₁]; exact huB))
        (by rw [hkv₁, harrs₁, halv, getElem?_arrOf _ u.isLt]) (hMB _ u.isLt)
    · exact evalB_get (evalB_var (by rw [hkv₁]; exact huB))
        (by rw [hkv₁, harrs₁, hclu, getElem?_arrOf _ u.isLt])
        (lt_of_le_of_lt (hXa1 _ u.isLt) hB)
    · have h₁ := hMB _ u.isLt
      have h₂ := hXa1 _ u.isLt
      simp only [Bop.apply_mul]
      calc M (u : ℕ) * Xa (u : ℕ) ≤ M (u : ℕ) * 1 := Nat.mul_le_mul_left _ h₂
        _ < B := by omega
  -- the counter, off whichever branch ran
  have hstep : ∀ τ : Env, τ.vars "kk" = σ.vars "kk" →
      Run B (.assign "kk" (.add (.var "kk") (.lit 1))) τ
        (τ.setVar "kk" (σ.vars "kk" + 1)) 4 := by
    intro τ hτ
    refine (Run.assign (B := B) (x := "kk") (σ := τ)
      (evalB_bin (evalB_var (by rw [hτ]; exact hkkB)) (evalB_lit (by omega)) ?_)).congr ?_
      |>.mono (by simp)
    · simp only [Bop.apply_add, hτ]; omega
    · rw [hτ]; simp only [Bop.apply_add]
  by_cases hkill : 0 < M (u : ℕ) * Xa (u : ℕ)
  · -- a guard-passing entry: the scan decides, the append follows its flag
    have hkilled : M (u : ℕ) ≠ 0 ∧ Xa (u : ℕ) ≠ 0 := by
      constructor <;> intro hc <;> simp [hc] at hkill
    have hr₂ := Run.assign (B := B) (x := "kf") (σ := σ₁) (evalB_lit (show 0 < B by omega))
    set σ₂ := σ₁.setVar "kf" 0 with hσ₂
    have hr₃ := Run.assign (B := B) (x := "kt") (σ := σ₂) (evalB_lit (show 0 < B by omega))
    set σ₃ := σ₂.setVar "kt" 0 with hσ₃
    have harrs₃ : ∀ a, σ₃.arrs a = σ.arrs a := fun a => by
      rw [hσ₃, arrs_setVar, hσ₂, arrs_setVar, harrs₁]
  -- the scan starts fresh
    have hI₃ : ScanInv mb j kl kq (u : ℕ) σ₃ := by
      refine ⟨by rw [harrs₃]; exact hkl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hσ₃, vars_setVar, if_neg (kkName_ne_kt j), hσ₂, vars_setVar,
          if_neg (kkName_ne_kf j), hσ₁, vars_setVar, if_neg (kkName_ne_kv j)]
        exact hkkq
      · rw [hσ₃, vars_setVar, if_neg (by decide), hσ₂, vars_setVar, if_neg (by decide)]
        exact hkv₁
      · rw [hσ₃, vars_setVar, if_pos rfl]; omega
      · rw [hσ₃, vars_setVar, if_neg (by decide), hσ₂, vars_setVar, if_pos rfl]; omega
      · have h1 : σ₃.vars "kf" = 0 := by
          rw [hσ₃, vars_setVar, if_neg (by decide), hσ₂, vars_setVar, if_pos rfl]
        have h2 : σ₃.vars "kt" = 0 := by rw [hσ₃, vars_setVar, if_pos rfl]
        rw [h1, h2]
        exact ⟨fun h => absurd rfl h, by rintro ⟨e, he, -⟩; omega⟩
    obtain ⟨σ₄, hr₄, hI₄, hkt₄, hfd₄⟩ :=
      (scan_spec (n := n) hB hn hmbB (by omega) huB hkln).run (σ := σ₃) hI₃
    -- the scan writes its two scalars and nothing else
    have hsfr : ∀ a, a ∉ (scanCom j).warrs := by
      intro a
      simp [scanCom, Com.warrs]
    have hsfv : ∀ y, y ≠ "kf" → y ≠ "kt" → y ∉ (scanCom j).wvars := by
      intro y h1 h2
      simp [scanCom, Com.wvars, h1, h2]
    have harrs₄ : ∀ a, σ₄.arrs a = σ.arrs a := fun a => by
      rw [hr₄.frame_arr a (hsfr a), harrs₃]
    have hkk₄ : σ₄.vars "kk" = σ.vars "kk" := by
      rw [hr₄.frame_var "kk" (hsfv _ (by decide) (by decide)), hσ₃, vars_setVar,
        if_neg (by decide), hσ₂, vars_setVar, if_neg (by decide), hσ₁, vars_setVar,
        if_neg (by decide)]
    obtain ⟨hkl₄, hkkq₄, hkv₄, -, hkf₄1, -⟩ := hI₄
    by_cases hnew : σ₄.vars "kf" = 0
    · -- a new kill: append it
      have hnotin : ∀ e, e < kq → kl e ≠ (u : ℕ) := fun e he hee =>
        (hfd₄.mpr ⟨e, he, hee⟩) hnew
      have happgd : (Cond.eq (.var "kf") (.lit 0)).evalB B σ₄ = some true := by
        rw [evalB_condEq (evalB_var (by omega)) (evalB_lit (by omega)), hnew]
        simp
      have hqlt : kq < mb := by omega
      have hia : (Expr.var (kkName j)).evalB B σ₄ = some kq := by
        rw [← hkkq₄]
        exact evalB_var (by rw [hkkq₄]; omega)
      have hva : (Expr.var "kv").evalB B σ₄ = some (u : ℕ) := by
        rw [← hkv₄]
        exact evalB_var (by rw [hkv₄]; exact huB)
      have hr₅ := Run.store (B := B) (σ := σ₄) (a := klName j) hia hva
        (by rw [hkl₄, length_arrOf]; exact hqlt)
      set σ₅ := σ₄.setArr (klName j) kq (u : ℕ) with hσ₅
      have hkkq₅ : σ₅.vars (kkName j) = kq := by rw [hσ₅, vars_setArr]; exact hkkq₄
      have hr₆ : Run B (.assign (kkName j) (.add (.var (kkName j)) (.lit 1))) σ₅
          (σ₅.setVar (kkName j) (kq + 1)) 4 := by
        refine (Run.assign (B := B) (x := kkName j) (σ := σ₅)
          (evalB_bin (evalB_var (by rw [hkkq₅]; omega)) (evalB_lit (by omega)) ?_)).congr ?_
          |>.mono (by simp)
        · simp only [Bop.apply_add]; rw [hkkq₅]; omega
        · rw [hkkq₅]; simp only [Bop.apply_add]
      set σ₆ := σ₅.setVar (kkName j) (kq + 1) with hσ₆
      have hkk₆ : σ₆.vars "kk" = σ.vars "kk" := by
        rw [hσ₆, vars_setVar, if_neg (Ne.symm (kkName_ne_kk j)), hσ₅, vars_setArr, hkk₄]
      have hr₇ := hstep σ₆ hkk₆
      refine ⟨σ₆.setVar "kk" (σ.vars "kk" + 1), _,
        hr₁.seq ((Run.ite_true (by rw [hguard]; simp [hkill])
          (hr₂.seq (hr₃.seq (hr₄.seq (Run.ite_true happgd (hr₅.seq hr₆)))))).seq hr₇),
        ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, by rw [vars_setVar, if_pos rfl]; omega⟩
      · rw [klTurnCost]
        simp only [size_condLt, size_condEq, size_lit, size_var, size_get, size_bin]
        omega
      · rw [arrs_setVar, hσ₆, arrs_setVar, hσ₅, arrs_setArr, if_neg (wa_ne_klName j),
          harrs₄]
        exact hwa
      · rw [arrs_setVar, hσ₆, arrs_setVar, hσ₅, arrs_setArr,
          if_neg (alvName_ne_klName j j), harrs₄]
        exact halv
      · rw [arrs_setVar, hσ₆, arrs_setVar, hσ₅, arrs_setArr,
          if_neg (cluName_ne_klName j j), harrs₄]
        exact hclu
      · rw [vars_setVar, if_pos rfl]; omega
      · -- the enumeration, extended by the new kill
        have hklf : (σ₆.setVar "kk" (σ.vars "kk" + 1)).arrs (klName j) =
            arrOf mb (upd kl kq (u : ℕ)) := by
          rw [arrs_setVar, hσ₆, arrs_setVar, hσ₅, arrs_setArr, if_pos rfl, hkl₄,
            set_arrOf_eq_upd]
        have hkqf : (σ₆.setVar "kk" (σ.vars "kk" + 1)).vars (kkName j) = kq + 1 := by
          rw [vars_setVar, if_neg (kkName_ne_kk j), hσ₆, vars_setVar, if_pos rfl]
        have hkkf : (σ₆.setVar "kk" (σ.vars "kk" + 1)).vars "kk" = σ.vars "kk" + 1 := by
          rw [vars_setVar, if_pos rfl]
        refine ⟨upd kl kq (u : ℕ), kq + 1, hklf, hkqf, by rw [hkkf]; omega,
          ?_, ?_, ?_, ?_⟩
        · intro e he
          rw [upd_apply]
          split
          · exact u.isLt
          · exact hkln e (by omega)
        · intro e₁ he₁ e₂ he₂ hee
          rw [upd_apply, upd_apply] at hee
          rcases eq_or_ne e₁ kq with h₁ | h₁ <;> rcases eq_or_ne e₂ kq with h₂ | h₂
          · omega
          · rw [if_pos h₁, if_neg h₂] at hee
            exact absurd hee.symm (hnotin e₂ (by omega))
          · rw [if_neg h₁, if_pos h₂] at hee
            exact absurd hee (hnotin e₁ (by omega))
          · rw [if_neg h₁, if_neg h₂] at hee
            exact hinj e₁ (by omega) e₂ (by omega) hee
        · intro e he
          rw [hkkf, upd_apply]
          split
          · exact ⟨hkilled.1, hkilled.2, p₀, by omega, by rw [hu]⟩
          · obtain ⟨hM, hX, p, hp, hpe⟩ := hsound e (by omega)
            exact ⟨hM, hX, p, by omega, hpe⟩
        · intro p hp hM hX
          rw [hkkf] at hp
          rcases Nat.lt_or_ge (p : ℕ) (σ.vars "kk") with h | h
          · obtain ⟨e, he, hpe⟩ := hcomp p h hM hX
            exact ⟨e, by omega, by rw [upd_apply, if_neg (by omega)]; exact hpe⟩
          · have hpp : p = p₀ := Fin.ext (by omega)
            exact ⟨kq, by omega, by rw [upd_apply, if_pos rfl, hpp, ← hu]⟩
    · -- already emitted: the scan found it, nothing moves
      have happgd : (Cond.eq (.var "kf") (.lit 0)).evalB B σ₄ = some false := by
        rw [evalB_condEq (evalB_var (by omega)) (evalB_lit (by omega))]
        simpa using hnew
      have hr₇ := hstep σ₄ hkk₄
      refine ⟨σ₄.setVar "kk" (σ.vars "kk" + 1), _,
        hr₁.seq ((Run.ite_true (by rw [hguard]; simp [hkill])
          (hr₂.seq (hr₃.seq (hr₄.seq (Run.ite_false happgd Run.skip))))).seq hr₇),
        ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, by rw [vars_setVar, if_pos rfl]; omega⟩
      · rw [klTurnCost]
        simp only [size_condLt, size_condEq, size_lit, size_var, size_get, size_bin]
        omega
      · rw [arrs_setVar, harrs₄]; exact hwa
      · rw [arrs_setVar, harrs₄]; exact halv
      · rw [arrs_setVar, harrs₄]; exact hclu
      · rw [vars_setVar, if_pos rfl]; omega
      · have hkkf : (σ₄.setVar "kk" (σ.vars "kk" + 1)).vars "kk" = σ.vars "kk" + 1 := by
          rw [vars_setVar, if_pos rfl]
        refine ⟨kl, kq, by rw [arrs_setVar]; exact hkl₄,
          by rw [vars_setVar, if_neg (kkName_ne_kk j)]; exact hkkq₄,
          by rw [hkkf]; omega, hkln, hinj, ?_, ?_⟩
        · intro e he
          rw [hkkf]
          obtain ⟨hM, hX, p, hp, hpe⟩ := hsound e he
          exact ⟨hM, hX, p, by omega, hpe⟩
        · intro p hp hM hX
          rw [hkkf] at hp
          rcases Nat.lt_or_ge (p : ℕ) (σ.vars "kk") with h | h
          · exact hcomp p h hM hX
          · have hpp : p = p₀ := Fin.ext (by omega)
            obtain ⟨e, he, hee⟩ := hfd₄.mp hnew
            exact ⟨e, he, by rw [hee, hpp, ← hu]⟩
  · -- not a guard-passing entry: nothing moves
    have hr₇ := hstep σ₁ (by rw [hσ₁, vars_setVar, if_neg (by decide)])
    refine ⟨σ₁.setVar "kk" (σ.vars "kk" + 1), _,
      hr₁.seq ((Run.ite_false (by rw [hguard]; simp [hkill]) Run.skip).seq hr₇),
      ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, by rw [vars_setVar, if_pos rfl]; omega⟩
    · rw [klTurnCost]
      simp only [size_condLt, size_condEq, size_lit, size_var, size_get, size_bin]
      omega
    · rw [arrs_setVar, harrs₁]; exact hwa
    · rw [arrs_setVar, harrs₁]; exact halv
    · rw [arrs_setVar, harrs₁]; exact hclu
    · rw [vars_setVar, if_pos rfl]; omega
    · have hkkf : (σ₁.setVar "kk" (σ.vars "kk" + 1)).vars "kk" = σ.vars "kk" + 1 := by
        rw [vars_setVar, if_pos rfl]
      refine ⟨kl, kq, by rw [arrs_setVar, harrs₁]; exact hkl,
        ?_, by rw [hkkf]; omega, hkln, hinj, ?_, ?_⟩
      · rw [vars_setVar, if_neg (kkName_ne_kk j), hσ₁, vars_setVar,
          if_neg (kkName_ne_kv j)]
        exact hkkq
      · intro e he
        rw [hkkf]
        obtain ⟨hM, hX, p, hp, hpe⟩ := hsound e he
        exact ⟨hM, hX, p, by omega, hpe⟩
      · intro p hp hM hX
        rw [hkkf] at hp
        rcases Nat.lt_or_ge (p : ℕ) (σ.vars "kk") with h | h
        · exact hcomp p h hM hX
        · exfalso
          have hpp : p = p₀ := Fin.ext (by omega)
          rw [hpp, ← hu] at hM hX
          exact hkill (Nat.pos_of_ne_zero (Nat.mul_ne_zero hM hX))

/-- **The kill list, walked.** At the exit, `klName j` holds — once
each — exactly the buffer entries that are alive at depth `j` and in the
cluster, and `kkName j` counts them: the four clauses
`Refine.ScatterDeadFold.sum_bit_eq_ncard_inter` consumes, at the whole
buffer. -/
theorem killListCom_spec {B mb j : ℕ} {M Xa : ℕ → ℕ} {w : Fin mb → Fin n}
    (hB : 1 < B) (hn : n < B) (hmbB : mb < B)
    (hMB : ∀ z < n, M z < B) (hXa1 : ∀ z < n, Xa z ≤ 1) :
    Spec B (fun σ => σ.arrs "wa" = arrOf mb (waCell mb w) ∧
        σ.arrs (alvName j) = arrOf n M ∧ σ.arrs (cluName j) = arrOf n Xa ∧
        ∃ g, σ.arrs (klName j) = arrOf mb g)
      (killListCom mb j)
      (fun _ σ' => ∃ kl kq : _, σ'.arrs (klName j) = arrOf mb kl ∧
        σ'.vars (kkName j) = kq ∧ kq ≤ mb ∧
        (∀ e, e < kq → kl e < n) ∧
        (∀ e₁, e₁ < kq → ∀ e₂, e₂ < kq → kl e₁ = kl e₂ → e₁ = e₂) ∧
        (∀ e, e < kq → M (kl e) ≠ 0 ∧ Xa (kl e) ≠ 0 ∧
          ∃ p : Fin mb, (w p : ℕ) = kl e) ∧
        (∀ p : Fin mb, M (w p : ℕ) ≠ 0 → Xa (w p : ℕ) ≠ 0 →
          ∃ e, e < kq ∧ kl e = (w p : ℕ)))
      (killListCost mb) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hwa, halv, hclu, g, hklg⟩ := hσ
  have hr₁ := Run.assign (B := B) (x := kkName j) (σ := σ) (evalB_lit (show 0 < B by omega))
  set σ₁ := σ.setVar (kkName j) 0 with hσ₁
  have hr₂ := Run.assign (B := B) (x := "kk") (σ := σ₁) (evalB_lit (show 0 < B by omega))
  set σ₂ := σ₁.setVar "kk" 0 with hσ₂
  have harrs₂ : ∀ a, σ₂.arrs a = σ.arrs a := fun a => by
    rw [hσ₂, arrs_setVar, hσ₁, arrs_setVar]
  have hI₂ : KLInv mb j M Xa w σ₂ := by
    refine ⟨by rw [harrs₂]; exact hwa, by rw [harrs₂]; exact halv,
      by rw [harrs₂]; exact hclu, by rw [hσ₂, vars_setVar, if_pos rfl]; omega,
      g, 0, by rw [harrs₂]; exact hklg, ?_,
      Nat.zero_le _,
      fun e he => absurd he (by omega), fun e₁ h₁ e₂ h₂ _ => by omega,
      fun e he => absurd he (by omega), fun p hp _ _ => by
        rw [hσ₂, vars_setVar, if_pos rfl] at hp
        exact absurd hp (by omega)⟩
    rw [hσ₂, vars_setVar, if_neg (kkName_ne_kk j), hσ₁, vars_setVar, if_pos rfl]
  obtain ⟨σ₃, hr₃, hI₃, hfalse⟩ :=
    (Spec.while_count (B := B) (P := KLInv mb j M Xa w)
      (K := (klTurnCost mb + 4) * mb + 4)
      (KLInv mb j M Xa w) (fun τ => mb - τ.vars "kk") (klTurnCost mb)
      (fun τ hτ => evalB_condLt_var_lit (by have := hτ.2.2.2.1; omega) hmbB)
      (klTurn_spec hB hn hmbB hMB hXa1) (fun _ hτ => hτ)
      (fun τ _ => by
        simp only [size_condLt, size_var, size_lit]
        rw [show 1 + (1 + 1 + 1) + klTurnCost mb = klTurnCost mb + 4 from by omega]
        have := Nat.mul_le_mul_left (klTurnCost mb + 4)
          (Nat.sub_le mb (τ.vars "kk"))
        omega)).run hI₂
  obtain ⟨-, -, -, hkkle₃, kl, kq, hkl, hkkq, hqle, hkln, hinj, hsound, hcomp⟩ := hI₃
  have hkk₃ : σ₃.vars "kk" = mb := by
    have hkkB : σ₃.vars "kk" < B := by omega
    rw [evalB_condLt (evalB_var hkkB) (evalB_lit hmbB)] at hfalse
    simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hfalse
    omega
  refine ⟨σ₃, _, hr₁.seq (hr₂.seq hr₃), ?_,
    kl, kq, hkl, hkkq, by omega,
    hkln, hinj,
    fun e he => ⟨(hsound e he).1, (hsound e he).2.1,
      ((hsound e he).2.2).imp fun p hp => hp.2⟩,
    fun p hM hX => hcomp p (by rw [hkk₃]; exact p.isLt) hM hX⟩
  rw [killListCost]
  simp only [size_lit]
  omega
/-! ### §3 The write sets

The pass writes the list, its count, and its four scratch scalars —
computed off the fixed syntax, for the threading checkpoint's frames. -/

theorem warrs_killListCom (mb j : ℕ) {a : String} (ha : a ∈ (killListCom mb j).warrs) :
    a = klName j := by
  simpa [killListCom, scanCom, Com.warrs] using ha

theorem wvars_killListCom (mb j : ℕ) {y : String} (hy : y ∈ (killListCom mb j).wvars) :
    y = kkName j ∨ y = "kk" ∨ y = "kv" ∨ y = "kf" ∨ y = "kt" := by
  simp only [killListCom, scanCom, Com.wvars, List.mem_append, List.mem_singleton,
    List.mem_cons, List.not_mem_nil, or_false] at hy
  tauto

theorem notMem_warrs_killListCom {mb j : ℕ} {a : String} (ha : a ≠ klName j) :
    a ∉ (killListCom mb j).warrs :=
  fun h => ha (warrs_killListCom mb j h)

theorem notMem_wvars_killListCom {mb j : ℕ} {y : String} (h₁ : y ≠ kkName j)
    (h₂ : y ≠ "kk") (h₃ : y ≠ "kv") (h₄ : y ≠ "kf") (h₅ : y ≠ "kt") :
    y ∉ (killListCom mb j).wvars := by
  intro h
  rcases wvars_killListCom mb j h with h | h | h | h | h
  · exact h₁ h
  · exact h₂ h
  · exact h₃ h
  · exact h₄ h
  · exact h₅ h

/-! ### §4 Axioms -/

/-- info: 'Lax3Proofs.Refine.KillListPass.killListCom_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms killListCom_spec

/-- info: 'Lax3Proofs.Refine.KillListPass.killList_interface_closes' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms killList_interface_closes

end Lax3Proofs.Refine.KillListPass
