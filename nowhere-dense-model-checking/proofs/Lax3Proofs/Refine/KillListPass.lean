import Lax3Proofs.Refine.KillListWalk
import Lax3Proofs.TgtWidenProbe
import Lax3Proofs.Refine.G2ExistsRevalidation

/-!
**The kill list, measured** — wave R1.8-T3-flip, scopes (a) and (a2).

`RamDriver.killListCom` is the program: the turn's kill set, enumerated
**once each** into `klName j` and counted into `kkName j`, by the same
guarded walk of the padded batch buffer as `RamDriver.killCom`, with a
membership scan of the already-emitted prefix as the dedupe.
`Refine.KillListWalk` proves its walk; **this** file is the measured
half — the compiled refutation that the dedupe is load-bearing, the
measured clock, the moved absorption constant `ctKL`, and the Σ closure
re-run at it.

**Why the halves are two files.** `RamDriverRoot` has to read the walk —
`RamDriverRoot.killListStep` is the discharge of
`RamDriverCluster.KillListStep`, and the turn's charge is a summand of
`RamDriverRoot.turnCost` — while re-running the Σ closure needs
`Refine.G2ExistsRevalidation`, which imports the driver's root. So the
walk sits above the driver (`Refine.KillListWalk`, importing only
`Refine.KillPass`) and the probes sit below it, exactly as
`Refine.KillPass` sits above and `Refine.DeadRowProbe` below for the kill
pass. Both halves are the one namespace `Lax3Proofs.Refine.KillListPass`.

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
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

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
