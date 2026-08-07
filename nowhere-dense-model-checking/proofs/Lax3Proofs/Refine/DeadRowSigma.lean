import Lax3Proofs.Refine.DeadRowProbe
import Lax3Proofs.Refine.G2ExistsRevalidation

/-!
# The dead-row probe's Σ closure — split out of `Refine/DeadRowProbe.lean`

Wave R1.8-T3-flip (c1), the second import-order repair of this road.

`DeadRowProbe` §6 was the only part of that file that consumes
`Refine.G2ExistsRevalidation`, and that consumption put the whole probe
— and with it `Refine.ScatterDeadFold`, `Refine.ScatterDeadEngine` and
`Refine.ScatterDeadPass`, which all read the probe's mathematics —
**below** `Lax3Proofs.RamDriverRoot` in the import order, because
`G2ExistsRevalidation` imports `Refine.DriverRootD`. The dead-aware atom
program's walks then could not reach `RamDriverCluster.ScatterStep`,
which is the obligation they exist to discharge.

The §6 closure is a statement about *numbers*: it names no program and
no state, and nothing above it reads it. So it moves here, into a file
below the driver root, and the probe's mathematics —
`stepColoringP_subset`, `sat_outside_uniform`,
`exists_outside_in_prefix`, `deadRows_split` and
`no_coeff_pays_outsideRows` — stays above it, where the atom program
can consume it.

Nothing is restated. The theorem below is the one that stood in
`DeadRowProbe` §6, in the same namespace, so its fully qualified name
`Refine.DeadRowProbe.deadRow_interface_closes` is unchanged and the
reference to it from `Refine.KillListPass` still names the same fact.

This is the same repair as the road's first import-order defect (wave
(a1)'s walk, which sat below the driver it served, and was fixed by
splitting the file).
-/

namespace Lax3Proofs.Refine.DeadRowProbe

/-! ## §6 The Σ interface closes at the probed constants

`G2ExistsRevalidation.g2m_exists`, consumed at the incremental charge:

* the order and cover slots at the measured M-class law `68·m + 12`
  (`OrderSigProbeM`, unchanged);
* the DEAD slot `Kd` at the CONSTANT `12` — the per-level dead-sweep
  pass is GONE; what remains per level is `O(1)` bookkeeping (the
  outside count and default bit ride the turn);
* the turn coefficient at `ct = 284 = 200 + 84`: BlockLeaves' measured
  `200` plus the measured kill-time write at the probe's instance
  (`killClock 2 · 3 = 84` — three kills, two tables), the kill charge
  riding INSIDE the turn's size-read slot `turnCostSizeA`;
* the base clause `Cb` generic — the base level is the member-list
  sweep plus the block-sized representative story (§3), both
  weight-linear; the `reprCost` floor that used to sit under
  `hKbase_gap` guarded the vestigial pass `tabled_isLocal` retires, and
  wave R1.8-T4a removed both (`Refine.BaseShed`), leaving the gap
  standing on the fold's carrier header alone.

The `#guard` pins the turn absorption at the empty block: the landed
leaf coefficient plus the whole measured kill write fit the slot's
`s = 0` reading. -/

#guard 200 + killClock 2 100 3 ≤ 284 * (0 + 1)

theorem deadRow_interface_closes (Cb : ℕ) :
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
        Lax3Proofs.Refine.G2CostProbe.turnCostSizeA 284 (10 ^ 4) s (Kl (j + 1) s) ≤
          Ks j s) ∧
      (∀ j < 3, ∀ w t : ℕ, t ≤ w → ∀ bs : ℕ → ℕ,
        (∑ c ∈ Finset.range t, bs c) ≤ 8 * (w + 1) →
        Ko j w + (Kc j w + (Kd j w + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
          ≤ Kl j w) ∧
      (∀ w, Kl 0 w ≤
        (3 * Lax3Proofs.Refine.G2ExistsRevalidation.g2M 68 12 68 12 0 12 0 284 (10 ^ 4) 8 +
          Cb) * (8 + 1) ^ 3 * (w + 1)) :=
  Lax3Proofs.Refine.G2ExistsRevalidation.g2m_exists 3 8 Cb 0 68 12 68 12 0 12 284 (10 ^ 4)
    (fun _ => 10 ^ 4) (fun _ _ => le_rfl)

/-! ## §7 Axioms -/

/-- info: 'Lax3Proofs.Refine.DeadRowProbe.deadRow_interface_closes' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms deadRow_interface_closes

end Lax3Proofs.Refine.DeadRowProbe
