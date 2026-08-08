import Lax3Proofs.Refine.DeadRowProbe

/-!
# The domain-restricted table invariant: the probe's reading and the landed one

Wave R1.8-T3-flip, scope (c2b). The design compiled the
domain-restricted table invariant in `Lax3Proofs.Refine.DeadRowProbe`
(`TableInvOn`, `tableInv_iff_on_split`, and the separation
`outsideRows_forced_by_deadRows`). The *landed* statements —
`RamDriver.LevelPostD`, `RamDriverCluster.ScatterStep`, `ReadbackStep`,
`LevelInv` — cannot name it: this file's import chain runs
`Refine.DeadRowProbe → Refine.DeadSweep → … → RamDriver`, so the probe
sits far ABOVE the surface the driver's obligations are written in. So
`RamDriver.TableInvOn` restates it, character for character.

This file is the record that the restatement is the same reading, and
the compiled separation that the flip is a genuine weakening rather
than a rename:

* `tableInvOn_eq` — the two definitions are the same function, by `rfl`.
  Everything the probe proves about its own form therefore holds of the
  landed one; `tableInv_iff_on_split` is transported below.
* `tableInvOn_strictly_weaker` — at a mask that kills the whole carrier,
  the landed `TableInvOn` on the level's own domain `alive ∪ ∅` holds of
  the junk state and `RamDriver.TableInv` fails at it. That is the
  content of the flip: a level owes rows on the alive set and on the
  domain its caller pre-wrote, and on nothing else — and no consumer
  asks for more (`Refine.DeadRowProbe.readback_dead_read_is_kill` for
  the readback, `Refine.ScatterDeadPass.atomTerms_iff_scatVal` for the
  dead-aware atom phase).
-/

namespace Lax3Proofs.Refine.DeadRowDomain

open Lax3Proofs.FormulaTables
open Lax3Proofs.RamDriver (TableInv TableInvOn tabName)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-- **The landed reading IS the probe's.** Stated as an equality of
functions so that no consumer has to know which of the two it holds. -/
theorem tableInvOn_eq :
    @DeadRowProbe.TableInvOn = @Lax3Proofs.RamDriver.TableInvOn := rfl

/-- **The carrier-wide invariant is exactly its two mask halves**, at
the landed definition — `DeadRowProbe.tableInv_iff_on_split`
transported. The alive half is what the turns write; the dead half is
what the flip cut down to the caller's pre-written domain. -/
theorem tableInv_iff_on_split (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) {n : ℕ}
    (G : SimpleGraph (Fin n)) (j : ℕ) (M : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (σ : Env) :
    TableInv q_top cap mb φ G j M C σ ↔
      (TableInvOn q_top cap mb φ G j M C {v : Fin n | M (v : ℕ) ≠ 0} σ ∧
       TableInvOn q_top cap mb φ G j M C {v : Fin n | M (v : ℕ) = 0} σ) :=
  DeadRowProbe.tableInv_iff_on_split q_top cap mb φ G j M C σ

/-- **The flip is a weakening, not a rename.** At the all-dead mask the
level's own postcondition domain — `alive ∪ D` at `D = ∅`, which is what
`RamDriver.LevelImplements` carries — is EMPTY, so the junk state of
`Refine.DeadRowProbe` §4 satisfies it; and it refutes the landed
`RamDriver.TableInv`, whose quantifier is the carrier and whose cells
are asked to be bits. Generic in the formula, wherever the depth has a
table at all.

This is the level obligation the wave removed: `n` rows per level at
vertices no reader reads, which the retired `RamDriver.sweepCom` was
there to write. -/
theorem tableInvOn_strictly_weaker (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (hlen : 0 < (tablesAt q_top cap mb φ j).length) :
    ∃ (M : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (σ : Env),
      TableInvOn q_top cap mb φ (⊥ : SimpleGraph (Fin 2)) j M C
          ({v : Fin 2 | M (v : ℕ) ≠ 0} ∪ (∅ : Set (Fin 2))) σ ∧
        ¬ TableInv q_top cap mb φ (⊥ : SimpleGraph (Fin 2)) j M C σ := by
  refine ⟨fun _ => 0, fun _ _ => 0, DeadRowProbe.junkEnv, ?_, ?_⟩
  · intro i _
    refine ⟨fun _ => 7, rfl, ?_, ?_⟩
    · rintro v (hv | hv)
      · exact absurd hv (by simp)
      · exact absurd hv (Set.notMem_empty v)
    · rintro v (hv | hv)
      · exact absurd hv (by simp)
      · exact absurd hv (Set.notMem_empty v)
  · intro h
    obtain ⟨Tb, harr, hbit, -⟩ := h 0 hlen
    have h1 : Tb 1 = 7 :=
      RamDriverCluster.eq_of_arrOf_eq (N := 2) (f := Tb) (g := fun _ => 7)
        (harr.symm.trans (rfl : DeadRowProbe.junkEnv.arrs (tabName j 0)
          = arrOf 2 (fun _ => 7))) (show (1 : ℕ) < 2 by omega)
    have := hbit 1 (by omega)
    omega

/-! ### Axioms -/

/-- info: 'Lax3Proofs.Refine.DeadRowDomain.tableInvOn_eq' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms tableInvOn_eq

/-- info: 'Lax3Proofs.Refine.DeadRowDomain.tableInvOn_strictly_weaker' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms tableInvOn_strictly_weaker

end Lax3Proofs.Refine.DeadRowDomain
