import Lax3Proofs.Refine.AugCompact
import Lax3Proofs.Refine.ElimCompactWalks

/-!
# ND-MC G2/E2-width — the compacted augmentation round on real discharges

`Refine/AugCompact.lean`'s `augCompact_spec` used to name two obligations
and a width. One of the obligations — `ElimCompact.ScatterBacks` — was
**compiled-refuted**, so the theorem was dead capital: no caller could
ever produce its second hypothesis. The width was
`RamAugment.augWidth mm d ≤ W`, whose `mm·mm` term is arena-quadratic and
is the one thing `g2-cost-design` §3(a) exists to remove.

This satellite is the composed reading with both closed, and it exists so
that the closure is *seen* rather than argued:

* the scatter obligation is supplied, not assumed —
  `ElimCompactWalks.scatterBacksW` is unconditional, with no hypothesis on
  `B`, `n`, `mm` or `Mem` at all, and the two member-list clauses
  `augCompact_spec` needs come out of one `ScatterBlock.MemList`, which is
  what every caller of the package already carries;
* the width is `AugCompact.augWidthE mm kd db` — the arena's own live
  vertex count and slot count, and a degree budget, with **no `mm·mm` and
  no carrier term**. `AugCompact.augWidthE_le_weight` reads it as
  `(db+1)² · (w+1)` at the arena's weight `w = mm + kd`, which is
  `g2-cost-design` §1's arena-affine shape with the coefficient depending
  on the degree budget alone.

`db` is the *next* round's in-degree budget, and `hdb` is the inequality
`TgtCoupling.two_sq_add_le_budget_succ` proves of the chain's budget
recursion: a fold that allocates at `chainWidthE`'s last budget and runs
round `i` at `budget i` has `hdb` for free, which is how
`RamDriverCompose.fold_step` already discharges the same two capacities
at the carrier.

What is left is one obligation, `AugCompact.AugPreps` — the eleven
preparation passes — and it is the E2-prep wave's.
-/

namespace Lax3Proofs.Refine.AugCompactScatter

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.RamElim (InCsr)
open Lax3Proofs.Augmentation (Orientation)
open Lax3Proofs.RamAugment (fratSlots)
open Lax3Proofs.Refine.ScatterBlock (MemList)
open Lax3Proofs.Refine.AugCompact

/-- **The compacted augmentation round, at the arena-affine width and
with the scatter discharged.** `AugCompact.augCompact_spec` with its
second obligation supplied by `ElimCompactWalks.scatterBacksW`, its two
member-list clauses read off a `MemList`, and its room supplied by
`AugCompact.augRoom_of_augWidthE` — so the allocation the caller has to
make is `augWidthE mm kd db`, in which the carrier does not occur and the
arena occurs linearly.

Everything else is verbatim `augCompact_spec`: the cost
`augCompactCost mm kd W`, the contract `AugMemPost` at the compacted
arena, and the level's own mask above the compact prefix handed back
untouched. -/
theorem augCompact_specE {B n mm nt W kd d db m : ℕ} {D : Orientation mm}
    {Mem IO IT : ℕ → ℕ} {X : Set (Fin n)} {σ : Env}
    (h1 : AugPreps B n mm nt W kd) (hml : MemList n mm Mem X)
    (hin : InCsr D m IO IT) (hd : D.InDegLE d) (hmkd : m ≤ kd) (hkdW : kd ≤ W)
    (hnt : fratSlots D ≤ nt) (hdb : 2 * (d * d) + d ≤ db)
    (hW : augWidthE mm kd db ≤ W) (hB : mm + W + 1 < B) (hnB : n < B) (hmn : mm ≤ n)
    (hIOB : ∀ i ≤ mm, IO i < B) (hITB : ∀ j < kd, IT j < B)
    (hmem : σ.arrs "mem" = arrOf n Mem) (hent : AugEntryC n mm nt W kd IO IT σ) :
    ∃ σ'', Run B augCompactCore σ σ'' (augCompactCost mm kd W) ∧
      AugMemPost mm W Mem D σ'' ∧
      (σ''.arrs "alv").drop mm = (σ.arrs "alv").drop mm :=
  augCompact_spec h1 Lax3Proofs.Refine.ElimCompactWalks.scatterBacksW hin hd hmkd hkdW hnt
    (augRoom_of_augWidthE hin hd hdb hW) hB hnB hmn hIOB hITB hmem
    (fun j hj => hml.lt j hj) (fun i j hij hj => hml.smono i j hij hj) hent

/-- **The same at the landed width**, so that the substitution is visibly
a *widening* of what the round can be run at and not a replacement: a
caller still holding `RamAugment.augWidth mm d ≤ W` reaches the identical
conclusion. -/
theorem augCompact_specW {B n mm nt W kd d m : ℕ} {D : Orientation mm}
    {Mem IO IT : ℕ → ℕ} {X : Set (Fin n)} {σ : Env}
    (h1 : AugPreps B n mm nt W kd) (hml : MemList n mm Mem X)
    (hin : InCsr D m IO IT) (hd : D.InDegLE d) (hmkd : m ≤ kd) (hkdW : kd ≤ W)
    (hnt : fratSlots D ≤ nt) (hW : Lax3Proofs.RamAugment.augWidth mm d ≤ W)
    (hB : mm + W + 1 < B) (hnB : n < B) (hmn : mm ≤ n)
    (hIOB : ∀ i ≤ mm, IO i < B) (hITB : ∀ j < kd, IT j < B)
    (hmem : σ.arrs "mem" = arrOf n Mem) (hent : AugEntryC n mm nt W kd IO IT σ) :
    ∃ σ'', Run B augCompactCore σ σ'' (augCompactCost mm kd W) ∧
      AugMemPost mm W Mem D σ'' ∧
      (σ''.arrs "alv").drop mm = (σ.arrs "alv").drop mm :=
  augCompact_spec h1 Lax3Proofs.Refine.ElimCompactWalks.scatterBacksW hin hd hmkd hkdW hnt
    (augRoom_of_augWidth hin hd hW) hB hnB hmn hIOB hITB hmem
    (fun j hj => hml.lt j hj) (fun i j hij hj => hml.smono i j hij hj) hent

/-! ## The separation, at the corollary's own parameters

The two allocations `augCompact_specE` and `augCompact_specW` ask for, at
a million-member arena of two million compact slots whose round runs at
in-degree four (so `db = 2·4² + 4 = 36`). The affine one is `1.373 · 10⁹`;
the quadratic one is `1.000 · 10¹²`, seven hundred times larger, and all
of the difference is the `mm·mm` term. -/

#guard augWidthE (10 ^ 6) (2 * 10 ^ 6) 36 = 1371000001
#guard Lax3Proofs.RamAugment.augWidth (10 ^ 6) 4 = 1000025000001
#guard 700 * augWidthE (10 ^ 6) (2 * 10 ^ 6) 36 ≤ Lax3Proofs.RamAugment.augWidth (10 ^ 6) 4
-- the affine reading of the width the corollary asks for: `(db+1)²·(w+1)`
-- at the arena's own weight `w = mm + kd`, with no `mm` in the coefficient
#guard augWidthE (10 ^ 6) (2 * 10 ^ 6) 36 ≤ 37 ^ 2 * (3 * 10 ^ 6 + 1)
-- and no such reading exists for the landed width, at any coefficient the
-- degree budget alone determines
#guard ¬ (Lax3Proofs.RamAugment.augWidth (10 ^ 6) 4 ≤ 37 ^ 2 * (3 * 10 ^ 6 + 1))

/-! ## Axioms -/

#print axioms augCompact_specE
#print axioms augCompact_specW

end Lax3Proofs.Refine.AugCompactScatter
