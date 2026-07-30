import Lax3Proofs.RamDriverWrites
import Lax3Proofs.RamDriverAugment
import Lax3Proofs.Refine.DeadSweep

/-!
**The end of the RAM chain**: `RamDriver.driverRoot`, at `R = 0`,
decides the sentence in the graph its input word encodes.

`driverRoot_decides_sentence` is `RamDriver.driver_correct` with every
obligation instantiated. What is left of the hypotheses is exactly three
kinds of thing.

* **The input word.** `Lax11.GraphEncoding.EncodesGraph`, the slot count,
  the two arrays it decodes into — and `RamElim.CsrSimple`, the clause
  wave D4 established as *data of the word*: the encoding deliberately
  permits a block to name a vertex twice, and the two eliminations of the
  ordering phase read a degree off a row, so "no block names a vertex
  twice" is produced at the root and threaded down.
* **The parameters.** `q_top` above the sentence's rank, `cap` the
  locality radius `rhoMinus 0 q_top`, `mb = ℓ·(2·cap+1)` the padded batch
  width, `ℓ = N (2s+2)` the round budget, the word bound, and the value
  bounds the base pass and the scatter atoms form.
* **The mathematics of the campaign.** `hQ`, uniform quasi-wideness of
  the arena at radius `2·cap` — the one hypothesis that is not about the
  machine at all — together with the cost side conditions, which are
  inequalities between free cost parameters and the landed costs of the
  phases.

No obligation `Prop` is a hypothesis. The chain, bottom up:

| slot | filled by |
|------|-----------|
| `ElimAvail` | `RamElim.implements` |
| `AugAvail` | `RamDriverAugment.implements` |
| `CoverAvail` | `RamDriverOrder.coverTurnImplements` |
| `DescendStep` | `RamDriverDescend.descendStep` |
| `EnumStep` | `RamDriverDescend.enumStep` |
| `ColourStep` | `RamDriverDescend.colourStep` |
| `InnerFrames` | `RamDriverFrames.innerFrames`, on this file's write sets |
| `ScatterStep` | `RamDriverFrames.scatterStep` |
| `ReadbackStep` | `RamDriverBase.readbackStep` |
| `ClusterStepImplements` | `RamDriverCluster.clusterStepImplements` |
| `ClusterFrames` | `RamDriverFrames.clusterFrames` |
| `OrderImplements` | `RamDriverCompose.orderImplements₀` (at `R = 0`) |
| `CoverImplements` | `RamDriverCompose.coverImplements` |
| `BaseImplements` | `RamDriverCompose.baseImplements` |
| `LevelImplements` | `RamDriverCluster.levelImplements` |
| `DecodeImplements` | `RamDriverIO.decodeImplements` |
| `SentenceImplements` | `RamDriverIO.sentenceImplements` |

**Why `R = 0`.** The ordering phase is discharged there and nowhere else:
`RamDriverCompose.orderImplements₀`'s docstring records that at `R > 0`
the two `tgt` couplings of `RamAugment.AugPre` are still open. The
augmentation round *itself* is proved — `RamDriverAugment.implements` is
`AugAvail` here — so what `R > 0` costs is a coupling and not a walk.
-/

namespace Lax3Proofs.RamDriverRoot

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax11.GraphEncoding
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked CsrGraph)
open Lax3Proofs.RamDriver
open Lax3Proofs.Refine.MassMath (blockSize)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ### The frame of the nested call, at the driver

`RamDriverFrames.innerFrames` asks four syntactic things of the nested
program. At `RamDriver.driverAt … (j+1)` each of them is
`Lax3Proofs.RamDriverWrites`' reading of the recursion: everything the
enclosing turn is holding is a name of a depth at or below `j`, and a
level at depth `j + 1` writes only depths `j + 1` and above. -/

section Frames

variable {q_top cap mb ℓ W j : ℕ} {φ : Lax3.FirstOrder.FO 0}

theorem turnFrozen_notMem_warrs_driverAt {a : String} (h : RamDriverFrames.TurnFrozen j a) :
    a ∉ (driverAt q_top cap mb 0 ℓ W φ (j + 1)).warrs := by
  refine RamDriverWrites.belowArr_notMem_warrs_driverAt ?_
  rcases h with hm | ⟨c, rfl⟩ | ⟨b, hb, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨j, Nat.lt_succ_self j, by tauto⟩
  · exact ⟨j, Nat.lt_succ_self j, by tauto⟩
  · exact ⟨b, by omega, by tauto⟩

theorem ctrName_notMem_wvars_driverAt {a : ℕ} (h : a ≤ j) :
    ctrName a ∉ (driverAt q_top cap mb 0 ℓ W φ (j + 1)).wvars :=
  RamDriverWrites.belowVar_notMem_wvars_driverAt ⟨a, by omega, Or.inl rfl⟩

theorem xpName_notMem_wvars_driverAt :
    xpName j ∉ (driverAt q_top cap mb 0 ℓ W φ (j + 1)).wvars :=
  RamDriverWrites.belowVar_notMem_wvars_driverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem curName_notMem_wvars_driverAt :
    curName j ∉ (driverAt q_top cap mb 0 ℓ W φ (j + 1)).wvars :=
  RamDriverWrites.belowVar_notMem_wvars_driverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem tabName_notMem_warrs_driverAt (i : ℕ) :
    tabName j i ∉ (driverAt q_top cap mb 0 ℓ W φ (j + 1)).warrs :=
  RamDriverWrites.belowArr_notMem_warrs_driverAt
    ⟨j, Nat.lt_succ_self j, by tauto⟩

/-! **Rebase B3.** The three names the compacted centre loop header owns
are frames of the whole turn: the nested level is a level at depth
`j + 1`, and the five other phases write no per-depth name but the
depth's connector, its cluster arrays and its tables. -/

theorem cpsName_notMem_warrs_driverAt :
    cpsName j ∉ (driverAt q_top cap mb 0 ℓ W φ (j + 1)).warrs :=
  RamDriverWrites.belowArr_notMem_warrs_driverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem cnumName_notMem_wvars_driverAt :
    cnumName j ∉ (driverAt q_top cap mb 0 ℓ W φ (j + 1)).wvars :=
  RamDriverWrites.belowVar_notMem_wvars_driverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem cixName_notMem_wvars_driverAt :
    cixName j ∉ (driverAt q_top cap mb 0 ℓ W φ (j + 1)).wvars :=
  RamDriverWrites.belowVar_notMem_wvars_driverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

open Classical in
/-- **The loop header's three names survive one turn.** -/
theorem loopFrames :
    cpsName j ∉ (clusterCom q_top cap mb φ j
        (driverAt q_top cap mb 0 ℓ W φ (j + 1))).warrs ∧
      cnumName j ∉ (clusterCom q_top cap mb φ j
        (driverAt q_top cap mb 0 ℓ W φ (j + 1))).wvars ∧
      cixName j ∉ (clusterCom q_top cap mb φ j
        (driverAt q_top cap mb 0 ℓ W φ (j + 1))).wvars :=
  ⟨RamDriverWrites.cpsName_notMem_warrs_clusterCom q_top cap mb j φ
      cpsName_notMem_warrs_driverAt,
    RamDriverWrites.cnumName_notMem_wvars_clusterCom q_top cap mb j φ
      cnumName_notMem_wvars_driverAt,
    RamDriverWrites.cixName_notMem_wvars_clusterCom q_top cap mb j φ
      cixName_notMem_wvars_driverAt⟩

end Frames

/-! ### One turn of the centre loop, and its frame

The two obligations `RamDriverCluster.levelImplements` takes at every
depth below the bottom, at the nested call the recursion actually
makes. -/

section Turn

variable {n : ℕ} {B q_top cap mb ns W ℓ j : ℕ} {φ : Lax3.FirstOrder.FO 0}
  {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
  {ord Xoff Xmem asg : ℕ → ℕ} {mm k : ℕ} {Kb Ki Ksc Ks : ℕ} {Kin : ℕ → ℕ}

/-- The five walks of a turn, at the costs their own files charge. -/
noncomputable def turnCost (n ns cap mb q_top j : ℕ) (φ : Lax3.FirstOrder.FO 0) (Ksc Kin : ℕ) : ℕ :=
  RamDriverDescend.descendCost n ns cap j +
    ((20 * n + 12 * mb + 30) +
      (RamDriverDescend.colourCost n ns cap mb (sigL cap mb j) +
        (Kin + (Ksc + RamDriverBase.rbCost q_top cap mb φ j n))))

/-- **The turn cost, size-indexed** (`integration-design.md` §5.7). The
new slot `s` is the number of members of the block the turn processes,
and the nested driver's budget arrives in `Kin` already read at that
size — which is what makes the level's bill a *sum* over its blocks
instead of `n` copies of the worst turn.

Today's leaves are carrier-driven, so `turnCostSize` ignores the slot
(`turnCostSize_eq` is that, by `rfl`): the Σ interface is landed **above**
the leaf costs, and brief B4's block-driven passes fill the slot without
touching a single consumer of this definition. That separation is the
point of naming the slot now — the alternative is re-threading every
obligation a second time when the leaves land. -/
noncomputable def turnCostSize (n ns cap mb q_top j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (Ksc _s Kin : ℕ) : ℕ :=
  turnCost n ns cap mb q_top j φ Ksc Kin

/-- The size slot is free until B4 fills it. -/
theorem turnCostSize_eq (n ns cap mb q_top j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (Ksc s Kin : ℕ) :
    turnCostSize n ns cap mb q_top j φ Ksc s Kin = turnCost n ns cap mb q_top j φ Ksc Kin := rfl

open Classical in
/-- **One turn of the centre loop, at the nested driver.**

**Rebase B2.** The turn is stated at its own position `k`, and the
nested driver's budget `Kin` is a function of the arena size, read at
this turn's block. `hmono` is what carries it across the descent's
§5.3 clause: the sub-arena is inside the block, so a monotone budget
read at the block pays for it. -/
theorem clusterStepAt
    (hcap : cap = rhoMinus 0 q_top) (hmb : mb = ℓ * (2 * cap + 1)) (hjl : j < ℓ)
    (hB : WordBound B n ns cap mb) (hcsr : CsrGraph G ns O T)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n ns σs.t ≤ Kb)
    (hcostI : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hKsc : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc)
    (hmono : Monotone Kin)
    (hK : turnCostSize n ns cap mb q_top j φ Ksc (blockSize Xoff k)
      (Kin (blockSize Xoff k)) ≤ Ks) :
    ClusterStepImplements B q_top cap mb ns W ℓ j φ G O T M Gm C π ord Xoff Xmem asg mm k
      (driverAt q_top cap mb 0 ℓ W φ (j + 1)) Kin Ks :=
  RamDriverCluster.clusterStepImplements hcap
    (RamDriverDescend.descendStep hmb hjl le_rfl)
    (fun _ _ _ _ => RamDriverDescend.enumStep hB le_rfl)
    (fun _ _ _ _ _ => RamDriverDescend.colourStep le_rfl)
    (fun hinner _ _ _ _ _ _ => RamDriverFrames.innerFrames hinner
      (fun _ ha => turnFrozen_notMem_warrs_driverAt ha)
      (fun _ ha => ctrName_notMem_wvars_driverAt ha)
      xpName_notMem_wvars_driverAt curName_notMem_wvars_driverAt)
    (fun _ _ _ _ _ _ => RamDriverFrames.scatterStep hcsr hB hbnd hcostI hKsc)
    (fun _ _ _ _ _ _ => RamDriverBase.readbackStep hB.one_lt hB.n_lt le_rfl)
    hmono hK

open Classical in
/-- **What one turn leaves alone, at the nested driver.** -/
theorem clusterFramesAt
    (hmb : mb = ℓ * (2 * cap + 1)) (hjl : j < ℓ)
    (hB : WordBound B n ns cap mb) (hcsr : CsrGraph G ns O T)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n ns σs.t ≤ Kb)
    (hcostI : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hKsc : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc)
    (hmono : Monotone Kin)
    (hK : turnCostSize n ns cap mb q_top j φ Ksc (blockSize Xoff k)
      (Kin (blockSize Xoff k)) ≤ Ks) :
    RamDriverCluster.ClusterFrames B q_top cap mb ns W ℓ j φ G O T M Gm C π ord
      Xoff Xmem asg mm k (driverAt q_top cap mb 0 ℓ W φ (j + 1)) Kin Ks :=
  RamDriverFrames.clusterFrames hcsr hB
    (RamDriverDescend.descendStep hmb hjl le_rfl)
    (fun _ _ _ _ => RamDriverDescend.enumStep hB le_rfl)
    (fun _ _ _ _ _ => RamDriverDescend.colourStep le_rfl)
    (fun _ ha => turnFrozen_notMem_warrs_driverAt ha)
      (fun _ ha => ctrName_notMem_wvars_driverAt ha)
    xpName_notMem_wvars_driverAt curName_notMem_wvars_driverAt
    (fun _ _ _ _ _ _ => RamDriverFrames.scatterStep hcsr hB hbnd hcostI hKsc)
    (fun _ _ _ _ _ _ => RamDriverBase.readbackStep hB.one_lt hB.n_lt le_rfl)
    (fun i => tabName_notMem_warrs_driverAt i)
    hmono hK

end Turn

/-! ### The level, and the root

`RamDriverCluster.levelImplements` is the downward induction; what is
supplied here is its six sub-walks and its two availabilities, at
`R = 0`. -/

section Level

variable {n : ℕ} {B q_top cap mb ns W ℓ s Kmass : ℕ} {N : ℕ → ℕ}
  {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
  {Kb : ℕ} {Ki Ksc : ℕ → ℕ} {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}

open Classical in
/-- **Every level of the driver, discharged**, at `R = 0`.

**Rebase B2.** Every cost is read at a size, so the two phase costs get
their own parameters `Ko`/`Kc` with the landed walks' constants as their
side conditions `hKo`/`hKc` — they were unified against the constants
before, which the size slot no longer permits. `hKl` is the level
condition in the Σ shape, which `levelCost_of_sigma` below produces from
`CostRecurrence.exists_driverCostsSigma`.

**Rebase B8.** The level has a third carrier-width phase, the dead-row
sweep, with its own size-read parameter `Kd` and side condition `hKd`;
`Refine.DeadSweep.sweepImplements` is the walk. And `hmass` is **gone**:
the mass mathematics is no longer threaded as an opaque bundle but
*derived*, by `Refine.ArenaBlock.mass_of_alive_compaction`, from the two
facts it actually needs — the cover's block injectivity `hbinj` and the
cover-degree bound `hdeg`. That is what the compaction's new `alive`
clause buys: the Σ interface now reads the turn count against the
**arena** rather than against the carrier. -/
theorem levelAt
    (hcap : cap = rhoMinus 0 q_top) (hmb : mb = ℓ * (2 * cap + 1)) (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBound B n ns cap mb) (hWB : n + W + 1 < B) (hpow : 2 ^ sigL cap mb ℓ < B)
    (hcsr : RamElim.CsrSimple G ns O T)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n ns σs.t ≤ Kb)
    (hcostI : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki j)
    (hKsc : ∀ j < ℓ, Ki j * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc j)
    (hKmono : ∀ j, Monotone (Kl j))
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      turnCostSize n ns cap mb q_top j φ (Ksc j) t (Kl (j + 1) t) ≤ Ks j t)
    (hKbase : ∀ m, RamDriverBot.baseCost q_top cap mb ℓ n φ ≤ Kl ℓ m)
    (hKo : ∀ j m, RamDriverCompose.orderPhaseCost n ns W ≤ Ko j m)
    (hKc : ∀ j m, RamDriverCompose.coverPhaseCost n ns ≤ Kc j m)
    (hKd : ∀ j m, Refine.DeadSweep.sweepCost q_top cap mb j n φ ≤ Kd j m)
    (hbinj : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (mm : ℕ),
      RamCover.CoverOut G M π ord cap mm Xoff Xmem asg → Refine.MassMath.BlockInj n Xoff Xmem)
    (hdeg : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (v : Fin n),
      (Lax12.ColoringNumbers.wreach (RamBfs.masked G M) π (2 * cap) v).ncard ≤ Kmass)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m) :
    ∀ j ≤ ℓ, ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      LevelImplements B q_top cap mb 0 ℓ W ns j φ G O T M Gm C (Kl j (arenaSize n M)) :=
  RamDriverCluster.levelImplements hB hWB hcsr
    (fun _ _ _ _ _ _ => RamElim.implements)
    (fun _ _ _ _ _ _ _ => RamDriverAugment.implements)
    (fun A₀ ord π => RamDriverOrder.coverTurnImplements B n ns G A₀ O T ord π cap)
    hQ hℓ
    (fun M Gm C hbot hbit => by
      rw [driverAt_bot]
      exact ((RamDriverCompose.baseImplements hB hpow hbot hbit).pre
        (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)).mono (hKbase _))
    (fun j _ M _ _ h₁ h₂ h₃ h₄ h₅ =>
      (RamDriverCompose.orderImplements₀ h₁ h₂ h₃ h₄ h₅).mono
        (hKo j (arenaSize n M)))
    (fun j _ M _ _ _ _ h₁ h₂ h₃ h₄ =>
      (RamDriverCompose.coverImplements h₁ h₂ h₃ h₄).mono (hKc j (arenaSize n M)))
    (fun j hj _ _ _ _ _ _ _ _ _ _ =>
      clusterStepAt hcap hmb hj hB hcsr.csr (hbnd j hj) (hcostI j hj) (hKsc j hj)
        (hKmono (j + 1)) (hKs j hj _))
    (fun j hj _ _ _ _ _ _ _ _ _ _ =>
      clusterFramesAt hmb hj hB hcsr.csr (hbnd j hj) (hcostI j hj) (hKsc j hj)
        (hKmono (j + 1)) (hKs j hj _))
    (fun _ _ => loopFrames)
    (fun j _ M _ _ =>
      (Refine.DeadSweep.sweepImplements (jd := j) hB).mono (hKd j (arenaSize n M)))
    (fun M π ord Xoff Xmem asg cps mm cnum hordby hout hcomp =>
      Refine.ArenaBlock.mass_of_alive_compaction hordby hout
        (hbinj M π ord Xoff Xmem asg mm hout) (hdeg M π) hcomp)
    hKl

end Level

/-! ### The level condition, against the solver and against the old interface

Two arithmetic corollaries and no machine: the first says
`CostRecurrence.exists_driverCostsSigma` discharges `levelAt`'s `hKl`,
the second says instantiating the size slots constantly gives back the
interface the driver had before this wave. Together they are the claim
that the re-threading is a *refinement*: nothing downstream can have got
harder. -/

section Bridge

variable {ℓ D : ℕ}

/-- **The solver discharges the level condition.**
`CostRecurrence.exists_driverCostsSigma` produces its turn budget `Kt`
with the loop's per-turn overhead at `8`; the compacted centre loop of
`RamDriverCluster.levelImplements` pays `11`, because B3's loop header
reads the turn's position out of the compacted list before the turn
(`3`) on top of the guard and the bump. The gap is a constant three per
turn and it is absorbed **here**, in the thread, not in the solver:
`exists_driverCostsSigma` is applied with its `turn` slot at
`turnCostSize … + 3`, which makes `hshift` its own turn clause.

The solver stays canonical (B6's minimality), and the driver's interface
stays the one its loop actually produces.

**Rebase B8.** The level has a third carrier-width phase — the dead-row
sweep — and it is absorbed on the *cover* side of the solver's two-phase
shape: the solver is applied with `Kc j m + Kd j m` where it expects the
cover's constant. Nothing about the solver changes; the sweep is a phase
constant read at the arena's size, exactly like `Ko` and `Kc`, and like
them it inherits the touched-only debt (R1.6). -/
theorem levelCost_of_sigma {Ko Kc Kd Ks Kt Kl : ℕ → ℕ → ℕ}
    (hshift : ∀ j s, Ks j s + 3 ≤ Kt j s)
    (hsolve : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ D * (m + 1) →
      Ko j m + ((Kc j m + Kd j m) + ((∑ c ∈ Finset.range t, (Kt j (bs c) + 8)) + 6))
        ≤ Kl j m) :
    ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ D * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m := by
  intro j hj m t htm bs hbs
  have hsum : (∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) ≤
      ∑ c ∈ Finset.range t, (Kt j (bs c) + 8) :=
    Finset.sum_le_sum fun c _ => by have := hshift j (bs c); omega
  have := hsolve j hj m t htm bs hbs
  omega

/-- **The uniform interface is the constant instantiation.** Reading
every size slot as a constant turns the Σ-shaped level condition back
into the one `driverRoot_decides_sentence` took before this wave —
`(Ks j + 11) · n + 6` — so every consumer that could discharge the old
condition can discharge the new one, and the re-threading costs no
slack. `Refine.SigmaLoop.sum_const_eq_uniform` is the loop-side half of
the same statement.

This is what keeps B4, B5 and B7 unblocked while the leaves are still
carrier-driven: they may supply size-blind costs and lose nothing. -/
theorem uniform_recovers_level {n : ℕ} {Ko Kc Kd Ks Kl : ℕ → ℕ}
    (huni : ∀ j < ℓ, Ko j + (Kc j + (Kd j + ((Ks j + 11) * n + 6))) ≤ Kl j) :
    ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → m ≤ n → ∀ bs : ℕ → ℕ,
      (fun (j : ℕ) (_ : ℕ) => Ko j) j m +
        ((fun (j : ℕ) (_ : ℕ) => Kc j) j m +
          ((fun (j : ℕ) (_ : ℕ) => Kd j) j m +
            ((∑ c ∈ Finset.range t, ((fun (j : ℕ) (_ : ℕ) => Ks j) j (bs c) + 11)) + 6)))
        ≤ (fun (j : ℕ) (_ : ℕ) => Kl j) j m := by
  intro j hj m t htm hmn bs
  have hconst : (∑ _c ∈ Finset.range t, (Ks j + 11)) = (Ks j + 11) * t := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
  have hmono : (Ks j + 11) * t ≤ (Ks j + 11) * n :=
    Nat.mul_le_mul_left _ (le_trans htm hmn)
  have := huni j hj
  simp only []
  omega

end Bridge

/-! ### The theorem -/

section Main

variable {n : ℕ} {B q_top cap mb ns W ℓ s Kmass : ℕ} {N : ℕ → ℕ}
  {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ} {x : List ℕ}
  {Kb Kb₀ Ki₀ Kdec Ksent : ℕ} {Ki Ksc : ℕ → ℕ} {Ko Kc Kd Ks Kl : ℕ → ℕ → ℕ}

open Classical in
/-- **The RAM driver decides the model-checking answer.**

Handed the tape encoding of a graph, `RamDriver.driverRoot` at `R = 0`
runs — inside the cost `Kdec + (Kl 0 n + Ksent)` — and writes `[1]` if
the first-order sentence `φ` holds in the graph and `[0]` if it does not.

Nothing about the machine is a hypothesis: every obligation of
`RamDriver.driver_correct`, of `RamDriverCluster.levelImplements` and of
the cluster step is instantiated by the walk that discharges it. What is
left is the input word's own data, the parameter equations, the campaign
mathematics `hQ`, and free cost parameters with their side conditions.

**Rebase B2 (§5.8).** The program, the precondition and the
postcondition are **byte-identical** to what they were; the cost is
`Kl 0 n` because a level's budget is now a function of the size of the
arena it runs on and the root's mask kills nothing
(`RamDriver.arenaSize_of_all_alive`). `hKs`/`hKl` are the §5.7/§5.6
shapes, `hKmono` is new, and — rebase B8 — the mass bundle `hmass` has
become the two facts it is derived from (`hbinj`, `hdeg`) while the
level gains its dead-row sweep (`hKd`). The conclusion is untouched. -/
theorem driverRoot_decides_sentence
    -- the input word
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hO : ∀ i ≤ n, O i = offset x i) (hT : ∀ i < ns, T i = target x i)
    (hxB : ∀ v ∈ x, v < B) (hcsr : RamElim.CsrSimple G ns O T)
    -- the parameters
    (hrank : Lax3.FirstOrder.rank φ ≤ q_top) (hcap : cap = rhoMinus 0 q_top)
    (hmb : mb = ℓ * (2 * cap + 1)) (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBound B n ns cap mb) (hWB : n + W + 1 < B) (hpow : 2 ^ sigL cap mb ℓ < B)
    -- the mathematics of the campaign
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    -- the value bounds and the costs
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n ns σs.t ≤ Kb)
    (hcostI : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki j)
    (hKsc : ∀ j < ℓ, Ki j * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc j)
    (hKmono : ∀ j, Monotone (Kl j))
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      turnCostSize n ns cap mb q_top j φ (Ksc j) t (Kl (j + 1) t) ≤ Ks j t)
    (hKbase : ∀ m, RamDriverBot.baseCost q_top cap mb ℓ n φ ≤ Kl ℓ m)
    (hKo : ∀ j m, RamDriverCompose.orderPhaseCost n ns W ≤ Ko j m)
    (hKc : ∀ j m, RamDriverCompose.coverPhaseCost n ns ≤ Kc j m)
    (hKd : ∀ j m, Refine.DeadSweep.sweepCost q_top cap mb j n φ ≤ Kd j m)
    (hbinj : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (mm : ℕ),
      RamCover.CoverOut G M π ord cap mm Xoff Xmem asg → Refine.MassMath.BlockInj n Xoff Xmem)
    (hdeg : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (v : Fin n),
      (Lax12.ColoringNumbers.wreach (RamBfs.masked G M) π (2 * cap) v).ncard ≤ Kmass)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + (Kd j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)))
        ≤ Kl j m)
    (hKdec : RamDriverIO.decodeCost n ns ≤ Kdec)
    (hatoms : ∀ s ∈ (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2,
      s.r + 1 < B ∧ s.t < B ∧ RamDriverIO.atomCost n ns s.t ≤ Kb₀)
    (hKsent : Kb₀ * (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2.length + 1 +
      (1 + (RamDriverIO.sentenceExpr q_top cap mb φ).size) ≤ Ksent) :
    Spec B (fun σ => DecodeMem n ns σ ∧ LevelMem B n cap mb σ ∧ DepthMem n cap mb σ ∧
        OrderMem B n ns W σ ∧ TablesSized q_top cap mb φ n σ ∧
        BaseArrs B q_top cap mb ℓ φ σ ∧ σ.inp = x ∧ σ.out = [])
      (driverRoot q_top cap mb 0 ℓ W φ)
      (fun _ σ' => σ'.out = [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
      (Kdec + (Kl 0 n + Ksent)) :=
  driver_correct hrank hB hxB
    (RamDriverIO.decodeImplements hx hns hO hT hKdec)
    (fun M Gm C hall => by
      have h := levelAt hcap hmb hℓ hB hWB hpow hcsr hQ hbnd hcostI hKsc hKmono hKs
        hKbase hKo hKc hKd hbinj hdeg hKl 0 (Nat.zero_le ℓ) M Gm C
      rwa [arenaSize_of_all_alive hall] at h)
    (fun _ _ _ => RamDriverIO.sentenceImplements hrank hcsr.csr hatoms hKsent)

end Main

end Lax3Proofs.RamDriverRoot
