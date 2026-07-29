import Lax3Proofs.RamDriverWrites
import Lax3Proofs.RamDriverAugment

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
  RamDriverWrites.belowVar_notMem_wvars_driverAt
    ⟨j, Nat.lt_succ_self j, Or.inr (Or.inl rfl)⟩

theorem curName_notMem_wvars_driverAt :
    curName j ∉ (driverAt q_top cap mb 0 ℓ W φ (j + 1)).wvars :=
  RamDriverWrites.belowVar_notMem_wvars_driverAt
    ⟨j, Nat.lt_succ_self j, Or.inr (Or.inr rfl)⟩

theorem tabName_notMem_warrs_driverAt (i : ℕ) :
    tabName j i ∉ (driverAt q_top cap mb 0 ℓ W φ (j + 1)).warrs :=
  RamDriverWrites.belowArr_notMem_warrs_driverAt
    ⟨j, Nat.lt_succ_self j, by tauto⟩

end Frames

/-! ### One turn of the centre loop, and its frame

The two obligations `RamDriverCluster.levelImplements` takes at every
depth below the bottom, at the nested call the recursion actually
makes. -/

section Turn

variable {n : ℕ} {B q_top cap mb ns W ℓ j : ℕ} {φ : Lax3.FirstOrder.FO 0}
  {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
  {ord Xoff Xmem asg : ℕ → ℕ} {mm : ℕ} {Kb Ki Ksc Kin Ks : ℕ}

/-- The five walks of a turn, at the costs their own files charge. -/
noncomputable def turnCost (n ns cap mb q_top j : ℕ) (φ : Lax3.FirstOrder.FO 0) (Ksc Kin : ℕ) : ℕ :=
  RamDriverDescend.descendCost n ns cap j +
    ((20 * n + 12 * mb + 30) +
      (RamDriverDescend.colourCost n ns cap mb (sigL cap mb j) +
        (Kin + (Ksc + RamDriverBase.rbCost q_top cap mb φ j n))))

open Classical in
/-- **One turn of the centre loop, at the nested driver.** -/
theorem clusterStepAt
    (hcap : cap = rhoMinus 0 q_top) (hmb : mb = ℓ * (2 * cap + 1)) (hjl : j < ℓ)
    (hB : WordBound B n ns cap mb) (hcsr : CsrGraph G ns O T)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t < B ∧ RamDriverIO.atomCost n ns σs.t ≤ Kb)
    (hcostI : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hKsc : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc)
    (hK : turnCost n ns cap mb q_top j φ Ksc Kin ≤ Ks) :
    ClusterStepImplements B q_top cap mb ns W ℓ j φ G O T M Gm C π ord Xoff Xmem asg mm
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
    hK

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
    (hK : turnCost n ns cap mb q_top j φ Ksc Kin ≤ Ks) :
    RamDriverCluster.ClusterFrames B q_top cap mb ns W ℓ j φ G O T M Gm C π ord
      Xoff Xmem asg mm (driverAt q_top cap mb 0 ℓ W φ (j + 1)) Kin Ks :=
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
    hK

end Turn

/-! ### The level, and the root

`RamDriverCluster.levelImplements` is the downward induction; what is
supplied here is its six sub-walks and its two availabilities, at
`R = 0`. -/

section Level

variable {n : ℕ} {B q_top cap mb ns W ℓ s : ℕ} {N : ℕ → ℕ}
  {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
  {Kb : ℕ} {Ki Ksc Ks Kl : ℕ → ℕ}

open Classical in
/-- **Every level of the driver, discharged**, at `R = 0`. -/
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
    (hKs : ∀ j < ℓ, turnCost n ns cap mb q_top j φ (Ksc j) (Kl (j + 1)) ≤ Ks j)
    (hKbase : RamDriverBot.baseCost q_top cap mb ℓ n φ ≤ Kl ℓ)
    (hKl : ∀ j < ℓ, RamDriverCompose.orderPhaseCost n ns W +
      (RamDriverCompose.coverPhaseCost n ns + ((Ks j + 8) * n + 6)) ≤ Kl j) :
    ∀ j ≤ ℓ, ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      LevelImplements B q_top cap mb 0 ℓ W ns j φ G O T M Gm C (Kl j) :=
  RamDriverCluster.levelImplements hB hWB hcsr
    (fun _ _ _ _ _ _ => RamElim.implements)
    (fun _ _ _ _ _ _ _ => RamDriverAugment.implements)
    (fun A₀ ord π => RamDriverOrder.coverTurnImplements B n ns G A₀ O T ord π cap)
    hQ hℓ
    (fun M Gm C hbot hbit => by
      rw [driverAt_bot]
      exact ((RamDriverCompose.baseImplements hB hpow hbot hbit).pre
        (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)).mono hKbase)
    (fun _ _ _ _ _ => RamDriverCompose.orderImplements₀)
    (fun _ _ _ _ _ _ _ => RamDriverCompose.coverImplements)
    (fun j hj _ _ _ _ _ _ _ _ _ =>
      clusterStepAt hcap hmb hj hB hcsr.csr (hbnd j hj) (hcostI j hj) (hKsc j hj) (hKs j hj))
    (fun j hj _ _ _ _ _ _ _ _ _ =>
      clusterFramesAt hmb hj hB hcsr.csr (hbnd j hj) (hcostI j hj) (hKsc j hj) (hKs j hj))
    hKl

end Level

/-! ### The theorem -/

section Main

variable {n : ℕ} {B q_top cap mb ns W ℓ s : ℕ} {N : ℕ → ℕ}
  {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ} {x : List ℕ}
  {Kb Kb₀ Ki₀ Kdec Ksent : ℕ} {Ki Ksc Ks Kl : ℕ → ℕ}

open Classical in
/-- **The RAM driver decides the model-checking answer.**

Handed the tape encoding of a graph, `RamDriver.driverRoot` at `R = 0`
runs — inside the cost `Kdec + (Kl 0 + Ksent)` — and writes `[1]` if the
first-order sentence `φ` holds in the graph and `[0]` if it does not.

Nothing about the machine is a hypothesis: every obligation of
`RamDriver.driver_correct`, of `RamDriverCluster.levelImplements` and of
the cluster step is instantiated by the walk that discharges it. What is
left is the input word's own data, the parameter equations, the campaign
mathematics `hQ`, and free cost parameters with their side
conditions. -/
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
    (hKs : ∀ j < ℓ, turnCost n ns cap mb q_top j φ (Ksc j) (Kl (j + 1)) ≤ Ks j)
    (hKbase : RamDriverBot.baseCost q_top cap mb ℓ n φ ≤ Kl ℓ)
    (hKl : ∀ j < ℓ, RamDriverCompose.orderPhaseCost n ns W +
      (RamDriverCompose.coverPhaseCost n ns + ((Ks j + 8) * n + 6)) ≤ Kl j)
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
      (Kdec + (Kl 0 + Ksent)) :=
  driver_correct hrank hB hxB
    (RamDriverIO.decodeImplements hx hns hO hT hKdec)
    (fun M Gm C _ =>
      levelAt hcap hmb hℓ hB hWB hpow hcsr hQ hbnd hcostI hKsc hKs hKbase hKl 0
        (Nat.zero_le ℓ) M Gm C)
    (fun _ _ _ => RamDriverIO.sentenceImplements hrank hcsr.csr hatoms hKsent)

end Main

end Lax3Proofs.RamDriverRoot
