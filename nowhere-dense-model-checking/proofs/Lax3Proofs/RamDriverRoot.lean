import Lax3Proofs.RamDriverWrites
import Lax3Proofs.RamDriverAugment
import Lax3Proofs.Refine.ArenaPointer
import Lax3Proofs.Refine.DeadSweep
import Lax3Proofs.Refine.KillPass
import Lax3Proofs.Refine.KillListWalk
import Lax3Proofs.Refine.MassWeight
import Lax3Proofs.Refine.ScatterDeadTurn

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

  **The word bound is `RamDriver.WordBoundK` at `Kmass`** (rebase E-mem,
  leaf W3), not the carrier bound `RamDriver.WordBound`: the cluster
  arena's pointer ceiling is read at the cover-degree parameter this
  theorem's own `hdeg` slot bounds, so the arena clause is
  `n·Kmass + n + ns + 2·cap + 2 < B` instead of `n² + ns + 2·cap + 2 < B`.
  No new parameter enters — `Kmass` is `hdeg`'s — and no conclusion
  moves; the two addresses into the arena that used to come off
  `WordBound.cover` are supplied by the mass readings
  `Refine.ArenaPointer.ptrWords_of_mass` / `massWords_of_mass` at the
  ordering the cover phase produced. What it buys is the bridge:
  `Refine.BridgeSeamProbe.no_word_size_for_sparse` refuted the carrier
  bound against `Compile.Layout.FitsWords` at word lengths C0's own
  domain admits, and `Refine.BridgeCrossing` compiles that the same
  argument at this slot is false.
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
| `ScatterStep` | `Refine.ScatterDeadTurn.scatterDeadStep` |
| `ReadbackStep` | `RamDriverBase.readbackStep` |
| `KillListStep` | `killListStep` below, on `Refine.KillListWalk` |
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

**The two data hypotheses, and their producers** (rebase F-c-3). Of the
hypotheses above that are neither input-word data, parameter equations
nor cost side conditions, exactly two were bare — carried because
nothing produced them:

| slot | producer |
|------|----------|
| `hbinj` | `blockInj_slot`, off `RamCover.CoverOut.block_inj` (B3) |
| `hdeg` | `wreachDeg_of_orderP`, off the phase's `P` slot at `R = R*` |

The first is closed here (`driverRoot_decides_sentence_binj`). The
second is closed *modulo one obligation*: the step from the slot to the
coefficient is proved, the threading through
`RamDriverCluster.levelImplements` is done, and what is left is the
`R > 0` phase walk `RamDriverCompose.OrderImplementsR`. See the two
sections below.
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
open Lax3Proofs.Refine.MassWeight (arenaWeight blockWeight)
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
    a ∉ (driverAt q_top cap mb 0 ℓ φ (j + 1)).warrs := by
  refine RamDriverWrites.belowArr_notMem_warrs_driverAt ?_
  rcases h with hm | ⟨c, rfl⟩ | ⟨b, hb, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨j, Nat.lt_succ_self j, by tauto⟩
  · exact ⟨j, Nat.lt_succ_self j, by tauto⟩
  · exact ⟨b, by omega, by tauto⟩

theorem ctrName_notMem_wvars_driverAt {a : ℕ} (h : a ≤ j) :
    ctrName a ∉ (driverAt q_top cap mb 0 ℓ φ (j + 1)).wvars :=
  RamDriverWrites.belowVar_notMem_wvars_driverAt ⟨a, by omega, Or.inl rfl⟩

theorem xpName_notMem_wvars_driverAt :
    xpName j ∉ (driverAt q_top cap mb 0 ℓ φ (j + 1)).wvars :=
  RamDriverWrites.belowVar_notMem_wvars_driverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

/-- The member count of any depth at or below `j` is not assigned by a
level at depth `j + 1` (rebase E-mem): the descent writes its own
child's count, which is depth `j + 2` or deeper. -/
theorem mnumName_notMem_wvars_driverAt {a : ℕ} (h : a ≤ j) :
    mnumName a ∉ (driverAt q_top cap mb 0 ℓ φ (j + 1)).wvars :=
  RamDriverWrites.belowVar_notMem_wvars_driverAt ⟨a, by omega, by tauto⟩

theorem curName_notMem_wvars_driverAt :
    curName j ∉ (driverAt q_top cap mb 0 ℓ φ (j + 1)).wvars :=
  RamDriverWrites.belowVar_notMem_wvars_driverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

/-- **The kill count of the enclosing turn survives the recursion**
(wave R1.8-T3-flip (c1c)): the list and its count are per-depth names of
depth `j`, and a level at depth `j + 1` writes no name of a depth below
its own. This is what carries `RamDriverCluster.KillListAt` across the
nested call, so the atom pass may read the turn's kills afterwards. -/
theorem kkName_notMem_wvars_driverAt :
    kkName j ∉ (driverAt q_top cap mb 0 ℓ φ (j + 1)).wvars :=
  RamDriverWrites.belowVar_notMem_wvars_driverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem tabName_notMem_warrs_driverAt (i : ℕ) :
    tabName j i ∉ (driverAt q_top cap mb 0 ℓ φ (j + 1)).warrs :=
  RamDriverWrites.belowArr_notMem_warrs_driverAt
    ⟨j, Nat.lt_succ_self j, by tauto⟩

/-! **Rebase B3.** The three names the compacted centre loop header owns
are frames of the whole turn: the nested level is a level at depth
`j + 1`, and the five other phases write no per-depth name but the
depth's connector, its cluster arrays and its tables. -/

theorem cpsName_notMem_warrs_driverAt :
    cpsName j ∉ (driverAt q_top cap mb 0 ℓ φ (j + 1)).warrs :=
  RamDriverWrites.belowArr_notMem_warrs_driverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem cnumName_notMem_wvars_driverAt :
    cnumName j ∉ (driverAt q_top cap mb 0 ℓ φ (j + 1)).wvars :=
  RamDriverWrites.belowVar_notMem_wvars_driverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem cixName_notMem_wvars_driverAt :
    cixName j ∉ (driverAt q_top cap mb 0 ℓ φ (j + 1)).wvars :=
  RamDriverWrites.belowVar_notMem_wvars_driverAt ⟨j, Nat.lt_succ_self j, by tauto⟩

open Classical in
/-- **The loop header's three names survive one turn.** -/
theorem loopFrames :
    cpsName j ∉ (clusterCom q_top cap mb φ j
        (driverAt q_top cap mb 0 ℓ φ (j + 1))).warrs ∧
      cnumName j ∉ (clusterCom q_top cap mb φ j
        (driverAt q_top cap mb 0 ℓ φ (j + 1))).wvars ∧
      cixName j ∉ (clusterCom q_top cap mb φ j
        (driverAt q_top cap mb 0 ℓ φ (j + 1))).wvars :=
  ⟨RamDriverWrites.cpsName_notMem_warrs_clusterCom q_top cap mb j φ
      cpsName_notMem_warrs_driverAt,
    RamDriverWrites.cnumName_notMem_wvars_clusterCom q_top cap mb j φ
      cnumName_notMem_wvars_driverAt,
    RamDriverWrites.cixName_notMem_wvars_clusterCom q_top cap mb j φ
      cixName_notMem_wvars_driverAt⟩

end Frames

/-! ### The kill list, at the surface the turn consumes it at

**Wave R1.8-T3-flip (a2).** `Refine.KillListWalk` is the walk;
`RamDriverCluster.KillListStep` is the surface, and this is the step
between them. There is no mathematics: the pass writes one array — the
depth's own kill list, a name no clause of a turn is about — and five
scalars, so every "unchanged" conjunct of the postcondition is one frame
lemma off `RamDriverWrites.warrs_killListCom` / `wvars_killListCom`, and
the one new conjunct is the walk's own enumeration re-read at the turn's
`X` and `W`.

That re-reading is the only thing worth naming. The walk's guard is the
two cells `alv[v]·clu[v]` at a *buffer entry*, and `KillListAt` speaks
about the set `{v | M v ≠ 0 ∧ v ∈ X ∧ v ∈ W}` — which is exactly
`RamDriverCluster.KillRowsAt`'s domain. The two are the same set because
`ClusterData` says the buffer's range is the batch's cluster half
(`Set.range w = W ∩ X`, wave R1.8-T3-flip (c2a)) and the cluster array
marks the cluster (`markSet n Xa = X`); that is where the turn's data
enters and nothing else does. The narrowing costs the re-reading
nothing: the guard already tests `clu[v]`, so the entries it drops are
exactly the ones the guard rejected. -/

section KillList

/-- **The kill pass leaves the padding buffer alone**, so the `ClusterWa`
seam runs one link further than it did in wave R1.8-T2: the kill pass
writes the child depth's tables and the evaluator's scratch, and `"wa"`
is neither. This is what makes the kill list the *fourth* consumer of the
seam, still strictly before the nested call. -/
theorem wa_notMem_warrs_killCom (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    "wa" ∉ (killCom q_top cap mb j φ).warrs :=
  Refine.KillPass.notMem_warrs_killCom
    (fun β hβ => (tableRank_of_mem_tablesAt (j + 1) β hβ).1)
    (fun i => RamDriverBase.lit_ne_tabName (by decide) (j + 1) i)
    (RamDriverBot.not_ext_of_not_prefix (by decide))

variable {n : ℕ} {B q_top cap mb ns Ws j : ℕ} {φ : Lax3.FirstOrder.FO 0}
  {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
  {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ} {X W : Set (Fin n)} {w : Fin mb → Fin n}
  {Alv' Gam' : ℕ → ℕ} {C' : ℕ → ℕ → ℕ}

open Lax3Proofs.RamDriverCluster (TurnPre ClusterData ClusterWa KillRowsAt KillListAt
  KillListStep markSet)

/-- **The kill list pass at the surface the turn consumes it at.**
`RamDriverCluster.KillListStep`, from
`Refine.KillListPass.killListCom_spec` and the frame. -/
theorem killListStep :
    KillListStep B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' (Refine.KillListPass.killListCost mb) := by
  intro d hB
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hturn, hdat, hwa, hcolarr, hplay, htsz, hkrows⟩ := hσ
  obtain ⟨Xa, hXa, hXaS, hXaB⟩ := hdat.1.1
  have hdep : DepthMem n cap mb σ := hturn.1.2.2.2.2.2.2.2.2.2.2.1
  -- the walk
  obtain ⟨σ', hrun, hlist⟩ :=
    (Refine.KillListPass.killListCom_spec (M := M) (Xa := Xa) (w := w) (j := j)
        hB.one_lt hB.n_lt hB.mb_lt (fun z hz => hturn.1.2.2.2.2.2.2.1 z hz) hXaB).run (σ := σ)
      ⟨Refine.KillPass.clusterWa_eq hwa, hturn.1.2.2.2.1, hXa, hdep.kl j⟩
  -- the frame, once: one array and five scalars
  have harr : ∀ a : String, a ≠ klName j → σ'.arrs a = σ.arrs a :=
    fun a ha => hrun.frame_arr a (RamDriverWrites.notMem_warrs_killListCom ha)
  have hvar : ∀ y : String, y ≠ kkName j → y ≠ "kk" → y ≠ "kv" → y ≠ "kf" → y ≠ "kt" →
      σ'.vars y = σ.vars y :=
    fun y h₁ h₂ h₃ h₄ h₅ =>
      hrun.frame_var y (RamDriverWrites.notMem_wvars_killListCom h₁ h₂ h₃ h₄ h₅)
  -- the four name shapes every clause below is an instance of
  have harrDepth : ∀ b : ℕ, σ'.arrs (alvName b) = σ.arrs (alvName b) := fun b =>
    harr _ (by simp [alvName, klName, String.ext_iff])
  have harrGam : ∀ b : ℕ, σ'.arrs (gamName b) = σ.arrs (gamName b) := fun b =>
    harr _ (by simp [gamName, klName, String.ext_iff])
  have harrCol : ∀ b q : ℕ, σ'.arrs (colName b q) = σ.arrs (colName b q) := fun b q =>
    harr _ (by simp [colName, klName, String.ext_iff])
  have harrMem : ∀ b : ℕ, σ'.arrs (memName b) = σ.arrs (memName b) := fun b =>
    harr _ (by simp [memName, klName, String.ext_iff])
  have hvarMm : ∀ b : ℕ, σ'.vars (mnumName b) = σ.vars (mnumName b) := fun b =>
    hvar _ (by simp [mnumName, kkName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, String.ext_iff])
  -- the level's own precondition
  have hlev' : LevelPre B n cap mb ns Ws O T j M Gm C σ' :=
    RamDriverCompose.levelPre_run hturn.1 hrun
      (RamDriverWrites.notMem_wvars_killListCom (by simp [kkName, String.ext_iff])
        (by decide) (by decide) (by decide) (by decide))
      (RamDriverWrites.notMem_wvars_killListCom (by simp [kkName, String.ext_iff])
        (by decide) (by decide) (by decide) (by decide))
      (RamDriverWrites.notMem_wvars_killListCom (by simp [kkName, String.ext_iff])
        (by decide) (by decide) (by decide) (by decide))
      (RamDriverWrites.notMem_warrs_killListCom (by simp [klName, String.ext_iff]))
      (RamDriverWrites.notMem_warrs_killListCom (by simp [klName, String.ext_iff]))
      (RamDriverWrites.notMem_warrs_killListCom (by simp [alvName, klName, String.ext_iff]))
      (RamDriverWrites.notMem_warrs_killListCom (by simp [gamName, klName, String.ext_iff]))
      (fun _ => RamDriverWrites.notMem_warrs_killListCom
        (by simp [colName, klName, String.ext_iff]))
      (fun a ha => by
        simp only [RamDriverCompose.zeroArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact RamDriverWrites.notMem_warrs_killListCom (by simp [klName, String.ext_iff]))
      (RamDriverWrites.notMem_warrs_killListCom (by simp [memName, klName, String.ext_iff]))
      (RamDriverWrites.notMem_wvars_killListCom (by simp [mnumName, kkName, String.ext_iff])
        (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
        (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff]))
  refine ⟨σ', _, hrun, le_rfl, ⟨hlev', ?_, ?_⟩, ⟨?_, hdat.2⟩, fun c hc => ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- the recorded play of the turn's own depth
    exact hturn.2.1.congr
      (fun a _ => hvar (ctrName a) (by simp [ctrName, kkName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff]))
      (fun a _ => harrGam a)
  · -- the cover's answers
    exact Refine.KillPass.coverHeld_congr hturn.2.2
      (harr (ordName j) (by simp [ordName, klName, String.ext_iff]))
      (harr (xofName j) (by simp [xofName, klName, String.ext_iff]))
      (harr (xmmName j) (by simp [xmmName, klName, String.ext_iff]))
      (harr (asgName j) (by simp [asgName, klName, String.ext_iff]))
      (hvar (xpName j) (by simp [xpName, kkName, String.ext_iff])
        (by simp [xpName, String.ext_iff]) (by simp [xpName, String.ext_iff])
        (by simp [xpName, String.ext_iff]) (by simp [xpName, String.ext_iff]))
  · -- the descent's data
    exact Refine.KillPass.batchData_congr hdat.1
      (harr (cluName j) (by simp [cluName, klName, String.ext_iff]))
      (harr (batName j) (by simp [batName, klName, String.ext_iff]))
      (harr (resName j) (by simp [resName, klName, String.ext_iff]))
      (harrDepth (j + 1)) (harrGam (j + 1)) (harrMem (j + 1)) (hvarMm (j + 1))
  · rw [harrCol (j + 1) c]; exact hcolarr c hc
  · -- and the child depth's recorded play
    exact hplay.congr
      (fun a _ => hvar (ctrName a) (by simp [ctrName, kkName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff]))
      (fun a _ => harrGam a)
  · exact hrun.out_eq (RamDriverWrites.noWrite_killListCom mb j)
  · exact hvar (curName j) (by simp [curName, kkName, String.ext_iff])
      (by simp [curName, String.ext_iff]) (by simp [curName, String.ext_iff])
      (by simp [curName, String.ext_iff]) (by simp [curName, String.ext_iff])
  · -- the kill pass's rows are about the child's tables, which this pass never names
    intro i hi Tb hTb
    exact hkrows i hi Tb (by rw [← harr (tabName (j + 1) i)
      (by simp [tabName, klName, String.ext_iff])]; exact hTb)
  · -- **the list, re-read at the turn's cluster and batch**
    obtain ⟨kl, kq, hkl, hkq, hqle, hkln, hinj, hsound, hcomp⟩ := hlist
    refine ⟨kl, kq, hkl, hkq, hqle, hkln, hinj, fun e he => ?_, fun v hMv hvX hvW => ?_⟩
    · obtain ⟨hM, hXv, p, hp⟩ := hsound e he
      refine ⟨w p, hp, by rw [hp]; exact hM, ?_, ?_⟩
      · rw [← hXaS]; show Xa (w p : ℕ) ≠ 0; rw [hp]; exact hXv
      · exact hdat.mem_batch p
    · obtain ⟨p, hp⟩ : ∃ p : Fin mb, w p = v := by
        have : v ∈ Set.range w := by rw [hdat.2]; exact ⟨hvW, hvX⟩
        exact this
      obtain ⟨e, he, hee⟩ := hcomp p (by rw [hp]; exact hMv)
        (by rw [hp]; rw [← hXaS] at hvX; exact hvX)
      exact ⟨e, he, by rw [hee, hp]⟩

end KillList

/-! ### One turn of the centre loop, and its frame

The two obligations `RamDriverCluster.levelImplements` takes at every
depth below the bottom, at the nested call the recursion actually
makes. -/

section Turn

variable {n : ℕ} {B q_top cap mb ns W ℓ j Kmass : ℕ} {φ : Lax3.FirstOrder.FO 0}
  {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
  {ord Xoff Xmem asg : ℕ → ℕ} {mm k : ℕ} {Kb Ki Ksc Ks : ℕ} {Kin : ℕ → ℕ}

/-- The seven walks of a turn, at the costs their own files charge.

**Wave R1.8-T2.** The kill pass is the fourth, and its charge is absorbed
here — inside the turn's own slot, which is design §7's disposition F-4.
It is one of the two summands that mention neither `n` nor `ns`:
`Refine.KillPass.killCost` is `(blockCost + 21) · mb + 6`, carrier-blind,
read at the child depth's table because that is the row it writes.

**Wave R1.8-T3-flip (a2).** The kill list is the fifth, and its charge is
absorbed the same way and for the same reason:
`Refine.KillListPass.killListCost mb = (20·mb + 64)·mb + 8` is
carrier-blind too — `n` does not occur — and quadratic in the *formula*
sized `mb = ℓ·(2·cap+1)`, which is the design's accepted `O(mb²)` dedupe
class (§6 (a)). The absorption is **not** free at the old constant: the
probe's `ct = 284` was an exact fit, so `Refine.KillListPass.ctKL` moves
it by exactly the measured instance and
`Refine.KillListPass.killList_interface_closes` re-runs the Σ closure
there — the closure is indifferent to the turn coefficient's value,
which is F-4's disposition, so absorbing the list moves a number and no
interface. -/
noncomputable def turnCost (n ns cap mb q_top j : ℕ) (φ : Lax3.FirstOrder.FO 0) (Ksc Kin : ℕ) : ℕ :=
  RamDriverDescend.descendCost n ns cap j +
    ((23 * n + 12 * mb + 30) +
      (RamDriverDescend.colourCost n ns cap mb (sigL cap mb j) +
        (Refine.KillPass.killCost q_top cap mb (j + 1) φ +
          (Refine.KillListPass.killListCost mb +
            (Kin + (Ksc + RamDriverBase.rbCost q_top cap mb φ j n))))))

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

**Rebase B2, read at the arena weight since G2/E6.** The turn is stated
at its own position `k`, and the nested driver's budget `Kin` is a
function of the **arena weight** (`Refine.MassWeight.arenaWeight`, at
the level's fixed graph `G`), read at this turn's block weight. `hmono`
carries it across the descent's §5.3 inclusion clause via
`Refine.MassWeight.arenaWeight_le_blockWeight`: the sub-arena is inside
the cluster, the cluster weighs at most its block, so a monotone budget
read at the block's weight pays for it. -/
theorem clusterStepAt
    (hcap : cap = rhoMinus 0 q_top) (hmb : mb = ℓ * (2 * cap + 1)) (hjl : j < ℓ)
    (hB : WordBoundK B n Kmass ns cap mb) (hcsr : CsrGraph G ns O T)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧
          Refine.ScatterDeadTurn.deadAtomK σs.β n n mb n ns n σs.t ≤ Kb)
    (hcostI : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hKsc : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc)
    (hmono : Monotone Kin)
    (hK : turnCostSize n ns cap mb q_top j φ Ksc (blockWeight n G Xoff Xmem k)
      (Kin (blockWeight n G Xoff Xmem k)) ≤ Ks) :
    ClusterStepImplements B q_top cap mb ns W ℓ j φ G O T M Gm C π ord Xoff Xmem asg mm k
      (arenaWeight n G) (driverAt q_top cap mb 0 ℓ φ (j + 1)) Kin Ks :=
  RamDriverCluster.clusterStepImplements hcap
    (RamDriverDescend.descendStep hmb hjl le_rfl)
    (fun _ _ _ _ => RamDriverDescend.enumStep hB le_rfl)
    (fun _ _ _ _ _ => RamDriverDescend.colourStep le_rfl)
    (RamDriverFrames.wa_notMem_warrs_colourCom cap mb j)
    (fun _ _ _ _ _ _ => Refine.KillPass.killStep)
    (wa_notMem_warrs_killCom q_top cap mb j φ)
    (fun _ _ _ _ _ _ => killListStep)
    (fun hinner _ _ _ _ _ _ => RamDriverFrames.innerFrames hinner
      (fun _ ha => turnFrozen_notMem_warrs_driverAt ha)
      (fun _ ha => ctrName_notMem_wvars_driverAt ha)
      xpName_notMem_wvars_driverAt curName_notMem_wvars_driverAt
      (fun _ ha => mnumName_notMem_wvars_driverAt ha)
      kkName_notMem_wvars_driverAt)
    (fun _ _ _ _ _ _ =>
      Refine.ScatterDeadTurn.scatterDeadStep hcsr hB hbnd hcostI hKsc)
    (Refine.ScatterDeadPass.ballBudget_carrier hcsr)
    (fun _ _ _ _ _ _ => RamDriverBase.readbackStep hB.one_lt hB.n_lt le_rfl)
    hmono
    (fun _ hkn hout hsub =>
      Refine.MassWeight.arenaWeight_le_blockWeight G hout hkn hsub)
    hK

open Classical in
/-- **What one turn leaves alone, at the nested driver.** -/
theorem clusterFramesAt
    (hmb : mb = ℓ * (2 * cap + 1)) (hjl : j < ℓ)
    (hB : WordBoundK B n Kmass ns cap mb) (hcsr : CsrGraph G ns O T)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧
          Refine.ScatterDeadTurn.deadAtomK σs.β n n mb n ns n σs.t ≤ Kb)
    (hcostI : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hKsc : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc)
    (hmono : Monotone Kin)
    (hK : turnCostSize n ns cap mb q_top j φ Ksc (blockWeight n G Xoff Xmem k)
      (Kin (blockWeight n G Xoff Xmem k)) ≤ Ks) :
    RamDriverCluster.ClusterFrames B q_top cap mb ns W ℓ j φ G O T M Gm C π ord
      Xoff Xmem asg mm k (arenaWeight n G)
      (driverAt q_top cap mb 0 ℓ φ (j + 1)) Kin Ks :=
  RamDriverFrames.clusterFrames hcsr hB
    (RamDriverDescend.descendStep hmb hjl le_rfl)
    (fun _ _ _ _ => RamDriverDescend.enumStep hB le_rfl)
    (fun _ _ _ _ _ => RamDriverDescend.colourStep le_rfl)
    (fun _ _ _ _ _ _ => Refine.KillPass.killStep)
    (fun i => Refine.KillPass.notMem_warrs_killCom
      (fun β hβ => (tableRank_of_mem_tablesAt (j + 1) β hβ).1)
      (fun i' => RamDriverBase.tabName_ne_succ j i i')
      (fun hc => RamDriverBot.not_ext_b_tabName j i (RamDriverCompose.ext_b_of_ext_bb hc)))
    (wa_notMem_warrs_killCom q_top cap mb j φ)
    (fun i => RamDriverWrites.notMem_warrs_killListCom
      (by simp [tabName, klName, String.ext_iff]))
    (fun _ _ _ _ _ _ => killListStep)
    (fun _ ha => turnFrozen_notMem_warrs_driverAt ha)
      (fun _ ha => ctrName_notMem_wvars_driverAt ha)
    xpName_notMem_wvars_driverAt curName_notMem_wvars_driverAt
    (fun _ ha => mnumName_notMem_wvars_driverAt ha)
    kkName_notMem_wvars_driverAt
    (fun _ _ _ _ _ _ =>
      Refine.ScatterDeadTurn.scatterDeadStep hcsr hB hbnd hcostI hKsc)
    (fun i => RamDriverWrites.tabName_notMem_warrs_scatterDeadPhase j j i
      (fun β hβ => (tableRank_of_mem_tablesAt (j + 1) β hβ).1) _ 0 (fun _ hβ => hβ))
    (Refine.ScatterDeadPass.ballBudget_carrier hcsr)
    (fun _ _ _ _ _ _ => RamDriverBase.readbackStep hB.one_lt hB.n_lt le_rfl)
    (fun i => tabName_notMem_warrs_driverAt i)
    hmono
    (fun _ hkn hout hsub =>
      Refine.MassWeight.arenaWeight_le_blockWeight G hout hkn hsub)
    hK

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
*derived* from the two facts it actually needs — the cover's block
injectivity `hbinj` and the cover-degree bound `hdeg`.

**Rebase G2/E6.** The Σ interface reads the **arena weight**: the
conclusion is `Kl j (arenaWeight n G M)`, the induction's abstract
measures are instantiated at `MassWeight.arenaWeight n G` /
`MassWeight.blockWeight n G` (ONE fixed root graph through the whole
recursion — E5's constraint), the mass pair comes from
`MassWeight.mass_of_alive_compaction_weight` at the same `Kmass`
coefficient, and the descend clause is consumed as
`MassWeight.arenaWeight_le_blockWeight`. The hypothesis LIST is
byte-identical to B8's — `∀ j m`-shaped side conditions are
form-invariant under the re-read; what changed is the point they are
READ at, and the four phase slots' honest forms are still the
carrier-charged ones (the per-slot gap ledger is compiled in
`Refine.G2CostProbe` §7 — they move only when the block-driven engines
land).

**Rebase E-mem/W3.** `hB` is `RamDriver.WordBoundK` at `Kmass` — the
degree parameter `hdeg` already bounds — and goes down to every phase
unchanged; the induction is uniform in it. The cover phase's two arena
slots, which are the only readings the carrier bound used to be needed
for, are the mass readings of `Refine.ArenaPointer` at the ordering the
loop produced, discharged from `hdeg` itself. The hypothesis list is
otherwise unchanged and the conclusion is untouched. -/
theorem levelAt
    (hcap : cap = rhoMinus 0 q_top) (hmb : mb = ℓ * (2 * cap + 1)) (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBoundK B n Kmass ns cap mb) (hWB : n + W + 1 < B) (hpow : 2 ^ sigL cap mb ℓ < B)
    (hcsr : RamElim.CsrSimple G ns O T)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧
          Refine.ScatterDeadTurn.deadAtomK σs.β n n mb n ns n σs.t ≤ Kb)
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
      LevelImplements B q_top cap mb 0 ℓ W ns j φ G O T M Gm C
        (Kl j (arenaWeight n G M)) :=
  -- every phase takes the value bound at a degree parameter, and the root now
  -- carries it there: `hB` goes down unchanged (rebase E-mem/W3). The cover
  -- phase's two arena slots are the mass readings, off this theorem's own
  -- `hdeg` at the ordering the loop produced.
  RamDriverCluster.levelImplements hB hWB hcsr
    (fun _ _ _ _ _ _ => RamElim.implements)
    (fun _ _ _ _ _ _ _ => RamDriverAugment.implements)
    (fun A₀ ord π => RamDriverOrder.coverTurnImplements B n ns G A₀ O T ord π cap)
    (fun M π _ hordby => Refine.ArenaPointer.ptrWords_of_mass hordby (hdeg M π) hB.arena)
    (fun M π _ hordby => Refine.ArenaPointer.massWords_of_mass hordby (hdeg M π) hB)
    hQ hℓ
    (fun M Gm C hbot hbit => by
      rw [driverAt_bot]
      exact ((RamDriverCompose.baseImplements hB hpow hbot hbit).pre
        (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)).mono (hKbase _))
    (fun j _ M _ _ _d h₁ h₂ h₃ h₄ h₅ =>
      (RamDriverCompose.orderImplements₀ h₁ h₂ h₃ h₄ h₅).mono
        (hKo j (arenaWeight n G M)))
    (fun j _ M _ _ _ _ _d h₁ h₂ h₃ h₄ h₅ h₆ =>
      (RamDriverCompose.coverImplements h₁ h₂ h₃ h₄ h₅ h₆).mono (hKc j (arenaWeight n G M)))
    (fun j hj _ _ _ _ _ _ _ _ _ _ =>
      clusterStepAt hcap hmb hj hB hcsr.csr (hbnd j hj) (hcostI j hj) (hKsc j hj)
        (hKmono (j + 1)) (hKs j hj _))
    (fun j hj _ _ _ _ _ _ _ _ _ _ =>
      clusterFramesAt hmb hj hB hcsr.csr (hbnd j hj) (hcostI j hj) (hKsc j hj)
        (hKmono (j + 1)) (hKs j hj _))
    (fun _ _ => loopFrames)
    (fun j _ M _ _ =>
      (Refine.DeadSweep.sweepImplements (jd := j) hB).mono
        (hKd j (arenaWeight n G M)))
    (fun M π ord Xoff Xmem asg cps mm cnum hordby _ hout hcomp =>
      Refine.MassWeight.mass_of_alive_compaction_weight G hordby hout
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

/-! ### The plug, checked

B8's stale-corollary discipline: `levelCost_of_sigma` is an arithmetic
statement *about* `levelAt`'s `hKl` slot, and an arithmetic statement
compiles whether or not it still fits the slot. So the fit is written
down as a term — `levelAt_of_sigma` is `levelAt` with its level
condition supplied by the solver's shape, and it type-checks only if
the two shapes are still the same one. Re-run at rebase F-c-2, whose
only cost move is `RamDriverCompose.orderPhaseCost`'s constants and so
touches `hKo`, not this. -/

section Plug

variable {n : ℕ} {B q_top cap mb ns W ℓ s Kmass : ℕ} {N : ℕ → ℕ}
  {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
  {Kb : ℕ} {Ki Ksc : ℕ → ℕ} {Ko Kc Kd Ks Kt Kl : ℕ → ℕ → ℕ}

open Classical in
/-- **Every level of the driver, against the solver's own shape.**
`levelAt` with `hKl` produced by `levelCost_of_sigma` — the plug B7
will call, and the check that the Σ interface and the level condition
have not drifted apart. -/
theorem levelAt_of_sigma
    (hcap : cap = rhoMinus 0 q_top) (hmb : mb = ℓ * (2 * cap + 1)) (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBoundK B n Kmass ns cap mb) (hWB : n + W + 1 < B) (hpow : 2 ^ sigL cap mb ℓ < B)
    (hcsr : RamElim.CsrSimple G ns O T)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧
          Refine.ScatterDeadTurn.deadAtomK σs.β n n mb n ns n σs.t ≤ Kb)
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
    (hshift : ∀ j t, Ks j t + 3 ≤ Kt j t)
    (hsolve : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + ((Kc j m + Kd j m) + ((∑ c ∈ Finset.range t, (Kt j (bs c) + 8)) + 6))
        ≤ Kl j m) :
    ∀ j ≤ ℓ, ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      LevelImplements B q_top cap mb 0 ℓ W ns j φ G O T M Gm C
        (Kl j (arenaWeight n G M)) :=
  levelAt hcap hmb hℓ hB hWB hpow hcsr hQ hbnd hcostI hKsc hKmono hKs hKbase hKo hKc hKd
    hbinj hdeg (levelCost_of_sigma hshift hsolve)

end Plug

/-! ### The `hbinj` slot, discharged (rebase F-c-3)

B6 designed `Refine.MassMath.BlockInj` to be *projected* out of the
cover pass's exit relation once the pass carried the clause, and in the
meantime stated every mass lemma against it as a named hypothesis —
which is how it reached this file's `hbinj`, one of the two slots B7's
hypothesis table had no producer for. Wave B3 added the clause
(`RamCover.CoverInv.block_inj`, threaded through `CoverInv.step` on
strict monotonicity of the write pointer and read off by
`CoverInv.out`), and its statement came out identical to `BlockInj`'s
clause for clause, so the projection is one field access —
`Refine.MassMath.blockInj_of_coverOut`.

`blockInj_slot` is that projection *at the slot's type*, written out
rather than inlined: the type below is `levelAt`'s and
`driverRoot_decides_sentence`'s `hbinj` hypothesis verbatim, so
supplying it is a type-check and not an argument. This is B8's
stale-corollary discipline applied to a slot with no arithmetic in it —
a producer compiles whether or not it still fits, and
`driverRoot_decides_sentence_binj` below is where the fit is
*witnessed*. -/

section BlockInjSlot

variable {n : ℕ}

/-- **The cover pass's blocks list each vertex once**, at the exact
shape the driver's `hbinj` slot asks for. Handed the exit relation of
the cover pass at any mask, any ordering and any emitted mass, this is
`RamCover.CoverOut.block_inj`. -/
theorem blockInj_slot (G : SimpleGraph (Fin n)) (cap : ℕ) :
    ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (mm : ℕ),
      RamCover.CoverOut G M π ord cap mm Xoff Xmem asg →
        Refine.MassMath.BlockInj n Xoff Xmem :=
  fun _ _ _ _ _ _ _ h => Refine.MassMath.blockInj_of_coverOut h

end BlockInjSlot

/-! ### The `hdeg` slot, and where its producer has to come from (F-c-3)

`hdeg` is the other of B7's two producerless hypotheses, and it is
producerless for a *structural* reason, not for want of a wave: it asks
for the cover-degree coefficient at **every** permutation of the
carrier, and a cover's degree is a property of the ordering the phase
built. No theorem of the campaign proves it for an arbitrary `π`, and
none can — `CoverDegree.exists_cover_degree`'s conclusion is about the
ordering of a chain's last elimination.

The slot the fact belongs in is `RamDriver.OrderImplements`'s parametric
`P`, anchored by F-c and instantiated by
`RamDriverCompose.OrderP` at `R = R*`. Two things were needed to make
that reach the coefficient, and both are done:

* **the threading** — `RamDriverCluster.levelImplements` destructured
  the phase's `P` witness away one line after it arrived; its `hmass`
  slot now takes `P π ord` beside `RamCover.OrdersBy` (F-c-3). At
  `R = 0`, `P` is `True` and `levelAt` supplies it with `_`, so nothing
  above this file moved;
* **the step** — `wreachDeg_of_orderP` below, which is
  `CoverDegree.wreach_degree_of_data` read at the slot value.

What is left is the phase walk itself
(`RamDriverCompose.OrderImplementsR`, residual itemized there). Until it
lands, `hdeg` stays a hypothesis of `driverRoot_decides_sentence` — but
it is a hypothesis with a named producer waiting on one obligation,
rather than one nothing can discharge. -/

section DegSlot

variable {n : ℕ}

/-- **From the phase's ordering property to the cover-degree
coefficient.** Handed a bound that holds of every `R`-round chain of the
arena, the phase's own slot value delivers it at the ordering the phase
built — which is the shape `RamDriverCluster.levelImplements`'s `hmass`
consumes and `Refine.ArenaBlock.mass_of_alive_compaction` charges the
level's turns against. -/
theorem wreachDeg_of_orderP {cap R Kmass : ℕ} {G : SimpleGraph (Fin n)} {M : ℕ → ℕ}
    (hchain : ∀ (D : ℕ → Lax3Proofs.Augmentation.Orientation n) (π : Equiv.Perm (Fin n))
      (d₀ k : ℕ), CoverDegree.AugChainData (masked G M) D π R d₀ k →
      ∀ v : Fin n, (Lax12.ColoringNumbers.wreach (masked G M) π (2 * cap) v).ncard ≤ Kmass)
    {π : Equiv.Perm (Fin n)} {ord : ℕ → ℕ} (hP : RamDriverCompose.OrderP R G M π ord) :
    ∀ v : Fin n, (Lax12.ColoringNumbers.wreach (masked G M) π (2 * cap) v).ncard ≤ Kmass := by
  obtain ⟨D, d₀, k, hdata⟩ := hP
  exact hchain D π d₀ k hdata

open scoped SimpleGraph in
/-- **The producer, end to end.** On a nowhere dense class, for every
cover radius, round budget and `δ > 0` there is a constant such that
*any* level whose arena embeds in a member of the class and whose
ordering carries the `R*` phase's slot has cover degree
`⌈c · n ^ δ⌉` — the driver's `Kmass`, at the ordering the phase
produced and at no other.

This is `CoverDegree.wreach_degree_of_data` with its bundle read off
`RamDriverCompose.OrderP`; the arithmetic that turns the ceiling into
the driver's cost parameter is P4's. -/
theorem exists_wreachDeg_of_orderP (C : Lax12.GraphClasses.GraphClass)
    (hC : Lax12.NowhereDenseClasses.NowhereDense C) (rc R t : ℕ)
    (ht : 3 * t ≤ R) (hrt : 2 * rc ≤ 2 ^ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (nn : ℕ) (Gn : SimpleGraph (Fin nn)), C nn Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)) (M : ℕ → ℕ), masked G M ⊑ Gn →
        ∀ (π : Equiv.Perm (Fin m)) (ord : ℕ → ℕ), RamDriverCompose.OrderP R G M π ord →
          ∀ v : Fin m,
            (Lax12.ColoringNumbers.wreach (masked G M) π (2 * rc) v).ncard ≤
              ⌈c * (m : ℝ) ^ δ⌉₊ := by
  obtain ⟨c, hc⟩ := CoverDegree.wreach_degree_of_data C hC rc R t ht hrt δ hδ
  refine ⟨c, fun nn Gn hGn m G M hsub π ord hP => ?_⟩
  exact wreachDeg_of_orderP (fun D π' d₀ k hdata => hc nn Gn hGn m (masked G M) hsub D π'
    d₀ k hdata) hP

end DegSlot

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

**Rebase B2 (§5.8), re-read at the weight (G2/E6).** The program, the
precondition and the postcondition are **byte-identical** to what they
were; the cost is `Kl 0 (n + ns)` because a level's budget is a
function of the **weight** of the arena it runs on and the root's mask
kills nothing (`Refine.MassWeight.arenaWeight_root`, which needs the
input word's `CsrSimple` — the clause G1's dedup produces at the C0
boundary). `hKs`/`hKl` are the §5.7/§5.6 shapes read at weights,
`hKmono` is new, and — rebase B8 — the mass bundle `hmass` has become
the two facts it is derived from (`hbinj`, `hdeg`) while the level
gains its dead-row sweep (`hKd`). The conclusion is untouched.

**Rebase E-mem/W3: the word-bound slot.** `hB` is
`RamDriver.WordBoundK B n Kmass ns cap mb`, the value bound with the
cluster arena's pointer ceiling read at `hdeg`'s own degree parameter,
in place of the carrier bound `RamDriver.WordBound`. It is the *only*
hypothesis that moved: the list, the order, the program, the
precondition, the postcondition and the cost are all what they were.
`hdeg` now does double duty — it bounds the cover's degree for the mass
recursion, as before, and it is what makes the arena's pointer a word
(`Refine.ArenaPointer.ptr_le_mass`). The bridge consequence is
`Refine.BridgeCrossing`: this slot has a value bound at every word of
C0's domain, at the layout's own constant, including at the instance
where `Refine.BridgeSeamProbe.no_word_size_for_sparse` kills the carrier
bound for every value bound. -/
theorem driverRoot_decides_sentence
    -- the input word
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hO : ∀ i ≤ n, O i = offset x i) (hT : ∀ i < ns, T i = target x i)
    (hxB : ∀ v ∈ x, v < B) (hcsr : RamElim.CsrSimple G ns O T)
    (hpad0 : ∀ z, ns ≤ z → z < W → T z = 0)
    -- the parameters
    (hrank : Lax3.FirstOrder.rank φ ≤ q_top) (hcap : cap = rhoMinus 0 q_top)
    (hmb : mb = ℓ * (2 * cap + 1)) (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBoundK B n Kmass ns cap mb) (hWB : n + W + 1 < B) (hpow : 2 ^ sigL cap mb ℓ < B)
    -- the mathematics of the campaign
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    -- the value bounds and the costs
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧
          Refine.ScatterDeadTurn.deadAtomK σs.β n n mb n ns n σs.t ≤ Kb)
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
    Spec B (fun σ => DecodeMem n ns W σ ∧ LevelMem B n cap mb σ ∧ DepthMem n cap mb σ ∧
        OrderMem B n ns W σ ∧ TablesSized q_top cap mb φ n σ ∧
        BaseArrs B q_top cap mb ℓ φ σ ∧ σ.inp = x ∧ σ.out = [])
      (driverRoot q_top cap mb 0 ℓ φ)
      (fun _ σ' => σ'.out = [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
      (Kdec + (Kl 0 (n + ns) + Ksent)) :=
  driver_correct hrank hB hxB (by omega) hpad0
    (RamDriverIO.decodeImplements hx hns hO hT hKdec)
    (fun M Gm C hall => by
      have h := levelAt hcap hmb hℓ hB hWB hpow hcsr hQ hbnd hcostI hKsc hKmono hKs
        hKbase hKo hKc hKd hbinj hdeg hKl 0 (Nat.zero_le ℓ) M Gm C
      rwa [Refine.MassWeight.arenaWeight_root hcsr hall] at h)
    (fun _ _ _ => RamDriverIO.sentenceImplements hrank hcsr.csr hatoms hKsent)

open Classical in
/-- **The same, with `hbinj` supplied** (rebase F-c-3). The root
theorem minus the block-injectivity slot, which
`RamDriverRoot.blockInj_slot` fills out of `RamCover.CoverOut`'s own
field. Nothing else moves: the program, the precondition, the
postcondition and the cost are `driverRoot_decides_sentence`'s, and the
remaining hypotheses are the same list in the same order.

This is the plug check for that slot in B8's sense. A producer of the
right *reading* type-checks on its own; what says it is the reading the
driver still asks for is this application, and it would break the
moment either side drifted. -/
theorem driverRoot_decides_sentence_binj
    -- the input word
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hO : ∀ i ≤ n, O i = offset x i) (hT : ∀ i < ns, T i = target x i)
    (hxB : ∀ v ∈ x, v < B) (hcsr : RamElim.CsrSimple G ns O T)
    (hpad0 : ∀ z, ns ≤ z → z < W → T z = 0)
    -- the parameters
    (hrank : Lax3.FirstOrder.rank φ ≤ q_top) (hcap : cap = rhoMinus 0 q_top)
    (hmb : mb = ℓ * (2 * cap + 1)) (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBoundK B n Kmass ns cap mb) (hWB : n + W + 1 < B) (hpow : 2 ^ sigL cap mb ℓ < B)
    -- the mathematics of the campaign
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    -- the value bounds and the costs
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧
          Refine.ScatterDeadTurn.deadAtomK σs.β n n mb n ns n σs.t ≤ Kb)
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
    Spec B (fun σ => DecodeMem n ns W σ ∧ LevelMem B n cap mb σ ∧ DepthMem n cap mb σ ∧
        OrderMem B n ns W σ ∧ TablesSized q_top cap mb φ n σ ∧
        BaseArrs B q_top cap mb ℓ φ σ ∧ σ.inp = x ∧ σ.out = [])
      (driverRoot q_top cap mb 0 ℓ φ)
      (fun _ σ' => σ'.out = [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
      (Kdec + (Kl 0 (n + ns) + Ksent)) :=
  driverRoot_decides_sentence hx hns hO hT hxB hcsr hpad0 hrank hcap hmb hℓ hB hWB hpow hQ
    hbnd hcostI hKsc hKmono hKs hKbase hKo hKc hKd (blockInj_slot G cap) hdeg hKl
    hKdec hatoms hKsent

end Main

end Lax3Proofs.RamDriverRoot
