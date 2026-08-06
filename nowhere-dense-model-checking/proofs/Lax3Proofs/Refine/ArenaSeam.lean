import Lax3Proofs.Refine.MemThreadGate
import Lax3Proofs.Refine.ScatterBlock

/-!
# The arena seam — the engines' member list, discharged from the driver

Flag F-2 of `plans/nowhere-dense-model-checking/e-mem-design.md`, closed
in the direction that matters. The design's §4 consumer table records
that the block engines carry an `hml : MemList …` hypothesis which
**nothing in the package constructs** — the contract existed, the supply
did not. This file is the supply.

### What closes, and against what

`RamDriver.LevelPre`'s sixteenth clause (rebase E-mem) says the depth
carries a member array `memName j` at physical length `n`, a count
`mnumName j`, and `MemEnum` — the driver's spelling of `MemList` at the
depth's own mask. `MemThreadGate.memList_of_memEnum` is the twin, so the
clause reads as the engines' contract. What was left was the *layout*:
the engines pinned `σ.arrs "mem" = arrOf mm Mem`, a physically
`mm`-cell array, while the driver hands down `n` cells with a live
prefix. That seam is now re-stated (`ScatterBlock.ArenaA` §1), and the
two halves meet here.

### The entry convention, and why it is not `copyCom`

`memEntry j` is the design's read convention verbatim: the count into
`"mm"`, then the LIVE PREFIX into `"mem"` by
`copyUpto (memName j) "mem" (.var "mm")` — the `CoverBlock.memCopy_spec`
leaf shape, `memCopyK mm = 12·mm + 6`. It is deliberately **not**
`RamDriver.copyCom`, the fixed-`n` copy that serves the masks: that is a
carrier walk, the class G2 exists to kill. The count is the runtime
bound, so the copy moves exactly the member cells, and the junk above
the prefix is never read, written, or claimed about — which is why the
copy can leave the destination's tail holding whatever it held.

The contract survives the copy because `MemList` speaks only of `k < mm`
(`MemList.congr_prefix`), and the copy's own postcondition is agreement
on exactly that prefix. Nothing here needs a tail conjunct, and adding
one would re-introduce the carrier walk.
-/

namespace Lax3Proofs.Refine.ArenaSeam

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3.ColoredGraphs Lax3.ScatterSentences
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs Lax3Proofs.RamScatter
open Lax3Proofs.RamDriver (memName mnumName MemEnum LevelPre copyUpto fillUpto memName_ne_mem)
open Lax3Proofs.RamDriverCluster (markSet mem_markSet)
open Lax3Proofs.Refine.ScatterBlock (ArenaA MemList MemOf BallBudget scatBlockCom scatBlockK
  scatBlock_specW)
open Lax3Proofs.Refine.CoverBlock (memCopyK)

/-! ### §1 The clause, opened at the engines' contract

One destructuring through the landed gate. This is the whole of the
driver's half: the depth's list, at the physical length the depth
allocates it at, with the count and the live-prefix word bound. -/

/-- **The depth's member list, as the engines state it.** `LevelPre`'s
sixteenth clause read through `MemThreadGate.memList_of_memEnum`, plus
the count bound every walk's range obligation is discharged by. -/
theorem memList_of_levelPre {B n cap mb ns W j : ℕ} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {σ : Env} (h : LevelPre B n cap mb ns W O T j M Gm C σ) :
    ∃ (Mem : ℕ → ℕ) (mm : ℕ), σ.arrs (memName j) = arrOf n Mem ∧
      σ.vars (mnumName j) = mm ∧ MemList n mm Mem (markSet n M) ∧
      (∀ z, z < mm → Mem z < B) ∧ mm ≤ n := by
  obtain ⟨-, -, Mem, mm, hA, hV, hL, hB⟩ := MemThreadGate.levelPreMLive_of_levelPre h
  exact ⟨Mem, mm, hA, hV, hL, hB, hL.card_le⟩

/-! ### §2 The entry program, and its frame -/

/-- **The engine entry, member half.** The count into `"mm"`, the live
prefix into `"mem"`. The bound is the runtime count, so the copy is
charged at the members and not at the carrier. -/
def memEntry (j : ℕ) : Com :=
  .seq (.assign "mm" (.var (mnumName j)))
    (copyUpto (memName j) "mem" (.var "mm"))

theorem notMem_memEntry_wvars (j : ℕ) {y : String} (h₁ : y ≠ "mm") (h₂ : y ≠ "i") :
    y ∉ (memEntry j).wvars := by
  simp [memEntry, copyUpto, fillUpto, Fill.put, Com.wvars, h₁, h₂]

theorem notMem_memEntry_warrs (j : ℕ) {a : String} (h : a ≠ "mem") :
    a ∉ (memEntry j).warrs := by
  simp [memEntry, copyUpto, fillUpto, Fill.put, Com.warrs, h]

/-! ### §3 The member conjuncts of the arena, discharged

The copy runs, and what comes out is the engine's hypothesis. The
`MemList` is the driver's, transported across the copy by
`MemList.congr_prefix` — the copy agrees with the source exactly on the
live prefix, and the live prefix is exactly what the contract reads. -/

/-- **The engine's `hml`, from the driver's state.** Given the depth's
list, `memEntry j` leaves `"mm"` holding the count and `"mem"` holding
an `n`-cell array whose live prefix is the list — i.e. it leaves the
`MemList` hypothesis the block engines take. The charge is the member
copy's, `memCopyK mm + 2`, in which the carrier does not occur. -/
theorem memEntry_run {B n j mm : ℕ} {Mem M : ℕ → ℕ} {σ : Env}
    (hB : 0 < B) (hnB : n < B)
    (hmem : σ.arrs (memName j) = arrOf n Mem)
    (hmm : σ.vars (mnumName j) = mm)
    (hml : MemList n mm Mem (markSet n M))
    (hMemB : ∀ z, z < mm → Mem z < B)
    (hdst : ∃ g, σ.arrs "mem" = arrOf n g) :
    ∃ (σ' : Env) (K : ℕ) (Mem' : ℕ → ℕ), Run B (memEntry j) σ σ' K ∧
      K ≤ memCopyK mm + 2 ∧ σ'.vars "mm" = mm ∧ σ'.arrs "mem" = arrOf n Mem' ∧
      MemList n mm Mem' (markSet n M) := by
  have hmn : mm ≤ n := hml.card_le
  have hmmB : mm < B := by omega
  -- the count
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = σ.setVar "mm" mm := ⟨_, rfl⟩
  have runc : Run B (.assign "mm" (.var (mnumName j))) σ τ 2 := by
    rw [hτ, ← hmm]
    exact (Run.assign (v := σ.vars (mnumName j))
      (evalB_var (by rw [hmm]; omega))).mono (by simp [Expr.size])
  -- the live-prefix copy, at the member charge
  have hQfr : ∀ σ₁ σ₂ : Env, (σ₁.vars "mm" = mm ∧ σ₁.arrs (memName j) = arrOf n Mem) →
      (∀ y, y ≠ "i" → σ₂.vars y = σ₁.vars y) →
      (∀ b, b ≠ "mem" → σ₂.arrs b = σ₁.arrs b) →
      (σ₂.vars "mm" = mm ∧ σ₂.arrs (memName j) = arrOf n Mem) := by
    rintro σ₁ σ₂ ⟨h₁, h₂⟩ hv ha
    exact ⟨by rw [hv "mm" (by decide)]; exact h₁,
      by rw [ha (memName j) (memName_ne_mem j)]; exact h₂⟩
  have hcopy := RamDriverCompose.copyPrefix_spec (B := B) mm n n (memName j) "mem"
    (.var "mm") Mem (fun σ₁ => σ₁.vars "mm" = mm ∧ σ₁.arrs (memName j) = arrOf n Mem)
    hB hmmB hmn hmn hQfr
    (fun σ₁ hQ => by rw [← hQ.1]; exact evalB_var (by rw [hQ.1]; omega))
    (fun σ₁ hQ => hQ.2) hMemB
  obtain ⟨g₀, hg₀⟩ := hdst
  obtain ⟨σ', hrun, ⟨Mem', harr, hcell⟩, -, hQ'⟩ :=
    hcopy.run (σ := τ) ⟨⟨g₀, by rw [hτ]; simpa using hg₀⟩,
      by rw [hτ]; exact ⟨by simp, by simp [hmem]⟩⟩
  refine ⟨σ', 2 + ((Expr.var "mm").size + 11) * mm + (Expr.var "mm").size + 5,
    Mem', runc.seq hrun, ?_, hQ'.1, harr, hml.congr_prefix hcell⟩
  simp only [memCopyK, Expr.size]
  omega

/-! ### §4 The whole arena, from a level

The other entry copies are the ones `ArenaA` already assumed and this
wave does not touch — the mask into `"alv"`, a clean `"dist"`, the two
queue arrays. What is new is that the member conjuncts are no longer
assumed: they come out of `LevelPre`. -/

/-- **The re-stated arena, discharged driver-side.** From a level state
and the engine's own scratch, the member copy leaves an `ArenaA` at the
threaded layout — physical length `n`, live prefix `mm` — together with
the `MemList` every block walk of `ScatterBlock` takes as a hypothesis.

The target array reading is the level's own `W`: `LevelPre` carries
`"tgt"` at the allocation width (rebase F-c-4), and `ArenaA` is stated
at an arbitrary target length for exactly this reason. -/
theorem arenaA_of_levelPre {B n cap mb ns W j r : ℕ} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {σ : Env} (hB : 0 < B) (hnB : n < B)
    (hlev : LevelPre B n cap mb ns W O T j M Gm C σ)
    (halv : σ.arrs "alv" = arrOf n M)
    (hdist : σ.arrs "dist" = arrOf n (fun _ => r + 1))
    (hq : ∃ g, σ.arrs "q" = arrOf n g) (hqd : ∃ g, σ.arrs "qd" = arrOf n g)
    (hdst : ∃ g, σ.arrs "mem" = arrOf n g) :
    ∃ (σ' : Env) (K mm : ℕ) (Mem : ℕ → ℕ), Run B (memEntry j) σ σ' K ∧
      K ≤ memCopyK mm + 2 ∧ mm ≤ n ∧
      ArenaA n W mm r O T M Mem σ' ∧ MemList n mm Mem (markSet n M) := by
  obtain ⟨Mem, mm, hmem, hmm, hml, hMemB, hmn⟩ := memList_of_levelPre hlev
  obtain ⟨hn, hoff, htgt, -⟩ := id hlev
  obtain ⟨σ', K, Mem', hrun, hK, hmmv, hmemv, hml'⟩ :=
    memEntry_run hB hnB hmem hmm hml hMemB hdst
  have hfa : ∀ a, a ≠ "mem" → σ'.arrs a = σ.arrs a :=
    fun a ha => hrun.frame_arr a (notMem_memEntry_warrs j ha)
  obtain ⟨gq, hgq⟩ := hq
  obtain ⟨gqd, hgqd⟩ := hqd
  refine ⟨σ', K, mm, Mem', hrun, hK, hmn, ⟨?_, hmmv, ?_, ?_, ?_, hmemv, ?_, ?_, ?_⟩, hml'⟩
  · rw [hrun.frame_var "n" (notMem_memEntry_wvars j (by decide) (by decide))]; exact hn
  · rw [hfa "off" (by decide)]; exact hoff
  · rw [hfa "tgt" (by decide)]; exact htgt
  · rw [hfa "alv" (by decide)]; exact halv
  · rw [hfa "dist" (by decide)]; exact hdist
  · exact ⟨gq, by rw [hfa "q" (by decide)]; exact hgq⟩
  · exact ⟨gqd, by rw [hfa "qd" (by decide)]; exact hgqd⟩

/-! ### §5 The seam closed, end to end

The engine that the member list was built for, run from a level state.
Nothing about the scatter pass changes — `scatBlock_specW` is the landed
export, applied — and the point is that its two member hypotheses are no
longer assumptions of the caller. -/

/-- **A block scatter pass, driven from the driver's own state.** The
member copy followed by the landed active-set pass decides the scatter
sentence about the depth's arena, at the member charge plus the copy's.
Neither `n` nor `ns` occurs in the charge. -/
theorem scatBlock_of_levelPre {B n cap mb ns W j r t nsg : ℕ} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {G : SimpleGraph (Fin n)} {σ : Env} {bw nb : ℕ}
    (hB : 0 < B) (hnB : n < B) (hnsB : nsg < B) (hnt : nsg ≤ W)
    (hrB : r + 1 < B) (htB : t < B)
    (hcsr : CsrGraph G nsg O T)
    (hbud : BallBudget n r G M O bw nb)
    (hlev : LevelPre B n cap mb ns W O T j M Gm C σ)
    (halv : σ.arrs "alv" = arrOf n M)
    (hdist : σ.arrs "dist" = arrOf n (fun _ => r + 1))
    (hq : ∃ g, σ.arrs "q" = arrOf n g) (hqd : ∃ g, σ.arrs "qd" = arrOf n g)
    (hdst : ∃ g, σ.arrs "mem" = arrOf n g) (hexc : ∃ g, σ.arrs "exc" = arrOf n g) :
    ∃ (σ' : Env) (K mm : ℕ), Run B (.seq (memEntry j) (scatBlockCom r t)) σ σ' K ∧
      K ≤ memCopyK mm + 2 + scatBlockK mm bw nb t ∧ mm ≤ n ∧
      (σ'.vars "flag" = 1 ↔ t ≤ (greedySet (masked G M) r (markSet n M)).ncard) ∧
      σ'.vars "flag" ≤ 1 := by
  obtain ⟨-, -, -, -, -, -, hMB, -⟩ := id hlev
  obtain ⟨τ, K₁, mm, Mem, hrun₁, hK₁, hmn, hA, hml⟩ :=
    arenaA_of_levelPre hB hnB hlev halv hdist hq hqd hdst
  obtain ⟨g, hg⟩ := hexc
  have hexcτ : τ.arrs "exc" = arrOf n g := by
    rw [hrun₁.frame_arr "exc" (notMem_memEntry_warrs j (by decide))]; exact hg
  obtain ⟨σ', hrun₂, hflag, hflag1⟩ :=
    (scatBlock_specW (G := G) (M := M) (O := O) (T := T) (Mem := Mem) (X := markSet n M)
      (ns := nsg) (nt := W) (mm := mm) hcsr hnB hnsB hnt hrB htB hMB hml hbud).run
      (σ := τ) ⟨hA, g, hexcτ⟩
  exact ⟨σ', K₁ + scatBlockK mm bw nb t, mm, hrun₁.seq hrun₂, by omega, hmn, hflag, hflag1⟩

/-! ### §6 The seam at concrete shapes

A four-vertex carrier whose mask leaves two vertices alive. The member
array is four cells long — the carrier's length — and its live prefix is
two: the third and fourth cells hold `99`, which is not a vertex, is not
claimed about, and is never read. This is the layout the driver hands
down, and the `example` is the check that the re-stated `Prop`s accept
it while the old length would not. -/

/-- Two vertices alive out of four. -/
def demoMask : ℕ → ℕ := fun z => if z = 1 then 1 else if z = 3 then 1 else 0

/-- Their list: two live cells, then junk. -/
def demoMem : ℕ → ℕ := fun k => if k = 0 then 1 else if k = 1 then 3 else 99

/-- The driver's clause at the demo shape, in the driver's spelling. -/
theorem demo_memEnum : MemEnum 4 2 demoMem demoMask := by
  refine ⟨fun k hk => ?_, fun i k hik hk => ?_, fun k hk => ?_, fun a ha hMa => ?_⟩
  · interval_cases k <;> simp [demoMem]
  · interval_cases k
    · omega
    · interval_cases i
      simp [demoMem]
  · interval_cases k <;> simp [demoMem, demoMask]
  · interval_cases a
    · exact absurd (by simp [demoMask] : demoMask 0 = 0) hMa
    · exact ⟨0, by omega, by simp [demoMem]⟩
    · exact absurd (by simp [demoMask] : demoMask 2 = 0) hMa
    · exact ⟨1, by omega, by simp [demoMem]⟩

/-- And the engines' contract at the same shape, through the twin. **The
junk tail is not a member and is not claimed about**: `demoMem 2 = 99`
is not even a vertex of the four-vertex carrier. -/
example : MemList 4 2 demoMem (markSet 4 demoMask) :=
  MemThreadGate.memList_of_memEnum demo_memEnum

/-- The demo state: every array the arena reads, with the member array at
the CARRIER's length and a live prefix of two. -/
def demoEnv : Env where
  vars := fun x => if x = "n" then 4 else if x = "mm" then 2 else 0
  arrs := fun a =>
    if a = "off" then arrOf 5 (fun _ => 0)
    else if a = "tgt" then arrOf 7 (fun _ => 0)
    else if a = "alv" then arrOf 4 demoMask
    else if a = "mem" then arrOf 4 demoMem
    else if a = "dist" then arrOf 4 (fun _ => 1)
    else arrOf 4 (fun _ => 0)
  inp := []
  out := []

/-- **The re-stated arena accepts the threaded layout.** Physical length
four, live prefix two, `nt = 7` (a target array wider than the block
structure, as `LevelPre`'s `W` is). -/
example : ArenaA 4 7 2 0 (fun _ => 0) (fun _ => 0) demoMask demoMem demoEnv :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨fun _ => 0, rfl⟩, ⟨fun _ => 0, rfl⟩⟩

/-- **And the old length-clause would refuse it** — the negative control
that the seam actually moved. The member array of the threaded layout is
four cells, not two; before this wave the arena demanded `arrOf mm Mem`,
which no depth of the driver ever hands an engine. -/
example : demoEnv.arrs "mem" ≠ arrOf 2 demoMem := by
  intro h
  have := congrArg List.length h
  simp [demoEnv] at this

#print axioms memList_of_levelPre
#print axioms memEntry_run
#print axioms arenaA_of_levelPre
#print axioms scatBlock_of_levelPre
#print axioms demo_memEnum

end Lax3Proofs.Refine.ArenaSeam
