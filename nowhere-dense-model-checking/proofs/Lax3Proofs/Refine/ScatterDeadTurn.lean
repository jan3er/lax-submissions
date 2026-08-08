import Lax3Proofs.RamDriverWrites

/-!
# The dead-aware atom phase, composed — wave R1.8-T3-flip (c1d)

The nine passes of `RamDriver.scatDeadCom` run in sequence, folded over
one formula's scatter atoms and then over a depth's table. This is the
last machine step of the R1.8 flip: everything below it is landed
capital, and what is added here is the composition — the frame chain
that carries each pass's product across the passes that follow it, and
the one semantic step at the end.

## Where the file sits, and why

`Refine.ScatterBlock`'s program text is *below* the driver since wave
(c1), so `RamDriver.scatDeadCom` can be written beside the driver's own
passes; but `Refine.ScatterDeadPass` — where the passes' walks are —
imports `RamDriverCluster`, so the walk of the composite cannot live in
`RamDriverFrames` beside the landed `RamScatter.scatterCom` fold. It
lives here, above `RamDriverWrites`, which is where the composite's
write sets already are.

## The order, and what it buys

`RamDriver.scatDeadCom`'s docstring states the order and why: the three
dead terms are computed *before* the engine, so nothing about the
depth's own arrays has to cross the engine's writes — after it only the
four scalars `"cnt"`, `"kc"`, `"bb"` and `"oc"` are read. §1 below is
the frame reading of that claim, pass by pass, and §3 is the chain
itself.

## What the composition is worth

`Refine.ScatterDeadPass.atomTerms_iff_scatVal_of_clusterData`: the
engine's counter, the kill bits and the probe's bit times the outside
count decide the atom, and **no term reads a table row outside
`alive ∪ kills`**. The three threads that theorem needs are all at hand
here — `hXalive` from `RamDriverCluster.ScatterStep`'s own antecedent,
`RamDriverCluster.KillListAt` from the precondition, and the ball budget
from the second antecedent — so nothing is pushed past the existentials
of `RamDriverCluster.clusterStepImplements`.
-/

namespace Lax3Proofs.Refine.ScatterDeadTurn

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3Proofs.FormulaTables
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs Lax3Proofs.RamScatter
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster (TurnPre ClusterData ScatVal KillListAt markSet
  masked_alv_eq)
open Lax3Proofs.RamDriverFrames (ScatPre scratchArrs BbExt)
open Lax3Proofs.Refine.ScatterBlock (ArenaA MemList BallBudget scatBlockCom scatBlockK)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {n : ℕ}

section Names

variable {B q_top cap mb ns Ws ℓ j : ℕ} {φ : Lax3.FirstOrder.FO 0}
  {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
  {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ} {X W : Set (Fin n)} {w : Fin mb → Fin n}
  {Alv' Gam' : ℕ → ℕ} {C' : ℕ → ℕ → ℕ}

end Names

/-! ### §1 The engine's frame, at the names the driver holds

`Refine.ScatterDeadPass.notMem_wvars_scatBlockCom` says the three dead
registers survive the engine; the composition also needs the *driver's*
scalars to, and the phase's own precondition pins six of them. The
engine's scalar set is a closed list of nineteen literals — the radius
and the threshold occur only inside expressions, which `Com.wvars` does
not look at — so every question about it is one `decide`. -/

/-- The engine's scalar set, off `Lax3Proofs.RamDriverWrites` — where
the recursion's own frame already needed it. -/
theorem notMem_wvars_scatBlockCom_of {r t : ℕ} {y : String}
    (h : y ∉ ["cnt", "mj", "mv", "sj", "src", "tail", "head", "sc", "v",
      "dv", "dn", "j", "jend", "w", "ri", "u", "du", "mw", "flag"]) :
    y ∉ (scatBlockCom r t).wvars :=
  RamDriverWrites.notMem_wvars_scatBlockCom_of h

/-- **And the engine writes nothing to the tape**, which is what the
phase's `out` clause needs of it. -/
theorem noWrite_scatBlockCom (r t : ℕ) : (scatBlockCom r t).NoWrite := by
  simp [scatBlockCom, ScatterBlock.clearMem, ScatterBlock.clearSlot,
    ScatterBlock.scatBlockLoop, ScatterBlock.scatBlockStep, ScatterBlock.scatBlockBody,
    ScatterBlock.pickBlock, ScatterBlock.markBall, ScatterBlock.markSlot,
    BfsBlock.bfsBlockCom, BfsBlock.unwind, BfsBlock.unwindSlot, seedSrc,
    bfsDrain, expandRow, scanSlot, Csr.scan, Com.NoWrite]

/-! ### §1b The evaluator's scratch is none of the driver's names

`RamDriverBot.Ext "bb"` names begin `bb`; the driver's four `b`-initial
families are `bal`, `blt`, `bat` and `bh`, and none continues with a
second `b`. The three below are the ones the phase's frame chain asks
for that `RamDriverCompose` does not already have. -/

/-- The two-character twin of `RamDriverBot.not_ext_b_of_cons`, at the
predicate the composite's write set is stated in. -/
theorem not_ext_bb_of_cons {y : String} {c₁ c₂ : Char} {t : List Char}
    (h : y.toList = c₁ :: c₂ :: t) (hc : ¬ (c₁ = 'b' ∧ c₂ = 'b')) :
    ¬ RamDriverBot.Ext "bb" y := RamDriverFrames.not_bbExt_of_cons h hc

/-- A one-character name is shorter than the prefix. -/
theorem not_ext_bb_short {y : String} (h : y.toList.length < 2) :
    ¬ RamDriverBot.Ext "bb" y := fun hp => by
  have hl := List.IsPrefix.length_le hp
  rw [show "bb".toList.length = 2 from rfl] at hl
  omega

theorem not_ext_bb_kkName (a : ℕ) : ¬ RamDriverBot.Ext "bb" (kkName a) :=
  not_ext_bb_of_cons (by rw [kkName, String.toList_append]; rfl) (by decide)

theorem not_ext_bb_klName (a : ℕ) : ¬ RamDriverBot.Ext "bb" (klName a) :=
  not_ext_bb_of_cons (by rw [klName, String.toList_append]; rfl) (by decide)

theorem not_ext_bb_curName (a : ℕ) : ¬ RamDriverBot.Ext "bb" (curName a) :=
  not_ext_bb_of_cons (by rw [curName, String.toList_append]; rfl) (by decide)

theorem not_ext_bb_ctrName (a : ℕ) : ¬ RamDriverBot.Ext "bb" (ctrName a) :=
  not_ext_bb_of_cons (by rw [ctrName, String.toList_append]; rfl) (by decide)

theorem not_ext_bb_xpName (a : ℕ) : ¬ RamDriverBot.Ext "bb" (xpName a) :=
  not_ext_bb_of_cons (by rw [xpName, String.toList_append]; rfl) (by decide)

theorem not_ext_bb_mnumName (a : ℕ) : ¬ RamDriverBot.Ext "bb" (mnumName a) :=
  not_ext_bb_of_cons (by rw [mnumName, String.toList_append]; rfl) (by decide)

theorem not_ext_bb_memName (a : ℕ) : ¬ RamDriverBot.Ext "bb" (memName a) :=
  not_ext_bb_of_cons (by rw [memName, String.toList_append]; rfl) (by decide)

theorem not_ext_bb_alvName (a : ℕ) : ¬ RamDriverBot.Ext "bb" (alvName a) := fun h =>
  RamDriverBot.not_ext_b_alvName a (RamDriverCompose.ext_b_of_ext_bb h)

theorem not_ext_bb_tabName (a b : ℕ) : ¬ RamDriverBot.Ext "bb" (tabName a b) := fun h =>
  RamDriverBot.not_ext_b_tabName a b (RamDriverCompose.ext_b_of_ext_bb h)

theorem not_ext_bb_flgName (a b c : ℕ) : ¬ RamDriverBot.Ext "bb" (flgName a b c) :=
  not_ext_bb_of_cons
    (by rw [flgName, String.toList_append, String.toList_append, String.toList_append,
      String.toList_append, String.toList_append]; rfl) (by decide)

/-! ### §2 The scalars of the whole atom program

Six of the driver's names have to cross all nine passes: the carrier,
the slot count, the live width, the connector and the cursor families,
and the depth's kill count. Each is settled pass by pass off the nine
`wvars` lemmas of `Refine.ScatterDeadPass` §5d. -/

open Classical in
/-- **What one dead-aware atom assigns**, off `RamDriverWrites`. -/
theorem wvars_scatDeadCom {L : ℕ} (j ti : ℕ) (β : DistFO L 1) (r t : ℕ) (hloc : IsLocal β)
    {y : String} (hy : y ∈ (scatDeadCom j ti β r t).wvars) :
    y ∈ ["kc", "ke", "of", "oz", "oi", "oc", "mm", "ak", "av", "i", "os", "flag"] ∨
      y ∈ ["cnt", "mj", "mv", "sj", "src", "tail", "head", "sc", "v",
        "dv", "dn", "j", "jend", "w", "ri", "u", "du", "mw", "flag"] ∨
      RamDriverBot.Ext "bb" y ∨ ∃ q, y = envName q :=
  RamDriverWrites.wvars_scatDeadCom j ti β r t hloc hy

/-- The driver's own prefixed names cross the whole atom program. -/
theorem notMem_wvars_scatDeadCom_append {L : ℕ} {j ti : ℕ} {β : DistFO L 1} {r t : ℕ}
    (hloc : IsLocal β) {p s : String}
    (h₁ : ∀ q ∈ ["kc", "ke", "of", "oz", "oi", "oc", "mm", "ak", "av", "i", "os", "flag"],
      q.toList.take p.toList.length ≠ p.toList)
    (h₂ : ∀ q ∈ ["cnt", "mj", "mv", "sj", "src", "tail", "head", "sc", "v",
      "dv", "dn", "j", "jend", "w", "ri", "u", "du", "mw", "flag"],
      q.toList.take p.toList.length ≠ p.toList)
    (h₃ : ¬ RamDriverBot.Ext "bb" (p ++ s)) (h₄ : ∀ q, p ++ s ≠ envName q) :
    p ++ s ∉ (scatDeadCom j ti β r t).wvars := by
  intro hy
  rcases wvars_scatDeadCom j ti β r t hloc hy with h | h | h | ⟨q, hq⟩
  · exact RamDriverIO.notMem_of_append h₁ h
  · exact RamDriverIO.notMem_of_append h₂ h
  · exact h₃ h
  · exact h₄ q hq

/-- And so do the three fixed ones the level pins. -/
theorem notMem_wvars_scatDeadCom_lit {L : ℕ} {j ti : ℕ} {β : DistFO L 1} {r t : ℕ}
    (hloc : IsLocal β) {y : String}
    (h₁ : y ∉ ["kc", "ke", "of", "oz", "oi", "oc", "mm", "ak", "av", "i", "os", "flag"])
    (h₂ : y ∉ ["cnt", "mj", "mv", "sj", "src", "tail", "head", "sc", "v",
      "dv", "dn", "j", "jend", "w", "ri", "u", "du", "mw", "flag"])
    (h₃ : ¬ RamDriverBot.Ext "bb" y) (h₄ : ∀ q, y ≠ envName q) :
    y ∉ (scatDeadCom j ti β r t).wvars := by
  intro hy
  rcases wvars_scatDeadCom j ti β r t hloc hy with h | h | h | ⟨q, hq⟩
  · exact h₁ h
  · exact h₂ h
  · exact h₃ h
  · exact h₄ q hq

/-- **The atom program leaves the tape alone.** Nine `NoWrite`s. -/
theorem noWrite_scatDeadCom {L : ℕ} (j ti : ℕ) (β : DistFO L 1) (r t : ℕ) :
    (scatDeadCom j ti β r t).NoWrite := by
  refine ⟨RamDriverWrites.noWrite_killSumCom j ti,
    RamDriverWrites.noWrite_outProbeCom j, ?_,
    RamDriverWrites.noWrite_outCntCom j, RamDriverWrites.noWrite_atomMemCom j ti,
    (by rw [RamDriverIO.copyCom_eq]; exact RamDriverIO.noWrite_fillCom _ _),
    RamDriverIO.noWrite_fillCom _ _, noWrite_scatBlockCom r t,
    RamDriverWrites.noWrite_atomFlagCom t⟩
  exact ⟨⟨trivial, RamDriverBot.noWrite_botCom β "bb"⟩, trivial⟩

/-! ### §3 What the phase carries

`RamDriverFrames.ScatPre` is the landed scatter phase's own state; the
dead-aware phase carries two things beside it, and both are already in
`RamDriverCluster.ScatterStep`'s precondition or derivable from a state
that satisfies it. `RamDriverCluster.KillListAt` is what the kill walk
reads, and it survives the phase because the phase writes no array of a
depth and no scalar of one. `RamDriver.BaseArrs` is what the outside
class's `botCom` fragment reads, and it survives every run. -/

variable {B q_top cap mb ns Ws ℓ j : ℕ} {φ : Lax3.FirstOrder.FO 0}
  {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
  {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ} {X W : Set (Fin n)} {w : Fin mb → Fin n}
  {Alv' Gam' : ℕ → ℕ} {C' : ℕ → ℕ → ℕ}

/-- **The dead-aware phase's precondition**, named once: the landed
scatter phase's state, the turn's kill list, and the generated
evaluator's arrays. -/
def DeadPre (B q_top cap mb ns Ws ℓ j : ℕ) (φ : Lax3.FirstOrder.FO 0) {n : ℕ}
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (ord Xoff Xmem asg : ℕ → ℕ) (m : ℕ) (X W : Set (Fin n)) (w : Fin mb → Fin n)
    (Alv' Gam' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ) (σ : Env) : Prop :=
  ScatPre B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m X W w Alv' Gam' C' σ ∧
    KillListAt mb j M X W σ ∧ BaseArrs B q_top cap mb ℓ φ σ

/-- **And it survives any call the phase makes.** The landed half is
`RamDriverFrames.ScatPre.run`; the kill list needs the depth's own array
and count left alone, and the evaluator's arrays are lengths. -/
theorem DeadPre.run {c : Com} {σ σ' : Env} {K : ℕ}
    (h : DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ)
    (hrun : Run B c σ σ' K) (hA : ∀ a ∈ c.warrs, a ∈ scratchArrs ∨ BbExt a)
    (hkl : klName j ∉ c.warrs)
    (hV : ∀ y ∈ ["n", "m", "lw"], y ∉ c.wvars)
    (hVctr : ∀ a : ℕ, ctrName a ∉ c.wvars) (hVxp : xpName j ∉ c.wvars)
    (hVmm : ∀ a : ℕ, mnumName a ∉ c.wvars) (hVkk : kkName j ∉ c.wvars) :
    DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ' := by
  obtain ⟨hpre, ⟨kl, kq, hklA, hkkV, hkqmb, hkllt, hklinj, hklsnd, hklcmp⟩, hbarr⟩ := h
  exact ⟨hpre.run hrun hA hV hVctr hVxp hVmm,
    ⟨kl, kq, by rw [hrun.frame_arr _ hkl]; exact hklA,
      by rw [hrun.frame_var _ hVkk]; exact hkkV, hkqmb, hkllt, hklinj, hklsnd, hklcmp⟩,
    hbarr.run hrun⟩

/-- The six scalars and the one array `DeadPre` pins, against the atom
program's own write sets. -/
theorem DeadPre.run_scatDead {L ti : ℕ} {β : DistFO L 1} {r t : ℕ} {σ σ' : Env} {K : ℕ}
    (h : DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ)
    (hloc : IsLocal β) (hrun : Run B (scatDeadCom j ti β r t) σ σ' K) :
    DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ' := by
  refine h.run hrun (fun a ha => ?_) (fun ha => ?_) (fun y hy => ?_) (fun a => ?_) ?_
    (fun a => ?_) ?_
  · rcases RamDriverWrites.warrs_scatDeadCom j ti β r t hloc ha with hm | hm
    · refine Or.inl ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [scratchArrs]
    · exact Or.inr hm
  · rcases RamDriverWrites.warrs_scatDeadCom j ti β r t hloc ha with hm | hm
    · revert hm; simp [klName, String.ext_iff]
    · exact not_ext_bb_klName j hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact notMem_wvars_scatDeadCom_lit hloc (by decide) (by decide)
        (not_ext_bb_short (by decide)) (fun q => by simp [envName, String.ext_iff])
    · exact notMem_wvars_scatDeadCom_lit hloc (by decide) (by decide)
        (not_ext_bb_short (by decide)) (fun q => by simp [envName, String.ext_iff])
    · exact notMem_wvars_scatDeadCom_lit hloc (by decide) (by decide)
        (not_ext_bb_of_cons rfl (by decide)) (fun q => by simp [envName, String.ext_iff])
  · exact notMem_wvars_scatDeadCom_lit hloc
      (RamDriverIO.notMem_of_append (p := "ctr") (s := toString a) (by decide))
      (RamDriverIO.notMem_of_append (p := "ctr") (s := toString a) (by decide))
      (not_ext_bb_ctrName a) (fun q => by simp [ctrName, envName, String.ext_iff])
  · exact notMem_wvars_scatDeadCom_lit hloc
      (RamDriverIO.notMem_of_append (p := "xq") (s := toString j) (by decide))
      (RamDriverIO.notMem_of_append (p := "xq") (s := toString j) (by decide))
      (not_ext_bb_xpName j) (fun q => by simp [xpName, envName, String.ext_iff])
  · exact notMem_wvars_scatDeadCom_lit hloc (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, String.ext_iff]) (not_ext_bb_mnumName a)
      (fun q => by simp [mnumName, envName, String.ext_iff])
  · exact notMem_wvars_scatDeadCom_lit hloc
      (RamDriverIO.notMem_of_append (p := "kq") (s := toString j) (by decide))
      (RamDriverIO.notMem_of_append (p := "kq") (s := toString j) (by decide))
      (not_ext_bb_kkName j) (fun q => by simp [kkName, envName, String.ext_iff])

/-- And across the flag assignment that follows it in the fold. -/
theorem DeadPre.run_flag {i k : ℕ} {σ σ' : Env} {K : ℕ}
    (h : DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ)
    (hrun : Run B (.assign (flgName j i k) (.var "flag")) σ σ' K) :
    DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m X W w
      Alv' Gam' C' σ' := by
  have hne : ∀ {p : String} (hp : '_' ∉ p.toList) (a : ℕ),
      p ++ toString a ∉ (Com.assign (flgName j i k) (.var "flag")).wvars := by
    intro p hp a hm
    simp only [Com.wvars, List.mem_cons, List.not_mem_nil, or_false] at hm
    exact RamDriverFrames.underscore_notMem_prefixed hp a
      (hm ▸ RamDriverFrames.underscore_mem_flgName j i k)
  refine h.run hrun (fun a ha => absurd ha (by simp [Com.warrs]))
    (by simp [Com.warrs]) (fun y hy => ?_) (fun a => hne (by decide) a) (hne (by decide) j)
    (fun a => hne (by decide) a) (hne (by decide) j)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  simp only [Com.wvars, List.mem_cons, List.not_mem_nil, or_false]
  rcases hy with rfl | rfl | rfl <;>
    exact RamDriverFrames.flgName_ne_lit j i k (by decide) ∘ Eq.symm

/-! ### §4 One atom, walked

The nine passes in sequence. What crosses each seam is stated by
`Refine.ScatterDeadPass` §5d, and the reading of the four registers at
the end is `atomTerms_iff_scatVal_of_clusterData` — whose three threads
are all in scope here: `hXalive` and `hbud` are
`RamDriverCluster.ScatterStep`'s two antecedents,
`RamDriverCluster.KillListAt` is `DeadPre`'s second conjunct, and
`RamDriverCluster.ClusterData` its first's. Nothing is pushed past
`clusterStepImplements`'s existentials. -/

/-- A name carrying the separator is none of a list of names without
one. -/
theorem notMem_of_underscore {y : String} (hy : '_' ∈ y.toList) {l : List String}
    (hl : ∀ q ∈ l, '_' ∉ q.toList) : y ∉ l := fun hm => hl y hm hy

open Classical in
/-- **One dead-aware scatter atom, discharged.** The kill walk, the
outside probe and its bit, the outside count, the atom's filtered member
list, the engine's calling convention, the active-set engine and the
verdict — and the flag they leave is the atom's greedy value in the
cluster step's arena.

The atom's row is read at the child's member list and at the turn's kill
list only; no clause about a row outside `alive ∪ kills` enters, which
is the whole content of the R1.8 domain change. -/
theorem scatDead_spec {bw nb : ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hXalive : ∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0)
    (hbud : ∀ r : ℕ, BallBudget n r G Alv' O bw nb)
    {σs : ScatterSentence (sigL cap mb (j + 1))}
    (hβ : σs.β ∈ tablesAt q_top cap mb φ (j + 1)) (hloc : IsLocal σs.β)
    (hrB : σs.r + 1 < B) (htB : σs.t + n + mb < B)
    {Kb : ℕ} (hKb : ScatterDeadPass.scatDeadK σs.β n n mb n bw nb σs.t ≤ Kb) :
    Spec B (DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m
        X W w Alv' Gam' C')
      (scatDeadCom j (posOf σs.β (tablesAt q_top cap mb φ (j + 1))) σs.β σs.r σs.t)
      (fun σ σ' => DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m
          X W w Alv' Gam' C' σ' ∧ σ'.out = σ.out ∧
        σ'.vars (curName j) = σ.vars (curName j) ∧
        (∀ i' k', σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
        σ'.vars "flag" ≤ 1 ∧
        (σ'.vars "flag" ≠ 0 ↔ ScatVal (stepArenaP (masked G M) X w)
          (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) σs))
      Kb := by
  classical
  have h1B : 1 < B := hB.one_lt
  have hnB : n < B := hB.n_lt
  have hnsB : ns < B := hB.ns_lt
  have hmbB : mb < B := hB.mb_lt
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hpre, hklist, hbarr⟩ := id hσ
  obtain ⟨hturn, hdata, hcolarr, hcolbit, hcolread, htab⟩ := id hpre
  obtain ⟨⟨Xa, hXaA, hXaS, hXaB⟩, ⟨Wa, hWaA, hWaS, hWaB⟩, ⟨Ra, hRaA, hRaS, hRaB⟩,
    halvA, hAlvB, hmaskeq, hmaskpt, hgamA, hGamB, Mem1, mm1, hmem1A, hmem1V, hmem1E,
    hmem1B⟩ := id hdata.1
  obtain ⟨kl, kq, hklA, hkkV, hkqmb, hkllt, hklinj, hklsnd, hklcmp⟩ := id hklist
  obtain ⟨hp, hpβ⟩ := getElem_posOf hβ
  obtain ⟨Tb, hTbA, hTb1, hTbS⟩ := htab _ hp
  have hn : σ.vars "n" = n := hpre.n_eq
  have hm1n : mm1 ≤ n := hmem1E.card_le
  -- the atom's set, as the child's table row decides it
  set S := ScatterDeadFold.satSet G (masked G M) Alv' (colRead n C (sigL cap mb j)) X w σs.β
    with hSdef
  -- **the row decides the atom on `alive ∪ kills` and nowhere else** (wave
  -- R1.8-T3-flip (c2b)): the domain `RamDriverCluster.rowDom` is where the rows
  -- exist, and every read below is inside it — the kill list's entries, the
  -- child's member list, and nothing more
  have hbitS : ∀ v : Fin n, v ∈ RamDriverCluster.rowDom M Alv' X W →
      (Tb (v : ℕ) ≠ 0 ↔ v ∈ S) := by
    intro v hv
    rw [hTbS v hv, hpβ, hcolread, hSdef]
    exact Iff.rfl
  have hklrow : ∀ e, (he : e < kq) →
      (⟨kl e, hkllt e he⟩ : Fin n) ∈ RamDriverCluster.rowDom M Alv' X W := by
    intro e he
    obtain ⟨v, hv, hM, hX, hW⟩ := hklsnd e he
    have hvv : (⟨kl e, hkllt e he⟩ : Fin n) = v := Fin.ext hv.symm
    rw [hvv]
    exact RamDriverCluster.mem_rowDom_of_kill ⟨hM, hX, hW⟩
  -- **pass 1**: the atom's bits at the turn's kills
  obtain ⟨σ₁, hr₁, hkc₁, hkk₁, hklA₁, hTbA₁⟩ :=
    (ScatterDeadPass.killSumCom_spec (B := B) (n := n) (mb := mb) (j := j)
      (ti := posOf σs.β (tablesAt q_top cap mb φ (j + 1))) (kq := kq) (kl := kl) (Tb := Tb)
      h1B hnB hmbB hkqmb hkllt
      (fun e he => hTb1 ⟨kl e, hkllt e he⟩ (hklrow e he))).run ⟨hkkV, hklA, hTbA⟩
  have hfa₁ : ∀ a : String, σ₁.arrs a = σ.arrs a :=
    fun a => hr₁.frame_arr a (by rw [ScatterDeadPass.warrs_killSumCom]; simp)
  have hfv₁ : ∀ y : String, y ≠ "kc" → y ≠ "ke" → σ₁.vars y = σ.vars y :=
    fun y h₁ h₂ => hr₁.frame_var y (ScatterDeadPass.notMem_wvars_killSumCom _ _ h₁ h₂)
  -- **pass 2**: the first dead vertex outside the cluster
  obtain ⟨σ₂, hr₂, hn₂, halv₂, hclu₂, hof₂, hno₂, hyes₂⟩ :=
    (ScatterDeadPass.outProbeCom_spec (B := B) (n := n) (j := j) (Alv' := Alv') (Xa := Xa)
      h1B hnB hAlvB (fun k hk => lt_of_le_of_lt (hXaB k hk) h1B)).run
      ⟨by rw [hfv₁ "n" (by decide) (by decide)]; exact hn,
        by rw [hfa₁]; exact halvA, by rw [hfa₁]; exact hXaA⟩
  have hfa₂ : ∀ a : String, σ₂.arrs a = σ₁.arrs a :=
    fun a => hr₂.frame_arr a (by rw [ScatterDeadPass.warrs_outProbeCom]; simp)
  have hfv₂ : ∀ y : String, y ≠ "of" → y ≠ "oz" → y ≠ "oi" → σ₂.vars y = σ₁.vars y :=
    fun y h₁ h₂ h₃ => hr₂.frame_var y (ScatterDeadPass.notMem_wvars_outProbeCom _ h₁ h₂ h₃)
  have hkc₂ : σ₂.vars "kc" = ∑ e ∈ Finset.range kq, Tb (kl e) := by
    rw [hfv₂ "kc" (by decide) (by decide) (by decide)]; exact hkc₁
  -- **pass 3**: the outside class's bit, guarded by the probe's flag
  have hbotmem₂ : BotMem B σs.β "bb" σ₂ :=
    botMem_of_length (fun a => by rw [hfa₂, hfa₁]) _ "bb"
      (hpβ ▸ hbarr.2 (j + 1) _ hp)
  have hcolarr₂ : ∀ c < sigL cap mb (j + 1), σ₂.arrs (colName (j + 1) c) = arrOf n (C' c) :=
    fun c hc => by rw [hfa₂, hfa₁]; exact hcolarr c hc
  obtain ⟨σ₃, K₃, hr₃, hK₃, hbb1₃, hout₃⟩ :
      ∃ (σ₃ : Env) (K₃ : ℕ), Run B (atomBitCom (j + 1) σs.β) σ₂ σ₃ K₃ ∧
        K₃ ≤ ScatterDeadPass.atomBitCost σs.β ∧ σ₃.vars "bb" ≤ 1 ∧
        (((∀ z, z < n → ¬ (Alv' z = 0 ∧ Xa z = 0)) ∧ σ₃.vars "bb" = 0) ∨
          (∃ zo : Fin n, Alv' (zo : ℕ) = 0 ∧ Xa (zo : ℕ) = 0 ∧ σ₃.vars "bb" ≤ 1 ∧
            (σ₃.vars "bb" ≠ 0 ↔ zo ∈ S))) := by
    by_cases hof : σ₂.vars "of" = 0
    · obtain ⟨τ, hrτ, hbb0⟩ :=
        (ScatterDeadPass.atomBitCom_spec_empty (B := B) (jd := j + 1) (β := σs.β)
          h1B hloc).run ⟨hof, by omega⟩
      exact ⟨τ, _, hrτ, le_rfl, by omega, Or.inl ⟨hno₂ hof, hbb0⟩⟩
    · obtain ⟨hozlt, hozdead, hozout⟩ := hyes₂ hof
      obtain ⟨τ, hrτ, hbb1, hbbiff⟩ :=
        (ScatterDeadPass.atomBitCom_spec_found (B := B) (n := n) (jd := j + 1) (C' := C')
          (β := σs.β) (G := G) (Alv' := Alv') (zo := ⟨σ₂.vars "oz", hozlt⟩)
          h1B hnB hcolbit hloc hozdead).run
          ⟨hcolarr₂, hbotmem₂, hof, by omega, rfl⟩
      exact ⟨τ, _, hrτ, le_rfl, hbb1,
        Or.inr ⟨⟨σ₂.vars "oz", hozlt⟩, hozdead, hozout, hbb1, by
          rw [hbbiff, hcolread]; exact Iff.rfl⟩⟩
  have hfa₃ : ∀ a : String, ¬ RamDriverBot.Ext "bb" a → σ₃.arrs a = σ₂.arrs a :=
    fun a ha => hr₃.frame_arr a (fun hm => ha (ScatterDeadPass.warrs_atomBitCom σs.β hloc hm))
  have hfv₃ : ∀ y : String, ¬ RamDriverBot.Ext "bb" y → (∀ q, y ≠ envName q) →
      σ₃.vars y = σ₂.vars y := by
    intro y h₁ h₂
    refine hr₃.frame_var y (fun hm => ?_)
    rcases ScatterDeadPass.wvars_atomBitCom σs.β hloc hm with h | ⟨q, hq⟩
    · exact h₁ h
    · exact h₂ q hq
  have hnotbb : ∀ (p : String) (c₁ c₂ : Char) (t : List Char),
      p.toList = c₁ :: c₂ :: t → ¬ (c₁ = 'b' ∧ c₂ = 'b') → ¬ RamDriverBot.Ext "bb" p :=
    fun _ _ _ _ h hc => not_ext_bb_of_cons h hc
  have hkc₃ : σ₃.vars "kc" = ∑ e ∈ Finset.range kq, Tb (kl e) := by
    rw [hfv₃ "kc" (not_ext_bb_of_cons rfl (by decide))
      (fun q => by simp [envName, String.ext_iff])]
    exact hkc₂
  -- **pass 4**: the outside class's count, off three landed scalars
  have hmm1B : mm1 < B := by omega
  have hkqB : kq < B := by omega
  obtain ⟨σ₄, hr₄, hoc₄, hn₄, hmm₄, hkq₄⟩ :=
    (ScatterDeadPass.outCntCom_spec (B := B) (n := n) (j := j) (mm1 := mm1) (kq := kq)
      h1B hnB hmm1B hkqB).run
      ⟨by rw [hfv₃ "n" (not_ext_bb_short (by decide))
            (fun q => by simp [envName, String.ext_iff])]; exact hn₂,
        by rw [hfv₃ _ (not_ext_bb_mnumName (j + 1))
            (fun q => by simp [mnumName, envName, String.ext_iff]),
          hfv₂ _ (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
            (by simp [mnumName, String.ext_iff]),
          hfv₁ _ (by simp [mnumName, String.ext_iff])
            (by simp [mnumName, String.ext_iff])]; exact hmem1V,
        by rw [hfv₃ _ (not_ext_bb_kkName j)
            (fun q => by simp [kkName, envName, String.ext_iff]),
          hfv₂ _ (by simp [kkName, String.ext_iff]) (by simp [kkName, String.ext_iff])
            (by simp [kkName, String.ext_iff]),
          hfv₁ _ (by simp [kkName, String.ext_iff])
            (by simp [kkName, String.ext_iff])]; exact hkkV⟩
  have hfa₄ : ∀ a : String, σ₄.arrs a = σ₃.arrs a :=
    fun a => hr₄.frame_arr a (by rw [ScatterDeadPass.warrs_outCntCom]; simp)
  have hfv₄ : ∀ y : String, y ≠ "oc" → σ₄.vars y = σ₃.vars y :=
    fun y h => hr₄.frame_var y (ScatterDeadPass.notMem_wvars_outCntCom _ h)
  have hkc₄ : σ₄.vars "kc" = ∑ e ∈ Finset.range kq, Tb (kl e) := by
    rw [hfv₄ "kc" (by decide)]; exact hkc₃
  have hbb₄ : σ₄.vars "bb" = σ₃.vars "bb" := hfv₄ "bb" (by decide)
  -- **pass 5**: the atom's own member list, out of the child's
  have hmemsz₄ : ∃ g : ℕ → ℕ, σ₄.arrs "mem" = arrOf n g := by
    have hlm : LevelMem B n cap mb σ₄ :=
      levelMem_run (hr₁.seq (hr₂.seq (hr₃.seq hr₄))) hpre.mem
    exact hlm.memArr
  obtain ⟨σ₅, hr₅, Mem, mm, hmemA₅, hmmv₅, hmmle, hml₅, hmem1A₅, hTbA₅, hmm₅⟩ :=
    (ScatterDeadPass.atomMemCom_spec (B := B) (n := n) (j := j)
      (ti := posOf σs.β (tablesAt q_top cap mb φ (j + 1))) (mm1 := mm1) (Mem1 := Mem1)
      (Tb := Tb) (A := Alv') h1B hnB hmem1E
      (fun p hp' => lt_of_le_of_lt
        (hTb1 ⟨Mem1 p, hmem1E.1 p hp'⟩
          (RamDriverCluster.mem_rowDom_of_alive (hmem1E.2.2.1 p hp'))) h1B)).run
      ⟨hmm₄,
        by rw [hfa₄, hfa₃ _ (not_ext_bb_memName (j + 1)), hfa₂, hfa₁]; exact hmem1A,
        by rw [hfa₄, hfa₃ _ (not_ext_bb_tabName (j + 1) _), hfa₂, hfa₁]; exact hTbA,
        hmemsz₄⟩
  have hfa₅ : ∀ a : String, a ≠ "mem" → σ₅.arrs a = σ₄.arrs a :=
    fun a ha => hr₅.frame_arr a (by rw [ScatterDeadPass.warrs_atomMemCom]; simpa using ha)
  have hfv₅ : ∀ y : String, y ≠ "mm" → y ≠ "ak" → y ≠ "av" → σ₅.vars y = σ₄.vars y :=
    fun y h₁ h₂ h₃ => hr₅.frame_var y (ScatterDeadPass.notMem_wvars_atomMemCom _ _ h₁ h₂ h₃)
  -- **pass 6**: the child's mask, into the name the engine reads
  have hn₅ : σ₅.vars "n" = n := by
    rw [hfv₅ "n" (by decide) (by decide) (by decide)]; exact hn₄
  have halvsz₅ : (σ₅.arrs "alv").length = n := by
    have hlm : LevelMem B n cap mb σ₅ :=
      levelMem_run (hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq hr₅)))) hpre.mem
    exact hlm.1.length (p := ("alv", n)) (by simp)
  obtain ⟨σ₆, hr₆, hn₆, halvA₆, halv₆⟩ :=
    (RamDriverIO.copy_spec (B := B) (n := n) (src := alvName (j + 1)) (dst := "alv")
      (RamDriverFrames.alvName_ne_alv (j + 1)) Alv' hnB hAlvB).run
      ⟨hn₅,
        by rw [hfa₅ _ (by simp [alvName, String.ext_iff]), hfa₄,
          hfa₃ _ (not_ext_bb_alvName (j + 1)), hfa₂, hfa₁]; exact halvA,
        halvsz₅⟩
  have hfa₆ : ∀ a : String, a ≠ "alv" → σ₆.arrs a = σ₅.arrs a :=
    fun a ha => hr₆.frame_arr a (by rw [ScatterDeadPass.warrs_copyCom]; simpa using ha)
  have hfv₆ : ∀ y : String, y ≠ "i" → σ₆.vars y = σ₅.vars y :=
    fun y h => hr₆.frame_var y (ScatterDeadPass.notMem_wvars_copyCom _ _ h)
  -- **pass 7**: a clean distance array, the engine's other entry condition
  have hdistsz₆ : (σ₆.arrs "dist").length = n := by
    have hlm : LevelMem B n cap mb σ₆ :=
      levelMem_run (hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq hr₆))))) hpre.mem
    exact hlm.1.length (p := ("dist", n)) (by simp)
  obtain ⟨σ₇, hr₇, g₇, hdist₇, hdistval₇⟩ :=
    (RamDriverIO.fill_spec (B := B) (n := n) (c := σs.r + 1) (a := "dist")
      hnB hrB).run ⟨hdistsz₆, hn₆⟩
  have hfa₇ : ∀ a : String, a ≠ "dist" → σ₇.arrs a = σ₆.arrs a :=
    fun a ha => hr₇.frame_arr a (by rw [ScatterDeadPass.warrs_fillCom]; simpa using ha)
  have hfv₇ : ∀ y : String, y ≠ "i" → σ₇.vars y = σ₆.vars y :=
    fun y h => hr₇.frame_var y (ScatterDeadPass.notMem_wvars_fillCom _ _ h)
  -- **pass 8**: the active-set engine, at the atom's alive part
  have hqsz₇ : (∃ g, σ₇.arrs "q" = arrOf n g) ∧ (∃ g, σ₇.arrs "qd" = arrOf n g) ∧
      (∃ g, σ₇.arrs "exc" = arrOf n g) := by
    have hlm : LevelMem B n cap mb σ₇ :=
      levelMem_run (hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq (hr₆.seq hr₇)))))) hpre.mem
    exact ⟨hlm.1 ("q", n) (by simp), hlm.qdArr, hlm.1 ("exc", n) (by simp)⟩
  have harena₇ : ArenaA n Ws mm σs.r O T Alv' Mem σ₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hqsz₇.1, hqsz₇.2.1⟩
    · rw [hfv₇ "n" (by decide)]; exact hn₆
    · rw [hfv₇ "mm" (by decide), hfv₆ "mm" (by decide)]; exact hmmv₅
    · rw [hfa₇ _ (by decide), hfa₆ _ (by decide), hfa₅ _ (by decide), hfa₄,
        hfa₃ "off" (not_ext_bb_of_cons rfl (by decide)), hfa₂, hfa₁]
      exact hturn.1.2.1
    · rw [hfa₇ _ (by decide), hfa₆ _ (by decide), hfa₅ _ (by decide), hfa₄,
        hfa₃ "tgt" (not_ext_bb_of_cons rfl (by decide)), hfa₂, hfa₁]
      exact hturn.1.2.2.1
    · rw [hfa₇ _ (by decide)]; exact halv₆
    · rw [hfa₇ _ (by decide), hfa₆ _ (by decide)]; exact hmemA₅
    · rw [hdist₇]; exact arrOf_congr (fun i hi => hdistval₇ i hi)
  obtain ⟨σ₈, hr₈, hflag₈, hflag1₈, hcnt₈, hkey₈⟩ :=
    (ScatterDeadEngine.scatBlockCnt_specW (B := B) (n := n) (ns := ns) (nt := Ws)
      (mm := mm) (r := σs.r) (t := σs.t) (G := G) (M := Alv') (O := O) (T := T) (Mem := Mem)
      (X := ScatterDeadPass.bitSet n Alv' Tb) (bw := bw) (nb := nb)
      hcsr hnB hnsB hpre.nsW hrB (by omega) hAlvB hml₅ (hbud σs.r)).run
      ⟨harena₇, hqsz₇.2.2⟩
  have hfa₈ : ∀ a : String, a ≠ "exc" → a ≠ "dist" → a ≠ "q" → a ≠ "qd" →
      σ₈.arrs a = σ₇.arrs a := by
    intro a h₁ h₂ h₃ h₄
    refine hr₈.frame_arr a (fun hm => ?_)
    rcases ScatterDeadPass.warrs_scatBlockCom _ _ hm with h | h | h | h
    exacts [h₁ h, h₂ h, h₃ h, h₄ h]
  have hfv₈ : ∀ y ∈ ["kc", "bb", "oc", "n", "mm"], σ₈.vars y = σ₇.vars y :=
    fun y hy => hr₈.frame_var y (ScatterDeadPass.notMem_wvars_scatBlockCom _ _ y hy)
  -- the three dead registers, at the engine's exit
  have hkc₈ : σ₈.vars "kc" = ∑ e ∈ Finset.range kq, Tb (kl e) := by
    rw [hfv₈ "kc" (by simp), hfv₇ "kc" (by decide), hfv₆ "kc" (by decide),
      hfv₅ "kc" (by decide) (by decide) (by decide)]
    exact hkc₄
  have hbb₈ : σ₈.vars "bb" = σ₃.vars "bb" := by
    rw [hfv₈ "bb" (by simp), hfv₇ "bb" (by decide), hfv₆ "bb" (by decide),
      hfv₅ "bb" (by decide) (by decide) (by decide)]
    exact hbb₄
  have hoc₈ : σ₈.vars "oc" = n - mm1 - kq := by
    rw [hfv₈ "oc" (by simp), hfv₇ "oc" (by decide), hfv₆ "oc" (by decide),
      hfv₅ "oc" (by decide) (by decide) (by decide)]
    exact hoc₄
  -- **pass 9**: the verdict
  have hkcle : σ₈.vars "kc" ≤ kq := by
    rw [hkc₈]
    calc (∑ e ∈ Finset.range kq, Tb (kl e)) ≤ ∑ _e ∈ Finset.range kq, 1 :=
          Finset.sum_le_sum fun e he =>
            hTb1 ⟨kl e, hkllt e (Finset.mem_range.1 he)⟩
              (hklrow e (Finset.mem_range.1 he))
      _ = kq := by simp
  have hbble : σ₈.vars "bb" ≤ 1 := by rw [hbb₈]; exact hbb1₃
  have hocle : σ₈.vars "oc" ≤ n := by rw [hoc₈]; omega
  have hmul : σ₈.vars "bb" * σ₈.vars "oc" ≤ n := by
    calc σ₈.vars "bb" * σ₈.vars "oc" ≤ 1 * n := Nat.mul_le_mul hbble hocle
      _ = n := by omega
  obtain ⟨σ₉, hr₉, hfl1₉, hfliff₉⟩ :=
    (ScatterDeadPass.atomFlagCom_spec (B := B) (t := σs.t) (cnt := σ₈.vars "cnt")
      (kc := σ₈.vars "kc") (bb := σ₈.vars "bb") (oc := σ₈.vars "oc")
      h1B (by omega) (by omega) (by omega) (by omega)).run ⟨rfl, rfl, rfl, rfl⟩
  -- the whole run
  have hrun : Run B (scatDeadCom j (posOf σs.β (tablesAt q_top cap mb φ (j + 1)))
      σs.β σs.r σs.t) σ σ₉ _ :=
    hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq (hr₆.seq (hr₇.seq (hr₈.seq hr₉)))))))
  refine ⟨σ₉, _, hrun, ?_, hσ.run_scatDead hloc hrun,
    hrun.out_eq (noWrite_scatDeadCom _ _ _ _ _), ?_, ?_, hfl1₉, ?_⟩
  -- the charge
  · refine le_trans ?_ hKb
    have hsb := ScatterBlock.scatBlockK_mono (mm := mm) (mm' := n) (bw := bw) (bw' := bw)
      (nb := nb) (nb' := nb) (t := σs.t) (t' := σs.t) (by omega) le_rfl le_rfl le_rfl
    simp only [ScatterDeadPass.scatDeadK, ScatterDeadPass.killSumCost,
      ScatterDeadPass.atomMemCost, ScatterDeadPass.outProbeCost,
      ScatterDeadPass.outCntCost, ScatterDeadPass.atomFlagCost]
    omega
  -- the cursor, and the flags
  · exact hrun.frame_var _ (notMem_wvars_scatDeadCom_lit hloc
      (RamDriverIO.notMem_of_append (p := "cu") (s := toString j) (by decide))
      (RamDriverIO.notMem_of_append (p := "cu") (s := toString j) (by decide))
      (not_ext_bb_curName j) (fun q => by simp [curName, envName, String.ext_iff]))
  · exact fun i' k' => hrun.frame_var _ (notMem_wvars_scatDeadCom_lit hloc
      (notMem_of_underscore (RamDriverFrames.underscore_mem_flgName j i' k') (by decide))
      (notMem_of_underscore (RamDriverFrames.underscore_mem_flgName j i' k') (by decide))
      (not_ext_bb_flgName j i' k')
      (fun q hq => absurd (hq ▸ RamDriverFrames.underscore_mem_flgName j i' k' :
          '_' ∈ (envName q).toList)
        (RamDriverFrames.underscore_notMem_prefixed (p := "ev") (by decide) q)))
  -- and what the flag is worth
  · rw [hfliff₉, ← masked_alv_eq hdata]
    refine (ScatterDeadPass.atomTerms_iff_scatVal_of_clusterData (n := n)
      (L := sigL cap mb j) (mb := mb) (cap := cap) (jd := j) (Bw := B) (G := G)
      (M := M) (Alv' := Alv') (Gam' := Gam') (Xa := Xa) (Tb := Tb) (kl := kl)
      (col := colRead n C (sigL cap mb j)) (w := w) (X := X) (W := W) (mm1 := mm1)
      (kq := kq) (cnt := σ₈.vars "cnt") (kc := σ₈.vars "kc") (bb := σ₈.vars "bb")
      (oc := σ₈.vars "oc") (σ := σ) σs hloc hdata hXaS hXalive ?_ hkllt ?_ ?_ ?_ ?_
      hkc₈ hoc₈ ?_ ?_).symm
    · exact ScatterDeadPass.ncard_eq_of_enum hmem1E.1
        (fun i hi k hk hik => by
          rcases lt_trichotomy i k with h | h | h
          · exact absurd (hmem1E.2.1 i k h hk) (by omega)
          · exact h
          · exact absurd (hmem1E.2.1 k i h hi) (by omega))
        (fun k hk => hmem1E.2.2.1 k hk)
        (fun v hv => hmem1E.2.2.2 (v : ℕ) v.isLt hv)
    · exact hklinj
    · intro e he
      obtain ⟨v, hv, hM, hX, hW⟩ := hklsnd e he
      have : (⟨kl e, hkllt e he⟩ : Fin n) = v := Fin.ext hv.symm
      rw [this]
      exact ⟨hM, hX, hW⟩
    · exact fun v hv => hklcmp v hv.1 hv.2.1 hv.2.2
    · exact fun v hv => ⟨hTb1 v (RamDriverCluster.mem_rowDom_of_kill hv),
        hbitS v (RamDriverCluster.mem_rowDom_of_kill hv)⟩
    · rw [hbb₈]
      rcases hout₃ with ⟨hno, hbb0⟩ | ⟨zo, h₁, h₂, h₃, h₄⟩
      · exact Or.inl ⟨hno, hbb0⟩
      · exact Or.inr ⟨zo, h₁, h₂, h₃, h₄⟩
    · intro e
      have := hkey₈ e
      rwa [ScatterDeadPass.bitSet_eq_inter
        (fun v hv => hbitS v (RamDriverCluster.mem_rowDom_of_alive hv))] at this

/-! ### §5 The folds

One atom's flag, then the fold over a formula's atoms, then the fold
over a depth's table — the same three-step shape
`RamDriverFrames.atom_spec`/`atoms_spec`/`blocks_spec` has for the
landed `RamScatter.scatterCom` phase, at the same flag names and with
the same postcondition. -/

/-- The per-atom charge: the nine passes and the flag. -/
noncomputable def deadAtomK {L : ℕ} (β : DistFO L 1) (n mm1 kq mm bw nb t : ℕ) : ℕ :=
  ScatterDeadPass.scatDeadK β n mm1 kq mm bw nb t + 2

open Classical in
/-- **One atom and its flag.** -/
theorem atomDead_spec {bw nb : ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hXalive : ∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0)
    (hbud : ∀ r : ℕ, BallBudget n r G Alv' O bw nb)
    (i k : ℕ) {σs : ScatterSentence (sigL cap mb (j + 1))}
    (hβ : σs.β ∈ tablesAt q_top cap mb φ (j + 1)) (hloc : IsLocal σs.β)
    (hrB : σs.r + 1 < B) (htB : σs.t + n + mb < B)
    {Kb : ℕ} (hKb : deadAtomK σs.β n n mb n bw nb σs.t ≤ Kb) :
    Spec B (DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m
        X W w Alv' Gam' C')
      (.seq (scatDeadCom j (posOf σs.β (tablesAt q_top cap mb φ (j + 1))) σs.β σs.r σs.t)
        (.assign (flgName j i k) (.var "flag")))
      (fun σ σ' => DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m
          X W w Alv' Gam' C' σ' ∧ σ'.out = σ.out ∧
        σ'.vars (curName j) = σ.vars (curName j) ∧
        (∀ i' k', ¬(i' = i ∧ k' = k) →
          σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
        σ'.vars (flgName j i k) ≤ 1 ∧
        (σ'.vars (flgName j i k) ≠ 0 ↔ ScatVal (stepArenaP (masked G M) X w)
          (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) σs))
      Kb := by
  classical
  have hcur : curName j ≠ flgName j i k := fun h =>
    RamDriverFrames.underscore_notMem_prefixed (p := "cu") (by decide) j
      (h ▸ (RamDriverFrames.underscore_mem_flgName j i k :
        '_' ∈ (flgName j i k).toList) : '_' ∈ (curName j).toList)
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨τ, hrτ, hdead, hout, hcurτ, hflgfr, hfl1, hfliff⟩ :=
    (scatDead_spec hcsr hB hXalive hbud hβ hloc hrB htB (le_refl _)).run hσ
  have hflagB : τ.vars "flag" < B := lt_of_le_of_lt hfl1 hB.one_lt
  have r₂ : Run B (.assign (flgName j i k) (.var "flag")) τ
      (τ.setVar (flgName j i k) (τ.vars "flag")) (1 + (Expr.var "flag").size) :=
    Run.assign (evalB_var hflagB)
  refine ⟨_, _, hrτ.seq r₂, ?_, hdead.run_flag r₂, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans ?_ hKb
    rw [deadAtomK]
    simp only [Expr.size]
    omega
  · rw [out_setVar]; exact hout
  · rw [vars_setVar, if_neg hcur]; exact hcurτ
  · intro i' k' hik
    rw [vars_setVar, if_neg (fun hc => hik (by
      obtain ⟨-, hi, hk⟩ := RamDriverFrames.flgName_inj hc; exact ⟨hi, hk⟩))]
    exact hflgfr i' k'
  · rw [vars_setVar, if_pos rfl]; exact hfl1
  · rw [vars_setVar, if_pos rfl]; exact hfliff

open Classical in
/-- **The dead-aware scatter block of one tabled formula**, over any list
of atoms starting at any position. -/
theorem atomsDead_spec {bw nb : ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hXalive : ∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0)
    (hbud : ∀ r : ℕ, BallBudget n r G Alv' O bw nb)
    (i : ℕ) {Kb : ℕ} :
    ∀ (l : List (ScatterSentence (sigL cap mb (j + 1)))) (k₀ : ℕ),
      (∀ σs ∈ l, σs.β ∈ tablesAt q_top cap mb φ (j + 1) ∧ σs.r + 1 < B ∧
        σs.t + n + mb < B ∧ deadAtomK σs.β n n mb n bw nb σs.t ≤ Kb) →
      Spec B (DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m
          X W w Alv' Gam' C')
        (foldIdx (fun k σs =>
            Com.seq (scatDeadCom j (posOf σs.β (tablesAt q_top cap mb φ (j + 1)))
              σs.β σs.r σs.t) (.assign (flgName j i k) (.var "flag"))) k₀ l)
        (fun σ σ' => DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m
            X W w Alv' Gam' C' σ' ∧ σ'.out = σ.out ∧
          σ'.vars (curName j) = σ.vars (curName j) ∧
          (∀ i' k', (i' ≠ i ∨ ∀ p < l.length, k' ≠ k₀ + p) →
            σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
          ∀ p, ∀ _ : p < l.length,
            σ'.vars (flgName j i (k₀ + p)) ≤ 1 ∧
            (σ'.vars (flgName j i (k₀ + p)) ≠ 0 ↔
              ScatVal (stepArenaP (masked G M) X w)
                (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) l[p]))
        (Kb * l.length + 1) := by
  intro l
  induction l with
  | nil =>
      intro k₀ _
      refine (Spec.skip (B := B) (P := DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord
        Xoff Xmem asg m X W w Alv' Gam' C')).post ?_ |>.mono (by simp)
      rintro σ σ' hσ rfl
      exact ⟨hσ, rfl, rfl, fun _ _ _ => rfl, fun p hp => absurd hp (by simp)⟩
  | cons x xs ih =>
      intro k₀ hall
      obtain ⟨hxβ, hxr, hxt, hxK⟩ := hall x (by simp)
      refine ((atomDead_spec hcsr hB hXalive hbud i k₀ hxβ
        (tableRank_of_mem_tablesAt (j + 1) _ hxβ).1 hxr hxt hxK).seq
        (ih (k₀ + 1) (fun s hs => hall s (by simp [hs]))) (fun _ _ _ hq => hq.1) ?_).mono
        (by simp [Nat.mul_succ]; omega)
      rintro σ σ' σ'' - ⟨-, hout', hc', hfl', hle', hval'⟩ ⟨hpre'', hout'', hc'', hfl'', hval''⟩
      refine ⟨hpre'', by rw [hout'', hout'], by rw [hc'', hc'], ?_, ?_⟩
      · intro i' k' hik
        rw [hfl'' i' k' ?_, hfl' i' k' ?_]
        · rcases hik with h | h
          · exact fun hc => h hc.1
          · exact fun hc => h 0 (by simp) (by omega)
        · rcases hik with h | h
          · exact _root_.Or.inl h
          · exact _root_.Or.inr fun p hp => by
              have := h (p + 1) (by simp only [List.length_cons]; omega); omega
      · intro p hp
        match p with
        | 0 =>
            rw [Nat.add_zero, hfl'' i k₀ (_root_.Or.inr fun p _ => by omega)]
            exact ⟨hle', hval'⟩
        | q + 1 =>
            rw [show k₀ + (q + 1) = k₀ + 1 + q from by omega]
            simpa using hval'' q (by simpa using hp)

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The dead-aware scatter phase of a depth**, over any list of tabled
formulas starting at any position. -/
theorem blocksDead_spec {bw nb : ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hXalive : ∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0)
    (hbud : ∀ r : ℕ, BallBudget n r G Alv' O bw nb)
    {Kb Ki : ℕ} :
    ∀ (l : List (DistFO (sigL cap mb j) 1)) (i₀ : ℕ),
      (∀ β ∈ l, β ∈ tablesAt q_top cap mb φ j) →
      (∀ β ∈ l, ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧
          deadAtomK σs.β n n mb n bw nb σs.t ≤ Kb) →
      (∀ β ∈ l, Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki) →
      Spec B (DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m
          X W w Alv' Gam' C')
        (foldIdx (fun i β => scatterDeadCom q_top cap mb φ j i β) i₀ l)
        (fun σ σ' => DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m
            X W w Alv' Gam' C' σ' ∧ σ'.out = σ.out ∧
          σ'.vars (curName j) = σ.vars (curName j) ∧
          (∀ i' k', (∀ p < l.length, i' ≠ i₀ + p) →
            σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
          ∀ p, ∀ hp : p < l.length,
            ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j l[p])).2,
              σ'.vars (flgName j (i₀ + p)
                  (posOf σs (bcAtomsOf q_top (stepFml cap mb j l[p])).2)) ≤ 1 ∧
              (σ'.vars (flgName j (i₀ + p)
                  (posOf σs (bcAtomsOf q_top (stepFml cap mb j l[p])).2)) ≠ 0 ↔
                ScatVal (stepArenaP (masked G M) X w)
                  (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) σs))
        (Ki * l.length + 1) := by
  intro l
  induction l with
  | nil =>
      intro i₀ _ _ _
      refine (Spec.skip (B := B) (P := DeadPre B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord
        Xoff Xmem asg m X W w Alv' Gam' C')).post ?_ |>.mono (by simp)
      rintro σ σ' hσ rfl
      exact ⟨hσ, rfl, rfl, fun _ _ _ => rfl, fun p hp => absurd hp (by simp)⟩
  | cons x xs ih =>
      intro i₀ hmem hbnd hcost
      have hx : x ∈ tablesAt q_top cap mb φ j := hmem x (by simp)
      refine (((atomsDead_spec hcsr hB hXalive hbud i₀
          (bcAtomsOf q_top (stepFml cap mb j x)).2 0
          (fun s hs => ⟨mem_tablesAt_succ_of_mem_bcAtomsOf_right hx hs,
            (hbnd x (by simp) s hs).1, (hbnd x (by simp) s hs).2.1,
            (hbnd x (by simp) s hs).2.2⟩)).mono (hcost x (by simp))).seq
        (ih (i₀ + 1) (fun β hβ => hmem β (by simp [hβ]))
          (fun β hβ => hbnd β (by simp [hβ])) (fun β hβ => hcost β (by simp [hβ])))
        (fun _ _ _ hq => hq.1) ?_).mono (by simp [Nat.mul_succ]; omega)
      rintro σ σ' σ'' - ⟨-, hout', hc', hfl', hval'⟩ ⟨hpre'', hout'', hc'', hfl'', hval''⟩
      refine ⟨hpre'', by rw [hout'', hout'], by rw [hc'', hc'], ?_, ?_⟩
      · intro i' k' hik
        rw [hfl'' i' k' (fun p hp => by
            have := hik (p + 1) (by simp only [List.length_cons]; omega); omega),
          hfl' i' k' (_root_.Or.inl (by have := hik 0 (by simp); omega))]
      · intro p hp
        match p with
        | 0 =>
            intro σs hσs
            simp only [List.getElem_cons_zero] at hσs ⊢
            obtain ⟨hlt, hget⟩ := getElem_posOf hσs
            have hb := hval' (posOf σs (bcAtomsOf q_top (stepFml cap mb j x)).2) hlt
            rw [Nat.zero_add, hget] at hb
            rw [Nat.add_zero, hfl'' i₀ _ (fun p _ => by omega)]
            exact hb
        | q + 1 =>
            intro σs hσs
            rw [show i₀ + (q + 1) = i₀ + 1 + q from by omega]
            exact hval'' q (by simpa using hp) σs (by simpa using hσs)

/-! ### §6 The obligation

`RamDriverCluster.ScatterStep`, at the fold of
`RamDriver.scatterDeadCom` and with the postcondition it has always
had. The two antecedents it carries are exactly the two the
composition consumes — the alive-cluster clause and the ball budget —
and `RamDriver.BaseArrs` is the one conjunct the precondition gained,
for the outside class's `RamDriver.botCom` fragment. -/

open Classical in
/-- **The dead-aware scatter atoms of one cluster, discharged.** One
`Refine.ScatterDeadEngine.scatBlockCnt_specW` per scatter atom of every
tabled formula, at the atom's *filtered* member list — never at the
carrier — with the turn's kill bits and the outside class's single bit
supplying the two dead terms. The flag it leaves is the same one the
landed fold left, and it is worth the same thing. -/
theorem scatterDeadStep {bw nb Kb Ki K : ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j, ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
      σs.r + 1 < B ∧ σs.t + n + mb < B ∧ deadAtomK σs.β n n mb n bw nb σs.t ≤ Kb)
    (hcost : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hK : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ K) :
    RamDriverCluster.ScatterStep B q_top cap mb ns Ws ℓ j φ G O T M Gm C π ord Xoff Xmem asg m
      X W w Alv' Gam' C' bw nb K := by
  intro hXalive hbud
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hturn, hdata, hcolarr, hcolbit, hcolread, htab, hklist, hbarr⟩ := hσ
  obtain ⟨σ', hrun, hpre', hout, hc, -, hval⟩ :=
    (blocksDead_spec hcsr hB hXalive hbud (tablesAt q_top cap mb φ j) 0
      (fun _ hβ => hβ) hbnd hcost).run
      ⟨⟨hturn, hdata, hcolarr, hcolbit, hcolread, htab⟩, hklist, hbarr⟩
  exact ⟨σ', _, hrun, hK, hpre'.1.1, hpre'.1.2.1, hpre'.1.2.2.1, hpre'.1.2.2.2.2.2,
    hout, hc, fun i hi σs hσs => by simpa using hval i hi σs hσs⟩

/-! ### §7 Axioms -/

/-- info: 'Lax3Proofs.Refine.ScatterDeadTurn.scatDead_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms scatDead_spec

/-- info: 'Lax3Proofs.Refine.ScatterDeadTurn.scatterDeadStep' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms scatterDeadStep

end Lax3Proofs.Refine.ScatterDeadTurn
