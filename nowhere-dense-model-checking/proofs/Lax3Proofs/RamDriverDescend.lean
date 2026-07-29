import Lax3Proofs.RamDriverCluster

/-!
The passes of one cluster of `Lax3Proofs.RamDriver`, walked: the
padding, and the expansion the two chains of a cluster are built from.

This file is stage three of the driver. It carries the walks of
`RamDriver.enumBatch` and of `RamDriver.expandCom`/`chainCom` — the
first is a whole obligation of `Lax3Proofs.RamDriverCluster`, the second
is what the descent's ball and the colouring's three slot families are
each an instance of — together with the three transport lemmas a pass
needs to hand a depth's state on.

# What is proved

* `enumBatch_spec`, the padding pass: the buffer ends holding exactly
  `mb` entries, every one a marked vertex and every marked vertex among
  them. Its content is a counting argument — `markedBelow` and
  `count_lt_of_mark` — that the collecting loop never overruns the
  buffer, and `PadInv` for the repetition that follows.
* `enumStepW`, that pass at the surface `RamDriverCluster.EnumStep`
  states it at, and `enumStep_of_maskWords`, which turns it into the
  obligation itself from one clause about the batch indicator.
* `expandSlot_step`, `expandStep_spec`, `expandCom_spec`: one step of
  neighbourhood expansion, the inner block scan against
  `Csr.rowScan_spec` with `RamDriverCluster.ScanHit`, the outer pass
  against `Spec.forRangeZero` with `RamDriverCluster.ExpandInv`, and
  `RamDriverCluster.hit_eq_expandVal` at the join.
* `chainCom_spec`, the chain of `r` of them: the last name of the
  family marks the `r`-neighbourhood of what the first one marked. The
  induction peels the chain from the *front*, which is what the syntax
  of `RamDriver.foldRange` gives (`chainCom_succ`), so the radius
  arithmetic it needs is `ballOf_nbhd` and not
  `RamDriverCluster.nbhd_ballOf`. The family of names is a parameter:
  the ball's chain alternates between two names
  (`RamDriver.ballStage`) and the colour chains run through distinct
  ones, and both are instances.
* `levelPre_congr`, `coverHeld_congr`, `batchData_congr`: the clauses of
  `RamDriverCluster.TurnPre` and the descent's data, carried across a
  pass off the frame rule's equations.

# What is *not* proved, and why

`RamDriverCluster.DescendStep`, `ColourStep` and `EnumStep` are **not
provable as stated**. Each of them is a `Spec` of the bounded semantics
whose precondition does not say enough about memory for the program
text to run at all — an out-of-range read has no value in IMP+ and a
read of a cell at or above the word bound has none either — and one of
them is short of a semantic invariant as well. Precisely:

1. **Indicator cells are not known to be words.** `BatchData` pins what
   `cluName j` and `batName j` *mark* (`markSet n Xa = X`) and says
   nothing about their cells, while `resName j`, `alvName (j+1)` and
   `gamName (j+1)` all carry `∀ k < n, · k < B`. `enumBatch`'s first
   read is `bat[z]`, so `EnumStep` fails on the missing clause alone.
   The repair is two conjuncts in `BatchData`; `MaskWords` below is the
   same statement in the form that crosses a run
   (`RamDriver.run_mem_arrs_lt`), and `enumStep_of_maskWords` is the
   obligation modulo it. The colour arrays of `LevelPre` are missing
   the same clause — `oldCom` multiplies `colName j c` by `cluName j` —
   and so is the ordering `ord` of `RamDriverCluster.CoverHeld`, whose
   cell `descendCom` reads into the connector on its first line:
   `RamCover.CoverOut` bounds `xmem` (`mem_lt`) and `asg` (`asg_lt`)
   and says nothing about `ord`, which `OrdersBy` — not carried by
   `CoverHeld` — is what would.
2. **The per-cluster arrays are not known to exist.** Nothing in
   `LevelPre`, `LevelMem` or `TurnPre` says that `cluName j`,
   `resName j`, `balName j`, `balAltName j`, `batName j`,
   `alvName (j+1)`, `gamName (j+1)` or the depth-`(j+1)` colour arrays
   `colName (j+1) c` are present at the carrier's length, and every one
   of them is *stored into* by `descendCom` or `colourCom`. A level's
   memory clause has to name them, exactly as `LevelMem` names the
   fixed scratch of the sub-programs; the colour family is the one that
   grows with the depth (`c < sigL cap mb (j+1)`).
3. **The recorded play is not in the state.** `descendCom`'s batch
   phase searches, for every earlier round `a < j`, from `ctrName a` in
   the game mask `gamName a` — arrays and scalars of *earlier* depths,
   which `TurnPre` does not mention at all, so for `j ≥ 1` the copy
   `copyCom (gamName a) "alv"` has no derivation. Worse, `PlayOk`'s
   rounds are existentially quantified, so even with the arrays present
   nothing connects `ctrName a`/`gamName a` to the play the hypothesis
   produces, and `batchO Or rounds P v ⊆ W` — what
   `RamDriver.playOk_succ` needs of the batch — cannot be derived. The
   repair is an invariant that records the play in the state (the
   connectors, the game masks, and that they are the rounds of the
   `ReachedO` witness), carried by `LevelPre` and descended by the turn.
4. **An unreachable ancestor is stuck.** `RamBfsPaths.bfsPath_spec` is
   conditional on `WithinDist (masked G M) (2·cap) s t`, and
   `SplitterWinOracle.genSetO` asks for the oracle's path from *every*
   earlier connector, reachable or not. In the bounded semantics
   `extractPathCom` then walks back `dist[t] + 1 > 2·cap + 1` cells and
   stores outside the buffer, which has no derivation — the machine's
   flat memory tolerates this and IMP+ does not. Either the program
   needs a guard (`if dist[tv] ≤ 2·cap then …`) or the batch phase
   needs the reachability of every ancestor as an invariant.
5. **`mb < B` is nowhere.** `enumBatch`'s second loop tests against the
   literal `mb`, which the bounded semantics evaluates only below the
   word bound, and `RamDriver.WordBound` bounds `n * n + ns + 2·cap + 2`
   and not `mb`. It is a hypothesis of `enumStepW` here; it belongs in
   `WordBound`.

None of the five is a defect of the *algorithm*: each is a clause a
precondition owes, and (3) and (4) are invariants the descent has to
carry. They are recorded here rather than repaired because the
obligation surfaces live in `Lax3Proofs.RamDriver` and
`Lax3Proofs.RamDriverCluster`.
-/

namespace Lax3Proofs.RamDriverDescend

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax3Proofs.Horizon Lax3Proofs.SyntaxLemmas Lax3Proofs.WalkDistance
open Lax3Proofs.FormulaTables Lax3Proofs.SplitterWin Lax3Proofs.SplitterWinOracle
open Lax3Proofs.RamBfs (masked masked_adj CsrGraph MAdj WD)
open Lax3Proofs.RamDriver Lax3Proofs.RamDriverCluster
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {n : ℕ}

/-! ### Reading a mask cell

A pass that reads a mask reads a *cell of a list*, and the bounded
semantics asks two things of such a read: that the index is inside the
list, and that the value it finds is a word. The first is the array's
length and the second is a clause about its contents — `MaskWords`
below — which no equation of the form `σ.arrs a = arrOf n Wa` implies
and which every pass that reads an indicator therefore has to be
handed. -/

/-- Every cell of the array named `a` is a word. Stated on the list, so
that `RamDriver.run_mem_arrs_lt` carries it across any run. -/
def MaskWords (B : ℕ) (a : String) (σ : Env) : Prop := ∀ v ∈ σ.arrs a, v < B

/-- A cell of an `arrOf` array is one of its members. -/
theorem mem_arrOf {N : ℕ} (f : ℕ → ℕ) {k : ℕ} (hk : k < N) : f k ∈ arrOf N f :=
  List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

/-- The word clause, read at a cell. -/
theorem MaskWords.get {B N : ℕ} {a : String} {σ : Env} {f : ℕ → ℕ} (h : MaskWords B a σ)
    (harr : σ.arrs a = arrOf N f) {k : ℕ} (hk : k < N) : f k < B :=
  h _ (by rw [harr]; exact mem_arrOf f hk)

/-- The clause survives any run. -/
theorem MaskWords.run {B : ℕ} {a : String} {c : Com} {σ σ' : Env} {K : ℕ}
    (h : MaskWords B a σ) (hr : Run B c σ σ' K) : MaskWords B a σ' :=
  run_mem_arrs_lt hr a h

/-! ### Carrying a depth's state across a pass

A pass of the driver writes a handful of arrays and a handful of
scalars, and everything else a depth is holding has to come back. The
frame rule reads off the syntax *which* names are safe; what it does
not do is put the depth's clauses back together out of them, and these
three lemmas are that — one per clause of `RamDriverCluster.TurnPre`
and one for the descent's own data. Each asks exactly for the names its
clause mentions, so a pass discharges it with one frame equation per
line and nothing is decided twice.

The memory clauses (`RamDriver.LevelMem`, the `Sized` list of
`RamDriver.OrderMem`) are not framed at all: a run cannot change the
length of an array, so they cross any pass by `RamDriver.Sized.run`. -/

section Frames

variable {B n cap mb ns Ws j K : ℕ} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
  {σ σ' : Env} {c : Com}

/-- **The engines' scratch, across a pass.** Only the eight zeroed
accumulators have to be named: the lengths cross by themselves. -/
theorem orderMem_congr (h : OrderMem n ns Ws σ) (hr : Run B c σ σ' K)
    (hz : ∀ a ∈ (["elm", "bh", "ooff", "noff", "stf", "sta", "std", "ste"] : List String),
      σ'.arrs a = σ.arrs a) : OrderMem n ns Ws σ' :=
  ⟨h.1, h.2.1.run hr, by rw [hz "elm" (by simp)]; exact h.2.2.1,
    by rw [hz "bh" (by simp)]; exact h.2.2.2.1,
    by rw [hz "ooff" (by simp)]; exact h.2.2.2.2.1,
    by rw [hz "noff" (by simp)]; exact h.2.2.2.2.2.1,
    by rw [hz "stf" (by simp)]; exact h.2.2.2.2.2.2.1,
    by rw [hz "sta" (by simp)]; exact h.2.2.2.2.2.2.2.1,
    by rw [hz "std" (by simp)]; exact h.2.2.2.2.2.2.2.2.1,
    by rw [hz "ste" (by simp)]; exact h.2.2.2.2.2.2.2.2.2⟩

/-- **The depth's state, across a pass.** -/
theorem levelPre_congr (h : LevelPre B n cap mb ns Ws O T j M Gm C σ) (hr : Run B c σ σ' K)
    (hn : σ'.vars "n" = σ.vars "n") (hm : σ'.vars "m" = σ.vars "m")
    (hoff : σ'.arrs "off" = σ.arrs "off") (htgt : σ'.arrs "tgt" = σ.arrs "tgt")
    (halv : σ'.arrs (alvName j) = σ.arrs (alvName j))
    (hgam : σ'.arrs (gamName j) = σ.arrs (gamName j))
    (hcol : ∀ c' < sigL cap mb j, σ'.arrs (colName j c') = σ.arrs (colName j c'))
    (hz : ∀ a ∈ (["elm", "bh", "ooff", "noff", "stf", "sta", "std", "ste"] : List String),
      σ'.arrs a = σ.arrs a) :
    LevelPre B n cap mb ns Ws O T j M Gm C σ' :=
  ⟨by rw [hn]; exact h.1, by rw [hoff]; exact h.2.1, by rw [htgt]; exact h.2.2.1,
    by rw [halv]; exact h.2.2.2.1, by rw [hgam]; exact h.2.2.2.2.1,
    fun c' hc' => by rw [hcol c' hc']; exact h.2.2.2.2.2.1 c' hc',
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, levelMem_run hr h.2.2.2.2.2.2.2.2.1,
    by rw [hm]; exact h.2.2.2.2.2.2.2.2.2.1,
    orderMem_congr h.2.2.2.2.2.2.2.2.2.2 hr hz⟩

variable {G : SimpleGraph (Fin n)} {π : Equiv.Perm (Fin n)} {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ}

/-- **The cover's three answers, across a pass.** -/
theorem coverHeld_congr (h : CoverHeld n G M π ord cap Xoff Xmem asg m σ)
    (hord : σ'.arrs "ord" = σ.arrs "ord") (hxoff : σ'.arrs "xoff" = σ.arrs "xoff")
    (hxmem : σ'.arrs "xmem" = σ.arrs "xmem") (hasg : σ'.arrs "asg" = σ.arrs "asg")
    (hxp : σ'.vars "xp" = σ.vars "xp") : CoverHeld n G M π ord cap Xoff Xmem asg m σ' :=
  ⟨by rw [hord]; exact h.1, by rw [hxoff]; exact h.2.1, by rw [hxmem]; exact h.2.2.1,
    by rw [hasg]; exact h.2.2.2.1, by rw [hxp]; exact h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2⟩

variable {X W : Set (Fin n)} {Alv' Gam' : ℕ → ℕ}

/-- **The descent's data, across a pass.** -/
theorem batchData_congr (h : BatchData n j B G M X W Alv' Gam' σ)
    (hclu : σ'.arrs (cluName j) = σ.arrs (cluName j))
    (hbat : σ'.arrs (batName j) = σ.arrs (batName j))
    (hres : σ'.arrs (resName j) = σ.arrs (resName j))
    (halv : σ'.arrs (alvName (j + 1)) = σ.arrs (alvName (j + 1)))
    (hgam : σ'.arrs (gamName (j + 1)) = σ.arrs (gamName (j + 1))) :
    BatchData n j B G M X W Alv' Gam' σ' := by
  obtain ⟨⟨Xa, hXa, hXs⟩, ⟨Wa, hWa, hWs⟩, ⟨Ra, hRa, hRm, hRB⟩, hA, hAB, hAm, hGa, hGB⟩ := h
  exact ⟨⟨Xa, by rw [hclu]; exact hXa, hXs⟩, ⟨Wa, by rw [hbat]; exact hWa, hWs⟩,
    ⟨Ra, by rw [hres]; exact hRa, hRm, hRB⟩, by rw [halv]; exact hA, hAB, hAm,
    by rw [hgam]; exact hGa, hGB⟩

end Frames

/-! ### The batch, enumerated

`RamDriver.enumBatch` is two loops over one buffer: the first collects
the marked vertices in vertex order, the second repeats the first entry
to the fixed width `mb`. What the first loop owes is that its counter
never leaves the buffer, and that is a *counting* statement — the
entries written so far are distinct marked vertices, so there are at
most `mb` of them. `markedBelow` is the set they are, and the three
lemmas below are its arithmetic. -/

section Enum

/-- The marked vertices below a position. -/
def markedBelow (n : ℕ) (Wa : ℕ → ℕ) (z : ℕ) : Set (Fin n) :=
  {v : Fin n | (v : ℕ) < z ∧ Wa (v : ℕ) ≠ 0}

/-- What is marked below a position is marked. -/
theorem markedBelow_subset (n : ℕ) (Wa : ℕ → ℕ) (z : ℕ) :
    markedBelow n Wa z ⊆ markSet n Wa := fun _ hv => hv.2

/-- Nothing is below zero. -/
theorem ncard_markedBelow_zero (n : ℕ) (Wa : ℕ → ℕ) : (markedBelow n Wa 0).ncard = 0 := by
  have h : markedBelow n Wa 0 = ∅ := by
    ext v
    simp only [markedBelow, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    omega
  rw [h, Set.ncard_empty]

/-- Passing a marked vertex adds one. -/
theorem ncard_markedBelow_succ_of_mark {n : ℕ} {Wa : ℕ → ℕ} {z : ℕ} (hz : z < n)
    (h : Wa z ≠ 0) :
    (markedBelow n Wa (z + 1)).ncard = (markedBelow n Wa z).ncard + 1 := by
  have hins : markedBelow n Wa (z + 1) = insert (⟨z, hz⟩ : Fin n) (markedBelow n Wa z) := by
    ext v
    simp only [markedBelow, Set.mem_setOf_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨hv, hw⟩
      rcases Nat.lt_or_ge (v : ℕ) z with h' | h'
      · exact Or.inr ⟨h', hw⟩
      · exact Or.inl (Fin.ext (show (v : ℕ) = z by omega))
    · rintro (rfl | ⟨hv, hw⟩)
      · exact ⟨Nat.lt_succ_self z, h⟩
      · exact ⟨by omega, hw⟩
  rw [hins, Set.ncard_insert_of_notMem (by simp [markedBelow])]

/-- Passing an unmarked vertex adds nothing. -/
theorem markedBelow_succ_of_unmarked {n : ℕ} {Wa : ℕ → ℕ} {z : ℕ} (h : Wa z = 0) :
    markedBelow n Wa (z + 1) = markedBelow n Wa z := by
  ext v
  simp only [markedBelow, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hv, hw⟩
    have hne : (v : ℕ) ≠ z := fun hc => hw (by rw [hc, h])
    exact ⟨by omega, hw⟩
  · rintro ⟨hv, hw⟩
    exact ⟨by omega, hw⟩

/-- **The buffer is never overrun.** At a marked vertex the entries
written so far, together with the vertex itself, are distinct marked
vertices, so there are at most `mb` of them and the counter is inside
the buffer. -/
theorem count_lt_of_mark {n mb : ℕ} {Wa : ℕ → ℕ} {z b : ℕ} (hz : z < n) (h : Wa z ≠ 0)
    (hb : b ≤ (markedBelow n Wa z).ncard) (hcard : (markSet n Wa).ncard ≤ mb) : b < mb := by
  have hsub : insert (⟨z, hz⟩ : Fin n) (markedBelow n Wa z) ⊆ markSet n Wa := by
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv'
    · exact h
    · exact hv'.2
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem (by simp [markedBelow])] at hle
  omega

/-- What the collecting loop has done by the position `z`: the buffer's
first `bc` cells are distinct marked vertices below `z`, and every
marked vertex below `z` is one of them. -/
def CollectAt (n mb : ℕ) (Wa : ℕ → ℕ) (bat : String) (z : ℕ) (σ : Env) : Prop :=
  σ.arrs bat = arrOf n Wa ∧ σ.vars "bc" ≤ (markedBelow n Wa z).ncard ∧
    ∃ E : ℕ → ℕ, σ.arrs "wa" = arrOf mb E ∧
      (∀ i, i < σ.vars "bc" → E i < z ∧ Wa (E i) ≠ 0) ∧
      (∀ v, v < z → Wa v ≠ 0 → ∃ i, i < σ.vars "bc" ∧ E i = v)

/-- The invariant of the collecting loop: its own counter, and what it
has done by where the counter stands. -/
def CollectInv (n mb : ℕ) (Wa : ℕ → ℕ) (bat : String) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "z" ≤ n ∧ CollectAt n mb Wa bat (σ.vars "z") σ

/-- **One turn of the collecting loop.** A marked vertex is appended to
the buffer and the counter moves on; an unmarked one is passed over. -/
theorem collectBody_spec (B n mb : ℕ) (Wa : ℕ → ℕ) (bat : String) (hbat : bat ≠ "wa")
    (hB : 1 < B) (hnB : n < B) (hmbB : mb < B) (hcard : (markSet n Wa).ncard ≤ mb)
    (hWB : ∀ k, k < n → Wa k < B) :
    Spec B (fun σ => CollectInv n mb Wa bat σ ∧ σ.vars "z" < n)
      (.seq (.ite (.lt (.lit 0) (.get bat (.var "z")))
              (.seq (.store "wa" (.var "bc") (.var "z"))
                (.assign "bc" (.add (.var "bc") (.lit 1))))
              .skip)
        (.assign "z" (.add (.var "z") (.lit 1))))
      (fun σ σ' => CollectInv n mb Wa bat σ' ∧ σ'.vars "z" = σ.vars "z" + 1) 16 := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨⟨hn, hzn, hbatσ, hbc, E, hwa, hlt, hcov⟩, hz⟩ := hσ
  have hzB : σ.vars "z" < B := by omega
  have hbcmb : σ.vars "bc" ≤ mb :=
    le_trans hbc (le_trans (Set.ncard_le_ncard (markedBelow_subset n Wa _) (Set.toFinite _)) hcard)
  have hWaB : Wa (σ.vars "z") < B := hWB _ hz
  have hcond : (Cond.lt (.lit 0) (.get bat (.var "z"))).evalB B σ =
      some (decide (0 < Wa (σ.vars "z"))) :=
    evalB_condLt (evalB_lit (by omega))
      (evalB_get (evalB_var hzB) (by rw [hbatσ, getElem?_arrOf Wa hz]) hWaB)
  by_cases hm : Wa (σ.vars "z") = 0
  · -- an unmarked vertex: the buffer is untouched
    have hz' : (σ.setVar "z" (σ.vars "z" + 1)).vars "z" = σ.vars "z" + 1 := by simp
    have hbc' : (σ.setVar "z" (σ.vars "z" + 1)).vars "bc" = σ.vars "bc" := by simp
    refine ⟨σ.setVar "z" (σ.vars "z" + 1), 10, ?_, by omega,
      ⟨by simpa using hn, by rw [hz']; omega, by simpa using hbatσ, ?_, E,
        by simpa using hwa, ?_, ?_⟩, hz'⟩
    · exact (Run.ite_false (by rw [hcond, hm]; simp) Run.skip).seq
        (Run.assign (evalB_bin (evalB_var hzB) (evalB_lit (by omega)) (by simp; omega)))
    · rw [hbc', hz', markedBelow_succ_of_unmarked hm]
      exact hbc
    · intro i hi
      rw [hbc'] at hi
      rw [hz']
      exact ⟨by have := (hlt i hi).1; omega, (hlt i hi).2⟩
    · intro v hv hwv
      rw [hz'] at hv
      rw [hbc']
      have hvz : v < σ.vars "z" := by
        rcases Nat.lt_or_ge v (σ.vars "z") with h' | h'
        · exact h'
        · exact absurd hwv (by rw [show v = σ.vars "z" by omega, hm]; simp)
      exact hcov v hvz hwv
  · -- a marked vertex: it is appended
    have hbclt : σ.vars "bc" < mb := count_lt_of_mark hz hm hbc hcard
    have hwalen : σ.vars "bc" < (σ.arrs "wa").length := by rw [hwa, length_arrOf]; exact hbclt
    set τ := ((σ.setArr "wa" (σ.vars "bc") (σ.vars "z")).setVar "bc"
      (σ.vars "bc" + 1)).setVar "z" (σ.vars "z" + 1) with hτ
    have hz' : τ.vars "z" = σ.vars "z" + 1 := by rw [hτ]; simp
    have hbc' : τ.vars "bc" = σ.vars "bc" + 1 := by rw [hτ]; simp
    have hn' : τ.vars "n" = σ.vars "n" := by rw [hτ]; simp
    have hwa' : τ.arrs "wa" = arrOf mb (upd E (σ.vars "bc") (σ.vars "z")) := by
      rw [hτ]
      simp [hwa, set_arrOf_eq_upd]
    have hbat' : τ.arrs bat = arrOf n Wa := by
      rw [hτ]
      simp only [arrs_setVar, arrs_setArr, if_neg hbat]
      exact hbatσ
    refine ⟨τ, 16, ?_, le_rfl,
      ⟨by rw [hn']; exact hn, by rw [hz']; omega, hbat', ?_,
        upd E (σ.vars "bc") (σ.vars "z"), hwa', ?_, ?_⟩, hz'⟩
    · refine (Run.ite_true (by rw [hcond]; simp; omega)
        ((Run.store (evalB_var (by omega)) (evalB_var hzB) hwalen).seq
          (Run.assign (evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega))
            (by simp; omega))))).seq
        (Run.assign (evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega))
          (by simp; omega))) |>.mono (by simp)
    · rw [hbc', hz', ncard_markedBelow_succ_of_mark hz hm]
      omega
    · intro i hi
      rw [hbc'] at hi
      rw [hz']
      by_cases hie : i = σ.vars "bc"
      · subst hie
        exact ⟨by rw [upd_self]; omega, by rw [upd_self]; exact hm⟩
      · rw [upd_of_ne _ hie]
        exact ⟨by have := (hlt i (by omega)).1; omega, (hlt i (by omega)).2⟩
    · intro v hv hwv
      rw [hz'] at hv
      rw [hbc']
      by_cases hve : v = σ.vars "z"
      · exact ⟨σ.vars "bc", by omega, by rw [upd_self, hve]⟩
      · obtain ⟨i, hi, hEi⟩ := hcov v (by omega) hwv
        exact ⟨i, by omega, by rw [upd_of_ne _ (by omega), hEi]⟩

/-- What the padding loop carries: every cell below the counter is a
marked vertex, the collected enumeration is still in the first `bc`
cells, and the first cell — the one being repeated — is unchanged. -/
def PadInv (n mb : ℕ) (Wa : ℕ → ℕ) (bc v0 : ℕ) (σ : Env) : Prop :=
  bc ≤ σ.vars "k" ∧ σ.vars "k" ≤ mb ∧
    ∃ E : ℕ → ℕ, σ.arrs "wa" = arrOf mb E ∧ E 0 = v0 ∧
      (∀ i, i < σ.vars "k" → E i < n ∧ Wa (E i) ≠ 0) ∧
      (∀ v, v < n → Wa v ≠ 0 → ∃ i, i < bc ∧ E i = v)

/-- **One turn of the padding loop**: the first entry is copied into the
cell the counter names. -/
theorem padBody_spec (B n mb : ℕ) (Wa : ℕ → ℕ) (bc v0 : ℕ) (hB : 1 < B) (hnB : n < B)
    (hmbB : mb < B) (hbcpos : 1 ≤ bc) :
    Spec B (fun σ => PadInv n mb Wa bc v0 σ ∧
        (Cond.lt (.var "k") (.lit mb)).evalB B σ = some true)
      (.seq (.store "wa" (.var "k") (.get "wa" (.lit 0)))
        (.assign "k" (.add (.var "k") (.lit 1))))
      (fun σ σ' => PadInv n mb Wa bc v0 σ' ∧ mb - σ'.vars "k" < mb - σ.vars "k") 8 := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨⟨hkbc, hkmb, E, hwa, hE0, hlt, hcov⟩, hcond⟩ := hσ
  have hkB : σ.vars "k" < B := by omega
  have hk : σ.vars "k" < mb := by
    rw [evalB_condLt (evalB_var hkB) (evalB_lit hmbB)] at hcond
    simpa using hcond
  have hE0n : E 0 < n := (hlt 0 (by omega)).1
  have hE0B : E 0 < B := by omega
  have hget : (Expr.get "wa" (.lit 0)).evalB B σ = some (E 0) :=
    evalB_get (evalB_lit (by omega)) (by rw [hwa, getElem?_arrOf E (by omega)]) hE0B
  have hwalen : σ.vars "k" < (σ.arrs "wa").length := by rw [hwa, length_arrOf]; exact hk
  set τ := (σ.setArr "wa" (σ.vars "k") (E 0)).setVar "k" (σ.vars "k" + 1) with hτ
  have hk' : τ.vars "k" = σ.vars "k" + 1 := by rw [hτ]; simp
  have hwa' : τ.arrs "wa" = arrOf mb (upd E (σ.vars "k") (E 0)) := by
    rw [hτ]; simp [hwa, set_arrOf_eq_upd]
  refine ⟨τ, 8, ((Run.store (evalB_var hkB) hget hwalen).seq
      (Run.assign (evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega))
        (by simp; omega)))).mono (by simp), le_rfl,
    ⟨by rw [hk']; omega, by rw [hk']; omega, upd E (σ.vars "k") (E 0), hwa', ?_, ?_, ?_⟩,
    by rw [hk']; omega⟩
  · rw [upd_of_ne _ (by omega), hE0]
  · intro i hi
    rw [hk'] at hi
    by_cases hie : i = σ.vars "k"
    · subst hie
      rw [upd_self]
      exact ⟨hE0n, (hlt 0 (by omega)).2⟩
    · rw [upd_of_ne _ hie]
      exact hlt i (by omega)
  · intro v hv hwv
    obtain ⟨i, hi, hEi⟩ := hcov v hv hwv
    exact ⟨i, hi, by rw [upd_of_ne _ (by omega), hEi]⟩

/-- **The padding pass.** `RamDriver.enumBatch` leaves in `wa` exactly
`mb` entries, every one of them a marked vertex, and every marked vertex
among them. -/
theorem enumBatch_spec (B n mb : ℕ) (Wa : ℕ → ℕ) (bat : String) (hbat : bat ≠ "wa")
    (hB : 1 < B) (hnB : n < B) (hmbB : mb < B) (hcard : (markSet n Wa).ncard ≤ mb)
    (hne : (markSet n Wa).Nonempty) (hWB : ∀ k, k < n → Wa k < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs bat = arrOf n Wa ∧ (∃ g, σ.arrs "wa" = arrOf mb g))
      (enumBatch bat mb)
      (fun _ σ' => ∃ E : ℕ → ℕ, σ'.arrs "wa" = arrOf mb E ∧
        (∀ i, i < mb → E i < n ∧ Wa (E i) ≠ 0) ∧
        (∀ v, v < n → Wa v ≠ 0 → ∃ i, i < mb ∧ E i = v))
      (20 * n + 12 * mb + 30) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hbatσ, gwa, hwa⟩ := hσ
  -- the two counters, zeroed
  have hr₁ : Run B (.assign "bc" (.lit 0)) σ (σ.setVar "bc" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hr₂ : Run B (.assign "z" (.lit 0)) (σ.setVar "bc" 0)
      ((σ.setVar "bc" 0).setVar "z" 0) 2 := (Run.assign (evalB_lit (by omega))).mono (by simp)
  set σ₂ := (σ.setVar "bc" 0).setVar "z" 0 with hσ₂
  have hz₂ : σ₂.vars "z" = 0 := by rw [hσ₂]; simp
  have hbc₂ : σ₂.vars "bc" = 0 := by rw [hσ₂]; simp
  have hI₂ : CollectInv n mb Wa bat σ₂ := by
    refine ⟨by rw [hσ₂]; simpa using hn, by rw [hz₂]; omega,
      by rw [hσ₂]; simpa using hbatσ, ?_, gwa, by rw [hσ₂]; simpa using hwa, ?_, ?_⟩
    · rw [hbc₂, hz₂, ncard_markedBelow_zero]
    · intro i hi; rw [hbc₂] at hi; omega
    · intro v hv hwv; rw [hz₂] at hv; omega
  -- the collecting loop
  obtain ⟨σ₃, hr₃, hI₃, hz₃⟩ :=
    (Spec.forRange (B := B) (P := CollectInv n mb Wa bat) "z" "n"
      (CollectInv n mb Wa bat) n 16 (20 * n + 4)
      (fun τ hτ => by have := hτ.2.1; omega) (fun τ hτ => by rw [hτ.1]; exact hnB)
      (fun τ hτ => hτ.1) (fun τ hτ => hτ.2.1)
      (collectBody_spec B n mb Wa bat hbat hB hnB hmbB hcard hWB) (fun _ hτ => hτ)
      (fun τ _ => by
        have : (16 + 4) * (n - τ.vars "z") ≤ 20 * n := by
          have := Nat.mul_le_mul_left 20 (Nat.sub_le n (τ.vars "z"))
          omega
        omega)).run hI₂
  obtain ⟨hn₃, -, hbat₃, hbc₃, E₃, hwa₃, hlt₃, hcov₃⟩ := hI₃
  rw [hz₃] at hbc₃ hlt₃ hcov₃
  -- the batch is not empty, so the buffer's first cell is a batch vertex
  obtain ⟨v, hv⟩ := hne
  obtain ⟨i₀, hi₀, -⟩ := hcov₃ (v : ℕ) v.isLt hv
  have hbcpos : 1 ≤ σ₃.vars "bc" := by omega
  have hbcmb : σ₃.vars "bc" ≤ mb :=
    le_trans hbc₃ (le_trans (Set.ncard_le_ncard (markedBelow_subset n Wa n) (Set.toFinite _)) hcard)
  -- k := bc
  have hr₄ : Run B (.assign "k" (.var "bc")) σ₃ (σ₃.setVar "k" (σ₃.vars "bc")) 2 :=
    (Run.assign (evalB_var (by omega))).mono (by simp)
  set σ₄ := σ₃.setVar "k" (σ₃.vars "bc") with hσ₄
  have hk₄ : σ₄.vars "k" = σ₃.vars "bc" := by rw [hσ₄]; simp
  have hI₄ : PadInv n mb Wa (σ₃.vars "bc") (E₃ 0) σ₄ := by
    refine ⟨by rw [hk₄], by rw [hk₄]; exact hbcmb, E₃, by rw [hσ₄]; simpa using hwa₃, rfl, ?_, ?_⟩
    · intro i hi
      rw [hk₄] at hi
      exact hlt₃ i hi
    · exact hcov₃
  -- the padding loop
  obtain ⟨σ₅, hr₅, hI₅, hfalse⟩ :=
    (Spec.while_count (B := B) (P := PadInv n mb Wa (σ₃.vars "bc") (E₃ 0)) (K := 12 * mb + 4)
      (PadInv n mb Wa (σ₃.vars "bc") (E₃ 0)) (fun τ => mb - τ.vars "k") 8
      (fun τ hτ => evalB_condLt_var_lit (by have := hτ.2.1; omega) hmbB)
      (padBody_spec B n mb Wa (σ₃.vars "bc") (E₃ 0) hB hnB hmbB hbcpos) (fun _ hτ => hτ)
      (fun τ _ => by
        have : (1 + 3 + 8) * (mb - τ.vars "k") ≤ 12 * mb := by
          have := Nat.mul_le_mul_left 12 (Nat.sub_le mb (τ.vars "k"))
          omega
        simp only [size_condLt, size_var, size_lit]
        omega)).run hI₄
  obtain ⟨-, hkmb₅, E₅, hwa₅, -, hlt₅, hcov₅⟩ := hI₅
  have hk₅ : σ₅.vars "k" = mb := by
    have hkB : σ₅.vars "k" < B := by omega
    rw [evalB_condLt (evalB_var hkB) (evalB_lit hmbB)] at hfalse
    simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hfalse
    omega
  rw [hk₅] at hlt₅
  exact ⟨σ₅, _, hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq hr₅))), by omega,
    E₅, hwa₅, hlt₅, fun v hv hwv => by
      obtain ⟨i, hi, hEi⟩ := hcov₅ v hv hwv
      exact ⟨i, by omega, hEi⟩⟩

/-! ### The obligation

`RamDriverCluster.EnumStep` is the padding pass at the surface the
cluster step consumes it at. Its precondition is missing one clause —
that the batch indicator holds *words* — without which the pass's very
first read, `bat[z]`, has no value in the bounded semantics and the
`Spec` is not provable at all: `RamDriverCluster.BatchData` pins what
the array marks (`markSet n Wa = W`) and never what its cells are. The
clause is `MaskWords B (batName j)`, it is what the descent that writes
the array leaves behind, and it survives every pass by
`MaskWords.run`; `EnumStepW` is the obligation with it, and
`enumStep_of_maskWords` turns the one into the other. -/

/-- `RamDriverCluster.EnumStep`, with the word clause its precondition
owes. -/
def EnumStepW (B cap mb ns Ws j : ℕ) (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (m : ℕ)
    (X W : Set (Fin n)) (Alv' Gam' : ℕ → ℕ) (K : ℕ) : Prop :=
  Spec B (fun σ => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ ∧
      BatchData n j B G M X W Alv' Gam' σ ∧
      W.Nonempty ∧ W.ncard ≤ mb ∧ (∃ g, σ.arrs "wa" = arrOf mb g) ∧
      MaskWords B (batName j) σ)
    (enumBatch (batName j) mb)
    (fun σ σ' => TurnPre B n cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m σ' ∧
      σ'.out = σ.out ∧ σ'.vars "c" = σ.vars "c" ∧
      ∃ w : Fin mb → Fin n, ClusterData n mb j B G M X W w Alv' Gam' σ') K

/-! The three frame readings of the pass, on its syntax. -/

theorem not_mem_wvars_enumBatch {bat y : String} {mb : ℕ} (h1 : y ≠ "bc") (h2 : y ≠ "z")
    (h3 : y ≠ "k") : y ∉ (enumBatch bat mb).wvars := by
  simp [enumBatch, Com.wvars, h1, h2, h3]

theorem not_mem_warrs_enumBatch {bat a : String} {mb : ℕ} (h : a ≠ "wa") :
    a ∉ (enumBatch bat mb).warrs := by simp [enumBatch, Com.warrs, h]

theorem noWrite_enumBatch (bat : String) (mb : ℕ) : (enumBatch bat mb).NoWrite := by
  simp [enumBatch, Com.NoWrite]

/-- **The padding, discharged.** -/
theorem enumStepW {B cap mb ns Ws j K : ℕ} {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)} {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ}
    {X W : Set (Fin n)} {Alv' Gam' : ℕ → ℕ}
    (hB : WordBound B n ns cap) (hmbB : mb < B) (hK : 20 * n + 12 * mb + 30 ≤ K) :
    EnumStepW B cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m X W Alv' Gam' K := by
  intro σ hσ
  obtain ⟨⟨hlev, hheld⟩, hbat, hne, hcard, ⟨gwa, hwa⟩, hmw⟩ := hσ
  obtain ⟨Wa, hWaarr, hWs⟩ := hbat.2.1
  have hbatwa : batName j ≠ "wa" := by simp [batName, String.ext_iff]
  obtain ⟨σ', hr, ⟨E, hwa', hltE, hcovE⟩, hfv, hfa, -, hout⟩ :=
    ((enumBatch_spec B n mb Wa (batName j) hbatwa hB.one_lt hB.n_lt hmbB
      (by rw [hWs]; exact hcard) (by rw [hWs]; exact hne)
      (fun k hk => hmw.get hWaarr hk)).frame).run ⟨hlev.1, hWaarr, gwa, hwa⟩
  have hav : ∀ a : String, a ≠ "wa" → σ'.arrs a = σ.arrs a :=
    fun a ha => hfa a (not_mem_warrs_enumBatch ha)
  have hvv : ∀ y : String, y ≠ "bc" → y ≠ "z" → y ≠ "k" → σ'.vars y = σ.vars y :=
    fun y h1 h2 h3 => hfv y (not_mem_wvars_enumBatch h1 h2 h3)
  -- the enumeration the buffer holds
  refine ⟨σ', hr.mono (by omega), ⟨levelPre_congr hlev hr (hvv "n" (by decide) (by decide)
      (by decide)) (hvv "m" (by decide) (by decide) (by decide)) (hav "off" (by decide))
      (hav "tgt" (by decide)) (hav _ (by simp [alvName, String.ext_iff]))
      (hav _ (by simp [gamName, String.ext_iff]))
      (fun c' _ => hav _ (by simp [colName, String.ext_iff]))
      (fun a ha => hav a (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)),
    coverHeld_congr hheld (hav "ord" (by decide)) (hav "xoff" (by decide))
      (hav "xmem" (by decide)) (hav "asg" (by decide))
      (hvv "xp" (by decide) (by decide) (by decide))⟩,
    hout (noWrite_enumBatch _ _), hvv "c" (by decide) (by decide) (by decide),
    fun i => ⟨E (i : ℕ), (hltE (i : ℕ) i.isLt).1⟩, ?_, ?_, ?_⟩
  · exact batchData_congr hbat (hav _ (by simp [cluName, String.ext_iff])) (hav _ hbatwa)
      (hav _ (by simp [resName, String.ext_iff])) (hav _ (by simp [alvName, String.ext_iff]))
      (hav _ (by simp [gamName, String.ext_iff]))
  · -- the range of the padded enumeration is the batch
    apply Set.eq_of_subset_of_subset
    · rintro v ⟨i, rfl⟩
      rw [← hWs]
      exact (hltE (i : ℕ) i.isLt).2
    · intro v hv
      rw [← hWs] at hv
      obtain ⟨i, hi, hEi⟩ := hcovE (v : ℕ) v.isLt hv
      exact ⟨⟨i, hi⟩, Fin.ext hEi⟩
  · rw [hwa']
    exact arrOf_congr (fun i hi => by rw [dif_pos hi])

/-- **The obligation itself**, from the walk and the one clause the
surface owes. The hypothesis is exactly the missing conjunct of
`RamDriverCluster.BatchData`, quantified over the states the obligation
speaks about; a `BatchData` carrying `∀ k < n, Wa k < B` discharges it
by `MaskWords` at the array it names, and nothing else in this file
changes. -/
theorem enumStep_of_maskWords {B cap mb ns Ws j K : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {ord Xoff Xmem asg : ℕ → ℕ} {m : ℕ} {X W : Set (Fin n)} {Alv' Gam' : ℕ → ℕ}
    (hB : WordBound B n ns cap) (hmbB : mb < B) (hK : 20 * n + 12 * mb + 30 ≤ K)
    (hmw : ∀ σ : Env, BatchData n j B G M X W Alv' Gam' σ → MaskWords B (batName j) σ) :
    EnumStep B cap mb ns Ws j G O T M Gm C π ord Xoff Xmem asg m X W Alv' Gam' K :=
  (enumStepW hB hmbB hK).pre (fun _ hσ => ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2,
    hmw _ hσ.2.1⟩)

end Enum

/-! ### One step of neighbourhood expansion, walked

`RamDriver.expandCom` is the pass both chains of a cluster are built
from — the ball of the round in the descent, the three slot families in
the colouring — and it is the one pass of the driver with a loop inside
a loop. `RamDriverCluster` carries its mathematics and both of its
invariants; what is walked here is the symbolic execution between them:
the inner scan against `Csr.rowScan_spec` with `ScanHit`, the outer pass
against `Spec.forRangeZero` with `ExpandInv`, and `hit_eq_expandVal` at
the join. -/

section Expand

variable {ns : ℕ} {G : SimpleGraph (Fin n)} {O T Msk Src : ℕ → ℕ} {msk src dst : String}

/-- **A dead vertex is not expanded into.** The step's conditional is
skipped there and the source's own cell stands, which is what
`expandVal` says of it: an arena edge needs both of its ends alive. -/
theorem expandVal_of_dead {z : ℕ} (h : Msk z = 0) : expandVal G Msk Src z = Src z := by
  classical
  unfold expandVal
  rw [if_neg]
  rintro ⟨y, hy, -⟩
  exact hy.alive_left h

/-- The block structure of a depth, as the reasoning kit's relation. -/
theorem csr_of_expandInv {σ : Env} (hcsr : CsrGraph G ns O T)
    (h : ExpandInv n ns G O T Msk Src msk src dst σ) :
    Csr "off" "tgt" n ns n O T σ :=
  ⟨h.2.2.1, h.2.2.2.1, fun i hi => hcsr.mono i hi, hcsr.last,
    fun p hp => hcsr.target_lt p hp⟩

/-- The pass's state does not see the three scalars the scan moves. -/
theorem expandInv_congr {σ σ' : Env} (h : ExpandInv n ns G O T Msk Src msk src dst σ)
    (hz : σ'.vars "z" = σ.vars "z") (hn : σ'.vars "n" = σ.vars "n")
    (ha : ∀ a : String, σ'.arrs a = σ.arrs a) :
    ExpandInv n ns G O T Msk Src msk src dst σ' :=
  ⟨h.1.of_eq (ha dst) hz, by rw [hn]; exact h.2.1, by rw [ha]; exact h.2.2.1,
    by rw [ha]; exact h.2.2.2.1, by rw [ha]; exact h.2.2.2.2.1, by rw [ha]; exact h.2.2.2.2.2⟩

/-- **One slot of the block.** The hit flag rises exactly when the slot
names a live marked vertex, which is the one turn `Csr.rowScan_spec`
asks for. -/
theorem expandSlot_step {B z : ℕ} (hcsr : CsrGraph G ns O T) (hB : 1 < B) (hnB : n < B)
    (hnsB : ns < B) (hMB : ∀ k, k < n → Msk k < B) (hSB : ∀ k, k < n → Src k < B)
    (hzn : z < n) (σ : Env) (hI : ScanHit n ns G O T Msk Src msk src dst z σ)
    (hj : σ.vars "j" < O (z + 1)) :
    ∃ σ' K', Run B (expandSlot msk src) σ σ' K' ∧
      ScanHit n ns G O T Msk Src msk src dst z σ' ∧ σ'.vars "j" = σ.vars "j" + 1 ∧ K' ≤ 20 := by
  classical
  obtain ⟨hinv, hzv, hjend, hjlo, -, hhit⟩ := hI
  have hcsrRel := csr_of_expandInv hcsr hinv
  have hjns : σ.vars "j" < ns := lt_of_lt_of_le hj (hcsrRel.row_le hzn)
  have hjB : σ.vars "j" < B := by omega
  have hTn : T (σ.vars "j") < n := hcsr.target_lt _ hjns
  have hslot : (Expr.get "tgt" (.var "j")).evalB B σ = some (T (σ.vars "j")) :=
    evalB_get (evalB_var hjB) (by rw [hinv.2.2.2.1, getElem?_arrOf T hjns]) (by omega)
  set τ := σ.setVar "w" (T (σ.vars "j")) with hτ
  have hrw : Run B (.assign "w" (.get "tgt" (.var "j"))) σ τ 3 :=
    (Run.assign hslot).mono (by simp)
  have hwv : τ.vars "w" = T (σ.vars "j") := by rw [hτ]; simp
  have hcmsk : (Cond.lt (.lit 0) (.get msk (.var "w"))).evalB B τ =
      some (decide (0 < Msk (T (σ.vars "j")))) :=
    evalB_condLt (evalB_lit (by omega))
      (evalB_get (evalB_var (by rw [hwv]; omega))
        (by rw [hτ, arrs_setVar, hinv.2.2.2.2.1, hwv, getElem?_arrOf Msk hTn]) (hMB _ hTn))
  have hcsrc : (Cond.lt (.lit 0) (.get src (.var "w"))).evalB B τ =
      some (decide (0 < Src (T (σ.vars "j")))) :=
    evalB_condLt (evalB_lit (by omega))
      (evalB_get (evalB_var (by rw [hwv]; omega))
        (by rw [hτ, arrs_setVar, hinv.2.2.2.2.2, hwv, getElem?_arrOf Src hTn]) (hSB _ hTn))
  -- the hit flag after the two tests, in either shape
  have hstepGen : ∀ (ρ : Env) (Kb : ℕ), Run B
        (.ite (.lt (.lit 0) (.get msk (.var "w")))
          (.ite (.lt (.lit 0) (.get src (.var "w"))) (.assign "hit" (.lit 1)) .skip) .skip) τ ρ Kb →
      ρ.vars "j" = σ.vars "j" → True := fun _ _ _ _ => trivial
  clear hstepGen
  by_cases hm : Msk (T (σ.vars "j")) = 0
  · -- a dead neighbour: nothing happens
    refine ⟨τ.setVar "j" (σ.vars "j" + 1), 20,
      (hrw.seq ((Run.ite_false (by rw [hcmsk, hm]; simp) Run.skip).seq
        (Run.assign (evalB_bin (evalB_var (by rw [hτ]; simp; omega)) (evalB_lit (by omega))
          (by simp [hτ]; omega))))).mono (by simp), ?_, by rw [hτ]; simp, le_rfl⟩
    refine ⟨expandInv_congr hinv (by rw [hτ]; simp) (by rw [hτ]; simp) (fun a => by rw [hτ]; simp),
      by rw [hτ]; simp [hzv], by rw [hτ]; simp [hjend], by rw [hτ]; simp; omega,
      by rw [hτ]; simp; omega, ?_⟩
    rw [show (τ.setVar "j" (σ.vars "j" + 1)).vars "hit" = σ.vars "hit" by rw [hτ]; simp,
      show (τ.setVar "j" (σ.vars "j" + 1)).vars "j" = σ.vars "j" + 1 by rw [hτ]; simp, hhit]
    congr 1
    refine propext ⟨fun ⟨p, h₁, h₂, h₃, h₄⟩ => ⟨p, h₁, by omega, h₃, h₄⟩,
      fun ⟨p, h₁, h₂, h₃, h₄⟩ => ⟨p, h₁, ?_, h₃, h₄⟩⟩
    rcases Nat.lt_or_ge p (σ.vars "j") with h' | h'
    · exact h'
    · exact absurd h₃ (by rw [show p = σ.vars "j" by omega, hm]; simp)
  · by_cases hs : Src (T (σ.vars "j")) = 0
    · -- alive but unmarked: nothing happens either
      refine ⟨τ.setVar "j" (σ.vars "j" + 1), 20,
        (hrw.seq ((Run.ite_true (by rw [hcmsk]; simp; omega)
          (Run.ite_false (by rw [hcsrc, hs]; simp) Run.skip)).seq
          (Run.assign (evalB_bin (evalB_var (by rw [hτ]; simp; omega)) (evalB_lit (by omega))
            (by simp [hτ]; omega))))).mono (by simp), ?_, by rw [hτ]; simp, le_rfl⟩
      refine ⟨expandInv_congr hinv (by rw [hτ]; simp) (by rw [hτ]; simp)
          (fun a => by rw [hτ]; simp),
        by rw [hτ]; simp [hzv], by rw [hτ]; simp [hjend], by rw [hτ]; simp; omega,
        by rw [hτ]; simp; omega, ?_⟩
      rw [show (τ.setVar "j" (σ.vars "j" + 1)).vars "hit" = σ.vars "hit" by rw [hτ]; simp,
        show (τ.setVar "j" (σ.vars "j" + 1)).vars "j" = σ.vars "j" + 1 by rw [hτ]; simp, hhit]
      congr 1
      refine propext ⟨fun ⟨p, h₁, h₂, h₃, h₄⟩ => ⟨p, h₁, by omega, h₃, h₄⟩,
        fun ⟨p, h₁, h₂, h₃, h₄⟩ => ⟨p, h₁, ?_, h₃, h₄⟩⟩
      rcases Nat.lt_or_ge p (σ.vars "j") with h' | h'
      · exact h'
      · exact absurd h₄ (by rw [show p = σ.vars "j" by omega, hs]; simp)
    · -- a live marked neighbour: the flag rises
      refine ⟨(τ.setVar "hit" 1).setVar "j" (σ.vars "j" + 1), 20,
        (hrw.seq ((Run.ite_true (by rw [hcmsk]; simp; omega)
          (Run.ite_true (by rw [hcsrc]; simp; omega)
            (Run.assign (evalB_lit (by omega))))).seq
          (Run.assign (evalB_bin (evalB_var (by rw [hτ]; simp; omega)) (evalB_lit (by omega))
            (by simp [hτ]; omega))))).mono (by simp), ?_, by rw [hτ]; simp, le_rfl⟩
      refine ⟨expandInv_congr hinv (by rw [hτ]; simp) (by rw [hτ]; simp)
          (fun a => by rw [hτ]; simp),
        by rw [hτ]; simp [hzv], by rw [hτ]; simp [hjend], by rw [hτ]; simp; omega,
        by rw [hτ]; simp; omega, ?_⟩
      rw [show ((τ.setVar "hit" 1).setVar "j" (σ.vars "j" + 1)).vars "hit" = 1 by rw [hτ]; simp,
        show ((τ.setVar "hit" 1).setVar "j" (σ.vars "j" + 1)).vars "j" = σ.vars "j" + 1 by
          rw [hτ]; simp]
      rw [if_pos ⟨σ.vars "j", hjlo, by omega, hm, hs⟩]

/-- **One vertex of the expansion.** The source's own cell, raised to
one when a live neighbour is marked: the block scan decides which, and
`hit_eq_expandVal` is what a full scan is worth. -/
theorem expandStep_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hB : 1 < B) (hnB : n < B)
    (hnsB : ns < B) (hMB : ∀ k, k < n → Msk k < B) (hSB : ∀ k, k < n → Src k < B)
    (hdm : dst ≠ msk) (hds : dst ≠ src) (hdo : dst ≠ "off") (hdt : dst ≠ "tgt") :
    Spec B (fun σ => ExpandInv n ns G O T Msk Src msk src dst σ ∧ σ.vars "z" < n)
      (expandStep msk src dst)
      (fun σ σ' => ExpandInv n ns G O T Msk Src msk src dst σ' ∧ σ'.vars "z" = σ.vars "z" + 1)
      (24 * ns + 40) := by
  classical
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hinv, hz⟩ := hσ
  have hzB : σ.vars "z" < B := by omega
  have hSz : Src (σ.vars "z") < B := hSB _ hz
  -- hit := src[z]
  have hr₁ : Run B (.assign "hit" (.get src (.var "z"))) σ
      (σ.setVar "hit" (Src (σ.vars "z"))) 3 :=
    (Run.assign (evalB_get (evalB_var hzB)
      (by rw [hinv.2.2.2.2.2, getElem?_arrOf Src hz]) hSz)).mono (by simp)
  set σ₁ := σ.setVar "hit" (Src (σ.vars "z")) with hσ₁
  have hz₁ : σ₁.vars "z" = σ.vars "z" := by rw [hσ₁]; simp
  have hhit₁ : σ₁.vars "hit" = Src (σ.vars "z") := by rw [hσ₁]; simp
  have hinv₁ : ExpandInv n ns G O T Msk Src msk src dst σ₁ :=
    expandInv_congr hinv hz₁ (by rw [hσ₁]; simp) (fun a => by rw [hσ₁]; simp)
  have hcond : (Cond.lt (.lit 0) (.get msk (.var "z"))).evalB B σ₁ =
      some (decide (0 < Msk (σ.vars "z"))) :=
    evalB_condLt (evalB_lit (by omega))
      (evalB_get (evalB_var (by rw [hz₁]; omega))
        (by rw [hinv₁.2.2.2.2.1, hz₁, getElem?_arrOf Msk hz]) (hMB _ hz))
  -- the conditional: a live vertex scans its block, a dead one does not
  have key : ∃ σ₂ K₂, Run B (.ite (.lt (.lit 0) (.get msk (.var "z")))
        (.seq (Csr.loadRow "off" "z" "j" "jend") (Csr.scan "j" "jend" (expandSlot msk src)))
        .skip) σ₁ σ₂ K₂ ∧ K₂ ≤ 24 * ns + 17 ∧
      ExpandInv n ns G O T Msk Src msk src dst σ₂ ∧ σ₂.vars "z" = σ.vars "z" ∧
      σ₂.vars "hit" = expandVal G Msk Src (σ.vars "z") := by
    by_cases hm : Msk (σ.vars "z") = 0
    · exact ⟨σ₁, 6, Run.ite_false (by rw [hcond, hm]; simp) Run.skip, by omega, hinv₁, hz₁,
        by rw [hhit₁, expandVal_of_dead hm]⟩
    · obtain ⟨σ₂, hr₂, hcsr₂, hj₂, hjend₂, hst₂⟩ :=
        (Csr.loadRow_spec B n ns n "off" "tgt" "z" "j" "jend" O T (by decide) (by decide)).run
          (σ := σ₁) ⟨⟨csr_of_expandInv hcsr hinv₁, by omega, hnsB⟩,
            by rw [hz₁]; exact hz, by rw [hz₁]; omega⟩
      rw [hz₁] at hj₂ hjend₂
      have hzz : σ₂.vars "z" = σ.vars "z" := by rw [hst₂]; simp [hz₁]
      have hhit₂ : σ₂.vars "hit" = Src (σ.vars "z") := by rw [hst₂]; simp [hhit₁]
      have hinv₂ : ExpandInv n ns G O T Msk Src msk src dst σ₂ :=
        expandInv_congr hinv₁ (by rw [hst₂]; simp) (by rw [hst₂]; simp)
          (fun a => by rw [hst₂]; simp)
      have hrow : O (σ.vars "z" + 1) ≤ ns := (csr_of_expandInv hcsr hinv).row_le hz
      have hlo : O (σ.vars "z") ≤ O (σ.vars "z" + 1) := hcsr.mono _ hz
      have hclause : σ₂.vars "hit" =
          (if ∃ p, O (σ.vars "z") ≤ p ∧ p < σ₂.vars "j" ∧ Msk (T p) ≠ 0 ∧ Src (T p) ≠ 0
            then 1 else Src (σ.vars "z")) := by
        rw [hhit₂, if_neg]
        rintro ⟨p, h₁, h₂, -⟩
        rw [hj₂] at h₂
        omega
      have hI₂ : ScanHit n ns G O T Msk Src msk src dst (σ.vars "z") σ₂ :=
        ⟨hinv₂, hzz, hjend₂, by omega, by omega, hclause⟩
      obtain ⟨σ₃, hr₃, hI₃, hj₃⟩ :=
        (Csr.rowScan_spec B (24 * ns + 4) (O (σ.vars "z" + 1)) 20 "j" "jend"
          (expandSlot msk src) (P := ScanHit n ns G O T Msk Src msk src dst (σ.vars "z"))
          (ScanHit n ns G O T Msk Src msk src dst (σ.vars "z")) (by omega)
          (fun ρ hρ => ⟨hρ.2.2.1, hρ.2.2.2.2.1⟩)
          (fun ρ hρ hjlt => expandSlot_step hcsr hB hnB hnsB hMB hSB hz ρ hρ hjlt)
          (fun _ hρ => hρ)
          (fun ρ hρ => by
            have h1 : (20 + 4) * (O (σ.vars "z" + 1) - ρ.vars "j") ≤ 24 * ns := by
              have := Nat.mul_le_mul_left 24
                (Nat.sub_le (O (σ.vars "z" + 1)) (ρ.vars "j"))
              omega
            omega)).run hI₂
      refine ⟨σ₃, 1 + 4 + (8 + (24 * ns + 4)), Run.ite_true (by rw [hcond]; simp; omega)
        (hr₂.seq hr₃), by omega, hI₃.1, hI₃.2.1, ?_⟩
      rw [hI₃.2.2.2.2.2, hj₃, hit_eq_expandVal hcsr hz hm]
  obtain ⟨σ₂, K₂, hr₂, hK₂, hinv₂, hzz, hhit₂⟩ := key
  -- the store, and the counter
  have hval : expandVal G Msk Src (σ.vars "z") < B := by
    rcases expandVal_eq_or G Msk Src (σ.vars "z") with h | h
    · rw [h]; omega
    · rw [h]; exact hSz
  have hdlen : σ₂.vars "z" < (σ₂.arrs dst).length := by rw [hinv₂.1.length, hzz]; exact hz
  refine ⟨(σ₂.setArr dst (σ₂.vars "z") (σ₂.vars "hit")).setVar "z" (σ₂.vars "z" + 1),
    3 + (K₂ + (3 + 4)), (hr₁.seq (hr₂.seq
      ((Run.store (evalB_var (by rw [hzz]; omega)) (evalB_var (by rw [hhit₂]; exact hval)) hdlen).seq
        (Run.assign (evalB_bin (evalB_var (by simp [hzz]; omega)) (evalB_lit (by omega))
          (by simp [hzz]; omega)))))), by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [hzz]⟩
  · exact hinv₂.1.step (by rw [hzz]; exact hz) (by rw [hhit₂, hzz])
  · simp only [vars_setVar, if_neg (by decide : ¬ ("n" = "z")), vars_setArr]
    exact hinv₂.2.1
  · rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdo)]; exact hinv₂.2.2.1
  · rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdt)]; exact hinv₂.2.2.2.1
  · rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdm)]; exact hinv₂.2.2.2.2.1
  · rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hds)]; exact hinv₂.2.2.2.2.2

/-- **One expansion pass, discharged.** The destination holds
`RamDriverCluster.expandVal` at every vertex of the carrier — so, by
`markSet_expandVal`, it marks one neighbourhood step of what the source
marks — and everything the pass reads comes back. -/
theorem expandCom_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hB : 1 < B) (hnB : n < B)
    (hnsB : ns < B) (hMB : ∀ k, k < n → Msk k < B) (hSB : ∀ k, k < n → Src k < B)
    (hdm : dst ≠ msk) (hds : dst ≠ src) (hdo : dst ≠ "off") (hdt : dst ≠ "tgt") :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧
        σ.arrs "tgt" = arrOf ns T ∧ σ.arrs msk = arrOf n Msk ∧ σ.arrs src = arrOf n Src ∧
        (∃ g, σ.arrs dst = arrOf n g))
      (expandCom msk src dst)
      (fun _ σ' => (∃ g, σ'.arrs dst = arrOf n g ∧
          ∀ k, k < n → g k = expandVal G Msk Src k) ∧
        σ'.vars "z" = n ∧ σ'.vars "n" = n ∧ σ'.arrs "off" = arrOf (n + 1) O ∧
        σ'.arrs "tgt" = arrOf ns T ∧ σ'.arrs msk = arrOf n Msk ∧ σ'.arrs src = arrOf n Src)
      ((24 * ns + 44) * n + 6) := by
  refine ((Spec.forRangeZero (B := B) "z" "n" (ExpandInv n ns G O T Msk Src msk src dst) n
    (24 * ns + 40) hnB (fun τ hτ => hτ.1.le) (fun τ hτ => hτ.2.1)
    (expandStep_spec hcsr hB hnB hnsB hMB hSB hdm hds hdo hdt)).pre ?_).post ?_ |>.mono
      (by ring_nf; omega)
  · rintro σ ⟨hn, hoff, htgt, hmsk, hsrc, g, hdst⟩
    exact ⟨Fill.below_zero (by rw [arrs_setVar]; exact hdst) (by simp),
      by simpa using hn, by simpa using hoff, by simpa using htgt, by simpa using hmsk,
      by simpa using hsrc⟩
  · rintro σ σ' - ⟨hinv, hz⟩
    exact ⟨hinv.1.done hz, hz, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1,
      hinv.2.2.2.2.2⟩

/-! ### The chain

`RamDriver.chainCom` is `expandCom` iterated, and its walk is an
induction whose step is the equation below: the chain of `r + 1`
expansions is one pass into the first scratch name followed by the
chain of `r` at the shifted family. The ball's chain alternates between
two names (`RamDriver.ballStage`) and the colour chains run through
distinct ones; both are instances of the same recursion, which is why
the family is a parameter. -/

theorem foldRange_succ (f : ℕ → Com) (r : ℕ) :
    foldRange f (r + 1) = .seq (f 0) (foldRange (fun a => f (a + 1)) r) := by
  simp [foldRange, List.range_succ_eq_map, List.foldr_map]

theorem chainCom_zero (msk : String) (nm : ℕ → String) : chainCom msk nm 0 = .skip := rfl

theorem chainCom_succ (msk : String) (nm : ℕ → String) (r : ℕ) :
    chainCom msk nm (r + 1) =
      .seq (expandCom msk (nm 0) (nm 1)) (chainCom msk (fun a => nm (a + 1)) r) := by
  simp [chainCom, foldRange_succ]

/-- **The radius of a chain that expands first.** The walk peels the
chain from the *front*, so what its induction produces is `r` units of
radius around one neighbourhood step; `nbhd_ballOf` is the same
statement with the step taken last. -/
theorem ballOf_nbhd (A : SimpleGraph (Fin n)) (r : ℕ) (S : Set (Fin n)) :
    ballOf A r (nbhd A S) = ballOf A (r + 1) S := by
  induction r with
  | zero => rw [ballOf_zero, ← nbhd_ballOf, ballOf_zero]
  | succ r ih => rw [← nbhd_ballOf A r, ih, nbhd_ballOf]

/-- A mask is what it marks below the carrier. -/
theorem markSet_congr {f g : ℕ → ℕ} (h : ∀ k, k < n → f k = g k) :
    markSet n f = markSet n g := by
  ext v
  rw [mem_markSet, mem_markSet, h (v : ℕ) v.isLt]

/-- An array that was there is still there: a run cannot change a
length. -/
theorem exists_arrOf_run {B K N : ℕ} {c : Com} {σ σ' : Env} {a : String}
    (hr : Run B c σ σ' K) (h : ∃ g, σ.arrs a = arrOf N g) : ∃ g, σ'.arrs a = arrOf N g :=
  exists_arrOf ((run_length_arrs hr a).trans (by obtain ⟨g, hg⟩ := h; rw [hg, length_arrOf]))

/-- **The chain of expansions, discharged.** After `r` passes the last
name of the family marks the `r`-neighbourhood of what the first one
marked, in the arena the mask cuts out. -/
theorem chainCom_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hB : 1 < B) (hnB : n < B)
    (hnsB : ns < B) (hMB : ∀ k, k < n → Msk k < B) :
    ∀ (r : ℕ) (nm : ℕ → String) (Sr : ℕ → ℕ), (∀ a, nm a ≠ nm (a + 1)) → (∀ a, nm a ≠ msk) →
      (∀ a, nm a ≠ "off") → (∀ a, nm a ≠ "tgt") → (∀ k, k < n → Sr k < B) →
      Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧
          σ.arrs "tgt" = arrOf ns T ∧ σ.arrs msk = arrOf n Msk ∧
          σ.arrs (nm 0) = arrOf n Sr ∧ (∀ a, 0 < a → a ≤ r → ∃ g, σ.arrs (nm a) = arrOf n g))
        (chainCom msk nm r)
        (fun _ σ' => (∃ g, σ'.arrs (nm r) = arrOf n g ∧ (∀ k, k < n → g k < B) ∧
            markSet n g = ballOf (masked G Msk) r (markSet n Sr)) ∧
          σ'.vars "n" = n ∧ σ'.arrs "off" = arrOf (n + 1) O ∧ σ'.arrs "tgt" = arrOf ns T ∧
          σ'.arrs msk = arrOf n Msk)
        (((24 * ns + 44) * n + 6) * r + 1) := by
  intro r
  induction r with
  | zero =>
    intro nm Sr _ _ _ _ hSB
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hn, hoff, htgt, hmskA, hsrc, -⟩ := hσ
    exact ⟨σ, 1, by rw [chainCom_zero]; exact Run.skip, by omega,
      ⟨Sr, hsrc, hSB, by rw [ballOf_zero]⟩, hn, hoff, htgt, hmskA⟩
  | succ r ih =>
    intro nm Sr hne hmk hof htg hSB
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨hn, hoff, htgt, hmskA, hsrc, hmem⟩ := hσ
    obtain ⟨g₁, hg₁⟩ := hmem 1 (by omega) (by omega)
    obtain ⟨σ₁, hr₁, ⟨g, hgarr, hgval⟩, -, hn₁, hoff₁, htgt₁, hmsk₁, hsrc₁⟩ :=
      (expandCom_spec (dst := nm 1) (src := nm 0) hcsr hB hnB hnsB hMB hSB (hmk 1)
        (Ne.symm (hne 0)) (hof 1) (htg 1)).run ⟨hn, hoff, htgt, hmskA, hsrc, g₁, hg₁⟩
    have hgB : ∀ k, k < n → g k < B := by
      intro k hk
      rw [hgval k hk]
      rcases expandVal_eq_or G Msk Sr k with h | h
      · rw [h]; omega
      · rw [h]; exact hSB k hk
    obtain ⟨σ₂, hr₂, ⟨g', hg'arr, hg'B, hg'mark⟩, hn₂, hoff₂, htgt₂, hmsk₂⟩ :=
      (ih (fun a => nm (a + 1)) g (fun a => hne (a + 1)) (fun a => hmk (a + 1))
        (fun a => hof (a + 1)) (fun a => htg (a + 1)) hgB).run
        ⟨hn₁, hoff₁, htgt₁, hmsk₁, hgarr,
          fun a _ ha => exists_arrOf_run hr₁ (hmem (a + 1) (by omega) (by omega))⟩
    refine ⟨σ₂, _, by rw [chainCom_succ]; exact hr₁.seq hr₂, by ring_nf; omega,
      ⟨g', hg'arr, hg'B, ?_⟩, hn₂, hoff₂, htgt₂, hmsk₂⟩
    rw [hg'mark, markSet_congr hgval, markSet_expandVal, ballOf_nbhd]

end Expand

end Lax3Proofs.RamDriverDescend
