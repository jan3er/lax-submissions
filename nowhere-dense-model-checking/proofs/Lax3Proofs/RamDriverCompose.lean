import Lax3Proofs.RamDriverOrder
import Lax3Proofs.RamDriverBot
import Lax3Proofs.RamDriverAugment
import Lax3Proofs.TgtCoupling

/-!
Three of the **composition obligations of the driver**, discharged:
`Lax3Proofs.RamDriver.CoverImplements`,
`Lax3Proofs.RamDriver.BaseImplements` and — at `R = 0` —
`Lax3Proofs.RamDriver.OrderImplements`.

# What is proved here

* `coverImplements` — **the cover phase**. The two copies that set the
  pass up, `RamDriverOrder.coverPass_spec` — which is
  `RamCover.cover_spec` with its walk obligation already discharged —
  and the four copies of `RamDriver.coverSave` that make the answers
  the depth's own. `RamDriver.LevelPre` crosses the phase as a frame:
  the pass writes only the fixed scratch names and the depth's own
  four, and the level's state speaks about none of them except through
  `LevelMem` and `DepthMem`, which are lengths.
* `baseImplements` — **the base case**: `RamDriverBot.base_spec`
  translated into the surface, the frame off that file's four syntactic
  lemmas and the postcondition off `masked G M = ⊥`. The locality of the
  tabled formulas is not a hypothesis and does not need to be —
  `FormulaTables.tableRank_of_mem_tablesAt` is that every table entry is
  local.
* `orderImplements₀` — **the ordering phase at `R = 0`**: twelve passes,
  of which the two eliminations are `elimRank_spec` (below), the rank
  inversion is `RamDriverOrder.ordCom_spec`, the block-structure copies
  are `saveCsr_spec`/`restoreCsr_spec`, and the eight fills of the
  re-zeroing tail are `orderZero_spec`. At `R = 0` the augmentation fold
  is `Com.skip`, so the round's own obligation is never applied; the
  postcondition is unchanged, since it names only *some* ordering, and
  what the augmentation buys — the cover's degree, hence the cost — is
  the cost wave's business.

### Ledger — the tower search underneath (rebase P1)

**P1/B-g — nothing above the obligation boundary moved.** The cover
pass now embeds the refinement tower's synthesized queue BFS
(`Lax3Proofs.Refine.BfsBridge.bfsQCom`) where `RamBfs.bfsCom` stood.
Four lines of this file change and no statement does: the two `rfl`
lists `wvars_coverCom`/`wvars_coverPhase` grow by the tower's own
scalar cells (the arrays written, and so `warrs_coverCom` and
`warrs_coverPhase`, are the same two in the same order),
`noWrite_coverPhase` reads the tower's `Codegen.noWrite_embed` instead
of the old search's five constructors, and the call of
`coverPass_spec` passes `LevelMem`'s `q` word clause beside its `dist`
one (ledger P1/B-d in `RamCover`). `coverImplements` proves
`RamDriver.CoverImplements` at `coverPhaseCost n ns`, verbatim as
before — the per-centre budget absorbs the new constant (P1/B-e).

Three pieces of reusable machinery come with them.

* `levelPre_run` and `orderMem_run` — **a level's state is a frame**.
* `fillPrefix_spec` and `copyPrefix_spec` — **a flat pass over a prefix
  of a longer array**.
* `coverOut_off_le` and `coverOut_congr` — **the cover's answer reads
  the member array only below the write pointer**.

And three more for the ordering phase: `elimRank_spec` (the elimination
with the rank bound its own surface drops), `fillZero_spec` /
`elimRezero_spec` / `orderZero_spec` (the flat zeroing passes), and the
syntactic section that reads `RamDriver.orderCom`'s write sets off its
text.

# The three defects wave D4 repaired

**A — the program.** `RamDriver.orderCom` ran `RamElim.elimCom` twice
with nothing between them that re-zeroes `elm` or `bh`, so the second
call's `elimLoop` dropped every slot it popped, never advanced `cnt`,
and read `bh[n+1]` out of range: for `n ≥ 1` there was **no run**, and
the obligation was refuted rather than unproved. `RamDriver.elimRezeroCom`
— the `elm` and `bh` fills, and only those two, since they are the only
clauses of `RamElim.ElimPre` that ask for a value rather than a length —
is inserted between `fillCom "alv" 1` and the second elimination. See
`RamDriver.orderCom`'s docstring for the full record.

**B — the ordering surface.** `RamElim.Implements` takes
`RamElim.CsrSimple`, which is `RamBfs.CsrGraph` with *no row names a
vertex twice* — the clause `RamElim.card_liveSlots` needs to read a
degree off a row. `RamDriver.OrderImplements` carried only `CsrGraph`,
and a structure listing a neighbour twice double-counts that degree. The
obligation now takes `CsrSimple`, and `RamDriverCluster.levelImplements`
takes it and hands `hcsr.csr` to the cover phase and the cluster step.

It is **not derivable from the input encoding**:
`Lax11.GraphEncoding.EncodesGraph`'s own note says that repetitions in a
block are deliberately not forbidden, the encoding being the dumbest
possible input format, and `m` is only the declared half-length of the
target array. So the clause is one more piece of *data of the input
word* — "no block of the word names a vertex twice" — and the root has
to supply it. (It is equivalent to the word's declared `m` being the
true edge count.)

**C — the scratch's word clause.** `orderCom` copies the *whole* of the
in-list target array, `copyUpto "itg" "dtg" (.lit W)`, while an
elimination fills only the `m ≤ ns` cells its own arcs occupy; the tail
above `m` is whatever the memory held, and a cell at or above the word
bound has no bounded evaluation. Any state satisfying `LevelPre` whose
`itg` holds `B` at a cell above the last arc therefore gives the phase
no run, and the obligation was again refuted.
`RamDriver.OrderMem` therefore gains `B` as a parameter and two clauses,
`itg` and `ntg` hold words — the same species as its eight zeroing
clauses, true of a machine's memory for the same reason, and neither is
a frame condition, since a bounded run stores only words. `ntg` is
`augRelinkCom`'s copy and is not reached at `R = 0`; it is carried
because it is the same defect one round later.

# The frontier for the wave that follows

**Closed at rebase F-c-5**: the `Rstar` section at the end of this file
now *discharges* the `R`-round phase — `orderImplementsR` proves
`OrderImplementsR` under the three mathematical hypotheses its
docstring names, exporting the `OrderP` chain bundle the root's `hdeg`
slot consumes through `RamDriverRoot.wreachDeg_of_orderP`. The two
couplings this paragraph used to record as open were closed by F-c-2
and F-c-4 (the `tgt` flip) and coupling (b) (`TgtCoupling.chainWidth`);
the round
itself is `RamDriverAugment.implementsW`. What the fold walk found and
repaired on the way — the round's entry was refuted as landed — is the
`Rstar` section header's F-c-5 record.

The end-to-end instantiation of `RamDriver.driver_correct` is
`Lax3Proofs.RamDriverRoot.driverRoot_decides_sentence`, at `R = 0` and
with costs parametric. What wave E2 had to move to get there — all three
of what this header used to list as missing — is recorded at its two
sites and summarized here.

* `RamDriver.AugAvail B n` is `RamDriverAugment.implements` (wave E1c).
  `RamDriver.ElimAvail` is `RamElim.implements` and
  `RamDriver.CoverAvail` is `RamDriverOrder.coverTurnImplements`.
* `RamDriverFrames.clusterFrames` and
  `RamDriverCluster.clusterStepImplements` took the family of
  `RamDriverCluster.InnerFrames` as a parameter, and `InnerFrames` is a
  `Spec` of the *nested driver*, so producing it needs that driver's
  termination — which is exactly the `hinner` those two carry as an
  antecedent. The hypothesis now sits **under** it:
  `clusterStepImplements`'s `hfr` takes
  `RamDriverCluster.InnerAvail` first, and `clusterFrames` takes
  `RamDriverFrames.innerFrames`' syntactic side and builds the family
  itself. The bit clause `InnerAvail` needs is the ninth conjunct of
  `RamDriver.LevelPre` at the next depth, so nothing else moved.
* `RamDriverCluster.levelImplements` still takes the *mathematics* of
  the campaign — `hQ`, uniform quasi-wideness of the arena at the radius
  `2·cap`, and `hℓ : ℓ = N (2s+2)` — and the cost side conditions, and
  the end-to-end theorem carries both: the first is the campaign's own
  input, the second is the cost wave's business.

Two clauses of `TurnFrozen` had to go, and not for convenience: a level
writes the padding buffer `"wa"` and every one of `RamDriver.OrderMem`'s
eight accumulators, so asking the nested call to leave them alone was
*refutable* — see `RamDriverWrites.wa_mem_warrs_driverAt` and
`elm_mem_warrs_driverAt`. The accumulators now come back from
`RamDriver.LevelPost`, and the buffer moved out of
`RamDriverCluster.ClusterData` into `ClusterWa`, live only between the
padding and the colouring.
-/

namespace Lax3Proofs.RamDriverCompose

open Lax3.ColoredGraphs Lax3.DistFO
open Lax3Proofs.SyntaxLemmas Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked CsrGraph)
open Lax3Proofs.RamCover (CoverOut CoverPre CoverPost OrdersBy)
open Lax3Proofs.RamElim (CsrSimple ElimPre ElimPreW ElimPost ElimMem elimCom elimCost adeg
  AfterDeg AfterBuck AfterLoop AfterOff AfterDegW AfterBuckW AfterLoopW AfterOffW)
open Lax3Proofs.RamDriver
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ### A name and its own prefix

Every per-depth name of the driver is a literal with a decimal numeral
appended, so it is never the literal itself. The numeral is nonempty
because `String.toNat?` reads it back, and the empty string reads back
as `none`. -/

/-- A decimal representation has at least one digit: `Nat.toDigits`'s
own recursion equation ends in a digit in both branches. -/
theorem toDigits_ne_nil (j : ℕ) : Nat.toDigits 10 j ≠ [] := by
  rw [Nat.toDigits_eq_if (by omega)]
  split <;> simp

/-- A decimal numeral is not the empty string. -/
@[local simp]
theorem toString_toList_ne_nil (j : ℕ) : (toString j).toList ≠ [] := by
  have h0 := toDigits_ne_nil j
  rw [Nat.toString_eq_repr, RamDriverBase.repr_eq_ofList]
  simp [h0]

/-- A per-depth name is not the literal it extends. -/
theorem append_toString_ne (p : String) (j : ℕ) : p ++ toString j ≠ p :=
  RamDriverBot.append_ne_self (toString_toList_ne_nil j)

/-- **A decimal representation contains only digits.** This is
`RamDriverBase.underscore_not_mem_toDigits` with the separator replaced
by any character that is not a digit, which is what a literal name
sharing a prefix with a per-depth name needs. -/
theorem notMem_toDigits {c : Char} (hc : ∀ d < 10, Nat.digitChar d ≠ c) :
    ∀ j : ℕ, c ∉ Nat.toDigits 10 j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rw [Nat.toDigits_eq_if (by omega)]
    split
    · rename_i hlt
      simp only [List.mem_singleton]
      exact fun h => hc _ hlt h.symm
    · rename_i hge
      have hpos : 0 < j := by omega
      simp only [List.mem_append, not_or]
      refine ⟨ih (j / 10) (Nat.div_lt_self hpos (by omega)), ?_⟩
      simp only [List.mem_singleton]
      exact fun h => hc _ (Nat.mod_lt _ (by omega)) h.symm

/-- A decimal numeral, as a list of characters. -/
theorem toList_toString (j : ℕ) : (toString j).toList = Nat.toDigits 10 j := by
  rw [Nat.toString_eq_repr, RamDriverBase.repr_eq_ofList]
  simp

/-- **The member array of the cover is not the depth's copy of it.**
Both begin `xm`, and what follows is `em` in the one and a decimal
numeral in the other. -/
theorem xmem_ne_xmmName (j : ℕ) : "xmem" ≠ xmmName j := by
  intro h
  rw [xmmName, String.ext_iff] at h
  have h' : Nat.toDigits 10 j = ['e', 'm'] := by
    rw [← toList_toString]
    exact (by simpa using h : ['e', 'm'] = (toString j).toList).symm
  exact notMem_toDigits (c := 'e') (by decide) j (by rw [h']; simp)

theorem alvName_ne_alv (j : ℕ) : alvName j ≠ "alv" := append_toString_ne "alv" j

theorem asgName_ne_asg (j : ℕ) : asgName j ≠ "asg" := by
  simp [asgName, String.ext_iff]

/-! ### What the cover phase writes -/

theorem warrs_compactCom (j : ℕ) : (compactCom j).warrs = [cpsName j] := by
  simp [compactCom, Com.warrs]

theorem wvars_compactCom (j : ℕ) :
    (compactCom j).wvars = [cnumName j, "i", cnumName j, "i"] := by
  simp [compactCom, Com.wvars]

theorem warrs_coverPhase (cap j : ℕ) : (coverPhase cap j).warrs =
    ["ord", "alv", "asg", "xoff", "dist", "dist", "q", "dist", "q", "xmem", "asg", "alv",
      "xoff", xofName j, xmmName j, asgName j, cpsName j] := rfl

theorem wvars_coverPhase (cap j : ℕ) : (coverPhase cap j).wvars =
    ["i", "i", "i", "i", "i", "i", "xp", "c", "src",
      "sent", "d", "one", "i", "head", "a", "tl", "v", "dv", "dv1", "k0", "v1", "kend",
      "u", "au", "du",
      "i", "a", "tl", "tl", "v", "dv", "head", "dv1", "k0", "v1", "kend", "u", "au",
      "du", "tl", "k0",
      "z", "dz", "xp", "z", "c",
      "i", "i", "i", "i", "i", "i", xpName j, cnumName j, "i", cnumName j, "i"] := rfl

/-! ### The frame of a level's state

`RamDriver.LevelPre` is thirteen clauses, of which two are scalars, five
are named arrays, and the last four survive any run outright. So a pass
that writes none of the seven names carries the whole clause across, and
that is what every phase of a level does with it. -/

/-- The eight arrays `RamDriver.OrderMem`'s zeroing half speaks about. -/
def zeroArrs : List String := ["elm", "bh", "ooff", "noff", "stf", "sta", "std", "ste"]

/-- **The engines' scratch survives a pass that does not write it.**
The eight zeroed arrays are the only frame: the lengths cross by
themselves, and the two word clauses cross because a bounded run stores
only words, whether or not it writes the array. -/
theorem orderMem_run {B n ns W : ℕ} {c : Com} {σ σ' : Env} {K : ℕ}
    (h : OrderMem B n ns W σ) (hr : Run B c σ σ' K) (hlw : "lw" ∉ c.wvars)
    (hz : ∀ a ∈ zeroArrs, a ∉ c.warrs) :
    OrderMem B n ns W σ' := by
  obtain ⟨hle, hlwv, hsz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨hle, by rw [hr.frame_var "lw" hlw]; exact hlwv, hsz.run hr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    run_mem_arrs_lt hr "itg" h9, run_mem_arrs_lt hr "ntg" h10⟩
  · rw [hr.frame_arr "elm" (hz "elm" (by simp [zeroArrs]))]; exact h1
  · rw [hr.frame_arr "bh" (hz "bh" (by simp [zeroArrs]))]; exact h2
  · rw [hr.frame_arr "ooff" (hz "ooff" (by simp [zeroArrs]))]; exact h3
  · rw [hr.frame_arr "noff" (hz "noff" (by simp [zeroArrs]))]; exact h4
  · rw [hr.frame_arr "stf" (hz "stf" (by simp [zeroArrs]))]; exact h5
  · rw [hr.frame_arr "sta" (hz "sta" (by simp [zeroArrs]))]; exact h6
  · rw [hr.frame_arr "std" (hz "std" (by simp [zeroArrs]))]; exact h7
  · rw [hr.frame_arr "ste" (hz "ste" (by simp [zeroArrs]))]; exact h8

/-- **A level's state survives a pass that writes none of its names.**
The two scalars, the five arrays and the eight zeroed ones are the whole
frame; everything else in `RamDriver.LevelPre` is a length or a value
bound and survives any run. -/
theorem levelPre_run {B n cap mb ns W j : ℕ} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {c : Com} {σ σ' : Env} {K : ℕ}
    (h : LevelPre B n cap mb ns W O T j M Gm C σ) (hr : Run B c σ σ' K)
    (hn : "n" ∉ c.wvars) (hm : "m" ∉ c.wvars) (hlw : "lw" ∉ c.wvars)
    (hoff : "off" ∉ c.warrs) (htgt : "tgt" ∉ c.warrs)
    (halv : alvName j ∉ c.warrs) (hgam : gamName j ∉ c.warrs)
    (hcol : ∀ q : ℕ, colName j q ∉ c.warrs)
    (hz : ∀ a ∈ zeroArrs, a ∉ c.warrs)
    (hmemA : memName j ∉ c.warrs) (hmmv : mnumName j ∉ c.wvars) :
    LevelPre B n cap mb ns W O T j M Gm C σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    Mem, mmj, hm1, hm2, hm3, hm4⟩ := h
  exact ⟨by rw [hr.frame_var "n" hn]; exact h1,
    by rw [hr.frame_arr "off" hoff]; exact h2,
    by rw [hr.frame_arr "tgt" htgt]; exact h3,
    by rw [hr.frame_arr _ halv]; exact h4,
    by rw [hr.frame_arr _ hgam]; exact h5,
    fun q hq => by rw [hr.frame_arr _ (hcol q)]; exact h6 q hq,
    h7, h8, h9, levelMem_run hr h10, h11.run hr,
    by rw [hr.frame_var "m" hm]; exact h12,
    orderMem_run h13 hr hlw hz, h14, h15,
    Mem, mmj, by rw [hr.frame_arr _ hmemA]; exact hm1,
    by rw [hr.frame_var _ hmmv]; exact hm2, hm3, hm4⟩

/-! ### The cover phase's own frames -/

theorem alvName_notMem_coverPhase (cap j a : ℕ) : alvName a ∉ (coverPhase cap j).warrs := by
  rw [warrs_coverPhase]
  simp [alvName, xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem gamName_notMem_coverPhase (cap j a : ℕ) : gamName a ∉ (coverPhase cap j).warrs := by
  rw [warrs_coverPhase]
  simp [gamName, xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem colName_notMem_coverPhase (cap j a c : ℕ) : colName a c ∉ (coverPhase cap j).warrs := by
  rw [warrs_coverPhase]
  simp [colName, xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem off_notMem_coverPhase (cap j : ℕ) : "off" ∉ (coverPhase cap j).warrs := by
  rw [warrs_coverPhase]
  simp [xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem tgt_notMem_coverPhase (cap j : ℕ) : "tgt" ∉ (coverPhase cap j).warrs := by
  rw [warrs_coverPhase]
  simp [xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem zero_notMem_coverPhase (cap j : ℕ) :
    ∀ a ∈ zeroArrs, a ∉ (coverPhase cap j).warrs := by
  rw [warrs_coverPhase]
  intro a ha
  simp only [zeroArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem ctrName_notMem_coverPhase (cap j a : ℕ) : ctrName a ∉ (coverPhase cap j).wvars := by
  rw [wvars_coverPhase]
  simp [ctrName, xpName, cnumName, String.ext_iff]

theorem n_notMem_coverPhase (cap j : ℕ) : "n" ∉ (coverPhase cap j).wvars := by
  rw [wvars_coverPhase]
  simp [xpName, cnumName, String.ext_iff]

theorem lw_notMem_coverPhase (cap j : ℕ) : "lw" ∉ (coverPhase cap j).wvars := by
  rw [wvars_coverPhase]
  simp [xpName, cnumName, String.ext_iff]

/-- The cover phase writes no depth's member list (rebase E-mem): the
per-cluster member CSR it fills is `xmmName j`, a different structure. -/
theorem memName_notMem_coverPhase (cap j a : ℕ) : memName a ∉ (coverPhase cap j).warrs := by
  rw [warrs_coverPhase]
  simp [memName, xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem mnumName_notMem_coverPhase (cap j a : ℕ) : mnumName a ∉ (coverPhase cap j).wvars := by
  rw [wvars_coverPhase]
  simp [mnumName, xpName, cnumName, String.ext_iff]

theorem m_notMem_coverPhase (cap j : ℕ) : "m" ∉ (coverPhase cap j).wvars := by
  rw [wvars_coverPhase]
  simp [xpName, cnumName, String.ext_iff]

/-! ### A copy into a prefix of a longer array

`RamDriverOrder.copyUpto_spec` — like everything built on
`Lax13Proofs.Reasoning.Lib.Fill.Below` — pins the destination's length
to the copy's bound. One pass of the driver does not have that shape:
`RamDriver.coverSave`'s member copy runs to the cover's write pointer
`xp`, while the destination `xmmName j` is the depth's own `n * n`-cell
array, and `RamDriver.DepthMem` sizes it there and nowhere else.

So the pass is restated with the destination's length a second
parameter, at or above the bound. Nothing else changes: the store's
range obligation is `i < N ≤ Na`, and the postcondition speaks only
about the cells below `N` — the tail of the destination is *not* claimed
to be untouched, and is not, since a shorter earlier copy may have left
anything there. -/

/-- **A flat pass over a prefix of an array**, the destination longer
than the bound. -/
theorem fillPrefix_spec {B : ℕ} (N Na : ℕ) (a : String) (bnd e : Expr) (F : ℕ → ℕ)
    (Q : Env → Prop) (hB : 0 < B) (hNB : N < B) (hNa : N ≤ Na)
    (hQfr : ∀ σ σ', Q σ → (∀ y, y ≠ "i" → σ'.vars y = σ.vars y) →
      (∀ b, b ≠ a → σ'.arrs b = σ.arrs b) → Q σ')
    (hbnd : ∀ σ, Q σ → bnd.evalB B σ = some N)
    (he : ∀ σ, Q σ → σ.vars "i" < N → e.evalB B σ = some (F (σ.vars "i"))) :
    Spec B (fun σ => (∃ g, σ.arrs a = arrOf Na g) ∧ Q σ)
      (fillUpto a bnd e)
      (fun _ σ' => (∃ g, σ'.arrs a = arrOf Na g ∧ ∀ k < N, g k = F k) ∧
        σ'.vars "i" = N ∧ Q σ')
      ((e.size + bnd.size + 9) * N + bnd.size + 5) := by
  have hbody : Spec B
      (fun σ => ((∃ g, σ.arrs a = arrOf Na g ∧ ∀ k < σ.vars "i", g k = F k) ∧
        σ.vars "i" ≤ N ∧ Q σ) ∧ σ.vars "i" < N)
      (Fill.put a "i" e)
      (fun σ σ' => ((∃ g, σ'.arrs a = arrOf Na g ∧ ∀ k < σ'.vars "i", g k = F k) ∧
        σ'.vars "i" ≤ N ∧ Q σ') ∧ σ'.vars "i" = σ.vars "i" + 1) (6 + e.size) := by
    refine Spec.of_exists fun σ hσ => ?_
    obtain ⟨⟨⟨g, harr, hcell⟩, hle, hQ⟩, hlt⟩ := hσ
    have hval := he σ hQ hlt
    have h1 : Run B (.store a (.var "i") e) σ
        (σ.setArr a (σ.vars "i") (F (σ.vars "i"))) (1 + 1 + e.size) := by
      have h := Run.store (B := B) (σ := σ) (a := a) (i := .var "i") (e := e)
        (evalB_var (by omega)) hval (by rw [harr, length_arrOf]; omega)
      simpa using h
    have h2 : Run B (.assign "i" (.add (.var "i") (.lit 1)))
        (σ.setArr a (σ.vars "i") (F (σ.vars "i")))
        ((σ.setArr a (σ.vars "i") (F (σ.vars "i"))).setVar "i" (σ.vars "i" + 1)) (1 + 3) := by
      have h := Run.assign (B := B) (σ := σ.setArr a (σ.vars "i") (F (σ.vars "i")))
        (x := "i") (e := .add (.var "i") (.lit 1))
        (evalB_bin (evalB_var (by rw [vars_setArr]; omega)) (evalB_lit (by omega))
          (by simp only [Bop.apply_add, vars_setArr]; omega))
      rw [Bop.apply_add, vars_setArr] at h
      simpa using h
    refine ⟨_, _, h1.seq h2, by omega,
      ⟨⟨upd g (σ.vars "i") (F (σ.vars "i")), ?_, ?_⟩,
        by rw [vars_setVar, if_pos rfl]; omega, ?_⟩, by simp⟩
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, harr, set_arrOf_eq_upd]
    · intro k hk
      rw [vars_setVar, if_pos rfl] at hk
      rcases Nat.lt_or_ge k (σ.vars "i") with hklt | hkge
      · rw [upd_of_ne _ (by omega)]; exact hcell k hklt
      · have : k = σ.vars "i" := by omega
        rw [this, upd_self]
    · exact hQfr σ _ hQ (fun y hy => by rw [vars_setVar, if_neg hy, vars_setArr])
        (fun b hb => by rw [arrs_setVar, arrs_setArr, if_neg hb])
  refine (((RamDriverOrder.forRangeZero' "i" bnd
    (fun σ => (∃ g, σ.arrs a = arrOf Na g ∧ ∀ k < σ.vars "i", g k = F k) ∧
      σ.vars "i" ≤ N ∧ Q σ) N (6 + e.size) hB
    (fun _ hσ => lt_of_le_of_lt hσ.2.1 hNB) (fun _ hσ => hbnd _ hσ.2.2)
    (fun _ hσ => hσ.2.1) hbody).pre ?_).post ?_).mono (le_of_eq (by ring))
  · rintro σ ⟨⟨g, harr⟩, hQ⟩
    refine ⟨⟨g, by rw [arrs_setVar]; exact harr, ?_⟩, by simp, ?_⟩
    · intro k hk; rw [vars_setVar, if_pos rfl] at hk; omega
    · exact hQfr σ _ hQ (fun y hy => by rw [vars_setVar, if_neg hy]) (fun _ _ => by
        rw [arrs_setVar])
  · rintro σ σ' - ⟨⟨⟨g, harr, hcell⟩, -, hQ⟩, hiN⟩
    exact ⟨⟨g, harr, fun k hk => hcell k (by rw [hiN]; exact hk)⟩, hiN, hQ⟩

/-- **A copy into a prefix of a longer array.** -/
theorem copyPrefix_spec {B : ℕ} (N Na Ns : ℕ) (src dst : String) (bnd : Expr) (g : ℕ → ℕ)
    (Q : Env → Prop) (hB : 0 < B) (hNB : N < B) (hNa : N ≤ Na) (hNs : N ≤ Ns)
    (hQfr : ∀ σ σ', Q σ → (∀ y, y ≠ "i" → σ'.vars y = σ.vars y) →
      (∀ b, b ≠ dst → σ'.arrs b = σ.arrs b) → Q σ')
    (hbnd : ∀ σ, Q σ → bnd.evalB B σ = some N)
    (hsrc : ∀ σ, Q σ → σ.arrs src = arrOf Ns g) (hgB : ∀ k < N, g k < B) :
    Spec B (fun σ => (∃ h, σ.arrs dst = arrOf Na h) ∧ Q σ)
      (copyUpto src dst bnd)
      (fun _ σ' => (∃ h, σ'.arrs dst = arrOf Na h ∧ ∀ k < N, h k = g k) ∧
        σ'.vars "i" = N ∧ Q σ')
      ((bnd.size + 11) * N + bnd.size + 5) :=
  (fillPrefix_spec N Na dst bnd (.get src (.var "i")) g Q hB hNB hNa hQfr hbnd
    (fun σ hQ hlt => evalB_get (evalB_var (by omega))
      (by rw [hsrc σ hQ, getElem?_arrOf g (by omega)]) (hgB _ hlt))).mono
    (le_of_eq (by simp only [size_get, size_var]; ring))

/-! ### Two readings of the cover's answer

The cluster arena occupies the member array only up to the write pointer
the pass left, so the block offsets are below it and the answer does not
depend on the array above it. Both are what makes the *partial* copy of
`RamDriver.coverSave` as good as the whole array. -/

section CoverAnswer

variable {n : ℕ} {G : SimpleGraph (Fin n)} {A₀ ord Xoff Xmem asg : ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)} {r m : ℕ}

/-- **Every block offset is below the arena's end.** -/
theorem coverOut_off_le (h : CoverOut G A₀ π ord r m Xoff Xmem asg) : ∀ k ≤ n, Xoff k ≤ m := by
  have key : ∀ d k, k + d = n → Xoff k ≤ Xoff n := by
    intro d
    induction d with
    | zero => intro k hk; rw [show k = n by omega]
    | succ d ih => intro k hk; exact le_trans (h.mono k (by omega)) (ih (k + 1) (by omega))
  intro k hk
  rw [← h.last]
  exact key (n - k) k (by omega)

/-- **The answer reads the member array only below the arena's end**, so
a copy of that prefix carries it. -/
theorem coverOut_congr {Xmem' : ℕ → ℕ} (h : CoverOut G A₀ π ord r m Xoff Xmem asg)
    (hX : ∀ p < m, Xmem' p = Xmem p) : CoverOut G A₀ π ord r m Xoff Xmem' asg := by
  have hblk : ∀ c < n, ∀ p, p < Xoff (c + 1) → p < m := fun c hc p hp =>
    lt_of_lt_of_le hp (coverOut_off_le h (c + 1) (by omega))
  refine ⟨h.zero, h.last, h.mono, fun p hp => by rw [hX p hp]; exact h.mem_lt p hp,
    fun c hc w => ?_, fun c hc p q hp₁ hp₂ hq₁ hq₂ he => ?_,
    fun c hc p q hp₁ hpq hq => ?_, h.asg_lt, h.asg_cover⟩
  · rw [← h.block c hc w]
    constructor
    · rintro ⟨p, hp1, hp2, hp3⟩
      exact ⟨p, hp1, hp2, by rw [← hX p (hblk c hc p hp2)]; exact hp3⟩
    · rintro ⟨p, hp1, hp2, hp3⟩
      exact ⟨p, hp1, hp2, by rw [hX p (hblk c hc p hp2)]; exact hp3⟩
  · refine h.block_inj c hc p q hp₁ hp₂ hq₁ hq₂ ?_
    rw [← hX p (hblk c hc p hp₂), ← hX q (hblk c hc q hq₂)]
    exact he
  · rw [hX p (hblk c hc p (by omega)), hX q (hblk c hc q hq)]
    exact h.block_mono c hc p q hp₁ hpq hq

end CoverAnswer

/-! ### The cover phase

`RamDriver.coverPhase` is the depth's ordering into the name the pass
reads, the depth's mask into the name it destroys,
`RamCover.coverCom` — whose walk is landed as
`RamDriverOrder.coverPass_spec`, with no obligation left in it — and the
four copies of `RamDriver.coverSave` that make the answers the depth's
own.

The only clause of the level's state the pass touches is none: it writes
`ord`, `alv`, `asg`, `xoff`, `xmem`, the two scratch arrays of the
search, and the depth's own four names, and `RamDriver.LevelPre` speaks
about none of them except through `LevelMem` and `DepthMem`, which are
lengths. So the whole clause crosses the phase by `levelPre_run`. -/

theorem warrs_copyUpto (src dst : String) (bnd : Expr) :
    (copyUpto src dst bnd).warrs = [dst] := rfl

theorem wvars_copyUpto (src dst : String) (bnd : Expr) :
    (copyUpto src dst bnd).wvars = ["i", "i"] := rfl

theorem warrs_copyCom (src dst : String) : (copyCom src dst).warrs = [dst] := rfl

theorem wvars_copyCom (src dst : String) : (copyCom src dst).wvars = ["i", "i"] := rfl

theorem wvars_coverCom (r : ℕ) : (RamCover.coverCom r).wvars =
    ["i", "i", "xp", "c", "src",
      "sent", "d", "one", "i", "head", "a", "tl", "v", "dv", "dv1", "k0", "v1", "kend",
      "u", "au", "du",
      "i", "a", "tl", "tl", "v", "dv", "head", "dv1", "k0", "v1", "kend", "u", "au",
      "du", "tl", "k0",
      "z", "dz", "xp", "z", "c"] := rfl

theorem warrs_coverCom (r : ℕ) : (RamCover.coverCom r).warrs =
    ["asg", "xoff", "dist", "dist", "q", "dist", "q", "xmem", "asg", "alv", "xoff"] := rfl

theorem ordName_notMem_coverPhase (cap j a : ℕ) : ordName a ∉ (coverPhase cap j).warrs := by
  rw [warrs_coverPhase]
  simp [ordName, xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem noWrite_coverPhase (cap j : ℕ) : (coverPhase cap j).NoWrite := by
  simp [coverPhase, coverSave, compactCom, copyCom, copyUpto, fillUpto, RamCover.coverCom,
    RamCover.initAsg, RamCover.centreStep, RamCover.emitLoop, RamCover.emitSlot,
    Refine.BfsBridge.bfsQCom, Refine.BfsBridge.bfsSetup, Com.NoWrite,
    Lax13Proofs.Refine.Codegen.noWrite_embed]

/-! ### The compaction scan

**Rebase B3.** `RamDriver.compactCom` is the last pass of the cover
phase: one scan of the depth's own block offsets, listing the positions
whose block is nonempty. The level's centre loop iterates that list
instead of the carrier, which is what takes the recursion's turn count
off `n` and onto the arena's mass.

The invariant is the obvious one — below the counter, every position
with a nonempty block has been listed, in increasing order — with one
clause that is not obvious and is the whole point: **the count never
overtakes the block offsets**, `cnum ≤ Xoff i`. Each listed position
contributes at least one member, and the members of the positions below
`i` all sit below `Xoff i`; at the exit `i = n` that reads
`cnum ≤ Xoff n = mm`. -/

/-- The invariant of `RamDriver.compactCom`. **Rebase B8:** the two
arrays the aliveness test reads, and the aliveness of every listed
position, join it. -/
def CompInv (n j : ℕ) (M ord Xoff : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs (xofName j) = arrOf (n + 1) Xoff ∧
    σ.arrs (alvName j) = arrOf n M ∧ σ.arrs (ordName j) = arrOf n ord ∧ σ.vars "i" ≤ n ∧
    ∃ cps : ℕ → ℕ, σ.arrs (cpsName j) = arrOf n cps ∧
      σ.vars (cnumName j) ≤ σ.vars "i" ∧ σ.vars (cnumName j) ≤ Xoff (σ.vars "i") ∧
      (∀ k < σ.vars (cnumName j), cps k < σ.vars "i" ∧ Xoff (cps k) < Xoff (cps k + 1) ∧
        M (ord (cps k)) ≠ 0) ∧
      (∀ k k' : ℕ, k < k' → k' < σ.vars (cnumName j) → cps k < cps k') ∧
      (∀ c < σ.vars "i", Xoff c < Xoff (c + 1) → M (ord c) ≠ 0 →
        ∃ k < σ.vars (cnumName j), cps k = c)

theorem cpsName_ne_xofName (j a : ℕ) : cpsName j ≠ xofName a := by
  simp [cpsName, xofName, String.ext_iff]

/-- **One turn of the compaction scan.** The block at the counter is
tested for emptiness and its centre for aliveness; if it is neither empty
nor dead the position is appended to the list and the count goes up.

**Rebase B8.** The inner test is the whole point of the pass: it is what
takes the level's turn count off the carrier and onto the *arena*
(`Refine.ArenaBlock.cnum_le_arenaSize`). The dead positions it drops are
the ones whose rows `RamDriver.sweepCom` has already written. -/
theorem compact_body {B n j : ℕ} {M ord Xoff : ℕ → ℕ}
    (hnB : n < B) (hmono : ∀ c < n, Xoff c ≤ Xoff (c + 1))
    (hXB : ∀ k < n + 1, Xoff k < B) (hordlt : ∀ z < n, ord z < n)
    (hMB : ∀ z < n, M z < B) :
    Spec B (fun σ => CompInv n j M ord Xoff σ ∧ σ.vars "i" < n)
      (.seq
        (.ite (.lt (.get (xofName j) (.var "i"))
            (.get (xofName j) (.add (.var "i") (.lit 1))))
          (.ite (.lt (.lit 0) (.get (alvName j) (.get (ordName j) (.var "i"))))
            (.seq (.store (cpsName j) (.var (cnumName j)) (.var "i"))
              (.assign (cnumName j) (.add (.var (cnumName j)) (.lit 1))))
            .skip)
          .skip)
        (.assign "i" (.add (.var "i") (.lit 1))))
      (fun σ σ' => CompInv n j M ord Xoff σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 27 := by
  have hnq : ("n" : String) ≠ cnumName j := by simp [cnumName, String.ext_iff]
  have hiq : ("i" : String) ≠ cnumName j := by simp [cnumName, String.ext_iff]
  have hxc : xofName j ≠ cpsName j := by simp [xofName, cpsName, String.ext_iff]
  have hac : alvName j ≠ cpsName j := by simp [alvName, cpsName, String.ext_iff]
  have hoc : ordName j ≠ cpsName j := by simp [ordName, cpsName, String.ext_iff]
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hn, hxof, halv, hodr, -, cps, hcps, hcle, hcX, hcpslt, hcpsmono, hcov⟩, hlt⟩ := hσ
  have hiB : σ.vars "i" < B := by omega
  have hKB : σ.vars (cnumName j) < B := by omega
  have hordn : ord (σ.vars "i") < n := hordlt _ hlt
  have he1 : (Expr.get (xofName j) (.var "i")).evalB B σ = some (Xoff (σ.vars "i")) :=
    evalB_get (evalB_var hiB) (by rw [hxof]; exact getElem?_arrOf Xoff (by omega))
      (hXB _ (by omega))
  have hidx : (Expr.add (.var "i") (.lit 1)).evalB B σ = some (σ.vars "i" + 1) := by
    have h := evalB_bin (B := B) (σ := σ) (op := .add) (e := .var "i") (f := .lit 1)
      (evalB_var hiB) (evalB_lit (by omega)) (by simp only [Bop.apply_add]; omega)
    rw [Bop.apply_add] at h
    exact h
  have he2 : (Expr.get (xofName j) (.add (.var "i") (.lit 1))).evalB B σ
      = some (Xoff (σ.vars "i" + 1)) :=
    evalB_get hidx (by rw [hxof]; exact getElem?_arrOf Xoff (by omega)) (hXB _ (by omega))
  have he3 : (Expr.get (ordName j) (.var "i")).evalB B σ = some (ord (σ.vars "i")) :=
    evalB_get (evalB_var hiB) (by rw [hodr]; exact getElem?_arrOf ord (by omega))
      (lt_trans hordn hnB)
  have he4 : (Expr.get (alvName j) (.get (ordName j) (.var "i"))).evalB B σ
      = some (M (ord (σ.vars "i"))) :=
    evalB_get he3 (by rw [halv]; exact getElem?_arrOf M hordn) (hMB _ hordn)
  have hstep : ∀ τ : Env, τ.vars "i" = σ.vars "i" →
      Run B (.assign "i" (.add (.var "i") (.lit 1))) τ
        (τ.setVar "i" (σ.vars "i" + 1)) 4 := by
    intro τ hτ
    have h := Run.assign (B := B) (σ := τ) (x := "i") (e := .add (.var "i") (.lit 1))
      (evalB_bin (evalB_var (by rw [hτ]; exact hiB)) (evalB_lit (by omega))
        (by simp only [Bop.apply_add, hτ]; omega))
    rw [Bop.apply_add, hτ] at h
    exact h.congr (by simp)
  by_cases hne : Xoff (σ.vars "i") < Xoff (σ.vars "i" + 1)
  · have hcond : (Cond.lt (Expr.get (xofName j) (.var "i"))
        (Expr.get (xofName j) (.add (.var "i") (.lit 1)))).evalB B σ = some true := by
      rw [evalB_condLt he1 he2]; simp [hne]
    by_cases hal : M (ord (σ.vars "i")) = 0
    · -- the centre is dead: the position is skipped
      have hcond2 : (Cond.lt (Expr.lit 0)
          (Expr.get (alvName j) (.get (ordName j) (.var "i")))).evalB B σ = some false := by
        rw [evalB_condLt (evalB_lit (by omega)) he4]; simp [hal]
      refine ⟨_, _, (Run.ite_true hcond (Run.ite_false hcond2 Run.skip)).seq (hstep σ rfl),
        by simp, ?_, by simp⟩
      have hKρ : (σ.setVar "i" (σ.vars "i" + 1)).vars (cnumName j) = σ.vars (cnumName j) := by
        simp [Ne.symm hiq]
      have hIρ : (σ.setVar "i" (σ.vars "i" + 1)).vars "i" = σ.vars "i" + 1 := by simp
      refine ⟨by simp [hnq, hn], by simp [hxof], by simp [halv], by simp [hodr],
        by rw [hIρ]; omega, cps, by simp [hcps], by rw [hKρ, hIρ]; omega,
        by rw [hKρ, hIρ]; exact le_trans hcX (hmono _ (by omega)), ?_, ?_, ?_⟩
      · intro k hk
        rw [hKρ] at hk
        rw [hIρ]
        exact ⟨by have := (hcpslt k hk).1; omega, (hcpslt k hk).2.1, (hcpslt k hk).2.2⟩
      · intro k k' hkk hk'
        rw [hKρ] at hk'
        exact hcpsmono k k' hkk hk'
      · intro c hc hnec hala
        rw [hIρ] at hc
        rw [hKρ]
        refine hcov c ?_ hnec hala
        rcases Nat.lt_or_ge c (σ.vars "i") with h | h
        · exact h
        · exact absurd (show M (ord c) = 0 by rw [show c = σ.vars "i" by omega]; exact hal) hala
    · -- the block is not empty and the centre is alive: the position joins the list
      have hcond2 : (Cond.lt (Expr.lit 0)
          (Expr.get (alvName j) (.get (ordName j) (.var "i")))).evalB B σ = some true := by
        rw [evalB_condLt (evalB_lit (by omega)) he4]; simp; omega
      have hst : Run B (.store (cpsName j) (.var (cnumName j)) (.var "i")) σ
          (σ.setArr (cpsName j) (σ.vars (cnumName j)) (σ.vars "i")) (1 + 1 + 1) :=
        Run.store (evalB_var hKB) (evalB_var hiB) (by rw [hcps, length_arrOf]; omega)
      have hbump : Run B (.assign (cnumName j) (.add (.var (cnumName j)) (.lit 1)))
          (σ.setArr (cpsName j) (σ.vars (cnumName j)) (σ.vars "i"))
          ((σ.setArr (cpsName j) (σ.vars (cnumName j)) (σ.vars "i")).setVar (cnumName j)
            (σ.vars (cnumName j) + 1)) 4 := by
        have h := Run.assign (B := B)
          (σ := σ.setArr (cpsName j) (σ.vars (cnumName j)) (σ.vars "i")) (x := cnumName j)
          (e := .add (.var (cnumName j)) (.lit 1))
          (evalB_bin (evalB_var (by simpa using hKB)) (evalB_lit (by omega))
            (by simp only [Bop.apply_add, vars_setArr]; omega))
        rw [Bop.apply_add, vars_setArr] at h
        exact h.congr (by simp)
      have hi₂ : ((σ.setArr (cpsName j) (σ.vars (cnumName j)) (σ.vars "i")).setVar (cnumName j)
          (σ.vars (cnumName j) + 1)).vars "i" = σ.vars "i" := by simp [hiq]
      refine ⟨_, _,
        (Run.ite_true hcond (Run.ite_true hcond2 (hst.seq hbump))).seq (hstep _ hi₂), by simp,
        ?_, by simp⟩
      have hKρ : (((σ.setArr (cpsName j) (σ.vars (cnumName j)) (σ.vars "i")).setVar
          (cnumName j) (σ.vars (cnumName j) + 1)).setVar "i" (σ.vars "i" + 1)).vars
          (cnumName j) = σ.vars (cnumName j) + 1 := by simp [Ne.symm hiq]
      have hIρ : (((σ.setArr (cpsName j) (σ.vars (cnumName j)) (σ.vars "i")).setVar
          (cnumName j) (σ.vars (cnumName j) + 1)).setVar "i" (σ.vars "i" + 1)).vars "i"
          = σ.vars "i" + 1 := by simp
      refine ⟨by simp [hnq, hn], by simp [hxc, hxof], by simp [hac, halv], by simp [hoc, hodr],
        by rw [hIρ]; omega,
        fun k => if k = σ.vars (cnumName j) then σ.vars "i" else cps k,
        by simp [hcps, set_arrOf], by rw [hKρ, hIρ]; omega,
        by rw [hKρ, hIρ]; omega, ?_, ?_, ?_⟩
      · intro k hk
        rw [hKρ] at hk
        rw [hIρ]
        by_cases hkK : k = σ.vars (cnumName j)
        · subst hkK
          refine ⟨by simp, ?_, ?_⟩
          · simp only [if_pos rfl]; exact hne
          · simp only [if_pos rfl]; exact hal
        · have h₁ := (hcpslt k (by omega)).1
          have h₂ := (hcpslt k (by omega)).2.1
          have h₃ := (hcpslt k (by omega)).2.2
          refine ⟨by simp only [if_neg hkK]; omega, ?_, ?_⟩
          · simp only [if_neg hkK]; exact h₂
          · simp only [if_neg hkK]; exact h₃
      · intro k k' hkk hk'
        rw [hKρ] at hk'
        by_cases hk'K : k' = σ.vars (cnumName j)
        · have h₁ := (hcpslt k (by omega)).1
          simp only [if_pos hk'K, if_neg (show k ≠ σ.vars (cnumName j) by omega)]
          omega
        · simp only [if_neg hk'K, if_neg (show k ≠ σ.vars (cnumName j) by omega)]
          exact hcpsmono k k' hkk (by omega)
      · intro c hc hnec hala
        rw [hIρ] at hc
        rw [hKρ]
        by_cases hci : c = σ.vars "i"
        · refine ⟨σ.vars (cnumName j), by omega, ?_⟩
          simp only [if_pos rfl]
          exact hci.symm
        · obtain ⟨k, hk, hkc⟩ := hcov c (by omega) hnec hala
          refine ⟨k, by omega, ?_⟩
          simp only [if_neg (show k ≠ σ.vars (cnumName j) by omega)]
          exact hkc
  · -- the block is empty: the position is skipped
    have hle : Xoff (σ.vars "i" + 1) = Xoff (σ.vars "i") :=
      le_antisymm (by omega) (hmono _ (by omega))
    have hcond : (Cond.lt (Expr.get (xofName j) (.var "i"))
        (Expr.get (xofName j) (.add (.var "i") (.lit 1)))).evalB B σ = some false := by
      rw [evalB_condLt he1 he2]; simp [hne]
    refine ⟨_, _, (Run.ite_false hcond Run.skip).seq (hstep σ rfl), by simp, ?_, by simp⟩
    have hKρ : (σ.setVar "i" (σ.vars "i" + 1)).vars (cnumName j) = σ.vars (cnumName j) := by
      simp [Ne.symm hiq]
    have hIρ : (σ.setVar "i" (σ.vars "i" + 1)).vars "i" = σ.vars "i" + 1 := by simp
    refine ⟨by simp [hnq, hn], by simp [hxof], by simp [halv], by simp [hodr],
      by rw [hIρ]; omega, cps,
      by simp [hcps], by rw [hKρ, hIρ]; omega, by rw [hKρ, hIρ, hle]; exact hcX, ?_, ?_, ?_⟩
    · intro k hk
      rw [hKρ] at hk
      rw [hIρ]
      exact ⟨by have := (hcpslt k hk).1; omega, (hcpslt k hk).2.1, (hcpslt k hk).2.2⟩
    · intro k k' hkk hk'
      rw [hKρ] at hk'
      exact hcpsmono k k' hkk hk'
    · intro c hc hnec hala
      rw [hIρ] at hc
      rw [hKρ]
      refine hcov c ?_ hnec hala
      rcases Nat.lt_or_ge c (σ.vars "i") with h | h
      · exact h
      · exact absurd (show Xoff (σ.vars "i") < Xoff (σ.vars "i" + 1) by
          rw [show σ.vars "i" = c by omega]; exact hnec) hne

/-- The cost of the compaction scan: one carrier-width pass, whose turn
is a two-sided test and, at most, a store and two increments. -/
def compactCost (n : ℕ) : ℕ := 31 * n + 8

/-- **The compaction scan, discharged.** What it leaves is
`RamDriver.Compacted` at the depth's own two names — with the aliveness
clause of rebase B8, which is what makes the level's turn count a
statement about the *arena* and not about the carrier. -/
theorem compact_spec {B n j : ℕ} {M ord Xoff : ℕ → ℕ}
    (hnB : n < B) (hmono : ∀ c < n, Xoff c ≤ Xoff (c + 1))
    (hXB : ∀ k < n + 1, Xoff k < B) (hordlt : ∀ z < n, ord z < n)
    (hMB : ∀ z < n, M z < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs (xofName j) = arrOf (n + 1) Xoff ∧
        σ.arrs (alvName j) = arrOf n M ∧ σ.arrs (ordName j) = arrOf n ord ∧
        ∃ g : ℕ → ℕ, σ.arrs (cpsName j) = arrOf n g)
      (compactCom j)
      (fun _ σ' => σ'.vars "n" = n ∧ σ'.arrs (xofName j) = arrOf (n + 1) Xoff ∧
        ∃ cps : ℕ → ℕ, σ'.arrs (cpsName j) = arrOf n cps ∧
          Compacted n (σ'.vars (cnumName j)) (Xoff n) M ord Xoff cps)
      (compactCost n) := by
  have hnq : ("n" : String) ≠ cnumName j := by simp [cnumName, String.ext_iff]
  have hiq : ("i" : String) ≠ cnumName j := by simp [cnumName, String.ext_iff]
  have hloop := Spec.forRangeZero (B := B) "i" "n" (CompInv n j M ord Xoff) n 27 hnB
    (fun _ hτ => hτ.2.2.2.2.1) (fun _ hτ => hτ.1)
    (compact_body hnB hmono hXB hordlt hMB)
  refine (Spec.seq (Spec.assign (B := B) (P := fun σ => σ.vars "n" = n ∧
        σ.arrs (xofName j) = arrOf (n + 1) Xoff ∧ σ.arrs (alvName j) = arrOf n M ∧
        σ.arrs (ordName j) = arrOf n ord ∧ ∃ g : ℕ → ℕ, σ.arrs (cpsName j) = arrOf n g)
      (x := cnumName j) (e := .lit 0) (f := fun _ => 0)
      (fun _ _ => evalB_lit (by omega)))
    hloop ?_ ?_).mono (by rw [compactCost]; simp only [size_lit]; omega)
  · -- the invariant holds once both counters are zeroed
    rintro σ σ' ⟨hn, hxof, halv, hodr, g, hg⟩ rfl
    refine ⟨by simp [hnq, hn], by simpa using hxof, by simpa using halv, by simpa using hodr,
      by simp, g, by simpa using hg,
      by simp [Ne.symm hiq], by simp [Ne.symm hiq], ?_, ?_, ?_⟩
    · intro k hk; simp [Ne.symm hiq] at hk
    · intro k k' _ hk'; simp [Ne.symm hiq] at hk'
    · intro c hc; simp at hc
  · rintro σ σ' σ'' - -
      ⟨⟨hn'', hxof'', -, -, -, cps, hcps, hcle, hcX, hcpslt, hcpsmono, hcov⟩, hi''⟩
    rw [hi''] at hcle hcX hcpslt hcov
    exact ⟨hn'', hxof'', cps, hcps,
      ⟨hcX, hcle, fun k hk => (hcpslt k hk).1, hcpsmono, fun k hk => (hcpslt k hk).2.1,
        fun k hk => (hcpslt k hk).2.2, hcov⟩⟩

/-- The cost of the cover phase: the pass, the two copies that set it
up, the four of `RamDriver.coverSave` — the member copy charged at the
whole cluster arena — and the compaction scan. -/
def coverPhaseCost (n ns : ℕ) : ℕ :=
  RamCover.coverCost n ns + 12 * (n * n) + 81 * n + 56

/-- **The cover phase of a level, discharged.** -/
theorem coverImplements {n : ℕ} {B cap mb ns W j : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)} {ord : ℕ → ℕ} :
    CoverImplements B cap mb ns W j G O T M Gm C π ord (coverPhaseCost n ns) := by
  intro d hB hcsr hptr hexit _ hord
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hlev, hordarr, hordlt⟩ := hσ
  have hnB : n < B := hB.n_lt
  have hn1B : n + 1 < B := hB.succ_lt
  have hnsB : ns < B := hB.ns_lt
  have hrB : 2 * cap + 1 < B := by have := hB.arena; omega
  obtain ⟨hvn, hoff, htgt, halvj, -, -, hMB, -, -, hmem, hdep, -, hordmem, hpad0, -⟩ := id hlev
  -- (1) the depth's ordering into the name the pass reads
  obtain ⟨σ₁, hr₁, ⟨u₁, hu₁, hagr₁⟩, -, hvn₁, -⟩ :=
    (RamDriverCluster.copyCom_spec B n n (ordName j) "ord" ord
        (by simp [ordName, String.ext_iff]) hnB le_rfl
        (fun k hk => lt_trans (hordlt k hk) hnB)).run
      ⟨hmem.1.get (p := ("ord", n)) (by simp), hvn, hordarr⟩
  have hordA₁ : σ₁.arrs "ord" = arrOf n ord := hu₁.trans (RamDriverOrder.arrOf_congr hagr₁)
  have hmem₁ : LevelMem B n cap mb σ₁ := levelMem_run hr₁ hmem
  have hdep₁ : DepthMem n cap mb σ₁ := hdep.run hr₁
  have halv₁ : σ₁.arrs (alvName j) = arrOf n M := by
    rw [hr₁.frame_arr _ (by rw [warrs_copyCom]; simp [alvName, String.ext_iff])]
    exact halvj
  -- (2) the depth's mask into the name the pass destroys
  obtain ⟨σ₂, hr₂, ⟨u₂, hu₂, hagr₂⟩, -, hvn₂, -⟩ :=
    (RamDriverCluster.copyCom_spec B n n (alvName j) "alv" M (alvName_ne_alv j) hnB le_rfl
        hMB).run ⟨hmem₁.1.get (p := ("alv", n)) (by simp), hvn₁, halv₁⟩
  have halvA₂ : σ₂.arrs "alv" = arrOf n M := hu₂.trans (RamDriverOrder.arrOf_congr hagr₂)
  have hmem₂ : LevelMem B n cap mb σ₂ := levelMem_run hr₂ hmem₁
  have hdep₂ : DepthMem n cap mb σ₂ := hdep₁.run hr₂
  have hordA₂ : σ₂.arrs "ord" = arrOf n ord := by
    rw [hr₂.frame_arr _ (by rw [warrs_copyCom]; decide)]; exact hordA₁
  have hoff₂ : σ₂.arrs "off" = arrOf (n + 1) O := by
    rw [hr₂.frame_arr _ (by rw [warrs_copyCom]; decide),
      hr₁.frame_arr _ (by rw [warrs_copyCom]; decide)]
    exact hoff
  have htgt₂ : σ₂.arrs "tgt" = arrOf W T := by
    rw [hr₂.frame_arr _ (by rw [warrs_copyCom]; decide),
      hr₁.frame_arr _ (by rw [warrs_copyCom]; decide)]
    exact htgt
  -- (3) the pass, at the level's allocation width: the block structure
  -- occupies the first `ns` slots and the padding above it is zero, which
  -- is `RamCover.cover_specW`'s `hpad` wherever a centre turn runs
  obtain ⟨σ₃, hr₃, Xoff, Xmem, asg, m, hxoff₃, hxmem₃, hasg₃, hxp₃, hmle, hout⟩ :=
    (RamDriverOrder.coverPass_specWP (r := cap) (A₀ := M) (nt := W) hcsr hord hnB hnsB hrB
        hptr hMB hordmem.1 (RamDriver.pad_lt_of_zero hpad0)).run
      ⟨⟨hvn₂, hoff₂, htgt₂, halvA₂, hordA₂, hmem₂.1.get (p := ("dist", n)) (by simp),
        hmem₂.1.get (p := ("q", n)) (by simp), hmem₂.1.get (p := ("asg", n)) (by simp),
        hmem₂.1.get (p := ("xoff", n + 1)) (by simp),
        hmem₂.1.get (p := ("xmem", n * n)) (by simp)⟩, hmem₂.2.1, hmem₂.2.2⟩
  have hdep₃ : DepthMem n cap mb σ₃ := hdep₂.run hr₃
  have hvn₃ : σ₃.vars "n" = n := by
    rw [hr₃.frame_var "n" (by rw [wvars_coverCom]; decide)]; exact hvn₂
  -- the exit pointer, and with it every block offset below it, is a word:
  -- the second of the cover phase's two arena slots (rebase E-mem/W2)
  have hmB : m < B := hexit hout hmle
  have hXoffB : ∀ k < n + 1, Xoff k < B := fun k hk =>
    lt_of_le_of_lt (coverOut_off_le hout k (by omega)) hmB
  have hXmemB : ∀ k < m, Xmem k < B := fun k hk => lt_trans (hout.mem_lt k hk) hnB
  -- (4) the four copies that make the answers the depth's own
  obtain ⟨σ₄, hr₄, ⟨v₄, hv₄, hagr₄⟩, -, hvn₄, -⟩ :=
    (RamDriverOrder.copyUpto_spec (B := B) (n + 1) (n + 1) "xoff" (xofName j)
        (.add (.var "n") (.lit 1)) Xoff
        (fun τ => τ.vars "n" = n ∧ τ.arrs "xoff" = arrOf (n + 1) Xoff) (by omega) hn1B le_rfl
        (fun τ τ' hQ hv ha => ⟨by rw [hv "n" (by decide)]; exact hQ.1,
          by rw [ha "xoff" (by simp [xofName, String.ext_iff])]; exact hQ.2⟩)
        (fun τ hQ => by
          have h := evalB_bin (B := B) (σ := τ) (op := .add) (e := .var "n") (f := .lit 1)
            (evalB_var (by rw [hQ.1]; omega)) (evalB_lit (by omega))
            (by simp only [Bop.apply_add, hQ.1]; omega)
          rw [Bop.apply_add, hQ.1] at h
          exact h)
        (fun τ hQ => hQ.2) hXoffB).run
      ⟨hdep₃.get j (p := (xofName j, n + 1)) (by simp), hvn₃, hxoff₃⟩
  have hdep₄ : DepthMem n cap mb σ₄ := hdep₃.run hr₄
  have hxp₄ : σ₄.vars "xp" = m := by
    rw [hr₄.frame_var "xp" (by rw [wvars_copyUpto]; decide)]; exact hxp₃
  have hxmem₄ : σ₄.arrs "xmem" = arrOf (n * n) Xmem := by
    rw [hr₄.frame_arr _ (by rw [warrs_copyUpto]; simp [xofName, String.ext_iff])]
    exact hxmem₃
  obtain ⟨σ₅, hr₅, ⟨v₅, hv₅, hagr₅⟩, -, hxp₅, -⟩ :=
    (copyPrefix_spec (B := B) m (n * n) (n * n) "xmem" (xmmName j) (.var "xp") Xmem
        (fun τ => τ.vars "xp" = m ∧ τ.arrs "xmem" = arrOf (n * n) Xmem) (by omega) hmB hmle
        hmle
        (fun τ τ' hQ hv ha => ⟨by rw [hv "xp" (by decide)]; exact hQ.1,
          by rw [ha "xmem" (xmem_ne_xmmName j)]; exact hQ.2⟩)
        (fun τ hQ => by rw [← hQ.1]; exact evalB_var (by rw [hQ.1]; omega))
        (fun τ hQ => hQ.2) hXmemB).run
      ⟨hdep₄.get j (p := (xmmName j, n * n)) (by simp), hxp₄, hxmem₄⟩
  have hdep₅ : DepthMem n cap mb σ₅ := hdep₄.run hr₅
  have hvn₅ : σ₅.vars "n" = n := by
    rw [hr₅.frame_var "n" (by rw [wvars_copyUpto]; decide)]; exact hvn₄
  have hasg₅ : σ₅.arrs "asg" = arrOf n asg := by
    rw [hr₅.frame_arr _ (by rw [warrs_copyUpto]; simp [xmmName, String.ext_iff]),
      hr₄.frame_arr _ (by rw [warrs_copyUpto]; simp [xofName, String.ext_iff])]
    exact hasg₃
  obtain ⟨σ₆, hr₆, ⟨v₆, hv₆, hagr₆⟩, -, -, -⟩ :=
    (RamDriverCluster.copyCom_spec B n n "asg" (asgName j) asg
        (fun h => asgName_ne_asg j h.symm) hnB le_rfl
        (fun k hk => lt_trans (hout.asg_lt k hk) hnB)).run
      ⟨hdep₅.get j (p := (asgName j, n)) (by simp), hvn₅, hasg₅⟩
  have hxp₆ : σ₆.vars "xp" = m := by
    rw [hr₆.frame_var "xp" (by rw [wvars_copyCom]; decide)]; exact hxp₅
  have hr₇ : Run B (.assign (xpName j) (.var "xp")) σ₆ (σ₆.setVar (xpName j) m) (1 + 1) := by
    have h := Run.assign (B := B) (σ := σ₆) (x := xpName j) (e := .var "xp")
      (evalB_var (show σ₆.vars "xp" < B by rw [hxp₆]; omega))
    rw [hxp₆] at h
    simpa using h
  set ρ := σ₆.setVar (xpName j) m with hρ
  -- the cover's four answers, at the depth's own names, before the scan
  have hxofρ : ρ.arrs (xofName j) = arrOf (n + 1) Xoff := by
    rw [hρ, arrs_setVar,
      hr₆.frame_arr _ (by rw [warrs_copyCom]; simp [xofName, asgName, String.ext_iff]),
      hr₅.frame_arr _ (by rw [warrs_copyUpto]; simp [xofName, xmmName, String.ext_iff]), hv₄,
      RamDriverOrder.arrOf_congr hagr₄]
  have hxmmρ : ρ.arrs (xmmName j) = arrOf (n * n) v₅ := by
    rw [hρ, arrs_setVar,
      hr₆.frame_arr _ (by rw [warrs_copyCom]; simp [xmmName, asgName, String.ext_iff]), hv₅]
  have hasgρ : ρ.arrs (asgName j) = arrOf n asg := by
    rw [hρ, arrs_setVar, hv₆, RamDriverOrder.arrOf_congr hagr₆]
  have hxpρ : ρ.vars (xpName j) = m := by rw [hρ, vars_setVar, if_pos rfl]
  have hvnρ : ρ.vars "n" = n := by
    rw [hρ, vars_setVar, if_neg (by simp [xpName, String.ext_iff]),
      hr₆.frame_var "n" (by rw [wvars_copyCom]; decide)]
    exact hvn₅
  have hdepρ : DepthMem n cap mb ρ := (hdep₅.run hr₆).setVar _ _
  -- the compaction scan
  have halvρ : ρ.arrs (alvName j) = arrOf n M := by
    rw [hρ, arrs_setVar,
      hr₆.frame_arr _ (by rw [warrs_copyCom]; simp [alvName, asgName, String.ext_iff]),
      hr₅.frame_arr _ (by rw [warrs_copyUpto]; simp [alvName, xmmName, String.ext_iff]),
      hr₄.frame_arr _ (by rw [warrs_copyUpto]; simp [alvName, xofName, String.ext_iff]),
      hr₃.frame_arr _ (by
        rw [warrs_coverCom]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        push_neg
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first
            | exact alvName_ne_alv j
            | simp [alvName, String.ext_iff]),
      hr₂.frame_arr _ (by rw [warrs_copyCom]; simpa using alvName_ne_alv j),
      hr₁.frame_arr _ (by rw [warrs_copyCom]; simp [alvName, String.ext_iff])]
    exact halvj
  have hordρ : ρ.arrs (ordName j) = arrOf n ord := by
    rw [hρ, arrs_setVar,
      hr₆.frame_arr _ (by rw [warrs_copyCom]; simp [ordName, asgName, String.ext_iff]),
      hr₅.frame_arr _ (by rw [warrs_copyUpto]; simp [ordName, xmmName, String.ext_iff]),
      hr₄.frame_arr _ (by rw [warrs_copyUpto]; simp [ordName, xofName, String.ext_iff]),
      hr₃.frame_arr _ (by rw [warrs_coverCom]; simp [ordName, String.ext_iff]),
      hr₂.frame_arr _ (by rw [warrs_copyCom]; simp [ordName, String.ext_iff]),
      hr₁.frame_arr _ (by rw [warrs_copyCom]; simp [ordName, String.ext_iff])]
    exact hordarr
  obtain ⟨σ₈, hr₈, hvn₈, hxof₈, cps, hcps₈, hcompact⟩ :=
    (compact_spec (B := B) (j := j) hnB hout.mono hXoffB hordlt hMB).run
      (σ := ρ) ⟨hvnρ, hxofρ, halvρ, hordρ, hdepρ.get j (p := (cpsName j, n)) (by simp)⟩
  -- the phase, assembled
  have hrS : Run B (coverSave j) σ₃ ρ _ := hr₄.seq (hr₅.seq (hr₆.seq hr₇))
  refine ⟨σ₈, _,
    hr₁.seq (hr₂.seq (hr₃.seq (hrS.seq hr₈))), ?_, ?_⟩
  · rw [coverPhaseCost, compactCost]
    simp only [size_add, size_var, size_lit]
    have h12 : 12 * m ≤ 12 * (n * n) := Nat.mul_le_mul_left 12 hmle
    omega
  have hrT : Run B (coverPhase cap j) σ σ₈ _ :=
    hr₁.seq (hr₂.seq (hr₃.seq (hrS.seq hr₈)))
  refine ⟨levelPre_run hlev hrT (n_notMem_coverPhase cap j) (m_notMem_coverPhase cap j)
      (lw_notMem_coverPhase cap j) (off_notMem_coverPhase cap j) (tgt_notMem_coverPhase cap j)
      (alvName_notMem_coverPhase cap j j) (gamName_notMem_coverPhase cap j j)
      (fun q => colName_notMem_coverPhase cap j j q) (zero_notMem_coverPhase cap j)
      (memName_notMem_coverPhase cap j j) (mnumName_notMem_coverPhase cap j j),
    hrT.out_eq (noWrite_coverPhase cap j),
    fun a => hrT.frame_var _ (ctrName_notMem_coverPhase cap j a),
    fun a => hrT.frame_arr _ (gamName_notMem_coverPhase cap j a),
    Xoff, v₅, asg, cps, m, σ₈.vars (cnumName j),
    ⟨?_, hxof₈, ?_, ?_, ?_, hmle, hmB, hordlt, coverOut_congr hout hagr₅⟩,
    hcps₈, rfl, ?_⟩
  · rw [hrT.frame_arr _ (ordName_notMem_coverPhase cap j j)]; exact hordarr
  · rw [hr₈.frame_arr _ (by rw [warrs_compactCom]; simp [cpsName, xmmName, String.ext_iff])]
    exact hxmmρ
  · rw [hr₈.frame_arr _ (by rw [warrs_compactCom]; simp [cpsName, asgName, String.ext_iff])]
    exact hasgρ
  · rw [hr₈.frame_var _ (by rw [wvars_compactCom]; simp [xpName, cnumName, String.ext_iff])]
    exact hxpρ
  · rw [← hout.last]; exact hcompact

/-! ### The base case

`RamDriverBot.base_spec` is the walk; what is left is the translation
into the surface. Two halves. The frame of `RamDriver.LevelPre` across
the pass comes off the four syntactic lemmas of that file — the base
pass writes the depth's own tables and the generated evaluator's own
names, and `LevelPre` speaks about neither. (Before R1.8-T4a it also
wrote the representative table; the frame lemmas still carry that
alternative, vacuously — `RamDriverBot.rep_notMem_warrs_baseCom`.) And
the postcondition `RamDriverBot.BaseTabOk … (fun _ => n)` is
`RamDriver.TableInv`'s content on the edgeless arena, which is the arena
the obligation's hypothesis says this is.

The locality of the tabled formulas is not a hypothesis of the
obligation and does not have to be:
`Lax3Proofs.FormulaTables.tableRank_of_mem_tablesAt` is that every entry
of every table is local. -/

/-- A name below the base evaluator's output is below `"b"`. -/
theorem ext_b_of_ext_bb {a : String} (h : RamDriverBot.Ext "bb" a) :
    RamDriverBot.Ext "b" a :=
  (RamDriverBot.ext_of_prefix (by decide)).trans h

/-! The two member names begin with `'m'` (rebase E-mem), which is all
the base pass's frame needs: it writes the tables and the names below its
own output, neither of which starts there. -/

theorem head_memName (a : ℕ) : ∃ t, (memName a).toList = 'm' :: t :=
  ⟨_, by rw [memName, String.toList_append]; rfl⟩

theorem head_mnumName (a : ℕ) : ∃ t, (mnumName a).toList = 'm' :: t :=
  ⟨_, by rw [mnumName, String.toList_append]; rfl⟩

theorem not_ext_bb_memName (a : ℕ) : ¬ RamDriverBot.Ext "bb" (memName a) := fun h =>
  RamDriverBot.not_ext_b_of_cons (y := memName a)
    (by rw [memName, String.toList_append]; rfl) (by decide) (ext_b_of_ext_bb h)

theorem not_ext_bb_mnumName (a : ℕ) : ¬ RamDriverBot.Ext "bb" (mnumName a) := fun h =>
  RamDriverBot.not_ext_b_of_cons (y := mnumName a)
    (by rw [mnumName, String.toList_append]; rfl) (by decide) (ext_b_of_ext_bb h)

/-- The three ways an array can escape the base pass's writes. -/
theorem notMem_warrs_baseCom {q_top cap mb ℓ : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ ℓ, IsLocal β) {a : String}
    (h1 : a ≠ "rep") (h2 : ∀ i, a ≠ tabName ℓ i) (h3 : ¬ RamDriverBot.Ext "bb" a) :
    a ∉ (baseCom q_top cap mb ℓ φ).warrs := fun ha => by
  rcases RamDriverBot.warrs_baseCom hlocal a ha with h | ⟨i, h⟩ | h
  · exact h1 h
  · exact h2 i h
  · exact h3 h

/-- And the three ways a scalar can. -/
theorem notMem_wvars_baseCom {q_top cap mb ℓ : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ ℓ, IsLocal β) {y : String}
    (h1 : y ∉ ["rp", "z", "seen", "rw", "rv"]) (h2 : ∀ i, y ≠ envName i)
    (h3 : ¬ RamDriverBot.Ext "bb" y) :
    y ∉ (baseCom q_top cap mb ℓ φ).wvars := fun hy => by
  rcases RamDriverBot.wvars_baseCom hlocal y hy with h | ⟨i, h⟩ | h
  · exact h1 h
  · exact h2 i h
  · exact h3 h

/-- **The base case of the driver, discharged.** -/
theorem baseImplements {n : ℕ} {B q_top cap mb ns W ℓ : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} :
    BaseImplements B q_top cap mb ns W ℓ φ G O T M Gm C
      (RamDriverBot.baseCost q_top cap mb ℓ n φ) := by
  -- R1.8-T4a: the `2 ^ sigL cap mb ℓ < B` hypothesis of the obligation and
  -- the `Sized [("rep", …)]` clause of `BaseArrs` are the representative
  -- scan's, and the scan is out of the program — `base_spec` asks for
  -- neither, so both go unused here.
  intro d hB _ hbot hbit
  have hlocal : ∀ β ∈ tablesAt q_top cap mb φ ℓ, IsLocal β :=
    fun β hβ => (FormulaTables.tableRank_of_mem_tablesAt ℓ β hβ).1
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hlev, hts, hbarr⟩ := hσ
  obtain ⟨σ', hrun, htab⟩ :=
    (RamDriverBot.base_spec hB.one_lt hB.n_lt hbit hlocal).run
      ⟨hlev.1, hlev.2.2.2.2.2.1, hbarr.2 ℓ, fun i hi => hts.get ℓ hi⟩
  refine ⟨σ', _, hrun, le_rfl,
    ⟨levelPre_run hlev hrun
      (notMem_wvars_baseCom hlocal (by decide) (fun i => RamDriverBot.lit_ne_envName
        ⟨_, rfl⟩ (by decide) i) (RamDriverBot.not_ext_of_not_prefix (by decide)))
      (notMem_wvars_baseCom hlocal (by decide) (fun i => RamDriverBot.lit_ne_envName
        ⟨_, rfl⟩ (by decide) i) (RamDriverBot.not_ext_of_not_prefix (by decide)))
      (notMem_wvars_baseCom hlocal (by decide) (fun i => RamDriverBot.lit_ne_envName
        ⟨_, rfl⟩ (by decide) i) (RamDriverBot.not_ext_of_not_prefix (by decide)))
      (notMem_warrs_baseCom hlocal (by decide)
        (fun i => RamDriverBase.lit_ne_tabName (by decide) ℓ i)
        (RamDriverBot.not_ext_of_not_prefix (by decide)))
      (notMem_warrs_baseCom hlocal (by decide)
        (fun i => RamDriverBase.lit_ne_tabName (by decide) ℓ i)
        (RamDriverBot.not_ext_of_not_prefix (by decide)))
      (notMem_warrs_baseCom hlocal (RamDriverBot.alvName_ne_rep ℓ)
        (fun i => RamDriverBot.alvName_ne_tabName ℓ ℓ i)
        (fun h => RamDriverBot.not_ext_b_alvName ℓ (ext_b_of_ext_bb h)))
      (notMem_warrs_baseCom hlocal (RamDriverBot.gamName_ne_rep ℓ)
        (fun i => RamDriverBot.gamName_ne_tabName ℓ ℓ i)
        (fun h => RamDriverBot.not_ext_b_gamName ℓ (ext_b_of_ext_bb h)))
      (fun q => notMem_warrs_baseCom hlocal (RamDriverBot.colName_ne_rep ℓ q)
        (fun i => RamDriverBot.colName_ne_tabName ℓ q ℓ i)
        (fun h => RamDriverBot.not_ext_b_colName ℓ q (ext_b_of_ext_bb h)))
      (fun a ha => by
        simp only [zeroArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact notMem_warrs_baseCom hlocal (by decide)
            (fun i => RamDriverBase.lit_ne_tabName (by decide) ℓ i)
            (RamDriverBot.not_ext_of_not_prefix (by decide)))
      (notMem_warrs_baseCom hlocal
        (RamDriverBot.ne_of_head_ne (head_memName ℓ) ⟨_, rfl⟩ (by decide))
        (fun i => RamDriverBot.ne_of_head_ne (head_memName ℓ)
          (RamDriverBot.head_tabName ℓ i) (by decide))
        (not_ext_bb_memName ℓ))
      (notMem_wvars_baseCom hlocal (by simp [mnumName, String.ext_iff])
        (fun i => RamDriverBot.lit_ne_envName (head_mnumName ℓ) (by decide) i)
        (not_ext_bb_mnumName ℓ)),
      hts.run hrun, ?_⟩,
    hrun.out_eq (RamDriverBot.noWrite_baseCom q_top cap mb ℓ φ)⟩
  intro i hi
  obtain ⟨Tb, hTb, hval⟩ := htab i hi
  exact ⟨Tb, hTb, fun v hv => (hval ⟨v, hv⟩ hv).1,
    fun v => by rw [hbot]; exact (hval v v.isLt).2⟩


/-! ### The elimination's rank bound

`Lax3Proofs.RamElim.ElimMem` — and so `RamElim.ElimPost` — does **not**
say that the ranks it leaves are vertex numbers, and nothing in it
implies that: `RamElim.ElimCert` is invariant under any order-preserving
relabelling of the rank, so `ρ` and `100·ρ` satisfy the whole of it
alike. The elimination's own walk knows better — `RamElim.AfterLoop` and
`RamElim.AfterOff` both carry `∀ v < n, R v < n`, and
`RamElim.elimLoop_spec` produces it — but the last phase drops it on the
way out.

`RamDriver.ordCom` cannot do without it: it stores at the index
`rnk[z]`, and an out-of-range store has no derivation, so the ordering
phase has *no run* unless the rank is bounded. So the five phase walks
are sequenced again here, with the clause kept. Nothing of the engine is
re-proved — `initDeg_spec`, `initBuck_spec`, `elimLoop_spec`,
`offPass_spec` and `fillPass_spec` are used exactly as
`RamElim.implements` uses them, against the same four predicates — and
the only difference is the last phase's postcondition, which keeps the
rank array and its bound (and its injectivity, so that a caller reading
both gets them for *one* function rather than two that happen to agree
below `n`).

**Defect record.** The proper repair is one conjunct in
`RamElim.ElimMem`, which `RamElim.implements`'s own `w5` has in hand.
The engines are frozen for this wave, so it is done here instead; a wave
that may edit `RamElim` should move it there and delete this. -/

variable {n : ℕ}

/-- **The elimination, with the rank bound its own surface drops — at
the widened input surface** (rebase F-c-2). The bridge is re-sequenced
from the engine's *widened* phase walks (`RamElim.initDeg_specW`,
`RamElim.elimLoop_specW`, `RamElim.fillPass_specW`, against the
`AfterXW` predicates), so the block structure it reads may live in a
target array wider than the call's own slot count.

That is what the ordering phase's *second* elimination needs: what it
eliminates is the symmetrization's `RamElim.CsrSimple (D R).toGraph
(m + m)`, whose slot count is the chain's arc count and not the
level's, while the array it sits in is the one the level allocated.
Nothing else moves — the three answers and the cost are the pinned
bridge's, which is now this one at `nt = ns`.

The counterpart on the round's side is
`RamDriverAugment.elimCert_specW`, which keeps the *certificate*
instead of the injectivity; the two die together with the same defect
record. -/
theorem elimRank_specW {B ns nt W : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}
    (hcsr : CsrSimple G ns O T) (hB : n + ns + 1 < B) (hMB : ∀ z < n, M z < B) (hW : ns ≤ W)
    (hnt : ns ≤ nt) :
    Spec B (ElimPreW n ns nt W O T M) elimCom
      (fun σ σ' => ElimPost G M ns W σ σ' ∧
        ∃ R, σ'.arrs "rnk" = arrOf n R ∧ (∀ v < n, R v < n) ∧
          Function.Injective (fun v : Fin n => R (v : ℕ)))
      (elimCost n ns) := by
  have hDlt : ∀ v < n, adeg G M v < n := fun v hv => by
    rw [RamElim.adeg_eq hv]; exact RamElim.card_nbrsIn_lt _ _
  have w1 : Spec B (ElimPreW n ns nt W O T M) RamElim.initDeg
      (fun _ σ' => AfterDegW n ns nt W G O T M σ') (48 * n + 44 * ns + 10) := by
    intro σ hσ
    obtain ⟨hn, hoff, htgt, halv, hdeg0, helm, hrnk, hidg, hbh, hbv, hbn, hioff, hifl,
      hitg⟩ := hσ
    obtain ⟨σ', hrun, ⟨hI, hi⟩, -, hfa, -, -⟩ :=
      (RamElim.initDeg_specW B n ns nt G O T M hcsr (by omega) (by omega) hnt hMB).frame σ
        ⟨hn, hoff, htgt, halv, hdeg0⟩
    obtain ⟨hn', hoff', htgt', halv', -, g, hdegg, hg⟩ := hI
    obtain ⟨e, he1, he2⟩ := helm
    obtain ⟨r, hr1⟩ := hrnk
    obtain ⟨d, hd1⟩ := hidg
    obtain ⟨bh, hbh1, hbh2⟩ := hbh
    obtain ⟨bv, hbv1⟩ := hbv
    obtain ⟨bn, hbn1⟩ := hbn
    obtain ⟨io, hio1⟩ := hioff
    obtain ⟨fl, hfl1⟩ := hifl
    obtain ⟨tg, htg1⟩ := hitg
    exact ⟨σ', hrun, hn', hoff', htgt', halv',
      by rw [hdegg, RamDriverOrder.arrOf_congr (fun j hj => hg j (by rw [hi]; exact hj))],
      ⟨e, by rw [hfa "elm" (by decide)]; exact he1, he2⟩,
      ⟨r, by rw [hfa "rnk" (by decide)]; exact hr1⟩,
      ⟨d, by rw [hfa "idg" (by decide)]; exact hd1⟩,
      ⟨bh, by rw [hfa "bh" (by decide)]; exact hbh1, hbh2⟩,
      ⟨bv, by rw [hfa "bv" (by decide)]; exact hbv1⟩,
      ⟨bn, by rw [hfa "bn" (by decide)]; exact hbn1⟩,
      ⟨io, by rw [hfa "ioff" (by decide)]; exact hio1⟩,
      ⟨fl, by rw [hfa "ifl" (by decide)]; exact hfl1⟩,
      ⟨tg, by rw [hfa "itg" (by decide)]; exact htg1⟩⟩
  have w2 : Spec B (AfterDegW n ns nt W G O T M) RamElim.initBuck
      (fun _ σ' => AfterBuckW n ns nt W G O T M σ') (29 * n + 10) := by
    intro σ hσ
    obtain ⟨hn, hoff, htgt, halv, hdeg, helm, hrnk, hidg, hbh, hbv, hbn, hioff, hifl,
      hitg⟩ := hσ
    obtain ⟨σ', hrun, ⟨hI, hi⟩, -, hfa, -, -⟩ :=
      (RamElim.initBuck_spec B n W (adeg G M) (by omega) hDlt).frame σ ⟨hn, hdeg, hbh, hbv, hbn⟩
    obtain ⟨e, he1, he2⟩ := helm
    obtain ⟨r, hr1⟩ := hrnk
    obtain ⟨d, hd1⟩ := hidg
    obtain ⟨io, hio1⟩ := hioff
    obtain ⟨fl, hfl1⟩ := hifl
    obtain ⟨tg, htg1⟩ := hitg
    exact ⟨σ', hrun, hI, hi,
      by rw [hfa "off" (by decide)]; exact hoff,
      by rw [hfa "tgt" (by decide)]; exact htgt,
      by rw [hfa "alv" (by decide)]; exact halv,
      ⟨e, by rw [hfa "elm" (by decide)]; exact he1, he2⟩,
      ⟨r, by rw [hfa "rnk" (by decide)]; exact hr1⟩,
      ⟨d, by rw [hfa "idg" (by decide)]; exact hd1⟩,
      ⟨io, by rw [hfa "ioff" (by decide)]; exact hio1⟩,
      ⟨fl, by rw [hfa "ifl" (by decide)]; exact hfl1⟩,
      ⟨tg, by rw [hfa "itg" (by decide)]; exact htg1⟩⟩
  have w3 : Spec B (AfterBuckW n ns nt W G O T M) RamElim.elimLoop
      (fun _ σ' => AfterLoopW n ns nt W G O T M σ') (160 * n + 100 * ns + 52) := by
    intro σ hσ
    obtain ⟨hbi, hi, hoff, htgt, halv, helm, hrnk, hidg, hioff, hifl, hitg⟩ := hσ
    obtain ⟨σ', hrun, ⟨R, ID, k, hn', hk', hrnk', hidg', hRlt, hcert, hIDc, hpsum⟩, -,
      hfa, -, -⟩ :=
      (RamElim.elimLoop_specW B n ns nt W G O T M (adeg G M) hcsr hB hW hnt hMB
        (fun _ _ => rfl)).frame σ ⟨hbi, hi, hoff, htgt, halv, helm, hrnk, hidg⟩
    obtain ⟨io, hio1⟩ := hioff
    obtain ⟨fl, hfl1⟩ := hifl
    obtain ⟨tg, htg1⟩ := hitg
    exact ⟨σ', hrun, R, ID, k, hn', hk',
      by rw [hfa "off" (by decide)]; exact hoff,
      by rw [hfa "tgt" (by decide)]; exact htgt,
      by rw [hfa "alv" (by decide)]; exact halv,
      hrnk', hidg', hRlt, hcert, hIDc, hpsum,
      ⟨io, by rw [hfa "ioff" (by decide)]; exact hio1⟩,
      ⟨fl, by rw [hfa "ifl" (by decide)]; exact hfl1⟩,
      ⟨tg, by rw [hfa "itg" (by decide)]; exact htg1⟩⟩
  have w4 : Spec B (AfterLoopW n ns nt W G O T M) RamElim.offPass
      (fun _ σ' => AfterOffW n ns nt W G O T M σ') (24 * n + 12) := by
    intro σ hσ
    obtain ⟨R, ID, k, hn, hk, hoff, htgt, halv, hrnk, hidg, hRlt, hcert, hIDc, hpsum,
      hioff, hifl, hitg⟩ := hσ
    obtain ⟨σ', hrun, ⟨hn', hs', hio', hfl'⟩, hfv, hfa, -, -⟩ :=
      (RamElim.offPass_spec B n ID (by omega) (by omega)).frame σ ⟨hn, hidg, hioff, hifl⟩
    obtain ⟨tg, htg1⟩ := hitg
    exact ⟨σ', hrun, R, ID, k, hn', by rw [hfv "kmax" (by decide)]; exact hk,
      by rw [hfa "off" (by decide)]; exact hoff,
      by rw [hfa "tgt" (by decide)]; exact htgt,
      by rw [hfa "alv" (by decide)]; exact halv,
      by rw [hfa "rnk" (by decide)]; exact hrnk,
      hRlt, hcert, hIDc, hpsum, hio', hfl',
      ⟨tg, by rw [hfa "itg" (by decide)]; exact htg1⟩⟩
  have w5 : Spec B (AfterOffW n ns nt W G O T M) RamElim.fillPass
      (fun _ σ' => ElimMem G M ns W σ' σ' ∧
        ∃ R, σ'.arrs "rnk" = arrOf n R ∧ (∀ v < n, R v < n) ∧
          Function.Injective (fun v : Fin n => R (v : ℕ)))
      (32 * n + 32 * ns + 10) := by
    intro σ hσ
    obtain ⟨R, ID, k, hn, hk, hoff, htgt, halv, hrnk, hRlt, hcert, hIDc, hpsum, hioff,
      hifl, hitg⟩ := hσ
    obtain ⟨g, hioffg, hioffv⟩ := hioff
    obtain ⟨σ', hrun, ⟨IT, hitg', harcs⟩, hfv, hfa, -, -⟩ :=
      (RamElim.fillPass_specW B n ns nt W G O T M R ID hcsr hB hW hnt hMB hRlt hIDc
        hpsum).frame σ ⟨hn, hoff, htgt, halv, hrnk, hifl, hitg⟩
    have hrnk' : σ'.arrs "rnk" = arrOf n R := by
      rw [hfa "rnk" (by decide)]; exact hrnk
    exact ⟨σ', hrun, ⟨R, RamElim.psum ID, IT, k, RamElim.psum ID n, hrnk',
      by rw [hfv "kmax" (by decide)]; exact hk,
      by rw [hfa "ioff" (by decide), hioffg]
         exact RamDriverOrder.arrOf_congr (fun j hj => hioffv j (by omega)),
      hitg', by omega, ⟨hcert, harcs⟩⟩, R, hrnk', hRlt, hcert.inj⟩
  have hall : Spec B (ElimPreW n ns nt W O T M) elimCom
      (fun _ σ' => ElimMem G M ns W σ' σ' ∧
        ∃ R, σ'.arrs "rnk" = arrOf n R ∧ (∀ v < n, R v < n) ∧
          Function.Injective (fun v : Fin n => R (v : ℕ)))
      (elimCost n ns) := by
    show Spec B (ElimPreW n ns nt W O T M) elimCom _ (600 * n + 600 * ns + 100)
    run_vcg [w1, w2, w3, w4, w5] <;> assumption
  exact hall.post fun _ _ _ hq => ⟨RamElim.elimPost_of_elimMem hq.1, hq.2⟩

/-- **The elimination bridge at the pinned width** — the widened one at
`nt = ns`, where `RamElim.ElimPre` *is* `RamElim.ElimPreW` clause for
clause, so nothing is re-walked. -/
theorem elimRank_spec {B ns W : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}
    (hcsr : CsrSimple G ns O T) (hB : n + ns + 1 < B) (hMB : ∀ z < n, M z < B) (hW : ns ≤ W) :
    Spec B (ElimPre n ns W O T M) elimCom
      (fun σ σ' => ElimPost G M ns W σ σ' ∧
        ∃ R, σ'.arrs "rnk" = arrOf n R ∧ (∀ v < n, R v < n) ∧
          Function.Injective (fun v : Fin n => R (v : ℕ)))
      (elimCost n ns) :=
  elimRank_specW hcsr hB hMB hW le_rfl

/-! ### The flat zeroing passes

`RamDriver.elimRezeroCom` and `RamDriver.orderZeroCom` are ten fills
between them, and every one is `RamDriverOrder.fillUpto_spec` (or
`RamDriverCluster.fillCom_spec`) at the constant zero. What the two
specifications below say is the shape their consumers want: an array
whose *cells* are all zero, which is what `RamDriver.OrderMem` asks for
and what `RamElim.ElimPre` asks for one array at a time. -/

/-- What a flat pass over a prefix writes. -/
theorem warrs_fillUpto (a : String) (bnd e : Expr) : (fillUpto a bnd e).warrs = [a] := rfl

/-- And a pass over the whole carrier. -/
theorem warrs_fillCom (a : String) (e : Expr) : (fillCom a e).warrs = [a] := rfl

/-- An array's length survives a run, so being `arrOf N` of something
does too. -/
theorem sizedRun {B N K : ℕ} {c : Com} {σ σ' : Env} {a : String} (hr : Run B c σ σ' K)
    (h : ∃ g, σ.arrs a = arrOf N g) : ∃ g, σ'.arrs a = arrOf N g := by
  obtain ⟨g, hg⟩ := h
  exact exists_arrOf ((run_length_arrs hr a).trans (by rw [hg, length_arrOf]))

/-- An `arrOf` whose cells below the length are zero holds only zeros. -/
theorem eq_zero_of_mem_arrOf {N : ℕ} {g : ℕ → ℕ} (h : ∀ k < N, g k = 0) :
    ∀ v ∈ arrOf N g, v = 0 := by
  intro v hv
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv
  exact h k (List.mem_range.1 hk)

/-- And back: an array of the right length holding only zeros is an
`arrOf` of a function that is zero below it. -/
theorem zeroed_of_mem {N : ℕ} {a : String} {σ : Env} (hlen : (σ.arrs a).length = N)
    (hz : ∀ v ∈ σ.arrs a, v = 0) : ∃ g, σ.arrs a = arrOf N g ∧ ∀ k < N, g k = 0 := by
  obtain ⟨g, hg⟩ := exists_arrOf hlen
  exact ⟨g, hg, fun k hk => hz (g k) (by rw [hg]; exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)⟩

/-- A nondecreasing offset array is bounded by its last entry — the
reading of `RamElim.InCsr` that puts every in-list offset inside the
arc array, hence inside the word bound. -/
theorem off_le_of_mono {IO : ℕ → ℕ} {N m : ℕ} (hmono : ∀ i < N, IO i ≤ IO (i + 1))
    (hlast : IO N = m) : ∀ k ≤ N, IO k ≤ m := by
  have key : ∀ d k, k + d = N → IO k ≤ IO N := by
    intro d
    induction d with
    | zero => intro k hk; rw [show k = N by omega]
    | succ d ih => intro k hk; exact le_trans (hmono k (by omega)) (ih (k + 1) (by omega))
  intro k hk
  rw [← hlast]
  exact key (N - k) k (by omega)


/-- A flat fill of a prefix at a bound the scalar `"n"` drives. -/
theorem fillZero_spec {B n N : ℕ} (a : String) (bnd : Expr) (hB : 0 < B) (hNB : N < B)
    (hbnd : ∀ σ : Env, σ.vars "n" = n → bnd.evalB B σ = some N) :
    Spec B (fun σ => (∃ g, σ.arrs a = arrOf N g) ∧ σ.vars "n" = n)
      (fillUpto a bnd (.lit 0))
      (fun _ σ' => (∃ g, σ'.arrs a = arrOf N g ∧ ∀ k < N, g k = 0) ∧ σ'.vars "n" = n)
      ((bnd.size + 10) * N + bnd.size + 5) :=
  ((RamDriverOrder.fillUpto_spec N a bnd (.lit 0) (fun _ => 0)
    (fun σ => σ.vars "n" = n) hB hNB
    (fun _ _ hQ hv _ => (hv "n" (by decide)).trans hQ)
    (fun σ hQ => hbnd σ hQ) (fun _ _ _ _ => evalB_lit hB)).post
      (fun _ _ _ hq => ⟨hq.1, hq.2.2⟩)).mono (le_of_eq (by simp only [size_lit]; ring))

theorem evalB_succ_n {B n : ℕ} {σ : Env} (hnB : n + 1 < B) (hn : σ.vars "n" = n) :
    (Expr.add (.var "n") (.lit 1)).evalB B σ = some (n + 1) := by
  have h := evalB_bin (B := B) (σ := σ) (op := .add) (e := .var "n") (f := .lit 1)
    (evalB_var (by rw [hn]; omega)) (evalB_lit (by omega))
    (by simp only [Bop.apply_add, hn]; omega)
  rw [Bop.apply_add, hn] at h
  exact h

/-- **The re-zeroing between the two eliminations**, walked. -/
theorem elimRezero_spec {B n : ℕ} (hnB : n < B) (hn1B : n + 1 < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ (∃ g, σ.arrs "elm" = arrOf n g) ∧
        (∃ g, σ.arrs "bh" = arrOf (n + 1) g))
      elimRezeroCom
      (fun _ σ' => σ'.vars "n" = n ∧ (∃ g, σ'.arrs "elm" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
        (∃ g, σ'.arrs "bh" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0))
      ((11 * n + 6) + (13 * (n + 1) + 8)) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hn, helm, hbh⟩ := hσ
  obtain ⟨τ, r₁, ⟨e, he1, he2⟩, -, hn₁⟩ :=
    (RamDriverCluster.fillCom_spec B n "elm" 0 hnB (by omega)).run ⟨helm, hn⟩
  have hbhτ : ∃ g, τ.arrs "bh" = arrOf (n + 1) g := by
    obtain ⟨g, hg⟩ := hbh
    exact exists_arrOf ((run_length_arrs r₁ "bh").trans (by rw [hg, length_arrOf]))
  obtain ⟨ρ, r₂, ⟨b, hb1, hb2⟩, hn₂⟩ :=
    (fillZero_spec (n := n) "bh" (.add (.var "n") (.lit 1)) (by omega) hn1B
      (fun _ h => evalB_succ_n hn1B h)).run ⟨hbhτ, hn₁⟩
  have helmρ : ρ.arrs "elm" = arrOf n e := by
    rw [r₂.frame_arr "elm" (by decide)]; exact he1
  refine ⟨ρ, _, r₁.seq r₂, ?_, hn₂, ⟨e, helmρ, he2⟩, ⟨b, hb1, fun k hk => hb2 k (by omega)⟩⟩
  simp only [size_add, size_var, size_lit]
  omega

/-- **The re-zeroing tail of the ordering phase**, walked. -/
theorem orderZero_spec {B n : ℕ} (hnB : n < B) (hn1B : n + 1 < B) :
    Spec B (fun σ => σ.vars "n" = n ∧
        (∃ g, σ.arrs "elm" = arrOf n g) ∧ (∃ g, σ.arrs "bh" = arrOf (n + 1) g) ∧
        (∃ g, σ.arrs "ooff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "noff" = arrOf (n + 1) g) ∧
        (∃ g, σ.arrs "stf" = arrOf n g) ∧ (∃ g, σ.arrs "sta" = arrOf n g) ∧
        (∃ g, σ.arrs "std" = arrOf n g) ∧ (∃ g, σ.arrs "ste" = arrOf n g))
      orderZeroCom
      (fun _ σ' => σ'.vars "n" = n ∧
        (∀ v ∈ σ'.arrs "elm", v = 0) ∧ (∀ v ∈ σ'.arrs "bh", v = 0) ∧
        (∀ v ∈ σ'.arrs "ooff", v = 0) ∧ (∀ v ∈ σ'.arrs "noff", v = 0) ∧
        (∀ v ∈ σ'.arrs "stf", v = 0) ∧ (∀ v ∈ σ'.arrs "sta", v = 0) ∧
        (∀ v ∈ σ'.arrs "std", v = 0) ∧ (∀ v ∈ σ'.arrs "ste", v = 0))
      (4 * (11 * n + 6) + 3 * (13 * (n + 1) + 8) + (11 * n + 6)) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hn, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hσ
  have hsucc : ∀ τ : Env, τ.vars "n" = n →
      (Expr.add (.var "n") (.lit 1)).evalB B τ = some (n + 1) := fun _ h => evalB_succ_n hn1B h
  obtain ⟨τ₁, r₁, ⟨e₁, hA₁, hZ₁⟩, -, hn₁⟩ :=
    (RamDriverCluster.fillCom_spec B n "elm" 0 hnB (by omega)).run ⟨h1, hn⟩
  obtain ⟨τ₂, r₂, ⟨e₂, hA₂, hZ₂⟩, hn₂⟩ :=
    (fillZero_spec (n := n) "bh" (.add (.var "n") (.lit 1)) (by omega) hn1B hsucc).run
      ⟨sizedRun r₁ h2, hn₁⟩
  obtain ⟨τ₃, r₃, ⟨e₃, hA₃, hZ₃⟩, hn₃⟩ :=
    (fillZero_spec (n := n) "ooff" (.add (.var "n") (.lit 1)) (by omega) hn1B hsucc).run
      ⟨sizedRun r₂ (sizedRun r₁ h3), hn₂⟩
  obtain ⟨τ₄, r₄, ⟨e₄, hA₄, hZ₄⟩, hn₄⟩ :=
    (fillZero_spec (n := n) "noff" (.add (.var "n") (.lit 1)) (by omega) hn1B hsucc).run
      ⟨sizedRun r₃ (sizedRun r₂ (sizedRun r₁ h4)), hn₃⟩
  obtain ⟨τ₅, r₅, ⟨e₅, hA₅, hZ₅⟩, -, hn₅⟩ :=
    (RamDriverCluster.fillCom_spec B n "stf" 0 hnB (by omega)).run
      ⟨sizedRun r₄ (sizedRun r₃ (sizedRun r₂ (sizedRun r₁ h5))), hn₄⟩
  obtain ⟨τ₆, r₆, ⟨e₆, hA₆, hZ₆⟩, -, hn₆⟩ :=
    (RamDriverCluster.fillCom_spec B n "sta" 0 hnB (by omega)).run
      ⟨sizedRun r₅ (sizedRun r₄ (sizedRun r₃ (sizedRun r₂ (sizedRun r₁ h6)))), hn₅⟩
  obtain ⟨τ₇, r₇, ⟨e₇, hA₇, hZ₇⟩, -, hn₇⟩ :=
    (RamDriverCluster.fillCom_spec B n "std" 0 hnB (by omega)).run
      ⟨sizedRun r₆ (sizedRun r₅ (sizedRun r₄ (sizedRun r₃ (sizedRun r₂ (sizedRun r₁ h7))))),
        hn₆⟩
  obtain ⟨τ₈, r₈, ⟨e₈, hA₈, hZ₈⟩, -, hn₈⟩ :=
    (RamDriverCluster.fillCom_spec B n "ste" 0 hnB (by omega)).run
      ⟨sizedRun r₇ (sizedRun r₆ (sizedRun r₅ (sizedRun r₄ (sizedRun r₃
        (sizedRun r₂ (sizedRun r₁ h8)))))), hn₇⟩
  have f₂ : ∀ a : String, a ≠ "bh" → τ₂.arrs a = τ₁.arrs a :=
    fun a ha => r₂.frame_arr a (by rw [warrs_fillUpto]; simpa using ha)
  have f₃ : ∀ a : String, a ≠ "ooff" → τ₃.arrs a = τ₂.arrs a :=
    fun a ha => r₃.frame_arr a (by rw [warrs_fillUpto]; simpa using ha)
  have f₄ : ∀ a : String, a ≠ "noff" → τ₄.arrs a = τ₃.arrs a :=
    fun a ha => r₄.frame_arr a (by rw [warrs_fillUpto]; simpa using ha)
  have f₅ : ∀ a : String, a ≠ "stf" → τ₅.arrs a = τ₄.arrs a :=
    fun a ha => r₅.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  have f₆ : ∀ a : String, a ≠ "sta" → τ₆.arrs a = τ₅.arrs a :=
    fun a ha => r₆.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  have f₇ : ∀ a : String, a ≠ "std" → τ₇.arrs a = τ₆.arrs a :=
    fun a ha => r₇.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  have f₈ : ∀ a : String, a ≠ "ste" → τ₈.arrs a = τ₇.arrs a :=
    fun a ha => r₈.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  have g₁ : τ₈.arrs "elm" = arrOf n e₁ := by
    rw [f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide), f₅ _ (by decide),
      f₄ _ (by decide), f₃ _ (by decide), f₂ _ (by decide)]; exact hA₁
  have g₂ : τ₈.arrs "bh" = arrOf (n + 1) e₂ := by
    rw [f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide), f₅ _ (by decide),
      f₄ _ (by decide), f₃ _ (by decide)]; exact hA₂
  have g₃ : τ₈.arrs "ooff" = arrOf (n + 1) e₃ := by
    rw [f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide), f₅ _ (by decide),
      f₄ _ (by decide)]; exact hA₃
  have g₄ : τ₈.arrs "noff" = arrOf (n + 1) e₄ := by
    rw [f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide), f₅ _ (by decide)]; exact hA₄
  have g₅ : τ₈.arrs "stf" = arrOf n e₅ := by
    rw [f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide)]; exact hA₅
  have g₆ : τ₈.arrs "sta" = arrOf n e₆ := by
    rw [f₈ _ (by decide), f₇ _ (by decide)]; exact hA₆
  have g₇ : τ₈.arrs "std" = arrOf n e₇ := by
    rw [f₈ _ (by decide)]; exact hA₇
  refine ⟨τ₈, _, r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq (r₇.seq r₈)))))), ?_, hn₈,
    by rw [g₁]; exact eq_zero_of_mem_arrOf hZ₁,
    by rw [g₂]; exact eq_zero_of_mem_arrOf hZ₂,
    by rw [g₃]; exact eq_zero_of_mem_arrOf hZ₃,
    by rw [g₄]; exact eq_zero_of_mem_arrOf hZ₄,
    by rw [g₅]; exact eq_zero_of_mem_arrOf hZ₅,
    by rw [g₆]; exact eq_zero_of_mem_arrOf hZ₆,
    by rw [g₇]; exact eq_zero_of_mem_arrOf hZ₇,
    by rw [hA₈]; exact eq_zero_of_mem_arrOf hZ₈⟩
  simp only [size_add, size_var, size_lit]
  omega



section Syntax

variable (j : ℕ)

/-! ### What the ordering phase writes

`RamDriver.orderCom 0 j` assigns no scalar the level's state names and
writes no array of it except `off` and `tgt` — which `restoreCsr` puts
back — and the eight of `OrderMem`'s zeroing half, which the tail puts
back. Its scalar write set does not mention `W` or `j` at all, so it is
the write set at `0 0`; its array write set mentions `j` once, at the
depth's own order array. -/

/-- The scalars the phase assigns do not depend on its parameters. -/
theorem wvars_orderCom₀ (j : ℕ) : (orderCom 0 j).wvars = (orderCom 0 0).wvars := rfl

/-- The arrays it writes, in order. Rebase F-c-2: the symmetrization's
five — the counting sort's `ooff`/`ofl`/`otg` and the union's
`off`/`tgt` — sit where `restoreCsr`'s two used to, and `restoreCsr`'s
`off`/`tgt` moved past the second elimination. -/
theorem warrs_orderCom₀ (j : ℕ) : (orderCom 0 j).warrs =
    ["gof", "gtg", "alv", "deg", "deg", "bv", "bn", "bh", "bh", "elm", "rnk", "idg", "deg",
      "bv", "bn", "bh", "ioff", "ifl", "ioff", "itg", "ifl", "doff", "dtg",
      "ooff", "ooff", "ofl", "otg", "ofl", "off", "tgt", "tgt",
      "alv", "elm", "bh", "deg", "deg", "bv", "bn", "bh", "bh", "elm", "rnk", "idg", "deg",
      "bv", "bn", "bh", "ioff", "ifl", "ioff", "itg", "ifl", "off", "tgt",
      ordName j, "elm", "bh", "ooff",
      "noff", "stf", "sta", "std", "ste"] := rfl

/-- It never writes to the output tape. -/
theorem noWrite_orderCom₀ (j : ℕ) : (orderCom 0 j).NoWrite :=
  show (orderCom 0 0).NoWrite by decide

set_option maxRecDepth 8000 in
/-- Every scalar it assigns is one of seventeen short literals — the
symmetrization's write pointer `"sy"` being the seventeenth. -/
theorem mem_wvars_orderCom₀ : ∀ y ∈ (orderCom 0 0).wvars,
    y ∈ ["i", "c", "j", "jend", "u", "sp", "ls", "d", "mind", "cnt", "kmax", "sc", "p", "w",
      "s", "z", "sy"] := by decide

/-- The re-zeroing tail writes exactly `OrderMem`'s eight. -/
theorem warrs_orderZeroCom :
    orderZeroCom.warrs = ["elm", "bh", "ooff", "noff", "stf", "sta", "std", "ste"] := rfl

/-- The rank inversion writes its destination and nothing else. -/
theorem warrs_ordCom (dst : String) : (ordCom dst).warrs = [dst] := rfl

/-- The save writes the reserved pair. -/
theorem warrs_saveCsr : saveCsr.warrs = ["gof", "gtg"] := rfl

/-- And the restore writes the level's own. -/
theorem warrs_restoreCsr : restoreCsr.warrs = ["off", "tgt"] := rfl

/-- A depth's mask is neither of the reserved pair. -/
theorem alvName_notMem_saveCsr (j : ℕ) : alvName j ∉ saveCsr.warrs := by
  rw [warrs_saveCsr]; simp [alvName, String.ext_iff]

/-- The mask copy writes `alv` and nothing else. -/
theorem lit_notMem_copyCom_alv (j : ℕ) (a : String) (h : a ≠ "alv" := by decide) :
    a ∉ (copyCom (alvName j) "alv").warrs := by
  rw [warrs_copyCom]; simpa using h

/-- The carrier's size is not assigned. -/
theorem n_notMem_orderCom₀ : "n" ∉ (orderCom 0 j).wvars := by
  rw [wvars_orderCom₀]; decide

/-- Nor is the slot count. -/
theorem m_notMem_orderCom₀ : "m" ∉ (orderCom 0 j).wvars := by
  rw [wvars_orderCom₀]; decide

/-- Nor the live width, which the two block-structure copies read and
no pass of the phase assigns (rebase G2/E1). -/
theorem lw_notMem_orderCom₀ : "lw" ∉ (orderCom 0 j).wvars := by
  rw [wvars_orderCom₀]; decide

/-- Nor is any depth's connector. -/
theorem ctrName_notMem_orderCom₀ (a : ℕ) : ctrName a ∉ (orderCom 0 j).wvars := by
  rw [wvars_orderCom₀]
  intro h
  have h' := mem_wvars_orderCom₀ _ h
  simp [ctrName, String.ext_iff] at h'

/-- No depth's game mask is written. -/
theorem gamName_notMem_orderCom₀ (a : ℕ) : gamName a ∉ (orderCom 0 j).warrs := by
  rw [warrs_orderCom₀]; simp [gamName, ordName, String.ext_iff]

/-- Nor the depth's own work mask. -/
theorem alvName_notMem_orderCom₀ : alvName j ∉ (orderCom 0 j).warrs := by
  rw [warrs_orderCom₀]; simp [alvName, ordName, String.ext_iff]

/-- Nor any of its colours. -/
theorem colName_notMem_orderCom₀ (c : ℕ) : colName j c ∉ (orderCom 0 j).warrs := by
  rw [warrs_orderCom₀]; simp [colName, ordName, String.ext_iff]

/-- Nor any depth's member list (rebase E-mem): the phase writes the
depth's ordering, and the member list is the descent's business. -/
theorem memName_notMem_orderCom₀ (a : ℕ) : memName a ∉ (orderCom 0 j).warrs := by
  rw [warrs_orderCom₀]; simp [memName, ordName, String.ext_iff]

/-- Nor any depth's member count. -/
theorem mnumName_notMem_orderCom₀ (a : ℕ) : mnumName a ∉ (orderCom 0 j).wvars := by
  rw [wvars_orderCom₀]
  intro h
  have h' := mem_wvars_orderCom₀ _ h
  simp [mnumName, String.ext_iff] at h'

/-- The tail leaves the order array the inversion just wrote. -/
theorem ordName_notMem_orderZeroCom : ordName j ∉ orderZeroCom.warrs := by
  rw [warrs_orderZeroCom]; simp [ordName, String.ext_iff]

end Syntax

/-- **The cost of the ordering phase at `R = 0`**: the two eliminations,
the four block-structure copies, the two in-list copies, the
symmetrization, the mask fill and the ten zeroing fills. The constants
are generous, as everywhere in this campaign: the sharp charging is the
cost wave's business.

**Rebase F-c-4.** The two block-structure copies are bounded by the
allocation width `W` rather than by the slot count `ns`, since that is
the array the level owns, so the `W` coefficient absorbs their `28·W`.

**Rebase F-c-2.** The symmetrization adds `RamDriverAugment.symCost n m
= 200·n + 100·m + 200` with `m` the chain's arc count, and
`m + m ≤ ns` at `R = 0` (`RamDriverAugment.two_mul_arcs_le`), so the
addend is read here at `200·n + 100·ns + 200`. The second elimination
got *cheaper* — it runs at the slot count `m + m ≤ ns` rather than at
`ns` — so nothing else moves. -/
def orderPhaseCost (n ns W : ℕ) : ℕ := 1600 * n + 1350 * ns + 60 * W + 650

set_option maxHeartbeats 1000000 in
/-- **The ordering phase of a level, discharged at `R = 0`.**

Twelve passes. `saveCsr` and `restoreCsr` are
`RamDriverOrder.saveCsr_spec`/`restoreCsr_spec`, the two eliminations
are `elimRank_spec`, the rank inversion is
`RamDriverOrder.ordCom_spec` — the only mathematics in the phase, since
its postcondition names no ordering in particular — and the rest is
`fillCom_spec`, `copyUpto_spec` and the two zeroing specifications
above. At `R = 0` the augmentation fold is `Com.skip`, so
`RamDriver.AugAvail` is never applied and `RamElim.Implements` enters
through `elimRank_spec` rather than through `RamDriver.ElimAvail`,
which the obligation therefore carries unused.

The level's state crosses the phase clause by clause and not as a
frame: `off` and `tgt` are written by `restoreCsr` and put back to what
they were, and the eight zeroed arrays are written by both eliminations
and put back by `orderZeroCom`. Everything else — the two scalars, the
depth's own four arrays, the lengths, the value bounds and the two word
clauses — crosses by the syntactic section above. -/
theorem orderImplements₀ {B cap mb ns W j : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} :
    OrderImplements B n 0 W cap mb ns j G O T M Gm C (fun _ _ => True)
      (orderPhaseCost n ns W) := by
  intro d hB hcsr hWB _helim _haug
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hvn, hoff, htgt, halvj, hgamj, hcolj, hMB, hGmB, hCbit, hmem, hdep, hmv,
    hordmem, hpad0, hTBW, hmemcl⟩ := id hσ
  obtain ⟨hnsW, hlwp, hosz, hzelm, hzbh, hzooff, -, -, -, -, -, hwitg, hwntg⟩ := id hordmem
  -- the runtime live width: the copies walk its prefix and nothing else
  obtain ⟨lw, hlw⟩ : ∃ lw, σ.vars "lw" = lw := ⟨_, rfl⟩
  rw [hlw] at hlwp
  obtain ⟨hlwns, hlwW⟩ := hlwp
  have hnB : n < B := hB.n_lt
  have hn1B : n + 1 < B := hB.succ_lt
  have hnsB : ns < B := hB.ns_lt
  have h1B : 1 < B := hB.one_lt
  have hWltB : W < B := by omega
  have hnnsB : n + ns + 1 < B := by
    have := hB.arena; omega
  have hOB : ∀ k < n + 1, O k < B := fun k hk =>
    lt_of_le_of_lt (hcsr.csr.le_ns (by omega)) hnsB
  have hTB : ∀ k < ns, T k < B := fun k hk => lt_trans (hcsr.csr.target_lt k hk) hnB
  -- (1) the block structure out of the way — the `lw`-cell live prefix
  -- of it, which contains the whole `ns`-slot structure since `ns ≤ lw`
  obtain ⟨σ₁, r₁, hvn₁, hmv₁, hlw₁, hoff₁, htgt₁, hgof₁, ⟨Tg, hgtg₁, hTgpre⟩⟩ :=
    (RamDriverOrder.saveCsr_spec (ns := ns) (lw := lw) hn1B hWltB hlwW hOB
      (fun k hk => hTBW k (by omega))).run
      ⟨hvn, hmv, hlw, hoff, htgt, hosz.get (p := ("gof", n + 1)) (by simp),
        hosz.get (p := ("gtg", W)) (by simp)⟩
  have hsz₁ := hosz.run r₁
  have hmem₁ := levelMem_run r₁ hmem
  have f₁ : ∀ a : String, a ∉ (saveCsr).warrs → σ₁.arrs a = σ.arrs a := fun a ha => r₁.frame_arr a ha
  -- (2) the depth's mask into the name the engine reads
  obtain ⟨σ₂, r₂, ⟨u₂, hu₂, hag₂⟩, -, hvn₂, -⟩ :=
    (RamDriverCluster.copyCom_spec B n n (alvName j) "alv" M (alvName_ne_alv j) hnB le_rfl
      hMB).run
      ⟨hmem₁.1.get (p := ("alv", n)) (by simp), hvn₁,
        by rw [f₁ _ (alvName_notMem_saveCsr j)]; exact halvj⟩
  have halv₂ : σ₂.arrs "alv" = arrOf n M := hu₂.trans (RamDriverOrder.arrOf_congr hag₂)
  have hsz₂ := hsz₁.run r₂
  have f₂ : ∀ a : String, a ∉ (copyCom (alvName j) "alv").warrs → σ₂.arrs a = σ₁.arrs a :=
    fun a ha => r₂.frame_arr a ha
  have helmσ₂ : ∀ v ∈ σ₂.arrs "elm", v = 0 := by
    rw [f₂ _ (lit_notMem_copyCom_alv j "elm"), f₁ _ (by rw [warrs_saveCsr]; decide)]; exact hzelm
  have hbhσ₂ : ∀ v ∈ σ₂.arrs "bh", v = 0 := by
    rw [f₂ _ (lit_notMem_copyCom_alv j "bh"), f₁ _ (by rw [warrs_saveCsr]; decide)]; exact hzbh
  -- (3) the first elimination
  obtain ⟨σ₃, r₃, ⟨Ra, IOa, ITa, ka, ma, Ea, -, -, hioff₃, hitg₃, hma, -, -, -, -, htoG₃, -, -,
      -, -, hincsr₃⟩, -⟩ :=
    (elimRank_specW (nt := W) hcsr hnnsB hMB hnsW hnsW).run
      ⟨hvn₂, by rw [f₂ _ (lit_notMem_copyCom_alv j "off")]; exact hoff₁,
        by rw [f₂ _ (lit_notMem_copyCom_alv j "tgt")]; exact htgt₁,
        halv₂, hsz₂.get (p := ("deg", n)) (by simp),
        zeroed_of_mem (hsz₂.length (p := ("elm", n)) (by simp)) helmσ₂,
        hsz₂.get (p := ("rnk", n)) (by simp), hsz₂.get (p := ("idg", n)) (by simp),
        (by
          obtain ⟨g, hg, hgz⟩ := zeroed_of_mem (hsz₂.length (p := ("bh", n + 1)) (by simp)) hbhσ₂
          exact ⟨g, hg, fun k hk => hgz k (by omega)⟩),
        hsz₂.get (p := ("bv", n + W + 1)) (by simp),
        hsz₂.get (p := ("bn", n + W + 1)) (by simp),
        hsz₂.get (p := ("ioff", n + 1)) (by simp), hsz₂.get (p := ("ifl", n)) (by simp),
        hsz₂.get (p := ("itg", W)) (by simp)⟩
  have hsz₃ := hsz₂.run r₃
  have f₃ : ∀ a : String, a ∉ RamElim.elimCom.warrs → σ₃.arrs a = σ₂.arrs a :=
    fun a ha => r₃.frame_arr a ha
  have hvn₃ : σ₃.vars "n" = n := by rw [r₃.frame_var "n" (by decide)]; exact hvn₂
  have hIOB : ∀ k < n + 1, IOa k < B := fun k hk =>
    lt_of_le_of_lt (le_trans (off_le_of_mono hincsr₃.mono hincsr₃.last k (by omega)) hma) hnsB
  -- (4) the in-list offsets, kept for the augmentation rounds
  obtain ⟨σ₄, r₄, ⟨dg₄, hdg₄, hdgv₄⟩, -, hvn₄, hioff₄⟩ :=
    (RamDriverOrder.copyUpto_spec (B := B) (n + 1) (n + 1) "ioff" "doff"
        (.add (.var "n") (.lit 1)) IOa
        (fun τ => τ.vars "n" = n ∧ τ.arrs "ioff" = arrOf (n + 1) IOa) (by omega) hn1B le_rfl
        (fun _ _ hQ hv ha => ⟨(hv "n" (by decide)).trans hQ.1,
          by rw [ha "ioff" (by decide)]; exact hQ.2⟩)
        (fun _ hQ => evalB_succ_n hn1B hQ.1) (fun _ hQ => hQ.2) hIOB).run
      ⟨hsz₃.get (p := ("doff", n + 1)) (by simp), hvn₃, hioff₃⟩
  have hsz₄ := hsz₃.run r₄
  have f₄ : ∀ a : String, a ∉ (copyUpto "ioff" "doff" (.add (.var "n") (.lit 1))).warrs →
      σ₄.arrs a = σ₃.arrs a := fun a ha => r₄.frame_arr a ha
  have hdoff₄ : σ₄.arrs "doff" = arrOf (n + 1) IOa :=
    hdg₄.trans (RamDriverOrder.arrOf_congr hdgv₄)
  -- (5) the in-list targets
  have hitg₄ : σ₄.arrs "itg" = arrOf W ITa := by
    rw [f₄ _ (by rw [warrs_copyUpto]; decide)]; exact hitg₃
  have hITB : ∀ k < W, ITa k < B := fun k hk =>
    RamDriverOrder.lt_of_mem_words
      (run_mem_arrs_lt r₄ "itg" (run_mem_arrs_lt r₃ "itg"
        (run_mem_arrs_lt r₂ "itg" (run_mem_arrs_lt r₁ "itg" hwitg)))) hitg₄ hk
  have hlw₄ : σ₄.vars "lw" = lw := by
    rw [r₄.frame_var "lw" (by rw [wvars_copyUpto]; decide), r₃.frame_var "lw" (by decide),
      r₂.frame_var "lw" (by rw [wvars_copyCom]; decide)]
    exact hlw₁
  -- the arcs of the arena's orientation fit the live prefix
  have hsub : ∀ u v : Fin n, Ea.toGraph.Adj u v → G.Adj u v := by
    intro u v h
    rw [htoG₃] at h
    exact (RamBfs.masked_adj.1 h).1
  have hfit : ma + ma ≤ ns := RamDriverAugment.two_mul_arcs_le hcsr hincsr₃ hsub
  obtain ⟨σ₅, r₅, ⟨dt₅, hdt₅, hdtv₅⟩, -, -⟩ :=
    (copyPrefix_spec (B := B) lw W W "itg" "dtg" (.var "lw") ITa
        (fun τ => τ.arrs "itg" = arrOf W ITa ∧ τ.vars "lw" = lw) (by omega) (by omega)
        hlwW hlwW
        (fun _ _ hQ hv ha => ⟨(ha "itg" (by decide)).trans hQ.1,
          (hv "lw" (by decide)).trans hQ.2⟩)
        (fun τ hQ => by
          have h := evalB_var (B := B) (σ := τ) (x := "lw")
            (show τ.vars "lw" < B by rw [hQ.2]; omega)
          rw [hQ.2] at h; exact h)
        (fun _ hQ => hQ.1) (fun k hk => hITB k (by omega))).run
      ⟨hsz₄.get (p := ("dtg", W)) (by simp), hitg₄, hlw₄⟩
  have hsz₅ := hsz₄.run r₅
  have f₅ : ∀ a : String, a ∉ (copyUpto "itg" "dtg" (.var "lw")).warrs →
      σ₅.arrs a = σ₄.arrs a := fun a ha => r₅.frame_arr a ha
  have hvn₅ : σ₅.vars "n" = n := by
    rw [r₅.frame_var "n" (by rw [wvars_copyUpto]; decide)]; exact hvn₄
  have hlw₅ : σ₅.vars "lw" = lw := by
    rw [r₅.frame_var "lw" (by rw [wvars_copyUpto]; decide)]; exact hlw₄
  have hdtg₅ : σ₅.arrs "dtg" = arrOf W dt₅ := hdt₅
  -- the in-lists survive the prefix copy: the structure reads its
  -- target function only below the arc count, which is inside `lw`
  have hincsr₅ : RamElim.InCsr Ea ma IOa dt₅ :=
    RamDriverAugment.inCsr_congr_prefix hincsr₃ (fun j hj => hdtv₅ j (by omega))
  have hdoff₅ : σ₅.arrs "doff" = arrOf (n + 1) IOa := by
    rw [f₅ _ (by rw [warrs_copyUpto]; decide)]; exact hdoff₄
  -- (6) no augmentation round: the fold is empty
  have r₆ : Run B (foldRange (fun _ => augRoundCom) 0) σ₅ σ₅ 1 :=
    Run.skip
  have hgof₅ : σ₅.arrs "gof" = arrOf (n + 1) O := by
    rw [f₅ _ (by rw [warrs_copyUpto]; decide),
      f₄ _ (by rw [warrs_copyUpto]; decide), f₃ _ (by decide),
      f₂ _ (lit_notMem_copyCom_alv j "gof")]
    exact hgof₁
  have hgtg₅ : σ₅.arrs "gtg" = arrOf W Tg := by
    rw [f₅ _ (by rw [warrs_copyUpto]; decide),
      f₄ _ (by rw [warrs_copyUpto]; decide), f₃ _ (by decide),
      f₂ _ (lit_notMem_copyCom_alv j "gtg")]
    exact hgtg₁
  -- (7) the chain's last orientation, symmetrized into `off`/`tgt`
  have hmv₅ : σ₅.vars "m" + σ₅.vars "m" = ns := by
    rw [r₅.frame_var "m" (by rw [wvars_copyUpto]; decide),
      r₄.frame_var "m" (by rw [wvars_copyUpto]; decide),
      r₃.frame_var "m" (by decide),
      r₂.frame_var "m" (by rw [wvars_copyCom]; decide), hmv₁]
    exact hmv
  have hzooff₅ : ∀ v ∈ σ₅.arrs "ooff", v = 0 := by
    rw [f₅ _ (by rw [warrs_copyUpto]; decide), f₄ _ (by rw [warrs_copyUpto]; decide),
      f₃ _ (by decide), f₂ _ (lit_notMem_copyCom_alv j "ooff"),
      f₁ _ (by rw [warrs_saveCsr]; decide)]
    exact hzooff
  have htgtV₅ : σ₅.arrs "tgt" = arrOf W T := by
    rw [f₅ _ (by rw [warrs_copyUpto]; decide), f₄ _ (by rw [warrs_copyUpto]; decide),
      f₃ _ (by decide), f₂ _ (lit_notMem_copyCom_alv j "tgt")]
    exact htgt₁
  obtain ⟨σ₇, K₇, Os, Ts, r₇, hK₇, hoffS, htgtS, hcsrS, htailS, hfaS, hfvS⟩ :=
    RamDriverAugment.symPass_run (B := B) (W := W) (nt := W) (m := ma) (D := Ea)
      (DO := IOa) (DT := dt₅) (σ := σ₅) hn1B (by omega) (by omega) (by omega) hvn₅ hincsr₅
      hdoff₅ hdtg₅
      (by
        obtain ⟨g, hg, hgz⟩ :=
          zeroed_of_mem (hsz₅.length (p := ("ooff", n + 1)) (by simp)) hzooff₅
        exact ⟨g, hg, fun k hk => hgz k (by omega)⟩)
      (hsz₅.get (p := ("ofl", n)) (by simp)) (hsz₅.get (p := ("otg", W)) (by simp))
      (sizedRun r₅ (sizedRun r₄ (sizedRun r₃ (sizedRun r₂ ⟨O, hoff₁⟩))))
      htgtV₅
  have hsz₇ := hsz₅.run r₇
  have hvn₇ : σ₇.vars "n" = n := by
    rw [hfvS "n" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hvn₅
  have hmv₇ : σ₇.vars "m" + σ₇.vars "m" = ns := by
    rw [hfvS "m" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hmv₅
  have hlw₇ : σ₇.vars "lw" = lw := by
    rw [hfvS "lw" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hlw₅
  have hgof₇ : σ₇.arrs "gof" = arrOf (n + 1) O := by
    rw [hfaS "gof" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hgof₅
  have hgtg₇ : σ₇.arrs "gtg" = arrOf W Tg := by
    rw [hfaS "gtg" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hgtg₅
  -- (8) everything alive again
  obtain ⟨σ₈, r₈, ⟨A, hA₈, hA₈v⟩, -, hvn₈⟩ :=
    (RamDriverCluster.fillCom_spec B n "alv" 1 hnB h1B).run
      ⟨sizedRun r₇ (sizedRun r₅ (sizedRun r₄ (sizedRun r₃ ⟨M, halv₂⟩))), hvn₇⟩
  have hsz₈ := hsz₇.run r₈
  have hAB : ∀ z < n, A z < B := fun z hz => by rw [hA₈v z hz]; exact h1B
  have f₈ : ∀ a : String, a ≠ "alv" → σ₈.arrs a = σ₇.arrs a :=
    fun a ha => r₈.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  -- (9) the elimination scratch, re-zeroed
  obtain ⟨σ₉, r₉, hvn₉, helm₉, hbh₉⟩ :=
    (elimRezero_spec hnB hn1B).run
      ⟨hvn₈, hsz₈.get (p := ("elm", n)) (by simp), hsz₈.get (p := ("bh", n + 1)) (by simp)⟩
  have hsz₉ := hsz₈.run r₉
  have f₉ : ∀ a : String, a ∉ elimRezeroCom.warrs → σ₉.arrs a = σ₈.arrs a :=
    fun a ha => r₉.frame_arr a ha
  -- (10) the second elimination, on the symmetrized graph
  obtain ⟨σ₁₀, r₁₀, -, R, hrnk₁₀, hRlt, hRinj⟩ :=
    (elimRank_specW (nt := W) hcsrS (by omega) hAB (by omega) (by omega)).run
      ⟨hvn₉,
        by rw [f₉ _ (by decide), f₈ _ (by decide)]; exact hoffS,
        by rw [f₉ _ (by decide), f₈ _ (by decide)]; exact htgtS,
        by rw [f₉ _ (by decide)]; exact hA₈,
        hsz₉.get (p := ("deg", n)) (by simp), helm₉,
        hsz₉.get (p := ("rnk", n)) (by simp), hsz₉.get (p := ("idg", n)) (by simp), hbh₉,
        hsz₉.get (p := ("bv", n + W + 1)) (by simp),
        hsz₉.get (p := ("bn", n + W + 1)) (by simp),
        hsz₉.get (p := ("ioff", n + 1)) (by simp), hsz₉.get (p := ("ifl", n)) (by simp),
        hsz₉.get (p := ("itg", W)) (by simp)⟩
  have hsz₁₀ := hsz₉.run r₁₀
  have hvn₁₀ : σ₁₀.vars "n" = n := by rw [r₁₀.frame_var "n" (by decide)]; exact hvn₉
  have f₁₀ : ∀ a : String, a ∉ RamElim.elimCom.warrs → σ₁₀.arrs a = σ₉.arrs a :=
    fun a ha => r₁₀.frame_arr a ha
  -- (11) the level's own block structure back
  have hmv₁₀ : σ₁₀.vars "m" + σ₁₀.vars "m" = ns := by
    rw [r₁₀.frame_var "m" (by decide), r₉.frame_var "m" (by decide),
      r₈.frame_var "m" (by decide)]
    exact hmv₇
  have hlw₁₀ : σ₁₀.vars "lw" = lw := by
    rw [r₁₀.frame_var "lw" (by decide), r₉.frame_var "lw" (by decide),
      r₈.frame_var "lw" (by decide)]
    exact hlw₇
  have htgt₁₀ : σ₁₀.arrs "tgt" = arrOf W Ts := by
    rw [f₁₀ _ (by decide), f₉ _ (by decide), f₈ _ (by decide)]
    exact htgtS
  obtain ⟨σ₁₁, r₁₁, hvn₁₁, -, -, -, -, hoff₁₁, htgt₁₁⟩ :=
    (RamDriverOrder.restoreCsr_spec (ns := ns) (lw := lw) (T := T) hn1B hWltB hlwW hOB
      (fun k hk => by rw [hTgpre k hk]; exact hTBW k (by omega)) hTgpre
      (fun z hz hzW => htailS z (by omega) hzW)).run
      ⟨hvn₁₀, hmv₁₀, hlw₁₀,
        by rw [f₁₀ _ (by decide), f₉ _ (by decide), f₈ _ (by decide)]; exact hgof₇,
        by rw [f₁₀ _ (by decide), f₉ _ (by decide), f₈ _ (by decide)]; exact hgtg₇,
        sizedRun r₁₀ (sizedRun r₉ (sizedRun r₈ ⟨Os, hoffS⟩)),
        htgt₁₀⟩
  have hsz₁₁ := hsz₁₀.run r₁₁
  have f₁₁ : ∀ a : String, a ∉ (restoreCsr).warrs → σ₁₁.arrs a = σ₁₀.arrs a :=
    fun a ha => r₁₁.frame_arr a ha
  -- (12) the rank array inverted into the order array
  obtain ⟨σ₁₂, r₁₂, hvn₁₂, -, π, ordv, hord₁₂, hordby⟩ :=
    (RamDriverOrder.ordCom_spec (B := B) (ordName j) (by simp [ordName, String.ext_iff]) hnB
      hRlt (fun v hv w hw h => congrArg Fin.val (hRinj (a₁ := ⟨v, hv⟩) (a₂ := ⟨w, hw⟩) h))).run
      ⟨hvn₁₁, by rw [f₁₁ _ (by rw [warrs_restoreCsr]; decide)]; exact hrnk₁₀,
        (hdep.run (r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₇.seq
          (r₈.seq (r₉.seq (r₁₀.seq r₁₁))))))))) ).get j (p := (ordName j, n)) (by simp)⟩
  have hsz₁₂ := hsz₁₁.run r₁₂
  -- (13) the re-zeroing tail
  obtain ⟨ρ, r₁₃, hvn₁₃, z₁, z₂, z₃, z₄, z₅, z₆, z₇, z₈⟩ :=
    (orderZero_spec hnB hn1B).run
      ⟨hvn₁₂, hsz₁₂.get (p := ("elm", n)) (by simp),
        hsz₁₂.get (p := ("bh", n + 1)) (by simp), hsz₁₂.get (p := ("ooff", n + 1)) (by simp),
        hsz₁₂.get (p := ("noff", n + 1)) (by simp), hsz₁₂.get (p := ("stf", n)) (by simp),
        hsz₁₂.get (p := ("sta", n)) (by simp), hsz₁₂.get (p := ("std", n)) (by simp),
        hsz₁₂.get (p := ("ste", n)) (by simp)⟩
  have f₁₂ : ∀ a : String, a ≠ ordName j → σ₁₂.arrs a = σ₁₁.arrs a :=
    fun a ha => r₁₂.frame_arr a (by rw [warrs_ordCom]; simpa using ha)
  have f₁₃ : ∀ a : String, a ∉ orderZeroCom.warrs → ρ.arrs a = σ₁₂.arrs a :=
    fun a ha => r₁₃.frame_arr a ha
  have hoffρ : ρ.arrs "off" = arrOf (n + 1) O := by
    rw [f₁₃ _ (by rw [warrs_orderZeroCom]; decide),
      f₁₂ _ (by simp [ordName, String.ext_iff])]
    exact hoff₁₁
  have htgtρ : ρ.arrs "tgt" = arrOf W T := by
    rw [f₁₃ _ (by rw [warrs_orderZeroCom]; decide),
      f₁₂ _ (by simp [ordName, String.ext_iff])]
    exact htgt₁₁
  -- the phase, assembled
  have hrT : Run B (orderCom 0 j) σ ρ _ :=
    r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq (r₇.seq (r₈.seq (r₉.seq
      (r₁₀.seq (r₁₁.seq (r₁₂.seq r₁₃)))))))))))
  refine ⟨ρ, _, hrT, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, hMB, hGmB, hCbit, levelMem_run hrT hmem,
      hdep.run hrT, ?_,
      ⟨hnsW, by rw [hrT.frame_var "lw" (lw_notMem_orderCom₀ j), hlw]; exact ⟨hlwns, hlwW⟩,
        hosz.run hrT, z₁, z₂, z₃, z₄, z₅, z₆, z₇, z₈,
        run_mem_arrs_lt hrT "itg" hwitg, run_mem_arrs_lt hrT "ntg" hwntg⟩, hpad0, hTBW,
      -- the member clause crosses the phase: the ordering writes neither
      -- the depth's member array nor its count (rebase E-mem)
      (by
        obtain ⟨Mem, mmj, hm1, hm2, hm3, hm4⟩ := hmemcl
        exact ⟨Mem, mmj, by rw [hrT.frame_arr _ (memName_notMem_orderCom₀ j j)]; exact hm1,
          by rw [hrT.frame_var _ (mnumName_notMem_orderCom₀ j j)]; exact hm2, hm3, hm4⟩)⟩,
    hrT.out_eq (noWrite_orderCom₀ j),
    fun a => hrT.frame_var _ (ctrName_notMem_orderCom₀ j a),
    fun a => hrT.frame_arr _ (gamName_notMem_orderCom₀ j a),
    π, ordv, ?_, hordby, trivial⟩
  · rw [orderPhaseCost]
    rw [RamDriverAugment.symCost] at hK₇
    simp only [RamElim.elimCost, size_add, size_var, size_lit]
    omega
  · exact hvn₁₃
  · exact hoffρ
  · exact htgtρ
  · rw [hrT.frame_arr _ (alvName_notMem_orderCom₀ j)]; exact halvj
  · rw [hrT.frame_arr _ (gamName_notMem_orderCom₀ j j)]; exact hgamj
  · intro c hc
    rw [hrT.frame_arr _ (colName_notMem_orderCom₀ j c)]; exact hcolj c hc
  · rw [hrT.frame_var "m" (m_notMem_orderCom₀ j)]; exact hmv
  · rw [f₁₃ _ (ordName_notMem_orderZeroCom j)]; exact hord₁₂

/-! ### The `R*` phase (rebase F-c-3, statement; F-c-5, walk)

`orderImplements₀` is the phase at `R = 0`, where the fold is
`Com.skip` and the parametric slot `P` is `True`. At `R = R*` the fold
is the point of the phase, and what it produces is
`Lax3Proofs.CoverDegree.AugChainData` — the six-clause bundle F-c-2
anchored the slot on. This section states the slot value `OrderP`, the
cost `orderPhaseCostR`, the obligation `OrderImplementsR` naming both —
and, since rebase F-c-5, **discharges it**: `orderImplementsR` at the
bottom of the section is the walk.

The walk's shape is F-c-3's residual list, executed:

1. **The fold** is `fold_run_aux` over `fold_step`: the invariant
   `FoldInv` carries the machine state *and* the chain built so far,
   `RamDriverAugment.implementsW` runs each round, and the chain grows
   by `RamAugment.AugPost`'s `AugStep`/`GreedyFratRound` clauses.
2. **The width**: one `W` serves every round, by
   `Augmentation.greedy_chain_inDegLE` + `TgtCoupling.budget_mono` +
   `augWidth_mono` against the hypothesis `chainWidth n d D₁ R ≤ W`.
3. **The two ends**: the first elimination's `RamElim.ElimPost` is kept
   (the foot `d₀ = ka` with its minimality against the arena), and so is
   the second's, on the symmetrized `(D R).toGraph` (the head `k` with
   its minimality) — F-c-3 recorded both as dropped, not missing, and
   that was exact.
4. **The syntax section** at general `R`: the fold's write sets are the
   round's (`mem_warrs_foldRange_const` and friends), and the round
   writes no per-depth name.
5. **`AugmentedDepthOneDensity`** enters as the hypothesis `hdens`,
   quantified over every chain the fold could build, and leaves through
   `P` — the one unproved statement of `Augmentation`, inherited, not
   this walk's debt. `hd` — a degeneracy bound of the arena — anchors
   the width budget at statement level.
6. **The cost**: `relinkCost` (walked at F-c-4, repaired **again** at
   F-c-5 — see its docstring; the fold walk refuted the *round* as
   landed and the repair `RamDriver.augPrepCom` is three more per-round
   passes), `RamAugment.augCost` for the round itself, and
   `orderPhaseCostR`'s fixed part for the twelve steps outside the
   fold. At `R = 0` the walk reproduces the landed budget: the
   `i = 0` clause of `FoldInv` keeps `m + m ≤ ns` so the symmetrization
   and the final elimination charge at `ns` exactly as
   `orderImplements₀` does. At `R ≥ 1` both charge at `W`, and *that*
   refuted F-c-3's round coefficient too — the third cost repair, the
   `650·W` surcharge; see `orderPhaseCostR`'s docstring and the
   accounting `#guard`s beside it.

**The defect the walk found (F-c-5).** The fold body as landed —
`augCom ; augRelinkCom` — had no run at `R ≥ 1`: `RamAugment.AugPre`
asks for `off`, `elm` and `bh` zeroed at every round's entry, the
phase's first elimination dirties `elm`/`bh`, `off` holds the level's
structure until the first relink, and the relink re-zeroes `off` but
never `elm`/`bh` (the round's *inner* elimination re-dirties them).
Wave D4's defect A, one pass earlier, found by walking the round's
entry against `AugPreW` and compiled in `TgtWidenProbe`'s R = 1 gate:
the old text is stuck on a `K₁,₄` level state, the prepped one runs and
reports the augmented graph's bound. The repair — `augPrepCom` inside
the fold body `augRoundCom` — keeps the `R = 0` text byte-identical. -/

section Rstar

variable {n : ℕ}

/-- **The `R*` phase's ordering property**, the value its parametric
slot `P` takes: the ordering `π` the phase built carries an `R`-round
greedy augmentation chain of the depth's arena, with the two elimination
bounds at its ends. This is `CoverDegree.AugChainData` with the
orientation family and the two bounds existentially quantified — the
phase knows they exist, the consumer needs nothing else.

The order array is not mentioned: the chain is a statement about the
permutation, and `RamCover.OrdersBy` is what ties the array to it. -/
def OrderP (R : ℕ) (G : SimpleGraph (Fin n)) (M : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (_ord : ℕ → ℕ) : Prop :=
  ∃ (D : ℕ → Lax3Proofs.Augmentation.Orientation n) (d₀ k : ℕ),
    CoverDegree.AugChainData (masked G M) D π R d₀ k

/-- At `R = 0` the bundle degenerates to the two elimination bounds of
the level's own arena (`CoverDegree.augChainData_zero`) and says nothing
about augmentation — which is why `orderImplements₀` instantiates the
slot at `True` and not at this. -/
theorem orderP_zero {R : ℕ} {G : SimpleGraph (Fin n)} {M : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {ord : ℕ → ℕ} (h : OrderP R G M π ord) :
    ∃ (D : ℕ → Lax3Proofs.Augmentation.Orientation n) (d₀ k : ℕ),
      CoverDegree.AugChainData (masked G M) D π R d₀ k := h

/-- **The bookkeeping between two rounds, charged.** `augRelinkCom` is
two copies and seven flat fills, and this is the sum of their nine kit
costs — not a guess.

**Rebase F-c-4: the constant was wrong.** F-c-3 landed this as `100·n +
20·W + 100`, marked "generous, not yet walked". Walking it
(`relinkCostSum` below, and `relinkCostSum_le` for the comparison) gives
`97·n + 12·W + 115`, whose *constant* is above `100`: the old bound is
refuted at every carrier below five vertices —
`relinkCost_old_refuted` is that falsification at `n = W = 0`. The `n` and `W` coefficients were indeed
generous; the constant was not, and a phase obligation stated at the old
number could not have been discharged.

**Rebase F-c-5: the round gained a prep pass.** The fold walk found the
round *itself* refuted as landed — `RamAugment.AugPre` asks for `off`,
`elm` and `bh` zeroed, and nothing between the phase's first elimination
and a round re-zeroes them (see `RamDriver.augPrepCom`'s defect record
and `TgtWidenProbe`'s R = 1 gate). The repair's three fills are per-round
bookkeeping of the same species as the nine relink passes, so this
constant is now the budget for **twelve** passes: `prepCostSum +
relinkCostSum = 134·n + 12·W + 163`, and F-c-4's `100·n + 20·W + 120` is
below that at every carrier (its `n` coefficient already fails at
`W = 0`, `n` large). `prep_relink_le` is the repaired comparison. -/
def relinkCost (n W : ℕ) : ℕ := 140 * n + 20 * W + 170

/-- **The nine passes of `RamDriver.augRelinkCom`, charged one by one**,
at the kit costs their walks come out at:
`RamDriverOrder.copyUpto_spec` is `(bnd.size + 11)·N + bnd.size + 5` and
`RamDriverOrder.fillUpto_spec` is `(e.size + bnd.size + 9)·N + bnd.size
+ 5`, with `Spec.seq` adding and nothing else. The two copies are at
`n + 1` (bound `n + 1`, size `3`) and at `W` (bound the literal `W`,
size `1`); the three offset fills are at `n + 1`; the four stamp fills
are `RamDriver.fillCom`, whose bound is `.var "n"` of size `1`, at `n`.
-/
def relinkCostSum (n W : ℕ) : ℕ :=
  (14 * (n + 1) + 8) + (12 * W + 6) + 3 * (13 * (n + 1) + 8) + 4 * (11 * n + 6)

/-- The sum, in closed form: `97·n + 12·W + 115`. -/
theorem relinkCostSum_eq (n W : ℕ) : relinkCostSum n W = 97 * n + 12 * W + 115 := by
  simp only [relinkCostSum]; ring

/-- **And it fits the budget** — the check the phase obligation needs,
at the repaired constant. -/
theorem relinkCostSum_le (n W : ℕ) : relinkCostSum n W ≤ relinkCost n W := by
  rw [relinkCostSum_eq, relinkCost]; omega

/-- **Refuted: the old constant.** `100·n + 20·W + 100` does not bound
the nine passes — at the empty carrier and the empty width the
bookkeeping still costs `115`, being nine loop entries and exits. This
is why the walk had to be done and not estimated. -/
theorem relinkCost_old_refuted : ¬ relinkCostSum 0 0 ≤ 100 * 0 + 20 * 0 + 100 := by
  rw [relinkCostSum_eq]; omega

-- the old bound fails on every carrier below five vertices, and holds
-- from five on: the defect is exactly the constant
#guard decide (relinkCostSum 0 0 = 115)
#guard ¬ decide (relinkCostSum 4 0 ≤ 100 * 4 + 20 * 0 + 100)
#guard decide (relinkCostSum 5 0 ≤ 100 * 5 + 20 * 0 + 100)

/-- **The three passes of `RamDriver.augPrepCom`, charged one by one**
(rebase F-c-5): the `off` fill at `n + 1` (bound size `3`), and
`elimRezeroCom`'s `elm` fill at `n` and `bh` fill at `n + 1` — the kit
costs `RamDriverOrder.fillUpto_spec` and `RamDriverCluster.fillCom_spec`
come out at. -/
def prepCostSum (n : ℕ) : ℕ :=
  (13 * (n + 1) + 8) + ((11 * n + 6) + (13 * (n + 1) + 8))

/-- The sum, in closed form: `37·n + 48`. -/
theorem prepCostSum_eq (n : ℕ) : prepCostSum n = 37 * n + 48 := by
  simp only [prepCostSum]; ring

/-- **And the twelve passes fit the repaired budget** — the check the
fold walk charges each round's bookkeeping against. -/
theorem prep_relink_le (n W : ℕ) : prepCostSum n + relinkCostSum n W ≤ relinkCost n W := by
  rw [prepCostSum_eq, relinkCostSum_eq, relinkCost]; omega

-- F-c-4's constant cannot pay for the prep pass the round turned out to
-- need: the defect record for the second repair of this constant
#guard ¬ decide (prepCostSum 0 + relinkCostSum 0 0 ≤ 100 * 0 + 20 * 0 + 120)
#guard decide (prepCostSum 0 + relinkCostSum 0 0 = 163)

/-- **The cost of the ordering phase at `R` rounds**: the `R = 0`
phase, plus `R` times a round, its bookkeeping, and the widened tail's
surcharge. The shape is what P3's `CostRecurrence` consumes — linear in
`R` with a single coefficient — and the `R = 0` instance is
`orderPhaseCost` on the nose.

**Rebase F-c-5: the third cost repair of this section.** F-c-3 landed
the coefficient as `augCost + relinkCost` alone, and the fold walk
refutes *that* too: at `R ≥ 1` the symmetrization and the final
elimination run at up to `W` slots — `2·m ≤ ns` is an `R = 0` fact —
so their budgets are `100·m + …` and `600·(m + m) + …` with only
`m + m ≤ W` to charge them against, up to `650·W` beyond the `60·W` the
fixed part carries; and the round term is consumed by the fold's own
component budgets, whose slack (`prep_relink_le`'s margin) is `8·W` a
round. The `#guard` below is the accounting at the smallest widened
shape (`n = 0`, `W = 2`, `m + m = W`, `R = 1`): the walk's component
budgets sum to `26194` against the old budget's `24980`. The surcharge
`650·W` is charged per round though the tail runs once, because the
budget's `R`-shape wants one coefficient; it is sound at every `R ≥ 1`,
and at `R = 0` the tail fits the fixed part exactly as
`orderImplements₀` proved. -/
def orderPhaseCostR (n ns W R : ℕ) : ℕ :=
  orderPhaseCost n ns W + R * (RamAugment.augCost n W + relinkCost n W + 650 * W)

-- the accounting that refutes F-c-3's coefficient, at `n = 0`,
-- `ns = 0`, `W = 2`, `m = 1`, `R = 1`: the thirteen component budgets
-- the walk composes …
#guard decide (
    ((14 * 1 + 14 * 2 + 16) + (12 * 0 + 6) + RamElim.elimCost 0 0 + (14 * 1 + 8)
      + (12 * 2 + 6) + (prepCostSum 0 + RamAugment.augCost 0 2 + relinkCostSum 0 2 + 1)
      + RamDriverAugment.symCost 0 1 + (11 * 0 + 6) + ((11 * 0 + 6) + (13 * 1 + 8))
      + RamElim.elimCost 0 2 + (14 * 1 + 14 * 2 + 16) + (12 * 0 + 6)
      + (4 * (11 * 0 + 6) + 3 * (13 * 1 + 8) + (11 * 0 + 6)))
    = 26194)
-- … exceed the old budget …
#guard ¬ decide ((26194 : ℕ) ≤
    orderPhaseCost 0 0 2 + 1 * (RamAugment.augCost 0 2 + relinkCost 0 2))
-- … and fit the repaired one
#guard decide ((26194 : ℕ) ≤ orderPhaseCostR 0 0 2 1)

/-- The `R = 0` reading of the `R`-round cost is the landed one. -/
theorem orderPhaseCostR_zero (n ns W : ℕ) :
    orderPhaseCostR n ns W 0 = orderPhaseCost n ns W := by
  simp [orderPhaseCostR]

/-- The budget grows with the round count, which is what a phase
obligation stated at `R` and consumed at `R' ≥ R` needs. -/
theorem orderPhaseCostR_mono (n ns W : ℕ) {R R' : ℕ} (h : R ≤ R') :
    orderPhaseCostR n ns W R ≤ orderPhaseCostR n ns W R' := by
  simp only [orderPhaseCostR]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- **The ordering phase at `R` rounds** — the obligation of the fold,
named. `RamDriver.OrderImplements` at the slot value `OrderP` and the
cost `orderPhaseCostR`; every other component is the `R = 0`
obligation's, unchanged.

Discharged by `orderImplementsR` at the end of this section (rebase
F-c-5), under the three mathematical hypotheses its docstring names. -/
def OrderImplementsR (B n R W cap mb ns j : ℕ) (G : SimpleGraph (Fin n)) (O T : ℕ → ℕ)
    (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) : Prop :=
  OrderImplements B n R W cap mb ns j G O T M Gm C (OrderP R G M) (orderPhaseCostR n ns W R)

/-- **The `R*` obligation at the live width** (rebase G2/E2b) —
`OrderImplementsR`'s Spec with the one pre-clause the live-prefix
copies need: the chain's degree-aware width budget fits the *runtime*
live width `σ.vars "lw"`, not merely the allocation width. `d`/`D₁` —
the degeneracy bound and the density constant the budget reads — are
parameters here because the clause has nowhere else to name them.

The clause is load-bearing, not slack: `RamDriver.OrderMem` now pins
only `ns ≤ lw ≤ W`, and at `lw = ns` the `R = 1` phase's chain
overruns the prefix the copies preserve — `TgtWidenProbe`'s
`ordLive8Run` boundary gate is that refutation, compiled. Without the
clause this obligation is **refutable**, which is why the live width
did not simply replace `W` in `OrderImplementsR`. -/
def OrderImplementsRL (B n R W cap mb ns j d D₁ : ℕ) (G : SimpleGraph (Fin n))
    (O T : ℕ → ℕ) (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) : Prop :=
  ∀ {dK : ℕ}, WordBoundK B n dK ns cap mb → RamElim.CsrSimple G ns O T → n + W + 1 < B →
  ElimAvail B n → AugAvail B n →
    Spec B (fun σ => LevelPre B n cap mb ns W O T j M Gm C σ ∧
        TgtCoupling.chainWidthE n ns d D₁ R ≤ σ.vars "lw")
      (orderCom R j)
      (fun σ σ' => LevelPre B n cap mb ns W O T j M Gm C σ' ∧
        σ'.out = σ.out ∧
        (∀ a : ℕ, σ'.vars (ctrName a) = σ.vars (ctrName a)) ∧
        (∀ a : ℕ, σ'.arrs (gamName a) = σ.arrs (gamName a)) ∧
        ∃ (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ),
          σ'.arrs (ordName j) = arrOf n ord ∧ RamCover.OrdersBy n π ord ∧
          OrderP R G M π ord)
      (orderPhaseCostR n ns W R)

/-! ### The fold, syntactically

`RamDriver.foldRange` at a constant body is the body sequenced `m`
times, and everything a frame lemma wants of it — its write sets, its
output silence — is the body's. The body of the ordering phase's fold is
`RamDriver.augRoundCom`, whose write sets do not depend on the width
parameter (it appears only inside expressions). -/

theorem foldRange_zero (f : ℕ → Com) : foldRange f 0 = .skip := rfl

theorem foldRange_const_succ (c : Com) (m : ℕ) :
    foldRange (fun _ => c) (m + 1) = .seq c (foldRange (fun _ => c) m) := by
  simp [foldRange, List.range_succ_eq_map, List.foldr_map]

theorem mem_wvars_foldRange_const {c : Com} {m : ℕ} {y : String}
    (h : y ∈ (foldRange (fun _ => c) m).wvars) : y ∈ c.wvars := by
  induction m with
  | zero => simp [foldRange_zero, Com.wvars] at h
  | succ m ih =>
      rw [foldRange_const_succ] at h
      simp only [Com.wvars, List.mem_append] at h
      exact h.elim id ih

theorem mem_warrs_foldRange_const {c : Com} {m : ℕ} {a : String}
    (h : a ∈ (foldRange (fun _ => c) m).warrs) : a ∈ c.warrs := by
  induction m with
  | zero => simp [foldRange_zero, Com.warrs] at h
  | succ m ih =>
      rw [foldRange_const_succ] at h
      simp only [Com.warrs, List.mem_append] at h
      exact h.elim id ih

theorem noWrite_foldRange_const {c : Com} (hc : c.NoWrite) :
    ∀ m, (foldRange (fun _ => c) m).NoWrite
  | 0 => by rw [foldRange_zero]; simp [Com.NoWrite]
  | m + 1 => by
      rw [foldRange_const_succ]
      exact ⟨hc, noWrite_foldRange_const hc m⟩

theorem warrs_augPrepCom : augPrepCom.warrs = ["off", "elm", "bh"] := rfl

set_option maxRecDepth 8000 in
/-- The round never assigns the carrier's size. -/
theorem n_notMem_augCom : "n" ∉ RamAugment.augCom.wvars := by decide

set_option maxRecDepth 8000 in
/-- Nor the live width the block copies read (rebase G2/E1). -/
theorem lw_notMem_augCom : "lw" ∉ RamAugment.augCom.wvars := by decide

set_option maxRecDepth 8000 in
/-- Every scalar a round assigns is one of nineteen short literals. -/
theorem mem_wvars_augRoundCom : ∀ y ∈ augRoundCom.wvars,
    y ∈ ["i", "j", "jend", "u", "c", "w", "q", "qe", "mf", "sp", "ls", "d", "mind", "cnt",
      "kmax", "sc", "p", "s", "mn"] := by decide

set_option maxRecDepth 8000 in
/-- And every array it stores into is one of twenty-six — the round's
own scratch and block structures, no per-depth name among them. -/
theorem mem_warrs_augRoundCom : ∀ a ∈ augRoundCom.warrs,
    a ∈ ["off", "elm", "bh", "ooff", "ofl", "otg", "stf", "ffl", "tgt", "alv", "deg", "bv",
      "bn", "rnk", "idg", "ioff", "ifl", "itg", "sta", "std", "ste", "noff", "nfl", "ntg",
      "doff", "dtg"] := by decide

/-! ### The write sets of the phase at general `R`

Everything `orderCom R j` writes, it writes either at `R = 0` — where
the landed `Syntax` section reads the sets off the text — or inside the
fold, where it is the round's. -/

theorem mem_wvars_orderCom {R j : ℕ} {y : String} (h : y ∈ (orderCom R j).wvars) :
    y ∈ (orderCom 0 j).wvars ∨ y ∈ augRoundCom.wvars := by
  simp only [orderCom, Com.wvars, List.mem_append, foldRange_zero, List.not_mem_nil,
    false_or] at h ⊢
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (mem_wvars_foldRange_const h)
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h)))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr h)))))))))))

theorem mem_warrs_orderCom {R j : ℕ} {a : String} (h : a ∈ (orderCom R j).warrs) :
    a ∈ (orderCom 0 j).warrs ∨ a ∈ augRoundCom.warrs := by
  simp only [orderCom, Com.warrs, List.mem_append, foldRange_zero, List.not_mem_nil,
    false_or] at h ⊢
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (mem_warrs_foldRange_const h)
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h)))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr h)))))))))))

theorem n_notMem_orderCom {R j : ℕ} : "n" ∉ (orderCom R j).wvars := by
  intro h
  rcases mem_wvars_orderCom h with h | h
  · exact n_notMem_orderCom₀ j h
  · have := mem_wvars_augRoundCom _ h
    simp at this

theorem m_notMem_orderCom {R j : ℕ} : "m" ∉ (orderCom R j).wvars := by
  intro h
  rcases mem_wvars_orderCom h with h | h
  · exact m_notMem_orderCom₀ j h
  · have := mem_wvars_augRoundCom _ h
    simp at this

theorem lw_notMem_orderCom {R j : ℕ} : "lw" ∉ (orderCom R j).wvars := by
  intro h
  rcases mem_wvars_orderCom h with h | h
  · exact lw_notMem_orderCom₀ j h
  · have := mem_wvars_augRoundCom _ h
    simp at this

theorem ctrName_notMem_orderCom {R j : ℕ} (a : ℕ) : ctrName a ∉ (orderCom R j).wvars := by
  intro h
  rcases mem_wvars_orderCom h with h | h
  · exact ctrName_notMem_orderCom₀ j a h
  · have := mem_wvars_augRoundCom _ h
    simp [ctrName, String.ext_iff] at this

theorem gamName_notMem_orderCom {R j : ℕ} (a : ℕ) : gamName a ∉ (orderCom R j).warrs := by
  intro h
  rcases mem_warrs_orderCom h with h | h
  · exact gamName_notMem_orderCom₀ j a h
  · have := mem_warrs_augRoundCom _ h
    simp [gamName, String.ext_iff] at this

theorem alvName_notMem_orderCom {R j : ℕ} : alvName j ∉ (orderCom R j).warrs := by
  intro h
  rcases mem_warrs_orderCom h with h | h
  · exact alvName_notMem_orderCom₀ j h
  · have := mem_warrs_augRoundCom _ h
    rcases List.mem_cons.1 this with hc | this
    · exact absurd hc (by simp [alvName, String.ext_iff])
    rcases List.mem_cons.1 this with hc | this
    · exact absurd hc (by simp [alvName, String.ext_iff])
    · revert this
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc |
        hc | hc | hc | hc | hc | hc | hc | hc | hc) <;>
        exact absurd hc (by simp [alvName, String.ext_iff])

theorem colName_notMem_orderCom {R j : ℕ} (c : ℕ) : colName j c ∉ (orderCom R j).warrs := by
  intro h
  rcases mem_warrs_orderCom h with h | h
  · exact colName_notMem_orderCom₀ j c h
  · have := mem_warrs_augRoundCom _ h
    simp [colName, String.ext_iff] at this

theorem memName_notMem_orderCom {R j : ℕ} (a : ℕ) : memName a ∉ (orderCom R j).warrs := by
  intro h
  rcases mem_warrs_orderCom h with h | h
  · exact memName_notMem_orderCom₀ j a h
  · have := mem_warrs_augRoundCom _ h
    simp [memName, String.ext_iff] at this

theorem mnumName_notMem_orderCom {R j : ℕ} (a : ℕ) : mnumName a ∉ (orderCom R j).wvars := by
  intro h
  rcases mem_wvars_orderCom h with h | h
  · exact mnumName_notMem_orderCom₀ j a h
  · have := mem_wvars_augRoundCom _ h
    simp [mnumName, String.ext_iff] at this

theorem noWrite_orderCom (R j : ℕ) : (orderCom R j).NoWrite := by
  refine ⟨show saveCsr.NoWrite by decide,
    show (copyCom (alvName j) "alv").NoWrite from show (copyCom "" "").NoWrite by decide,
    show RamElim.elimCom.NoWrite by decide,
    show (copyUpto "ioff" "doff" (.add (.var "n") (.lit 1))).NoWrite by decide,
    show (copyUpto "itg" "dtg" (.var "lw")).NoWrite by decide,
    noWrite_foldRange_const (c := augRoundCom) (show augRoundCom.NoWrite by decide) R,
    show RamDriver.symCom.NoWrite by decide,
    show (fillCom "alv" (.lit 0)).NoWrite by decide,
    show elimRezeroCom.NoWrite by decide,
    show RamElim.elimCom.NoWrite by decide,
    show restoreCsr.NoWrite by decide,
    show (ordCom (ordName j)).NoWrite from show (ordCom "").NoWrite by decide,
    show orderZeroCom.NoWrite by decide⟩

/-! ### The width thread

One width serves every round. Historically `TgtCoupling.chainWidth` was
`RamAugment.augWidth` at the last round's budget (`chainWidth_eq_augWidth`
below, kept as the record); since rebase G2/E2 the fold runs at the
degree-aware `TgtCoupling.chainWidthE`, which carries no `n · n` room, so
`fold_step` derives the round's two capacities directly — the fraternity
term from `budget_mono` and the raw assembly arcs from
`TgtCoupling.two_sq_add_le_budget_succ` — and enters the round through
`RamDriverAugment.augment_specWE`. -/

theorem augWidth_mono (n : ℕ) {b b' : ℕ} (h : b ≤ b') :
    RamAugment.augWidth n b ≤ RamAugment.augWidth n b' := by
  simp only [RamAugment.augWidth]
  have hp : (b + 1) ^ 2 ≤ (b' + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have := Nat.mul_le_mul_left n hp
  omega

/-- The chain's width is the round width at the last budget, on the
nose. -/
theorem chainWidth_eq_augWidth (n d D₁ r : ℕ) :
    TgtCoupling.chainWidth n d D₁ r = RamAugment.augWidth n (Augmentation.budget d D₁ r) :=
  rfl

/-! ### The prep and the relink, walked

`RamDriver.augPrepCom` is three flat fills and `RamDriver.augRelinkCom`
is two copies and seven, all `RamDriverOrder.fillUpto_spec`,
`RamDriverOrder.copyUpto_spec` or `RamDriverCluster.fillCom_spec` — the
same kit the `R = 0` walk is made of. -/

/-- **The per-round prep, walked**: the fraternity accumulator and the
engine's two dirty arrays, zeroed. -/
theorem augPrep_spec {B n : ℕ} (hnB : n < B) (hn1B : n + 1 < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ (∃ g, σ.arrs "off" = arrOf (n + 1) g) ∧
        (∃ g, σ.arrs "elm" = arrOf n g) ∧ (∃ g, σ.arrs "bh" = arrOf (n + 1) g))
      augPrepCom
      (fun _ σ' => σ'.vars "n" = n ∧
        (∃ g, σ'.arrs "off" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0) ∧
        (∃ g, σ'.arrs "elm" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
        (∃ g, σ'.arrs "bh" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0))
      (prepCostSum n) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hn, hoffE, helmE, hbhE⟩ := hσ
  obtain ⟨τ, r₁, ⟨o, ho1, ho2⟩, hnτ⟩ :=
    (fillZero_spec (n := n) "off" (.add (.var "n") (.lit 1)) (by omega) hn1B
      (fun _ h => evalB_succ_n hn1B h)).run ⟨hoffE, hn⟩
  obtain ⟨ρ, r₂, hnρ, helmρ, hbhρ⟩ :=
    (elimRezero_spec hnB hn1B).run ⟨hnτ, sizedRun r₁ helmE, sizedRun r₁ hbhE⟩
  have hoffρ : ρ.arrs "off" = arrOf (n + 1) o := by
    rw [r₂.frame_arr "off" (by decide)]; exact ho1
  refine ⟨ρ, _, r₁.seq r₂, ?_, hnρ, ⟨o, hoffρ, fun k hk => ho2 k (by omega)⟩, helmρ, hbhρ⟩
  simp only [prepCostSum, size_add, size_var, size_lit]
  omega

/-- **The relink, walked**: the round's output block structure into the
next round's input, and the seven accumulators and stamps zeroed.

**The target copy walks the live prefix** (rebase G2/E2b): the bound is
the scalar `"lw"`, whose runtime value `lw` may sit strictly below the
allocation width `W`, so the destination `dtg` comes back as the copied
`lw`-prefix of `NT` over whatever tail it already had — the fold's
`inCsr_congr_prefix` step is what makes that as good as the whole
array, the chain's arcs living below `chainWidthE ≤ lw`. The cost reads
`relinkCostSum n lw`. -/
theorem augRelink_spec {B n W lw : ℕ} {NO NT : ℕ → ℕ} (hnB : n < B) (hn1B : n + 1 < B)
    (hWB : W < B) (hlwW : lw ≤ W) (hNOB : ∀ k < n + 1, NO k < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.vars "lw" = lw ∧ σ.arrs "noff" = arrOf (n + 1) NO ∧
        σ.arrs "ntg" = arrOf W NT ∧ (∀ v ∈ σ.arrs "ntg", v < B) ∧
        (∃ g, σ.arrs "doff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "dtg" = arrOf W g) ∧
        (∃ g, σ.arrs "ooff" = arrOf (n + 1) g) ∧ (∃ g, σ.arrs "off" = arrOf (n + 1) g) ∧
        (∃ g, σ.arrs "stf" = arrOf n g) ∧ (∃ g, σ.arrs "sta" = arrOf n g) ∧
        (∃ g, σ.arrs "std" = arrOf n g) ∧ (∃ g, σ.arrs "ste" = arrOf n g))
      augRelinkCom
      (fun _ σ' => σ'.vars "n" = n ∧ σ'.vars "lw" = lw ∧
        σ'.arrs "doff" = arrOf (n + 1) NO ∧
        (∃ h, σ'.arrs "dtg" = arrOf W h ∧ ∀ k < lw, h k = NT k) ∧
        (∃ g, σ'.arrs "ooff" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0) ∧
        (∃ g, σ'.arrs "off" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0) ∧
        (∃ g, σ'.arrs "noff" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0) ∧
        (∃ g, σ'.arrs "stf" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
        (∃ g, σ'.arrs "sta" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
        (∃ g, σ'.arrs "std" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
        (∃ g, σ'.arrs "ste" = arrOf n g ∧ ∀ k < n, g k = 0))
      (relinkCostSum n lw) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hn, hlw, hnoff, hntg, hntgW, hdoffE, hdtgE, hooffE, hoffE, hstfE, hstaE, hstdE,
    hsteE⟩ := hσ
  have hNTB : ∀ k < W, NT k < B := fun k hk =>
    RamDriverOrder.lt_of_mem_words hntgW hntg hk
  -- (1) the offsets of the next round's input
  obtain ⟨τ₁, r₁, ⟨d₁, hd₁, hd₁v⟩, -, hn₁, hnoff₁⟩ :=
    (RamDriverOrder.copyUpto_spec (B := B) (n + 1) (n + 1) "noff" "doff"
        (.add (.var "n") (.lit 1)) NO
        (fun τ => τ.vars "n" = n ∧ τ.arrs "noff" = arrOf (n + 1) NO) (by omega) hn1B le_rfl
        (fun _ _ hQ hv ha => ⟨(hv "n" (by decide)).trans hQ.1,
          by rw [ha "noff" (by decide)]; exact hQ.2⟩)
        (fun _ hQ => evalB_succ_n hn1B hQ.1) (fun _ hQ => hQ.2) hNOB).run
      ⟨hdoffE, hn, hnoff⟩
  have hdoff₁ : τ₁.arrs "doff" = arrOf (n + 1) NO :=
    hd₁.trans (RamDriverOrder.arrOf_congr hd₁v)
  have f₁ : ∀ a : String, a ≠ "doff" → τ₁.arrs a = σ.arrs a := fun a ha =>
    r₁.frame_arr a (by rw [warrs_copyUpto]; simpa using ha)
  have hlw₁ : τ₁.vars "lw" = lw := by
    rw [r₁.frame_var "lw" (by rw [wvars_copyUpto]; decide)]; exact hlw
  -- (2) its targets, walking only the live prefix
  obtain ⟨τ₂, r₂, ⟨d₂, hd₂, hd₂v⟩, -, hntg₂, hlw₂⟩ :=
    (copyPrefix_spec (B := B) lw W W "ntg" "dtg" (.var "lw") NT
        (fun τ => τ.arrs "ntg" = arrOf W NT ∧ τ.vars "lw" = lw) (by omega) (by omega)
        hlwW hlwW
        (fun _ _ hQ hv ha => ⟨(ha "ntg" (by decide)).trans hQ.1,
          (hv "lw" (by decide)).trans hQ.2⟩)
        (fun τ hQ => by
          have h := evalB_var (B := B) (σ := τ) (x := "lw")
            (show τ.vars "lw" < B by rw [hQ.2]; omega)
          rw [hQ.2] at h; exact h)
        (fun _ hQ => hQ.1) (fun k hk => hNTB k (by omega))).run
      ⟨sizedRun r₁ hdtgE, by rw [f₁ _ (by decide)]; exact hntg, hlw₁⟩
  have hdtg₂ : τ₂.arrs "dtg" = arrOf W d₂ := hd₂
  have f₂ : ∀ a : String, a ≠ "dtg" → τ₂.arrs a = τ₁.arrs a := fun a ha =>
    r₂.frame_arr a (by rw [warrs_copyUpto]; simpa using ha)
  have hn₂ : τ₂.vars "n" = n := by
    rw [r₂.frame_var "n" (by rw [wvars_copyUpto]; decide)]; exact hn₁
  have hsucc : ∀ τ : Env, τ.vars "n" = n →
      (Expr.add (.var "n") (.lit 1)).evalB B τ = some (n + 1) := fun _ h => evalB_succ_n hn1B h
  -- (3)–(5) the three offset accumulators
  obtain ⟨τ₃, r₃, ⟨e₃, hA₃, hZ₃⟩, hn₃⟩ :=
    (fillZero_spec (n := n) "ooff" (.add (.var "n") (.lit 1)) (by omega) hn1B hsucc).run
      ⟨sizedRun r₂ (sizedRun r₁ hooffE), hn₂⟩
  obtain ⟨τ₄, r₄, ⟨e₄, hA₄, hZ₄⟩, hn₄⟩ :=
    (fillZero_spec (n := n) "off" (.add (.var "n") (.lit 1)) (by omega) hn1B hsucc).run
      ⟨sizedRun r₃ (sizedRun r₂ (sizedRun r₁ hoffE)), hn₃⟩
  obtain ⟨τ₅, r₅, ⟨e₅, hA₅, hZ₅⟩, hn₅⟩ :=
    (fillZero_spec (n := n) "noff" (.add (.var "n") (.lit 1)) (by omega) hn1B hsucc).run
      ⟨sizedRun r₄ (sizedRun r₃ (sizedRun r₂ ⟨NO, hnoff₁⟩)), hn₄⟩
  -- (6)–(9) the four stamps
  obtain ⟨τ₆, r₆, ⟨e₆, hA₆, hZ₆⟩, -, hn₆⟩ :=
    (RamDriverCluster.fillCom_spec B n "stf" 0 hnB (by omega)).run
      ⟨sizedRun r₅ (sizedRun r₄ (sizedRun r₃ (sizedRun r₂ (sizedRun r₁ hstfE)))), hn₅⟩
  obtain ⟨τ₇, r₇, ⟨e₇, hA₇, hZ₇⟩, -, hn₇⟩ :=
    (RamDriverCluster.fillCom_spec B n "sta" 0 hnB (by omega)).run
      ⟨sizedRun r₆ (sizedRun r₅ (sizedRun r₄ (sizedRun r₃ (sizedRun r₂
        (sizedRun r₁ hstaE))))), hn₆⟩
  obtain ⟨τ₈, r₈, ⟨e₈, hA₈, hZ₈⟩, -, hn₈⟩ :=
    (RamDriverCluster.fillCom_spec B n "std" 0 hnB (by omega)).run
      ⟨sizedRun r₇ (sizedRun r₆ (sizedRun r₅ (sizedRun r₄ (sizedRun r₃ (sizedRun r₂
        (sizedRun r₁ hstdE)))))), hn₇⟩
  obtain ⟨τ₉, r₉, ⟨e₉, hA₉, hZ₉⟩, -, hn₉⟩ :=
    (RamDriverCluster.fillCom_spec B n "ste" 0 hnB (by omega)).run
      ⟨sizedRun r₈ (sizedRun r₇ (sizedRun r₆ (sizedRun r₅ (sizedRun r₄ (sizedRun r₃
        (sizedRun r₂ (sizedRun r₁ hsteE))))))), hn₈⟩
  have f₃ : ∀ a : String, a ≠ "ooff" → τ₃.arrs a = τ₂.arrs a := fun a ha =>
    r₃.frame_arr a (by rw [warrs_fillUpto]; simpa using ha)
  have f₄ : ∀ a : String, a ≠ "off" → τ₄.arrs a = τ₃.arrs a := fun a ha =>
    r₄.frame_arr a (by rw [warrs_fillUpto]; simpa using ha)
  have f₅ : ∀ a : String, a ≠ "noff" → τ₅.arrs a = τ₄.arrs a := fun a ha =>
    r₅.frame_arr a (by rw [warrs_fillUpto]; simpa using ha)
  have f₆ : ∀ a : String, a ≠ "stf" → τ₆.arrs a = τ₅.arrs a := fun a ha =>
    r₆.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  have f₇ : ∀ a : String, a ≠ "sta" → τ₇.arrs a = τ₆.arrs a := fun a ha =>
    r₇.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  have f₈ : ∀ a : String, a ≠ "std" → τ₈.arrs a = τ₇.arrs a := fun a ha =>
    r₈.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  have f₉ : ∀ a : String, a ≠ "ste" → τ₉.arrs a = τ₈.arrs a := fun a ha =>
    r₉.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  have hlw₉ : τ₉.vars "lw" = lw := by
    rw [r₉.frame_var "lw" (by decide), r₈.frame_var "lw" (by decide),
      r₇.frame_var "lw" (by decide), r₆.frame_var "lw" (by decide),
      r₅.frame_var "lw" (by decide), r₄.frame_var "lw" (by decide),
      r₃.frame_var "lw" (by decide)]
    exact hlw₂
  have hdoff₉ : τ₉.arrs "doff" = arrOf (n + 1) NO := by
    rw [f₉ _ (by decide), f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide),
      f₅ _ (by decide), f₄ _ (by decide), f₃ _ (by decide), f₂ _ (by decide)]
    exact hdoff₁
  have hdtg₉ : τ₉.arrs "dtg" = arrOf W d₂ := by
    rw [f₉ _ (by decide), f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide),
      f₅ _ (by decide), f₄ _ (by decide), f₃ _ (by decide)]
    exact hdtg₂
  have hooff₉ : τ₉.arrs "ooff" = arrOf (n + 1) e₃ := by
    rw [f₉ _ (by decide), f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide),
      f₅ _ (by decide), f₄ _ (by decide)]
    exact hA₃
  have hoff₉ : τ₉.arrs "off" = arrOf (n + 1) e₄ := by
    rw [f₉ _ (by decide), f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide),
      f₅ _ (by decide)]
    exact hA₄
  have hnoff₉ : τ₉.arrs "noff" = arrOf (n + 1) e₅ := by
    rw [f₉ _ (by decide), f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide)]
    exact hA₅
  have hstf₉ : τ₉.arrs "stf" = arrOf n e₆ := by
    rw [f₉ _ (by decide), f₈ _ (by decide), f₇ _ (by decide)]; exact hA₆
  have hsta₉ : τ₉.arrs "sta" = arrOf n e₇ := by
    rw [f₉ _ (by decide), f₈ _ (by decide)]; exact hA₇
  have hstd₉ : τ₉.arrs "std" = arrOf n e₈ := by
    rw [f₉ _ (by decide)]; exact hA₈
  refine ⟨τ₉, _,
    r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq (r₇.seq (r₈.seq r₉))))))), ?_,
    hn₉, hlw₉, hdoff₉, ⟨d₂, hdtg₉, hd₂v⟩,
    ⟨e₃, hooff₉, fun k hk => hZ₃ k (by omega)⟩,
    ⟨e₄, hoff₉, fun k hk => hZ₄ k (by omega)⟩,
    ⟨e₅, hnoff₉, fun k hk => hZ₅ k (by omega)⟩,
    ⟨e₆, hstf₉, hZ₆⟩, ⟨e₇, hsta₉, hZ₇⟩, ⟨e₈, hstd₉, hZ₈⟩, ⟨e₉, hA₉, hZ₉⟩⟩
  simp only [relinkCostSum, size_add, size_var, size_lit]
  omega

/-! ### The fold's invariant

What is true between two rounds: the machine holds the chain-so-far's
last orientation as the next round's input block structure, the
accumulators and stamps the relink re-zeroed, and the chain itself — the
family `D`, grown a round at a time, with the two clauses
`Augmentation.greedy_chain_inDegLE` consumes and the first elimination's
in-degree bound at its foot. `elm`, `bh` and `off` are *not* here: each
round's prep re-zeroes them, which is the F-c-5 repair. -/

/-- The invariant of the ordering phase's fold, after `i` rounds.

**Live width** (rebase G2/E2b): the scalar `"lw"` holds the runtime
value `lw` — between `ns` and `W`, no longer pinned to `W` — the `tgt`
tail at or above it stays zero across every round (the level's own
padding, which the restore counts on), and the chain-so-far's arc
count sits below `lw`, which is what lets each relink's live-prefix
copy carry the whole block structure. -/
def FoldInv (B n ns W lw d₀ : ℕ) (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (i : ℕ)
    (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "lw" = lw ∧
  Sized [("doff", n + 1), ("dtg", W), ("ooff", n + 1), ("otg", W), ("ofl", n),
      ("gof", n + 1), ("gtg", W), ("ffl", n), ("deg", n), ("rnk", n), ("idg", n),
      ("bh", n + 1), ("bv", n + W + 1), ("bn", n + W + 1), ("ioff", n + 1), ("ifl", n),
      ("itg", W), ("noff", n + 1), ("nfl", n), ("ntg", W), ("elm", n),
      ("stf", n), ("sta", n), ("std", n), ("ste", n)] σ ∧
  (∀ v ∈ σ.arrs "ntg", v < B) ∧
  (∃ g, σ.arrs "ooff" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0) ∧
  (∃ g, σ.arrs "noff" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0) ∧
  (∃ g, σ.arrs "stf" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
  (∃ g, σ.arrs "sta" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
  (∃ g, σ.arrs "std" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
  (∃ g, σ.arrs "ste" = arrOf n g ∧ ∀ k < n, g k = 0) ∧
  (∃ g, σ.arrs "off" = arrOf (n + 1) g) ∧
  (∃ g, σ.arrs "tgt" = arrOf W g ∧ ∀ z, lw ≤ z → z < W → g z = 0) ∧
  (∃ g, σ.arrs "alv" = arrOf n g) ∧
  ∃ (D : ℕ → Augmentation.Orientation n) (m' : ℕ) (DO DT : ℕ → ℕ),
    Augmentation.IsAugChain (masked G M) D i ∧
    (∀ l < i, Augmentation.GreedyFratRound (D l) (D (l + 1))) ∧
    (D 0).InDegLE d₀ ∧
    RamElim.InCsr (D i) m' DO DT ∧ m' ≤ lw ∧ (i = 0 → m' + m' ≤ ns) ∧
    σ.arrs "doff" = arrOf (n + 1) DO ∧ σ.arrs "dtg" = arrOf W DT

/-- **One round of the fold preserves the invariant** — the
chain-carrying step. The prep re-zeroes what the previous elimination
dirtied, `RamDriverAugment.implementsW` runs the round at the one width
`W`, `RamAugment.AugPost` hands back the augmentation step, the greedy
clause and the output block structure, and the relink makes that
structure the next round's input. The chain grows by
`Augmentation.isAugChain_succ`'s reading: the family is updated at
`i + 1` and nothing below moves. -/
theorem fold_step {B n ns W lw d D₁ d₀ R : ℕ} {G : SimpleGraph (Fin n)} {M : ℕ → ℕ}
    (hB : n + W + 1 < B) (hd₀d : d₀ ≤ d) (hlwW : lw ≤ W)
    (hdens : ∀ (D : ℕ → Augmentation.Orientation n) (i : ℕ), i ≤ R →
      Augmentation.IsAugChain (masked G M) D i →
      (∀ l < i, Augmentation.GreedyFratRound (D l) (D (l + 1))) →
      Augmentation.AugmentedDepthOneDensity D i D₁)
    (hWc : TgtCoupling.chainWidthE n ns d D₁ R ≤ lw) :
    ∀ i σ, i < R → FoldInv B n ns W lw d₀ G M i σ →
      ∃ σ', Run B (augRoundCom) σ σ' (RamAugment.augCost n W + relinkCost n W) ∧
        FoldInv B n ns W lw d₀ G M (i + 1) σ' := by
  intro i σ hiR hI
  obtain ⟨hn, hlw, hsz, hntgW, hooffZ, hnoffZ, hstfZ, hstaZ, hstdZ, hsteZ, hoffE, htgtE,
    halvE, D, m', DO, DT, hchain, hgreedy, hD0, hincsr, hm'lw, -, hdoff, hdtg⟩ := hI
  obtain ⟨Tc, htgtc, htailc⟩ := htgtE
  -- the round's in-degree budget, off the chain so far
  set bi := Augmentation.budget d D₁ i with hbi_def
  have hbi : (D i).InDegLE bi :=
    Augmentation.greedy_chain_inDegLE hchain
      (hdens D i (by omega) hchain hgreedy) hgreedy
      (fun v => le_trans (hD0 v) hd₀d) i le_rfl
  -- the two E-width capacities, from the repaired width (rebase G2/E2):
  -- the round's fraternity term sits under the last budget's, and the
  -- raw assembly arcs under the *next* budget — no `n · n` room used
  have hbR : bi ≤ Augmentation.budget d D₁ R :=
    TgtCoupling.budget_mono d D₁ (le_of_lt hiR)
  have hsqR : n * (bi + 1) ^ 2 ≤ n * (Augmentation.budget d D₁ R + 1) ^ 2 :=
    Nat.mul_le_mul_left n (Nat.pow_le_pow_left (by omega) 2)
  have hsqW : n * (bi + 1) ^ 2 < W := by
    have h2 := hWc
    simp only [TgtCoupling.chainWidthE] at h2
    omega
  have hcapW : n * (2 * (bi * bi) + bi) ≤ W := by
    have h1 : 2 * (bi * bi) + bi ≤ Augmentation.budget d D₁ (i + 1) :=
      TgtCoupling.two_sq_add_le_budget_succ d D₁ i
    have h2 : Augmentation.budget d D₁ (i + 1) ≤ Augmentation.budget d D₁ R :=
      TgtCoupling.budget_mono d D₁ (by omega)
    have h3 : n * (2 * (bi * bi) + bi) ≤ n * Augmentation.budget d D₁ R :=
      Nat.mul_le_mul_left n (by omega)
    have h4 : n * Augmentation.budget d D₁ R ≤
        n * (Augmentation.budget d D₁ R + 1) ^ 2 :=
      Nat.mul_le_mul_left n (by nlinarith)
    have h5 := hWc
    simp only [TgtCoupling.chainWidthE] at h5
    omega
  -- the fraternity graph fits the LIVE width, not just the allocation:
  -- this is what keeps the round's `tgt` writes inside the prefix the
  -- copies preserve
  have hfratL : RamAugment.fratSlots (D i) ≤ lw := by
    have h1 : RamAugment.fratSlots (D i) ≤ n * (bi * bi) := RamAugment.fratSlots_le hbi
    have h2 : n * (bi * bi) ≤ n * (bi + 1) ^ 2 := Nat.mul_le_mul_left n (by nlinarith)
    have h5 := hWc
    simp only [TgtCoupling.chainWidthE] at h5
    omega
  have hfrat : RamAugment.fratSlots (D i) ≤ W := le_trans hfratL hlwW
  -- (1) the prep: what the previous elimination dirtied, zeroed again
  obtain ⟨σb, rb, hnb, hoffZb, helmZb, hbhZb⟩ :=
    (augPrep_spec (B := B) (n := n) (by omega) (by omega)).run
      ⟨hn, hoffE, hsz.get (p := ("elm", n)) (by simp), hsz.get (p := ("bh", n + 1)) (by simp)⟩
  have fb : ∀ a : String, a ∉ augPrepCom.warrs → σb.arrs a = σ.arrs a :=
    fun a ha => rb.frame_arr a ha
  have hlwb : σb.vars "lw" = lw := by rw [rb.frame_var "lw" (by decide)]; exact hlw
  have htgtcb : σb.arrs "tgt" = arrOf W Tc := by
    rw [fb "tgt" (by rw [warrs_augPrepCom]; decide)]; exact htgtc
  have hszb := hsz.run rb
  -- (2) the round
  obtain ⟨g₃, hg₃, hz₃⟩ := hooffZ
  obtain ⟨g₅, hg₅, hz₅⟩ := hnoffZ
  obtain ⟨g₆, hg₆, hz₆⟩ := hstfZ
  obtain ⟨g₇, hg₇, hz₇⟩ := hstaZ
  obtain ⟨g₈, hg₈, hz₈⟩ := hstdZ
  obtain ⟨g₉, hg₉, hz₉⟩ := hsteZ
  obtain ⟨σc, rc, hpost, htailRound⟩ :=
    (RamDriverAugment.augment_specWE (B := B) (n := n) (d := bi) (nt := W) (W := W)
        (m := m') (D := D i) (DO := DO) (DT := DT)
        hincsr hbi hfrat (by omega) hsqW hcapW hB).run
      ⟨hnb,
        by rw [fb "doff" (by rw [warrs_augPrepCom]; decide)]; exact hdoff,
        by rw [fb "dtg" (by rw [warrs_augPrepCom]; decide)]; exact hdtg,
        ⟨g₃, by rw [fb "ooff" (by rw [warrs_augPrepCom]; decide)]; exact hg₃, hz₃⟩,
        hszb.get (p := ("otg", W)) (by simp), hszb.get (p := ("ofl", n)) (by simp),
        hoffZb, ⟨Tc, htgtcb⟩, hszb.get (p := ("ffl", n)) (by simp),
        sizedRun rb halvE, hszb.get (p := ("deg", n)) (by simp), helmZb,
        hszb.get (p := ("rnk", n)) (by simp), hszb.get (p := ("idg", n)) (by simp),
        hbhZb, hszb.get (p := ("bv", n + W + 1)) (by simp),
        hszb.get (p := ("bn", n + W + 1)) (by simp),
        hszb.get (p := ("ioff", n + 1)) (by simp), hszb.get (p := ("ifl", n)) (by simp),
        hszb.get (p := ("itg", W)) (by simp),
        ⟨g₅, by rw [fb "noff" (by rw [warrs_augPrepCom]; decide)]; exact hg₅, hz₅⟩,
        hszb.get (p := ("nfl", n)) (by simp), hszb.get (p := ("ntg", W)) (by simp),
        ⟨g₆, by rw [fb "stf" (by rw [warrs_augPrepCom]; decide)]; exact hg₆, hz₆⟩,
        ⟨g₇, by rw [fb "sta" (by rw [warrs_augPrepCom]; decide)]; exact hg₇, hz₇⟩,
        ⟨g₈, by rw [fb "std" (by rw [warrs_augPrepCom]; decide)]; exact hg₈, hz₈⟩,
        ⟨g₉, by rw [fb "ste" (by rw [warrs_augPrepCom]; decide)]; exact hg₉, hz₉⟩⟩
  obtain ⟨R', NO, NT, k', m₂, D', hrnk', hkm', hnoff', hntg', hmn', hm₂W, hstep, hincsr',
    hkmin', hgreedy', hbud'⟩ := hpost
  have hszc := hszb.run rc
  have hnc : σc.vars "n" = n := by
    rw [rc.frame_var "n" n_notMem_augCom]
    exact hnb
  have hlwc : σc.vars "lw" = lw := by
    rw [rc.frame_var "lw" lw_notMem_augCom]
    exact hlwb
  have hNOB : ∀ k < n + 1, NO k < B := fun k hk =>
    lt_of_le_of_lt (le_trans (off_le_of_mono hincsr'.mono hincsr'.last k (by omega)) hm₂W)
      (by omega)
  -- (3) the relink: the round's output becomes the next round's input
  obtain ⟨σd, rd, hnd, hlwd, hdoffd, hdtgd, hooffd, hoffd, hnoffd, hstfd, hstad, hstdd,
      hsted⟩ :=
    (augRelink_spec (B := B) (n := n) (W := W) (lw := lw) (NO := NO) (NT := NT) (by omega)
        (by omega) (by omega) hlwW hNOB).run
      ⟨hnc, hlwc, hnoff', hntg', run_mem_arrs_lt rc "ntg" (run_mem_arrs_lt rb "ntg" hntgW),
        hszc.get (p := ("doff", n + 1)) (by simp), hszc.get (p := ("dtg", W)) (by simp),
        hszc.get (p := ("ooff", n + 1)) (by simp),
        sizedRun rc (by
          obtain ⟨g, hg, -⟩ := hoffZb
          exact ⟨g, hg⟩),
        hszc.get (p := ("stf", n)) (by simp), hszc.get (p := ("sta", n)) (by simp),
        hszc.get (p := ("std", n)) (by simp), hszc.get (p := ("ste", n)) (by simp)⟩
  -- the new family: the chain, one round longer
  obtain ⟨dg, hdtgdA, hdgv⟩ := hdtgd
  set Dnew : ℕ → Augmentation.Orientation n := fun l => if l = i + 1 then D' else D l
    with hDnew
  have hchainN : Augmentation.IsAugChain (masked G M) Dnew (i + 1) := by
    refine ⟨by simp only [hDnew, if_neg (show 0 ≠ i + 1 by omega)]; exact hchain.1,
      fun l hl => ?_⟩
    rcases Nat.lt_or_ge l i with h | h
    · simp only [hDnew, if_neg (show l ≠ i + 1 by omega),
        if_neg (show l + 1 ≠ i + 1 by omega)]
      exact hchain.2 l h
    · have hli : l = i := by omega
      subst hli
      simp only [hDnew, if_neg (show l ≠ l + 1 by omega), if_pos rfl]
      exact hstep
  have hgreedyN : ∀ l < i + 1, Augmentation.GreedyFratRound (Dnew l) (Dnew (l + 1)) := by
    intro l hl
    rcases Nat.lt_or_ge l i with h | h
    · simp only [hDnew, if_neg (show l ≠ i + 1 by omega),
        if_neg (show l + 1 ≠ i + 1 by omega)]
      exact hgreedy l h
    · have hli : l = i := by omega
      subst hli
      simp only [hDnew, if_neg (show l ≠ l + 1 by omega), if_pos rfl]
      exact hgreedy'
  have hD0N : (Dnew 0).InDegLE d₀ := by
    simp only [hDnew, if_neg (show 0 ≠ i + 1 by omega)]
    exact hD0
  -- the NEW last orientation's arcs also fit the live width: the chain
  -- one round longer is still greedy, so its budget is `budget (i + 1)`
  have hbN : (Dnew (i + 1)).InDegLE (Augmentation.budget d D₁ (i + 1)) :=
    Augmentation.greedy_chain_inDegLE hchainN
      (hdens Dnew (i + 1) (by omega) hchainN hgreedyN) hgreedyN
      (fun v => le_trans (hD0N v) hd₀d) (i + 1) le_rfl
  have hbD' : D'.InDegLE (Augmentation.budget d D₁ (i + 1)) := by
    simpa only [hDnew, if_pos rfl] using hbN
  have hm₂lw : m₂ ≤ lw := by
    have h1 : m₂ ≤ n * Augmentation.budget d D₁ (i + 1) :=
      RamDriverAugment.arcs_le hincsr' hbD'
    have h2 : Augmentation.budget d D₁ (i + 1) ≤ Augmentation.budget d D₁ R :=
      TgtCoupling.budget_mono d D₁ (by omega)
    have h3 : n * Augmentation.budget d D₁ (i + 1) ≤ n * Augmentation.budget d D₁ R :=
      Nat.mul_le_mul_left n h2
    have h4 : n * Augmentation.budget d D₁ R ≤
        n * (Augmentation.budget d D₁ R + 1) ^ 2 :=
      Nat.mul_le_mul_left n (by nlinarith)
    have h5 := hWc
    simp only [TgtCoupling.chainWidthE] at h5
    omega
  -- the copied prefix carries the whole structure
  have hincsrN : RamElim.InCsr D' m₂ NO dg :=
    RamDriverAugment.inCsr_congr_prefix hincsr' (fun j hj => hdgv j (by omega))
  -- the `tgt` tail above the live width is still zero: the round wrote
  -- only below its fraternity slots, which sit below `lw`
  have htgtd : ∃ g, σd.arrs "tgt" = arrOf W g ∧ ∀ z, lw ≤ z → z < W → g z = 0 := by
    obtain ⟨Tc', htgtc'⟩ :=
      sizedRun rc (⟨Tc, htgtcb⟩ : ∃ g, σb.arrs "tgt" = arrOf W g)
    refine ⟨Tc', by rw [rd.frame_arr "tgt" (by decide)]; exact htgtc', ?_⟩
    intro z hz hzW
    have h1 := htailRound z (le_trans hfratL hz) hzW
    rw [htgtc', getD_arrOf Tc' hzW, htgtcb, getD_arrOf Tc hzW] at h1
    rw [h1]
    exact htailc z hz hzW
  refine ⟨σd, (rb.seq (rc.seq rd)).mono (by
      have h1 := prep_relink_le n W
      have h2 : relinkCostSum n lw ≤ relinkCostSum n W := by
        simp only [relinkCostSum]; omega
      omega),
    hnd, hlwd, (hszc.run rd),
    run_mem_arrs_lt rd "ntg" (run_mem_arrs_lt rc "ntg" (run_mem_arrs_lt rb "ntg" hntgW)),
    hooffd, hnoffd, hstfd, hstad, hstdd, hsted,
    (by obtain ⟨g, hg, -⟩ := hoffd; exact ⟨g, hg⟩),
    htgtd,
    sizedRun rd (sizedRun rc (sizedRun rb halvE)),
    Dnew, m₂, NO, dg, hchainN, hgreedyN, hD0N,
    (by simp only [hDnew, if_pos rfl]; exact hincsrN),
    hm₂lw, (fun h => absurd h (by omega)), hdoffd, hdtgdA⟩

/-- **The fold, run**: `m` rounds from stage `j`, by induction on the
round count. -/
theorem fold_run_aux {B Kb : ℕ} {c : Com} {I : ℕ → Env → Prop} {R : ℕ}
    (hstep : ∀ j σ, j < R → I j σ → ∃ σ', Run B c σ σ' Kb ∧ I (j + 1) σ') :
    ∀ (m j : ℕ), j + m ≤ R → ∀ σ, I j σ →
      ∃ σ', Run B (foldRange (fun _ => c) m) σ σ' (m * Kb + 1) ∧ I (j + m) σ'
  | 0, j, _, σ, hI => by
      refine ⟨σ, ?_, by simpa using hI⟩
      rw [foldRange_zero]
      exact Run.skip.mono (by omega)
  | m + 1, j, hle, σ, hI => by
      obtain ⟨σ₁, r₁, hI₁⟩ := hstep j σ (by omega) hI
      obtain ⟨σ', r', hI'⟩ := fold_run_aux hstep m (j + 1) (by omega) σ₁ hI₁
      refine ⟨σ', ?_, by rw [show j + (m + 1) = j + 1 + m by omega]; exact hI'⟩
      rw [foldRange_const_succ]
      exact (r₁.seq r').mono (le_of_eq (by ring))

/-! ### The rank inversion, with its data

`RamDriverOrder.ordCom_spec`'s postcondition quantifies the permutation
away, and at `R = 0` that is enough — the phase's postcondition names
only *some* ordering. The `R*` phase's slot is about the ordering the
**final elimination** produced, so the walk needs the inversion facts
the landed lemma's loop invariant carries and its last step drops: the
order array inverts the rank array. This is that lemma with the final
weakening removed; the loop is `ordCom_spec`'s, step for step. -/

/-- **`RamDriver.ordCom` inverts the rank array**, with the inversion
kept. -/
theorem ordCom_specData {B n : ℕ} {R : ℕ → ℕ} (dst : String) (hdr : dst ≠ "rnk")
    (hnB : n < B) (hR : ∀ v < n, R v < n)
    (hinj : ∀ v < n, ∀ w < n, R v = R w → v = w) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.arrs "rnk" = arrOf n R ∧ (∃ g, σ.arrs dst = arrOf n g))
      (RamDriver.ordCom dst)
      (fun _ σ' => σ'.vars "n" = n ∧ σ'.arrs "rnk" = arrOf n R ∧
        ∃ g, σ'.arrs dst = arrOf n g ∧ (∀ c < n, g c < n) ∧
          (∀ c < n, R (g c) = c) ∧ (∀ v < n, g (R v) = v))
      (12 * n + 6) := by
  have hbody : Spec B
      (fun σ => (∃ g, σ.vars "n" = n ∧ σ.arrs "rnk" = arrOf n R ∧ σ.arrs dst = arrOf n g ∧
        σ.vars "z" ≤ n ∧ ∀ v < σ.vars "z", g (R v) = v) ∧ σ.vars "z" < n)
      (.seq (.store dst (.get "rnk" (.var "z")) (.var "z"))
        (.assign "z" (.add (.var "z") (.lit 1))))
      (fun σ σ' => (∃ g, σ'.vars "n" = n ∧ σ'.arrs "rnk" = arrOf n R ∧
        σ'.arrs dst = arrOf n g ∧ σ'.vars "z" ≤ n ∧ ∀ v < σ'.vars "z", g (R v) = v) ∧
        σ'.vars "z" = σ.vars "z" + 1) 8 := by
    refine Spec.of_exists fun σ hσ => ?_
    obtain ⟨⟨g, hn, hrnk, hordv, -, hinvv⟩, hz⟩ := hσ
    have hRz : R (σ.vars "z") < n := hR _ hz
    have h1 : Run B (.store dst (.get "rnk" (.var "z")) (.var "z")) σ
        (σ.setArr dst (R (σ.vars "z")) (σ.vars "z")) (1 + 2 + 1) := by
      have h := Run.store (B := B) (σ := σ) (a := dst) (i := .get "rnk" (.var "z"))
        (e := .var "z")
        (evalB_get (evalB_var (by omega)) (by rw [hrnk, getElem?_arrOf R hz]) (by omega))
        (evalB_var (by omega)) (by rw [hordv, length_arrOf]; exact hRz)
      simpa using h
    have h2 : Run B (.assign "z" (.add (.var "z") (.lit 1)))
        (σ.setArr dst (R (σ.vars "z")) (σ.vars "z"))
        ((σ.setArr dst (R (σ.vars "z")) (σ.vars "z")).setVar "z" (σ.vars "z" + 1)) (1 + 3) := by
      have h := Run.assign (B := B) (σ := σ.setArr dst (R (σ.vars "z")) (σ.vars "z"))
        (x := "z") (e := .add (.var "z") (.lit 1))
        (evalB_bin (evalB_var (by rw [vars_setArr]; omega)) (evalB_lit (by omega))
          (by simp only [Bop.apply_add, vars_setArr]; omega))
      rw [Bop.apply_add, vars_setArr] at h
      simpa using h
    refine ⟨_, _, h1.seq h2, by omega,
      ⟨upd g (R (σ.vars "z")) (σ.vars "z"), by simp [hn],
        by rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdr)]; exact hrnk, ?_,
        by simp; omega, ?_⟩, by simp⟩
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, hordv, set_arrOf_eq_upd]
    · intro v hv
      rw [vars_setVar, if_pos rfl] at hv
      rcases Nat.lt_or_ge v (σ.vars "z") with hlt | hge
      · rw [upd_of_ne _ (fun hc => absurd (hinj v (by omega) _ hz hc) (by omega))]
        exact hinvv v hlt
      · have : v = σ.vars "z" := by omega
        rw [this, upd_self]
  refine ((Spec.forRangeZero (B := B) "z" "n"
    (fun σ => ∃ g, σ.vars "n" = n ∧ σ.arrs "rnk" = arrOf n R ∧ σ.arrs dst = arrOf n g ∧
      σ.vars "z" ≤ n ∧ ∀ v < σ.vars "z", g (R v) = v) n 8 hnB
    (fun _ h => by obtain ⟨-, -, -, -, hzz, -⟩ := h; exact hzz)
    (fun _ h => by obtain ⟨-, hnn, -⟩ := h; exact hnn) hbody).pre ?_).post ?_
  · rintro σ ⟨hn, hrnk, ⟨g, hordv⟩⟩
    exact ⟨g, by simp [hn], by simp [hrnk], by simp [hordv], by simp,
      fun v hv => absurd hv (by simp)⟩
  · rintro σ σ' - ⟨⟨g, hn, hrnk, hordv, -, hinvv⟩, hzn⟩
    rw [hzn] at hinvv
    have hordlt : ∀ c < n, g c < n := by
      intro c hc
      obtain ⟨v, hv, rfl⟩ := RamDriverOrder.exists_preimage_of_inj hR hinj hc
      rw [hinvv v hv]; exact hv
    have hRo : ∀ c < n, R (g c) = c := by
      intro c hc
      obtain ⟨v, hv, rfl⟩ := RamDriverOrder.exists_preimage_of_inj hR hinj hc
      rw [hinvv v hv]
    exact ⟨hn, hrnk, g, hordv, hordlt, hRo, hinvv⟩

/-! ### The theorem -/

set_option maxHeartbeats 4000000 in
/-- **The ordering phase at `R` rounds, discharged.** The thirteen-step
walk of `orderImplements₀` at a general round count: the fold is the
chain-carrying induction `fold_run_aux`/`fold_step`, the two
eliminations *keep* the `RamElim.ElimPost`s the `R = 0` walk discards —
the first is the foot of the chain (`d₀` and its minimality against the
arena), the second, on the symmetrized graph of the chain's last
orientation, is its head (`k` and its minimality against
`(D R).toGraph`) — and the rank inversion keeps the inversion facts, so
the exported ordering is provably the final elimination's. What comes
out through the parametric slot is `OrderP`: the six-clause
`CoverDegree.AugChainData` bundle, which
`RamDriverRoot.wreachDeg_of_orderP` turns into the root's cover-degree
coefficient `hdeg`.

The three hypotheses beyond the obligation's own are the campaign's
mathematics, not the machine's: `hd` is a degeneracy bound of the
arena (what `d₀`'s minimality is measured against, and the foot of the
width budget), `hdens` is `Augmentation.AugmentedDepthOneDensity` for
every chain the fold could build — the one unproved statement of
`Augmentation`, inherited here as that file's header says it must be —
and `hWc` says the level's allocation width covers
`TgtCoupling.chainWidthE` — the degree-aware width (rebase G2/E2),
whose `ns` term replaces the old `chainWidth`'s fatal `n · n` — the one
width that serves every round (coupling (b) of F-c-3's design, repaired
per `g2-cost-design.md` §3(a)). At `R = 0` the obligation reduces to
the landed `orderImplements₀`'s: the fold is `Com.skip`, the cost is
`orderPhaseCost` on the nose (`orderPhaseCostR_zero`), and the slot
degenerates to the two elimination bounds
(`CoverDegree.augChainData_zero`). -/
theorem orderImplementsR {B cap mb ns W j R d D₁ : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    (hd : Augmentation.LowDegreeVertices (masked G M) d)
    (hdens : ∀ (D : ℕ → Augmentation.Orientation n) (i : ℕ), i ≤ R →
      Augmentation.IsAugChain (masked G M) D i →
      (∀ l < i, Augmentation.GreedyFratRound (D l) (D (l + 1))) →
      Augmentation.AugmentedDepthOneDensity D i D₁) :
    OrderImplementsRL B n R W cap mb ns j d D₁ G O T M Gm C := by
  intro dK hB hcsr hWB _helim _haug
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hσL, hWclw⟩ := hσ
  obtain ⟨hvn, hoff, htgt, halvj, hgamj, hcolj, hMB, hGmB, hCbit, hmem, hdep, hmv,
    hordmem, hpad0, hTBW, hmemcl⟩ := id hσL
  obtain ⟨hnsW, hlwp, hosz, hzelm, hzbh, hzooff, hznoff, hzstf, hzsta, hzstd, hzste, hwitg,
    hwntg⟩ := id hordmem
  -- the runtime live width, with the chain's budget inside it
  obtain ⟨lw, hlw⟩ : ∃ lw, σ.vars "lw" = lw := ⟨_, rfl⟩
  rw [hlw] at hlwp hWclw
  obtain ⟨hlwns, hlwW⟩ := hlwp
  have hnB : n < B := hB.n_lt
  have hn1B : n + 1 < B := hB.succ_lt
  have hnsB : ns < B := hB.ns_lt
  have h1B : 1 < B := hB.one_lt
  have hWltB : W < B := by omega
  have hnnsB : n + ns + 1 < B := by
    have := hB.arena; omega
  have hOB : ∀ k < n + 1, O k < B := fun k hk =>
    lt_of_le_of_lt (hcsr.csr.le_ns (by omega)) hnsB
  -- (1) the block structure out of the way — its live prefix
  obtain ⟨σ₁, r₁, hvn₁, hmv₁, hlw₁, hoff₁, htgt₁, hgof₁, ⟨Tg, hgtg₁, hTgpre⟩⟩ :=
    (RamDriverOrder.saveCsr_spec (ns := ns) (lw := lw) hn1B hWltB hlwW hOB
      (fun k hk => hTBW k (by omega))).run
      ⟨hvn, hmv, hlw, hoff, htgt, hosz.get (p := ("gof", n + 1)) (by simp),
        hosz.get (p := ("gtg", W)) (by simp)⟩
  have hsz₁ := hosz.run r₁
  have hmem₁ := levelMem_run r₁ hmem
  have f₁ : ∀ a : String, a ∉ (saveCsr).warrs → σ₁.arrs a = σ.arrs a :=
    fun a ha => r₁.frame_arr a ha
  -- (2) the depth's mask into the name the engine reads
  obtain ⟨σ₂, r₂, ⟨u₂, hu₂, hag₂⟩, -, hvn₂, -⟩ :=
    (RamDriverCluster.copyCom_spec B n n (alvName j) "alv" M (alvName_ne_alv j) hnB le_rfl
      hMB).run
      ⟨hmem₁.1.get (p := ("alv", n)) (by simp), hvn₁,
        by rw [f₁ _ (alvName_notMem_saveCsr j)]; exact halvj⟩
  have halv₂ : σ₂.arrs "alv" = arrOf n M := hu₂.trans (RamDriverOrder.arrOf_congr hag₂)
  have hsz₂ := hsz₁.run r₂
  have f₂ : ∀ a : String, a ∉ (copyCom (alvName j) "alv").warrs → σ₂.arrs a = σ₁.arrs a :=
    fun a ha => r₂.frame_arr a ha
  have helmσ₂ : ∀ v ∈ σ₂.arrs "elm", v = 0 := by
    rw [f₂ _ (lit_notMem_copyCom_alv j "elm"), f₁ _ (by rw [warrs_saveCsr]; decide)]
    exact hzelm
  have hbhσ₂ : ∀ v ∈ σ₂.arrs "bh", v = 0 := by
    rw [f₂ _ (lit_notMem_copyCom_alv j "bh"), f₁ _ (by rw [warrs_saveCsr]; decide)]
    exact hzbh
  -- (3) the first elimination — keeping the foot of the chain this time
  obtain ⟨σ₃, r₃, ⟨Ra, IOa, ITa, ka, ma, Ea, -, -, hioff₃, hitg₃, hma, -, horients₃,
      hindeg₃, -, htoG₃, -, -, -, hkmin₃, hincsr₃⟩, -⟩ :=
    (elimRank_specW (nt := W) hcsr hnnsB hMB hnsW hnsW).run
      ⟨hvn₂, by rw [f₂ _ (lit_notMem_copyCom_alv j "off")]; exact hoff₁,
        by rw [f₂ _ (lit_notMem_copyCom_alv j "tgt")]; exact htgt₁,
        halv₂, hsz₂.get (p := ("deg", n)) (by simp),
        zeroed_of_mem (hsz₂.length (p := ("elm", n)) (by simp)) helmσ₂,
        hsz₂.get (p := ("rnk", n)) (by simp), hsz₂.get (p := ("idg", n)) (by simp),
        (by
          obtain ⟨g, hg, hgz⟩ :=
            zeroed_of_mem (hsz₂.length (p := ("bh", n + 1)) (by simp)) hbhσ₂
          exact ⟨g, hg, fun k hk => hgz k (by omega)⟩),
        hsz₂.get (p := ("bv", n + W + 1)) (by simp),
        hsz₂.get (p := ("bn", n + W + 1)) (by simp),
        hsz₂.get (p := ("ioff", n + 1)) (by simp), hsz₂.get (p := ("ifl", n)) (by simp),
        hsz₂.get (p := ("itg", W)) (by simp)⟩
  have hsz₃ := hsz₂.run r₃
  have f₃ : ∀ a : String, a ∉ RamElim.elimCom.warrs → σ₃.arrs a = σ₂.arrs a :=
    fun a ha => r₃.frame_arr a ha
  have hvn₃ : σ₃.vars "n" = n := by rw [r₃.frame_var "n" (by decide)]; exact hvn₂
  have hIOB : ∀ k < n + 1, IOa k < B := fun k hk =>
    lt_of_le_of_lt (le_trans (off_le_of_mono hincsr₃.mono hincsr₃.last k (by omega)) hma) hnsB
  -- (4) the in-list offsets into the fold's input
  obtain ⟨σ₄, r₄, ⟨dg₄, hdg₄, hdgv₄⟩, -, hvn₄, hioff₄⟩ :=
    (RamDriverOrder.copyUpto_spec (B := B) (n + 1) (n + 1) "ioff" "doff"
        (.add (.var "n") (.lit 1)) IOa
        (fun τ => τ.vars "n" = n ∧ τ.arrs "ioff" = arrOf (n + 1) IOa) (by omega) hn1B le_rfl
        (fun _ _ hQ hv ha => ⟨(hv "n" (by decide)).trans hQ.1,
          by rw [ha "ioff" (by decide)]; exact hQ.2⟩)
        (fun _ hQ => evalB_succ_n hn1B hQ.1) (fun _ hQ => hQ.2) hIOB).run
      ⟨hsz₃.get (p := ("doff", n + 1)) (by simp), hvn₃, hioff₃⟩
  have hsz₄ := hsz₃.run r₄
  have f₄ : ∀ a : String, a ∉ (copyUpto "ioff" "doff" (.add (.var "n") (.lit 1))).warrs →
      σ₄.arrs a = σ₃.arrs a := fun a ha => r₄.frame_arr a ha
  have hdoff₄ : σ₄.arrs "doff" = arrOf (n + 1) IOa :=
    hdg₄.trans (RamDriverOrder.arrOf_congr hdgv₄)
  -- (5) the in-list targets
  have hitg₄ : σ₄.arrs "itg" = arrOf W ITa := by
    rw [f₄ _ (by rw [warrs_copyUpto]; decide)]; exact hitg₃
  have hITB : ∀ k < W, ITa k < B := fun k hk =>
    RamDriverOrder.lt_of_mem_words
      (run_mem_arrs_lt r₄ "itg" (run_mem_arrs_lt r₃ "itg"
        (run_mem_arrs_lt r₂ "itg" (run_mem_arrs_lt r₁ "itg" hwitg)))) hitg₄ hk
  have hlw₄ : σ₄.vars "lw" = lw := by
    rw [r₄.frame_var "lw" (by rw [wvars_copyUpto]; decide), r₃.frame_var "lw" (by decide),
      r₂.frame_var "lw" (by rw [wvars_copyCom]; decide)]
    exact hlw₁
  -- the arena's arcs fit the live prefix
  have hsub : ∀ u v : Fin n, Ea.toGraph.Adj u v → G.Adj u v := by
    intro u v h
    rw [htoG₃] at h
    exact (RamBfs.masked_adj.1 h).1
  have hfit : ma + ma ≤ ns := RamDriverAugment.two_mul_arcs_le hcsr hincsr₃ hsub
  obtain ⟨σ₅, r₅, ⟨dt₅, hdt₅, hdtv₅⟩, -, -⟩ :=
    (copyPrefix_spec (B := B) lw W W "itg" "dtg" (.var "lw") ITa
        (fun τ => τ.arrs "itg" = arrOf W ITa ∧ τ.vars "lw" = lw) (by omega) (by omega)
        hlwW hlwW
        (fun _ _ hQ hv ha => ⟨(ha "itg" (by decide)).trans hQ.1,
          (hv "lw" (by decide)).trans hQ.2⟩)
        (fun τ hQ => by
          have h := evalB_var (B := B) (σ := τ) (x := "lw")
            (show τ.vars "lw" < B by rw [hQ.2]; omega)
          rw [hQ.2] at h; exact h)
        (fun _ hQ => hQ.1) (fun k hk => hITB k (by omega))).run
      ⟨hsz₄.get (p := ("dtg", W)) (by simp), hitg₄, hlw₄⟩
  have hsz₅ := hsz₄.run r₅
  have f₅ : ∀ a : String, a ∉ (copyUpto "itg" "dtg" (.var "lw")).warrs →
      σ₅.arrs a = σ₄.arrs a := fun a ha => r₅.frame_arr a ha
  have hvn₅ : σ₅.vars "n" = n := by
    rw [r₅.frame_var "n" (by rw [wvars_copyUpto]; decide)]; exact hvn₄
  have hlw₅ : σ₅.vars "lw" = lw := by
    rw [r₅.frame_var "lw" (by rw [wvars_copyUpto]; decide)]; exact hlw₄
  have hdtg₅ : σ₅.arrs "dtg" = arrOf W dt₅ := hdt₅
  have hincsr₅ : RamElim.InCsr Ea ma IOa dt₅ :=
    RamDriverAugment.inCsr_congr_prefix hincsr₃ (fun j hj => hdtv₅ j (by omega))
  have hdoff₅ : σ₅.arrs "doff" = arrOf (n + 1) IOa := by
    rw [f₅ _ (by rw [warrs_copyUpto]; decide)]; exact hdoff₄
  -- the fold's entry invariant: the chain is one orientation long
  have hframe₅ : ∀ a : String, a ≠ "dtg" → a ≠ "doff" → a ∉ RamElim.elimCom.warrs →
      a ≠ "alv" → a ≠ "gof" → a ≠ "gtg" → σ₅.arrs a = σ.arrs a := by
    intro a h5 h4 h3 h2 hg1 hg2
    rw [f₅ _ (by rw [warrs_copyUpto]; simpa using h5),
      f₄ _ (by rw [warrs_copyUpto]; simpa using h4), f₃ _ h3,
      f₂ _ (by rw [warrs_copyCom]; simpa using h2),
      f₁ _ (by rw [warrs_saveCsr]; simp [hg1, hg2])]
  have hooffZ₅ : ∃ g, σ₅.arrs "ooff" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0 := by
    obtain ⟨g, hg, hz⟩ := zeroed_of_mem (hsz₅.length (p := ("ooff", n + 1)) (by simp))
      (by
        rw [hframe₅ "ooff" (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
        exact hzooff)
    exact ⟨g, hg, fun k hk => hz k (by omega)⟩
  have hnoffZ₅ : ∃ g, σ₅.arrs "noff" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0 := by
    obtain ⟨g, hg, hz⟩ := zeroed_of_mem (hsz₅.length (p := ("noff", n + 1)) (by simp))
      (by
        rw [hframe₅ "noff" (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
        exact hznoff)
    exact ⟨g, hg, fun k hk => hz k (by omega)⟩
  have hstfZ₅ : ∃ g, σ₅.arrs "stf" = arrOf n g ∧ ∀ k < n, g k = 0 :=
    zeroed_of_mem (hsz₅.length (p := ("stf", n)) (by simp))
      (by
        rw [hframe₅ "stf" (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
        exact hzstf)
  have hstaZ₅ : ∃ g, σ₅.arrs "sta" = arrOf n g ∧ ∀ k < n, g k = 0 :=
    zeroed_of_mem (hsz₅.length (p := ("sta", n)) (by simp))
      (by
        rw [hframe₅ "sta" (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
        exact hzsta)
  have hstdZ₅ : ∃ g, σ₅.arrs "std" = arrOf n g ∧ ∀ k < n, g k = 0 :=
    zeroed_of_mem (hsz₅.length (p := ("std", n)) (by simp))
      (by
        rw [hframe₅ "std" (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
        exact hzstd)
  have hsteZ₅ : ∃ g, σ₅.arrs "ste" = arrOf n g ∧ ∀ k < n, g k = 0 :=
    zeroed_of_mem (hsz₅.length (p := ("ste", n)) (by simp))
      (by
        rw [hframe₅ "ste" (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
        exact hzste)
  have hoff₅ : σ₅.arrs "off" = arrOf (n + 1) O := by
    rw [hframe₅ "off" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hoff
  have htgt₅ : σ₅.arrs "tgt" = arrOf W T := by
    rw [hframe₅ "tgt" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact htgt
  have hka_d : ka ≤ d := hkmin₃ d hd
  have hI0 : FoldInv B n ns W lw ka G M 0 σ₅ :=
    ⟨hvn₅, hlw₅, hsz₅,
      run_mem_arrs_lt r₅ "ntg" (run_mem_arrs_lt r₄ "ntg" (run_mem_arrs_lt r₃ "ntg"
        (run_mem_arrs_lt r₂ "ntg" (run_mem_arrs_lt r₁ "ntg" hwntg)))),
      hooffZ₅, hnoffZ₅, hstfZ₅, hstaZ₅, hstdZ₅, hsteZ₅,
      ⟨O, hoff₅⟩, ⟨T, htgt₅, fun z hz hzW => hpad0 z (by omega) hzW⟩,
      ⟨M, by rw [f₅ _ (by rw [warrs_copyUpto]; decide),
        f₄ _ (by rw [warrs_copyUpto]; decide), f₃ _ (by decide)]; exact halv₂⟩,
      (fun _ => Ea), ma, IOa, dt₅,
      ⟨horients₃, fun l hl => absurd hl (Nat.not_lt_zero l)⟩,
      (fun l hl => absurd hl (Nat.not_lt_zero l)), hindeg₃, hincsr₅, by omega,
      (fun _ => hfit), hdoff₅, hdtg₅⟩
  -- (6) the fold: `R` rounds, the chain built round by round
  obtain ⟨σF, rF, hIF⟩ :=
    fold_run_aux (fold_step hWB hka_d hlwW hdens hWclw) R 0 (by omega) σ₅ hI0
  have hIF' : FoldInv B n ns W lw ka G M R σF := by simpa using hIF
  obtain ⟨hvnF, hlwF, hszF, hntgWF, ⟨gOo, hgOo, hzOo⟩, hnoffZF, hstfZF, hstaZF, hstdZF,
    hsteZF,
    hoffEF, ⟨TF, hTF, hTFtail⟩, halvEF, D, mR, DO, DT, hchainR, hgreedyR, hD0F, hincsrR,
    hmRlw, hmR0, hdoffF, hdtgF⟩ := hIF'
  have fF : ∀ a : String, a ∉ augRoundCom.warrs → σF.arrs a = σ₅.arrs a := by
    intro a ha
    refine rF.frame_arr a fun h => ha ?_
    exact mem_warrs_foldRange_const h
  have fFv : ∀ y : String, y ∉ augRoundCom.wvars → σF.vars y = σ₅.vars y := by
    intro y hy
    refine rF.frame_var y fun h => hy ?_
    exact mem_wvars_foldRange_const h
  -- the width still covers twice the chain's arcs
  have hbR : (D R).InDegLE (Augmentation.budget d D₁ R) :=
    Augmentation.greedy_chain_inDegLE hchainR (hdens D R le_rfl hchainR hgreedyR) hgreedyR
      (fun v => le_trans (hD0F v) hka_d) R le_rfl
  have hmRn : mR ≤ n * Augmentation.budget d D₁ R := RamDriverAugment.arcs_le hincsrR hbR
  -- twice the chain's arcs fit the LIVE width: the tail above `lw`
  -- survives the symmetrization
  have h2mLw : mR + mR ≤ lw := by
    have hb2 : n * (2 * Augmentation.budget d D₁ R) ≤
        n * ((Augmentation.budget d D₁ R + 1) ^ 2) :=
      Nat.mul_le_mul_left n (by nlinarith)
    have h3 : n * ((Augmentation.budget d D₁ R + 1) ^ 2) ≤
        TgtCoupling.chainWidthE n ns d D₁ R := by
      simp only [TgtCoupling.chainWidthE]; omega
    have h1 : n * (2 * Augmentation.budget d D₁ R) = n * Augmentation.budget d D₁ R
        + n * Augmentation.budget d D₁ R := by ring
    omega
  have h2mW : mR + mR ≤ W := le_trans h2mLw hlwW
  -- (7) the chain's last orientation, symmetrized into `off`/`tgt`
  obtain ⟨σ₇, K₇, Os, Ts, r₇, hK₇, hoffS, htgtS, hcsrS, htailS, hfaS, hfvS⟩ :=
    RamDriverAugment.symPass_run (B := B) (W := W) (nt := W) (m := mR) (D := D R)
      (DO := DO) (DT := DT) (σ := σF) hn1B (by omega) (by omega) h2mW hvnF hincsrR
      hdoffF hdtgF ⟨gOo, hgOo, hzOo⟩ (hszF.get (p := ("ofl", n)) (by simp))
      (hszF.get (p := ("otg", W)) (by simp)) hoffEF hTF
  have hsz₇ := hszF.run r₇
  have hvn₇ : σ₇.vars "n" = n := by
    rw [hfvS "n" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hvnF
  have hlw₇ : σ₇.vars "lw" = lw := by
    rw [hfvS "lw" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hlwF
  have hmv₅ : σ₅.vars "m" + σ₅.vars "m" = ns := by
    rw [r₅.frame_var "m" (by rw [wvars_copyUpto]; decide),
      r₄.frame_var "m" (by rw [wvars_copyUpto]; decide),
      r₃.frame_var "m" (by decide),
      r₂.frame_var "m" (by rw [wvars_copyCom]; decide), hmv₁]
    exact hmv
  have hmv₇ : σ₇.vars "m" + σ₇.vars "m" = ns := by
    rw [hfvS "m" (by decide) (by decide) (by decide) (by decide) (by decide),
      fFv "m" (by
        intro h
        have := mem_wvars_augRoundCom _ h
        simp at this)]
    exact hmv₅
  have hgofF : σF.arrs "gof" = arrOf (n + 1) O := by
    rw [fF "gof" (by
        intro h
        have := mem_warrs_augRoundCom _ h
        simp at this),
      f₅ _ (by rw [warrs_copyUpto]; decide), f₄ _ (by rw [warrs_copyUpto]; decide),
      f₃ _ (by decide), f₂ _ (lit_notMem_copyCom_alv j "gof")]
    exact hgof₁
  have hgtgF : σF.arrs "gtg" = arrOf W Tg := by
    rw [fF "gtg" (by
        intro h
        have := mem_warrs_augRoundCom _ h
        simp at this),
      f₅ _ (by rw [warrs_copyUpto]; decide), f₄ _ (by rw [warrs_copyUpto]; decide),
      f₃ _ (by decide), f₂ _ (lit_notMem_copyCom_alv j "gtg")]
    exact hgtg₁
  have hgof₇ : σ₇.arrs "gof" = arrOf (n + 1) O := by
    rw [hfaS "gof" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hgofF
  have hgtg₇ : σ₇.arrs "gtg" = arrOf W Tg := by
    rw [hfaS "gtg" (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hgtgF
  -- (8) everything alive again
  obtain ⟨σ₈, r₈, ⟨A, hA₈, hA₈v⟩, -, hvn₈⟩ :=
    (RamDriverCluster.fillCom_spec B n "alv" 1 hnB h1B).run
      ⟨sizedRun r₇ halvEF, hvn₇⟩
  have hsz₈ := hsz₇.run r₈
  have hAB : ∀ z < n, A z < B := fun z hz => by rw [hA₈v z hz]; exact h1B
  have f₈ : ∀ a : String, a ≠ "alv" → σ₈.arrs a = σ₇.arrs a :=
    fun a ha => r₈.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  -- (9) the elimination scratch, re-zeroed
  obtain ⟨σ₉, r₉, hvn₉, helm₉, hbh₉⟩ :=
    (elimRezero_spec hnB hn1B).run
      ⟨hvn₈, hsz₈.get (p := ("elm", n)) (by simp), hsz₈.get (p := ("bh", n + 1)) (by simp)⟩
  have hsz₉ := hsz₈.run r₉
  have f₉ : ∀ a : String, a ∉ elimRezeroCom.warrs → σ₉.arrs a = σ₈.arrs a :=
    fun a ha => r₉.frame_arr a ha
  -- (10) the second elimination, on the symmetrized augmented graph —
  -- keeping the head of the chain this time
  obtain ⟨σ₁₀, r₁₀, ⟨R₁, IO₁, IT₁, k₂, m₂e, E₂, hrnkE, -, -, -, -, -, -, -, -, -, hbackE,
      -, -, hkminE, -⟩, R₂, hrnk₁₀, hRlt, hRinj⟩ :=
    (elimRank_specW (nt := W) hcsrS (by omega) hAB (by omega) (by omega)).run
      ⟨hvn₉,
        by rw [f₉ _ (by decide), f₈ _ (by decide)]; exact hoffS,
        by rw [f₉ _ (by decide), f₈ _ (by decide)]; exact htgtS,
        by rw [f₉ _ (by decide)]; exact hA₈,
        hsz₉.get (p := ("deg", n)) (by simp), helm₉,
        hsz₉.get (p := ("rnk", n)) (by simp), hsz₉.get (p := ("idg", n)) (by simp), hbh₉,
        hsz₉.get (p := ("bv", n + W + 1)) (by simp),
        hsz₉.get (p := ("bn", n + W + 1)) (by simp),
        hsz₉.get (p := ("ioff", n + 1)) (by simp), hsz₉.get (p := ("ifl", n)) (by simp),
        hsz₉.get (p := ("itg", W)) (by simp)⟩
  have hsz₁₀ := hsz₉.run r₁₀
  have hvn₁₀ : σ₁₀.vars "n" = n := by rw [r₁₀.frame_var "n" (by decide)]; exact hvn₉
  have f₁₀ : ∀ a : String, a ∉ RamElim.elimCom.warrs → σ₁₀.arrs a = σ₉.arrs a :=
    fun a ha => r₁₀.frame_arr a ha
  have hmaskA : masked ((D R).toGraph) A = (D R).toGraph :=
    RamElim.masked_of_all_alive _ (fun v hv => by rw [hA₈v v hv]; omega)
  -- (11) the level's own block structure back
  have hmv₁₀ : σ₁₀.vars "m" + σ₁₀.vars "m" = ns := by
    rw [r₁₀.frame_var "m" (by decide), r₉.frame_var "m" (by decide),
      r₈.frame_var "m" (by decide)]
    exact hmv₇
  have hlw₁₀ : σ₁₀.vars "lw" = lw := by
    rw [r₁₀.frame_var "lw" (by decide), r₉.frame_var "lw" (by decide),
      r₈.frame_var "lw" (by decide)]
    exact hlw₇
  have htgt₁₀ : σ₁₀.arrs "tgt" = arrOf W Ts := by
    rw [f₁₀ _ (by decide), f₉ _ (by decide), f₈ _ (by decide)]
    exact htgtS
  obtain ⟨σ₁₁, r₁₁, hvn₁₁, -, -, -, -, hoff₁₁, htgt₁₁⟩ :=
    (RamDriverOrder.restoreCsr_spec (ns := ns) (lw := lw) (T := T) hn1B hWltB hlwW hOB
      (fun k hk => by rw [hTgpre k hk]; exact hTBW k (by omega)) hTgpre
      (fun z hz hzW => by
        rw [htailS z (by omega) hzW, hTFtail z hz hzW, hpad0 z (by omega) hzW])).run
      ⟨hvn₁₀, hmv₁₀, hlw₁₀,
        by rw [f₁₀ _ (by decide), f₉ _ (by decide), f₈ _ (by decide)]; exact hgof₇,
        by rw [f₁₀ _ (by decide), f₉ _ (by decide), f₈ _ (by decide)]; exact hgtg₇,
        sizedRun r₁₀ (sizedRun r₉ (sizedRun r₈ ⟨Os, hoffS⟩)),
        htgt₁₀⟩
  have hsz₁₁ := hsz₁₀.run r₁₁
  have f₁₁ : ∀ a : String, a ∉ (restoreCsr).warrs → σ₁₁.arrs a = σ₁₀.arrs a :=
    fun a ha => r₁₁.frame_arr a ha
  -- (12) the rank array inverted into the order array, inversion kept
  obtain ⟨σ₁₂, r₁₂, hvn₁₂, -, gord, hord₁₂, hordlt, hRo, hinvv⟩ :=
    (ordCom_specData (B := B) (n := n) (R := R₂) (ordName j)
      (by simp [ordName, String.ext_iff]) hnB hRlt
      (fun v hv w hw h => congrArg Fin.val (hRinj (a₁ := ⟨v, hv⟩) (a₂ := ⟨w, hw⟩) h))).run
      ⟨hvn₁₁, by rw [f₁₁ _ (by rw [warrs_restoreCsr]; decide)]; exact hrnk₁₀,
        (hdep.run (r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (rF.seq (r₇.seq
          (r₈.seq (r₉.seq (r₁₀.seq r₁₁))))))))))).get j (p := (ordName j, n)) (by simp)⟩
  have hsz₁₂ := hsz₁₁.run r₁₂
  -- (13) the re-zeroing tail
  obtain ⟨ρ, r₁₃, hvn₁₃, z₁, z₂, z₃, z₄, z₅, z₆, z₇, z₈⟩ :=
    (orderZero_spec hnB hn1B).run
      ⟨hvn₁₂, hsz₁₂.get (p := ("elm", n)) (by simp),
        hsz₁₂.get (p := ("bh", n + 1)) (by simp), hsz₁₂.get (p := ("ooff", n + 1)) (by simp),
        hsz₁₂.get (p := ("noff", n + 1)) (by simp), hsz₁₂.get (p := ("stf", n)) (by simp),
        hsz₁₂.get (p := ("sta", n)) (by simp), hsz₁₂.get (p := ("std", n)) (by simp),
        hsz₁₂.get (p := ("ste", n)) (by simp)⟩
  have f₁₂ : ∀ a : String, a ≠ ordName j → σ₁₂.arrs a = σ₁₁.arrs a :=
    fun a ha => r₁₂.frame_arr a (by rw [warrs_ordCom]; simpa using ha)
  have f₁₃ : ∀ a : String, a ∉ orderZeroCom.warrs → ρ.arrs a = σ₁₂.arrs a :=
    fun a ha => r₁₃.frame_arr a ha
  have hoffρ : ρ.arrs "off" = arrOf (n + 1) O := by
    rw [f₁₃ _ (by rw [warrs_orderZeroCom]; decide),
      f₁₂ _ (by simp [ordName, String.ext_iff])]
    exact hoff₁₁
  have htgtρ : ρ.arrs "tgt" = arrOf W T := by
    rw [f₁₃ _ (by rw [warrs_orderZeroCom]; decide),
      f₁₂ _ (by simp [ordName, String.ext_iff])]
    exact htgt₁₁
  -- the two ranks are one function on the carrier
  have hR12 : ∀ v < n, R₁ v = R₂ v := by
    intro v hv
    have h : (arrOf n R₁)[v]? = (arrOf n R₂)[v]? := by rw [← hrnkE, ← hrnk₁₀]
    rw [getElem?_arrOf R₁ hv, getElem?_arrOf R₂ hv] at h
    exact Option.some.inj h
  -- the phase, assembled
  have hrT : Run B (orderCom R j) σ ρ _ :=
    r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (rF.seq (r₇.seq (r₈.seq (r₉.seq
      (r₁₀.seq (r₁₁.seq (r₁₂.seq r₁₃)))))))))))
  refine ⟨ρ, _, hrT, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, hMB, hGmB, hCbit, levelMem_run hrT hmem,
      hdep.run hrT, ?_,
      ⟨hnsW, by rw [hrT.frame_var "lw" lw_notMem_orderCom, hlw]; exact ⟨hlwns, hlwW⟩,
        hosz.run hrT, z₁, z₂, z₃, z₄, z₅, z₆, z₇, z₈,
        run_mem_arrs_lt hrT "itg" hwitg, run_mem_arrs_lt hrT "ntg" hwntg⟩, hpad0, hTBW,
      (by
        obtain ⟨Mem, mmj, hm1, hm2, hm3, hm4⟩ := hmemcl
        exact ⟨Mem, mmj, by rw [hrT.frame_arr _ (memName_notMem_orderCom j)]; exact hm1,
          by rw [hrT.frame_var _ (mnumName_notMem_orderCom j)]; exact hm2, hm3, hm4⟩)⟩,
    hrT.out_eq (noWrite_orderCom R j),
    fun a => hrT.frame_var _ (ctrName_notMem_orderCom a),
    fun a => hrT.frame_arr _ (gamName_notMem_orderCom a),
    RamCover.rankPerm n R₂ gord hRlt hordlt hRo hinvv, gord, ?_,
    RamCover.ordersBy_rankPerm n R₂ gord hRlt hordlt hRo hinvv, ?_⟩
  · -- the cost. At `R = 0` the widened terms sit below `ns`
    -- (`FoldInv`'s `i = 0` clause) and the omega is the landed one; at
    -- `R ≥ 1` they sit below `W` and the round term's surcharge pays.
    rw [orderPhaseCostR, orderPhaseCost]
    rw [RamDriverAugment.symCost] at hK₇
    simp only [RamElim.elimCost, size_add, size_var, size_lit]
    rcases Nat.eq_zero_or_pos R with hR0 | hRpos
    · subst hR0
      have hfit0 := hmR0 rfl
      simp only [Nat.zero_mul]
      omega
    · have hsplit : R * (RamAugment.augCost n W + relinkCost n W + 650 * W) =
          R * (RamAugment.augCost n W + relinkCost n W) + R * (650 * W) := by ring
      have h650 : 650 * W ≤ R * (650 * W) := Nat.le_mul_of_pos_left _ hRpos
      rw [hsplit]
      set X := R * (RamAugment.augCost n W + relinkCost n W) with hXdef
      set Y := R * (650 * W) with hYdef
      omega
  · exact hvn₁₃
  · exact hoffρ
  · exact htgtρ
  · rw [hrT.frame_arr _ alvName_notMem_orderCom]; exact halvj
  · rw [hrT.frame_arr _ (gamName_notMem_orderCom j)]; exact hgamj
  · intro c hc
    rw [hrT.frame_arr _ (colName_notMem_orderCom c)]; exact hcolj c hc
  · rw [hrT.frame_var "m" m_notMem_orderCom]; exact hmv
  · rw [f₁₃ _ (ordName_notMem_orderZeroCom j)]; exact hord₁₂
  · -- the slot: the chain, with its two ends
    refine ⟨D, ka, k₂, hchainR, hgreedyR, hD0F, hkmin₃, ?_, ?_⟩
    · -- `BackDegLE` at the exported permutation is the final
      -- elimination's, the two rank functions agreeing on the carrier
      have hb : Augmentation.BackDegLE ((D R).toGraph)
          (fun v : Fin n => R₁ (v : ℕ)) k₂ := by
        rw [← hmaskA]; exact hbackE
      have hfun : (fun v : Fin n =>
            ((RamCover.rankPerm n R₂ gord hRlt hordlt hRo hinvv v : Fin n) : ℕ))
          = fun v : Fin n => R₁ (v : ℕ) := funext fun v => (hR12 _ v.isLt).symm
      rw [hfun]
      exact hb
    · intro k' hk'
      exact hkminE k' (by rw [hmaskA]; exact hk')

end Rstar

end Lax3Proofs.RamDriverCompose
