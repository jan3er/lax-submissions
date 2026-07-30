import Lax3Proofs.RamDriverOrder
import Lax3Proofs.RamDriverBot

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

`orderImplements₀` is stated at `R = 0` because at `R > 0` the round's
own obligation, `RamDriver.AugAvail`, is **not discharged** —
`RamAugment.Implements` is the one engine walk the campaign has not
walked — and because the two `tgt` couplings `OrderImplements`'s
docstring records are still open: `RamAugment.AugPre` asks for `tgt` at
the fraternity graph's slot count while the driver's is the level's
`ns`, and nothing relates the width `W` to the in-degrees the chain
reaches.

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
open Lax3Proofs.RamElim (CsrSimple ElimPre ElimPost ElimMem elimCom elimCost adeg
  AfterDeg AfterBuck AfterLoop AfterOff)
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

theorem warrs_compactCom (j : ℕ) : (compactCom j).warrs = [cpsName j] := rfl

theorem wvars_compactCom (j : ℕ) :
    (compactCom j).wvars = [cnumName j, "i", cnumName j, "i"] := rfl

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
    (h : OrderMem B n ns W σ) (hr : Run B c σ σ' K) (hz : ∀ a ∈ zeroArrs, a ∉ c.warrs) :
    OrderMem B n ns W σ' := by
  obtain ⟨hle, hsz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨hle, hsz.run hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
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
    (hn : "n" ∉ c.wvars) (hm : "m" ∉ c.wvars)
    (hoff : "off" ∉ c.warrs) (htgt : "tgt" ∉ c.warrs)
    (halv : alvName j ∉ c.warrs) (hgam : gamName j ∉ c.warrs)
    (hcol : ∀ q : ℕ, colName j q ∉ c.warrs)
    (hz : ∀ a ∈ zeroArrs, a ∉ c.warrs) :
    LevelPre B n cap mb ns W O T j M Gm C σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨by rw [hr.frame_var "n" hn]; exact h1,
    by rw [hr.frame_arr "off" hoff]; exact h2,
    by rw [hr.frame_arr "tgt" htgt]; exact h3,
    by rw [hr.frame_arr _ halv]; exact h4,
    by rw [hr.frame_arr _ hgam]; exact h5,
    fun q hq => by rw [hr.frame_arr _ (hcol q)]; exact h6 q hq,
    h7, h8, h9, levelMem_run hr h10, h11.run hr,
    by rw [hr.frame_var "m" hm]; exact h12,
    orderMem_run h13 hr hz⟩

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
    fun c hc w => ?_, fun c hc p q hp₁ hp₂ hq₁ hq₂ he => ?_, h.asg_lt, h.asg_cover⟩
  · rw [← h.block c hc w]
    constructor
    · rintro ⟨p, hp1, hp2, hp3⟩
      exact ⟨p, hp1, hp2, by rw [← hX p (hblk c hc p hp2)]; exact hp3⟩
    · rintro ⟨p, hp1, hp2, hp3⟩
      exact ⟨p, hp1, hp2, by rw [hX p (hblk c hc p hp2)]; exact hp3⟩
  · refine h.block_inj c hc p q hp₁ hp₂ hq₁ hq₂ ?_
    rw [← hX p (hblk c hc p hp₂), ← hX q (hblk c hc q hq₂)]
    exact he

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

/-- The invariant of `RamDriver.compactCom`. -/
def CompInv (n j : ℕ) (Xoff : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs (xofName j) = arrOf (n + 1) Xoff ∧ σ.vars "i" ≤ n ∧
    ∃ cps : ℕ → ℕ, σ.arrs (cpsName j) = arrOf n cps ∧
      σ.vars (cnumName j) ≤ σ.vars "i" ∧ σ.vars (cnumName j) ≤ Xoff (σ.vars "i") ∧
      (∀ k < σ.vars (cnumName j), cps k < σ.vars "i" ∧ Xoff (cps k) < Xoff (cps k + 1)) ∧
      (∀ k k' : ℕ, k < k' → k' < σ.vars (cnumName j) → cps k < cps k') ∧
      (∀ c < σ.vars "i", Xoff c < Xoff (c + 1) → ∃ k < σ.vars (cnumName j), cps k = c)

theorem cpsName_ne_xofName (j a : ℕ) : cpsName j ≠ xofName a := by
  simp [cpsName, xofName, String.ext_iff]

/-- **One turn of the compaction scan.** The block at the counter is
tested for emptiness; if it is not empty the position is appended to the
list and the count goes up. -/
theorem compact_body {B n j : ℕ} {Xoff : ℕ → ℕ}
    (hnB : n < B) (hmono : ∀ c < n, Xoff c ≤ Xoff (c + 1))
    (hXB : ∀ k < n + 1, Xoff k < B) :
    Spec B (fun σ => CompInv n j Xoff σ ∧ σ.vars "i" < n)
      (.seq
        (.ite (.lt (.get (xofName j) (.var "i"))
            (.get (xofName j) (.add (.var "i") (.lit 1))))
          (.seq (.store (cpsName j) (.var (cnumName j)) (.var "i"))
            (.assign (cnumName j) (.add (.var (cnumName j)) (.lit 1))))
          .skip)
        (.assign "i" (.add (.var "i") (.lit 1))))
      (fun σ σ' => CompInv n j Xoff σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 19 := by
  have hnq : ("n" : String) ≠ cnumName j := by simp [cnumName, String.ext_iff]
  have hiq : ("i" : String) ≠ cnumName j := by simp [cnumName, String.ext_iff]
  have hxc : xofName j ≠ cpsName j := by simp [xofName, cpsName, String.ext_iff]
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hn, hxof, -, cps, hcps, hcle, hcX, hcpslt, hcpsmono, hcov⟩, hlt⟩ := hσ
  have hiB : σ.vars "i" < B := by omega
  have hKB : σ.vars (cnumName j) < B := by omega
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
  · -- the block is not empty: the position joins the list
    have hcond : (Cond.lt (Expr.get (xofName j) (.var "i"))
        (Expr.get (xofName j) (.add (.var "i") (.lit 1)))).evalB B σ = some true := by
      rw [evalB_condLt he1 he2]; simp [hne]
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
    refine ⟨_, _, (Run.ite_true hcond (hst.seq hbump)).seq (hstep _ hi₂), by simp,
      ?_, by simp⟩
    -- the invariant, with the position appended
    have hKρ : (((σ.setArr (cpsName j) (σ.vars (cnumName j)) (σ.vars "i")).setVar
        (cnumName j) (σ.vars (cnumName j) + 1)).setVar "i" (σ.vars "i" + 1)).vars
        (cnumName j) = σ.vars (cnumName j) + 1 := by simp [Ne.symm hiq]
    have hIρ : (((σ.setArr (cpsName j) (σ.vars (cnumName j)) (σ.vars "i")).setVar
        (cnumName j) (σ.vars (cnumName j) + 1)).setVar "i" (σ.vars "i" + 1)).vars "i"
        = σ.vars "i" + 1 := by simp
    refine ⟨by simp [hnq, hn], by simp [hxc, hxof], by rw [hIρ]; omega,
      fun k => if k = σ.vars (cnumName j) then σ.vars "i" else cps k,
      by simp [hcps, set_arrOf], by rw [hKρ, hIρ]; omega,
      by rw [hKρ, hIρ]; omega, ?_, ?_, ?_⟩
    · intro k hk
      rw [hKρ] at hk
      rw [hIρ]
      by_cases hkK : k = σ.vars (cnumName j)
      · subst hkK
        refine ⟨by simp, ?_⟩
        simp only [if_pos rfl]
        exact hne
      · have h₁ := (hcpslt k (by omega)).1
        have h₂ := (hcpslt k (by omega)).2
        refine ⟨by simp only [if_neg hkK]; omega, ?_⟩
        simp only [if_neg hkK]
        exact h₂
    · intro k k' hkk hk'
      rw [hKρ] at hk'
      by_cases hk'K : k' = σ.vars (cnumName j)
      · have h₁ := (hcpslt k (by omega)).1
        simp only [if_pos hk'K, if_neg (show k ≠ σ.vars (cnumName j) by omega)]
        omega
      · simp only [if_neg hk'K, if_neg (show k ≠ σ.vars (cnumName j) by omega)]
        exact hcpsmono k k' hkk (by omega)
    · intro c hc hnec
      rw [hIρ] at hc
      rw [hKρ]
      by_cases hci : c = σ.vars "i"
      · refine ⟨σ.vars (cnumName j), by omega, ?_⟩
        simp only [if_pos rfl]
        exact hci.symm
      · obtain ⟨k, hk, hkc⟩ := hcov c (by omega) hnec
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
    refine ⟨by simp [hnq, hn], by simp [hxof], by rw [hIρ]; omega, cps,
      by simp [hcps], by rw [hKρ, hIρ]; omega, by rw [hKρ, hIρ, hle]; exact hcX, ?_, ?_, ?_⟩
    · intro k hk
      rw [hKρ] at hk
      rw [hIρ]
      exact ⟨by have := (hcpslt k hk).1; omega, (hcpslt k hk).2⟩
    · intro k k' hkk hk'
      rw [hKρ] at hk'
      exact hcpsmono k k' hkk hk'
    · intro c hc hnec
      rw [hIρ] at hc
      rw [hKρ]
      refine hcov c ?_ hnec
      rcases Nat.lt_or_ge c (σ.vars "i") with h | h
      · exact h
      · exact absurd (show Xoff (σ.vars "i") < Xoff (σ.vars "i" + 1) by
          rw [show σ.vars "i" = c by omega]; exact hnec) hne

/-- The cost of the compaction scan: one carrier-width pass, whose turn
is a two-sided test and, at most, a store and two increments. -/
def compactCost (n : ℕ) : ℕ := 23 * n + 8

/-- **The compaction scan, discharged.** What it leaves is
`RamDriver.Compacted` at the depth's own two names. -/
theorem compact_spec {B n j : ℕ} {Xoff : ℕ → ℕ}
    (hnB : n < B) (hmono : ∀ c < n, Xoff c ≤ Xoff (c + 1))
    (hXB : ∀ k < n + 1, Xoff k < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs (xofName j) = arrOf (n + 1) Xoff ∧
        ∃ g : ℕ → ℕ, σ.arrs (cpsName j) = arrOf n g)
      (compactCom j)
      (fun _ σ' => σ'.vars "n" = n ∧ σ'.arrs (xofName j) = arrOf (n + 1) Xoff ∧
        ∃ cps : ℕ → ℕ, σ'.arrs (cpsName j) = arrOf n cps ∧
          Compacted n (σ'.vars (cnumName j)) (Xoff n) Xoff cps)
      (compactCost n) := by
  have hnq : ("n" : String) ≠ cnumName j := by simp [cnumName, String.ext_iff]
  have hiq : ("i" : String) ≠ cnumName j := by simp [cnumName, String.ext_iff]
  have hloop := Spec.forRangeZero (B := B) "i" "n" (CompInv n j Xoff) n 19 hnB
    (fun _ hτ => hτ.2.2.1) (fun _ hτ => hτ.1) (compact_body hnB hmono hXB)
  refine (Spec.seq (Spec.assign (B := B) (P := fun σ => σ.vars "n" = n ∧
        σ.arrs (xofName j) = arrOf (n + 1) Xoff ∧ ∃ g : ℕ → ℕ, σ.arrs (cpsName j) = arrOf n g)
      (x := cnumName j) (e := .lit 0) (f := fun _ => 0)
      (fun _ _ => evalB_lit (by omega)))
    hloop ?_ ?_).mono (by rw [compactCost]; simp only [size_lit]; omega)
  · -- the invariant holds once both counters are zeroed
    rintro σ σ' ⟨hn, hxof, g, hg⟩ rfl
    refine ⟨by simp [hnq, hn], by simpa using hxof, by simp, g, by simpa using hg,
      by simp [Ne.symm hiq], by simp [Ne.symm hiq], ?_, ?_, ?_⟩
    · intro k hk; simp [Ne.symm hiq] at hk
    · intro k k' _ hk'; simp [Ne.symm hiq] at hk'
    · intro c hc; simp at hc
  · rintro σ σ' σ'' - - ⟨⟨hn'', hxof'', -, cps, hcps, hcle, hcX, hcpslt, hcpsmono, hcov⟩,
      hi''⟩
    rw [hi''] at hcle hcX hcpslt hcov
    exact ⟨hn'', hxof'', cps, hcps,
      ⟨hcX, hcle, fun k hk => (hcpslt k hk).1, hcpsmono, fun k hk => (hcpslt k hk).2, hcov⟩⟩

/-- The cost of the cover phase: the pass, the two copies that set it
up, the four of `RamDriver.coverSave` — the member copy charged at the
whole cluster arena — and the compaction scan. -/
def coverPhaseCost (n ns : ℕ) : ℕ :=
  RamCover.coverCost n ns + 12 * (n * n) + 73 * n + 56

/-- **The cover phase of a level, discharged.** -/
theorem coverImplements {n : ℕ} {B cap mb ns W j : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)} {ord : ℕ → ℕ} :
    CoverImplements B cap mb ns W j G O T M Gm C π ord (coverPhaseCost n ns) := by
  intro hB hcsr _ hord
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hlev, hordarr, hordlt⟩ := hσ
  have hnB : n < B := hB.n_lt
  have hn1B : n + 1 < B := hB.succ_lt
  have hcovB := hB.cover
  have hnnB : n * n < B := by omega
  obtain ⟨hvn, hoff, htgt, halvj, -, -, hMB, -, -, hmem, hdep, -, -⟩ := id hlev
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
  have htgt₂ : σ₂.arrs "tgt" = arrOf ns T := by
    rw [hr₂.frame_arr _ (by rw [warrs_copyCom]; decide),
      hr₁.frame_arr _ (by rw [warrs_copyCom]; decide)]
    exact htgt
  -- (3) the pass
  obtain ⟨σ₃, hr₃, Xoff, Xmem, asg, m, hxoff₃, hxmem₃, hasg₃, hxp₃, hmle, hout⟩ :=
    (RamDriverOrder.coverPass_spec (r := cap) (A₀ := M) hcsr hord hcovB hMB).run
      ⟨⟨hvn₂, hoff₂, htgt₂, halvA₂, hordA₂, hmem₂.1.get (p := ("dist", n)) (by simp),
        hmem₂.1.get (p := ("q", n)) (by simp), hmem₂.1.get (p := ("asg", n)) (by simp),
        hmem₂.1.get (p := ("xoff", n + 1)) (by simp),
        hmem₂.1.get (p := ("xmem", n * n)) (by simp)⟩, hmem₂.2.1, hmem₂.2.2⟩
  have hdep₃ : DepthMem n cap mb σ₃ := hdep₂.run hr₃
  have hvn₃ : σ₃.vars "n" = n := by
    rw [hr₃.frame_var "n" (by rw [wvars_coverCom]; decide)]; exact hvn₂
  have hmB : m < B := by omega
  have hXoffB : ∀ k < n + 1, Xoff k < B := fun k hk =>
    lt_of_le_of_lt (le_trans (coverOut_off_le hout k (by omega)) hmle) hnnB
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
  obtain ⟨σ₈, hr₈, hvn₈, hxof₈, cps, hcps₈, hcompact⟩ :=
    (compact_spec (B := B) (j := j) hnB hout.mono hXoffB).run
      (σ := ρ) ⟨hvnρ, hxofρ, hdepρ.get j (p := (cpsName j, n)) (by simp)⟩
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
      (off_notMem_coverPhase cap j) (tgt_notMem_coverPhase cap j)
      (alvName_notMem_coverPhase cap j j) (gamName_notMem_coverPhase cap j j)
      (fun q => colName_notMem_coverPhase cap j j q) (zero_notMem_coverPhase cap j),
    hrT.out_eq (noWrite_coverPhase cap j),
    fun a => hrT.frame_var _ (ctrName_notMem_coverPhase cap j a),
    fun a => hrT.frame_arr _ (gamName_notMem_coverPhase cap j a),
    Xoff, v₅, asg, cps, m, σ₈.vars (cnumName j),
    ⟨?_, hxof₈, ?_, ?_, ?_, hmle, hordlt, coverOut_congr hout hagr₅⟩,
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
pass writes the representative table, the depth's own tables and the
generated evaluator's own names, and `LevelPre` speaks about none of
them. And the postcondition `RamDriverBot.BaseTabOk … (fun _ => n)` is
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
  intro hB hL hbot hbit
  have hlocal : ∀ β ∈ tablesAt q_top cap mb φ ℓ, IsLocal β :=
    fun β hβ => (FormulaTables.tableRank_of_mem_tablesAt ℓ β hβ).1
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hlev, hts, hbarr⟩ := hσ
  obtain ⟨σ', hrun, htab⟩ :=
    (RamDriverBot.base_spec hB.one_lt hB.n_lt hL hbit hlocal).run
      ⟨hlev.1, hlev.2.2.2.2.2.1, hbarr.2,
        hbarr.1.get (p := ("rep", 2 ^ sigL cap mb ℓ)) (by simp),
        fun i hi => hts.get ℓ hi⟩
  refine ⟨σ', _, hrun, le_rfl,
    ⟨levelPre_run hlev hrun
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
            (RamDriverBot.not_ext_of_not_prefix (by decide))),
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

/-- **The elimination, with the rank bound its own surface drops.** -/
theorem elimRank_spec {B ns W : ℕ} {G : SimpleGraph (Fin n)} {O T M : ℕ → ℕ}
    (hcsr : CsrSimple G ns O T) (hB : n + ns + 1 < B) (hMB : ∀ z < n, M z < B) (hW : ns ≤ W) :
    Spec B (ElimPre n ns W O T M) elimCom
      (fun σ σ' => ElimPost G M ns W σ σ' ∧
        ∃ R, σ'.arrs "rnk" = arrOf n R ∧ (∀ v < n, R v < n) ∧
          Function.Injective (fun v : Fin n => R (v : ℕ)))
      (elimCost n ns) := by
  have hDlt : ∀ v < n, adeg G M v < n := fun v hv => by
    rw [RamElim.adeg_eq hv]; exact RamElim.card_nbrsIn_lt _ _
  have w1 : Spec B (ElimPre n ns W O T M) RamElim.initDeg
      (fun _ σ' => AfterDeg n ns W G O T M σ') (48 * n + 44 * ns + 10) := by
    intro σ hσ
    obtain ⟨hn, hoff, htgt, halv, hdeg0, helm, hrnk, hidg, hbh, hbv, hbn, hioff, hifl,
      hitg⟩ := hσ
    obtain ⟨σ', hrun, ⟨hI, hi⟩, -, hfa, -, -⟩ :=
      (RamElim.initDeg_spec B n ns G O T M hcsr (by omega) (by omega) hMB).frame σ
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
  have w2 : Spec B (AfterDeg n ns W G O T M) RamElim.initBuck
      (fun _ σ' => AfterBuck n ns W G O T M σ') (29 * n + 10) := by
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
  have w3 : Spec B (AfterBuck n ns W G O T M) RamElim.elimLoop
      (fun _ σ' => AfterLoop n ns W G O T M σ') (160 * n + 100 * ns + 52) := by
    intro σ hσ
    obtain ⟨hbi, hi, hoff, htgt, halv, helm, hrnk, hidg, hioff, hifl, hitg⟩ := hσ
    obtain ⟨σ', hrun, ⟨R, ID, k, hn', hk', hrnk', hidg', hRlt, hcert, hIDc, hpsum⟩, -,
      hfa, -, -⟩ :=
      (RamElim.elimLoop_spec B n ns W G O T M (adeg G M) hcsr hB hW hMB (fun _ _ => rfl)).frame σ
        ⟨hbi, hi, hoff, htgt, halv, helm, hrnk, hidg⟩
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
  have w4 : Spec B (AfterLoop n ns W G O T M) RamElim.offPass
      (fun _ σ' => AfterOff n ns W G O T M σ') (24 * n + 12) := by
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
  have w5 : Spec B (AfterOff n ns W G O T M) RamElim.fillPass
      (fun _ σ' => ElimMem G M ns W σ' σ' ∧
        ∃ R, σ'.arrs "rnk" = arrOf n R ∧ (∀ v < n, R v < n) ∧
          Function.Injective (fun v : Fin n => R (v : ℕ)))
      (32 * n + 32 * ns + 10) := by
    intro σ hσ
    obtain ⟨R, ID, k, hn, hk, hoff, htgt, halv, hrnk, hRlt, hcert, hIDc, hpsum, hioff,
      hifl, hitg⟩ := hσ
    obtain ⟨g, hioffg, hioffv⟩ := hioff
    obtain ⟨σ', hrun, ⟨IT, hitg', harcs⟩, hfv, hfa, -, -⟩ :=
      (RamElim.fillPass_spec B n ns W G O T M R ID hcsr hB hW hMB hRlt hIDc hpsum).frame σ
        ⟨hn, hoff, htgt, halv, hrnk, hifl, hitg⟩
    have hrnk' : σ'.arrs "rnk" = arrOf n R := by
      rw [hfa "rnk" (by decide)]; exact hrnk
    exact ⟨σ', hrun, ⟨R, RamElim.psum ID, IT, k, RamElim.psum ID n, hrnk',
      by rw [hfv "kmax" (by decide)]; exact hk,
      by rw [hfa "ioff" (by decide), hioffg]
         exact RamDriverOrder.arrOf_congr (fun j hj => hioffv j (by omega)),
      hitg', by omega, ⟨hcert, harcs⟩⟩, R, hrnk', hRlt, hcert.inj⟩
  have hall : Spec B (ElimPre n ns W O T M) elimCom
      (fun _ σ' => ElimMem G M ns W σ' σ' ∧
        ∃ R, σ'.arrs "rnk" = arrOf n R ∧ (∀ v < n, R v < n) ∧
          Function.Injective (fun v : Fin n => R (v : ℕ)))
      (elimCost n ns) := by
    show Spec B (ElimPre n ns W O T M) elimCom _ (600 * n + 600 * ns + 100)
    run_vcg [w1, w2, w3, w4, w5] <;> assumption
  exact hall.post fun _ _ _ hq => ⟨RamElim.elimPost_of_elimMem hq.1, hq.2⟩

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

variable (W j : ℕ)

/-! ### What the ordering phase writes

`RamDriver.orderCom 0 W j` assigns no scalar the level's state names and
writes no array of it except `off` and `tgt` — which `restoreCsr` puts
back — and the eight of `OrderMem`'s zeroing half, which the tail puts
back. Its scalar write set does not mention `W` or `j` at all, so it is
the write set at `0 0`; its array write set mentions `j` once, at the
depth's own order array. -/

/-- The scalars the phase assigns do not depend on its parameters. -/
theorem wvars_orderCom₀ (W j : ℕ) : (orderCom 0 W j).wvars = (orderCom 0 0 0).wvars := rfl

/-- The arrays it writes, in order. -/
theorem warrs_orderCom₀ (W j : ℕ) : (orderCom 0 W j).warrs =
    ["gof", "gtg", "alv", "deg", "deg", "bv", "bn", "bh", "bh", "elm", "rnk", "idg", "deg",
      "bv", "bn", "bh", "ioff", "ifl", "ioff", "itg", "ifl", "doff", "dtg", "off", "tgt",
      "alv", "elm", "bh", "deg", "deg", "bv", "bn", "bh", "bh", "elm", "rnk", "idg", "deg",
      "bv", "bn", "bh", "ioff", "ifl", "ioff", "itg", "ifl", ordName j, "elm", "bh", "ooff",
      "noff", "stf", "sta", "std", "ste"] := rfl

/-- It never writes to the output tape. -/
theorem noWrite_orderCom₀ (W j : ℕ) : (orderCom 0 W j).NoWrite :=
  show (orderCom 0 0 0).NoWrite by decide

set_option maxRecDepth 8000 in
/-- Every scalar it assigns is one of sixteen short literals. -/
theorem mem_wvars_orderCom₀ : ∀ y ∈ (orderCom 0 0 0).wvars,
    y ∈ ["i", "c", "j", "jend", "u", "sp", "ls", "d", "mind", "cnt", "kmax", "sc", "p", "w",
      "s", "z"] := by decide

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
theorem n_notMem_orderCom₀ : "n" ∉ (orderCom 0 W j).wvars := by
  rw [wvars_orderCom₀]; decide

/-- Nor is the slot count. -/
theorem m_notMem_orderCom₀ : "m" ∉ (orderCom 0 W j).wvars := by
  rw [wvars_orderCom₀]; decide

/-- Nor is any depth's connector. -/
theorem ctrName_notMem_orderCom₀ (a : ℕ) : ctrName a ∉ (orderCom 0 W j).wvars := by
  rw [wvars_orderCom₀]
  intro h
  have h' := mem_wvars_orderCom₀ _ h
  simp [ctrName, String.ext_iff] at h'

/-- No depth's game mask is written. -/
theorem gamName_notMem_orderCom₀ (a : ℕ) : gamName a ∉ (orderCom 0 W j).warrs := by
  rw [warrs_orderCom₀]; simp [gamName, ordName, String.ext_iff]

/-- Nor the depth's own work mask. -/
theorem alvName_notMem_orderCom₀ : alvName j ∉ (orderCom 0 W j).warrs := by
  rw [warrs_orderCom₀]; simp [alvName, ordName, String.ext_iff]

/-- Nor any of its colours. -/
theorem colName_notMem_orderCom₀ (c : ℕ) : colName j c ∉ (orderCom 0 W j).warrs := by
  rw [warrs_orderCom₀]; simp [colName, ordName, String.ext_iff]

/-- The tail leaves the order array the inversion just wrote. -/
theorem ordName_notMem_orderZeroCom : ordName j ∉ orderZeroCom.warrs := by
  rw [warrs_orderZeroCom]; simp [ordName, String.ext_iff]

end Syntax

/-- **The cost of the ordering phase at `R = 0`**: the two eliminations,
the four block-structure copies, the two in-list copies, the mask fill
and the ten zeroing fills. The constants are generous, as everywhere in
this campaign: the sharp charging is the cost wave's business. -/
def orderPhaseCost (n ns W : ℕ) : ℕ := 1400 * n + 1250 * ns + 20 * W + 450

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
    OrderImplements B n 0 W cap mb ns j G O T M Gm C (orderPhaseCost n ns W) := by
  intro hB hcsr hWB _helim _haug
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hvn, hoff, htgt, halvj, hgamj, hcolj, hMB, hGmB, hCbit, hmem, hdep, hmv,
    hordmem⟩ := id hσ
  obtain ⟨hnsW, hosz, hzelm, hzbh, -, -, -, -, -, -, hwitg, hwntg⟩ := id hordmem
  have hnB : n < B := hB.n_lt
  have hn1B : n + 1 < B := hB.succ_lt
  have hnsB : ns < B := hB.ns_lt
  have h1B : 1 < B := hB.one_lt
  have hWltB : W < B := by omega
  have hnnsB : n + ns + 1 < B := by
    have := le_mul_self n; have := hB.cover; omega
  have hOB : ∀ k < n + 1, O k < B := fun k hk =>
    lt_of_le_of_lt (hcsr.csr.le_ns (by omega)) hnsB
  have hTB : ∀ k < ns, T k < B := fun k hk => lt_trans (hcsr.csr.target_lt k hk) hnB
  -- (1) the block structure out of the way
  obtain ⟨σ₁, r₁, hvn₁, hmv₁, hoff₁, htgt₁, hgof₁, hgtg₁⟩ :=
    (RamDriverOrder.saveCsr_spec hn1B hnsB hOB hTB).run
      ⟨hvn, hmv, hoff, htgt, hosz.get (p := ("gof", n + 1)) (by simp),
        hosz.get (p := ("gtg", ns)) (by simp)⟩
  have hsz₁ := hosz.run r₁
  have hmem₁ := levelMem_run r₁ hmem
  have f₁ : ∀ a : String, a ∉ saveCsr.warrs → σ₁.arrs a = σ.arrs a := fun a ha => r₁.frame_arr a ha
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
    rw [f₂ _ (lit_notMem_copyCom_alv j "elm"), f₁ _ (by decide)]; exact hzelm
  have hbhσ₂ : ∀ v ∈ σ₂.arrs "bh", v = 0 := by
    rw [f₂ _ (lit_notMem_copyCom_alv j "bh"), f₁ _ (by decide)]; exact hzbh
  -- (3) the first elimination
  obtain ⟨σ₃, r₃, ⟨Ra, IOa, ITz, ka, ma, Ea, -, -, hioff₃, -, hma, -, -, -, -, -, -, -, -, -,
      hincsr₃⟩, -⟩ :=
    (elimRank_spec hcsr hnnsB hMB hnsW).run
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
  obtain ⟨σ₄, r₄, -, -, hvn₄, hioff₄⟩ :=
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
  -- (5) the in-list targets
  obtain ⟨ITa, hitg₄⟩ := hsz₄.get (p := ("itg", W)) (by simp)
  have hITB : ∀ k < W, ITa k < B := fun k hk =>
    RamDriverOrder.lt_of_mem_words
      (run_mem_arrs_lt r₄ "itg" (run_mem_arrs_lt r₃ "itg"
        (run_mem_arrs_lt r₂ "itg" (run_mem_arrs_lt r₁ "itg" hwitg)))) hitg₄ hk
  obtain ⟨σ₅, r₅, -, -, -⟩ :=
    (RamDriverOrder.copyUpto_spec (B := B) W W "itg" "dtg" (.lit W) ITa
        (fun τ => τ.arrs "itg" = arrOf W ITa) (by omega) hWltB le_rfl
        (fun _ _ hQ _ ha => (ha "itg" (by decide)).trans hQ)
        (fun _ _ => evalB_lit hWltB) (fun _ hQ => hQ) hITB).run
      ⟨hsz₄.get (p := ("dtg", W)) (by simp), hitg₄⟩
  have hsz₅ := hsz₄.run r₅
  have f₅ : ∀ a : String, a ∉ (copyUpto "itg" "dtg" (.lit W)).warrs → σ₅.arrs a = σ₄.arrs a :=
    fun a ha => r₅.frame_arr a ha
  have hvn₅ : σ₅.vars "n" = n := by
    rw [r₅.frame_var "n" (by rw [wvars_copyUpto]; decide)]; exact hvn₄
  -- (6) no augmentation round: the fold is empty
  have r₆ : Run B (foldRange (fun _ => .seq RamAugment.augCom (augRelinkCom W)) 0) σ₅ σ₅ 1 :=
    Run.skip
  have hgof₅ : σ₅.arrs "gof" = arrOf (n + 1) O := by
    rw [f₅ _ (by rw [warrs_copyUpto]; decide),
      f₄ _ (by rw [warrs_copyUpto]; decide), f₃ _ (by decide),
      f₂ _ (lit_notMem_copyCom_alv j "gof")]
    exact hgof₁
  have hgtg₅ : σ₅.arrs "gtg" = arrOf ns T := by
    rw [f₅ _ (by rw [warrs_copyUpto]; decide),
      f₄ _ (by rw [warrs_copyUpto]; decide), f₃ _ (by decide),
      f₂ _ (lit_notMem_copyCom_alv j "gtg")]
    exact hgtg₁
  -- (7) the block structure back
  have hmv₅ : σ₅.vars "m" + σ₅.vars "m" = ns := by
    rw [r₅.frame_var "m" (by rw [wvars_copyUpto]; decide),
      r₄.frame_var "m" (by rw [wvars_copyUpto]; decide),
      r₃.frame_var "m" (by decide),
      r₂.frame_var "m" (by rw [wvars_copyCom]; decide), hmv₁]
    exact hmv
  obtain ⟨σ₇, r₇, hvn₇, hmv₇, -, -, hoff₇, htgt₇⟩ :=
    (RamDriverOrder.restoreCsr_spec hn1B hnsB hOB hTB).run
      ⟨hvn₅, hmv₅,
        hgof₅, hgtg₅,
        sizedRun r₅ (sizedRun r₄ (sizedRun r₃ (sizedRun r₂ ⟨O, hoff₁⟩))),
        sizedRun r₅ (sizedRun r₄ (sizedRun r₃ (sizedRun r₂ ⟨T, htgt₁⟩)))⟩
  have hsz₇ := hsz₅.run r₇
  have f₇ : ∀ a : String, a ∉ restoreCsr.warrs → σ₇.arrs a = σ₅.arrs a :=
    fun a ha => r₇.frame_arr a ha
  -- (8) everything alive again
  obtain ⟨σ₈, r₈, ⟨A, hA₈, hA₈v⟩, -, hvn₈⟩ :=
    (RamDriverCluster.fillCom_spec B n "alv" 1 hnB h1B).run
      ⟨sizedRun r₇ (sizedRun r₅ (sizedRun r₄ (sizedRun r₃ ⟨M, halv₂⟩))), hvn₇⟩
  have hsz₈ := hsz₇.run r₈
  have hAB : ∀ z < n, A z < B := fun z hz => by rw [hA₈v z hz]; exact h1B
  -- (9) the elimination scratch, re-zeroed
  obtain ⟨σ₉, r₉, hvn₉, helm₉, hbh₉⟩ :=
    (elimRezero_spec hnB hn1B).run
      ⟨hvn₈, hsz₈.get (p := ("elm", n)) (by simp), hsz₈.get (p := ("bh", n + 1)) (by simp)⟩
  have hsz₉ := hsz₈.run r₉
  have f₉ : ∀ a : String, a ∉ elimRezeroCom.warrs → σ₉.arrs a = σ₈.arrs a :=
    fun a ha => r₉.frame_arr a ha
  -- (10) the second elimination
  obtain ⟨σ₁₀, r₁₀, -, R, hrnk₁₀, hRlt, hRinj⟩ :=
    (elimRank_spec hcsr hnnsB hAB hnsW).run
      ⟨hvn₉,
        by rw [f₉ _ (by decide), r₈.frame_arr "off" (by rw [warrs_fillCom]; decide)]
           exact hoff₇,
        by rw [f₉ _ (by decide), r₈.frame_arr "tgt" (by rw [warrs_fillCom]; decide)]
           exact htgt₇,
        by rw [f₉ _ (by decide)]; exact hA₈,
        hsz₉.get (p := ("deg", n)) (by simp), helm₉,
        hsz₉.get (p := ("rnk", n)) (by simp), hsz₉.get (p := ("idg", n)) (by simp), hbh₉,
        hsz₉.get (p := ("bv", n + W + 1)) (by simp),
        hsz₉.get (p := ("bn", n + W + 1)) (by simp),
        hsz₉.get (p := ("ioff", n + 1)) (by simp), hsz₉.get (p := ("ifl", n)) (by simp),
        hsz₉.get (p := ("itg", W)) (by simp)⟩
  have hsz₁₀ := hsz₉.run r₁₀
  have hvn₁₀ : σ₁₀.vars "n" = n := by rw [r₁₀.frame_var "n" (by decide)]; exact hvn₉
  -- (11) the rank array inverted into the order array
  obtain ⟨σ₁₁, r₁₁, hvn₁₁, -, π, ordv, hord₁₁, hordby⟩ :=
    (RamDriverOrder.ordCom_spec (B := B) (ordName j) (by simp [ordName, String.ext_iff]) hnB
      hRlt (fun v hv w hw h => congrArg Fin.val (hRinj (a₁ := ⟨v, hv⟩) (a₂ := ⟨w, hw⟩) h))).run
      ⟨hvn₁₀, hrnk₁₀, (hdep.run (r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₇.seq
        (r₈.seq (r₉.seq r₁₀)))))))) ).get j (p := (ordName j, n)) (by simp)⟩
  have hsz₁₁ := hsz₁₀.run r₁₁
  -- (12) the re-zeroing tail
  obtain ⟨ρ, r₁₂, hvn₁₂, z₁, z₂, z₃, z₄, z₅, z₆, z₇, z₈⟩ :=
    (orderZero_spec hnB hn1B).run
      ⟨hvn₁₁, hsz₁₁.get (p := ("elm", n)) (by simp),
        hsz₁₁.get (p := ("bh", n + 1)) (by simp), hsz₁₁.get (p := ("ooff", n + 1)) (by simp),
        hsz₁₁.get (p := ("noff", n + 1)) (by simp), hsz₁₁.get (p := ("stf", n)) (by simp),
        hsz₁₁.get (p := ("sta", n)) (by simp), hsz₁₁.get (p := ("std", n)) (by simp),
        hsz₁₁.get (p := ("ste", n)) (by simp)⟩
  have f₈ : ∀ a : String, a ≠ "alv" → σ₈.arrs a = σ₇.arrs a :=
    fun a ha => r₈.frame_arr a (by rw [warrs_fillCom]; simpa using ha)
  have f₁₀ : ∀ a : String, a ∉ RamElim.elimCom.warrs → σ₁₀.arrs a = σ₉.arrs a :=
    fun a ha => r₁₀.frame_arr a ha
  have f₁₁ : ∀ a : String, a ≠ ordName j → σ₁₁.arrs a = σ₁₀.arrs a :=
    fun a ha => r₁₁.frame_arr a (by rw [warrs_ordCom]; simpa using ha)
  have f₁₂ : ∀ a : String, a ∉ orderZeroCom.warrs → ρ.arrs a = σ₁₁.arrs a :=
    fun a ha => r₁₂.frame_arr a ha
  have hoffρ : ρ.arrs "off" = arrOf (n + 1) O := by
    rw [f₁₂ _ (by rw [warrs_orderZeroCom]; decide),
      f₁₁ _ (by simp [ordName, String.ext_iff]), f₁₀ _ (by decide), f₉ _ (by decide),
      f₈ _ (by decide)]
    exact hoff₇
  have htgtρ : ρ.arrs "tgt" = arrOf ns T := by
    rw [f₁₂ _ (by rw [warrs_orderZeroCom]; decide),
      f₁₁ _ (by simp [ordName, String.ext_iff]), f₁₀ _ (by decide), f₉ _ (by decide),
      f₈ _ (by decide)]
    exact htgt₇
  -- the phase, assembled
  have hrT : Run B (orderCom 0 W j) σ ρ _ :=
    r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq (r₇.seq (r₈.seq (r₉.seq
      (r₁₀.seq (r₁₁.seq r₁₂))))))))))
  refine ⟨ρ, _, hrT, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, hMB, hGmB, hCbit, levelMem_run hrT hmem,
      hdep.run hrT, ?_, hnsW, hosz.run hrT, z₁, z₂, z₃, z₄, z₅, z₆, z₇, z₈,
      run_mem_arrs_lt hrT "itg" hwitg, run_mem_arrs_lt hrT "ntg" hwntg⟩,
    hrT.out_eq (noWrite_orderCom₀ W j),
    fun a => hrT.frame_var _ (ctrName_notMem_orderCom₀ W j a),
    fun a => hrT.frame_arr _ (gamName_notMem_orderCom₀ W j a),
    π, ordv, ?_, hordby⟩
  · rw [orderPhaseCost, RamElim.elimCost]
    simp only [size_add, size_var, size_lit]
    omega
  · exact hvn₁₂
  · exact hoffρ
  · exact htgtρ
  · rw [hrT.frame_arr _ (alvName_notMem_orderCom₀ W j)]; exact halvj
  · rw [hrT.frame_arr _ (gamName_notMem_orderCom₀ W j j)]; exact hgamj
  · intro c hc
    rw [hrT.frame_arr _ (colName_notMem_orderCom₀ W j c)]; exact hcolj c hc
  · rw [hrT.frame_var "m" (m_notMem_orderCom₀ W j)]; exact hmv
  · rw [f₁₂ _ (ordName_notMem_orderZeroCom j)]; exact hord₁₁


end Lax3Proofs.RamDriverCompose
