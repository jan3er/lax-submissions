import Lax3Proofs.RamDriverOrder
import Lax3Proofs.RamDriverBot

/-!
Two of the **composition obligations of the driver**, discharged:
`Lax3Proofs.RamDriver.CoverImplements` and
`Lax3Proofs.RamDriver.BaseImplements`.

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

Three pieces of reusable machinery come with them.

* `levelPre_run` and `orderMem_run` — **a level's state is a frame**.
  Thirteen clauses, of which two are scalars, five are named arrays and
  eight are the zeroing half of `RamDriver.OrderMem`; everything else
  survives any run. Every phase of a level carries `LevelPre` across by
  this one lemma and a list of `∉ warrs`.
* `fillPrefix_spec` and `copyPrefix_spec` — **a flat pass over a prefix
  of a longer array**. Everything built on
  `Lax13Proofs.Reasoning.Lib.Fill.Below` pins the destination's length
  to the pass's bound, and `RamDriver.coverSave`'s member copy does not
  have that shape.
* `coverOut_off_le` and `coverOut_congr` — **the cover's answer reads
  the member array only below the write pointer**, which is what makes
  that partial copy as good as the whole array.

# The ordering phase is not here

`RamDriver.OrderImplements` is **refutable as stated**, and the defect
is at the very first command of `RamDriver.orderCom`.

`RamDriver.LevelPre` says `σ.arrs "off" = arrOf (n + 1) O` and
`σ.arrs "tgt" = arrOf ns T` and nothing else about the block structure:
not that it *is* one, and not that its cells are words. `saveCsr`'s
first act is `.get "off" (.var "i")`, and a cell at or above the word
bound has no bounded evaluation, so at `n = 1`, `ns = 0`,
`cap = mb = 0`, `W = 0`, `B = 4` and `O = fun _ => 4` — a state
satisfying `WordBound B n ns cap mb`, `n + W + 1 < B` and every clause
of `LevelPre` — the phase has no `Run` at all and the `Spec` is false.
The same absence blocks the two `RamElim.elimCom` calls, whose
`RamElim.Implements` takes `RamElim.CsrSimple G ns O T`: the obligation
does not carry a graph, so no instance of the engine's availability
applies to them.

The repair is the one `CoverImplements` already had: a graph parameter
`G` and the hypothesis `RamBfs.CsrGraph G ns O T`, whose `le_ns` and
`target_lt'` give both the block structure the engine reads and the word
bounds the copies need.

Two further gaps sit behind that one, and both are the `tgt` coupling
`OrderImplements`'s own docstring records rather than anything new.

* `RamAugment.AugPre n nf W DO DT` asks for `tgt` at length `nf` and
  `RamAugment.Implements` asks for `fratSlots D = nf`. At the driver
  `tgt` is the level's own array, of length `ns`, so a round composes
  only when `fratSlots D = ns` — which is false in general and *worse*
  than false when `fratSlots D > ns`: `RamAugment.fratPass` stores into
  `tgt` at the fraternity graph's own slot count, so the round is stuck
  and the obligation is refuted. `G = K₁,₄` is such a case —
  `n = 5`, `ns = 8`, the elimination orientation points all four leaves
  at the centre, and its six fraternal pairs give `fratSlots = 12`.
* `RamAugment.Implements` also asks for `RamAugment.augWidth n d ≤ W`,
  and the obligation carries no hypothesis relating `W` to the
  in-degrees the chain reaches.

So the ordering phase is discharged at `R = 0` or not at all until that
wave runs; at `R = 0` the postcondition is still the whole of what the
driver's *correctness* asks — `OrderImplements` promises only that `ord`
orders some permutation — and only the cover's degree, hence the cost,
is lost.

# Two more defects, found at `R = 0` (wave D3)

Even at `R = 0` the phase is **not** dischargeable, and the first of the
two reasons is a defect in the *program* rather than in a surface.

**1. The second elimination is entered with dirty scratch — the
obligation is refuted, not merely unproved.** `RamDriver.orderCom` calls
`RamElim.elimCom` twice and re-zeroes nothing between them:
`RamDriver.orderZeroCom` is its *last* pass, and `RamDriver.augRelinkCom`
— which does run between rounds — zeroes `ooff`, `off`, `noff` and the
four stamps but neither `elm` nor `bh`. `RamElim.ElimPre` asks for both
zeroed, and the first call leaves neither: `RamElim.elimVertex` stores
`elm[w] := 1` at every extraction and nothing resets it, and `bh` ends
holding the run's own bucket heads.

The consequence is not just a missing hypothesis. In the second call
`RamElim.elimLoop` starts at `mind = 0`, `cnt = 0`, and every turn that
pops a slot finds `elm[w] = 1` and drops it, so `cnt` never moves; the
loop's test `cnt < n` therefore never fails, `mind` climbs turn after
turn, and at `mind = n + 1` the read `.get "bh" (.var "mind")` is out of
range — which in IMP+ has no derivation at all. So for every `n ≥ 1`
there is **no run** of `orderCom R W j`, and the `Spec` — being total
correctness — is false. Any state satisfying `LevelPre` at `n = 1` is a
counterexample.

The repair is one line of program text: `RamDriver.orderZeroCom` (or at
least its `elm` and `bh` fills) between `fillCom "alv" (.lit 1)` and the
second `RamElim.elimCom`. It is exactly the argument `orderZeroCom`'s own
docstring already makes about the level's exit, applied one pass earlier;
it changes no arena, no ordering and no postcondition, only the cost.

**2. The engine wants `CsrSimple`, and the obligation carries
`CsrGraph`.** `RamElim.Implements` takes `RamElim.CsrSimple G ns O T` —
`RamBfs.CsrGraph` together with *no row names a vertex twice*, which is
what `RamElim.card_liveSlots` needs to read a degree off a row. Wave D1
repaired `OrderImplements` to carry `CsrGraph`, which is what the
`saveCsr` copies and the cover pass need but is strictly weaker than what
the two `elimCom` calls need, and nothing in the driver bridges the two:
a block structure listing a neighbour twice is a `CsrGraph` and not a
`CsrSimple`, and it counts that neighbour twice into `deg`.

So `OrderImplements`'s hypothesis has to become `CsrSimple G ns O T`, and
the clause has to be threaded through `RamDriverCluster.levelImplements`
(whose `hcsr` is handed to `horder`) and produced at the root — either
from `Lax11.GraphEncoding.EncodesGraph` if that surface forbids repeated
targets, or as one more clause of the input encoding's data.
-/

namespace Lax3Proofs.RamDriverCompose

open Lax3.ColoredGraphs Lax3.DistFO
open Lax3Proofs.SyntaxLemmas Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked CsrGraph)
open Lax3Proofs.RamCover (CoverOut CoverPre CoverPost OrdersBy)
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

theorem warrs_coverPhase (cap j : ℕ) : (coverPhase cap j).warrs =
    ["ord", "alv", "asg", "xoff", "dist", "dist", "q", "dist", "q", "xmem", "asg", "alv",
      "xoff", xofName j, xmmName j, asgName j] := rfl

theorem wvars_coverPhase (cap j : ℕ) : (coverPhase cap j).wvars =
    ["i", "i", "i", "i", "i", "i", "xp", "c", "src", "i", "i", "tail", "tail", "head", "sc",
      "v", "dv", "dn", "j", "jend", "w", "tail", "sc", "j", "head", "z", "dz", "xp", "z", "c",
      "i", "i", "i", "i", "i", "i", xpName j] := rfl

/-! ### The frame of a level's state

`RamDriver.LevelPre` is thirteen clauses, of which two are scalars, five
are named arrays, and the last four survive any run outright. So a pass
that writes none of the seven names carries the whole clause across, and
that is what every phase of a level does with it. -/

/-- The eight arrays `RamDriver.OrderMem`'s zeroing half speaks about. -/
def zeroArrs : List String := ["elm", "bh", "ooff", "noff", "stf", "sta", "std", "ste"]

/-- **The engines' scratch survives a pass that does not write it.** -/
theorem orderMem_run {B n ns W : ℕ} {c : Com} {σ σ' : Env} {K : ℕ}
    (h : OrderMem n ns W σ) (hr : Run B c σ σ' K) (hz : ∀ a ∈ zeroArrs, a ∉ c.warrs) :
    OrderMem n ns W σ' := by
  obtain ⟨hle, hsz, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨hle, hsz.run hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  simp [alvName, xofName, xmmName, asgName, String.ext_iff]

theorem gamName_notMem_coverPhase (cap j a : ℕ) : gamName a ∉ (coverPhase cap j).warrs := by
  rw [warrs_coverPhase]
  simp [gamName, xofName, xmmName, asgName, String.ext_iff]

theorem colName_notMem_coverPhase (cap j a c : ℕ) : colName a c ∉ (coverPhase cap j).warrs := by
  rw [warrs_coverPhase]
  simp [colName, xofName, xmmName, asgName, String.ext_iff]

theorem off_notMem_coverPhase (cap j : ℕ) : "off" ∉ (coverPhase cap j).warrs := by
  rw [warrs_coverPhase]
  simp [xofName, xmmName, asgName, String.ext_iff]

theorem tgt_notMem_coverPhase (cap j : ℕ) : "tgt" ∉ (coverPhase cap j).warrs := by
  rw [warrs_coverPhase]
  simp [xofName, xmmName, asgName, String.ext_iff]

theorem zero_notMem_coverPhase (cap j : ℕ) :
    ∀ a ∈ zeroArrs, a ∉ (coverPhase cap j).warrs := by
  rw [warrs_coverPhase]
  intro a ha
  simp only [zeroArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [xofName, xmmName, asgName, String.ext_iff]

theorem ctrName_notMem_coverPhase (cap j a : ℕ) : ctrName a ∉ (coverPhase cap j).wvars := by
  rw [wvars_coverPhase]
  simp [ctrName, xpName, String.ext_iff]

theorem n_notMem_coverPhase (cap j : ℕ) : "n" ∉ (coverPhase cap j).wvars := by
  rw [wvars_coverPhase]
  simp [xpName, String.ext_iff]

theorem m_notMem_coverPhase (cap j : ℕ) : "m" ∉ (coverPhase cap j).wvars := by
  rw [wvars_coverPhase]
  simp [xpName, String.ext_iff]

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
    fun c hc w => ?_, h.asg_lt, h.asg_cover⟩
  rw [← h.block c hc w]
  constructor
  · rintro ⟨p, hp1, hp2, hp3⟩
    exact ⟨p, hp1, hp2, by rw [← hX p (hblk c hc p hp2)]; exact hp3⟩
  · rintro ⟨p, hp1, hp2, hp3⟩
    exact ⟨p, hp1, hp2, by rw [hX p (hblk c hc p hp2)]; exact hp3⟩

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
    ["i", "i", "xp", "c", "src", "i", "i", "tail", "tail", "head", "sc", "v", "dv", "dn",
      "j", "jend", "w", "tail", "sc", "j", "head", "z", "dz", "xp", "z", "c"] := rfl

theorem warrs_coverCom (r : ℕ) : (RamCover.coverCom r).warrs =
    ["asg", "xoff", "dist", "dist", "q", "dist", "q", "xmem", "asg", "alv", "xoff"] := rfl

theorem ordName_notMem_coverPhase (cap j a : ℕ) : ordName a ∉ (coverPhase cap j).warrs := by
  rw [warrs_coverPhase]
  simp [ordName, xofName, xmmName, asgName, String.ext_iff]

theorem noWrite_coverPhase (cap j : ℕ) : (coverPhase cap j).NoWrite := by
  simp [coverPhase, coverSave, copyCom, copyUpto, fillUpto, RamCover.coverCom,
    RamCover.initAsg, RamCover.centreStep, RamCover.emitLoop, RamCover.emitSlot,
    RamBfs.bfsCom, RamBfs.initDist, RamBfs.seedSrc, RamBfs.bfsDrain, RamBfs.expandRow,
    RamBfs.scanSlot, Com.NoWrite]

/-- The cost of the cover phase: the pass, the two copies that set it
up, and the four of `RamDriver.coverSave`, the member copy charged at
the whole cluster arena. -/
def coverPhaseCost (n ns : ℕ) : ℕ := RamCover.coverCost n ns + 12 * (n * n) + 50 * n + 48

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
        hmem₂.1.get (p := ("xmem", n * n)) (by simp)⟩, hmem₂.2.1⟩
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
  -- the phase, assembled
  refine ⟨σ₆.setVar (xpName j) m, _,
    hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq (hr₆.seq hr₇))))), ?_, ?_⟩
  · rw [coverPhaseCost]
    simp only [size_add, size_var, size_lit]
    have h12 : 12 * m ≤ 12 * (n * n) := Nat.mul_le_mul_left 12 hmle
    omega
  set ρ := σ₆.setVar (xpName j) m with hρ
  have hrT : Run B (coverPhase cap j) σ ρ _ :=
    hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq (hr₆.seq hr₇)))))
  refine ⟨levelPre_run hlev hrT (n_notMem_coverPhase cap j) (m_notMem_coverPhase cap j)
      (off_notMem_coverPhase cap j) (tgt_notMem_coverPhase cap j)
      (alvName_notMem_coverPhase cap j j) (gamName_notMem_coverPhase cap j j)
      (fun q => colName_notMem_coverPhase cap j j q) (zero_notMem_coverPhase cap j),
    hrT.out_eq (noWrite_coverPhase cap j),
    fun a => hrT.frame_var _ (ctrName_notMem_coverPhase cap j a),
    fun a => hrT.frame_arr _ (gamName_notMem_coverPhase cap j a),
    Xoff, v₅, asg, m, ?_, ?_, ?_, ?_, ?_, hmle, hordlt, coverOut_congr hout hagr₅⟩
  · rw [hrT.frame_arr _ (ordName_notMem_coverPhase cap j j)]; exact hordarr
  · rw [hρ, arrs_setVar,
      hr₆.frame_arr _ (by rw [warrs_copyCom]; simp [xofName, asgName, String.ext_iff]),
      hr₅.frame_arr _ (by rw [warrs_copyUpto]; simp [xofName, xmmName, String.ext_iff]), hv₄,
      RamDriverOrder.arrOf_congr hagr₄]
  · rw [hρ, arrs_setVar,
      hr₆.frame_arr _ (by rw [warrs_copyCom]; simp [xmmName, asgName, String.ext_iff]), hv₅]
  · rw [hρ, arrs_setVar, hv₆, RamDriverOrder.arrOf_congr hagr₆]
  · rw [hρ, vars_setVar, if_pos rfl]

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

end Lax3Proofs.RamDriverCompose
