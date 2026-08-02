import Lax3Proofs.Refine.AugmentTwins
import Lax13Proofs.Refine.Examples.BfsQSynth
import Lax13Proofs.Refine.Sepref.Examples.WordAssnSpike

/-!
# ND-MC rebase P2 / satellite 2C — the augmentation round, re-derived
through the refinement tower

`Lax3Proofs.RamAugment` is one round of transitive–fraternal
augmentation: ten passes over three block structures and one call to the
elimination engine. Its phases are

1. `outPass` — the out-lists of `D`, a counting sort of the in-lists
   (`outCount`, `outPrefix`, `outFill`);
2. `fratPass` — the fraternity graph, materialized and deduplicated by a
   stamp array (`fratCount`, `fratPrefix`, `fratFill`);
3. `alvSet` — the all-alive mask the engine is handed;
4. `elimCom` — `RamElim`'s engine, called on the fraternity graph;
5. `asmPass` — the assembly, three enumerations under `NewArc`
   (`asmCount`, `asmPrefix`, `asmFill`).

This file re-derives the passes of **phase 1** and **phase 3** through
the tower, and says exactly how far each one got:

| pass | abstract + correctness | `sepref_synth` | `BRefine` | `Spec` export |
|---|---|---|---|---|
| `alvSet` (phase 3) | §2, inherited | §2 | §2.1 | §6.1, incl. `arrOf` bridge |
| `outPrefix` = `fratPrefix` = `asmPrefix` | §3 | §3.3 | §4b | — (§9) |
| `outCount` (both loops) | §4 | §4.5 | — (§9) | — (§9) |
| `outFill` | twin only (`AugmentTwins`) | — | — | — |

**Update (wave 2C′).** The out-fill row above is superseded:
`Refine/AugmentSynth2.lean` derives it — abstract program, correctness
against the twin, cost `26·n + 26·m + 4`, synthesized `Com`, gate — so
**phase 1 is complete through the tower**, and that file's §2.1 runs the
three synthesized programs one after another against `outPassTw`. Its §5
records what a future `R > 0` wave would still need; the `BRefine` debt
of §10 gap 3 below is unchanged and now covers two passes.

The prefix pass is one program at three of the round's ten uses
(`RamDriverAugment.prefixCom`), so the three derived passes cover **five
of the ten**. Phases 2, 4 and 5 are not synthesized: §8 prices them and
§7 measures the composition boundary they run into. What is *not* left
to a later reading is the arithmetic: `Refine/AugmentTwins.lean`
(split out of this file for length) differential-tests computable twins
of **all** the block-structure passes — including the ones that are not
synthesized — against `RamAugment.Demo`'s own reported numbers and
against `Lax3Proofs.TgtCoupling`'s K₁,₄ witness, and §5 below runs the
*synthesized* programs against those twins.

## The two findings

**F1 — a two-loop pass over a block structure synthesizes** (§4.5).
Satellite 2B (`Refine/ElimSynth.lean`, P2/2B/D-a) reports that its
two-loop `degPass` does *not* translate, at 1 000 000 and at 4 000 000
heartbeats. `cntPass` here has the same shape in every respect 2B names
— outer loop over vertices, inner loop **in the middle** of the body,
the inner loop's result feeding the operations after it — and it
translates in seconds. The variable the two runs isolate is therefore
2B's remaining difference: the two-armed `irIf` whose *both* arms
`mopAset` the enclosing loop's own state array.

**F2 — two passes over the same array do not compose in the tool**
(§7). `bindT (cntPass …) fun r => prefLoop n (r.1, ofl₀, 0)` stalls with
`hnr_while`: "the rule's precondition conjuncts could not all be matched
against the goal's". This is 2A's T1 at its cheapest instance — no
engine, no leaf rule, two ordinary loops over `"ooff"` — and it is why
the passes here are exported one by one and glued at the `Spec` level
(the P1-style shape the brief allows).

## What is consumed rather than re-proved

* `Lax3Proofs.TgtCoupling` (landed this session) is the abstract slot
  mathematics: `csrSlots`, `csrSlots_fratGraph_le` (a round's fraternity
  graph is `n · d²` slots), `chainWidth_dominates` (one width for the
  chain) and `not_csrSlots_fratGraph_le_csrSlots` (the level's `ns` is
  *not* a bound — K₁,₄). None of it is re-proved here; `AugmentTwins`
  §1.5 *runs* the
  fraternity twin on the K₁,₄ witness and identifies its answer with
  `TgtCoupling.csrSlots (fratGraph starOr)`, so the refutation bites on
  this file's program and not only on the Finset shadow.
* `RamAugment.outSet`, `sum_card_outSet`, `fratNbrs_eq`, `augOr`,
  `inN_augOr_eq` and the in-degree budget are the baseline's own
  mathematics, cited. The tower re-derives the *programs*.
* `BfsQ.fillLoop`/`fillLoop_le` is landed capital: the mask pass **is**
  the fill loop at `sent = 1` (§2), so its abstract bound is inherited by
  one rewrite rather than re-proved.

## Where the round's one non-obvious cost fact now lives (R2C/D-a)

`RamDriverAugment.slotCnt_out_eq` — "an out-slot names `w` exactly as
often as `w` has in-neighbours" — is the exchange that makes the
assembly's stamping pass linear. In this derivation its content is
**`slotCnt`, an abstract-level list function**, and it is the
*postcondition of the counting pass* rather than a lemma about a walk:
`cntPass_spec` (§4.4) says the pass leaves `ooff[k] = bumpCnt DT 0 m k`
— the number of slots naming `k-1`, i.e. the out-degree — and
`sum_bumpCnt` (§4.2) says those numbers add up to `m` over the carrier
(`Finset.card_eq_sum_card_fiberwise`, one line). The Finset-level
counterpart is `RamAugment.sum_card_outSet`, which is *cited* for the
budget and is one rewrite away. So the exchange is no longer a walk
lemma at all: it is what a pass computes.

## Judgment calls

**R2C/D-b — the prefix pass computes `i+1` twice.** The baseline writes
`off[i+1] := off[i+1] + off[i]` as one IMP+ expression over one index
expression `i+1`; the IR is three-address, so `i+1` is a cell, and the
counter's own bump at the end of the body is a *second* `add`. That is a
cost-only change (one `add` per vertex) and is why `prefK` carries a
`14` where the baseline's `prefixCom` walk carries a `13`.

**R2C/D-c — every scratch cell is `"ag"`-prefixed and digit-free**
(P1/B-f). The array names are the baseline's verbatim (`doff`, `dtg`,
`ooff`, `otg`, `ofl`, `alv`), since those are the integration surface;
only the scratch *cells* are renamed, and they carry no digits, so the
integration wave's relisting is mechanical (§9).

**R2C/D-d — the mask pass reuses the BFS fill loop.** `alvSet` is
`Fill.loop_spec` with the constant one in the baseline and
`BfsQ.fillLoop n 1` here. Rather than author a second copy of the
flattest loop in the campaign, this file *instantiates* the P1 wave's
own, at its own array and cell names. The synthesis is re-run (the cell
names differ); the abstract bound is not.
-/

namespace Lax3Proofs.Refine.AugmentSynth

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Sepref.WordSpike
open Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest Lax13Proofs.Refine.Codegen
open Lax13Proofs.Refine.BfsQ (cu iter irWhile_exit get!_set liftACost_cu)
open Lax3Proofs.Refine.AugmentTwins

/-! ## 2. The mask pass (`RamAugment.alvSet`)

The one pass of the round with no data in it: the whole fraternity graph
is in play, so every vertex is alive. It is `BfsQ.fillLoop n 1` on the
nose — the P1 wave's fill loop at the constant one — so the abstract
program and its bound are *instantiated*, not re-authored (R2C/D-d), and
only the synthesis is re-run, at this round's array and cell names. -/

section Mask

open Lax13Proofs.Refine.BfsQ (fillLoop fillC fillLoop_le)

/-- **The mask pass's abstract bound**, inherited from the fill loop. -/
theorem alvLoop_le (n : ℕ) (A : List ℕ) (hlen : A.length = n) :
    BfsQSynth.fillLoop' n 1 (A, 0)
      ≤ NRest.spec (fun p : List ℕ × ℕ => p.1.length = n ∧ ∀ j, j < n → p.1[j]! = 1)
          (fun _ => liftACost (n • iter fillC + cu Currency.«while»)) := by
  rw [BfsQSynth.fillLoop'_eq]
  have h := fillLoop_le n 1 n A 0 hlen (by omega) (fun j hj => absurd hj (Nat.not_lt_zero j))
  simpa using h

set_option maxHeartbeats 1000000 in
sepref_synth alvSynth (n : ℕ) (alv₀ : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (alv₀, 0) ("alv", "agi") ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one")
    _ _ ("alv", "agi") (arrayAssn ×ₐ natAssn)
    (BfsQSynth.fillLoop' n 1 (alv₀, 0))

-- The synthesized mask pass, pinned.
#guard alvSynth_impl =
  Com.while (Cond.lt (Operand.cell "agi") (Operand.cell "n"))
    ((Com.aset "alv" "agi" "one").seq
      ((Com.binop Lax13Proofs.Imp.Bop.add "agi" "agi" "one").seq Com.skip))

/-! ### 2.1 The bounds pass -/

/-- The loop assertion: the array and the counter it mutates, the three
constants it reads. -/
def alvΓ (n : ℕ) : List ℕ × ℕ → Assn := fun t =>
  arrayAssn t.1 "alv" ∗ natAssn t.2 "agi" ∗ natAssn n "n" ∗ natAssn 1 "one"

/-- The abstract invariant. One conjunct. -/
def alvI (n : ℕ) : List ℕ × ℕ → Prop := fun t => t.2 ≤ n

theorem alv_guard (n : ℕ) (t : List ℕ × ℕ) (F : Assn) (s : Ir.State) (cr : ECost)
    (r : Bool) (_ : alvI n t) (hs : irSTATE (alvΓ n t ∗ F) (s, cr))
    (hev : (Cond.lt (Operand.cell "agi") (Operand.cell "n")).eval s = some r) :
    decide (t.2 < n) = r := by
  obtain ⟨a, b, ha, hb, rfl⟩ := BfsQSynth.eval_lt_cells hev
  have hi : s.vars "agi" = some t.2 :=
    natAssn_vars (F := arrayAssn t.1 "alv" ∗ natAssn n "n" ∗ natAssn 1 "one" ∗ F)
      (irSTATE_cong (by rw [alvΓ]; ac_rfl) hs)
  have hn : s.vars "n" = some n :=
    natAssn_vars (F := arrayAssn t.1 "alv" ∗ natAssn t.2 "agi" ∗ natAssn 1 "one" ∗ F)
      (irSTATE_cong (by rw [alvΓ]; ac_rfl) hs)
  rw [hi] at ha
  rw [hn] at hb
  rw [Option.some.inj ha, Option.some.inj hb]

/-- The mask pass's loop body, named. -/
def alvBody : Com :=
  (Com.aset "alv" "agi" "one").seq
    ((Com.binop Lax13Proofs.Imp.Bop.add "agi" "agi" "one").seq Com.skip)

theorem alvSynth_impl_eq :
    alvSynth_impl = Com.while (Cond.lt (Operand.cell "agi") (Operand.cell "n")) alvBody := rfl

theorem alv_body_brefine {B n : ℕ} (hnB : n < B) (t : List ℕ × ℕ) (_hI : alvI n t)
    (hbf : decide (t.2 < n) = true) :
    BRefine B (alvΓ n t) alvBody (LoopAssn (alvI n) (alvΓ n)) := by
  have hlt : t.2 < n := of_decide_eq_true hbf
  rw [alvBody]
  refine BRefine.seq (Γ₁ := ⌜t.2 < t.1.length⌝ ∗ alvΓ n (t.1.set t.2 1, t.2)) ?_ ?_
  · exact BRefine.perm
      (P := (arrayAssn t.1 "alv" ∗ natAssn t.2 "agi" ∗ natAssn 1 "one") ∗ natAssn n "n")
      (P' := (⌜t.2 < t.1.length⌝ ∗ arrayAssn (t.1.set t.2 1) "alv" ∗ natAssn t.2 "agi" ∗
        natAssn 1 "one") ∗ natAssn n "n")
      (by simp only [alvΓ]; ac_rfl) (by simp only [alvΓ]; ac_rfl)
      (BRefine.frame BRefine.aset)
  · refine BRefine.pre_pure fun _ => ?_
    refine BRefine.seq
      (Γ₁ := alvΓ n (t.1.set t.2 1, Lax13Proofs.Imp.Bop.apply .add t.2 1)) ?_ ?_
    · exact BRefine.perm
        (P := (natAssn t.2 "agi" ∗ natAssn 1 "one") ∗
          (arrayAssn (t.1.set t.2 1) "alv" ∗ natAssn n "n"))
        (P' := (natAssn (Lax13Proofs.Imp.Bop.apply .add t.2 1) "agi" ∗ natAssn 1 "one") ∗
          (arrayAssn (t.1.set t.2 1) "alv" ∗ natAssn n "n"))
        (by simp only [alvΓ]; ac_rfl) (by simp only [alvΓ]; ac_rfl)
        (BRefine.frame (BRefine.binop_self
          (by rw [Lax13Proofs.Imp.Bop.apply_add]; omega)))
    · exact BRefine.skip.cons (entails_refl _)
        (loopAssn_intro (I := alvI n) (Γ := alvΓ n)
          (t := (t.1.set t.2 1, Lax13Proofs.Imp.Bop.apply .add t.2 1))
          (by simp only [alvI, Lax13Proofs.Imp.Bop.apply_add]; omega))

/-- **The mask pass's bounds pass.** -/
theorem alv_brefine {B n : ℕ} (hnB : n < B) :
    BRefine B (LoopAssn (alvI n) (alvΓ n)) alvSynth_impl (LoopAssn (alvI n) (alvΓ n)) := by
  rw [alvSynth_impl_eq]
  exact BRefine.while_guard (bf := fun t => decide (t.2 < n))
    BfsQSynth.litLt_lt_cells (alv_guard n)
    (fun t hI hbf => alv_body_brefine hnB t hI hbf)
    (fun t hI _ => loopAssn_intro hI)

end Mask

/-! ## 3. The prefix pass (`RamAugment.outPrefix` = `fratPrefix` =
`asmPrefix`)

`RamDriverAugment.prefixCom` is one program used at three array pairs:
the running sum that turns a degree array into a block structure, and
the fill pointer opened at each block's start. It is derived here once,
at the out-list pair (`"ooff"`, `"ofl"`); the other two uses are the
same abstract program at other array names, and re-synthesizing them is
mechanical (§10, tool gap 5: there is no name-generic synthesis).

The loop state is a *triple* — two arrays and the counter — which is the
shape `BfsQ.pack4` exists for. -/

section Prefix

/-- The prefix pass's loop state: the offsets, the fill pointers, the
vertex counter. -/
abbrev PSt : Type := List ℕ × List ℕ × ℕ

/-- Assemble the state, at the IR's tuple operation. -/
noncomputable def packOF (O F : List ℕ) (i : ℕ) : NRest PSt ECost :=
  bindT (mopPair F i) fun p => mopPair O p

/-- One vertex's turn: `off[i+1] := off[i+1] + off[i]`, then
`fl[i] := off[i]`, then the counter. Seven operations, since `i+1` is a
cell and the counter's bump is a second `add` (R2C/D-b). -/
noncomputable def prefF : PSt → NRest PSt ECost := fun s =>
  bindT (mopBinop .add s.2.2 1) fun ip =>
    bindT (mopAget s.1 ip) fun b =>
      bindT (mopAget s.1 s.2.2) fun a =>
        bindT (mopBinop .add b a) fun t =>
          bindT (mopAset s.1 ip t) fun O =>
            bindT (mopAset s.2.1 s.2.2 a) fun F =>
              bindT (BfsQSynth.mopSucc s.2.2) fun i' => packOF O F i'

def prefBf (n : ℕ) : PSt → Bool := fun s => decide (s.2.2 < n)

/-- What one turn needs: both stores in range. -/
def prefP (n : ℕ) : PSt → Prop := fun s =>
  s.1.length = n + 1 ∧ s.2.1.length = n ∧ s.2.2 < n

/-- **The prefix pass.** -/
noncomputable def prefLoop (n : ℕ) (s₀ : PSt) : NRest PSt ECost :=
  irWhileIT (fun s => prefBf n s = true → prefP n s) (prefBf n) prefF s₀

/-- The step, as a function — the twin of §1 at one vertex. -/
def prefStep : PSt → PSt := fun s =>
  (s.1.set (s.2.2 + 1) (s.1[s.2.2 + 1]! + s.1[s.2.2]!), s.2.1.set s.2.2 s.1[s.2.2]!,
    s.2.2 + 1)

/-- One turn, priced: three adds, two reads, two stores, two tuple
steps. -/
def prefC : ACost String ℕ :=
  cu (binopCurrency .add) + cu Currency.aget + cu Currency.aget + cu (binopCurrency .add)
    + cu Currency.aset + cu Currency.aset + cu (binopCurrency .add) + cu Currency.skip
    + cu Currency.skip

theorem prefF_le (s : PSt) (h1 : s.2.2 + 1 < s.1.length) (h2 : s.2.2 < s.2.1.length) :
    prefF s ≤ NRest.consume (NRest.returnT (prefStep s)) (liftACost prefC) := by
  have h0 : s.2.2 < s.1.length := by omega
  refine le_of_eq ?_
  simp only [prefF, packOF, BfsQSynth.mopSucc_eq, mopAget_def, mopAset_def, mopBinop_def,
    mopPair_def, NRest.assert_pos h0, NRest.assert_pos h1, NRest.assert_pos h2,
    NRest.returnT_bindT, bindT_unitT, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, prefC, liftACost_add, liftACost_cu,
    prefStep]
  congr 1
  ac_rfl

/-! ### 3.1 What the pass computes

The running sum. `cumsum O₀ k` is the value the pass leaves at `k`, and
when `O₀` is the degree array one place up it is the block structure's
offset — `∑_{j<k} deg j`. -/

/-- The running sum of an array, at one index. -/
def cumsum (O₀ : List ℕ) (k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), O₀[j]!

theorem cumsum_succ (O₀ : List ℕ) (k : ℕ) : cumsum O₀ (k + 1) = cumsum O₀ k + O₀[k + 1]! := by
  rw [cumsum, cumsum, Finset.sum_range_succ]

theorem cumsum_zero (O₀ : List ℕ) : cumsum O₀ 0 = O₀[0]! := by
  rw [cumsum, Finset.sum_range_one]

/-- The pass's invariant: the prefix is summed, the suffix is untouched,
and the fill pointers already written are the offsets. -/
def prefInv (n : ℕ) (O₀ : List ℕ) : PSt → Prop := fun s =>
  s.1.length = n + 1 ∧ s.2.1.length = n ∧ s.2.2 ≤ n ∧
    (∀ k, k ≤ s.2.2 → s.1[k]! = cumsum O₀ k) ∧
    (∀ k, s.2.2 < k → k ≤ n → s.1[k]! = O₀[k]!) ∧
    (∀ k, k < s.2.2 → s.2.1[k]! = cumsum O₀ k)

theorem prefInv_step {n : ℕ} {O₀ : List ℕ} {s : PSt} (hI : prefInv n O₀ s)
    (hlt : s.2.2 < n) : prefInv n O₀ (prefStep s) := by
  obtain ⟨hO, hF, hi, hpre, hsuf, hfl⟩ := hI
  have hi1 : s.2.2 + 1 < s.1.length := by omega
  have hi0 : s.2.2 < s.1.length := by omega
  have hiF : s.2.2 < s.2.1.length := by omega
  have hb : s.1[s.2.2 + 1]! = O₀[s.2.2 + 1]! := hsuf _ (by omega) (by omega)
  have ha : s.1[s.2.2]! = cumsum O₀ s.2.2 := hpre _ le_rfl
  refine ⟨by simp [prefStep, hO], by simp [prefStep, hF], by simp only [prefStep]; omega,
    ?_, ?_, ?_⟩
  · intro k hk
    show (s.1.set (s.2.2 + 1) _)[k]! = _
    rw [get!_set _ _ _ _ hi1]
    by_cases hke : k = s.2.2 + 1
    · rw [if_pos hke, hke, hb, ha, cumsum_succ, Nat.add_comm]
    · rw [if_neg hke]
      exact hpre k (by simp only [prefStep] at hk; omega)
  · intro k hk1 hk2
    show (s.1.set (s.2.2 + 1) _)[k]! = _
    simp only [prefStep] at hk1
    rw [get!_set _ _ _ _ hi1, if_neg (by omega)]
    exact hsuf k (by omega) hk2
  · intro k hk
    show (s.2.1.set s.2.2 _)[k]! = _
    simp only [prefStep] at hk
    rw [get!_set _ _ _ _ hiF]
    by_cases hke : k = s.2.2
    · rw [if_pos hke, hke, ha]
    · rw [if_neg hke]
      exact hfl k (by omega)

/-! ### 3.2 The loop, bounded -/

theorem prefLoop_le (n : ℕ) (O₀ : List ℕ) :
    ∀ (fuel : ℕ) (s : PSt), prefInv n O₀ s → n - s.2.2 ≤ fuel →
      prefLoop n s
        ≤ NRest.spec (fun t : PSt => prefInv n O₀ t ∧ n ≤ t.2.2)
            (fun _ => liftACost ((n - s.2.2) • iter prefC + cu Currency.«while»)) := by
  have exit : ∀ s : PSt, prefInv n O₀ s → n ≤ s.2.2 →
      prefLoop n s
        ≤ NRest.spec (fun t : PSt => prefInv n O₀ t ∧ n ≤ t.2.2)
            (fun _ => liftACost ((n - s.2.2) • iter prefC + cu Currency.«while»)) := by
    intro s hI hge
    have hb : prefBf n s = false := by simp only [prefBf, decide_eq_false_iff_not]; omega
    simp only [prefLoop, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨hI, hge⟩ ?_
    rw [show n - s.2.2 = 0 by omega]
    simp
  intro fuel
  induction fuel with
  | zero => intro s hI hf; exact exit s hI (by omega)
  | succ fuel ih =>
    intro s hI hf
    by_cases hb : s.2.2 < n
    · have hbt : prefBf n s = true := by simp [prefBf, hb]
      have hI' := hI
      obtain ⟨hOl, hFl, -, -, -, -⟩ := hI
      have hP : prefP n s := ⟨hOl, hFl, hb⟩
      have hIs : prefBf n s = true → prefP n s := fun _ => hP
      have h1 : s.2.2 + 1 < s.1.length := by omega
      have h2 : s.2.2 < s.2.1.length := by omega
      have hstep : (prefStep s).2.2 = s.2.2 + 1 := rfl
      have hih := ih (prefStep s) (prefInv_step hI' hb) (by rw [hstep]; omega)
      rw [hstep] at hih
      have hcost : irUnit Currency.«while»
          + (liftACost prefC + liftACost ((n - (s.2.2 + 1)) • iter prefC + cu Currency.«while»))
          = liftACost ((n - s.2.2) • iter prefC + cu Currency.«while») := by
        rw [show n - s.2.2 = (n - (s.2.2 + 1)) + 1 by omega, succ_nsmul]
        simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
        ac_rfl
      calc prefLoop n s
          = NRest.consume (NRest.bindT (prefF s) fun s' => prefLoop n s')
              (irUnit Currency.«while») := by
            simp only [prefLoop]; rw [irWhileIT_of_true hIs hbt]
        _ ≤ NRest.consume (NRest.bindT
              (NRest.consume (NRest.returnT (prefStep s)) (liftACost prefC))
              fun s' => prefLoop n s') (irUnit Currency.«while») :=
            NRest.consume_mono
              (NRest.bindT_mono (prefF_le s h1 h2) fun _ => le_rfl) le_rfl
        _ = NRest.consume (NRest.consume (prefLoop n (prefStep s)) (liftACost prefC))
              (irUnit Currency.«while») := by rw [bindT_unitT]
        _ ≤ _ := by
            rw [← hcost]
            exact NRest.consume_mono (NRest.consume_mono hih le_rfl) le_rfl |>.trans
              (le_of_eq (by rw [Sepref.consume_spec, Sepref.consume_spec]))
    · exact exit s hI (by omega)

/-- **The prefix pass, run from the start.** -/
theorem prefLoop_spec (n : ℕ) (O₀ F₀ : List ℕ) (hO : O₀.length = n + 1) (hF : F₀.length = n) :
    prefLoop n (O₀, F₀, 0)
      ≤ NRest.spec (fun t : PSt => t.1.length = n + 1 ∧ t.2.1.length = n ∧ t.2.2 = n ∧
            (∀ k, k ≤ n → t.1[k]! = cumsum O₀ k) ∧ ∀ k, k < n → t.2.1[k]! = cumsum O₀ k)
          (fun _ => liftACost (n • iter prefC + cu Currency.«while»)) := by
  have hstart : prefInv n O₀ (O₀, F₀, 0) := by
    refine ⟨hO, hF, Nat.zero_le n, ?_, ?_, ?_⟩
    · intro k hk
      obtain rfl : k = 0 := Nat.le_zero.1 hk
      rw [cumsum_zero]
    · intro k _ _; rfl
    · intro k hk; exact absurd hk (Nat.not_lt_zero k)
  refine le_trans (prefLoop_le n O₀ n (O₀, F₀, 0) hstart (by simp)) ?_
  refine spec_mono ?_ (fun _ _ => le_of_eq (by simp))
  rintro t ⟨⟨hO', hF', hle, hpre, -, hfl⟩, hge⟩
  exact ⟨hO', hF', by omega, fun k hk => hpre k (by omega), fun k hk => hfl k (by omega)⟩

/-! ### 3.3 The synthesis -/

set_option maxHeartbeats 1000000 in
sepref_synth prefSynth (n : ℕ) (ooff₀ ofl₀ : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ natAssn) (ooff₀, ofl₀, 0)
        ("ooff", "ofl", "agi") ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "agip" ∗ junkCell "agb" ∗ junkCell "aga" ∗ junkCell "agt")
    _ _ ("ooff", "ofl", "agi") (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
    (prefLoop n (ooff₀, ofl₀, 0))

end Prefix

/-! ## 4. The counting pass (`RamAugment.outCount`)

The first half of the counting sort, and the pass that *is* the round's
one non-obvious cost fact (R2C/D-a): every slot of every in-block names
a vertex `u`, and the pass bumps `ooff[u+1]`. What it leaves at `u+1` is
therefore the number of slots naming `u` — which is the out-degree of
`u`, since a slot of `i`'s in-block naming `u` is the arc `u → i`.

Two loops: the row scan over `[doff[i], doff[i+1])` and the pass over
the vertices. -/

section Count

/-- The loop state of both loops: the offset array being accumulated,
and an index. -/
abbrev CSt : Type := List ℕ × ℕ

/-! ### 4.1 The slot scan -/

def cntBf (jend : ℕ) : CSt → Bool := fun s => decide (s.2 < jend)

/-- What one slot needs: the slot is in the target array and the vertex
it names has a place in the offset array. -/
def cntSlotP (T : List ℕ) : CSt → Prop := fun s =>
  s.2 < T.length ∧ T[s.2]! + 1 < s.1.length

/-- One slot: read the target, bump the count one place up. -/
noncomputable def cntF (T : List ℕ) : CSt → NRest CSt ECost := fun s =>
  bindT (mopAget T s.2) fun u =>
    bindT (mopBinop .add u 1) fun up =>
      bindT (mopAget s.1 up) fun c =>
        bindT (BfsQSynth.mopSucc c) fun c' =>
          bindT (mopAset s.1 up c') fun O =>
            bindT (BfsQSynth.mopSucc s.2) fun j => mopPair O j

/-- The scan of one row. -/
noncomputable def cntScan (T : List ℕ) (jend : ℕ) (s₀ : CSt) : NRest CSt ECost :=
  irWhileIT (fun s => cntBf jend s = true → cntSlotP T s) (cntBf jend) (cntF T) s₀

/-- The step, as a function. -/
def cntSlot (T : List ℕ) : CSt → CSt := fun s =>
  (s.1.set (T[s.2]! + 1) (s.1[T[s.2]! + 1]! + 1), s.2 + 1)

/-- One slot, priced: two reads, two adds, the store, the index, the
tuple. -/
def cntC : ACost String ℕ :=
  cu Currency.aget + cu (binopCurrency .add) + cu Currency.aget + cu (binopCurrency .add)
    + cu Currency.aset + cu (binopCurrency .add) + cu Currency.skip

theorem cntF_le (T : List ℕ) (s : CSt) (h : cntSlotP T s) :
    cntF T s ≤ NRest.consume (NRest.returnT (cntSlot T s)) (liftACost cntC) := by
  obtain ⟨h1, h2⟩ := h
  refine le_of_eq ?_
  simp only [cntF, BfsQSynth.mopSucc_eq, mopAget_def, mopAset_def, mopBinop_def, mopPair_def,
    NRest.assert_pos h1, NRest.assert_pos h2, NRest.returnT_bindT, bindT_unitT,
    NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, cntC,
    liftACost_add, liftACost_cu, cntSlot]
  congr 1
  ac_rfl

/-! ### 4.2 What the scan counts — the exchange, abstractly (R2C/D-a)

`bumpCnt T a b k` is the number of slots in `[a, b)` that bump the cell
`k`: the slots naming `k - 1`. It is the whole content of
`RamDriverAugment.slotCnt_out_eq` at the list layer, and here it is not
a lemma about a walk but the *postcondition of a pass*. -/

/-- The slots of `[a, b)` that bump the cell `k`. -/
def bumpCnt (T : List ℕ) (a b k : ℕ) : ℕ :=
  ((Finset.Ico a b).filter fun p => T[p]! + 1 = k).card

theorem bumpCnt_self (T : List ℕ) (a k : ℕ) : bumpCnt T a a k = 0 := by simp [bumpCnt]

theorem bumpCnt_succ (T : List ℕ) {a b : ℕ} (h : a ≤ b) (k : ℕ) :
    bumpCnt T a (b + 1) k = bumpCnt T a b k + (if T[b]! + 1 = k then 1 else 0) := by
  rw [bumpCnt, bumpCnt, Nat.Ico_succ_right_eq_insert_Ico h, Finset.filter_insert]
  by_cases hb : T[b]! + 1 = k
  · rw [if_pos hb, if_pos hb, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg hb, if_neg hb, Nat.add_zero]

theorem bumpCnt_add (T : List ℕ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (k : ℕ) :
    bumpCnt T a b k + bumpCnt T b c k = bumpCnt T a c k := by
  rw [bumpCnt, bumpCnt, bumpCnt, ← Finset.card_union_of_disjoint, ← Finset.filter_union,
    Finset.Ico_union_Ico_eq_Ico hab hbc]
  exact Finset.disjoint_filter_filter
    (by rw [Finset.disjoint_left]; intro p hp hp'
        exact absurd (Finset.mem_Ico.1 hp').1 (by have := (Finset.mem_Ico.1 hp).2; omega))

/-- **The exchange, summed.** Every slot bumps exactly one cell, so the
counts the pass leaves add up to the number of slots. This is
`RamAugment.sum_card_outSet` at the list layer — the out-degrees add up
to the arcs — and it is what a width argument spends. -/
theorem sum_bumpCnt (T : List ℕ) (n a b : ℕ) (_hab : a ≤ b)
    (hlt : ∀ p, a ≤ p → p < b → T[p]! < n) :
    ∑ k ∈ Finset.range (n + 1), bumpCnt T a b k = b - a := by
  classical
  have hcard : ((Finset.Ico a b).card : ℕ) = b - a := Nat.card_Ico a b
  rw [← hcard]
  refine (Finset.card_eq_sum_card_fiberwise (f := fun p => T[p]! + 1) ?_).symm
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_Ico.1 hp
  have hT := hlt p hp1 hp2
  exact Finset.mem_range.2 (show T[p]! + 1 < n + 1 by omega)

/-- The scan's invariant, at the row start `j0`: every cell carries what
it started with plus the slots passed so far that bump it. -/
def cntInv (T O₀ : List ℕ) (j0 jend : ℕ) : CSt → Prop := fun s =>
  j0 ≤ s.2 ∧ s.2 ≤ jend ∧ s.1.length = O₀.length ∧
    ∀ k, k < s.1.length → s.1[k]! = O₀[k]! + bumpCnt T j0 s.2 k

theorem cntScan_le {Inv : CSt → Prop} (T : List ℕ) (jend : ℕ)
    (hs : ∀ t : CSt, Inv t → cntBf jend t = true → cntSlotP T t ∧ Inv (cntSlot T t)) :
    ∀ (fuel : ℕ) (s : CSt), Inv s → jend - s.2 ≤ fuel →
      cntScan T jend s
        ≤ NRest.spec (fun t : CSt => Inv t ∧ jend ≤ t.2)
            (fun _ => liftACost ((jend - s.2) • iter cntC + cu Currency.«while»)) := by
  have exit : ∀ s : CSt, Inv s → jend ≤ s.2 →
      cntScan T jend s
        ≤ NRest.spec (fun t : CSt => Inv t ∧ jend ≤ t.2)
            (fun _ => liftACost ((jend - s.2) • iter cntC + cu Currency.«while»)) := by
    intro s hI hk
    have hb : cntBf jend s = false := by simp only [cntBf, decide_eq_false_iff_not]; omega
    simp only [cntScan, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨hI, hk⟩ ?_
    rw [show jend - s.2 = 0 by omega]
    simp
  intro fuel
  induction fuel with
  | zero => intro s hI hf; exact exit s hI (by omega)
  | succ fuel ih =>
    intro s hI hf
    by_cases hb : s.2 < jend
    · have hbt : cntBf jend s = true := by simp [cntBf, hb]
      obtain ⟨hPs, hInv'⟩ := hs s hI hbt
      have hIs : cntBf jend s = true → cntSlotP T s := fun _ => hPs
      have hk' : (cntSlot T s).2 = s.2 + 1 := rfl
      have hih := ih (cntSlot T s) hInv' (by rw [hk']; omega)
      rw [hk'] at hih
      have hcost : irUnit Currency.«while»
          + (liftACost cntC + liftACost ((jend - (s.2 + 1)) • iter cntC + cu Currency.«while»))
          = liftACost ((jend - s.2) • iter cntC + cu Currency.«while») := by
        rw [show jend - s.2 = (jend - (s.2 + 1)) + 1 by omega, succ_nsmul]
        simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
        ac_rfl
      calc cntScan T jend s
          = NRest.consume (NRest.bindT (cntF T s) fun s' => cntScan T jend s')
              (irUnit Currency.«while») := by
            simp only [cntScan]; rw [irWhileIT_of_true hIs hbt]
        _ ≤ NRest.consume (NRest.bindT
              (NRest.consume (NRest.returnT (cntSlot T s)) (liftACost cntC))
              fun s' => cntScan T jend s') (irUnit Currency.«while») :=
            NRest.consume_mono (NRest.bindT_mono (cntF_le T s hPs) fun _ => le_rfl) le_rfl
        _ = NRest.consume (NRest.consume (cntScan T jend (cntSlot T s)) (liftACost cntC))
              (irUnit Currency.«while») := by rw [bindT_unitT]
        _ ≤ _ := by
            rw [← hcost]
            exact NRest.consume_mono (NRest.consume_mono hih le_rfl) le_rfl |>.trans
              (le_of_eq (by rw [Sepref.consume_spec, Sepref.consume_spec]))
    · exact exit s hI (by omega)

/-! ### 4.3 The pass -/

/-- The block structure the pass walks, as the tower reads it: the same
five clauses as `BfsQ.Shape` minus the mask, since this pass has none. -/
def CShape (n : ℕ) (doff dtg : List ℕ) : Prop :=
  doff.length = n + 1 ∧ (∀ i, i < n → doff[i]! ≤ doff[i + 1]!) ∧ doff[n]! ≤ dtg.length ∧
    ∀ p, p < dtg.length → dtg[p]! < n

theorem CShape.mono' {n : ℕ} {doff dtg : List ℕ} (h : CShape n doff dtg) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ n → doff[i]! ≤ doff[j]! := by
  intro i j hij hjn
  induction j with
  | zero => obtain rfl : i = 0 := Nat.le_zero.1 hij; exact le_rfl
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · exact le_trans (ih (by omega) (by omega)) (h.2.1 j (by omega))
    · obtain rfl : i = j + 1 := by omega
      exact le_rfl

def cntRowBf (n : ℕ) : CSt → Bool := fun s => decide (s.2 < n)

def cntRowP (n : ℕ) (doff dtg : List ℕ) : CSt → Prop := fun s =>
  CShape n doff dtg ∧ s.1.length = n + 1 ∧ s.2 < n

/-- One vertex's row: the block bounds, then the scan, then the counter. -/
noncomputable def cntRowF (doff dtg : List ℕ) : CSt → NRest CSt ECost := fun s =>
  bindT (mopAget doff s.2) fun j0 =>
    bindT (mopBinop .add s.2 1) fun ip =>
      bindT (mopAget doff ip) fun jend =>
        bindT (mopPair s.1 j0) fun z0 =>
          bindT (cntScan dtg jend z0) fun r =>
            bindT (BfsQSynth.mopSucc s.2) fun i => mopPair r.1 i

/-- **The counting pass.** -/
noncomputable def cntPass (n : ℕ) (doff dtg : List ℕ) (s₀ : CSt) : NRest CSt ECost :=
  irWhileIT (fun s => cntRowBf n s = true → cntRowP n doff dtg s) (cntRowBf n)
    (cntRowF doff dtg) s₀

/-- One row, everything outside the scan — including the scan loop's own
entry test. -/
def cntRowC : ACost String ℕ :=
  cu Currency.aget + cu (binopCurrency .add) + cu Currency.aget + cu Currency.skip
    + cu Currency.«while» + cu (binopCurrency .add) + cu Currency.skip

/-! ### 4.4 One row, and the pass -/

theorem cntRowF_le {n : ℕ} {doff dtg : List ℕ} (hsh : CShape n doff dtg)
    (s : CSt) (hlen : s.1.length = n + 1) (hi : s.2 < n) :
    cntRowF doff dtg s
      ≤ NRest.spec
          (fun t : CSt => t.1.length = n + 1 ∧ t.2 = s.2 + 1 ∧
            ∀ k, k < n + 1 → t.1[k]! = s.1[k]! + bumpCnt dtg doff[s.2]! doff[s.2 + 1]! k)
          (fun _ => liftACost (cntRowC + (doff[s.2 + 1]! - doff[s.2]!) • iter cntC)) := by
  have hdlen : doff.length = n + 1 := hsh.1
  have h0 : s.2 < doff.length := by omega
  have h1 : s.2 + 1 < doff.length := by omega
  have hmono : doff[s.2]! ≤ doff[s.2 + 1]! := hsh.2.1 _ hi
  have hrow : doff[s.2 + 1]! ≤ dtg.length :=
    le_trans (hsh.mono' (show s.2 + 1 ≤ n by omega) le_rfl) hsh.2.2.1
  have hs : ∀ z : CSt, cntInv dtg s.1 doff[s.2]! doff[s.2 + 1]! z →
      cntBf doff[s.2 + 1]! z = true →
      cntSlotP dtg z ∧ cntInv dtg s.1 doff[s.2]! doff[s.2 + 1]! (cntSlot dtg z) := by
    rintro z ⟨hz1, hz2, hz3, hz4⟩ hzb
    have hzlt : z.2 < doff[s.2 + 1]! := by simpa [cntBf] using hzb
    have hzt : z.2 < dtg.length := by omega
    have hun : dtg[z.2]! < n := hsh.2.2.2 _ hzt
    have hup : dtg[z.2]! + 1 < z.1.length := by omega
    refine ⟨⟨hzt, hup⟩, ?_, ?_, ?_, ?_⟩
    · show doff[s.2]! ≤ z.2 + 1
      omega
    · show z.2 + 1 ≤ doff[s.2 + 1]!
      omega
    · show (z.1.set (dtg[z.2]! + 1) _).length = _
      simpa using hz3
    · intro k hk
      show (z.1.set (dtg[z.2]! + 1) (z.1[dtg[z.2]! + 1]! + 1))[k]!
        = s.1[k]! + bumpCnt dtg doff[s.2]! (z.2 + 1) k
      rw [get!_set _ _ _ _ hup, bumpCnt_succ dtg hz1]
      by_cases hke : k = dtg[z.2]! + 1
      · rw [if_pos hke, if_pos (by omega), hke, hz4 _ hup]
        omega
      · have hk' : k < z.1.length := by simpa [cntSlot] using hk
        rw [if_neg hke, if_neg (by omega), hz4 k hk']
        omega
  have hstart : cntInv dtg s.1 doff[s.2]! doff[s.2 + 1]! (s.1, doff[s.2]!) :=
    ⟨le_rfl, hmono, rfl, fun k _ => by
      show s.1[k]! = s.1[k]! + bumpCnt dtg doff[s.2]! doff[s.2]! k
      rw [bumpCnt_self, Nat.add_zero]⟩
  have hscan := cntScan_le (Inv := cntInv dtg s.1 doff[s.2]! doff[s.2 + 1]!) dtg
    doff[s.2 + 1]! hs (doff[s.2 + 1]! - doff[s.2]!) (s.1, doff[s.2]!) hstart (by simp)
  have hK : ∀ r : CSt,
      (cntInv dtg s.1 doff[s.2]! doff[s.2 + 1]! r ∧ doff[s.2 + 1]! ≤ r.2) →
      NRest.consume (NRest.returnT ((r.1, s.2 + 1) : CSt))
          (irUnit (binopCurrency .add) + irUnit Currency.skip)
        ≤ NRest.spec
            (fun t : CSt => t.1.length = n + 1 ∧ t.2 = s.2 + 1 ∧
              ∀ k, k < n + 1 → t.1[k]! = s.1[k]! + bumpCnt dtg doff[s.2]! doff[s.2 + 1]! k)
            (fun _ => irUnit (binopCurrency .add) + irUnit Currency.skip) := by
    rintro r ⟨⟨-, hr2, hr3, hr4⟩, hdone⟩
    have hrend : r.2 = doff[s.2 + 1]! := by omega
    refine consume_returnT_le_spec ⟨by rw [hr3, hlen], rfl, fun k hk => ?_⟩ le_rfl
    rw [hr4 k (by rw [hr3, hlen]; exact hk), hrend]
  simp only [cntRowF, BfsQSynth.mopSucc_eq, mopAget_def, mopBinop_def, mopPair_def,
    NRest.assert_pos h0, NRest.assert_pos h1, NRest.returnT_bindT,
    NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, NRest.bindT_assoc_acost]
  refine le_trans (NRest.consume_mono
    (le_trans (NRest.bindT_mono hscan fun _ => le_rfl) (bindT_spec_le _ _ _ _ _ hK)) le_rfl)
    (le_of_eq ?_)
  rw [Sepref.consume_spec]
  refine congrArg (NRest.spec _) (funext fun _ => ?_)
  simp only [cntRowC, iter, liftACost_add, liftACost_nsmul, liftACost_cu, binopCurrency_add]
  ac_rfl

/-- **The counting pass, bounded.** Two currencies: one row-cost per
vertex still to visit and one slot-cost per slot still to scan. The
second is bounded because the rows *tile* the target array. -/
theorem cntPass_le {n : ℕ} {doff dtg : List ℕ} (hsh : CShape n doff dtg) (O₀ : List ℕ) :
    ∀ (fuel : ℕ) (s : CSt), s.1.length = n + 1 → s.2 ≤ n → n - s.2 ≤ fuel →
      (∀ k, k < n + 1 → s.1[k]! = O₀[k]! + bumpCnt dtg doff[0]! doff[s.2]! k) →
      cntPass n doff dtg s
        ≤ NRest.spec
            (fun t : CSt => t.1.length = n + 1 ∧
              ∀ k, k < n + 1 → t.1[k]! = O₀[k]! + bumpCnt dtg doff[0]! doff[n]! k)
            (fun _ => liftACost (E2 (iter cntRowC) (iter cntC) (n - s.2)
              (doff[n]! - doff[s.2]!) + cu Currency.«while»)) := by
  have exit : ∀ s : CSt, s.1.length = n + 1 → n ≤ s.2 → s.2 ≤ n →
      (∀ k, k < n + 1 → s.1[k]! = O₀[k]! + bumpCnt dtg doff[0]! doff[s.2]! k) →
      cntPass n doff dtg s
        ≤ NRest.spec
            (fun t : CSt => t.1.length = n + 1 ∧
              ∀ k, k < n + 1 → t.1[k]! = O₀[k]! + bumpCnt dtg doff[0]! doff[n]! k)
            (fun _ => liftACost (E2 (iter cntRowC) (iter cntC) (n - s.2)
              (doff[n]! - doff[s.2]!) + cu Currency.«while»)) := by
    intro s hlen hge hle hall
    have hb : cntRowBf n s = false := by simp only [cntRowBf, decide_eq_false_iff_not]; omega
    obtain rfl : s.2 = n := by omega
    simp only [cntPass, irWhile_exit hb]
    refine consume_returnT_le_spec ⟨hlen, hall⟩ ?_
    rw [liftACost_add, liftACost_cu, add_comm]
    exact cost_le_add _ _
  intro fuel
  induction fuel with
  | zero => intro s hlen hle hf hall; exact exit s hlen (by omega) hle hall
  | succ fuel ih =>
    intro s hlen hle hf hall
    by_cases hb : s.2 < n
    · have hbt : cntRowBf n s = true := by simp [cntRowBf, hb]
      have hIs : cntRowBf n s = true → cntRowP n doff dtg s := fun _ => ⟨hsh, hlen, hb⟩
      have hmono : doff[s.2]! ≤ doff[s.2 + 1]! := hsh.2.1 _ hb
      have htop : doff[s.2 + 1]! ≤ doff[n]! := hsh.mono' (by omega) le_rfl
      have hbot : doff[0]! ≤ doff[s.2]! := hsh.mono' (Nat.zero_le _) (by omega)
      have hcont : ∀ t : CSt, (t.1.length = n + 1 ∧ t.2 = s.2 + 1 ∧
            ∀ k, k < n + 1 → t.1[k]! = s.1[k]! + bumpCnt dtg doff[s.2]! doff[s.2 + 1]! k) →
          cntPass n doff dtg t
            ≤ NRest.spec
                (fun t' : CSt => t'.1.length = n + 1 ∧
                  ∀ k, k < n + 1 → t'.1[k]! = O₀[k]! + bumpCnt dtg doff[0]! doff[n]! k)
                (fun _ => liftACost (E2 (iter cntRowC) (iter cntC) (n - (s.2 + 1))
                  (doff[n]! - doff[s.2 + 1]!) + cu Currency.«while»)) := by
        rintro t ⟨htlen, hti, htval⟩
        refine le_trans (ih t htlen (by omega) (by omega) ?_) (le_of_eq ?_)
        · intro k hk
          rw [htval k hk, hall k hk, hti, Nat.add_assoc,
            bumpCnt_add dtg hbot hmono k]
        · rw [hti]
      have hcost : irUnit Currency.«while»
          + (liftACost (cntRowC + (doff[s.2 + 1]! - doff[s.2]!) • iter cntC)
            + liftACost (E2 (iter cntRowC) (iter cntC) (n - (s.2 + 1))
                (doff[n]! - doff[s.2 + 1]!) + cu Currency.«while»))
          = liftACost (E2 (iter cntRowC) (iter cntC) (n - s.2)
              (doff[n]! - doff[s.2]!) + cu Currency.«while») := by
        rw [show n - s.2 = (n - (s.2 + 1)) + 1 by omega,
          show doff[n]! - doff[s.2]!
            = (doff[n]! - doff[s.2 + 1]!) + (doff[s.2 + 1]! - doff[s.2]!) by omega,
          E2_split]
        simp only [iter, liftACost_add, liftACost_nsmul, liftACost_cu]
        ac_rfl
      calc cntPass n doff dtg s
            = NRest.consume (NRest.bindT (cntRowF doff dtg s)
                fun t => cntPass n doff dtg t) (irUnit Currency.«while») := by
              simp only [cntPass]; rw [irWhileIT_of_true hIs hbt]
        _ ≤ NRest.consume (NRest.spec _ (fun _ =>
              liftACost (cntRowC + (doff[s.2 + 1]! - doff[s.2]!) • iter cntC)
              + liftACost (E2 (iter cntRowC) (iter cntC) (n - (s.2 + 1))
                  (doff[n]! - doff[s.2 + 1]!) + cu Currency.«while»)))
              (irUnit Currency.«while») :=
            NRest.consume_mono
              (le_trans (NRest.bindT_mono (cntRowF_le hsh s hlen hb) fun _ => le_rfl)
                (bindT_spec_le _ _ _ _ _ hcont)) le_rfl
        _ = _ := by rw [Sepref.consume_spec, ← hcost]
    · exact exit s hlen (by omega) hle hall

/-- **The counting pass, run from the start**: what it leaves at `u+1`
is the number of slots naming `u` — the out-degree of `u`. -/
theorem cntPass_spec {n : ℕ} {doff dtg : List ℕ} (hsh : CShape n doff dtg)
    (O₀ : List ℕ) (hO : O₀.length = n + 1) (hz : ∀ k, k < n + 1 → O₀[k]! = 0)
    (hd0 : doff[0]! = 0) :
    cntPass n doff dtg (O₀, 0)
      ≤ NRest.spec
          (fun t : CSt => t.1.length = n + 1 ∧
            ∀ k, k < n + 1 → t.1[k]! = bumpCnt dtg 0 doff[n]! k)
          (fun _ => liftACost (E2 (iter cntRowC) (iter cntC) n doff[n]!
            + cu Currency.«while»)) := by
  have hstart : ∀ k, k < n + 1 →
      (O₀, (0 : ℕ)).1[k]! = O₀[k]! + bumpCnt dtg doff[0]! doff[(O₀, (0 : ℕ)).2]! k :=
    fun k _ => by
      show O₀[k]! = O₀[k]! + bumpCnt dtg doff[0]! doff[0]! k
      rw [bumpCnt_self, Nat.add_zero]
  refine le_trans (cntPass_le hsh O₀ n (O₀, 0) hO (Nat.zero_le n) (by simp) hstart) ?_
  refine spec_mono (fun t ht => ⟨ht.1, fun k hk => ?_⟩) (fun _ _ => le_of_eq (by rw [hd0, Nat.sub_zero, Nat.sub_zero]))
  rw [ht.2 k hk, hz k hk, hd0, Nat.zero_add]

/-! ### 4.5 The synthesis -/

set_option maxHeartbeats 1000000 in
sepref_synth cntScanSynth (dtg : List ℕ) (jend j₀ : ℕ) (ooff₀ : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (ooff₀, j₀) ("ooff", "agj") ∗
      hnCtxt arrayAssn dtg "dtg" ∗ hnCtxt natAssn jend "agend" ∗
      hnCtxt natAssn 1 "one" ∗
      junkCell "agu" ∗ junkCell "agup" ∗ junkCell "agc")
    _ _ ("ooff", "agj") (arrayAssn ×ₐ natAssn)
    (cntScan dtg jend (ooff₀, j₀))

/-! **The whole counting pass, synthesized — both loops.** This is the
measurement satellite 2B's P2/2B/D-a asked for: a two-loop pass whose
inner loop sits *in the middle* of the outer body and whose result feeds
the operations after it translates in seconds, at the same budget on
which 2B's `degPass` times out. The variable the two runs isolate is
therefore **not** nesting and **not** a mid-body loop: it is 2B's
two-armed `irIf` whose both arms `mopAset` the enclosing loop's own
state array. See the header's F1. -/
set_option maxHeartbeats 1000000 in
sepref_synth cntPassSynth (n : ℕ) (doff dtg ooff₀ : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (ooff₀, 0) ("ooff", "agi") ∗
      hnCtxt arrayAssn doff "doff" ∗ hnCtxt arrayAssn dtg "dtg" ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "agjo" ∗ junkCell "agip" ∗ junkCell "agend" ∗
      junkCell "agu" ∗ junkCell "agup" ∗ junkCell "agc")
    _ _ ("ooff", "agi") (arrayAssn ×ₐ natAssn)
    (cntPass n doff dtg (ooff₀, 0))

-- The synthesized counting pass, pinned: `RamAugment.outCount` —
-- `forVerts (blockScan "doff" "dtg" …)` — instruction for instruction,
-- with the row bounds loaded into `agjo`/`agend` exactly as
-- `Csr.loadRow` loads them.
#guard cntPassSynth_impl =
  Com.while (Cond.lt (Operand.cell "agi") (Operand.cell "n"))
    ((Com.aget "agjo" "doff" "agi").seq
      ((Com.binop Lax13Proofs.Imp.Bop.add "agip" "agi" "one").seq
        ((Com.aget "agend" "doff" "agip").seq
          (Com.skip.seq
            ((Com.while (Cond.lt (Operand.cell "agjo") (Operand.cell "agend"))
                  ((Com.aget "agu" "dtg" "agjo").seq
                    ((Com.binop Lax13Proofs.Imp.Bop.add "agup" "agu" "one").seq
                      ((Com.aget "agc" "ooff" "agup").seq
                        ((Com.binop Lax13Proofs.Imp.Bop.add "agc" "agc" "one").seq
                          ((Com.aset "ooff" "agup" "agc").seq
                            ((Com.binop Lax13Proofs.Imp.Bop.add "agjo" "agjo" "one").seq
                              Com.skip))))))).seq
              ((Com.binop Lax13Proofs.Imp.Bop.add "agi" "agi" "one").seq Com.skip))))))

end Count

/-! ## 4b. The prefix pass's bounds pass, via `BRefine`

The first body in this file with genuine arithmetic *creation* sites:
two `add`s whose results have to fit in a word. Both side conditions are
about the **abstract** values, and both are supplied by the abstract
program's own invariant — the running sum's own bound. No `Ir.State`
predicate is authored (P0.2's verdict, R2/D-b).

The seven scratch values are existential in the loop assertion, as
`ScatterSynth`'s seven are: `BRefine` has no junk-cell rule (§10, tool
gap 2). -/

section PrefBounds

/-- The prefix pass's assertion at *named* scratch values. -/
def pfΓ (n : ℕ) (O F : List ℕ) (i ip b a t : ℕ) : Assn :=
  arrayAssn O "ooff" ∗ arrayAssn F "ofl" ∗ natAssn i "agi" ∗ natAssn n "n" ∗
    natAssn 1 "one" ∗ natAssn ip "agip" ∗ natAssn b "agb" ∗ natAssn a "aga" ∗
    natAssn t "agt"

/-- …and the loop assertion, with the four scratch cells quantified. -/
def prefΓ (n : ℕ) : PSt → Assn := fun s =>
  sepEx fun y : ℕ × ℕ × ℕ × ℕ => pfΓ n s.1 s.2.1 s.2.2 y.1 y.2.1 y.2.2.1 y.2.2.2

/-- The abstract invariant the bounds pass runs on: the pass's own
invariant, plus the word bound on the running sum (statement delta
P7/D-bo). -/
def prefIB (n B : ℕ) (O₀ : List ℕ) : PSt → Prop := fun t =>
  prefInv n O₀ t ∧ ∀ k, k ≤ n → cumsum O₀ k < B

theorem pfΓ_agi {n : ℕ} {O F : List ℕ} {i ip b a t : ℕ} {F' : Assn} {s : Ir.State}
    {cr : ECost} (h : irSTATE (pfΓ n O F i ip b a t ∗ F') (s, cr)) : s.vars "agi" = some i :=
  natAssn_vars (F := (arrayAssn O "ooff" ∗ arrayAssn F "ofl" ∗ natAssn n "n" ∗
    natAssn 1 "one" ∗ natAssn ip "agip" ∗ natAssn b "agb" ∗ natAssn a "aga" ∗
    natAssn t "agt") ∗ F') (irSTATE_cong (by simp only [pfΓ]; ac_rfl) h)

theorem pfΓ_n {n : ℕ} {O F : List ℕ} {i ip b a t : ℕ} {F' : Assn} {s : Ir.State}
    {cr : ECost} (h : irSTATE (pfΓ n O F i ip b a t ∗ F') (s, cr)) : s.vars "n" = some n :=
  natAssn_vars (F := (arrayAssn O "ooff" ∗ arrayAssn F "ofl" ∗ natAssn i "agi" ∗
    natAssn 1 "one" ∗ natAssn ip "agip" ∗ natAssn b "agb" ∗ natAssn a "aga" ∗
    natAssn t "agt") ∗ F') (irSTATE_cong (by simp only [pfΓ]; ac_rfl) h)

theorem pfΓ_entails_prefΓ (n : ℕ) (O F : List ℕ) (i ip b a t : ℕ) :
    pfΓ n O F i ip b a t ⊢ prefΓ n (O, F, i) :=
  fun _ h => ⟨(ip, b, a, t), h⟩

theorem pref_guard {B n : ℕ} {O₀ : List ℕ} (t : PSt) (F : Assn) (s : Ir.State) (cr : ECost)
    (r : Bool) (_ : prefIB n B O₀ t) (hs : irSTATE (prefΓ n t ∗ F) (s, cr))
    (hev : (Cond.lt (Operand.cell "agi") (Operand.cell "n")).eval s = some r) :
    decide (t.2.2 < n) = r := by
  obtain ⟨x, y, hx, hy, rfl⟩ := BfsQSynth.eval_lt_cells hev
  simp only [prefΓ] at hs
  rw [sepEx_sepConj] at hs
  obtain ⟨z, hz⟩ := hs
  rw [pfΓ_agi hz] at hx
  rw [pfΓ_n hz] at hy
  rw [Option.some.inj hx, Option.some.inj hy]

section PrefSteps

variable {B n : ℕ} {O F : List ℕ} {i ip b a t : ℕ}

theorem pstep_ip (hb : Lax13Proofs.Imp.Bop.apply .add i 1 < B) :
    BRefine B (pfΓ n O F i ip b a t) (Com.binop Lax13Proofs.Imp.Bop.add "agip" "agi" "one")
      (pfΓ n O F i (Lax13Proofs.Imp.Bop.apply .add i 1) b a t) :=
  BRefine.perm
    (P := (natAssn ip "agip" ∗ natAssn i "agi" ∗ natAssn 1 "one") ∗
      (arrayAssn O "ooff" ∗ arrayAssn F "ofl" ∗ natAssn n "n" ∗ natAssn b "agb" ∗
        natAssn a "aga" ∗ natAssn t "agt"))
    (P' := (natAssn (Lax13Proofs.Imp.Bop.apply .add i 1) "agip" ∗ natAssn i "agi" ∗
        natAssn 1 "one") ∗
      (arrayAssn O "ooff" ∗ arrayAssn F "ofl" ∗ natAssn n "n" ∗ natAssn b "agb" ∗
        natAssn a "aga" ∗ natAssn t "agt"))
    (by simp only [pfΓ]; ac_rfl) (by simp only [pfΓ]; ac_rfl)
    (BRefine.frame (BRefine.binop hb))

theorem pstep_b :
    BRefine B (pfΓ n O F i ip b a t) (Com.aget "agb" "ooff" "agip")
      (⌜ip < O.length⌝ ∗ pfΓ n O F i ip O[ip]! a t) :=
  BRefine.perm
    (P := (natAssn b "agb" ∗ arrayAssn O "ooff" ∗ natAssn ip "agip") ∗
      (arrayAssn F "ofl" ∗ natAssn i "agi" ∗ natAssn n "n" ∗ natAssn 1 "one" ∗
        natAssn a "aga" ∗ natAssn t "agt"))
    (P' := (⌜ip < O.length⌝ ∗ natAssn O[ip]! "agb" ∗ arrayAssn O "ooff" ∗
        natAssn ip "agip") ∗
      (arrayAssn F "ofl" ∗ natAssn i "agi" ∗ natAssn n "n" ∗ natAssn 1 "one" ∗
        natAssn a "aga" ∗ natAssn t "agt"))
    (by simp only [pfΓ]; ac_rfl) (by simp only [pfΓ]; ac_rfl)
    (BRefine.frame BRefine.aget)

theorem pstep_a :
    BRefine B (pfΓ n O F i ip b a t) (Com.aget "aga" "ooff" "agi")
      (⌜i < O.length⌝ ∗ pfΓ n O F i ip b O[i]! t) :=
  BRefine.perm
    (P := (natAssn a "aga" ∗ arrayAssn O "ooff" ∗ natAssn i "agi") ∗
      (arrayAssn F "ofl" ∗ natAssn n "n" ∗ natAssn 1 "one" ∗ natAssn ip "agip" ∗
        natAssn b "agb" ∗ natAssn t "agt"))
    (P' := (⌜i < O.length⌝ ∗ natAssn O[i]! "aga" ∗ arrayAssn O "ooff" ∗ natAssn i "agi") ∗
      (arrayAssn F "ofl" ∗ natAssn n "n" ∗ natAssn 1 "one" ∗ natAssn ip "agip" ∗
        natAssn b "agb" ∗ natAssn t "agt"))
    (by simp only [pfΓ]; ac_rfl) (by simp only [pfΓ]; ac_rfl)
    (BRefine.frame BRefine.aget)

theorem pstep_t (hb : Lax13Proofs.Imp.Bop.apply .add b a < B) :
    BRefine B (pfΓ n O F i ip b a t) (Com.binop Lax13Proofs.Imp.Bop.add "agt" "agb" "aga")
      (pfΓ n O F i ip b a (Lax13Proofs.Imp.Bop.apply .add b a)) :=
  BRefine.perm
    (P := (natAssn t "agt" ∗ natAssn b "agb" ∗ natAssn a "aga") ∗
      (arrayAssn O "ooff" ∗ arrayAssn F "ofl" ∗ natAssn i "agi" ∗ natAssn n "n" ∗
        natAssn 1 "one" ∗ natAssn ip "agip"))
    (P' := (natAssn (Lax13Proofs.Imp.Bop.apply .add b a) "agt" ∗ natAssn b "agb" ∗
        natAssn a "aga") ∗
      (arrayAssn O "ooff" ∗ arrayAssn F "ofl" ∗ natAssn i "agi" ∗ natAssn n "n" ∗
        natAssn 1 "one" ∗ natAssn ip "agip"))
    (by simp only [pfΓ]; ac_rfl) (by simp only [pfΓ]; ac_rfl)
    (BRefine.frame (BRefine.binop hb))

theorem pstep_setO :
    BRefine B (pfΓ n O F i ip b a t) (Com.aset "ooff" "agip" "agt")
      (⌜ip < O.length⌝ ∗ pfΓ n (O.set ip t) F i ip b a t) :=
  BRefine.perm
    (P := (arrayAssn O "ooff" ∗ natAssn ip "agip" ∗ natAssn t "agt") ∗
      (arrayAssn F "ofl" ∗ natAssn i "agi" ∗ natAssn n "n" ∗ natAssn 1 "one" ∗
        natAssn b "agb" ∗ natAssn a "aga"))
    (P' := (⌜ip < O.length⌝ ∗ arrayAssn (O.set ip t) "ooff" ∗ natAssn ip "agip" ∗
        natAssn t "agt") ∗
      (arrayAssn F "ofl" ∗ natAssn i "agi" ∗ natAssn n "n" ∗ natAssn 1 "one" ∗
        natAssn b "agb" ∗ natAssn a "aga"))
    (by simp only [pfΓ]; ac_rfl) (by simp only [pfΓ]; ac_rfl)
    (BRefine.frame BRefine.aset)

theorem pstep_setF :
    BRefine B (pfΓ n O F i ip b a t) (Com.aset "ofl" "agi" "aga")
      (⌜i < F.length⌝ ∗ pfΓ n O (F.set i a) i ip b a t) :=
  BRefine.perm
    (P := (arrayAssn F "ofl" ∗ natAssn i "agi" ∗ natAssn a "aga") ∗
      (arrayAssn O "ooff" ∗ natAssn n "n" ∗ natAssn 1 "one" ∗ natAssn ip "agip" ∗
        natAssn b "agb" ∗ natAssn t "agt"))
    (P' := (⌜i < F.length⌝ ∗ arrayAssn (F.set i a) "ofl" ∗ natAssn i "agi" ∗
        natAssn a "aga") ∗
      (arrayAssn O "ooff" ∗ natAssn n "n" ∗ natAssn 1 "one" ∗ natAssn ip "agip" ∗
        natAssn b "agb" ∗ natAssn t "agt"))
    (by simp only [pfΓ]; ac_rfl) (by simp only [pfΓ]; ac_rfl)
    (BRefine.frame BRefine.aset)

theorem pstep_bump (hb : Lax13Proofs.Imp.Bop.apply .add i 1 < B) :
    BRefine B (pfΓ n O F i ip b a t) (Com.binop Lax13Proofs.Imp.Bop.add "agi" "agi" "one")
      (pfΓ n O F (Lax13Proofs.Imp.Bop.apply .add i 1) ip b a t) :=
  BRefine.perm
    (P := (natAssn i "agi" ∗ natAssn 1 "one") ∗
      (arrayAssn O "ooff" ∗ arrayAssn F "ofl" ∗ natAssn n "n" ∗ natAssn ip "agip" ∗
        natAssn b "agb" ∗ natAssn a "aga" ∗ natAssn t "agt"))
    (P' := (natAssn (Lax13Proofs.Imp.Bop.apply .add i 1) "agi" ∗ natAssn 1 "one") ∗
      (arrayAssn O "ooff" ∗ arrayAssn F "ofl" ∗ natAssn n "n" ∗ natAssn ip "agip" ∗
        natAssn b "agb" ∗ natAssn a "aga" ∗ natAssn t "agt"))
    (by simp only [pfΓ]; ac_rfl) (by simp only [pfΓ]; ac_rfl)
    (BRefine.frame (BRefine.binop_self hb))

end PrefSteps

/-- The prefix pass's loop body, named. -/
def prefBody : Com :=
  (Com.binop Lax13Proofs.Imp.Bop.add "agip" "agi" "one").seq
    ((Com.aget "agb" "ooff" "agip").seq
      ((Com.aget "aga" "ooff" "agi").seq
        ((Com.binop Lax13Proofs.Imp.Bop.add "agt" "agb" "aga").seq
          ((Com.aset "ooff" "agip" "agt").seq
            ((Com.aset "ofl" "agi" "aga").seq
              ((Com.binop Lax13Proofs.Imp.Bop.add "agi" "agi" "one").seq
                (Com.skip.seq Com.skip)))))))

theorem prefSynth_impl_eq :
    prefSynth_impl = Com.while (Cond.lt (Operand.cell "agi") (Operand.cell "n")) prefBody :=
  rfl

/-- **The prefix pass's loop body.** Two arithmetic side conditions —
the index `i+1` and the running sum — and both are discharged from the
abstract invariant: the sum the body creates is `cumsum O₀ (i+1)`, which
the invariant bounds. -/
theorem pref_body_brefine {B n : ℕ} {O₀ : List ℕ} (hnB : n < B) (t : PSt)
    (hI : prefIB n B O₀ t) (hbf : decide (t.2.2 < n) = true) :
    BRefine B (prefΓ n t) prefBody (LoopAssn (prefIB n B O₀) (prefΓ n)) := by
  have hlt : t.2.2 < n := of_decide_eq_true hbf
  obtain ⟨⟨hOl, hFl, hin, hpre, hsuf, hfl⟩, hcb⟩ := hI
  have hb : t.1[t.2.2 + 1]! = O₀[t.2.2 + 1]! := hsuf _ (by omega) (by omega)
  have ha : t.1[t.2.2]! = cumsum O₀ t.2.2 := hpre _ le_rfl
  have hsum : Lax13Proofs.Imp.Bop.apply .add t.1[t.2.2 + 1]! t.1[t.2.2]! < B := by
    rw [Lax13Proofs.Imp.Bop.apply_add, hb, ha, Nat.add_comm, ← cumsum_succ]
    exact hcb _ (by omega)
  have hip : Lax13Proofs.Imp.Bop.apply .add t.2.2 1 < B := by
    rw [Lax13Proofs.Imp.Bop.apply_add]; omega
  simp only [prefΓ]
  refine BRefine.pre_ex fun y => ?_
  rw [prefBody]
  refine BRefine.seq (pstep_ip hip) ?_
  refine BRefine.seq pstep_b (BRefine.pre_pure fun _ => ?_)
  refine BRefine.seq pstep_a (BRefine.pre_pure fun _ => ?_)
  refine BRefine.seq (pstep_t hsum) ?_
  refine BRefine.seq pstep_setO (BRefine.pre_pure fun _ => ?_)
  refine BRefine.seq pstep_setF (BRefine.pre_pure fun _ => ?_)
  refine BRefine.seq (pstep_bump hip)
    (BRefine.seq BRefine.skip (BRefine.skip.cons (entails_refl _) ?_))
  have hstep : prefIB n B O₀ (prefStep t) :=
    ⟨prefInv_step ⟨hOl, hFl, hin, hpre, hsuf, hfl⟩ hlt, hcb⟩
  exact entails_trans (pfΓ_entails_prefΓ _ _ _ _ _ _ _ _)
    (loopAssn_intro (I := prefIB n B O₀) (Γ := prefΓ n) (t := prefStep t) hstep)

/-- **The prefix pass's bounds pass.** -/
theorem pref_brefine {B n : ℕ} {O₀ : List ℕ} (hnB : n < B) :
    BRefine B (LoopAssn (prefIB n B O₀) (prefΓ n)) prefSynth_impl
      (LoopAssn (prefIB n B O₀) (prefΓ n)) := by
  rw [prefSynth_impl_eq]
  exact BRefine.while_guard (bf := fun t => decide (t.2.2 < n))
    BfsQSynth.litLt_lt_cells (fun t F s cr r hI hs hev => pref_guard t F s cr r hI hs hev)
    (fun t hI hbf => pref_body_brefine hnB t hI hbf)
    (fun t hI _ => loopAssn_intro hI)

end PrefBounds

/-! ## 5. Gate: the *synthesized* programs, run

§1 tested the twins; this section tests the `Ir.Com`s the tool emitted,
by `Ir/Semantics.lean`'s own evaluator, on the same data — so the chain
twin → abstract program → synthesized program is closed by computation
at both ends. Every positive check carries a negative control. -/

section Gate

/-- The counting pass's store: nine scalars, three arrays. -/
def cntState (n : ℕ) (doff dtg : List ℕ) : Ir.State :=
  Ir.State.ofPairs
    [("agi", 0), ("n", n), ("one", 1), ("agjo", 0), ("agip", 0), ("agend", 0),
      ("agu", 0), ("agup", 0), ("agc", 0)]
    [("ooff", List.replicate (n + 1) 0), ("doff", doff), ("dtg", dtg)]

def gCnt (n : ℕ) (doff dtg : List ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 4000 cntPassSynth_impl (cntState n doff dtg)).bind fun p => p.1.arrs "ooff"

/-- The prefix pass's store. -/
def prefState (n : ℕ) (O₀ : List ℕ) : Ir.State :=
  Ir.State.ofPairs
    [("agi", 0), ("n", n), ("one", 1), ("agip", 0), ("agb", 0), ("aga", 0), ("agt", 0)]
    [("ooff", O₀), ("ofl", List.replicate n 0)]

def gPref (n : ℕ) (O₀ : List ℕ) : Option (List ℕ × List ℕ) :=
  (Ir.evalFuel 4000 prefSynth_impl (prefState n O₀)).bind fun p =>
    (p.1.arrs "ooff").bind fun O => (p.1.arrs "ofl").map fun F => (O, F)

/-- The mask pass's store. -/
def alvState (n : ℕ) (A₀ : List ℕ) : Ir.State :=
  Ir.State.ofPairs [("agi", 0), ("n", n), ("one", 1)] [("alv", A₀)]

def gAlv (n : ℕ) (A₀ : List ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 4000 alvSynth_impl (alvState n A₀)).bind fun p => p.1.arrs "alv"

-- **The counting pass agrees with its twin** on the demo orientation …
#guard gCnt 4 dOff dTgt = some (outCountTw 4 dOff dTgt)
#guard gCnt 4 dOff dTgt = some [0, 2, 1, 1, 0]
-- … on the doubly-witnessed pair …
#guard gCnt 4 wOff wTgt = some (outCountTw 4 wOff wTgt)
-- … and on the K₁,₄ witness, where every leaf has out-degree one
#guard gCnt 5 starOff starTgt = some (outCountTw 5 starOff starTgt)
#guard gCnt 5 starOff starTgt = some [0, 0, 1, 1, 1, 1]

-- **The prefix pass agrees with its twin**, and turns the counts into
-- the block structure `RamAugment.Demo` runs on.
#guard gPref 4 (outCountTw 4 dOff dTgt) = some (prefixTw 4 (outCountTw 4 dOff dTgt))
#guard gPref 4 (outCountTw 4 dOff dTgt) = some ([0, 2, 3, 4, 4], [0, 2, 3, 4])

-- **The mask pass** sets every bit of the carrier.
#guard gAlv 4 [0, 0, 0, 0] = some [1, 1, 1, 1]
#guard gAlv 5 [0, 1, 0, 1, 0] = some [1, 1, 1, 1, 1]

-- **The negative controls.** The counting pass counts the *out*-degrees
-- and the check can tell an in-degree array …
/--
error: Expression
  decide (gCnt 4 dOff dTgt = some [0, 0, 1, 2, 1])
did not evaluate to `true`
-/
#guard_msgs in
#guard gCnt 4 dOff dTgt = some [0, 0, 1, 2, 1]

-- … the prefix pass really accumulates …
/--
error: Expression
  decide (gPref 4 (outCountTw 4 dOff dTgt) = some ([0, 2, 1, 1, 0], [0, 2, 3, 4]))
did not evaluate to `true`
-/
#guard_msgs in
#guard gPref 4 (outCountTw 4 dOff dTgt) = some ([0, 2, 1, 1, 0], [0, 2, 3, 4])

-- … and the mask pass really runs.
/--
error: Expression
  decide (gAlv 4 [0, 0, 0, 0] = some [0, 0, 0, 0])
did not evaluate to `true`
-/
#guard_msgs in
#guard gAlv 4 [0, 0, 0, 0] = some [0, 0, 0, 0]

/-! ### 5.1 The out-list build, end to end

The two synthesized passes composed by hand — the counting pass, then
the prefix pass on what it left — reproduce `outPassTw`'s offsets, which
are the block structure `RamAugment.Demo`'s fraternity build reads. This
is the *`Spec`-level* composition of §6: two synthesized programs glued
outside the tool. -/

def gOutPass (n : ℕ) (doff dtg : List ℕ) : Option (List ℕ × List ℕ) :=
  (gCnt n doff dtg).bind fun O => gPref n O

#guard gOutPass 4 dOff dTgt = some ([0, 2, 3, 4, 4], [0, 2, 3, 4])
#guard (gOutPass 4 dOff dTgt).map (fun p => p.1) = some (outPassTw 4 4 dOff dTgt).1
#guard (gOutPass 5 starOff starTgt).map (fun p => p.1) = some (outPassTw 5 4 starOff starTgt).1

end Gate

/-! ## 6. The costs, computed, and the mask pass's export

The per-iteration accounts of §2–§4 are cashed by `decide +kernel` — the
constants are *computed*, not tuned — and the mask pass is carried the
rest of the way to a `Reasoning.Spec` in the baseline's own vocabulary.
§9 tabulates all three against `RamDriverAugment`'s hand-tuned
figures. -/

section Cost

open Lax13Proofs.Refine.BfsQ (fillC)

/-- **The mask pass's cost**: `12·n + 4` IMP+ time units, against the
baseline's `11·n + 8` (`RamDriverAugment.alvSet_run`). -/
def alvK (n : ℕ) : ℕ := 12 * n + 4

/-- **The prefix pass's cost**: `30·n + 4`, against the baseline's
`≈ 23·n + 8`. The gap is R2C/D-b — `i+1` is a cell and the counter's
bump is a second `add`. -/
def prefK (n : ℕ) : ℕ := 30 * n + 4

/-- **The counting pass's cost**: `24·n + 26·m + 4`, two currencies —
one per vertex and one per *slot* — against the baseline's
`21·m + 20·n + 8` (`RamDriverAugment.outCount_run`). The `m` here is
`doff[n]`, the number of arcs, so this is the touched-only charge the
campaign's cost discipline asks for: no array is swept. -/
def cntK (n m : ℕ) : ℕ := 24 * n + 26 * m + 4

theorem ecash_alvTotal (n : ℕ) :
    ecash (liftACost (n • iter fillC + cu Currency.«while»)) = (alvK n : ℕ∞) := by
  rw [BfsQSynth.ecash_liftACost, Codegen.cash_add, BfsQSynth.cash_nsmul,
    show Codegen.cash (iter fillC) = 12 from by decide +kernel,
    show Codegen.cash (cu Currency.«while») = 4 from by decide +kernel, alvK]
  push_cast
  ring

theorem ecash_prefTotal (n : ℕ) :
    ecash (liftACost (n • iter prefC + cu Currency.«while»)) = (prefK n : ℕ∞) := by
  rw [BfsQSynth.ecash_liftACost, Codegen.cash_add, BfsQSynth.cash_nsmul,
    show Codegen.cash (iter prefC) = 30 from by decide +kernel,
    show Codegen.cash (cu Currency.«while») = 4 from by decide +kernel, prefK]
  push_cast
  ring

theorem ecash_cntTotal (n m : ℕ) :
    ecash (liftACost (E2 (iter cntRowC) (iter cntC) n m + cu Currency.«while»))
      = (cntK n m : ℕ∞) := by
  rw [E2, BfsQSynth.ecash_liftACost, Codegen.cash_add, Codegen.cash_add,
    BfsQSynth.cash_nsmul, BfsQSynth.cash_nsmul,
    show Codegen.cash (iter cntRowC) = 24 from by decide +kernel,
    show Codegen.cash (iter cntC) = 26 from by decide +kernel,
    show Codegen.cash (cu Currency.«while») = 4 from by decide +kernel, cntK]
  push_cast
  ring

end Cost

/-! ### 6.1 The mask pass, exported

The cashing chain at one initial store, then the `Reasoning.Spec` a
caller in the baseline's own vocabulary can consume. This is the pass
whose export the driver reads through `RamElim.masked_of_all_alive` —
"the arena of an all-ones mask is the graph" — so the postcondition
below is exactly what that lemma's hypothesis wants, at the tower's list
arrays and with the two standing statement deltas (P7/D-bo, P7/D-bp). -/

section Export

open Lax13Proofs.Reasoning (arrOf length_arrOf)
open Lax13Proofs.Refine.BfsQ (fillC)

def alvPre (n : ℕ) (A₀ : List ℕ) : Assn :=
  hnCtxt (arrayAssn ×ₐ natAssn) (A₀, 0) ("alv", "agi") ∗ hnCtxt natAssn n "n" ∗
    hnCtxt natAssn 1 "one"

def alvFrame (n : ℕ) : Assn := hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one"

theorem alvSynth' (n : ℕ) (A₀ : List ℕ) :
    hnRefine (alvPre n A₀) alvSynth_impl (alvFrame n) ("alv", "agi")
      (arrayAssn ×ₐ natAssn) (BfsQSynth.fillLoop' n 1 (A₀, 0)) := alvSynth n A₀

def alvHole (n : ℕ) (A₀ : List ℕ) : Assn :=
  EXACT ((vcells (alvState n A₀) |>.erase "agi" |>.erase "n" |>.erase "one",
    acells (alvState n A₀) |>.erase "alv", hcells (alvState n A₀)), 0)

theorem alv_state_holds (n : ℕ) (A₀ : List ℕ) :
    irSTATE (alvPre n A₀ ∗ alvHole n A₀) (alvState n A₀, 0) := by
  show (alvPre n A₀ ∗ alvHole n A₀)
    ((vcells (alvState n A₀), acells (alvState n A₀), hcells (alvState n A₀)), 0)
  simp only [alvPre, hnCtxt, prodAssn, natAssn_def, arrayAssn_def, sepConj_assoc]
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  exact Ir.ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩

theorem alvΓ_holds (n : ℕ) (A₀ : List ℕ) :
    irSTATE (alvΓ n (A₀, 0) ∗ alvHole n A₀) (alvState n A₀, 0) := by
  show (alvΓ n (A₀, 0) ∗ alvHole n A₀)
    ((vcells (alvState n A₀), acells (alvState n A₀), hcells (alvState n A₀)), 0)
  simp only [alvΓ, natAssn_def, arrayAssn_def, sepConj_assoc]
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  exact Ir.ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩

theorem alvState_bound {B n : ℕ} {A₀ : List ℕ} (hnB : n < B) (h1B : 1 < B)
    (hA : ∀ v ∈ A₀, v < B) : Ir.StateBound B (alvState n A₀) := by
  refine Codegen.stateBound_ofPairs ?_ ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simpa using by omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact hA

theorem alv_bpre {B n : ℕ} {A₀ : List ℕ} (hnB : n < B) (h1B : 1 < B)
    (hA : ∀ v ∈ A₀, v < B) :
    Ir.bpre B alvSynth_impl (fun _ => True) (alvState n A₀) :=
  bpre_of_BRefine (F := alvHole n A₀) (alv_brefine hnB)
    (start_entailsE (alvΓ_holds n A₀)
      (sepConj_mono_left (loopAssn_intro (I := alvI n) (Γ := alvΓ n)
        (t := (A₀, 0)) (Nat.zero_le n))))
    (alvState_bound hnB h1B hA)

theorem alv_spec_at {B n : ℕ} (A₀ : List ℕ) (hnB : n < B) (h1B : 1 < B)
    (hA : ∀ v ∈ A₀, v < B) (hlen : A₀.length = n) :
    Lax13Proofs.Reasoning.Spec B (agree (alvState n A₀)) (embed alvSynth_impl)
      (fun _ σ' => ∃ A : List ℕ, σ'.arrs "alv" = A ∧ A.length = n ∧ ∀ j, j < n → A[j]! = 1)
      (alvK n) := by
  have hle := alvLoop_le n A₀ hlen
  have hspec := spec_of_hnRefine
    (Φ := fun p : List ℕ × ℕ => p.1.length = n ∧ ∀ j, j < n → p.1[j]! = 1)
    (Q := fun (ra : List ℕ × ℕ) σ' => σ'.arrs "alv" = ra.1 ∧ σ'.vars "agi" = ra.2)
    (alvSynth' n A₀) hle (alv_state_holds n A₀) (alvState_bound hnB h1B hA)
    (exists_bigStepB_of_hnRefine (alvSynth' n A₀) hle (alv_state_holds n A₀)
      (alv_bpre hnB h1B hA))
    (le_of_eq (ecash_alvTotal n)) ?_
  · exact hspec.post (by
      rintro σ σ' - ⟨ra, ⟨hlen', hz⟩, hread, hvar⟩
      exact ⟨ra.1, hread, hlen', hz⟩)
  · intro ra s' cr σ' hΦ hst hag
    have he : (alvFrame n ∗ (arrayAssn ×ₐ natAssn) ra ("alv", "agi") ∗
        alvHole n A₀ ∗ GC)
        = (alvFrame n ∗ arrayAssn ra.1 "alv" ∗ (natAssn ra.2 "agi" ∗ alvHole n A₀) ∗ GC) := by
      simp only [prodAssn]; ac_rfl
    have he' : (alvFrame n ∗ (arrayAssn ×ₐ natAssn) ra ("alv", "agi") ∗
        alvHole n A₀ ∗ GC)
        = (alvFrame n ∗ natAssn ra.2 "agi" ∗ (arrayAssn ra.1 "alv" ∗ alvHole n A₀) ∗ GC) := by
      simp only [prodAssn]; ac_rfl
    exact ⟨readout_arr (he ▸ hst) hag, readout_scalar (he' ▸ hst) hag⟩

/-- **The mask pass, exported.** Stated from any IMP+ environment that
holds the store — the shape `RamDriverAugment.alvSet_run` is consumed
in. -/
theorem alvCom_spec {B n : ℕ} (hnB : n < B) (h1B : 1 < B) :
    Lax13Proofs.Reasoning.Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "agi" = 0 ∧ σ.vars "one" = 1 ∧
        (∃ A₀, σ.arrs "alv" = A₀ ∧ A₀.length = n ∧ ∀ v ∈ A₀, v < B))
      (embed alvSynth_impl)
      (fun _ σ' => ∃ A : List ℕ, σ'.arrs "alv" = A ∧ A.length = n ∧ ∀ j, j < n → A[j]! = 1)
      (alvK n) := by
  intro σ hσ
  obtain ⟨hn, hi, hone, A₀, halv, hlen, hAB⟩ := hσ
  have hag : agree (alvState n A₀) σ := by
    refine Codegen.agree_ofPairs ?_ ?_
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      assumption
  exact (alv_spec_at A₀ hnB h1B hAB hlen) σ hag

theorem getElem!_arrOf {m i : ℕ} (f : ℕ → ℕ) (h : i < m) : (arrOf m f)[i]! = f i := by
  rw [getElem!_pos (arrOf m f) i (by simpa using h)]
  simp

theorem mem_arrOf_lt {m B : ℕ} {f : ℕ → ℕ} (h : ∀ z < m, f z < B) :
    ∀ w ∈ arrOf m f, w < B := by
  intro w hw
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hw
  exact h k (List.mem_range.1 hk)

/-- **The mask pass in the baseline's own shape.** `RamAugment.alvSet`
leaves `alv = arrOf n (fun _ => 1)`, which is the hypothesis
`RamElim.masked_of_all_alive` turns back into the fraternity graph. This
is that postcondition, at the tower's cost. -/
theorem alvCom_spec_arrOf {B n : ℕ} {M : ℕ → ℕ} (hnB : n < B) (h1B : 1 < B)
    (hM : ∀ i < n, M i < B) :
    Lax13Proofs.Reasoning.Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "agi" = 0 ∧ σ.vars "one" = 1 ∧
        σ.arrs "alv" = arrOf n M)
      (embed alvSynth_impl)
      (fun _ σ' => σ'.arrs "alv" = arrOf n (fun _ => 1))
      (alvK n) := by
  intro σ hσ
  obtain ⟨hn, hi, hone, halv⟩ := hσ
  obtain ⟨σ', hrun, A, hread, hAlen, hAval⟩ :=
    (alvCom_spec (B := B) (n := n) hnB h1B) σ
      ⟨hn, hi, hone, arrOf n M, halv, length_arrOf n M, mem_arrOf_lt hM⟩
  refine ⟨σ', hrun, ?_⟩
  show σ'.arrs "alv" = arrOf n (fun _ => 1)
  rw [hread]
  refine List.ext_getElem (by rw [length_arrOf, hAlen]) fun i h₁ h₂ => ?_
  have hi' : i < n := by rw [hAlen] at h₁; exact h₁
  rw [Lax13Proofs.Reasoning.Lib.getElem_arrOf, ← getElem!_pos A i h₁, hAval i hi']

end Export

/-! ## 7. The composition boundary, measured (T1)

Satellite 2A's finding — a synthesized engine fires as a *leaf*, but a
consumer that reads one component of its bound result tuple stalls in
`fri` — is the standing hazard for gluing this round's passes. This
section measures where the boundary actually is for **two passes of the
same round over the same array**, which is the shape the out-list build
has: `cntPass` leaves `ooff`, and `prefLoop` reads and rewrites it.

`#sepref_synth` reports and does not throw, so whatever it says is the
measurement and the build stands either way. -/

section Compose

set_option maxHeartbeats 400000 in
#sepref_synth (n : ℕ) (doff dtg ooff₀ ofl₀ : List ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ natAssn) (ooff₀, 0) ("ooff", "agi") ∗
      hnCtxt arrayAssn doff "doff" ∗ hnCtxt arrayAssn dtg "dtg" ∗
      hnCtxt arrayAssn ofl₀ "ofl" ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "agjo" ∗ junkCell "agip" ∗ junkCell "agend" ∗
      junkCell "agu" ∗ junkCell "agup" ∗ junkCell "agc" ∗
      junkCell "agb" ∗ junkCell "aga" ∗ junkCell "agt")
    _ _ ("ooff", "ofl", "agi") (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
    (NRest.bindT (cntPass n doff dtg (ooff₀, 0)) fun r => prefLoop n (r.1, ofl₀, 0))

/-! **What the probe reports** (F2, measured):

```
sepref: phase 'trans' (priority 80) failed.  sepref: no rule translates
  hnr_bind: applied, but a side condition stalled
    hnr_while: the rule's precondition conjuncts
      could not all be matched against the goal's
```

`hnr_bind` fires the counting pass — so a *synthesized two-loop pass is
usable as a leaf*, which is 2A's first report reconfirmed one scale up —
and then the prefix loop stalls, because its three-component state has
to be built out of `r.1`, a component of the counting pass's bound
result tuple, and the frame layer will not split a bound `prodAssn` in
the `fri` direction. `Sepref/Frame.lean`'s `conjunctsSplit` does this
split in the other direction (P7/D-ba).

The instance matters for the worklist: 2A's stall was *engine* against
*sweep* and could be read as a scale problem. This one is two flat-ish
passes over one `List ℕ` in one file, with no engine anywhere, and it is
the same rule. So the fix is confirmed to be the single `fri`
counterpart rule, and it is what the augmentation round needs to be
glued **inside** the tool rather than at `Spec` level. -/

end Compose

/-! ## 8. What is not derived here, and what it would cost

**`fratPass` (phase 2), the fraternity build.** Three nested loops — the
out-block of `i`, the in-block of each vertex it names, the stamped
emit — run twice per vertex (emit, then clear), plus the prefix pass
(derived, §3) between them. Two things price it:

* *Correctness.* The content is "a stamped walk emits each partner
  exactly once", which is `RamDriverAugment`'s `Emits`/`rowAcc`
  machinery. At the tower it is an invariant on the stamp *list* — the
  set of vertices whose stamp is one is exactly the set already
  counted — which is the same shape as `cntInv` here and needs no new
  tool. §1.2's twin is the program it would be proved about, and §1.4
  shows the stamp is load-bearing (the unstamped walk counts a
  two-witness pair twice).
* *Cost.* The inner scan is charged per slot of an in-block of a vertex
  the out-block names, so the pass's total is `∑_p indeg(OT p)` — the
  exchange. `bumpCnt`/`sum_bumpCnt` (§4.2) is that fact at the list
  layer, at the *other* array; the same two lemmas serve.

The tool risk is F1's: the fraternity emit has a guard
(`if stf[u] = 0`), i.e. exactly the two-armed branch 2B's stall points
at — but here both arms write the **inner** loop's state, as
`BfsQSynth.scanF'` does, not the outer's. That is the configuration
that already works, so the fraternity build is expected to translate;
it is the assembly (`asmPass`) whose branches write across levels.

**`elimCom` (phase 4).** Satellite 2B is deriving the engine. Composing
it here is F2: it will fire as a leaf (`hnr_bind` does), and the pass
that reads its output arrays will stall until the `fri` split exists.
Until then the round is a `Spec`-level fold, which is what
`RamDriverAugment.implements` already is.

**`asmPass` (phase 5).** The heaviest: two stamp arrays, three
enumerations, a rank comparison and a nested guard, with `AugPre`'s
`sta`/`std`/`ste` all live at once. Its correctness is
`RamAugment.inN_augOr_eq` — landed capital, cited, not re-provable
work — and its cost is the same exchange again
(`RamDriverAugment.asm_cost_le`). It is the pass to derive *after* the
`fri` rule exists, since it is the one that reads what the engine
wrote.

## 9. Telemetry

* **Synthesis wall clock**, warm build: the whole file elaborates in
  **≈13 s** with three `sepref_synth` invocations (mask ≈1 s, prefix
  ≈2 s, counting pass — two loops — ≈4 s) plus the two probes; the F2
  probe of §7 adds ≈50 s, since it re-runs the counting pass's own
  translate before stalling. No bespoke tactic work, no hand-written
  frame clause, no `LOOP_VARIANT`. All four `Com`s came out right on the
  first run, every scratch cell in the slot the program consumes it at.

* **Cost constants, computed** (`decide +kernel`, not tuned):

  | pass | tower | baseline (`RamDriverAugment`) | ratio |
  |---|---|---|---|
  | mask | `alvK n = 12·n + 4` | `11·n + 8` | 1.09 |
  | prefix | `prefK n = 30·n + 4` | `≈ 23·n + 8` | 1.30 |
  | count | `cntK n m = 24·n + 26·m + 4` | `21·m + 20·n + 8` | 1.24 |

  The prefix gap is R2C/D-b and nothing else. The count pass is charged
  in **two currencies**, one per vertex and one per *slot* — the
  touched-only discipline: `m` is `doff[n]`, the arcs, and no array is
  swept.

* **Bounds pass via `BRefine`: 0 `Ir.State` predicates authored.** Two
  loops bounded (mask, prefix). The prefix body — seven operations,
  three arrays, a triple loop state — has **two** side conditions, one
  per arithmetic creation site: the index `i+1` and the running sum
  `cumsum O₀ (i+1)`, the latter discharged from the abstract invariant's
  own word bound. That is the P0.2 prediction confirmed a third time at
  "≈1 per creation site". The counting pass's bounds pass is **not**
  done: it needs a `BRefine` rule for a nested `while` (the inner loop's
  assertion has to be framed inside the outer body), which no worked
  example has yet — §10, tool gap 3.

* **Refuted before proved.** `AugmentTwins` tests four computable twins
  against
  `RamAugment.Demo`'s own reported `mf = 2` and against
  `TgtCoupling`'s K₁,₄ slot count, with three pinned negative controls
  and the stamp shown to be load-bearing; §5 runs the three
  *synthesized* programs on the same data with three more pinned
  negative controls. The `omega`-through-`Ir.Val` trap did not fire
  (every side condition is on ℕ-typed abstract values); the
  junk-destination misfire did not fire (cells listed in consumption
  order, R2C/D-c).

* **Integration notes.** Cells written: `"agi"`, `"agj"`/`"agjo"`,
  `"agip"`, `"agend"`, `"agu"`, `"agup"`, `"agc"`, `"aga"`, `"agb"`,
  `"agt"` — all `"ag"`-prefixed and **digit-free** (P1/B-f). Cells read
  only: `"n"`, `"one"`. Arrays: `"alv"` (written), `"ooff"` (written),
  `"ofl"` (written), `"doff"`/`"dtg"` (read). The entry store is pinned
  at zero for every scratch cell (P7/D-bp) and the arrays' entries are
  words state-globally (P7/D-bo).

## 10. Tool gaps (feeding the worklist)

1. **No `sepref_brefine_rules` database** — each of the seven operation
   lemmas of §4b is `BRefine.perm … (by ac_rfl) … ∘ BRefine.frame`, the
   permutation the synthesis driver already computes, re-authored by
   hand (2A's gap 1, re-met at seven operations).
2. **No `BRefine` rule for junk cells** — `junkCell` is opened with
   `BRefine.pre_ex`, so the prefix loop's assertion carries its four
   scratch values in a four-tuple existential (`prefΓ`). 2A's gap 2.
3. **No `BRefine` rule for a nested loop** — new here. `BRefine.while`
   proves a loop at *its own* loop assertion; a loop that sits inside
   another body needs its assertion framed by the outer body's
   ownership and its exit re-opened, and no worked example does it. This
   is the only thing between §4's counting pass and its `Spec` export;
   the correctness and the cost are already proved (`cntPass_spec`).
4. **`fri` cannot split a bound tuple** — §7, F2, confirmed at its
   cheapest instance. 2A's gap 3, unchanged and now cheaper to
   reproduce.
5. **No name-generic synthesis** — the prefix pass is one abstract
   program used at three array pairs in the round, and each pair needs
   its own `sepref_synth` invocation because the array names are baked
   into the emitted `Com`. Mechanical, but three copies. -/

/-! ## 11. Axioms -/

/-- info: 'Lax3Proofs.Refine.AugmentSynth.alvCom_spec_arrOf' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms alvCom_spec_arrOf

/-- info: 'Lax3Proofs.Refine.AugmentSynth.cntPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms cntPass_spec

/-- info: 'Lax3Proofs.Refine.AugmentSynth.cntPassSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms cntPassSynth

/-- info: 'Lax3Proofs.Refine.AugmentSynth.prefSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms prefSynth

/-- info: 'Lax3Proofs.Refine.AugmentSynth.pref_brefine' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms pref_brefine

/-- info: 'Lax3Proofs.Refine.AugmentSynth.prefLoop_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms prefLoop_spec

end Lax3Proofs.Refine.AugmentSynth
