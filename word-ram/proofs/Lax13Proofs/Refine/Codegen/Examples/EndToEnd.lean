import Lax13Proofs.Refine.Codegen.Cash
import Lax13Proofs.Refine.Sepref.Examples.Acceptance

/-!
P5's acceptance: P4's two toy programs, landed at `ComputesInTime`.

The plan's P5 gate is "P4's toy programs land at `computesInTime`
mechanically". This file is that landing, for both of them, with nothing
between the synthesized `Ir.Com` and the machine that is not one of the
five components of the design record.

Per program the chain is

```
sepref_synth  ──▶  hnRefine Γ c Γ' d R (irWhileIT …)      [P4, imported]
abstract loop ──▶  irWhileIT … ≤ SPEC (· = twin) T        [§1 here]
bounds pass   ──▶  ∃ s' κ, Ir.BigStepB B c s₀ s' κ        [§3, ir_bound_vcg]
cashing       ──▶  Reasoning.Spec B (agree s₀) (embed c) … N   [Cash.lean]
harness       ──▶  Spec B (· = initEnv ext x) (whole) … K      [Harness.lean]
boundary      ──▶  Transfer.Solves ──▶ ComputesInTime           [Cash.lean]
```

## Judgment calls

**P5/D-ag — the loop's constant cells are initialised by the harness,
not by the IR.** Both synthesized programs need cells the marshalling
prelude leaves at zero: filter-count owns `"one" ↦ᵥ 1`, reverse owns
that and `"j" ↦ᵥ |ys| - 1`. The prelude reads *input*, so somebody has
to write them. Doing it with IR `const` ops would mean composing another
`hnRefine` in front of the synthesized one — a synthesis problem, not a
codegen one — so it is done with two IMP+ assignments instead,
`Spec.assign`, priced at `2` and `4`. The constants are marshalling: an
`Ir.Com` that owns a cell holding `1` is a program whose caller supplies
it, exactly as `Γ` says.

**P5/D-ah — the abstract cost is an *exact* fuel recursion, not a
closed form.** `fcTotal`/`rvTotal` are defined by recursion on the
iteration budget and the loop lemma is `≤ SPEC (· = twin) (fun _ =>
total m)`; `ecash_fcTotal` then evaluates the price to `20·m + 4` in one
induction. Doing it the other way — a closed-form `ECost` and a
`nsmul` — makes the loop induction carry an arithmetic side condition at
every step for no gain.

**P5/D-ai — the value function of the `ComputesInTime` statement is the
program's own executable twin.** For filter-count that is `fcCount`,
which §5 `#guard`s equal to `(xs.filter (· < t)).length` — an
independent decider — on every sample. For reverse it is `rvOutFn`,
`#guard`ed equal to `List.reverse`. Proving those equalities is
functional correctness of the *examples*, which P4's own backlog (i)
already records as out of scope: P4's gate is the synthesis and P5's is
the codegen, and neither is a statement about `List.reverse`. The
backlog entry is carried forward at the end of this file.

**P5/D-aj — the value bound is `B x = x.sum + 2` for both programs.**
`Solves` wants a bound as a function of the input. Every value either
program creates is an entry of the array, an index into it, a count of
its entries, or the threshold — all bounded by the sum of the input,
which is also the cheapest bound to *state*. It is not tight and does
not need to be: `Transfer`'s word-length hypothesis is
`L.span (B x) ≤ 2 ^ w`, and a caller who wants `w = O(log n)` writes a
sharper `B` and re-runs §3 with the same invariants.
-/

namespace Lax13Proofs.Refine.Codegen

open Lax13Proofs.Refine.Ir Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Sepref.Acceptance
open Lax13Proofs.Codegen Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax13Proofs.Imp Lax13Proofs.Compile

namespace EndToEnd

/-! ## 0. The two currencies that `Cash.lean` states at `binopCurrency` -/

theorem ecash_unit_add : ecash (irUnit Currency.add) = 4 := ecash_irUnit_binop .add
theorem ecash_unit_sub : ecash (irUnit Currency.sub) = 4 := ecash_irUnit_binop .sub

/-! ## 1. Filter-count: the abstract loop's value and cost

`irWhileIT` unfolds to a `consume` of its body and a recursive call
(`IrOps.lean`'s `irWhileIT_of_true`), the body is a `consume` of a
`returnT` (`Acceptance.lean`'s `fcF_eq`), and `bindT_unit` collapses the
two. What comes out is one `SPEC` per fuel budget. -/

/-- The price of `m` turns of filter-count's loop, plus the last test. -/
noncomputable def fcTotal : ℕ → ECost
  | 0 => irUnit Currency.«while»
  | m + 1 => irUnit Currency.«while» + (fcCost + fcTotal m)

theorem ecash_fcTotal (m : ℕ) : ecash (fcTotal m) = 20 * m + 4 := by
  induction m with
  | zero => simp [fcTotal]
  | succ m ih =>
      rw [fcTotal, ecash_add, ecash_add, ih, fcCost]
      simp only [ecash_add, ecash_irUnit_aget, ecash_irUnit_ite, ecash_unit_add,
        ecash_irUnit_skip, ecash_irUnit_while]
      push_cast
      ring

/-- Adding a turn only costs more. -/
theorem fcTotal_le_succ (m : ℕ) : irUnit Currency.«while» ≤ fcTotal (m + 1) := by
  rw [fcTotal]
  exact ACost.le_def.2 fun k => by rw [ACost.toFun_add]; exact le_self_add

/-- **The abstract loop.** With enough fuel, the loop computes its twin
and costs `fcTotal` of the fuel. -/
theorem fc_loop_le (ys : List ℕ) (t : ℕ) : ∀ (m : ℕ) (s : ℕ × ℕ), ys.length - s.1 ≤ m →
    irWhileIT fcI (fcBf ys) (fcF ys t) s ≤
      NRest.spec (· = fcRun ys t m s) (fun _ => fcTotal m) := by
  intro m
  induction m with
  | zero =>
      intro s hle
      have hb : fcBf ys s = false := by
        simp only [fcBf, decide_eq_false_iff_not]
        omega
      rw [irWhileIT_of_false trivial hb]
      exact le_spec_of_consume_returnT s _
  | succ m ih =>
      intro s hle
      by_cases hb : fcBf ys s = true
      · have hk : s.1 < ys.length := by simpa [fcBf] using hb
        have hstep : ys.length - (fcStep ys t s).1 ≤ m := by
          simp only [fcStep]
          omega
        rw [irWhileIT_of_true trivial hb, fcF_eq ys t s hk, bindT_unit, NRest.consume_consume,
          show fcRun ys t (m + 1) s = fcRun ys t m (fcStep ys t s) by rw [fcRun, if_pos hb]]
        refine le_trans (NRest.consume_mono (ih (fcStep ys t s) hstep) le_rfl) ?_
        rw [consume_spec]
        exact spec_mono_cost _ (le_of_eq (by rw [fcTotal]; exact add_assoc _ _ _))
      · rw [Bool.not_eq_true] at hb
        rw [irWhileIT_of_false trivial hb, show fcRun ys t (m + 1) s = s by
          rw [fcRun, if_neg (by simp [hb])]]
        exact le_trans (le_spec_of_consume_returnT s _)
          (spec_mono_cost _ (fcTotal_le_succ m))

/-- The count never exceeds the fuel plus what it started at. -/
theorem fcRun_snd_le (ys : List ℕ) (t : ℕ) : ∀ (m : ℕ) (s : ℕ × ℕ),
    (fcRun ys t m s).2 ≤ s.2 + m := by
  intro m
  induction m with
  | zero => intro s; simp [fcRun]
  | succ m ih =>
      intro s
      rw [fcRun]
      split
      · exact le_trans (ih (fcStep ys t s)) (by simp only [fcStep]; split <;> omega)
      · omega

/-- What the whole program computes. -/
def fcCountOf (ys : List ℕ) (t : ℕ) : ℕ := (fcRun ys t ys.length (0, 0)).2

theorem fcCountOf_le (ys : List ℕ) (t : ℕ) : fcCountOf ys t ≤ ys.length := by
  simpa using fcRun_snd_le ys t ys.length (0, 0)

/-! ## 2. Filter-count: the initial IR state

`hnRefine` is used at the frame `fcHole`, the `EXACT` resource holding
every cell of `fcState` that `fcPre` does not own — which is none of
them, but writing it as an `EXACT` is what lets the eight-conjunct
assertion be checked by `rfl` rather than by extensionality over the
name space (`Ir/Triples.lean`'s `rtPre_holds` does the same). -/

/-- The IR state `fcPre` describes: the loop's two cells, the scratch
cell, the array, the threshold, the length, and the two constants. -/
def fcState (ys : List ℕ) (t : ℕ) : Ir.State :=
  Ir.State.ofPairs [("k", 0), ("acc", 0), ("v", 0), ("t", t), ("n", ys.length),
    ("one", 1), ("zero", 0)] [("A", ys)]

/-- The frame: everything `fcPre` leaves. -/
def fcHole (ys : List ℕ) (t : ℕ) : Assn :=
  EXACT (((((((((vcells (fcState ys t)).erase "k").erase "acc").erase "v").erase "t").erase
    "n").erase "one").erase "zero", (acells (fcState ys t)).erase "A",
    hcells (fcState ys t)), 0)

theorem fc_state_holds (ys : List ℕ) (t : ℕ) :
    irSTATE (fcPre ys t ∗ fcHole ys t) (fcState ys t, 0) := by
  show (fcPre ys t ∗ fcHole ys t)
    ((vcells (fcState ys t), acells (fcState ys t), hcells (fcState ys t)), 0)
  simp only [fcPre, hnCtxt, prod_assn_pair_conv, natAssn_def, arrayAssn_def, sepConj_assoc]
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩⟩
  rw [junkCell_def, sepEx_sepConj]
  refine ⟨0, Ir.ptoVar_sepConj_iff.2 ⟨rfl, Ir.ptoArr_sepConj_iff.2 ⟨rfl,
    Ir.ptoVar_sepConj_iff.2 ⟨rfl, Ir.ptoVar_sepConj_iff.2 ⟨rfl,
      Ir.ptoVar_sepConj_iff.2 ⟨rfl, Ir.ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩

/-! ## 3. Filter-count: the bounds pass

The whole per-program annotation is `fcInv` and `fcVar` below — eleven
lines. Everything else is `ir_bound_vcg` and the arithmetic the
invariant already carries. -/

/-- The bound the program runs under, as a function of the input. -/
def fcB (x : List ℕ) : ℕ := x.sum + 2

/-- The loop invariant of the bounds pass. -/
def fcInv (ys : List ℕ) (t B : ℕ) (s : Ir.State) : Prop :=
  (∃ k acc : ℕ, s.vars "k" = some k ∧ s.vars "acc" = some acc ∧ acc ≤ k ∧ k ≤ ys.length) ∧
    (∃ w : ℕ, s.vars "v" = some w ∧ w < B) ∧ s.arrs "A" = some ys ∧
    s.vars "t" = some t ∧ s.vars "n" = some ys.length ∧
    s.vars "one" = some 1 ∧ s.vars "zero" = some 0

/-- The variant: the entries still to scan. -/
def fcVar (ys : List ℕ) (s : Ir.State) : ℕ := ys.length - (s.vars "k").getD 0

/-- The obligations the bound places on `B`, collected. -/
structure FcBounds (ys : List ℕ) (t B : ℕ) : Prop where
  /-- The length, with room for one more. -/
  len : ys.length + 1 < B
  /-- The threshold. -/
  thr : t < B
  /-- Every entry. -/
  ent : ∀ v ∈ ys, v < B

theorem FcBounds.one {ys t B} (h : FcBounds ys t B) : 1 < B := by
  have := h.len; omega

theorem fc_guard {ys : List ℕ} {t B : ℕ} (hB : FcBounds ys t B) {s : Ir.State}
    (h : fcInv ys t B s) {k : ℕ} (hk : s.vars "k" = some k) (hkle : k ≤ ys.length) :
    (Cond.lt (.cell "k") (.cell "n")).evalB B s = some (decide (k < ys.length)) := by
  have hkB : k < B := by have := hB.len; omega
  have hnB : ys.length < B := by have := hB.len; omega
  exact Cond.evalB_lt_of (Operand.evalB_of_eval (u := .cell "k") (by simpa using hk) hkB)
    (Operand.evalB_of_eval (u := .cell "n") (by simpa using h.2.2.2.2.1) hnB)

/-- **The bounds witness.** The loop runs, under the bound, from the
initial state. -/
theorem fc_runs (ys : List ℕ) (t B : ℕ) (hB : FcBounds ys t B) :
    ∃ s' κ, Ir.BigStepB B fcLoop_impl (fcState ys t) s' κ := by
  have hinit : fcInv ys t B (fcState ys t) :=
    ⟨⟨0, 0, rfl, rfl, le_rfl, Nat.zero_le _⟩, ⟨0, rfl, by have := hB.len; omega⟩,
      rfl, rfl, rfl, rfl, rfl⟩
  refine Runs.exists (Q := fun s' => fcInv ys t B s' ∧ _)
    (runs_while (fcInv ys t B) (fcVar ys) ?_ ?_ hinit)
  · rintro s ⟨⟨k, acc, hk, hacc, hak, hkn⟩, hv, hA, ht, hn, hone, hzero⟩
    exact ⟨_, fc_guard hB ⟨⟨k, acc, hk, hacc, hak, hkn⟩, hv, hA, ht, hn, hone, hzero⟩ hk hkn⟩
  · rintro s ⟨⟨k, acc, hk, hacc, hak, hkn⟩, ⟨w, hw, hwB⟩, hA, ht, hn, hone, hzero⟩ hb
    have hI : fcInv ys t B s := ⟨⟨k, acc, hk, hacc, hak, hkn⟩, ⟨w, hw, hwB⟩, hA, ht, hn,
      hone, hzero⟩
    rw [fc_guard hB hI hk hkn] at hb
    have hklt : k < ys.length := by simpa using hb
    -- the entry the body reads
    obtain ⟨e, he⟩ : ∃ e, ys[k]? = some e := ⟨ys[k], List.getElem?_eq_getElem hklt⟩
    have heB : e < B := hB.ent e (List.mem_of_getElem? he)
    have htB : t < B := hB.thr
    have honeB : 1 < B := hB.one
    have hkB : k + 1 < B := by have := hB.len; omega
    have haccB : acc + 1 < B := by have := hB.len; omega
    have haccB0 : acc + 0 < B := by have := hB.len; omega
    ir_bound_vcg
    refine ⟨(by rw [hw]; simp), k, ys, e, hk, hA, he, ?_⟩
    -- the branch
    have hguard : (Cond.lt (Operand.cell "v") (Operand.cell "t")).evalB B
        (s.setVar "v" e) = some (decide (e < t)) :=
      Cond.evalB_lt_of (Operand.evalB_of_eval (u := .cell "v") (by simp) heB)
        (Operand.evalB_of_eval (u := .cell "t") (by simpa using ht) htB)
    by_cases hbr : e < t
    · refine Or.inl ⟨by rw [hguard, decide_eq_true hbr], ?_, acc, 1, (by simp [hacc]),
        (by simp [hone]), (by simpa using haccB), ?_, k, 1, (by simp [hk]), (by simp [hone]),
        (by simpa using hkB), ?_⟩
      · rw [hacc]; simp
      · rw [hk]; simp
      · refine ⟨⟨⟨k + 1, acc + 1, (by simp), (by simp), (by omega), (by omega)⟩,
          ⟨e, (by simp), heB⟩, (by simp [hA]), (by simpa using ht), (by simpa using hn),
          (by simpa using hone), (by simpa using hzero)⟩, ?_⟩
        simp only [fcVar, Ir.State.vars_setVar, hk, if_true, Option.getD_some]
        omega
    · refine Or.inr ⟨by rw [hguard, decide_eq_false hbr], ?_, acc, 0, (by simp [hacc]),
        (by simp [hzero]), (by simpa using haccB0), ?_, k, 1, (by simp [hk]), (by simp [hone]),
        (by simpa using hkB), ?_⟩
      · rw [hacc]; simp
      · rw [hk]; simp
      · refine ⟨⟨⟨k + 1, acc + 0, (by simp), (by simp), (by omega), (by omega)⟩,
          ⟨e, (by simp), heB⟩, (by simp [hA]), (by simpa using ht), (by simpa using hn),
          (by simpa using hone), (by simpa using hzero)⟩, ?_⟩
        simp only [fcVar, Ir.State.vars_setVar, hk, if_true, Option.getD_some]
        omega

/-! ## 4. Filter-count: the cashing, the harness and the boundary -/

/-- The declared array length, per input. -/
def fcExt (ys : List ℕ) : String → ℕ := fun b => if b = "A" then ys.length else 0

/-- The body the harness wraps: the constant `"one"`, then the
synthesized loop (judgment call P5/D-ag). -/
def fcBody : Imp.Com := .seq (.assign "one" (.lit 1)) (embed fcLoop_impl)

/-- The whole program: prelude, body, epilogue. -/
def fcProgram : Imp.Com :=
  .seq (readScalarsThenArr ["t", "n"] "A" "cnt" "n" "tp") (.seq fcBody (writeScalar "acc"))

/-- Nine scalars, one array, two temporaries. -/
def fcLayout : Layout := ⟨["t", "n", "cnt", "tp", "k", "acc", "v", "one", "zero"], ["A"], 2⟩

/-- The admissible inputs: a threshold, a length, and that many
entries. -/
def fcD : Set (List ℕ) := {x | ∃ (t : ℕ) (ys : List ℕ), x = [t, ys.length] ++ ys}

/-- The function computed (judgment call P5/D-ai). -/
def fcOut (x : List ℕ) : List ℕ := [fcCountOf (x.drop 2) x.headI]

/-- The cost: `2 + 12·n` marshalling in, `20·n + 6` body, `11`
epilogue and glue. -/
def fcK (x : List ℕ) : ℕ := 32 * (x.drop 2).length + 17

theorem fcBounds_holds (ys : List ℕ) (t : ℕ) : FcBounds ys t (fcB ([t, ys.length] ++ ys)) where
  len := by
    simp only [fcB, List.sum_append, List.sum_cons, List.sum_nil]
    omega
  thr := by
    simp only [fcB, List.sum_append, List.sum_cons, List.sum_nil]
    omega
  ent := by
    intro v hv
    have := List.single_le_sum (l := ys) (fun _ _ => Nat.zero_le _) v hv
    simp only [fcB, List.sum_append, List.sum_cons, List.sum_nil]
    omega

theorem fc_stateBound (ys : List ℕ) (t B : ℕ) (hb : FcBounds ys t B) :
    Ir.StateBound B (fcState ys t) := by
  refine stateBound_ofPairs ?_ ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    have h1 := hb.len
    have h2 := hb.thr
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact hb.ent

/-- **The cashing step**, at filter-count: the synthesized loop, cashed
into a `Reasoning.Spec` about the embedded program. -/
theorem fc_loop_spec (ys : List ℕ) (t : ℕ) :
    Reasoning.Spec (fcB ([t, ys.length] ++ ys)) (agree (fcState ys t)) (embed fcLoop_impl)
      (fun _ σ' => σ'.vars "acc" = fcCountOf ys t) (20 * ys.length + 4) := by
  have hspec := spec_of_hnRefine (Φ := (· = fcRun ys t ys.length (0, 0)))
    (Q := fun ra σ' => σ'.vars "acc" = ra.2)
    (fcLoop' ys t) (fc_loop_le ys t ys.length (0, 0) (by simp))
    (fc_state_holds ys t) (fc_stateBound ys t _ (fcBounds_holds ys t))
    (fc_runs ys t _ (fcBounds_holds ys t))
    (by rw [ecash_fcTotal]; exact le_rfl)
    ?_
  · exact hspec.post (by
      rintro σ σ' - ⟨ra, rfl, hq⟩
      exact hq)
  · intro ra s' cr σ' _ h hag
    have he : (fcFrame ys t ∗ (natAssn ×ₐ natAssn) ra ("k", "acc") ∗ fcHole ys t ∗ GC)
        = ("acc" ↦ᵥ ra.2) ∗ (fcFrame ys t ∗ (("k" ↦ᵥ ra.1) ∗ (fcHole ys t ∗ GC))) := by
      simp only [prodAssn, natAssn_def]
      ac_rfl
    rw [he] at h
    exact hag.var (Ir.ptoVar_vars h)

/-- The body's specification, against the marshal descriptor. -/
theorem fc_body_spec (ys : List ℕ) (t : ℕ) :
    Reasoning.Spec (fcB ([t, ys.length] ++ ys))
      (ScalarsArrIn (fcExt ys) ["t", "n"] "A" "cnt" "tp" [t, ys.length] ys) fcBody
      (fun _ σ' => σ'.vars "acc" = fcCountOf ys t) (20 * ys.length + 6) := by
  have hone : Reasoning.Spec (fcB ([t, ys.length] ++ ys))
      (ScalarsArrIn (fcExt ys) ["t", "n"] "A" "cnt" "tp" [t, ys.length] ys)
      (.assign "one" (.lit 1)) (fun σ σ' => σ' = σ.setVar "one" 1) 2 := by
    refine (Reasoning.Spec.assign (f := fun _ => 1) (x := "one") (e := .lit 1) ?_).mono (by simp)
    intro σ _
    exact Reasoning.evalB_lit (by have := (fcBounds_holds ys t).len; omega)
  refine (Reasoning.Spec.seq hone (fc_loop_spec ys t) ?_ ?_).mono (by omega)
  · intro σ σ' hσ hq
    subst hq
    refine agree_ofPairs ?_ ?_
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa using hσ.zero "k" (by simp) (by decide) (by decide)
      · simpa using hσ.zero "acc" (by simp) (by decide) (by decide)
      · simpa using hσ.zero "v" (by simp) (by decide) (by decide)
      · simpa using hσ.cells ("t", t) (by simp)
      · simpa using hσ.cells ("n", ys.length) (by simp)
      · simp
      · simpa using hσ.zero "zero" (by simp) (by decide) (by decide)
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      simpa using hσ.arr
  · intro σ σ' σ'' _ _ hq
    exact hq

/-- **The program's specification at `initEnv`.** -/
theorem fc_program_spec (ys : List ℕ) (t : ℕ) :
    Reasoning.Spec (fcB ([t, ys.length] ++ ys))
      (fun σ => σ = initEnv (fcExt ys) ([t, ys.length] ++ ys)) fcProgram
      (fun _ σ' => σ'.out = [fcCountOf ys t]) (32 * ys.length + 17) := by
  have hb := fcBounds_holds ys t
  have hnB : ys.length < fcB ([t, ys.length] ++ ys) := by have := hb.len; omega
  have hres : fcCountOf ys t < fcB ([t, ys.length] ++ ys) := by
    have := fcCountOf_le ys t; have := hb.len; omega
  refine (Lax13Proofs.Codegen.marshal_scalarsArr_scalar _ (fcExt ys) ["t", "n"] "A" "cnt" "n"
    "tp" "acc" [t, ys.length] ys fcBody (20 * ys.length + 6) (fcCountOf ys t)
    (by simp) rfl (by simp) (by simp) (by simp) (by decide) (by decide) (by decide)
    (by simp [fcExt]) hnB hb.ent (by simp [fcBody, Imp.Com.NoWrite, noWrite_embed]) hres
    (fc_body_spec ys t)).mono (by simp only [List.length_cons, List.length_nil]; omega)

theorem fcProgram_ok : Compile.Com.Ok fcLayout fcProgram := by
  simp [fcProgram, fcBody, readScalarsThenArr, readArr, writeScalar,
    Lax13Proofs.Reasoning.Lib.Fill.put, fcLayout, Compile.Com.Ok, Compile.Cond.Ok,
    Compile.condExpr, Compile.Expr.Ok, fcLoop_impl, embed, embedCond, embedOperand]

/-- **The boundary.** -/
theorem fc_solves : Transfer.Solves fcLayout fcProgram fcD fcOut fcB fcK := by
  refine solves_of_spec fcProgram_ok ?_ ?_
  · rintro x ⟨t, ys, rfl⟩ v hv
    have hs : ∀ v ∈ ys, v ≤ ys.sum := fun v hv =>
      List.single_le_sum (fun _ _ => Nat.zero_le _) v hv
    simp only [fcB, List.sum_append, List.sum_cons, List.sum_nil]
    simp only [List.cons_append, List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · omega
    · omega
    · have := hs v hv; omega
  · rintro x ⟨t, ys, rfl⟩
    refine ⟨fcExt ys, ?_⟩
    have h := fc_program_spec ys t
    have hout : fcOut ([t, ys.length] ++ ys) = [fcCountOf ys t] := by
      simp [fcOut]
    have hK : fcK ([t, ys.length] ++ ys) = 32 * ys.length + 17 := by simp [fcK]
    rw [hout, hK]
    exact h

/-- **The P5 gate for filter-count**: the compiled machine program
computes the count in `L.const · (32·n + 17)` steps. -/
theorem fc_computesInTime (w : ℕ) (hfit : ∀ x ∈ fcD, fcLayout.FitsWords (fcB x) w) :
    Lax13.RamComputes.ComputesInTime w (compileProgram fcLayout fcProgram) fcD fcOut
      (fun x => fcLayout.const * fcK x) :=
  fc_solves.computesInTime hfit

/-! ## 5. In-place reverse: the abstract loop -/

/-- The twin of reverse's loop, at a fuel budget. -/
def rvIter : ℕ → (ℕ × ℕ × List ℕ) → ℕ × ℕ × List ℕ
  | 0, s => s
  | m + 1, s => if rvBf s then rvIter m (rvStep s) else s

theorem rvIter_length : ∀ (m : ℕ) (s : ℕ × ℕ × List ℕ),
    (rvIter m s).2.2.length = s.2.2.length := by
  intro m
  induction m with
  | zero => intro s; rfl
  | succ m ih =>
      intro s
      rw [rvIter]
      split
      · rw [ih (rvStep s)]; simp [rvStep]
      · rfl

/-- The price of `m` turns of reverse's loop, plus the last test. -/
noncomputable def rvTotal : ℕ → ECost
  | 0 => irUnit Currency.«while»
  | m + 1 => irUnit Currency.«while» + (rvCost + rvTotal m)

theorem ecash_rvTotal (m : ℕ) : ecash (rvTotal m) = 26 * m + 4 := by
  induction m with
  | zero => simp [rvTotal]
  | succ m ih =>
      rw [rvTotal, ecash_add, ecash_add, ih, rvCost]
      simp only [ecash_add, ecash_irUnit_aget, ecash_irUnit_aset, ecash_unit_add,
        ecash_unit_sub, ecash_irUnit_skip, ecash_irUnit_while]
      push_cast
      ring

theorem rvTotal_le_succ (m : ℕ) : irUnit Currency.«while» ≤ rvTotal (m + 1) := by
  rw [rvTotal]
  exact ACost.le_def.2 fun k => by rw [ACost.toFun_add]; exact le_self_add

/-- The abstract invariant survives a turn. -/
theorem rvI_step {s : ℕ × ℕ × List ℕ} (hI : rvI s) (hb : rvBf s = true) : rvI (rvStep s) := by
  obtain ⟨h1, h2⟩ := rv_bounds hI hb
  intro _
  simp only [rvStep, List.length_set]
  omega

/-- …and the variant decreases. -/
theorem rvV_step {s : ℕ × ℕ × List ℕ} (hb : rvBf s = true) : rvV (rvStep s) < rvV s := by
  have hlt : s.1 < s.2.1 := by simpa [rvBf] using hb
  simp only [rvV, rvStep]
  omega

/-- **The abstract loop**, reverse. -/
theorem rv_loop_le : ∀ (m : ℕ) (s : ℕ × ℕ × List ℕ), rvI s → rvV s ≤ m →
    irWhileIT rvI rvBf rvF s ≤ NRest.spec (· = rvIter m s) (fun _ => rvTotal m) := by
  intro m
  induction m with
  | zero =>
      intro s hI hle
      have hb : rvBf s = false := by
        simp only [rvBf, decide_eq_false_iff_not]
        simp only [rvV] at hle
        omega
      rw [irWhileIT_of_false hI hb]
      exact le_spec_of_consume_returnT s _
  | succ m ih =>
      intro s hI hle
      by_cases hb : rvBf s = true
      · obtain ⟨h1, h2⟩ := rv_bounds hI hb
        have hstep : rvV (rvStep s) ≤ m := by have := rvV_step hb; omega
        rw [irWhileIT_of_true hI hb, rvF_eq s h1 h2, bindT_unit, NRest.consume_consume,
          show rvIter (m + 1) s = rvIter m (rvStep s) by rw [rvIter, if_pos hb]]
        refine le_trans (NRest.consume_mono (ih (rvStep s) (rvI_step hI hb) hstep) le_rfl) ?_
        rw [consume_spec]
        exact spec_mono_cost _ (le_of_eq (by rw [rvTotal]; exact add_assoc _ _ _))
      · rw [Bool.not_eq_true] at hb
        rw [irWhileIT_of_false hI hb, show rvIter (m + 1) s = s by
          rw [rvIter, if_neg (by simp [hb])]]
        exact le_trans (le_spec_of_consume_returnT s _)
          (spec_mono_cost _ (rvTotal_le_succ m))

/-- What the whole program computes (judgment call P5/D-ai). -/
def rvOutFn (ys : List ℕ) : List ℕ := (rvIter (ys.length - 1) (0, ys.length - 1, ys)).2.2

theorem rvOutFn_length (ys : List ℕ) : (rvOutFn ys).length = ys.length := by
  simp [rvOutFn, rvIter_length]

theorem rv_init_inv (ys : List ℕ) : rvI (0, ys.length - 1, ys) := by
  intro h
  simp only at h ⊢
  omega

/-! ## 6. In-place reverse: the initial IR state -/

/-- The IR state `rvPre` describes. -/
def rvState (ys : List ℕ) : Ir.State :=
  Ir.State.ofPairs [("i", 0), ("j", ys.length - 1), ("t1", 0), ("t2", 0), ("one", 1)]
    [("A", ys)]

/-- The frame. -/
def rvHole (ys : List ℕ) : Assn :=
  EXACT (((((((vcells (rvState ys)).erase "i").erase "j").erase "t1").erase "t2").erase "one",
    (acells (rvState ys)).erase "A", hcells (rvState ys)), 0)

theorem rv_state_holds (ys : List ℕ) :
    irSTATE (rvPre ys ∗ rvHole ys) (rvState ys, 0) := by
  have hrw : rvPre ys ∗ rvHole ys = (("i" ↦ᵥ 0) ∗ (("j" ↦ᵥ (ys.length - 1)) ∗ (("A" ↦ₐ ys) ∗
      (junkCell "t1" ∗ (junkCell "t2" ∗ (("one" ↦ᵥ 1) ∗ rvHole ys)))))) := by
    simp only [rvPre, hnCtxt, prod_assn_pair_conv, natAssn_def, arrayAssn_def]
    ac_rfl
  rw [hrw]
  refine start_entailsE (P := ("i" ↦ᵥ 0) ∗ (("j" ↦ᵥ (ys.length - 1)) ∗ (("A" ↦ₐ ys) ∗
      (("t1" ↦ᵥ 0) ∗ (("t2" ↦ᵥ 0) ∗ (("one" ↦ᵥ 1) ∗ rvHole ys)))))) ?_ ?_
  · exact Ir.ptoVar_sepConj_iff.2 ⟨rfl, Ir.ptoVar_sepConj_iff.2 ⟨rfl,
      Ir.ptoArr_sepConj_iff.2 ⟨rfl, Ir.ptoVar_sepConj_iff.2 ⟨rfl,
        Ir.ptoVar_sepConj_iff.2 ⟨rfl, Ir.ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩
  · exact conj_entails_mono (entails_refl _) (conj_entails_mono (entails_refl _)
      (conj_entails_mono (entails_refl _) (conj_entails_mono
        (natAssn_entails_junkCell 0 "t1") (conj_entails_mono
          (natAssn_entails_junkCell 0 "t2") (entails_refl _)))))

/-! ## 7. In-place reverse: the bounds pass -/

/-- The obligations the bound places on `B`. -/
structure RvBounds (ys : List ℕ) (B : ℕ) : Prop where
  /-- The length, with room for one more index. -/
  len : ys.length + 1 < B
  /-- Every entry. -/
  ent : ∀ v ∈ ys, v < B

/-- The loop invariant of the bounds pass. -/
def rvInv (ys : List ℕ) (B : ℕ) (s : Ir.State) : Prop :=
  (∃ i j : ℕ, s.vars "i" = some i ∧ s.vars "j" = some j ∧ i ≤ ys.length ∧ j ≤ ys.length ∧
      (i < j → j < ys.length)) ∧
    (∃ zs : List ℕ, s.arrs "A" = some zs ∧ zs.length = ys.length ∧ ∀ v ∈ zs, v < B) ∧
    (∃ a : ℕ, s.vars "t1" = some a ∧ a < B) ∧ (∃ b : ℕ, s.vars "t2" = some b ∧ b < B) ∧
    s.vars "one" = some 1

/-- The variant. -/
def rvVar (s : Ir.State) : ℕ := (s.vars "j").getD 0 - (s.vars "i").getD 0

theorem rv_guard {ys : List ℕ} {B : ℕ} (hB : RvBounds ys B) {s : Ir.State} {i j : ℕ}
    (hi : s.vars "i" = some i) (hj : s.vars "j" = some j) (hile : i ≤ ys.length)
    (hjle : j ≤ ys.length) :
    (Cond.lt (.cell "i") (.cell "j")).evalB B s = some (decide (i < j)) := by
  have hiB : i < B := by have := hB.len; omega
  have hjB : j < B := by have := hB.len; omega
  exact Cond.evalB_lt_of (Operand.evalB_of_eval (u := .cell "i") (by simpa using hi) hiB)
    (Operand.evalB_of_eval (u := .cell "j") (by simpa using hj) hjB)

/-- **The bounds witness** for reverse. -/
theorem rv_runs (ys : List ℕ) (B : ℕ) (hB : RvBounds ys B) :
    ∃ s' κ, Ir.BigStepB B rvLoop_impl (rvState ys) s' κ := by
  have h1B : 1 < B := by have := hB.len; omega
  have hinit : rvInv ys B (rvState ys) :=
    ⟨⟨0, ys.length - 1, rfl, rfl, Nat.zero_le _, by omega, by omega⟩,
      ⟨ys, rfl, rfl, hB.ent⟩, ⟨0, rfl, by omega⟩, ⟨0, rfl, by omega⟩, rfl⟩
  refine Runs.exists (Q := fun s' => rvInv ys B s' ∧ _)
    (runs_while (rvInv ys B) rvVar ?_ ?_ hinit)
  · rintro s ⟨⟨i, j, hi, hj, hile, hjle, hij⟩, -, -, -, -⟩
    exact ⟨_, rv_guard hB hi hj hile hjle⟩
  · rintro s ⟨⟨i, j, hi, hj, hile, hjle, hij⟩, ⟨zs, hA, hzl, hzB⟩, ⟨a0, ha0, -⟩,
      ⟨b0, hb0, -⟩, hone⟩ hb
    rw [rv_guard hB hi hj hile hjle] at hb
    have hlt : i < j := by simpa using hb
    have hjlen : j < zs.length := by rw [hzl]; exact hij hlt
    have hilen : i < zs.length := lt_trans hlt hjlen
    obtain ⟨a, ha⟩ : ∃ a, zs[i]? = some a := ⟨zs[i], List.getElem?_eq_getElem hilen⟩
    obtain ⟨b, hbb⟩ : ∃ b, zs[j]? = some b := ⟨zs[j], List.getElem?_eq_getElem hjlen⟩
    have haB : a < B := hzB a (List.mem_of_getElem? ha)
    have hbB : b < B := hzB b (List.mem_of_getElem? hbb)
    have hiB : i + 1 < B := by have := hB.len; omega
    have hset : ∀ v ∈ (zs.set i b).set j a, v < B := by
      intro v hv
      rcases List.mem_or_eq_of_mem_set hv with hv' | rfl
      · rcases List.mem_or_eq_of_mem_set hv' with hv'' | rfl
        · exact hzB v hv''
        · exact hbB
      · exact haB
    ir_bound_vcg
    refine ⟨(by rw [ha0]; simp), i, zs, a, hi, hA, ha, ?_⟩
    refine ⟨(by simp [hb0]), j, zs, b, (by simp [hj]), (by simpa using hA), hbb, ?_⟩
    refine ⟨i, b, zs, (by simp [hi]), (by simp), (by simpa using hA), hilen, ?_⟩
    refine ⟨j, a, zs.set i b, (by simp [hj]), (by simp), (by simp),
      (by simpa using hjlen), ?_⟩
    refine ⟨(by simp [hi]), i, 1, (by simp [hi]), (by simp [hone]), (by simpa using hiB), ?_⟩
    refine ⟨(by simp [hj]), j, 1, (by simp [hj]), (by simp [hone]),
      apply_sub_lt (show j < B by have := hB.len; omega), ?_⟩
    refine ⟨⟨⟨i + 1, j - 1, (by simp), (by simp), (by omega), (by omega), (by omega)⟩,
      ⟨(zs.set i b).set j a, (by simp), (by simp [hzl]), hset⟩,
      ⟨a, (by simp), haB⟩, ⟨b, (by simp), hbB⟩, (by simp [hone])⟩, ?_⟩
    simp only [rvVar]
    simp [hi, hj]
    omega

/-! ## 8. In-place reverse: the cashing, the harness and the boundary -/

private theorem getBang_lt {B : ℕ} {xs : List ℕ} {k : ℕ} (h : ∀ v ∈ xs, v < B) (h0 : 0 < B) :
    xs[k]! < B := by
  by_cases hk : k < xs.length
  · rw [getElem!_pos xs k hk]; exact h _ (List.getElem_mem hk)
  · rw [getElem!_neg xs k hk]; exact h0

theorem rvIter_bound {B : ℕ} (h0 : 0 < B) : ∀ (m : ℕ) (s : ℕ × ℕ × List ℕ),
    (∀ v ∈ s.2.2, v < B) → ∀ v ∈ (rvIter m s).2.2, v < B := by
  intro m
  induction m with
  | zero => intro s h; exact h
  | succ m ih =>
      intro s h
      rw [rvIter]
      split
      · refine ih (rvStep s) ?_
        intro v hv
        simp only [rvStep] at hv
        rcases List.mem_or_eq_of_mem_set hv with hv' | rfl
        · rcases List.mem_or_eq_of_mem_set hv' with hv'' | rfl
          · exact h v hv''
          · exact getBang_lt h h0
        · exact getBang_lt h h0
      · exact h

/-- The declared array length, per input. -/
def rvExt (ys : List ℕ) : String → ℕ := fun b => if b = "A" then ys.length else 0

/-- The body: the constant `"one"`, the initial upper index, then the
synthesized loop (judgment call P5/D-ag). -/
def rvBody : Imp.Com :=
  .seq (.assign "one" (.lit 1))
    (.seq (.assign "j" (.bin .sub (.var "n") (.lit 1))) (embed rvLoop_impl))

/-- The whole program. -/
def rvProgram : Imp.Com :=
  .seq (readScalarsThenArr ["n"] "A" "cnt" "n" "tp") (.seq rvBody (writeArr "A" "jj" "n"))

/-- Nine scalars, one array, two temporaries. -/
def rvLayout : Layout :=
  ⟨["n", "cnt", "tp", "i", "j", "t1", "t2", "one", "jj"], ["A"], 2⟩

/-- The admissible inputs: a length, and that many entries. -/
def rvD : Set (List ℕ) := {x | ∃ ys : List ℕ, x = [ys.length] ++ ys}

/-- The function computed (judgment call P5/D-ai). -/
def rvOut' (x : List ℕ) : List ℕ := rvOutFn (x.drop 1)

/-- The cost. -/
def rvK (x : List ℕ) : ℕ :=
  12 * (x.drop 1).length + 26 * ((x.drop 1).length - 1) + 11 * (x.drop 1).length + 24

theorem rvBounds_holds (ys : List ℕ) : RvBounds ys (fcB ([ys.length] ++ ys)) where
  len := by
    simp only [fcB, List.sum_append, List.sum_cons, List.sum_nil]
    omega
  ent := by
    intro v hv
    have := List.single_le_sum (l := ys) (fun _ _ => Nat.zero_le _) v hv
    simp only [fcB, List.sum_append, List.sum_cons, List.sum_nil]
    omega

theorem rv_stateBound (ys : List ℕ) (B : ℕ) (hb : RvBounds ys B) :
    Ir.StateBound B (rvState ys) := by
  refine stateBound_ofPairs ?_ ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    have h1 := hb.len
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact hb.ent

/-- **The cashing step**, at reverse. -/
theorem rv_loop_spec (ys : List ℕ) :
    Reasoning.Spec (fcB ([ys.length] ++ ys)) (agree (rvState ys)) (embed rvLoop_impl)
      (fun _ σ' => σ'.arrs "A" = rvOutFn ys) (26 * (ys.length - 1) + 4) := by
  have hspec := spec_of_hnRefine
    (Φ := (· = rvIter (ys.length - 1) (0, ys.length - 1, ys)))
    (Q := fun (ra : ℕ × ℕ × List ℕ) σ' => σ'.arrs "A" = ra.2.2)
    (rvLoop' ys)
    (rv_loop_le (ys.length - 1) (0, ys.length - 1, ys) (rv_init_inv ys) (by simp [rvV]))
    (rv_state_holds ys) (rv_stateBound ys _ (rvBounds_holds ys))
    (rv_runs ys _ (rvBounds_holds ys))
    (by rw [ecash_rvTotal]; exact le_rfl)
    ?_
  · exact hspec.post (by
      rintro σ σ' - ⟨ra, rfl, hq⟩
      exact hq)
  · intro ra s' cr σ' _ h hag
    have he : (rvFrame ∗ (natAssn ×ₐ natAssn ×ₐ arrayAssn) ra ("i", "j", "A") ∗
        rvHole ys ∗ GC)
        = ("A" ↦ₐ ra.2.2) ∗ (rvFrame ∗ (("i" ↦ᵥ ra.1) ∗ (("j" ↦ᵥ ra.2.1) ∗
            (rvHole ys ∗ GC)))) := by
      simp only [prodAssn, natAssn_def, arrayAssn_def]
      ac_rfl
    rw [he] at h
    exact hag.arr (Ir.ptoArr_arrs h)

/-- What the two initialising assignments leave behind: the cells the
synthesized loop's precondition owns, plus the length cell the epilogue
needs. -/
def rvMid (ys : List ℕ) (σ : Imp.Env) : Prop :=
  σ.vars "n" = ys.length ∧ σ.arrs "A" = ys ∧ σ.vars "i" = 0 ∧ σ.vars "t1" = 0 ∧
    σ.vars "t2" = 0 ∧ σ.vars "one" = 1

/-- The body's specification, against the marshal descriptor. -/
theorem rv_body_spec (ys : List ℕ) :
    Reasoning.Spec (fcB ([ys.length] ++ ys))
      (ScalarsArrIn (rvExt ys) ["n"] "A" "cnt" "tp" [ys.length] ys) rvBody
      (fun _ σ' => σ'.arrs "A" = rvOutFn ys ∧ σ'.vars "n" = (rvOutFn ys).length)
      (26 * (ys.length - 1) + 10) := by
  have hb := rvBounds_holds ys
  have h1B : 1 < fcB ([ys.length] ++ ys) := by have := hb.len; omega
  have hnlt : ys.length < fcB ([ys.length] ++ ys) := by have := hb.len; omega
  -- phase 1: the constant
  have hone : Reasoning.Spec (fcB ([ys.length] ++ ys))
      (ScalarsArrIn (rvExt ys) ["n"] "A" "cnt" "tp" [ys.length] ys)
      (.assign "one" (.lit 1)) (fun _ σ' => rvMid ys σ') 2 := by
    refine ((Reasoning.Spec.assign (f := fun _ => 1) (x := "one") (e := .lit 1)
      (fun σ _ => Reasoning.evalB_lit h1B)).post ?_).mono (by simp)
    rintro σ σ' hσ rfl
    exact ⟨by simpa using hσ.cells ("n", ys.length) (by simp),
      by simpa using hσ.arr,
      by simpa using hσ.zero "i" (by simp) (by decide) (by decide),
      by simpa using hσ.zero "t1" (by simp) (by decide) (by decide),
      by simpa using hσ.zero "t2" (by simp) (by decide) (by decide),
      by simp⟩
  -- phase 2: the initial upper index
  have hj : Reasoning.Spec (fcB ([ys.length] ++ ys)) (rvMid ys)
      (.assign "j" (.bin .sub (.var "n") (.lit 1)))
      (fun _ σ' => agree (rvState ys) σ' ∧ σ'.vars "n" = ys.length) 4 := by
    refine ((Reasoning.Spec.assign (f := fun _ => ys.length - 1) (x := "j")
      (e := .bin .sub (.var "n") (.lit 1)) ?_).post ?_).mono (by simp)
    · intro σ hσ
      have hn : σ.vars "n" = ys.length := hσ.1
      have := Reasoning.evalB_bin (B := fcB ([ys.length] ++ ys)) (op := .sub)
        (Reasoning.evalB_var (x := "n") (σ := σ) (by rw [hn]; omega))
        (Reasoning.evalB_lit (B := fcB ([ys.length] ++ ys)) (n := 1) h1B)
        (by rw [hn]; show ys.length - 1 < fcB ([ys.length] ++ ys); omega)
      rw [hn] at this
      exact this
    · rintro σ σ' hσ rfl
      refine ⟨agree_ofPairs ?_ ?_, by simpa using hσ.1⟩
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl
        · simpa using hσ.2.2.1
        · simp
        · simpa using hσ.2.2.2.1
        · simpa using hσ.2.2.2.2.1
        · simpa using hσ.2.2.2.2.2
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl
        simpa using hσ.2.1
  -- phase 3: the loop, framed so that the length cell survives it
  have hloop : Reasoning.Spec (fcB ([ys.length] ++ ys))
      (fun σ => agree (rvState ys) σ ∧ σ.vars "n" = ys.length) (embed rvLoop_impl)
      (fun _ σ' => σ'.arrs "A" = rvOutFn ys ∧ σ'.vars "n" = (rvOutFn ys).length)
      (26 * (ys.length - 1) + 4) :=
    (((rv_loop_spec ys).frame).pre (fun σ hσ => hσ.1)).post (by
      rintro σ σ' ⟨-, hn⟩ ⟨harr, hfr, -, -, -⟩
      exact ⟨harr, by rw [hfr "n" (by decide), hn, rvOutFn_length]⟩)
  have hinner : Reasoning.Spec (fcB ([ys.length] ++ ys)) (rvMid ys)
      (.seq (.assign "j" (.bin .sub (.var "n") (.lit 1))) (embed rvLoop_impl))
      (fun _ σ'' => σ''.arrs "A" = rvOutFn ys ∧ σ''.vars "n" = (rvOutFn ys).length)
      (4 + (26 * (ys.length - 1) + 4)) :=
    Reasoning.Spec.seq hj hloop (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq)
  exact (Reasoning.Spec.seq hone hinner (fun _ _ _ hq => hq)
    (fun _ _ _ _ _ hq => hq)).mono (by omega)

/-- **The program's specification at `initEnv`.** -/
theorem rv_program_spec (ys : List ℕ) :
    Reasoning.Spec (fcB ([ys.length] ++ ys))
      (fun σ => σ = initEnv (rvExt ys) ([ys.length] ++ ys)) rvProgram
      (fun _ σ' => σ'.out = rvOutFn ys)
      (12 * ys.length + 26 * (ys.length - 1) + 11 * ys.length + 24) := by
  have hb := rvBounds_holds ys
  have hnB : ys.length < fcB ([ys.length] ++ ys) := by have := hb.len; omega
  have h0 : 0 < fcB ([ys.length] ++ ys) := by have := hb.len; omega
  have hresN : (rvOutFn ys).length < fcB ([ys.length] ++ ys) := by
    rw [rvOutFn_length]; exact hnB
  have hresB : ∀ v ∈ rvOutFn ys, v < fcB ([ys.length] ++ ys) :=
    rvIter_bound h0 _ _ hb.ent
  refine (Lax13Proofs.Codegen.marshal_scalarsArr_arr _ (rvExt ys) ["n"] "A" "cnt" "n" "tp"
    "A" "jj" "n" [ys.length] ys (rvOutFn ys) rvBody (26 * (ys.length - 1) + 10)
    (by simp) rfl (by simp) (by simp) (by simp) (by decide) (by decide) (by decide)
    (by simp [rvExt]) hnB hb.ent (by decide) hresN hresB
    (by simp [rvBody, Imp.Com.NoWrite, noWrite_embed]) (rv_body_spec ys)).mono ?_
  rw [rvOutFn_length]
  simp only [List.length_cons, List.length_nil]
  omega

theorem rvProgram_ok : Compile.Com.Ok rvLayout rvProgram := by
  simp [rvProgram, rvBody, readScalarsThenArr, readArr, writeArr,
    Lax13Proofs.Reasoning.Lib.Fill.put, rvLayout, Compile.Com.Ok, Compile.Cond.Ok,
    Compile.condExpr, Compile.Expr.Ok, rvLoop_impl, embed, embedCond, embedOperand]

/-- **The boundary.** -/
theorem rv_solves : Transfer.Solves rvLayout rvProgram rvD rvOut' fcB rvK := by
  refine solves_of_spec rvProgram_ok ?_ ?_
  · rintro x ⟨ys, rfl⟩ v hv
    have hs : ∀ v ∈ ys, v ≤ ys.sum := fun v hv =>
      List.single_le_sum (fun _ _ => Nat.zero_le _) v hv
    simp only [fcB, List.sum_append, List.sum_cons, List.sum_nil]
    simp only [List.cons_append, List.mem_cons] at hv
    rcases hv with rfl | hv
    · omega
    · have := hs v hv; omega
  · rintro x ⟨ys, rfl⟩
    refine ⟨rvExt ys, ?_⟩
    have hout : rvOut' ([ys.length] ++ ys) = rvOutFn ys := by simp [rvOut']
    have hK : rvK ([ys.length] ++ ys)
        = 12 * ys.length + 26 * (ys.length - 1) + 11 * ys.length + 24 := by simp [rvK]
    rw [hout, hK]
    exact rv_program_spec ys

/-- **The P5 gate for reverse.** -/
theorem rv_computesInTime (w : ℕ) (hfit : ∀ x ∈ rvD, rvLayout.FitsWords (fcB x) w) :
    Lax13.RamComputes.ComputesInTime w (compileProgram rvLayout rvProgram) rvD rvOut'
      (fun x => rvLayout.const * rvK x) :=
  rv_solves.computesInTime hfit

/-! ## 9. The gates (ledger D4)

Both programs are *run on the machine*, at the word length the transfer
theorem is stated at, and what comes off the output tape is `#guard`ed
against the value function — together with the step count against the
cost the theorems above claim. Each has a negative control.

The value functions are also checked against independent specifications
(`List.filter`, `List.reverse`), which is the honest reading of judgment
call P5/D-ai. -/

namespace Gate

open Lax13.Ram

/-! ### Filter-count: `[3, 1, 4, 1, 5]` under `t = 4` -/

-- The value function against an independent decider.
#guard fcCountOf [3, 1, 4, 1, 5] 4 = 3
#guard fcCountOf [3, 1, 4, 1, 5] 4 = ([3, 1, 4, 1, 5].filter (fun v => decide (v < 4))).length
#guard fcCountOf [3, 1, 4, 1, 5] 0 = 0
#guard fcCountOf [3, 1, 4, 1, 5] 6 = 5
#guard fcCountOf [] 4 = 0

/-- The input tape: the threshold, the length, the entries. -/
def fcInput : List ℕ := [4, 5] ++ [3, 1, 4, 1, 5]

theorem fcInput_mem : fcInput ∈ fcD := ⟨4, [3, 1, 4, 1, 5], rfl⟩

/-- The machine program. -/
def fcProg : Program := compileProgram fcLayout fcProgram

/-- …and its run. -/
def fcRunGate : Option (List ℕ × ℕ) := runOut 16 400000 fcProg (initState fcInput) 0

#guard fcRunGate.map Prod.fst = some [3]

-- **The negative control**: not the number of entries *above* the
-- threshold, which on this input is `2`.
#guard fcRunGate.map Prod.fst ≠ some [2]

-- The cost cross-check: the machine run stays inside `L.const · K`.
#guard (fcRunGate.map Prod.snd).getD 0 ≤ fcLayout.const * fcK fcInput

/-! ### Reverse: `[1, 2, 3, 4]` -/

#guard rvOutFn [1, 2, 3, 4] = [4, 3, 2, 1]
#guard rvOutFn [1, 2, 3, 4] = List.reverse [1, 2, 3, 4]
#guard rvOutFn [1, 2, 3, 4, 5] = List.reverse [1, 2, 3, 4, 5]
#guard rvOutFn [7, 7, 0] = List.reverse [7, 7, 0]
#guard rvOutFn [5] = [5]
#guard rvOutFn [] = []

/-- The input tape: the length, the entries. -/
def rvInput : List ℕ := [4] ++ [1, 2, 3, 4]

theorem rvInput_mem : rvInput ∈ rvD := ⟨[1, 2, 3, 4], rfl⟩

def rvProg : Program := compileProgram rvLayout rvProgram

def rvRunGate : Option (List ℕ × ℕ) := runOut 16 400000 rvProg (initState rvInput) 0

#guard rvRunGate.map Prod.fst = some [4, 3, 2, 1]

-- **The negative control**: the identity is not the reverse.
#guard rvRunGate.map Prod.fst ≠ some [1, 2, 3, 4]

#guard (rvRunGate.map Prod.snd).getD 0 ≤ rvLayout.const * rvK rvInput

end Gate

/-! ## 10. The axiom check -/

#print axioms fc_solves
#print axioms fc_computesInTime
#print axioms rv_solves
#print axioms rv_computesInTime

/-! ## 11. Telemetry (the plan's P5 gate numbers)

* **The gate.** Both P4 toys reach `Transfer.Solves` and
  `ComputesInTime` on the endorsed boundary, with no `sorry` and no
  axiom beyond `propext`, `Classical.choice`, `Quot.sound`:
  - `fc_computesInTime : ComputesInTime w (compileProgram fcLayout fcProgram) fcD fcOut
    (fun x => fcLayout.const * fcK x)`, `fcK x = 32·n + 17`;
  - `rv_computesInTime : ComputesInTime w (compileProgram rvLayout rvProgram) rvD rvOut'
    (fun x => rvLayout.const * rvK x)`, `rvK x = 12·n + 26·(n−1) + 11·n + 24`
    — that is `49·n − 2` for `n ≥ 1`, and `24` at `n = 0`, where the
    truncated subtraction of the loop's iteration budget bites. The four
    summands are left unsummed because each is one phase's lemma.

* **Authored lines.** A nesting-aware scan of this file: 990 physical,
  110 blank, 231 comment, **649 authored** — for two whole chains,
  including the abstract cost lemmas, the initial-state construction,
  the cashing, the harness assembly, the boundary and the gates.

* **Lines of *bounds* annotation** — the number the P7 `wordAssn`
  decision turns on. Everything that exists only because
  `BoundVcg.lean` has to be fed, per program:
  - filter-count: `fcB` 1, `fcInv` 5, `fcVar` 1, `FcBounds` 4,
    `FcBounds.one` 2, `fc_guard` 7, `fc_runs` 48, `fcBounds_holds` 12,
    `fc_stateBound` 12 — **92 lines**;
  - reverse: `RvBounds` 3, `rvInv` 6, `rvVar` 1, `rv_guard` 8,
    `rv_runs` 43, `rvBounds_holds` 9, `rv_stateBound` 11 — **81 lines**.
  Together **173 of 649**, about **27 %** of the end-to-end authored
  cost. But the *annotation proper* — the loop invariant, the variant
  and the record of what the bound has to satisfy — is only **10 lines
  per program**; the other ~70 are the *discharge*
  (`fc_runs` / `rv_runs` re-establishing the invariant, plus
  `…Bounds_holds` and `…_stateBound` instantiating it at `B x`).

* **What a `wordAssn B` retrofit would actually buy.** Of `fc_runs`'s 48
  lines, six are `< B` facts (`heB`, `htB`, `honeB`, `hkB`, `haccB`,
  `haccB0`) and one is the guard; the remaining ~40 re-establish the
  loop invariant — which a bounded assertion would still have to
  establish, only inside synthesis instead of after it. `apply_sub_lt`
  already removes reverse's only subtraction obligation outright, and no
  `copy`/`aget`/`aset` produced a goal at all. **Recommendation to P7:
  do not thaw P4.** The retrofit trades ~10 authored lines per program
  for a `wordAssn` side condition in every arithmetic hnr rule, and the
  70 lines it does *not* remove are the ones that cost time.

* **Wall clock**, warm build, `lake env lean` on single files (the
  import-only baseline is given for each, so the difference is
  elaboration):
  - `BoundVcg.lean` 4.8 s (baseline 3.7 s) — **1.1 s**;
  - `Cash.lean` 4.6 s (baseline 3.7 s) — **0.9 s**;
  - this file 7.3 s (baseline 4.3 s) — **3.0 s** for *both* end-to-end
    chains, gates and machine runs included.

* **Refute before prove.** The cost arithmetic was checked for direction
  before it was proved: `Cash.lean` §5 pins that `ecash` and `cash`
  agree on a lifted account (so `cash κ ≤ ecash T` is tight, not slack
  the wrong way) at `Ir/Semantics.lean`'s own countdown, and the two
  `#guard`s of §9 above check the *machine* step count against
  `L.const · K` on real runs of both compiled programs. No inequality
  came out backwards. Negative controls: one per program in §9, plus
  `BoundVcg.lean`'s `no_runs_bigConst` and `Sim.lean`'s two.

* **Backlog.**
  (i) The value functions are the programs' twins (P5/D-ai): that
  `fcCountOf ys t = (ys.filter (· < t)).length` and
  `rvOutFn ys = ys.reverse` are `#guard`ed, not proved. Both are
  loop-invariant arguments about `List`, independent of the tower;
  P4's backlog (i) records the same for reverse.
  (ii) `fcB` is shared by both programs (`x.sum + 2` either way). If P7
  wants a sharper word-length hypothesis, the place to change it is
  `fcB` and the two `…Bounds_holds` lemmas; §3 and §7 are unchanged.
  (iii) The `Spec.frame` step that carries `"n"` past reverse's loop
  (`rv_body_spec`, phase 3) is the only `∗`-free frame written by hand
  at the IMP+ level; a `Spec` combinator for "this phase writes none of
  these cells" would remove it.
  (iv) `omega` does not see through the reducible abbreviation
  `Ir.Val = ℕ` when it is a variable's declared type. Every invariant
  above therefore binds its indices at `ℕ` explicitly. A `Val`-aware
  `omega` preprocessing step, or making `Val` a plain `def` with a
  `simp` unfolding, would remove the trap; it cost an hour to find and
  is invisible at the call site.
-/

end EndToEnd

end Lax13Proofs.Refine.Codegen
