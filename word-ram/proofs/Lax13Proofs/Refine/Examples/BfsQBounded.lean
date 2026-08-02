import Lax13Proofs.Refine.Examples.BfsQSynth
import Lax13Proofs.Refine.Sepref.Examples.WordAssnSpike

/-!
# The spike's measurement: the BFS fill loop's bounds pass, re-derived

`Sepref/Examples/WordAssnSpike.lean` builds the two candidate layers for
the P8 verdict's option (b): `wordAssn` (§1–§3 there) and `BRefine`
(§4 there). This file is the *measurement* — the same obligation
`Examples/BfsQSynth.lean` §12 discharges, on the largest engine fragment
the spike budget reached, done the new way and counted.

## What is measured, and against what

The baseline is `BfsQSynth.lean` §12's bounds pass. Its **fill-loop
share** is:

| baseline declaration | raw lines |
|---|---|
| `eval_lt_cells` (guard inversion, shared with the drain) | 8 |
| `FInv` | 6 |
| `FInv.setVar` | 11 |
| `FInv.setArr` | 17 |
| `fill_body_bpre` | 24 |
| **total** | **66** |

plus the loop's share of `bfsQ_bpre`'s assembly (the `refine ⟨FInv …⟩`
block and the invariant at the initial store, 15 raw lines) — call it
**81 raw lines** for the fill loop alone, out of the 560 the verdict
priced.

§2 below is the same obligation through `BRefine`. It is *not* an
apples-to-apples full re-derivation of the BFS engine: the drain and row
scan are not attempted (R2/D-f records why), so the number is a
fragment-level ratio, not a program-level one.

## R2/D-f — why the measurement stops at the fill loop

The three-loop engine needs three things this spike does not have:

1. a `BRefine` analogue of `hnr_If` that knows *which* branch it is in
   (the row scan's `dist[u] = sent` test gates the queue store), so that
   the two arms can have different postconditions merged by `MERGE`;
2. `prodAssn` splitting in `BRefine`, since the drain's loop state is a
   four-component tuple and the ops want its components separately —
   `Sepref/Frame.lean`'s `conjunctsSplit` does this for the synthesis
   layer and has no `BRefine` counterpart;
3. tool integration: `BRefine` is assembled by hand here, whereas the
   synthesis layer's `sepref` driver picks and permutes rules
   automatically. Every `BRefine.perm (by ac_rfl)` below is a line the
   driver would emit.

None is deep; all three are P2 rule-layer work, and (3) is where the
remaining ratio lives. The fragment measured is the one that needs none
of them.
-/

namespace Lax13Proofs.Refine

namespace BfsQBounded

open Sepref Sepref.WordSpike Ir NRest

/-! ## 1. The fill loop's bounds annotation, via `BRefine`

`BfsQSynth.fillSynth_impl` is

```
while (i < n) { dist[i] := sent ; i := i + one ; skip }
```

and what follows is everything the bounds pass needs for it. -/

/-- The loop assertion, at the abstract loop state `(dist, i)`: the two
components the program mutates, and the three constants it reads. The
tower's own `fillLoop'` state is exactly this pair. -/
def fillΓ (n sent : ℕ) : List ℕ × ℕ → Assn := fun t =>
  arrayAssn t.1 "dist" ∗ natAssn t.2 "i" ∗ natAssn n "n" ∗ natAssn sent "sent" ∗
    natAssn 1 "one"

/-- The abstract invariant. **One conjunct** — the index never passes the
bound. `dist`'s entries, the constants and every in-range fact are
carried by the assertion and by the run; §12's `FInv` needed six
conjuncts and three closure lemmas to say the same thing over
`Ir.State`. -/
def fillI (n : ℕ) : List ℕ × ℕ → Prop := fun t => t.2 ≤ n

/-- The guard bridge (`hg` of `BRefine.while_guard`): the concrete
`i < n` is the abstract `i < n`, read off ownership. One lemma per guard
*shape*; `BfsQSynth.eval_lt_cells` is the inversion, reused. -/
theorem fill_guard (n sent : ℕ) (t : List ℕ × ℕ) (F : Assn) (s : Ir.State) (cr : ECost)
    (r : Bool) (_ : fillI n t) (hs : irSTATE (fillΓ n sent t ∗ F) (s, cr))
    (hev : (Cond.lt (Operand.cell "i") (Operand.cell "n")).eval s = some r) :
    decide (t.2 < n) = r := by
  obtain ⟨a, b, ha, hb, rfl⟩ := BfsQSynth.eval_lt_cells hev
  have hi : s.vars "i" = some t.2 :=
    natAssn_vars (F := arrayAssn t.1 "dist" ∗ natAssn n "n" ∗ natAssn sent "sent" ∗
      natAssn 1 "one" ∗ F) (irSTATE_cong (by rw [fillΓ]; ac_rfl) hs)
  have hn : s.vars "n" = some n :=
    natAssn_vars (F := arrayAssn t.1 "dist" ∗ natAssn t.2 "i" ∗ natAssn sent "sent" ∗
      natAssn 1 "one" ∗ F) (irSTATE_cong (by rw [fillΓ]; ac_rfl) hs)
  rw [hi] at ha
  rw [hn] at hb
  rw [Option.some.inj ha, Option.some.inj hb]

/-- **The loop body.** The single side condition `i + 1 < B` is
discharged from the *abstract* guard and `n < B` — no `Ir.State`, no
`setVar`/`setArr` closure, no `Option.some.inj`. -/
theorem fill_body_brefine {B n sent : ℕ} (hnB : n < B) (t : List ℕ × ℕ)
    (_hI : fillI n t) (hbf : decide (t.2 < n) = true) :
    BRefine B (fillΓ n sent t)
      ((Com.aset "dist" "i" "sent").seq ((Com.binop Imp.Bop.add "i" "i" "one").seq Com.skip))
      (LoopAssn (fillI n) (fillΓ n sent)) := by
  have hlt : t.2 < n := of_decide_eq_true hbf
  refine BRefine.seq (Γ₁ := ⌜t.2 < t.1.length⌝ ∗ fillΓ n sent (t.1.set t.2 sent, t.2)) ?_ ?_
  · exact BRefine.perm
      (P := (arrayAssn t.1 "dist" ∗ natAssn t.2 "i" ∗ natAssn sent "sent") ∗
        (natAssn n "n" ∗ natAssn 1 "one"))
      (P' := (⌜t.2 < t.1.length⌝ ∗ arrayAssn (t.1.set t.2 sent) "dist" ∗ natAssn t.2 "i" ∗
        natAssn sent "sent") ∗ (natAssn n "n" ∗ natAssn 1 "one"))
      (by simp only [fillΓ]; ac_rfl) (by simp only [fillΓ]; ac_rfl)
      (BRefine.frame BRefine.aset)
  · refine BRefine.pre_pure fun _ => ?_
    refine BRefine.seq
      (Γ₁ := fillΓ n sent (t.1.set t.2 sent, Imp.Bop.apply .add t.2 1)) ?_ ?_
    · exact BRefine.perm
        (P := (natAssn t.2 "i" ∗ natAssn 1 "one") ∗
          (arrayAssn (t.1.set t.2 sent) "dist" ∗ natAssn n "n" ∗ natAssn sent "sent"))
        (P' := (natAssn (Imp.Bop.apply .add t.2 1) "i" ∗ natAssn 1 "one") ∗
          (arrayAssn (t.1.set t.2 sent) "dist" ∗ natAssn n "n" ∗ natAssn sent "sent"))
        (by simp only [fillΓ]; ac_rfl) (by simp only [fillΓ]; ac_rfl)
        (BRefine.frame (BRefine.binop_self (by rw [Imp.Bop.apply_add]; omega)))
    · exact BRefine.skip.cons (entails_refl _)
        (loopAssn_intro (I := fillI n) (Γ := fillΓ n sent)
          (t := (t.1.set t.2 sent, Imp.Bop.apply .add t.2 1))
          (by simp only [fillI, Imp.Bop.apply_add]; omega))

/-- **The fill loop's bounds pass.** -/
theorem fill_brefine {B n sent : ℕ} (hnB : n < B) :
    BRefine B (LoopAssn (fillI n) (fillΓ n sent)) BfsQSynth.fillSynth_impl
      (LoopAssn (fillI n) (fillΓ n sent)) := by
  rw [BfsQSynth.fillSynth_impl]
  exact BRefine.while_guard (bf := fun t => decide (t.2 < n))
    BfsQSynth.litLt_lt_cells (fill_guard n sent)
    (fun t hI hbf => fill_body_brefine hnB t hI hbf)
    (fun t hI _ => loopAssn_intro hI)

/-! ## 2. End to end: the `BigStepB` witness

A concrete initial store for the loop, the ownership proof, and the
`Ir.bpre` the cashing chain consumes. -/

/-- The fill loop's own store. -/
def fillState (n sent : ℕ) (D : List ℕ) : Ir.State :=
  Ir.State.ofPairs [("i", 0), ("n", n), ("sent", sent), ("one", 1)] [("dist", D)]

def fillHole (n sent : ℕ) (D : List ℕ) : Assn :=
  EXACT ((((((vcells (fillState n sent D)).erase "i").erase "n").erase "sent").erase "one",
    (acells (fillState n sent D)).erase "dist", hcells (fillState n sent D)), 0)

theorem fillState_holds (n sent : ℕ) (D : List ℕ) :
    irSTATE (fillΓ n sent (D, 0) ∗ fillHole n sent D) (fillState n sent D, 0) := by
  show (fillΓ n sent (D, 0) ∗ fillHole n sent D)
    ((vcells (fillState n sent D), acells (fillState n sent D),
      hcells (fillState n sent D)), 0)
  simp only [fillΓ, natAssn_def, arrayAssn_def, sepConj_assoc]
  refine Ir.ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  exact Ir.ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩

theorem fillState_bound {B n sent : ℕ} {D : List ℕ} (hnB : n < B) (hsB : sent < B)
    (h1B : 1 < B) (hD : ∀ v ∈ D, v < B) : Ir.StateBound B (fillState n sent D) := by
  refine Codegen.stateBound_ofPairs ?_ ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simpa using by omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact hD

/-- **The bounds witness for the fill loop**, in the shape
`Codegen/Cash.lean`'s `exists_bigStepB_of_hnRefine` consumes. -/
theorem fill_bpre {B n sent : ℕ} {D : List ℕ} (hnB : n < B) (hsB : sent < B) (h1B : 1 < B)
    (hD : ∀ v ∈ D, v < B) :
    Ir.bpre B BfsQSynth.fillSynth_impl (fun _ => True) (fillState n sent D) :=
  bpre_of_BRefine (F := fillHole n sent D) (fill_brefine hnB)
    (start_entailsE (fillState_holds n sent D)
      (sepConj_mono_left (loopAssn_intro (I := fillI n) (t := (D, 0)) (Nat.zero_le n))))
    (fillState_bound hnB hsB h1B hD)

/-- …and the bounded run itself, from the plain one the semantics
gives. -/
theorem fill_bigStepB {B n sent : ℕ} {D : List ℕ} (hnB : n < B) (hsB : sent < B)
    (h1B : 1 < B) (hD : ∀ v ∈ D, v < B) {s' : Ir.State} {κ : Ir.Cost}
    (hrun : Ir.BigStep BfsQSynth.fillSynth_impl (fillState n sent D) s' κ) :
    Ir.BigStepB B BfsQSynth.fillSynth_impl (fillState n sent D) s' κ :=
  (hrun.bigStepB_of_inv (fill_bpre hnB hsB h1B hD)).1

/-! ## 3. Gate (ledger D4)

The pass is refuted where it should fail: at a bound the loop counter
overflows. -/

/-- The loop bumps `i` up to `n`, so `n < B` is not slack — at `B = n`
the very first bump is out of range and there is no `BRefine`. The
refutation is on `bpre` itself, at `n = 1`, `B = 1`. -/
theorem no_fill_bpre_at_bound :
    ¬ Ir.bpre 1 BfsQSynth.fillSynth_impl (fun _ => True) (fillState 1 0 [0]) := by
  rw [BfsQSynth.fillSynth_impl, Ir.bpre_while]
  rintro ⟨Inv, hI, hg, hbody, -⟩
  have hev : (Cond.lt (Operand.cell "i") (Operand.cell "n")).eval (fillState 1 0 [0])
      = some true := rfl
  have hb := hbody _ hI hev
  rw [Ir.bpre_seq, Ir.bpre_aset] at hb
  have hb2 := hb 0 0 [0] rfl rfl rfl (by decide)
  rw [Ir.bpre_seq, Ir.bpre_binop] at hb2
  exact absurd (hb2 0 1 rfl rfl).1 (by decide)

/-! ## 4. Axioms -/

#print axioms fill_bpre
#print axioms fill_bigStepB
#print axioms no_fill_bpre_at_bound

/-! ## 5. Telemetry (the spike's numbers)

All counts are raw lines, measured, declaration by declaration.

**(a) Authored lines on the bounds class.**

| this file, §1 | raw | `BfsQSynth.lean` §12, fill share | raw |
|---|---|---|---|
| `fillΓ` | 3 | `eval_lt_cells` | 8 |
| `fillI` | 1 | `FInv` | 5 |
| `fill_guard` | 14 | `FInv.setVar` | 10 |
| `fill_body_brefine` | 28 | `FInv.setArr` | 16 |
| `fill_brefine` | 8 | `fill_body_bpre` | 23 |
| | | fill's share of `bfsQ_bpre` | 13 |
| **total** | **54** | **total** | **75** |

**28 % as authored today.** The composition matters more than the
ratio:

* of the new 54, **14 are the guard bridge** — one lemma per guard
  *shape* (`Cond.lt` of two cells), not per loop and not per program, so
  the engine's three loops share it;
* another **14 are `BRefine.perm`/`BRefine.frame` bookkeeping** — the
  rule-application permutations `Sepref/Translate.lean`'s driver already
  computes for the synthesis half, and which a `sepref_brefine_rules`
  database would emit instead of the author;
* the per-loop marginal is therefore **≈ 26 lines**, against a baseline
  per-loop marginal of **≈ 67** (only `eval_lt_cells` amortizes there).

So the honest projection for the engine is **a 55–62 % cut of the
560-line class, to 210–250 lines**, and the part that survives is the
part that is real: the abstract invariant and one arithmetic goal per
creation site.

What is *gone*, structurally: the `Ir.State` predicate (`FInv`/`DInv`),
its `setVar`/`setArr` closure lemmas, and every `Option.some.inj` /
`simpa using` identification between a cell and the value it holds. The
assertion already says that, which is R2/D-b.

**(b) Side-condition traffic.** **Two** arithmetic goals in the whole
fragment: `Imp.Bop.apply .add i 1 < B` at the bump (the creation site)
and `i + 1 ≤ n` at the invariant restoration. Discharge mode:
`rw [Imp.Bop.apply_add]; omega` for both — **zero manual**. Notably the
`omega`-through-`Ir.Val` trap (`BfsQSynth.lean` §12's header) does *not*
fire: the operands are `ℕ`-typed abstract values, not `Ir.Val` clause
binders. Everything else — the `aset`, the guard evaluation, the `skip`,
every in-range index — is free, exactly as P7/D-bl's table predicts.

**(c) Synthesis wall-clock: unchanged, by construction.** `BRefine` is a
second component proved *after* synthesis; this file consumes
`BfsQSynth.fillSynth_impl` byte-identical, so the baseline's 49 s stands.
The added elaboration cost is the two new files: ≈ 6 s for the rule layer
(`WordAssnSpike.lean`, 900 lines including its own gate) and ≈ 6 s here.
The `wordAssn` route's synthesis time **cannot be measured**: R2/D-c
says it does not reach a two-operation program.

**(d) Rule-layer gaps.** R2/D-f above (branch-aware `ite`, `prodAssn`
splitting, tool integration), plus: no `BRefine` rule for `mopPair`/the
`pack` shapes, no `BRefine` counterpart of `MERGE`, and no
`sepref_brefine_rules` database — every rule here is applied by name.
-/

end BfsQBounded

end Lax13Proofs.Refine
