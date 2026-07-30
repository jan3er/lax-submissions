import Lax3Proofs.Refine.ElimSynth
import Lax13Proofs.Refine.Sepref.IrOpsExtra

/-!
# P2 wave 2B′ — the elimination engine, completed through the tower (I)

Satellite 2B (`Refine/ElimSynth.lean`) landed the engine's falsification
gate — a computable twin of all five phases, guard-checked against
`RamElim.Demo`'s runs of the *compiled machine program* — and the degree
pass end to end. It retained the other four phases because the
translate driver stalled on a two-loop pass (2B/D-a). Tool wave T1
(`Sepref/Frame.lean` T1/D-a, T1/D-b, T1/D-d, T1/D-e, T1/D-f) fixed the
stall.

This file and `ElimSynth3.lean` carry the remaining four phases through
the tower. Here: the bucket build, the offset pass and the fill pass;
`ElimSynth3.lean`: the elimination loop, whose state is eleven
components wide.

## Where each phase stands after this wave

| phase | abstract | cost | `RamElim` postcondition | `sepref_synth` |
|---|---|---|---|---|
| degree pass (2B) | §3 of `ElimSynth` | `36n+23ns+4` | `adeg` (`degPass_adeg`) | inner loop |
| bucket build | §2 | `31n+4` | `Buck n n` (`buckPass_spec`) | **whole pass** |
| elimination loop | `ElimSynth3` §2–3 | debt E1 | debt E2 | **whole loop** |
| offset pass | §3 | `28n+4` | `psum` (`offPass_spec`) | **whole pass** |
| fill pass | §4 | per-iteration | debt F1 | **whole pass** |

The degree pass's *outer* loop, which 2B could not translate, is not
re-run here: 2B's `degPass_le` and `degPass_adeg` are landed capital and
the one thing missing from that phase is a `sepref_synth` invocation
that tool wave T1 has now made possible. The whole-engine export is
**not** in this wave: it needs the elimination loop's and the fill
pass's postconditions, which are debts E2 and F1.

## The one reusable device (§1.2)

Every loop below, and every loop of `ElimSynth3.lean`, is bounded by a
single lemma — `while_pot_le`. Satellite 2B wrote the fuel induction
out twice (`degScan_le`, `degPass_le`, ≈100 lines); `RamElim`'s own
walks write it out five times against `Spec.while_potential`. The
elimination engine has *eight* loops, so the induction is factored once:
a body that is bounded by one result at a known price, an invariant it
preserves, a variant it drops and a **potential** it pays out of. The
two-currency energy `E2` of 2B's `degPass` is one instance (`Φ s = E2 …`
and `C s` the row's own price), and so is the amortized elimination loop
of `ElimSynth3.lean`.

## The array/function bridge (§1.1)

`RamElim`'s mathematics — `Buck`, `Elim`, `InCsr`, `psum` — is stated
over functions `ℕ → ℕ`, *not* over `Env`: nothing in it knows about the
machine. So the tower can consume it directly, and the whole bridge is
`larr l = fun i => l[i]!` with the one lemma that a `List.set` is an
`upd` (`larr_set`). That is why the phase postconditions below are
literally `RamElim.Buck`, `RamElim.psum` and `RamElim.InCsr` rather than
list-level restatements needing a translation later.

## `ls` is not a state component (2B′/D-a)

The machine program carries a cell `ls`, the number of slots the buckets
hold, bumped by `push` and dropped by `elimTurn`. 2B's twin does not,
and neither do the programs here: `ls` is *determined* by the bucket
arrays (`Buck.ls_eq`: it is `∑ d ≤ n, |chain BN (BH d)|`), it is not an
output of the engine, and the potential that pays for the elimination
loop can read it off the state. Dropping it is therefore cost-only —
one `add` per push, one `sub` per pop — and it keeps the elimination
loop's state at eleven components instead of twelve. Recorded as a
deviation from the machine program's text; the *values* the engine
reports are unchanged, which is what §1's guards check.

## House traps observed

`omega` is blind through `Ir.Val`; `decide +kernel` for the numerals;
never `simp [Codegen.embed]`; junk cells are consumed in written order
and are digit-free.
-/

namespace Lax3Proofs.Refine.ElimSynth2

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax13Proofs.Refine.Codegen
open Lax13Proofs.Refine.BfsQ (Shape cu iter irWhile_exit get!_set res_of_le liftACost_cu)
open Lax3Proofs.Refine.ElimSynth hiding mopSucc mopSucc_eq mopKeep mopKeep_eq

/-! ## 1. The two devices -/

section Devices

/-! ### 1.1 An array, read as a function -/

/-- An array, read as the function `RamElim`'s mathematics speaks
about. -/
def larr (l : List ℕ) : ℕ → ℕ := fun i => l[i]!

@[simp] theorem larr_apply (l : List ℕ) (i : ℕ) : larr l i = l[i]! := rfl

/-- **A `List.set` is an `upd`** — in range, which is the only place the
engine writes. -/
theorem larr_set {l : List ℕ} {d : ℕ} (h : d < l.length) (v : ℕ) :
    larr (l.set d v) = Lax13Proofs.Reasoning.Lib.upd (larr l) d v := by
  funext j
  rw [larr_apply, get!_set _ _ _ _ h, Lax13Proofs.Reasoning.Lib.upd, larr_apply]

@[simp] theorem length_set (l : List ℕ) (i v : ℕ) : (l.set i v).length = l.length :=
  List.length_set ..

/-! ### 1.2 One loop lemma for the whole engine

The shape every loop of the engine has: a body bounded by **one**
result at a known price, an invariant, a variant, and a potential the
price is paid out of. `Φ` is a *function of the state*, so the two
amortized loops (the degree pass's two-currency energy, the
elimination loop's four-term potential) are instances and not special
cases. -/

theorem while_pot_le {σ : Type} {P I : σ → Prop} {bf : σ → Bool} {f : σ → NRest σ ECost}
    {V : σ → ℕ} {Φ Φ' C : σ → ACost String ℕ}
    (hP : ∀ s, I s → bf s = true → P s)
    (hstep : ∀ s, I s → bf s = true →
      f s ≤ NRest.spec (fun t => I t ∧ V t < V s ∧ Φ t ≤ Φ' s) (fun _ => liftACost (C s)))
    (hΦ : ∀ s, I s → bf s = true → iter (C s) + Φ' s ≤ Φ s) :
    ∀ (fuel : ℕ) (s : σ), I s → V s < fuel →
      irWhileIT (fun t => bf t = true → P t) bf f s
        ≤ NRest.spec (fun t => I t ∧ bf t = false)
            (fun _ => liftACost (Φ s + cu Currency.«while»)) := by
  have exit : ∀ s : σ, I s → bf s = false →
      irWhileIT (fun t => bf t = true → P t) bf f s
        ≤ NRest.spec (fun t => I t ∧ bf t = false)
            (fun _ => liftACost (Φ s + cu Currency.«while»)) := by
    intro s hIs hb
    rw [irWhile_exit hb]
    refine consume_returnT_le_spec ⟨hIs, hb⟩ ?_
    rw [liftACost_add, liftACost_cu, add_comm]
    exact cost_le_add _ _
  intro fuel
  induction fuel with
  | zero => intro s hIs hf; exact absurd hf (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro s hIs hf
    by_cases hb : bf s = true
    · have hIs' : bf s = true → P s := fun _ => hP s hIs hb
      have hcont : ∀ t, (I t ∧ V t < V s ∧ Φ t ≤ Φ' s) →
          irWhileIT (fun y => bf y = true → P y) bf f t
            ≤ NRest.spec (fun y => I y ∧ bf y = false)
                (fun _ => liftACost (Φ' s + cu Currency.«while»)) := by
        rintro t ⟨hIt, hVt, hΦt⟩
        refine le_trans (ih t hIt (by omega)) (spec_mono (fun _ h => h) (fun _ _ => ?_))
        simp only [liftACost_le_iff]
        exact add_le_add hΦt le_rfl
      have hcost : irUnit Currency.«while»
          + (liftACost (C s) + liftACost (Φ' s + cu Currency.«while»))
          ≤ liftACost (Φ s + cu Currency.«while») := by
        simp only [← liftACost_cu, ← liftACost_add, liftACost_le_iff]
        have h := hΦ s hIs hb
        rw [ACost.le_def] at h ⊢
        intro k
        have hk := h k
        simp only [ACost.toFun_add, iter] at hk ⊢
        omega
      calc irWhileIT (fun t => bf t = true → P t) bf f s
          = NRest.consume (NRest.bindT (f s)
              fun s' => irWhileIT (fun t => bf t = true → P t) bf f s')
              (irUnit Currency.«while») := irWhileIT_of_true hIs' hb
        _ ≤ NRest.consume (NRest.bindT
              (NRest.spec (fun t => I t ∧ V t < V s ∧ Φ t ≤ Φ' s)
                (fun _ => liftACost (C s)))
              fun s' => irWhileIT (fun t => bf t = true → P t) bf f s')
              (irUnit Currency.«while») :=
            NRest.consume_mono
              (NRest.bindT_mono (hstep s hIs hb) fun _ => le_rfl) le_rfl
        _ ≤ NRest.spec (fun t => I t ∧ bf t = false)
              (fun _ => liftACost (Φ s + cu Currency.«while»)) := by
            refine le_trans (NRest.consume_mono (bindT_spec_le _ _ _ _ _ hcont) le_rfl) ?_
            rw [Sepref.consume_spec]
            exact spec_mono (fun _ h => h) (fun _ _ => hcost)
    · exact exit s hIs (by simpa using hb)

/-- The body bound in the shape `while_pot_le` asks for, when the body
has **one** result. -/
theorem step_spec {σ : Type} {I : σ → Prop} {V : σ → ℕ} {Φ Φ' C : σ → ACost String ℕ}
    {m : NRest σ ECost} {s x : σ}
    (hm : m ≤ NRest.consume (NRest.returnT x) (liftACost (C s)))
    (hI : I x) (hV : V x < V s) (hΦ : Φ x ≤ Φ' s) :
    m ≤ NRest.spec (fun t => I t ∧ V t < V s ∧ Φ t ≤ Φ' s) (fun _ => liftACost (C s)) :=
  le_trans hm (consume_returnT_le_spec ⟨hI, hV, hΦ⟩ le_rfl)

/-- The variant of a loop whose body is bounded by one result, in the
form `LOOP_VARIANT` asks for. -/
theorem variant_of_step {σ : Type} {P : σ → Prop} {bf : σ → Bool} {f : σ → NRest σ ECost}
    {step : σ → σ} {V : σ → ℕ} {C : σ → ACost String ℕ}
    (hstep : ∀ s, P s → bf s = true →
      f s ≤ NRest.consume (NRest.returnT (step s)) (liftACost (C s)))
    (hV : ∀ s, P s → bf s = true → V (step s) < V s) :
    LOOP_VARIANT (fun t => bf t = true → P t) bf f V := by
  intro s s' hI hb hle
  rw [res_of_le (hstep s (hI hb) hb) hle]
  exact hV s (hI hb) hb

end Devices

/-! ## 2. The bucket build

`RamElim.initBuck`: one slot per vertex, pushed onto the stack of the
bucket its degree names. The arena is allocated upwards from slot `1`,
slot `0` being the sentinel, so an empty bucket reads `0` and no bucket
has to be initialised — which is what the machine's zeroed memory
already says, and what at this layer is the caller's `bh₀` being zero.

The postcondition is `RamElim.Buck` itself: the mathematics of the
lazily deleted stacks is `RamElim`'s and is consumed, not re-proved. -/

section Bucket

/-- The bucket build's state, flattened: heads, slot vertices, slot
links, the next free slot, the counter. -/
abbrev BS : Type := List ℕ × List ℕ × List ℕ × ℕ × ℕ

/-- 2B's `BSt × ℕ`, flattened. -/
def bflat : ElimSynth.BSt × ℕ → BS := fun s => (s.1.1, s.1.2.1, s.1.2.2.1, s.1.2.2.2, s.2)

/-- **One vertex, bucketed** — 2B's `initBuckRowTw` at the flat state. -/
def buckTw (deg : List ℕ) : BS → BS := fun s =>
  (s.1.set deg[s.2.2.2.2]! s.2.2.2.1, s.2.1.set s.2.2.2.1 s.2.2.2.2,
    s.2.2.1.set s.2.2.2.1 s.1[deg[s.2.2.2.2]!]!, s.2.2.2.1 + 1, s.2.2.2.2 + 1)

/-- The flattening is a step-for-step identity, so `ElimSynth` §1's
differential test is a test of *this* program. -/
theorem buckTw_flat (deg : List ℕ) (s : ElimSynth.BSt × ℕ) :
    bflat (initBuckRowTw deg s) = buckTw deg (bflat s) := rfl

/-- The pass, as a fuelled function. -/
def buckRunTw (n : ℕ) (deg : List ℕ) : ℕ → BS → BS
  | 0, s => s
  | fuel + 1, s => if s.2.2.2.2 < n then buckRunTw n deg fuel (buckTw deg s) else s

theorem buckRunTw_flat (n : ℕ) (deg : List ℕ) :
    ∀ (fuel : ℕ) (s : ElimSynth.BSt × ℕ),
      bflat (initBuckTw n deg fuel s) = buckRunTw n deg fuel (bflat s)
  | 0, _ => rfl
  | fuel + 1, s => by
    show bflat (if s.2 < n then initBuckTw n deg fuel (initBuckRowTw deg s) else s)
      = if s.2 < n then buckRunTw n deg fuel (buckTw deg (bflat s)) else bflat s
    by_cases hb : s.2 < n
    · rw [if_pos hb, if_pos hb, buckRunTw_flat n deg fuel, buckTw_flat]
    · rw [if_neg hb, if_neg hb]

/-! ### 2.1 The differential test -/

/-- The demo arena's degrees, from 2B's degree twin. -/
def demoDeg (a2 : ℕ) : List ℕ :=
  (initDegTw 5 demoOff demoTgt (demoAlv a2) 30 (List.replicate 5 0, 0)).1

/-- The demo's empty arena. -/
def demoB0 : BS := (List.replicate 6 0, List.replicate 16 0, List.replicate 16 0, 1, 0)

-- mask on: the degrees `2 2 3 2 1` the triangle-plus-path forces
#guard demoDeg 1 = [2, 2, 3, 2, 1]
-- mask off at `2`: the arena breaks into `0—1` and `3—4`, and `2` is
-- isolated
#guard demoDeg 0 = [1, 1, 0, 1, 1]

-- **The flat pass is 2B's pass**, at both masks and the demo's width.
#guard buckRunTw 5 (demoDeg 1) 30 demoB0
  = bflat (initBuckTw 5 (demoDeg 1) 30
      ((List.replicate 6 0, List.replicate 16 0, List.replicate 16 0, 1), 0))
#guard buckRunTw 5 (demoDeg 0) 30 demoB0
  = bflat (initBuckTw 5 (demoDeg 0) 30
      ((List.replicate 6 0, List.replicate 16 0, List.replicate 16 0, 1), 0))

-- …and what it leaves: five slots and the arena pointer at `6`.
#guard (buckRunTw 5 (demoDeg 1) 30 demoB0).2.2.2.1 = 6
#guard (buckRunTw 5 (demoDeg 1) 30 demoB0).1 = [0, 5, 4, 3, 0, 0]

/-- The push with the head **written before it is read** — the
transposition 2B's `pushTwWrong` exhibits, at the flat state. -/
def buckTwWrong (deg : List ℕ) : BS → BS := fun s =>
  (s.1.set deg[s.2.2.2.2]! s.2.2.2.1, s.2.1.set s.2.2.2.1 s.2.2.2.2,
    s.2.2.1.set s.2.2.2.1 (s.1.set deg[s.2.2.2.2]! s.2.2.2.1)[deg[s.2.2.2.2]!]!,
    s.2.2.2.1 + 1, s.2.2.2.2 + 1)

def buckRunTwWrong (n : ℕ) (deg : List ℕ) : ℕ → BS → BS
  | 0, s => s
  | fuel + 1, s => if s.2.2.2.2 < n then buckRunTwWrong n deg fuel (buckTwWrong deg s) else s

-- **Negative control on the in-place aliasing**: the head is read
-- before it is written, so the second push into a bucket links to the
-- first; the transposition links it to itself, and the check sees it.
#guard buckRunTwWrong 5 (demoDeg 1) 30 demoB0 ≠ buckRunTw 5 (demoDeg 1) 30 demoB0

/-! ### 2.2 The abstract program

The loop state is a **resource**: it is assembled with `mopPair`, never
written as a literal tuple (T1/P4/D-m — the linearity of the tool's
state matching). `pack5` is the five-component form. -/

/-- Assemble a five-component state. -/
noncomputable def pack5 (BH BV BN : List ℕ) (sp i : ℕ) : NRest BS ECost :=
  bindT (mopPair sp i) fun p => bindT (mopPair BN p) fun q =>
    bindT (mopPair BV q) fun r => mopPair BH r

/-- The pass's guard. -/
def buckBf (n : ℕ) : BS → Bool := fun s => decide (s.2.2.2.2 < n)

/-- What one row needs in range: the counter is a vertex, the degree it
reads names a bucket, and the fresh slot is inside the arena. -/
def buckP (deg : List ℕ) : BS → Prop := fun s =>
  s.2.2.2.2 < deg.length ∧ deg[s.2.2.2.2]! < s.1.length ∧
    s.2.2.2.1 < s.2.1.length ∧ s.2.2.2.1 < s.2.2.1.length

/-- **One vertex, put in the bucket of its degree.** -/
noncomputable def buckF (deg : List ℕ) : BS → NRest BS ECost := fun s =>
  bindT (mopAget deg s.2.2.2.2) fun d =>
    bindT (mopAget s.1 d) fun h =>
      bindT (mopAset s.2.1 s.2.2.2.1 s.2.2.2.2) fun BV =>
        bindT (mopAset s.2.2.1 s.2.2.2.1 h) fun BN =>
          bindT (mopAset s.1 d s.2.2.2.1) fun BH =>
            bindT (mopSucc s.2.2.2.1) fun sp =>
              bindT (mopSucc s.2.2.2.2) fun i => pack5 BH BV BN sp i

/-- **The bucket build.** -/
noncomputable def buckPass (n : ℕ) (deg : List ℕ) (s₀ : BS) : NRest BS ECost :=
  irWhileIT (fun s => buckBf n s = true → buckP deg s) (buckBf n) (buckF deg) s₀

/-- One row's price: two reads, three writes, two bumps, the tuple. -/
def buckC : ACost String ℕ := cu Currency.aget + cu Currency.aget + cu Currency.aset
  + cu Currency.aset + cu Currency.aset + cu Currency.add + cu Currency.add
  + cu Currency.skip + cu Currency.skip + cu Currency.skip + cu Currency.skip

theorem buckF_le (deg : List ℕ) (s : BS) (h : buckP deg s) :
    buckF deg s ≤ NRest.consume (NRest.returnT (buckTw deg s)) (liftACost buckC) := by
  refine le_of_eq ?_
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [buckF, buckTw, pack5, mopAget_def, mopAset_def, mopSucc_eq, mopBinop_def,
    mopPair_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h3,
    NRest.assert_pos h4, NRest.returnT_bindT,
    NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, buckC, liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

/-! ### 2.3 The invariant, in `RamElim`'s vocabulary -/

/-- The bucket build's invariant: the arrays at their lengths, one slot
per vertex placed so far, and `RamElim.Buck` on the nose. -/
def buckI (n W : ℕ) (deg : List ℕ) : BS → Prop := fun s =>
  s.1.length = n + 1 ∧ s.2.1.length = n + W + 1 ∧ s.2.2.1.length = n + W + 1 ∧
    deg.length = n ∧ (∀ v < n, deg[v]! < n) ∧
    s.2.2.2.2 ≤ n ∧ s.2.2.2.1 = s.2.2.2.2 + 1 ∧
    RamElim.Buck n s.2.2.2.2 (fun _ => 0) (larr deg) (larr s.1) (larr s.2.1)
      (larr s.2.2.1) s.2.2.2.1 s.2.2.2.2

theorem buckI_range {n W : ℕ} {deg : List ℕ} {s : BS} (hI : buckI n W deg s)
    (hb : buckBf n s = true) : buckP deg s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := hI
  have hi : s.2.2.2.2 < n := by simpa [buckBf] using hb
  exact ⟨by omega, by rw [h1]; have := h5 _ hi; omega, by omega, by omega⟩

theorem buckI_step {n W : ℕ} {deg : List ℕ} {s : BS} (hI : buckI n W deg s)
    (hb : buckBf n s = true) : buckI n W deg (buckTw deg s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hbk⟩ := hI
  have hi : s.2.2.2.2 < n := by simpa [buckBf] using hb
  have hdi : deg[s.2.2.2.2]! < n := h5 _ hi
  have hdlen : deg[s.2.2.2.2]! < s.1.length := by omega
  have hsplen1 : s.2.2.2.1 < s.2.1.length := by omega
  have hsplen2 : s.2.2.2.1 < s.2.2.1.length := by omega
  have hpush := hbk.push (D' := larr deg) (x := s.2.2.2.2) (d := deg[s.2.2.2.2]!)
    (m' := s.2.2.2.2 + 1) hi (by omega) rfl (fun _ _ => rfl)
    (fun v hv => le_of_lt (h5 v (by omega))) (fun v hv hvx => by omega)
  simp only [buckI, buckTw]
  refine ⟨by simpa using h1, by simpa using h2, by simpa using h3, h4, h5, by omega,
    by omega, ?_⟩
  rw [larr_set hdlen, larr_set hsplen1, larr_set hsplen2]
  exact hpush

theorem buck_variant (n : ℕ) (deg : List ℕ) :
    LOOP_VARIANT (fun s => buckBf n s = true → buckP deg s) (buckBf n) (buckF deg)
      (fun s => n - s.2.2.2.2) :=
  variant_of_step (step := buckTw deg) (C := fun _ => buckC) (V := fun s => n - s.2.2.2.2)
    (fun s hP _ => buckF_le deg s hP)
    (fun s _ hb => by
      have hi : s.2.2.2.2 < n := by simpa [buckBf] using hb
      show n - (s.2.2.2.2 + 1) < n - s.2.2.2.2
      omega)

/-! ### 2.4 The pass, bounded and exported -/

theorem buckPass_le {n W : ℕ} {deg : List ℕ} :
    ∀ (fuel : ℕ) (s : BS), buckI n W deg s → n - s.2.2.2.2 < fuel →
      buckPass n deg s
        ≤ NRest.spec (fun t => buckI n W deg t ∧ buckBf n t = false)
            (fun _ => liftACost ((n - s.2.2.2.2) • iter buckC + cu Currency.«while»)) :=
  while_pot_le (P := buckP deg) (V := fun s => n - s.2.2.2.2)
    (Φ := fun s => (n - s.2.2.2.2) • iter buckC)
    (Φ' := fun s => (n - (s.2.2.2.2 + 1)) • iter buckC)
    (C := fun _ => buckC) (fun _ h hb => buckI_range h hb)
    (fun s h hb => by
      have hi : s.2.2.2.2 < n := by simpa [buckBf] using hb
      refine step_spec (s := s) (x := buckTw deg s) (C := fun _ => buckC)
        (Φ := fun s => (n - s.2.2.2.2) • iter buckC)
        (Φ' := fun s => (n - (s.2.2.2.2 + 1)) • iter buckC)
        (V := fun s => n - s.2.2.2.2) (buckF_le deg s (buckI_range h hb))
        (buckI_step h hb) ?_ ?_
      · show n - (s.2.2.2.2 + 1) < n - s.2.2.2.2
        omega
      · show (n - (s.2.2.2.2 + 1)) • iter buckC ≤ (n - (s.2.2.2.2 + 1)) • iter buckC
        exact le_rfl)
    (fun s _ hb => by
      have hi : s.2.2.2.2 < n := by simpa [buckBf] using hb
      show iter buckC + (n - (s.2.2.2.2 + 1)) • iter buckC ≤ (n - s.2.2.2.2) • iter buckC
      rw [show n - s.2.2.2.2 = (n - (s.2.2.2.2 + 1)) + 1 by omega, succ_nsmul]
      exact le_of_eq (by ac_rfl))

/-- **The bucket build's export.** From a zeroed head array the pass
leaves `RamElim.Buck n n` — the relation the elimination loop carries —
with the arena pointer at `n + 1`. -/
theorem buckPass_spec {n W : ℕ} {deg bh₀ bv₀ bn₀ : List ℕ} (hd : deg.length = n)
    (hD : ∀ v < n, deg[v]! < n) (hbh : bh₀.length = n + 1) (hbh0 : ∀ j ≤ n, bh₀[j]! = 0)
    (hbv : bv₀.length = n + W + 1) (hbn : bn₀.length = n + W + 1) :
    buckPass n deg (bh₀, bv₀, bn₀, 1, 0)
      ≤ NRest.spec
          (fun t : BS => t.1.length = n + 1 ∧ t.2.1.length = n + W + 1 ∧
            t.2.2.1.length = n + W + 1 ∧ t.2.2.2.1 = n + 1 ∧ t.2.2.2.2 = n ∧
            RamElim.Buck n n (fun _ => 0) (larr deg) (larr t.1) (larr t.2.1) (larr t.2.2.1)
              (n + 1) n)
          (fun _ => liftACost (n • iter buckC + cu Currency.«while»)) := by
  have hI0 : buckI n W deg (bh₀, bv₀, bn₀, 1, 0) := by
    refine ⟨hbh, hbv, hbn, hd, hD, Nat.zero_le n, rfl, ?_⟩
    show RamElim.Buck n 0 (fun _ => 0) (larr deg) (larr bh₀) (larr bv₀) (larr bn₀) 1 0
    refine ⟨Nat.zero_lt_one, fun d hdn => ?_, fun p hp hps => absurd hps (by omega),
      fun p hp hps => absurd hps (by omega), fun v hv => absurd hv (by omega),
      fun v hv => absurd hv (by omega), ?_⟩
    · show bh₀[d]! < 1
      rw [hbh0 d hdn]; omega
    · refine (Finset.sum_eq_zero fun d hdm => ?_).symm
      show (RamElim.chain (larr bn₀) (larr bh₀ d)).length = 0
      rw [larr_apply, hbh0 d (by have := Finset.mem_range.1 hdm; omega), RamElim.chain_zero]
      simp
  refine le_trans (buckPass_le (n + 1) (bh₀, bv₀, bn₀, 1, 0) hI0 (by simp)) (spec_mono ?_ ?_)
  · rintro t ⟨⟨t1, t2, t3, -, -, t6, t7, tbk⟩, hbf⟩
    have hti : t.2.2.2.2 = n := by
      have : ¬ t.2.2.2.2 < n := by simpa [buckBf] using hbf
      omega
    rw [hti] at tbk t7
    refine ⟨t1, t2, t3, by omega, hti, ?_⟩
    rw [← t7]
    exact tbk
  · intro _ _
    simp

/-! ### 2.5 The synthesis -/

set_option maxHeartbeats 1000000 in
sepref_synth buckSynth (n : ℕ) (deg bh₀ bv₀ bn₀ : List ℕ) (sp₀ i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (bh₀, bv₀, bn₀, sp₀, i₀) ("bh", "bv", "bn", "sp", "i") ∗
      hnCtxt arrayAssn deg "deg" ∗ hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "d" ∗ junkCell "bhd")
    _ _ ("bh", "bv", "bn", "sp", "i")
    (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (buckPass n deg (bh₀, bv₀, bn₀, sp₀, i₀))

-- The synthesized bucket build, pinned: `RamElim.initBuckRow` — its
-- `push` inlined — instruction for instruction, minus the `ls` bump
-- that 2B′/D-a drops.
#guard buckSynth_impl =
  Com.while (Cond.lt (Operand.cell "i") (Operand.cell "n"))
    ((Com.aget "d" "deg" "i").seq
      ((Com.aget "bhd" "bh" "d").seq
        ((Com.aset "bv" "sp" "i").seq
          ((Com.aset "bn" "sp" "bhd").seq
            ((Com.aset "bh" "d" "sp").seq
              ((Com.binop Lax13Proofs.Imp.Bop.add "sp" "sp" "one").seq
                ((Com.binop Lax13Proofs.Imp.Bop.add "i" "i" "one").seq
                  (Com.skip.seq (Com.skip.seq (Com.skip.seq Com.skip))))))))))

-- **Negative control on the pin**: the head is read into `bhd` *before*
-- `bh[d]` is written, so a program that wrote first is a different one.
#guard buckSynth_impl ≠
  Com.while (Cond.lt (Operand.cell "i") (Operand.cell "n"))
    ((Com.aget "d" "deg" "i").seq
      ((Com.aset "bh" "d" "sp").seq
        ((Com.aget "bhd" "bh" "d").seq
          ((Com.aset "bv" "sp" "i").seq
            ((Com.aset "bn" "sp" "bhd").seq
              ((Com.binop Lax13Proofs.Imp.Bop.add "sp" "sp" "one").seq
                ((Com.binop Lax13Proofs.Imp.Bop.add "i" "i" "one").seq
                  (Com.skip.seq (Com.skip.seq (Com.skip.seq Com.skip))))))))))

/-- The bucket build's synthesis with its variant discharged. -/
theorem buckSynth' (n : ℕ) (deg bh₀ bv₀ bn₀ : List ℕ) (sp₀ i₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
        (bh₀, bv₀, bn₀, sp₀, i₀) ("bh", "bv", "bn", "sp", "i") ∗
        hnCtxt arrayAssn deg "deg" ∗ hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗
        junkCell "d" ∗ junkCell "bhd")
      buckSynth_impl Γ' ("bh", "bv", "bn", "sp", "i")
      (arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (buckPass n deg (bh₀, bv₀, bn₀, sp₀, i₀)) :=
  ⟨_, buckSynth n deg bh₀ bv₀ bn₀ sp₀ i₀⟩

end Bucket

/-! ## 3. The offset pass

`RamElim.offPass`: the recorded extraction degrees turned into block
offsets by a running sum, with each vertex's fill pointer set at the
start of its own block. Its whole content is `RamElim.psum`, and the
postcondition below is `RamElim.AfterOff`'s two `ioff`/`ifl` clauses at
the list layer. -/

section Offsets

/-- The offset pass's state: the offsets, the fill pointers, the running
sum, the counter. This is 2B's `offRowTw` state unchanged. -/
abbrev OS : Type := List ℕ × List ℕ × ℕ × ℕ

/-- Assemble a four-component state. -/
noncomputable def pack4o (IO FL : List ℕ) (s i : ℕ) : NRest OS ECost :=
  bindT (mopPair s i) fun p => bindT (mopPair FL p) fun q => mopPair IO q

/-- The pass's guard. -/
def offBf (n : ℕ) : OS → Bool := fun t => decide (t.2.2.2 < n)

/-- What one row needs in range. -/
def offP (idg : List ℕ) : OS → Prop := fun t =>
  t.2.2.2 < t.2.1.length ∧ t.2.2.2 < idg.length ∧ t.2.2.2 + 1 < t.1.length

/-- **One vertex's block, opened.** The old running sum goes into the
vertex's fill pointer *before* the sum moves — the in-place `+ idg[i]`
is `mopAddIn`, the shared counter operation. -/
noncomputable def offF (idg : List ℕ) : OS → NRest OS ECost := fun t =>
  bindT (mopAset t.2.1 t.2.2.2 t.2.2.1) fun FL =>
    bindT (mopAget idg t.2.2.2) fun di =>
      bindT (mopAddIn t.2.2.1 di) fun s' =>
        bindT (mopBinop .add t.2.2.2 1) fun ip =>
          bindT (mopAset t.1 ip s') fun IO =>
            bindT (mopSucc t.2.2.2) fun i => pack4o IO FL s' i

/-- **The offset pass.** -/
noncomputable def offPass (n : ℕ) (idg : List ℕ) (t₀ : OS) : NRest OS ECost :=
  irWhileIT (fun t => offBf n t = true → offP idg t) (offBf n) (offF idg) t₀

/-- One row's price. -/
def offC : ACost String ℕ := cu Currency.aset + cu Currency.aget + cu Currency.add
  + cu Currency.add + cu Currency.aset + cu Currency.add
  + cu Currency.skip + cu Currency.skip + cu Currency.skip

theorem offF_le (idg : List ℕ) (t : OS) (h : offP idg t) :
    offF idg t ≤ NRest.consume (NRest.returnT (offRowTw idg t)) (liftACost offC) := by
  refine le_of_eq ?_
  obtain ⟨h1, h2, h3⟩ := h
  simp only [offF, offRowTw, pack4o, mopAget_def, mopAset_def, mopSucc_eq, mopAddIn_eq,
    mopBinop_def, mopPair_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h3,
    NRest.returnT_bindT, NRest.bindT_consume NRest.addSupContinuousB_acost,
    NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, offC,
    liftACost_add, liftACost_cu]
  congr 1
  ac_rfl

/-- The offset pass's invariant: the running sum is the partial sum, the
blocks below the counter are open, and every fill pointer below it is at
the start of its own block. -/
def offI (n : ℕ) (idg : List ℕ) : OS → Prop := fun t =>
  t.1.length = n + 1 ∧ t.2.1.length = n ∧ idg.length = n ∧ t.2.2.2 ≤ n ∧
    t.2.2.1 = RamElim.psum (larr idg) t.2.2.2 ∧
    (∀ j ≤ t.2.2.2, t.1[j]! = RamElim.psum (larr idg) j) ∧
    (∀ j < t.2.2.2, t.2.1[j]! = RamElim.psum (larr idg) j)

theorem offI_range {n : ℕ} {idg : List ℕ} {t : OS} (hI : offI n idg t)
    (hb : offBf n t = true) : offP idg t := by
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := hI
  have hi : t.2.2.2 < n := by simpa [offBf] using hb
  exact ⟨by omega, by omega, by omega⟩

theorem offI_step {n : ℕ} {idg : List ℕ} {t : OS} (hI : offI n idg t)
    (hb : offBf n t = true) : offI n idg (offRowTw idg t) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  have hi : t.2.2.2 < n := by simpa [offBf] using hb
  have hiolen : t.2.2.2 + 1 < t.1.length := by omega
  have hfllen : t.2.2.2 < t.2.1.length := by omega
  have hsucc : t.2.2.1 + idg[t.2.2.2]! = RamElim.psum (larr idg) (t.2.2.2 + 1) := by
    rw [RamElim.psum_succ, h5, larr_apply]
  simp only [offI, offRowTw]
  refine ⟨by simpa using h1, by simpa using h2, h3, by omega, ?_, ?_, ?_⟩
  · show t.2.2.1 + idg[t.2.2.2]! = _
    exact hsucc
  · intro j hj
    show (t.1.set (t.2.2.2 + 1) (t.2.2.1 + idg[t.2.2.2]!))[j]! = _
    rw [get!_set _ _ _ _ hiolen]
    by_cases hje : j = t.2.2.2 + 1
    · rw [if_pos hje, hje]; exact hsucc
    · rw [if_neg hje]; exact h6 j (by omega)
  · intro j hj
    show (t.2.1.set t.2.2.2 t.2.2.1)[j]! = _
    rw [get!_set _ _ _ _ hfllen]
    by_cases hje : j = t.2.2.2
    · rw [if_pos hje, hje]; exact h5
    · rw [if_neg hje]; exact h7 j (by omega)

theorem off_variant (n : ℕ) (idg : List ℕ) :
    LOOP_VARIANT (fun t => offBf n t = true → offP idg t) (offBf n) (offF idg)
      (fun t => n - t.2.2.2) :=
  variant_of_step (step := offRowTw idg) (C := fun _ => offC) (V := fun t => n - t.2.2.2)
    (fun t hP _ => offF_le idg t hP)
    (fun t _ hb => by
      have hi : t.2.2.2 < n := by simpa [offBf] using hb
      show n - (t.2.2.2 + 1) < n - t.2.2.2
      omega)

theorem offPass_le {n : ℕ} {idg : List ℕ} :
    ∀ (fuel : ℕ) (t : OS), offI n idg t → n - t.2.2.2 < fuel →
      offPass n idg t
        ≤ NRest.spec (fun r => offI n idg r ∧ offBf n r = false)
            (fun _ => liftACost ((n - t.2.2.2) • iter offC + cu Currency.«while»)) :=
  while_pot_le (P := offP idg) (V := fun t => n - t.2.2.2)
    (Φ := fun t => (n - t.2.2.2) • iter offC) (Φ' := fun t => (n - (t.2.2.2 + 1)) • iter offC)
    (C := fun _ => offC) (fun _ h hb => offI_range h hb)
    (fun t h hb => by
      have hi : t.2.2.2 < n := by simpa [offBf] using hb
      refine step_spec (s := t) (x := offRowTw idg t) (C := fun _ => offC)
        (Φ := fun t => (n - t.2.2.2) • iter offC)
        (Φ' := fun t => (n - (t.2.2.2 + 1)) • iter offC)
        (V := fun t => n - t.2.2.2) (offF_le idg t (offI_range h hb)) (offI_step h hb) ?_ ?_
      · show n - (t.2.2.2 + 1) < n - t.2.2.2
        omega
      · show (n - (t.2.2.2 + 1)) • iter offC ≤ (n - (t.2.2.2 + 1)) • iter offC
        exact le_rfl)
    (fun t _ hb => by
      have hi : t.2.2.2 < n := by simpa [offBf] using hb
      show iter offC + (n - (t.2.2.2 + 1)) • iter offC ≤ (n - t.2.2.2) • iter offC
      rw [show n - t.2.2.2 = (n - (t.2.2.2 + 1)) + 1 by omega, succ_nsmul]
      exact le_of_eq (by ac_rfl))

/-- **The offset pass's export**, in `RamElim.AfterOff`'s vocabulary:
every block is opened at the partial sum before it, and every fill
pointer stands at the start of its own block. -/
theorem offPass_spec {n : ℕ} {idg ioff₀ ifl₀ : List ℕ} (hd : idg.length = n)
    (hio : ioff₀.length = n + 1) (hio0 : ioff₀[0]! = 0) (hfl : ifl₀.length = n) :
    offPass n idg (ioff₀, ifl₀, 0, 0)
      ≤ NRest.spec
          (fun t : OS => t.1.length = n + 1 ∧ t.2.1.length = n ∧
            (∀ j ≤ n, t.1[j]! = RamElim.psum (larr idg) j) ∧
            (∀ j < n, t.2.1[j]! = RamElim.psum (larr idg) j))
          (fun _ => liftACost (n • iter offC + cu Currency.«while»)) := by
  have hI0 : offI n idg (ioff₀, ifl₀, 0, 0) := by
    refine ⟨hio, hfl, hd, Nat.zero_le n, by simp [RamElim.psum], ?_, ?_⟩
    · intro j hj
      show ioff₀[j]! = _
      have hj0 : j = 0 := by simpa using hj
      rw [hj0, hio0, RamElim.psum]
      simp
    · intro j hj
      exact absurd (show j < 0 by simpa using hj) (by omega)
  refine le_trans (offPass_le (n + 1) (ioff₀, ifl₀, 0, 0) hI0 (by simp)) (spec_mono ?_ ?_)
  · rintro t ⟨⟨t1, t2, -, t4, -, t6, t7⟩, hbf⟩
    have hti : t.2.2.2 = n := by
      have : ¬ t.2.2.2 < n := by simpa [offBf] using hbf
      omega
    exact ⟨t1, t2, fun j hj => t6 j (by omega), fun j hj => t7 j (by omega)⟩
  · intro _ _
    simp

/-! ### 3.1 The synthesis -/

set_option maxHeartbeats 1000000 in
sepref_synth offSynth (n : ℕ) (idg ioff₀ ifl₀ : List ℕ) (s₀ i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (ioff₀, ifl₀, s₀, i₀) ("ioff", "ifl", "s", "i") ∗
      hnCtxt arrayAssn idg "idg" ∗ hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "di" ∗ junkCell "ip")
    _ _ ("ioff", "ifl", "s", "i")
    (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
    (offPass n idg (ioff₀, ifl₀, s₀, i₀))

-- The synthesized offset pass, pinned: `RamElim.offRow` instruction for
-- instruction, with the one three-address split R2C/D-b records (the
-- index `i + 1` is a cell).
#guard offSynth_impl =
  Com.while (Cond.lt (Operand.cell "i") (Operand.cell "n"))
    ((Com.aset "ifl" "i" "s").seq
      ((Com.aget "di" "idg" "i").seq
        ((Com.binop Lax13Proofs.Imp.Bop.add "s" "s" "di").seq
          ((Com.binop Lax13Proofs.Imp.Bop.add "ip" "i" "one").seq
            ((Com.aset "ioff" "ip" "s").seq
              ((Com.binop Lax13Proofs.Imp.Bop.add "i" "i" "one").seq
                (Com.skip.seq (Com.skip.seq Com.skip))))))))

/-- The offset pass's synthesis with its variant discharged. -/
theorem offSynth' (n : ℕ) (idg ioff₀ ifl₀ : List ℕ) (s₀ i₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
        (ioff₀, ifl₀, s₀, i₀) ("ioff", "ifl", "s", "i") ∗
        hnCtxt arrayAssn idg "idg" ∗ hnCtxt natAssn n "n" ∗ hnCtxt natAssn 1 "one" ∗
        junkCell "di" ∗ junkCell "ip")
      offSynth_impl Γ' ("ioff", "ifl", "s", "i")
      (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (offPass n idg (ioff₀, ifl₀, s₀, i₀)) :=
  ⟨_, offSynth n idg ioff₀ ifl₀ s₀ i₀⟩

end Offsets

/-! ## 4. The fill pass

`RamElim.fillPass`: a second walk of the block structure, writing each
arc into the block of the endpoint of *larger* rank — the one
eliminated first. Two loops, the inner one in the middle of the outer
body, with a two-armed branch that writes **both** state arrays: the
exact shape 2B measured as not translating (2B/D-a) and 2C isolated as
the remaining variable (its F1). It translates. -/

section Fill

/-- The fill's state: the in-lists, the fill pointers, the index. The
outer loop's index is a vertex, the inner loop's a slot. -/
abbrev FS : Type := List ℕ × List ℕ × ℕ

/-- Assemble a three-component state. -/
noncomputable def pack3f (IT FL : List ℕ) (j : ℕ) : NRest FS ECost :=
  bindT (mopPair FL j) fun p => mopPair IT p

/-- **One slot of the fill**, as a function, with the conjunction of
2B's `fillSlotTw` spelled as the nested branch the IR's `Cond` forces,
and the row's own rank hoisted into `ri` (2B′/D-d: the machine reads
`rnk[i]` once per slot, this reads it once per row — cost-only). -/
def fillStep (tgt alv rnk : List ℕ) (i ri : ℕ) : FS → FS := fun t =>
  if 0 < alv[tgt[t.2.2]!]! then
    if rnk[tgt[t.2.2]!]! < ri then
      (t.1.set t.2.1[i]! tgt[t.2.2]!, t.2.1.set i (t.2.1[i]! + 1), t.2.2 + 1)
    else (t.1, t.2.1, t.2.2 + 1)
  else (t.1, t.2.1, t.2.2 + 1)

/-- …and it is 2B's slot, at the row's own rank. -/
theorem fillStep_eq (tgt alv rnk : List ℕ) (i : ℕ) (t : FS) :
    fillStep tgt alv rnk i rnk[i]! t = fillSlotTw tgt alv rnk i t := by
  simp only [fillStep, fillSlotTw]
  by_cases h1 : 0 < alv[tgt[t.2.2]!]!
  · by_cases h2 : rnk[tgt[t.2.2]!]! < rnk[i]!
    · rw [if_pos h1, if_pos h2, if_pos (And.intro h1 h2)]
    · rw [if_pos h1, if_neg h2, if_neg (fun h : _ ∧ _ => h2 h.2)]
  · rw [if_neg h1, if_neg (fun h : _ ∧ _ => h1 h.1)]

/-- The row scan's guard. -/
def fillBf (jend : ℕ) : FS → Bool := fun t => decide (t.2.2 < jend)

/-- What one slot needs in range. -/
def fillP (tgt alv rnk : List ℕ) (i : ℕ) : FS → Prop := fun t =>
  t.2.2 < tgt.length ∧ tgt[t.2.2]! < alv.length ∧ tgt[t.2.2]! < rnk.length ∧
    i < t.2.1.length ∧ t.2.1[i]! < t.1.length

/-- **One slot of the fill.** -/
noncomputable def fillF (tgt alv rnk : List ℕ) (i ri : ℕ) : FS → NRest FS ECost := fun t =>
  bindT (mopAget tgt t.2.2) fun u =>
    bindT (mopAget alv u) fun au =>
      bindT (irIf (decide (0 < au))
          (bindT (mopAget rnk u) fun ru =>
            irIf (decide (ru < ri))
              (bindT (mopAget t.2.1 i) fun p =>
                bindT (mopAset t.1 p u) fun IT =>
                  bindT (mopSucc p) fun p' =>
                    bindT (mopAset t.2.1 i p') fun FL => mopPair IT FL)
              (mopPair t.1 t.2.1))
          (mopPair t.1 t.2.1)) fun r =>
        bindT (mopSucc t.2.2) fun j => pack3f r.1 r.2 j

/-- **The fill's row scan.** -/
noncomputable def fillScan (tgt alv rnk : List ℕ) (i ri jend : ℕ) (t₀ : FS) :
    NRest FS ECost :=
  irWhileIT (fun t => fillBf jend t = true → fillP tgt alv rnk i t) (fillBf jend)
    (fillF tgt alv rnk i ri) t₀

/-- The outer pass's guard. -/
def fillRowBf (n : ℕ) : FS → Bool := fun t => decide (t.2.2 < n)

/-- What one row needs in range. -/
def fillRowP (n : ℕ) (off alv rnk : List ℕ) : FS → Prop := fun t =>
  t.2.2 < alv.length ∧ t.2.2 < rnk.length ∧ t.2.2 < off.length ∧ t.2.2 + 1 < off.length

/-- **One vertex's in-neighbours, written out.** A dead vertex carries
no arcs, so its row is not scanned. -/
noncomputable def fillRowF (n : ℕ) (off tgt alv rnk : List ℕ) : FS → NRest FS ECost :=
  fun t =>
    bindT (mopAget alv t.2.2) fun ai =>
      bindT (irIf (decide (0 < ai))
          (bindT (mopAget rnk t.2.2) fun ri =>
            bindT (mopAget off t.2.2) fun j0 =>
              bindT (mopBinop .add t.2.2 1) fun ip =>
                bindT (mopAget off ip) fun jend =>
                  bindT (pack3f t.1 t.2.1 j0) fun z =>
                    bindT (fillScan tgt alv rnk t.2.2 ri jend z) fun r =>
                      mopPair r.1 r.2.1)
          (mopPair t.1 t.2.1)) fun r =>
        bindT (mopSucc t.2.2) fun i => pack3f r.1 r.2 i

/-- **The fill pass.** -/
noncomputable def fillPass (n : ℕ) (off tgt alv rnk : List ℕ) (t₀ : FS) : NRest FS ECost :=
  irWhileIT (fun t => fillRowBf n t = true → fillRowP n off alv rnk t) (fillRowBf n)
    (fillRowF n off tgt alv rnk) t₀

/-! ### 4.1 The prices -/

/-- What every slot of the fill pays. -/
def fillC0 : ACost String ℕ := cu Currency.aget + cu Currency.aget + cu Currency.ite
  + cu Currency.skip + cu Currency.add + cu Currency.skip + cu Currency.skip

/-- …a slot whose target is alive pays the rank read and the second
branch on top… -/
def fillC1 : ACost String ℕ := fillC0 + (cu Currency.aget + cu Currency.ite)

/-- …and the slot that actually writes an arc pays the pointer read,
the two writes and the bump. -/
def fillC : ACost String ℕ := fillC1 + (cu Currency.aget + cu Currency.aset
  + cu Currency.add + cu Currency.aset)

/-- One row of the fill, everything outside the scan — including the
scan loop's own entry test. -/
def fillRowC : ACost String ℕ := cu Currency.aget + cu Currency.ite + cu Currency.aget
  + cu Currency.aget + cu Currency.add + cu Currency.aget + cu Currency.skip
  + cu Currency.skip + cu Currency.«while» + cu Currency.skip + cu Currency.add
  + cu Currency.skip + cu Currency.skip

theorem fillF_le (tgt alv rnk : List ℕ) (i ri : ℕ) (t : FS) (h : fillP tgt alv rnk i t) :
    fillF tgt alv rnk i ri t
      ≤ NRest.consume (NRest.returnT (fillStep tgt alv rnk i ri t)) (liftACost fillC) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have base1 : liftACost fillC1 ≤ liftACost fillC := by
    rw [fillC, liftACost_add]; exact cost_le_add _ _
  have base : liftACost fillC0 ≤ liftACost fillC :=
    le_trans (by rw [fillC1, liftACost_add]; exact cost_le_add _ _) base1
  by_cases hb1 : 0 < alv[tgt[t.2.2]!]!
  · by_cases hb2 : rnk[tgt[t.2.2]!]! < ri
    · refine le_of_eq ?_
      simp only [fillF, fillStep, pack3f, mopAget_def, mopAset_def, mopSucc_eq, mopBinop_def,
        mopPair_def, irIf_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h3,
        NRest.assert_pos h4, NRest.assert_pos h5, NRest.returnT_bindT,
        NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
        Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, decide_eq_true_eq, if_pos hb1,
        if_pos hb2, fillC, fillC1, fillC0, liftACost_add, liftACost_cu]
      congr 1
      ac_rfl
    · simp only [fillF, fillStep, pack3f, mopAget_def, mopSucc_eq, mopBinop_def, mopPair_def,
        irIf_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h3,
        NRest.returnT_bindT, NRest.bindT_consume NRest.addSupContinuousB_acost,
        NRest.consume_consume, Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add,
        decide_eq_true_eq, if_pos hb1, if_neg hb2]
      refine NRest.consume_mono le_rfl (le_trans (le_of_eq ?_) base1)
      simp only [fillC1, fillC0, liftACost_add, liftACost_cu]
      ac_rfl
  · simp only [fillF, fillStep, pack3f, mopAget_def, mopSucc_eq, mopBinop_def, mopPair_def,
      irIf_def, NRest.assert_pos h1, NRest.assert_pos h2, NRest.returnT_bindT,
      NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.consume_consume,
      Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, decide_eq_true_eq, if_neg hb1]
    refine NRest.consume_mono le_rfl (le_trans (le_of_eq ?_) base)
    simp only [fillC0, liftACost_add, liftACost_cu]
    ac_rfl

/-! ### 4.2 The synthesis -/

set_option maxHeartbeats 1000000 in
sepref_synth fillScanSynth (tgt alv rnk : List ℕ) (i ri jend : ℕ)
    (itg₀ ifl₀ : List ℕ) (j₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ natAssn) (itg₀, ifl₀, j₀)
      ("itg", "ifl", "j") ∗
      hnCtxt arrayAssn tgt "tgt" ∗ hnCtxt arrayAssn alv "alv" ∗
      hnCtxt arrayAssn rnk "rnk" ∗ hnCtxt natAssn i "i" ∗ hnCtxt natAssn ri "ri" ∗
      hnCtxt natAssn jend "jend" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "u" ∗ junkCell "au" ∗ junkCell "ru" ∗ junkCell "p")
    _ _ ("itg", "ifl", "j") (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
    (fillScan tgt alv rnk i ri jend (itg₀, ifl₀, j₀))

set_option maxHeartbeats 4000000 in
sepref_synth fillSynth (n : ℕ) (off tgt alv rnk : List ℕ) (itg₀ ifl₀ : List ℕ) (i₀ : ℕ) :
  hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ natAssn) (itg₀, ifl₀, i₀)
      ("itg", "ifl", "i") ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
      hnCtxt arrayAssn alv "alv" ∗ hnCtxt arrayAssn rnk "rnk" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
      junkCell "ai" ∗ junkCell "ri" ∗ junkCell "j" ∗ junkCell "ip" ∗ junkCell "jend" ∗
      junkCell "u" ∗ junkCell "au" ∗ junkCell "ru" ∗ junkCell "p")
    _ _ ("itg", "ifl", "i") (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
    (fillPass n off tgt alv rnk (itg₀, ifl₀, i₀))

-- The synthesized row scan of the fill, pinned: `RamElim.fillSlot`
-- instruction for instruction, with the row's rank hoisted (2B′/D-d).
#guard fillScanSynth_impl =
  Com.while (Cond.lt (Operand.cell "j") (Operand.cell "jend"))
    ((Com.aget "u" "tgt" "j").seq
      ((Com.aget "au" "alv" "u").seq
        ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "au"))
              ((Com.aget "ru" "rnk" "u").seq
                (Com.ite (Cond.lt (Operand.cell "ru") (Operand.cell "ri"))
                  ((Com.aget "p" "ifl" "i").seq
                    ((Com.aset "itg" "p" "u").seq
                      ((Com.binop Lax13Proofs.Imp.Bop.add "p" "p" "one").seq ((Com.aset "ifl" "i" "p").seq Com.skip))))
                  Com.skip))
              Com.skip).seq
          ((Com.binop Lax13Proofs.Imp.Bop.add "j" "j" "one").seq (Com.skip.seq Com.skip)))))

-- **The whole fill pass, pinned** — outer loop, inner loop in the
-- middle of the body, and a two-armed branch whose `then` arm writes
-- *both* arrays of the enclosing loop's state. This is the goal
-- satellite 2B measured as not translating at 4 000 000 heartbeats
-- (2B/D-a) and 2C isolated the variable of (its F1); after tool wave T1
-- it translates.
#guard fillSynth_impl =
  Com.while (Cond.lt (Operand.cell "i") (Operand.cell "n"))
    ((Com.aget "ai" "alv" "i").seq
      ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "ai"))
            ((Com.aget "ri" "rnk" "i").seq
              ((Com.aget "j" "off" "i").seq
                ((Com.binop Lax13Proofs.Imp.Bop.add "ip" "i" "one").seq
                  ((Com.aget "jend" "off" "ip").seq
                    ((Com.skip.seq Com.skip).seq
                      ((Com.while (Cond.lt (Operand.cell "j") (Operand.cell "jend"))
                            ((Com.aget "u" "tgt" "j").seq
                              ((Com.aget "au" "alv" "u").seq
                                ((Com.ite (Cond.lt (Operand.cell "zero") (Operand.cell "au"))
                                      ((Com.aget "ru" "rnk" "u").seq
                                        (Com.ite (Cond.lt (Operand.cell "ru") (Operand.cell "ri"))
                                          ((Com.aget "p" "ifl" "i").seq
                                            ((Com.aset "itg" "p" "u").seq
                                              ((Com.binop Lax13Proofs.Imp.Bop.add "p" "p" "one").seq
                                                ((Com.aset "ifl" "i" "p").seq Com.skip))))
                                          Com.skip))
                                      Com.skip).seq
                                  ((Com.binop Lax13Proofs.Imp.Bop.add "j" "j" "one").seq
                                    (Com.skip.seq Com.skip)))))).seq
                        Com.skip))))))
            Com.skip).seq
        ((Com.binop Lax13Proofs.Imp.Bop.add "i" "i" "one").seq (Com.skip.seq Com.skip))))

/-- The fill pass's synthesis, with the tool's frame left existential. -/
theorem fillSynth' (n : ℕ) (off tgt alv rnk itg₀ ifl₀ : List ℕ) (i₀ : ℕ) :
    ∃ Γ', hnRefine (hnCtxt (arrayAssn ×ₐ arrayAssn ×ₐ natAssn) (itg₀, ifl₀, i₀)
        ("itg", "ifl", "i") ∗
        hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
        hnCtxt arrayAssn alv "alv" ∗ hnCtxt arrayAssn rnk "rnk" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "zero" ∗
        junkCell "ai" ∗ junkCell "ri" ∗ junkCell "j" ∗ junkCell "ip" ∗ junkCell "jend" ∗
        junkCell "u" ∗ junkCell "au" ∗ junkCell "ru" ∗ junkCell "p")
      fillSynth_impl Γ' ("itg", "ifl", "i") (arrayAssn ×ₐ arrayAssn ×ₐ natAssn)
      (fillPass n off tgt alv rnk (itg₀, ifl₀, i₀)) :=
  ⟨_, fillSynth n off tgt alv rnk itg₀ ifl₀ i₀⟩

/-! ### 4.3 Debt F1 — the fill pass's postcondition

`RamElim.fillPass_spec` establishes `InCsr`: every block holds exactly
the in-neighbours of its vertex in the elimination orientation. Its
mathematics — `written`, `written_succ_of_take`, `not_mem_written` (the
`CsrSimple` `nodup` clause spent again), `written_last`, `inN_of_dead`,
`exists_block` — is stated over functions `ℕ → ℕ` and so is consumed by
`larr` verbatim; what is missing is the two loops' invariants
(`FillSt`/`FillScanInv` at the list layer) and the amortized bound over
the rows tiling the target array, which is `degPass_le`'s two-currency
energy with `fillRowC`/`fillC` in place of `degRowC`/`degC`. The
programs, their per-iteration accounts and the synthesized `Com` are
here; the walk is not. -/

end Fill

/-! ## 5. The two flat passes' costs, cashed

The constants are **computed** from the per-iteration accounts by
`decide +kernel`, not tuned.

**2B′/F-a — the state-as-resource discipline has a price, and it is one
`skip` per component per iteration.** 2B's degree pass came out *below*
the hand-walked baseline (`36 n + 23 ns + 4` against `48 n + 44 ns +
10`) because its state has two components. These two passes have five
and four, and they come out **above** it: `31 n + 4` against the
baseline's `29 n + 10` for the bucket build, `28 n + 4` against `24 n +
12` for the offsets. The whole difference is `mopPair`: a loop state of
`k` components is assembled by `k − 1` `mopPair`s, each compiling to
`Com.skip` and costing one IMP+ time unit, on **every** iteration. The
machine program does not pay it because its state *is* the store. This
is not a defect of any of the three passes — it is the standing cost of
`hnr_while_var` reading a loop's state off one `hnCtxt` conjunct
(P4/D-m), it is linear in the state width, and it is the number a future
tower wave that wants a multi-conjunct loop rule should be measured
against. -/

section Cash

/-- **The bucket build's cost**: `31·n + 4` IMP+ time units, against the
baseline's `29·n + 10` (`RamElim.implements`'s `w2`); the difference is
the four `mopPair` skips of the five-component state (F-a). -/
def buckK (n : ℕ) : ℕ := 31 * n + 4

theorem cash_buckBudget (n : ℕ) :
    Codegen.cash (n • iter buckC + cu Currency.«while») = buckK n := by
  rw [Codegen.cash_add, BfsQSynth.cash_nsmul,
    show Codegen.cash (iter buckC) = 31 from by decide +kernel,
    show Codegen.cash (cu Currency.«while») = 4 from by decide +kernel, buckK]
  ring

/-- **The offset pass's cost**: `28·n + 4` IMP+ time units, against the
baseline's `24·n + 12` (`RamElim.implements`'s `w4`). -/
def offK (n : ℕ) : ℕ := 28 * n + 4

theorem cash_offBudget (n : ℕ) :
    Codegen.cash (n • iter offC + cu Currency.«while») = offK n := by
  rw [Codegen.cash_add, BfsQSynth.cash_nsmul,
    show Codegen.cash (iter offC) = 28 from by decide +kernel,
    show Codegen.cash (cu Currency.«while») = 4 from by decide +kernel, offK]
  ring

-- the two figures side by side at the demo's size, with the sign of
-- the difference recorded rather than assumed (F-a)
#guard buckK 5 = 159
#guard 29 * 5 + 10 = 155
#guard offK 5 = 144
#guard 24 * 5 + 12 = 132

/-- The fill pass's per-slot and per-row accounts, cashed — the two
constants the pass's amortized bound is built from. -/
theorem cash_fillC : Codegen.cash (iter fillC) = 41 := by decide +kernel

theorem cash_fillRowC : Codegen.cash (iter fillRowC) = 37 := by decide +kernel

end Cash

/-! ## 6. Axioms -/

/-- info: 'Lax3Proofs.Refine.ElimSynth2.buckPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms buckPass_spec

/-- info: 'Lax3Proofs.Refine.ElimSynth2.offPass_spec' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms offPass_spec

/-- info: 'Lax3Proofs.Refine.ElimSynth2.buckSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms buckSynth

/-- info: 'Lax3Proofs.Refine.ElimSynth2.offSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms offSynth

/-- info: 'Lax3Proofs.Refine.ElimSynth2.fillSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms fillSynth

end Lax3Proofs.Refine.ElimSynth2
