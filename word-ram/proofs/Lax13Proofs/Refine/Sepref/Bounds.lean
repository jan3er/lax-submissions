import Lax13Proofs.Refine.Sepref.Definition
import Lax13Proofs.Refine.Codegen.Cash

/-!
# `BRefine` — the bounds half of a synthesis (promoted), and its tooling

ND-MC rebase tool wave T2. The `BRefine` judgment was built by the P0.2
spike (`Sepref/Examples/WordAssnSpike.lean` §4) as the answer to R2/D-b:
what the bounds pass needs is not a bounded assertion but a **second
component of the judgment** that transports `Ir.bpre` alongside the
synthesis. Three engine waves then consumed it from the spike file and
measured the tool debts this file pays.

## Judgment calls (T2 ledger)

**T2/D-a — the core is promoted here; the spike re-exports.** Every
name keeps its spike-era full identifier
(`Lax13Proofs.Refine.Sepref.WordSpike.*`): the ND-MC satellites import
the spike path and `open … WordSpike`, and the promotion must not move
a single consumer. So this file declares into the same `WordSpike`
namespace and the spike imports it; nothing else changes. §1–§2 are
the spike's §4, verbatim.

**T2/D-b — the nested-`while` rules.** `BRefine.while_guard` proves a
loop at *its own* `LoopAssn`; a loop inside another loop's body needs
(i) its assertion entered from whatever the outer body holds at that
point, (ii) the cells the inner loop does not touch framed around it,
and (iii) its exit *re-opened* — the continuation must learn which
abstract state the inner loop stopped at and that its guard is false.
`ExitAssn` is the exit shape, `BRefine.while_nested` is (i)+(ii)+(iii)
packaged at a `.while` command, and `BRefine.while_seq` is the form a
body actually contains — `(.while b c).seq d` — with the continuation
entered per exit state. This is AugmentSynth §10 gap 3 and ElimSynth3
§5 debt E3: every two-level engine pass was blocked on exactly this.
Exercised on the counting-pass shape in `Examples/BoundsProbe.lean`.

**T2/D-c — junk-cell rules.** A scratch cell is `junkCell` in a loop
assertion, and `BRefine` had only `pre_ex` to open it — so every loop
carried its scratch values as an n-tuple existential and paid ~20
lines of open/close per body (ScatterSynth's seven-tuple `markΓ`,
AugmentSynth's four-tuple `prefΓ`). `BRefine.pre_junk` opens one junk
cell directly, and the `*_junk` op rules consume a junk *destination*
with no opening at all, which is what a loop-body derivation actually
wants: scratch enters junk, is written, and is weakened back to junk
at the close (`natAssn_entails_junkCell`, already a `fri_rules`
member).

**T2/D-d — the `sepref_brefine_rules` database and the `brefine`
driver.** The op rules below are tagged into the database
(`Sepref/Attrs.lean`), and the `brefine` tactic walks a `.seq` chain
emitting per-op the `BRefine.perm … (by sepref_ac) … ∘ BRefine.frame`
glue that AugmentSynth §10 gap 1 measures at ~150 hand lines per
engine: it matches the op's conjuncts with `Frame.frameMatch` (the
same matcher the synthesis driver uses), frames the remainder, opens
pure conjuncts (`pre_pure`) as it goes, and leaves exactly the goals a
human must own — arithmetic side conditions its fallback cannot close,
`while` sub-goals (whose invariants are proof ideas), and the final
entailment into the caller's loop assertion. A named assertion (a
`def` folding a `∗`-chain) is unfolded before matching, which also
retires the R2A/D-f illegibility for this driver's goals.

**T2/D-f — the run adapter (`BRefine_of_run`).** The 2A′ satellite's
R2A/D-l: composing `BRefine` through an *engine leaf* means passing an
assertion through a whole synthesized `Com`, and the tower's bound for
such a program exists as `bpre` facts and `BigStepB` runs, not as
`BRefine` rules — and `bpre` (all runs) versus the run a consumer
holds (one run) do not bridge syntactically. They bridge semantically:
`Ir.BigStep` is deterministic, so **one bounded run pins every run**,
and `bpre_of_bigStepB` below turns a `BigStepB` derivation into
`Ir.bpre` at *any* postcondition the final state satisfies (the
`while` clause is re-established by `bpre_while_step`, with the
derivation's own loop-head states as the invariant). `BRefine_of_run`
packages it: an engine leaf is a `BRefine` as soon as, from every
state its precondition describes, some bounded run lands back in its
postcondition — which is exactly the ∃-form that
`exists_bigStepB_of_hnRefine` + the engine's own spec deliver. The
per-engine assembly (whose spec lemmas name the engine's arrays)
belongs to the engine waves; the bridge itself is here and gated.

Refute-before-prove: every new *reasoning* rule of this file has a
negative control in §7 (`no_bpre_nested` refutes through two loop
levels; `no_brefine_const_junk_at_bound` bites the junk rule's
creation site; `no_run_at_bound` shows the adapter's premise is not
manufacturable). The driver is MetaM code, exempt, and covered by
keeping every consumer green plus the gate examples it emits here.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

namespace WordSpike

/-! ## 1. `BRefine` — the component the bounds pass actually needs
(moved verbatim from the spike's §4; T2/D-a)

R2/D-b, built. `Codegen/Cash.lean` wants `∃ s' κ, Ir.BigStepB B c s₀ s' κ`,
and `BigStep.exists_bigStepB_of_inv` reduces that to `Ir.bpre B c Q s₀`.
`bpre` is *syntax-directed on the concrete `Com`*, exactly like
`hnRefine`'s translate phase, so it can be carried alongside the
judgment by rules of the same shape.

`BRefine B Γ c Γ'` is that second component, in continuation-passing
form: from any state the precondition holds of, under the state
invariant `Ir.StateBound B`, the residual bounds precondition holds.

**No `wordAssn` appears in it.** The abstract values are pinned by
ordinary `natAssn`/`arrayAssn` ownership — `natAssn m y` says the cell
`y` holds *exactly* `m`.

**R2/D-d — credits are threaded existentially, and the assertions must
be credit-free.** `bpre` knows nothing about credits, so the
continuation quantifies the balance. Every data assertion used with
`BRefine` must therefore own no `¤` conjunct; all of
`natAssn`/`arrayAssn`/`junkCell`/`junkArray` qualify. -/

/-- `BRefine B Γ c Γ'`: the `bpre` half of a synthesis. -/
def BRefine (B : ℕ) (Γ : Assn) (c : Com) (Γ' : Assn) : Prop :=
  ∀ (F : Assn) (Q : Ir.State → Prop) (s : Ir.State) (cr : ECost),
    irSTATE (Γ ∗ F) (s, cr) → Ir.StateBound B s →
    (∀ (s' : Ir.State) (cr' : ECost), irSTATE (Γ' ∗ F) (s', cr') →
      Ir.StateBound B s' → Q s') →
      Ir.bpre B c Q s

/-- Rewrite an `irSTATE` along an assertion equation — the `ac_rfl`
vehicle every op rule below permutes with. -/
theorem irSTATE_cong {P P' : Assn} {s : Ir.State} {cr : ECost} (he : P = P')
    (h : irSTATE P (s, cr)) : irSTATE P' (s, cr) := he ▸ h

/-- An entailment by permutation — the `BRefine.cons`/`loopAssn_intro`
vehicle (T2). -/
theorem entails_of_eq {P Q : Assn} (h : P = Q) : P ⊢ Q := by
  rw [h]

/-! The four extraction lemmas of `Ir/Assn.lean`, restated at the
`natAssn`/`arrayAssn` spelling. They are the same theorems (`natAssn` is
`↦ᵥ` by definition), but `ac_rfl` compares atoms *syntactically*, so a
permutation goal must be stated in one spelling throughout — the P7/D-ba
lesson, one layer down. -/

theorem natAssn_vars {x : String} {v : ℕ} {F : Assn} {s : Ir.State} {cr : ECost}
    (h : irSTATE (natAssn v x ∗ F) (s, cr)) : s.vars x = some v := Ir.ptoVar_vars h

theorem natAssn_setVar {x : String} {v n : ℕ} {F : Assn} {s : Ir.State} {cr : ECost}
    (h : irSTATE (natAssn v x ∗ F) (s, cr)) :
    irSTATE (natAssn n x ∗ F) (s.setVar x n, cr) := Ir.ptoVar_setVar h

theorem arrayAssn_arrs {a : String} {xs : List ℕ} {F : Assn} {s : Ir.State} {cr : ECost}
    (h : irSTATE (arrayAssn xs a ∗ F) (s, cr)) : s.arrs a = some xs := Ir.ptoArr_arrs h

theorem arrayAssn_setArr {a : String} {xs ys : List ℕ} {F : Assn} {s : Ir.State}
    {cr : ECost} (h : irSTATE (arrayAssn xs a ∗ F) (s, cr)) :
    irSTATE (arrayAssn ys a ∗ F) (s.setArr a ys, cr) := Ir.ptoArr_setArr h

/-- **The consumer.** A `BRefine` at the caller's own hole is exactly the
`bpre` witness `exists_bigStepB_of_hnRefine` asks for. -/
theorem bpre_of_BRefine {B : ℕ} {Γ Γ' F : Assn} {c : Com} {s : Ir.State} {cr : ECost}
    (h : BRefine B Γ c Γ') (hs : irSTATE (Γ ∗ F) (s, cr)) (hSB : Ir.StateBound B s) :
    Ir.bpre B c (fun _ => True) s :=
  h F (fun _ => True) s cr hs hSB (fun _ _ _ _ => trivial)

/-! ### Structural rules -/

theorem BRefine.cons {B : ℕ} {Γ Γ₀ Γ' Γ'₀ : Assn} {c : Com} (h : BRefine B Γ₀ c Γ'₀)
    (hpre : Γ ⊢ Γ₀) (hpost : Γ'₀ ⊢ Γ') : BRefine B Γ c Γ' := by
  intro F Q s cr hs hSB hQ
  refine h F Q s cr (start_entailsE hs (sepConj_mono_left hpre)) hSB ?_
  exact fun s' cr' hs' hSB' => hQ s' cr' (start_entailsE hs' (sepConj_mono_left hpost)) hSB'

theorem BRefine.frame {B : ℕ} {Γ Γ' D : Assn} {c : Com} (h : BRefine B Γ c Γ') :
    BRefine B (Γ ∗ D) c (Γ' ∗ D) := by
  intro F Q s cr hs hSB hQ
  refine h (D ∗ F) Q s cr (irSTATE_cong (by ac_rfl) hs) hSB ?_
  exact fun s' cr' hs' hSB' => hQ s' cr' (irSTATE_cong (by ac_rfl) hs') hSB'

theorem BRefine.perm {B : ℕ} {Γ P Γ' P' : Assn} {c : Com} (he : Γ = P) (he' : P' = Γ')
    (h : BRefine B P c P') : BRefine B Γ c Γ' := by rw [he, ← he']; exact h

/-- Extracting a pure conjunct from the precondition — how a store's own
in-range hypothesis reaches the next operation. -/
theorem BRefine.pre_pure {B : ℕ} {Φ : Prop} {Γ Γ' : Assn} {c : Com}
    (h : Φ → BRefine B Γ c Γ') : BRefine B (⌜Φ⌝ ∗ Γ) c Γ' := by
  intro F Q s cr hs hSB hQ
  rw [sepConj_assoc] at hs
  obtain ⟨hΦ, hs'⟩ := predLift_sepConj_iff.1 hs
  exact h hΦ F Q s cr hs' hSB hQ

/-- …and opening an existential (`junkCell`, `junkArray`). -/
theorem BRefine.pre_ex {β : Type} {B : ℕ} {Γ : β → Assn} {Γ' : Assn} {c : Com}
    (h : ∀ y, BRefine B (Γ y) c Γ') : BRefine B (∃ᵃ y, Γ y) c Γ' := by
  intro F Q s cr hs hSB hQ
  rw [sepEx_sepConj] at hs
  obtain ⟨y, hy⟩ := hs
  exact h y F Q s cr hy hSB hQ

theorem BRefine.skip {B : ℕ} {Γ : Assn} : BRefine B Γ .skip Γ :=
  fun _ _ _ _ hs hSB hQ => hQ _ _ hs hSB

theorem BRefine.seq {B : ℕ} {Γ Γ₁ Γ' : Assn} {c d : Com}
    (h₁ : BRefine B Γ c Γ₁) (h₂ : BRefine B Γ₁ d Γ') : BRefine B Γ (.seq c d) Γ' := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_seq]
  exact h₁ F _ s cr hs hSB fun s' cr' hs' hSB' => h₂ F Q s' cr' hs' hSB' hQ

/-! ### The operation rules

One per `BigStepB` constructor that has a residual (P7/D-bl's table).
Each is tagged `sepref_brefine_rules` (T2/D-d) so the `brefine` driver
below can find it; the tag order puts the in-place and junk-destination
forms first, which is the order a synthesized body's shapes actually
occur in. -/

/-- `x := n`: **the literal must fit**. -/
theorem BRefine.const {B : ℕ} {x : String} {n v : ℕ} (hn : n < B) :
    BRefine B (natAssn v x) (.const x n) (natAssn n x) := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_const]
  exact ⟨hn, hQ _ cr (natAssn_setVar hs) (hSB.setVar hn)⟩

/-- `x := y`: nothing is created. -/
theorem BRefine.copy {B : ℕ} {x y : String} {v w : ℕ} :
    BRefine B (natAssn v x ∗ natAssn w y) (.copy x y) (natAssn w x ∗ natAssn w y) := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_copy]
  intro w' hw'
  have hy : s.vars y = some w :=
    natAssn_vars (F := natAssn v x ∗ F) (irSTATE_cong (by ac_rfl) hs)
  obtain rfl : w = w' := Option.some.inj (hy ▸ hw')
  have h1 : irSTATE (natAssn v x ∗ (natAssn w y ∗ F)) (s, cr) := irSTATE_cong (by ac_rfl) hs
  have h2 := natAssn_setVar (n := w) h1
  exact hQ _ cr (irSTATE_cong (by ac_rfl) h2) (hSB.setVar (hSB.var hy))

/-- `x := y ⊕ z`: **the creation site**. The side condition is on the
*abstract* operands, which is where the abstract program's own loop
invariant is available — the whole content of the spike. -/
theorem BRefine.binop {B : ℕ} {op : Imp.Bop} {x y z : String} {v m n : ℕ}
    (hb : op.apply m n < B) :
    BRefine B (natAssn v x ∗ natAssn m y ∗ natAssn n z) (.binop op x y z)
      (natAssn (op.apply m n) x ∗ natAssn m y ∗ natAssn n z) := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_binop]
  intro m' n' hm' hn'
  have hy : s.vars y = some m :=
    natAssn_vars (F := natAssn v x ∗ natAssn n z ∗ F) (irSTATE_cong (by ac_rfl) hs)
  have hz : s.vars z = some n :=
    natAssn_vars (F := natAssn v x ∗ natAssn m y ∗ F) (irSTATE_cong (by ac_rfl) hs)
  obtain rfl : m = m' := Option.some.inj (hy ▸ hm')
  obtain rfl : n = n' := Option.some.inj (hz ▸ hn')
  have h1 : irSTATE (natAssn v x ∗ (natAssn m y ∗ natAssn n z ∗ F)) (s, cr) :=
    irSTATE_cong (by ac_rfl) hs
  have h2 := natAssn_setVar (n := op.apply m n) h1
  exact ⟨hb, hQ _ cr (irSTATE_cong (by ac_rfl) h2) (hSB.setVar hb)⟩

/-- `x := x ⊕ z`, in place (the `mopSucc` shape). -/
theorem BRefine.binop_self {B : ℕ} {op : Imp.Bop} {x z : String} {m n : ℕ}
    (hb : op.apply m n < B) :
    BRefine B (natAssn m x ∗ natAssn n z) (.binop op x x z)
      (natAssn (op.apply m n) x ∗ natAssn n z) := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_binop]
  intro m' n' hm' hn'
  have h0 : irSTATE (natAssn m x ∗ (natAssn n z ∗ F)) (s, cr) := irSTATE_cong (by ac_rfl) hs
  have hx : s.vars x = some m := natAssn_vars h0
  have hz : s.vars z = some n :=
    natAssn_vars (F := natAssn m x ∗ F) (irSTATE_cong (by ac_rfl) hs)
  obtain rfl : m = m' := Option.some.inj (hx ▸ hm')
  obtain rfl : n = n' := Option.some.inj (hz ▸ hn')
  have h2 := natAssn_setVar (n := op.apply m n) h0
  exact ⟨hb, hQ _ cr (irSTATE_cong (by ac_rfl) h2) (hSB.setVar hb)⟩

/-- `x := a[i]`: nothing is created — and the run *hands over*
`k < xs.length`, which is what makes the index facts free (P7/D-bl's
`aget` row). -/
theorem BRefine.aget {B : ℕ} {x a i : String} {v k : ℕ} {xs : List ℕ} :
    BRefine B (natAssn v x ∗ arrayAssn xs a ∗ natAssn k i) (.aget x a i)
      (⌜k < xs.length⌝ ∗ natAssn xs[k]! x ∗ arrayAssn xs a ∗ natAssn k i) := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_aget]
  intro k' ys w hk' hys hw
  have hi : s.vars i = some k :=
    natAssn_vars (F := natAssn v x ∗ arrayAssn xs a ∗ F) (irSTATE_cong (by ac_rfl) hs)
  have ha : s.arrs a = some xs :=
    arrayAssn_arrs (F := natAssn v x ∗ natAssn k i ∗ F) (irSTATE_cong (by ac_rfl) hs)
  obtain rfl : k = k' := Option.some.inj (hi ▸ hk')
  obtain rfl : xs = ys := Option.some.inj (ha ▸ hys)
  obtain ⟨hklen, rfl⟩ := List.getElem?_eq_some_iff.1 hw
  rw [← getElem!_pos xs k hklen] at hw ⊢
  have h1 : irSTATE (natAssn v x ∗ (arrayAssn xs a ∗ natAssn k i ∗ F)) (s, cr) :=
    irSTATE_cong (by ac_rfl) hs
  have h2 := natAssn_setVar (n := xs[k]!) h1
  refine hQ _ cr (irSTATE_cong ?_ h2) (hSB.setVar (hSB.getElem ha hw))
  rw [predLift_of_true hklen, emp_sepConj]
  ac_rfl

/-- `a[i] := v`: nothing is created, and the store's own in-range
hypothesis is **handed to the caller** — the row of P7/D-bl's table that
pays for the whole file, here delivered as a pure postcondition
conjunct. -/
theorem BRefine.aset {B : ℕ} {a i v : String} {k n : ℕ} {xs : List ℕ} :
    BRefine B (arrayAssn xs a ∗ natAssn k i ∗ natAssn n v) (.aset a i v)
      (⌜k < xs.length⌝ ∗ arrayAssn (xs.set k n) a ∗ natAssn k i ∗ natAssn n v) := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_aset]
  intro k' n' ys hk' hn' hys hklen
  have hi : s.vars i = some k :=
    natAssn_vars (F := arrayAssn xs a ∗ natAssn n v ∗ F) (irSTATE_cong (by ac_rfl) hs)
  have hv : s.vars v = some n :=
    natAssn_vars (F := arrayAssn xs a ∗ natAssn k i ∗ F) (irSTATE_cong (by ac_rfl) hs)
  have h0 : irSTATE (arrayAssn xs a ∗ (natAssn k i ∗ natAssn n v ∗ F)) (s, cr) :=
    irSTATE_cong (by ac_rfl) hs
  have ha : s.arrs a = some xs := arrayAssn_arrs h0
  obtain rfl : k = k' := Option.some.inj (hi ▸ hk')
  obtain rfl : n = n' := Option.some.inj (hv ▸ hn')
  obtain rfl : xs = ys := Option.some.inj (ha ▸ hys)
  have h2 := arrayAssn_setArr (ys := xs.set k n) h0
  refine hQ _ cr (irSTATE_cong ?_ h2) (hSB.setArr ha (hSB.var hv))
  rw [predLift_of_true hklen, emp_sepConj]
  ac_rfl

/-! ## 2. Control (moved verbatim; T2/D-a)

A loop's assertion is `LoopAssn I Γ`: the abstract state exists, the
abstract invariant holds of it, and the concrete assertion is at that
state. This is where the *abstract* program's own invariant — the one
the correctness wave already proved — is what supplies the word bounds,
rather than a second copy of them over `Ir.State`. -/

/-- The loop's assertion, over the abstract state. -/
def LoopAssn {σ : Type} (I : σ → Prop) (Γ : σ → Assn) : Assn := ∃ᵃ t, (⌜I t⌝ ∗ Γ t)

theorem loopAssn_intro {σ : Type} {I : σ → Prop} {Γ : σ → Assn} {t : σ}
    (hI : I t) : Γ t ⊢ LoopAssn I Γ := by
  intro p hp
  exact ⟨t, predLift_sepConj_iff.2 ⟨hI, hp⟩⟩

/-- A branch: the guard's literals must fit, and both arms must reach the
same postcondition (merge by `BRefine.cons`, as the frame layer's
`MERGE` does). -/
theorem BRefine.ite {B : ℕ} {Γ Γ' : Assn} {b : Cond} {c d : Com}
    (hlit : b.LitLt B) (ht : BRefine B Γ c Γ') (he : BRefine B Γ d Γ') :
    BRefine B Γ (.ite b c d) Γ' := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_ite]
  exact ⟨fun _ hev => Ir.Cond.evalB_of_stateBound hSB hlit hev,
    fun _ => ht F Q s cr hs hSB hQ, fun _ => he F Q s cr hs hSB hQ⟩

/-- A loop: the guard's literals must fit and the body must preserve the
loop assertion. **No variant** — termination comes from the run
(P7/D-bl's `while` row, and R0/D-b at the synthesis layer). -/
theorem BRefine.while {B : ℕ} {σ : Type} {I : σ → Prop} {Γ : σ → Assn} {Γ' : Assn}
    {b : Cond} {c : Com} (hlit : b.LitLt B)
    (hbody : BRefine B (LoopAssn I Γ) c (LoopAssn I Γ))
    (hexit : LoopAssn I Γ ⊢ Γ') :
    BRefine B (LoopAssn I Γ) (.while b c) Γ' := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_while]
  refine ⟨fun t => (∃ cr', irSTATE (LoopAssn I Γ ∗ F) (t, cr')) ∧ Ir.StateBound B t,
    ⟨⟨cr, hs⟩, hSB⟩, ?_, ?_, ?_⟩
  · exact fun t _ hInv hev => Ir.Cond.evalB_of_stateBound hInv.2 hlit hev
  · rintro t ⟨⟨cr', hs'⟩, hSB'⟩ _
    exact hbody F _ t cr' hs' hSB' fun s'' cr'' h'' hSB'' => ⟨⟨cr'', h''⟩, hSB''⟩
  · rintro t ⟨⟨cr', hs'⟩, hSB'⟩ _
    exact hQ t cr' (start_entailsE hs' (sepConj_mono_left hexit)) hSB'

/-- **The loop rule an engine actually needs**: the body is entered only
when the guard holds, and `hg` is what turns the *concrete* guard's truth
into the *abstract* guard's — the `CondRefine` obligation of the
synthesis layer, restated for the bounds pass. This is the one place the
two layers must agree, and it is one lemma per guard shape, not one per
program. -/
theorem BRefine.while_guard {B : ℕ} {σ : Type} {I : σ → Prop} {Γ : σ → Assn} {Γ' : Assn}
    {b : Cond} {c : Com} {bf : σ → Bool} (hlit : b.LitLt B)
    (hg : ∀ (t : σ) (F : Assn) (s : Ir.State) (cr : ECost) (r : Bool),
      I t → irSTATE (Γ t ∗ F) (s, cr) → b.eval s = some r → bf t = r)
    (hbody : ∀ t, I t → bf t = true → BRefine B (Γ t) c (LoopAssn I Γ))
    (hexit : ∀ t, I t → bf t = false → (Γ t ⊢ Γ')) :
    BRefine B (LoopAssn I Γ) (.while b c) Γ' := by
  intro F Q s cr hs hSB hQ
  rw [Ir.bpre_while]
  refine ⟨fun t => (∃ cr', irSTATE (LoopAssn I Γ ∗ F) (t, cr')) ∧ Ir.StateBound B t,
    ⟨⟨cr, hs⟩, hSB⟩, ?_, ?_, ?_⟩
  · exact fun t _ hInv hev => Ir.Cond.evalB_of_stateBound hInv.2 hlit hev
  · rintro t ⟨⟨cr', hs'⟩, hSB'⟩ hev
    rw [LoopAssn, sepEx_sepConj] at hs'
    obtain ⟨u, hu⟩ := hs'
    rw [sepConj_assoc] at hu
    obtain ⟨hIu, hu'⟩ := predLift_sepConj_iff.1 hu
    exact hbody u hIu (hg u F t cr' true hIu hu' hev) F _ t cr' hu' hSB'
      fun s'' cr'' h'' hSB'' => ⟨⟨cr'', h''⟩, hSB''⟩
  · rintro t ⟨⟨cr', hs'⟩, hSB'⟩ hev
    rw [LoopAssn, sepEx_sepConj] at hs'
    obtain ⟨u, hu⟩ := hs'
    rw [sepConj_assoc] at hu
    obtain ⟨hIu, hu'⟩ := predLift_sepConj_iff.1 hu
    have hu2 : irSTATE (Γ u ∗ F) (t, cr') := hu'
    exact hQ t cr' (start_entailsE hu2
      (sepConj_mono_left (hexit u hIu (hg u F t cr' false hIu hu' hev)))) hSB'

/-! ## 3. T2/D-b — the nested-`while` rules

`while_guard` demands the precondition be *literally* `LoopAssn I Γ`
and fixes the exit to a single assertion, which is right for a
top-level loop and wrong for one inside a body: there the loop is
entered from whatever the preceding operations left (`hinit`), the
cells it does not touch ride around it (`D`), and the continuation
needs to know *which* abstract state it stopped at and that the guard
is false. `ExitAssn` carries exactly that, and `while_seq` re-opens it
per exit state. -/

/-- The exit of a nested loop: some final abstract state, with the
invariant and the guard's falsity handed to the continuation. -/
def ExitAssn {σ : Type} (I : σ → Prop) (bf : σ → Bool) (Γ : σ → Assn) : Assn :=
  ∃ᵃ u, (⌜I u ∧ bf u = false⌝ ∗ Γ u)

theorem ExitAssn_def {σ : Type} (I : σ → Prop) (bf : σ → Bool) (Γ : σ → Assn) :
    ExitAssn I bf Γ = ∃ᵃ u, (⌜I u ∧ bf u = false⌝ ∗ Γ u) := rfl

theorem exitAssn_intro {σ : Type} {I : σ → Prop} {bf : σ → Bool} {Γ : σ → Assn} {u : σ}
    (hI : I u) (hbf : bf u = false) : Γ u ⊢ ExitAssn I bf Γ := by
  intro p hp
  exact ⟨u, predLift_sepConj_iff.2 ⟨⟨hI, hbf⟩, hp⟩⟩

/-- **A `while` inside a body** (T2/D-b): entered from `Δ` through
`hinit`, with the untouched cells `D` framed around it, exiting at
`ExitAssn I bf Γ ∗ D`. -/
theorem BRefine.while_nested {B : ℕ} {σ : Type} {I : σ → Prop} {Γ : σ → Assn}
    {b : Cond} {c : Com} {bf : σ → Bool} {Δ D : Assn} (hlit : b.LitLt B)
    (hg : ∀ (t : σ) (F : Assn) (s : Ir.State) (cr : ECost) (r : Bool),
      I t → irSTATE (Γ t ∗ F) (s, cr) → b.eval s = some r → bf t = r)
    (hbody : ∀ t, I t → bf t = true → BRefine B (Γ t) c (LoopAssn I Γ))
    (hinit : Δ ⊢ (LoopAssn I Γ ∗ D)) :
    BRefine B Δ (.while b c) (ExitAssn I bf Γ ∗ D) := by
  refine BRefine.cons (BRefine.frame (D := D) ?_) hinit (entails_refl _)
  exact BRefine.while_guard hlit hg hbody (fun u hI hbf => exitAssn_intro hI hbf)

/-- **The composing rule** (T2/D-b): the shape a two-level body actually
contains, `(.while b c).seq d`, with the continuation entered per exit
state — the inner loop's own invariant and the falsity of its guard are
what the operations after it run on. This is what unblocks every
two-level engine pass (ElimSynth3 §5 E3, AugmentSynth §10 gap 3). -/
theorem BRefine.while_seq {B : ℕ} {σ : Type} {I : σ → Prop} {Γ : σ → Assn}
    {b : Cond} {c : Com} {bf : σ → Bool} {Δ D Θ : Assn} {d : Com} (hlit : b.LitLt B)
    (hg : ∀ (t : σ) (F : Assn) (s : Ir.State) (cr : ECost) (r : Bool),
      I t → irSTATE (Γ t ∗ F) (s, cr) → b.eval s = some r → bf t = r)
    (hbody : ∀ t, I t → bf t = true → BRefine B (Γ t) c (LoopAssn I Γ))
    (hinit : Δ ⊢ (LoopAssn I Γ ∗ D))
    (hcont : ∀ u, I u → bf u = false → BRefine B (Γ u ∗ D) d Θ) :
    BRefine B Δ ((Com.while b c).seq d) Θ := by
  refine BRefine.seq (BRefine.while_nested hlit hg hbody hinit) ?_
  rw [ExitAssn_def, sepEx_sepConj]
  refine BRefine.pre_ex fun u => ?_
  rw [sepConj_assoc]
  exact BRefine.pre_pure fun hu => hcont u hu.1 hu.2

/-! ## 4. T2/D-c — the junk-cell rules

A scratch cell is `junkCell` in a loop assertion. `pre_junk` opens one
directly; the `*_junk` op rules consume a junk *destination* with no
opening at all. The value is threaded out (`natAssn` in the post), and
weakening it back to junk at the loop close is
`natAssn_entails_junkCell`. -/

/-- Open one junk cell of the precondition. -/
theorem BRefine.pre_junk {B : ℕ} {x : String} {Γ Γ' : Assn} {c : Com}
    (h : ∀ v, BRefine B (natAssn v x ∗ Γ) c Γ') :
    BRefine B (junkCell x ∗ Γ) c Γ' := by
  rw [junkCell_def, sepEx_sepConj]
  exact BRefine.pre_ex fun v => h v

/-- …and one junk array. -/
theorem BRefine.pre_junkArray {B : ℕ} {a : String} {Γ Γ' : Assn} {c : Com}
    (h : ∀ xs, BRefine B (arrayAssn xs a ∗ Γ) c Γ') :
    BRefine B (junkArray a ∗ Γ) c Γ' := by
  rw [junkArray_def, sepEx_sepConj]
  exact BRefine.pre_ex fun xs => h xs

/-- `x := n` at a junk destination. -/
theorem BRefine.const_junk {B : ℕ} {x : String} {n : ℕ} (hn : n < B) :
    BRefine B (junkCell x) (.const x n) (natAssn n x) := by
  rw [junkCell_def]
  exact BRefine.pre_ex fun v => BRefine.const hn

/-- `x := y` at a junk destination. -/
theorem BRefine.copy_junk {B : ℕ} {x y : String} {w : ℕ} :
    BRefine B (junkCell x ∗ natAssn w y) (.copy x y) (natAssn w x ∗ natAssn w y) := by
  rw [junkCell_def, sepEx_sepConj]
  exact BRefine.pre_ex fun v => BRefine.copy

/-- `x := y ⊕ z` at a junk destination — the creation site, junk form. -/
theorem BRefine.binop_junk {B : ℕ} {op : Imp.Bop} {x y z : String} {m n : ℕ}
    (hb : op.apply m n < B) :
    BRefine B (junkCell x ∗ natAssn m y ∗ natAssn n z) (.binop op x y z)
      (natAssn (op.apply m n) x ∗ natAssn m y ∗ natAssn n z) := by
  rw [junkCell_def, sepEx_sepConj]
  exact BRefine.pre_ex fun v => BRefine.binop hb

/-- `x := a[i]` at a junk destination. -/
theorem BRefine.aget_junk {B : ℕ} {x a i : String} {k : ℕ} {xs : List ℕ} :
    BRefine B (junkCell x ∗ arrayAssn xs a ∗ natAssn k i) (.aget x a i)
      (⌜k < xs.length⌝ ∗ natAssn xs[k]! x ∗ arrayAssn xs a ∗ natAssn k i) := by
  rw [junkCell_def, sepEx_sepConj]
  exact BRefine.pre_ex fun v => BRefine.aget

/-! The database (T2/D-d): in-place and junk-destination forms first. -/

attribute [sepref_brefine_rules]
  BRefine.binop_self BRefine.binop_junk BRefine.const_junk BRefine.copy_junk
  BRefine.aget_junk BRefine.aset BRefine.const BRefine.copy BRefine.binop BRefine.aget

/-! ## 5. T2/D-f — the run adapter

The ∀/∃ bridge for engine leaves (2A′'s R2A/D-l). `bpre` demands a
clause at every run; a consumer holds *one* bounded run; and the
language is deterministic, so the one run pins them all. The content is
`bpre_of_bigStepB` — a `BigStepB` derivation is an `Ir.bpre` at any
postcondition its final state satisfies — whose `while` case
re-establishes the invariant-existential from the derivation itself
(`bpre_while_step`). `BRefine_of_run` then turns "some bounded run from
every `Γ`-state lands in a `Γ'`-state" into the judgment, which is the
∃-form an engine's `hnRefine` + spec + `exists_bigStepB_of_hnRefine`
deliver. -/

/-- `bpre` is monotone in its postcondition. -/
theorem bpre_mono {B : ℕ} : ∀ (c : Com) {Q₁ Q₂ : Ir.State → Prop},
    (∀ t, Q₁ t → Q₂ t) → ∀ s : Ir.State, Ir.bpre B c Q₁ s → Ir.bpre B c Q₂ s := by
  intro c
  induction c with
  | skip => exact fun hQ s h => hQ s h
  | const x n => exact fun hQ s h => ⟨h.1, hQ _ h.2⟩
  | copy x y => exact fun hQ s h v hv => hQ _ (h v hv)
  | binop op x y z =>
    exact fun hQ s h m n hm hn => ⟨(h m n hm hn).1, hQ _ (h m n hm hn).2⟩
  | aget x a i => exact fun hQ s h k xs v hk ha hv => hQ _ (h k xs v hk ha hv)
  | aset a i v => exact fun hQ s h k n xs hk hn ha hlen => hQ _ (h k n xs hk hn ha hlen)
  | seq c d ihc ihd => exact fun hQ s h => ihc (fun t ht => ihd hQ t ht) s h
  | ite b c d ihc ihd =>
    exact fun hQ s h =>
      ⟨h.1, fun ht => ihc hQ s (h.2.1 ht), fun hf => ihd hQ s (h.2.2 hf)⟩
  | «while» b c ihc =>
    intro Q₁ Q₂ hQ s h
    obtain ⟨Inv, hI, hg, hb, he⟩ := h
    exact ⟨Inv, hI, hg, hb, fun t ht hf => hQ _ (he t ht hf)⟩

/-- One unfolding of a bounded loop's `bpre`: a guard read below the
bound and a body that re-establishes the loop's own `bpre`. The
invariant offered is "the entry state, or any state whose own `bpre`
holds" — which is what makes a *derivation* an invariant. -/
theorem bpre_while_step {B : ℕ} {b : Cond} {c : Com} {Q : Ir.State → Prop} {s : Ir.State}
    (hb : b.evalB B s = some true)
    (hbody : Ir.bpre B c (Ir.bpre B (.while b c) Q) s) :
    Ir.bpre B (.while b c) Q s := by
  rw [Ir.bpre_while]
  refine ⟨fun t => t = s ∨ Ir.bpre B (.while b c) Q t,
    show s = s ∨ Ir.bpre B (.while b c) Q s from Or.inl rfl, ?_, ?_, ?_⟩
  · rintro t r (rfl | hW) hev
    · rw [Ir.Cond.eval_of_evalB hb] at hev
      cases Option.some.inj hev
      exact hb
    · rw [Ir.bpre_while] at hW
      obtain ⟨Inv₂, hI₂, hg₂, -, -⟩ := hW
      exact hg₂ t r hI₂ hev
  · rintro t (rfl | hW) hev
    · exact bpre_mono c (fun u hu => Or.inr hu) t hbody
    · rw [Ir.bpre_while] at hW
      obtain ⟨Inv₂, hI₂, hg₂, hb₂, he₂⟩ := hW
      refine bpre_mono c (fun u hu => Or.inr ?_) t (hb₂ t hI₂ hev)
      rw [Ir.bpre_while]
      exact ⟨Inv₂, hu, hg₂, hb₂, he₂⟩
  · rintro t (rfl | hW) hev
    · rw [Ir.Cond.eval_of_evalB hb] at hev
      exact absurd (Option.some.inj hev) (by simp)
    · rw [Ir.bpre_while] at hW
      obtain ⟨Inv₂, hI₂, -, -, he₂⟩ := hW
      exact he₂ t hI₂ hev

/-- **A bounded derivation is a `bpre`, at any postcondition its final
state satisfies** (T2/D-f). This is the ∀/∃ bridge: the derivation's
own guard reads supply the `evalB` clauses, its stores supply the
updates, and `bpre_while_step` rebuilds the loop invariant from the
derivation's own loop-head states. -/
theorem bpre_of_bigStepB {B : ℕ} {c : Com} {s s' : Ir.State} {κ : Ir.Cost}
    (h : Ir.BigStepB B c s s' κ) : ∀ Q : Ir.State → Prop, Q s' → Ir.bpre B c Q s := by
  induction h with
  | skip => exact fun Q hQ => hQ
  | const _ hn => exact fun Q hQ => ⟨hn, hQ⟩
  | copy _ hy =>
    intro Q hQ v' hv'
    cases Option.some.inj (hy.symm.trans hv')
    exact hQ
  | binop _ hy hz hb =>
    intro Q hQ m' n' hm' hn'
    cases Option.some.inj (hy.symm.trans hm')
    cases Option.some.inj (hz.symm.trans hn')
    exact ⟨hb, hQ⟩
  | aget _ hi ha hv =>
    intro Q hQ k' xs' v' hk' ha' hv'
    cases Option.some.inj (hi.symm.trans hk')
    cases Option.some.inj (ha.symm.trans ha')
    cases Option.some.inj (hv.symm.trans hv')
    exact hQ
  | aset hi hv ha hk =>
    intro Q hQ k' n' xs' hk' hn' ha' _
    cases Option.some.inj (hi.symm.trans hk')
    cases Option.some.inj (hv.symm.trans hn')
    cases Option.some.inj (ha.symm.trans ha')
    exact hQ
  | seq _ _ ih ih' => exact fun Q hQ => ih _ (ih' Q hQ)
  | ite_true hb _ ih =>
    intro Q hQ
    rw [Ir.bpre_ite]
    have hev := Ir.Cond.eval_of_evalB hb
    refine ⟨fun r hr => ?_, fun _ => ih Q hQ, fun hf => ?_⟩
    · cases Option.some.inj (hev.symm.trans hr)
      exact hb
    · exact absurd (Option.some.inj (hev.symm.trans hf)) (by simp)
  | ite_false hb _ ih =>
    intro Q hQ
    rw [Ir.bpre_ite]
    have hev := Ir.Cond.eval_of_evalB hb
    refine ⟨fun r hr => ?_, fun ht => ?_, fun _ => ih Q hQ⟩
    · cases Option.some.inj (hev.symm.trans hr)
      exact hb
    · exact absurd (Option.some.inj (hev.symm.trans ht)) (by simp)
  | while_true hb _ _ ih ih' => exact fun Q hQ => bpre_while_step hb (ih _ (ih' Q hQ))
  | @while_false b c s hb =>
    intro Q hQ
    rw [Ir.bpre_while]
    have hev := Ir.Cond.eval_of_evalB hb
    refine ⟨fun t => t = s, show s = s from rfl, ?_, ?_, ?_⟩
    · rintro t r rfl hr
      cases Option.some.inj (hev.symm.trans hr)
      exact hb
    · rintro t rfl ht
      exact absurd (Option.some.inj (hev.symm.trans ht)) (by simp)
    · rintro t rfl _
      exact hQ

/-- **The run adapter** (T2/D-f). An engine leaf is a `BRefine` as soon
as, from every state its precondition describes, *some* bounded run
lands back in its postcondition — the ∃-form the engine's `hnRefine` +
spec + `exists_bigStepB_of_hnRefine` deliver. `StateBound` at the exit
is free (`BigStepB.stateBound`). -/
theorem BRefine_of_run {B : ℕ} {Γ Γ' : Assn} {c : Com}
    (h : ∀ (F : Assn) (s : Ir.State) (cr : ECost), irSTATE (Γ ∗ F) (s, cr) →
      Ir.StateBound B s →
      ∃ (s' : Ir.State) (κ : Ir.Cost) (cr' : ECost),
        Ir.BigStepB B c s s' κ ∧ irSTATE (Γ' ∗ F) (s', cr')) :
    BRefine B Γ c Γ' := by
  intro F Q s cr hs hSB hQ
  obtain ⟨s', κ, cr', hrun, hpost⟩ := h F s cr hs hSB
  exact bpre_of_bigStepB hrun Q (hQ s' cr' hpost (hrun.stateBound hSB))

end WordSpike

/-! ## 6. T2/D-d — the `brefine` driver

Walks a `.seq` chain, emitting per operation the permutation/frame glue
around a `sepref_brefine_rules` entry — exactly the
`BRefine.perm … (by sepref_ac) … ∘ BRefine.frame` bookkeeping the
engine waves authored by hand. Pure conjuncts are opened as they are
produced (`pre_pure`, with the fact introduced into the context so the
side conditions downstream can use it). What is left open, in order:
arithmetic side conditions the fallback (`assumption`/`decide`/`omega`,
with the `Bop.apply` spellings normalized) cannot close, `while`-headed
sub-goals (their invariants are proof ideas — `while_guard`/`while_seq`
consume them, and a `while` in seq position is left in `while_seq`'s
own shape), and the final entailment into a concrete target assertion
(`loopAssn_intro`'s job). -/

namespace Bounds

open Lean Elab Meta
open Frame

/-- Build a `BRefine` proposition. -/
private def mkBRefine (B Γ c Γ' : Expr) : Expr :=
  mkApp4 (mkConst ``WordSpike.BRefine) B Γ c Γ'

/-- Unfold a *named* assertion (a `def` folding a `∗`-chain) until the
matcher can read it. Recognised assertion formers are left alone. -/
partial def unfoldAssn (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  match e.getAppFnArgs.1 with
  | ``sepConj | ``natAssn | ``arrayAssn | ``junkCell | ``junkArray | ``predLift
  | ``sepEx | ``hnCtxt | ``WordSpike.LoopAssn | ``WordSpike.ExitAssn | ``emp
  | ``Ir.ptoVar | ``Ir.ptoArr => return e
  | _ =>
    match ← unfoldDefinition? e with
    | some e' => unfoldAssn e'
    | none => return e

/-- The side-condition fallback: the cheap closers, with the
`Bop.apply` spellings normalized for `omega`. -/
def tryClose (g : MVarId) : TermElabM Bool := do
  let st ← saveState
  try
    let rest ← Tactic.run g (Tactic.evalTactic (← `(tactic|
      first
        | assumption
        | decide
        | omega
        | (simp only [Lax13Proofs.Imp.Bop.apply_add, Lax13Proofs.Imp.Bop.apply_sub,
             Lax13Proofs.Imp.Bop.apply_mul]
           omega)
        | (simp only [Lax13Proofs.Imp.Bop.apply_add, Lax13Proofs.Imp.Bop.apply_sub,
             Lax13Proofs.Imp.Bop.apply_mul]
           assumption))))
    if rest.isEmpty then
      return true
    else
      st.restore
      return false
  catch _ =>
    st.restore
    return false

/-- One operation, against the `sepref_brefine_rules` database: match
the rule's conjuncts (`frameMatch`), frame the remainder, permute, and
leave open what the fallback cannot close. -/
def opStep (g : MVarId) (acc : IO.Ref (Array MVarId)) (B Γ com Γ' : Expr)
    (cs : Array Expr) (α : Expr) : TermElabM Unit := do
  let rules ← (try labelled `sepref_brefine_rules catch _ => pure #[])
  let mut reasons : Array MessageData := #[]
  for nm in rules do
    let st ← saveState
    try
      let rule ← mkConstWithFreshMVarLevels nm
      let (mvars, _, concl) ← forallMetaTelescope (← inferType rule)
      let (``WordSpike.BRefine, #[Br, Pr, cr, Pr']) := concl.getAppFnArgs
        | throwError "not a BRefine rule"
      unless ← isDefEq cr com do throwError "!stated at another operation"
      unless ← isDefEq Br B do throwError "the rule's bound does not match the goal's"
      let PrI ← instantiateMVars Pr
      let some (matched, frame) ← frameMatch (conjuncts PrI) cs
        | throwError "{← noPairMsg (conjuncts PrI) cs}"
      let ruleProof := mkAppN rule mvars
      let PmE ← mkConjuncts α matched
      let Pr'I ← instantiateMVars Pr'
      let (prf, pre, post) ←
        if frame.isEmpty then
          pure (ruleProof, PmE, Pr'I)
        else do
          let D ← mkConjuncts α frame
          pure (← mkAppOptM ``WordSpike.BRefine.frame
              #[none, none, none, some D, none, some ruleProof],
            ← mkAppM ``sepConj #[PmE, D], ← mkAppM ``sepConj #[Pr'I, D])
      let heq ← proveConjEq Γ pre
      let mut pend : Array MVarId := #[]
      if Γ'.getAppFn.isMVar then
        Translate.assignChecked g
          (← mkAppM ``WordSpike.BRefine.perm #[heq, ← mkEqRefl post, prf])
      else if ← isDefEq Γ' post then
        Translate.assignChecked g
          (← mkAppM ``WordSpike.BRefine.perm #[heq, ← mkEqRefl post, prf])
      else
        try
          let heq' ← proveConjEq post Γ'
          Translate.assignChecked g
            (← mkAppM ``WordSpike.BRefine.perm #[heq, heq', prf])
        catch _ =>
          let prf₂ ← mkAppM ``WordSpike.BRefine.perm #[heq, ← mkEqRefl post, prf]
          let hpost ← mkFreshExprMVar (← mkAppM ``entails #[post, Γ'])
          Translate.assignChecked g (← mkAppM ``WordSpike.BRefine.cons
            #[prf₂, ← mkAppM ``entails_refl #[Γ], hpost])
          pend := pend.push hpost.mvarId!
      let mut sides : Array MVarId := #[]
      for mv in mvars do
        let mid := mv.mvarId!
        unless ← mid.isAssigned do
          let mty ← instantiateMVars (← mid.getType)
          if ← isProp mty then sides := sides.push mid
          else throwError "the rule's premises left a non-propositional argument open"
      for mid in sides do
        unless ← tryClose mid do acc.modify (·.push mid)
      for p in pend do
        acc.modify (·.push p)
      return
    catch e =>
      st.restore
      let txt ← e.toMessageData.toString
      unless txt.startsWith "!" do reasons := reasons.push m!"{nm}: {e.toMessageData}"
  throwError "brefine: no bounds rule applies to{indentExpr com}\nunder the ownership\
    {indentExpr Γ}\ncandidates tried:\n{MessageData.joinSep reasons.toList "\n"}"

/-- The driver's recursion. -/
partial def go (g : MVarId) (acc : IO.Ref (Array MVarId)) : TermElabM Unit := do
  if ← g.isAssigned then return
  g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  let (``WordSpike.BRefine, #[B, Γ0, com, Γ']) := ty.getAppFnArgs
    | do acc.modify (·.push g); return
  if Γ0.getAppFn.isMVar then
    acc.modify (·.push g)
    return
  let Γu ← unfoldAssn Γ0
  let g ← if Γu == Γ0 then pure g else g.change (mkBRefine B Γu com Γ')
  g.withContext do
  let Γ := Γu
  let cs := conjuncts Γ
  let α ← carrierOf Γ
  -- A pure conjunct is opened first, its fact introduced.
  if let some i := cs.findIdx? (fun c => c.getAppFnArgs.1 == ``predLift) then
    let pureC := cs[i]!
    let Φ := pureC.getAppArgs.back!
    let rest ← mkConjuncts α ((cs.toList.eraseIdx i).toArray)
    let target ← mkAppM ``sepConj #[pureC, rest]
    let heq ← proveConjEq Γ target
    let hm ← mkFreshExprMVar (← mkArrow Φ (mkBRefine B rest com Γ'))
    Translate.assignChecked g (← mkAppM ``WordSpike.BRefine.perm
      #[heq, ← mkEqRefl Γ', ← mkAppM ``WordSpike.BRefine.pre_pure #[hm]])
    let (_, g') ← hm.mvarId!.intro1
    go g' acc
    return
  let comW ← whnf com
  match comW.getAppFnArgs with
  | (``Ir.Com.seq, #[c₁, c₂]) =>
    if (← whnf c₁).getAppFnArgs.1 == ``Ir.Com.while then
      -- A loop in the middle of a body: leave the goal in
      -- `BRefine.while_seq`'s own shape.
      acc.modify (·.push g)
      return
    let Γ₁ ← mkFreshExprMVar (← inferType Γ)
    let m₁ ← mkFreshExprMVar (mkBRefine B Γ c₁ Γ₁)
    let m₂ ← mkFreshExprMVar (mkBRefine B Γ₁ c₂ Γ')
    Translate.assignChecked g (← mkAppM ``WordSpike.BRefine.seq #[m₁, m₂])
    go m₁.mvarId! acc
    go m₂.mvarId! acc
  | (``Ir.Com.skip, _) =>
    let skipPrf ← mkAppOptM ``WordSpike.BRefine.skip #[some B, some Γ]
    if Γ'.getAppFn.isMVar then
      Translate.assignChecked g skipPrf
    else if ← isDefEq Γ' Γ then
      Translate.assignChecked g skipPrf
    else
      let hpost ← mkFreshExprMVar (← mkAppM ``entails #[Γ, Γ'])
      Translate.assignChecked g (← mkAppM ``WordSpike.BRefine.cons
        #[skipPrf, ← mkAppM ``entails_refl #[Γ], hpost])
      acc.modify (·.push hpost.mvarId!)
  | (``Ir.Com.while, _) =>
    -- A top-level loop: its invariant is a proof idea.
    acc.modify (·.push g)
  | _ => opStep g acc B Γ com Γ' cs α

open Elab in
/-- **The bounds driver** (T2/D-d): discharge a `BRefine` goal's
straight-line operations from the `sepref_brefine_rules` database,
leaving side conditions, `while` sub-goals and final entailments. -/
elab "brefine" : tactic => do
  let g ← Tactic.getMainGoal
  let acc ← IO.mkRef (#[] : Array MVarId)
  go g acc
  Tactic.replaceMainGoal (← acc.get).toList

end Bounds

namespace WordSpike

/-! ## 7. Gate (ledger D4, refute before prove)

The new rules of §3–§5, controlled. The moved rules of §1–§2 keep their
controls where they were exercised (the spike's §5, untouched by the
promotion); the two-level composition runs end to end on the
counting-pass shape in `Examples/BoundsProbe.lean`. -/

namespace BoundsGate

/-- Guard-shape facts, local (`Sepref/Examples/BfsQSynth.lean` is
downstream of this file). -/
theorem litLt_lt_cells {B : ℕ} {x y : String} :
    (Cond.lt (Operand.cell x) (Operand.cell y)).LitLt B := ⟨trivial, trivial⟩

theorem eval_lt_cells {s : Ir.State} {x y : String} {r : Bool}
    (h : (Ir.Cond.lt (.cell x) (.cell y)).eval s = some r) :
    ∃ a b : ℕ, s.vars x = some a ∧ s.vars y = some b ∧ r = decide (a < b) := by
  rw [Ir.Cond.eval_lt, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rfl⟩ := h
  exact ⟨a, b, by simpa using ha, by simpa using hb, rfl⟩

/-- One store for all the controls. -/
def bState : Ir.State :=
  Ir.State.ofPairs [("i", 0), ("n", 1), ("j", 3), ("m", 4), ("z", 4), ("one", 1)] []

def bFrame : Assn :=
  EXACT ((((((((vcells bState).erase "i").erase "n").erase "j").erase "m").erase
    "z").erase "one", acells bState, hcells bState), 0)

def bOwn : Assn :=
  natAssn 0 "i" ∗ natAssn 1 "n" ∗ natAssn 3 "j" ∗ natAssn 4 "m" ∗ natAssn 4 "z" ∗
    natAssn 1 "one"

theorem bOwn_holds : irSTATE (bOwn ∗ bFrame) (bState, 0) := by
  show (bOwn ∗ bFrame) ((vcells bState, acells bState, hcells bState), 0)
  simp only [bOwn, natAssn_def, sepConj_assoc]
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine Ir.ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  exact Ir.ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩

theorem bState_bound : Ir.StateBound 100 bState :=
  Codegen.stateBound_ofPairs (by decide) (by decide)

/-! ### T2/D-c and T2/D-d controls: the junk rules and the driver

Positive: a junk destination is written and then accumulated into,
straight off the database — the whole two-op chain is driver-emitted,
no `pre_ex`, no hand permutation. Negative: the junk form does not
weaken the creation site — `x := 8` at `B = 8` from a junk cell has no
`BRefine` at any exit, because `bpre` is false at a state that owns the
cell. -/

example : BRefine 100 (junkCell "j" ∗ natAssn 4 "z")
    ((Com.const "j" 5).seq (Com.binop .add "j" "j" "z"))
    (natAssn (Imp.Bop.apply .add 5 4) "j" ∗ natAssn 4 "z") := by
  brefine

theorem no_bpre_const_at_bound :
    ¬ Ir.bpre 8 (.const "j" 8) (fun _ => True) bState := by
  rw [Ir.bpre_const]
  exact fun h => absurd h.1 (by decide)

theorem no_brefine_const_junk_at_bound {Γ' : Assn} :
    ¬ BRefine 8 (junkCell "j") (.const "j" 8) Γ' := by
  intro h
  have hmid : irSTATE (natAssn 3 "j" ∗ (natAssn 0 "i" ∗ natAssn 1 "n" ∗ natAssn 4 "m" ∗
      natAssn 4 "z" ∗ natAssn 1 "one" ∗ bFrame)) (bState, 0) :=
    irSTATE_cong (by rw [bOwn]; ac_rfl) bOwn_holds
  have hs : irSTATE (junkCell "j" ∗ (natAssn 0 "i" ∗ natAssn 1 "n" ∗ natAssn 4 "m" ∗
      natAssn 4 "z" ∗ natAssn 1 "one" ∗ bFrame)) (bState, 0) :=
    start_entailsE hmid (sepConj_mono_left (natAssn_entails_junkCell 3 "j"))
  exact no_bpre_const_at_bound (bpre_of_BRefine h hs
    (Codegen.stateBound_ofPairs (by decide) (by decide)))

/-! ### T2/D-b controls: the nested loop

Positive: an inner loop entered from a plain assertion through
`while_nested`, cashed to an `Ir.bpre` witness at `bState` — the layer
agreement (`hg`) and the exit shape are both exercised (the full
two-level `while_seq` composition is the probe's). Negative: an inner
creation site that overflows refutes the judgment *through both loop
levels* — whatever invariants are offered, they hold at the entry
states and force the overflowing `binop`'s side condition. -/

/-- The inner loop of the controls: `while (j < m) { j := j + z }`. -/
def innerNest : Com :=
  Com.while (Cond.lt (Operand.cell "j") (Operand.cell "m")) (Com.binop .add "j" "j" "z")

/-- The two-level nest: the inner loop, then the outer counter. -/
def outerNest : Com :=
  Com.while (Cond.lt (Operand.cell "i") (Operand.cell "n"))
    (innerNest.seq (Com.binop .add "i" "i" "one"))

/-- The inner loop's assertion, at its own abstract state `j`. -/
def nΓ : ℕ → Assn := fun j => natAssn j "j" ∗ natAssn 4 "m" ∗ natAssn 4 "z"

/-- Its invariant. -/
def nI : ℕ → Prop := fun j => j ≤ 7

theorem nest_guard (t : ℕ) (F : Assn) (s : Ir.State) (cr : ECost) (r : Bool)
    (_ : nI t) (hs : irSTATE (nΓ t ∗ F) (s, cr))
    (hev : (Cond.lt (Operand.cell "j") (Operand.cell "m")).eval s = some r) :
    decide (t < 4) = r := by
  obtain ⟨a, b, ha, hb, rfl⟩ := eval_lt_cells hev
  have hj : s.vars "j" = some t :=
    natAssn_vars (F := natAssn 4 "m" ∗ natAssn 4 "z" ∗ F)
      (irSTATE_cong (by simp only [nΓ]; ac_rfl) hs)
  have hm : s.vars "m" = some 4 :=
    natAssn_vars (F := natAssn t "j" ∗ natAssn 4 "z" ∗ F)
      (irSTATE_cong (by simp only [nΓ]; ac_rfl) hs)
  rw [hj] at ha
  rw [hm] at hb
  rw [Option.some.inj ha, Option.some.inj hb]

/-- The inner body, driver-emitted: one database step, one side
condition (closed from `hbf` by the fallback), one entailment back into
the loop assertion. -/
theorem nest_body (t : ℕ) (_hI : nI t) (hbf : decide (t < 4) = true) :
    BRefine 100 (nΓ t) (Com.binop .add "j" "j" "z") (LoopAssn nI nΓ) := by
  have hlt : t < 4 := of_decide_eq_true hbf
  simp only [nΓ]
  brefine
  refine entails_trans (entails_of_eq (?_ : _ = nΓ (Imp.Bop.apply .add t 4)))
    (loopAssn_intro ?_)
  · simp only [nΓ]
    ac_rfl
  · simp only [nI, Imp.Bop.apply_add]
    omega

/-- **Positive control**: `while_nested` from a plain entry assertion… -/
theorem nest_brefine :
    BRefine 100 bOwn innerNest
      (ExitAssn nI (fun t => decide (t < 4)) nΓ ∗
        (natAssn 0 "i" ∗ natAssn 1 "n" ∗ natAssn 1 "one")) := by
  rw [innerNest]
  refine BRefine.while_nested litLt_lt_cells nest_guard nest_body ?_
  have h1 : bOwn = nΓ 3 ∗ (natAssn 0 "i" ∗ natAssn 1 "n" ∗ natAssn 1 "one") := by
    simp only [bOwn, nΓ]
    ac_rfl
  rw [h1]
  exact sepConj_mono_left (loopAssn_intro (I := nI) (Γ := nΓ) (t := 3)
    (by simp only [nI]; omega))

/-- …cashed to the `bpre` witness at a concrete store. -/
theorem nest_bpre : Ir.bpre 100 innerNest (fun _ => True) bState :=
  bpre_of_BRefine (F := bFrame) nest_brefine bOwn_holds bState_bound

/-- **Negative control (T2/D-b)**: at `B = 7` the inner body's `3 + 4`
does not fit, and `bpre` is false through both loop levels. -/
theorem no_bpre_nested : ¬ Ir.bpre 7 outerNest (fun _ => True) bState := by
  rw [outerNest, Ir.bpre_while]
  rintro ⟨Inv, hI0, -, hb, -⟩
  have h1 := hb bState hI0 rfl
  rw [Ir.bpre_seq, innerNest, Ir.bpre_while] at h1
  obtain ⟨Inv2, hI20, -, hb2, -⟩ := h1
  have h2 := hb2 bState hI20 rfl
  rw [Ir.bpre_binop] at h2
  exact absurd (h2 3 4 rfl rfl).1 (by decide)

/-- …so no `BRefine 7` for the nest exists at an assertion the store
satisfies. -/
theorem no_brefine_nested {Γ' : Assn} : ¬ BRefine 7 bOwn outerNest Γ' := by
  intro h
  exact no_bpre_nested (bpre_of_BRefine (F := bFrame) h bOwn_holds
    (Codegen.stateBound_ofPairs (by decide) (by decide)))

/-! ### T2/D-f controls: the run adapter

Positive I: a hand-built derivation of the inner loop (one iteration)
consumed by `bpre_of_bigStepB` — the `while` clause of the bridge, at a
concrete run. Positive II: the adapter derives an op's `BRefine` from
runs alone, agreeing with the rule layer. Negative: the adapter's
premise cannot be manufactured — at `B = 7` no bounded run of the
overflowing `binop` exists at all, from any state owning the cells. -/

/-- The one-iteration derivation of the inner loop, by hand. -/
theorem nest_run :
    Ir.BigStepB 100 innerNest bState (bState.setVar "j" (Imp.Bop.apply .add 3 4))
      (ACost.cost Currency.«while» 1 + ACost.cost (binopCurrency .add) 1
        + ACost.cost Currency.«while» 1) := by
  rw [innerNest]
  exact Ir.BigStepB.while_true (by decide)
    (Ir.BigStepB.binop (by decide) rfl rfl (by decide))
    (Ir.BigStepB.while_false (by decide))

theorem nest_bpre_via_run : Ir.bpre 100 innerNest (fun _ => True) bState :=
  bpre_of_bigStepB nest_run _ trivial

/-- The adapter agrees with the rule layer at an op. -/
theorem binop_brefine_via_run :
    BRefine 100 (natAssn 3 "j" ∗ natAssn 4 "z") (Com.binop .add "j" "j" "z")
      (natAssn (Imp.Bop.apply .add 3 4) "j" ∗ natAssn 4 "z") := by
  refine BRefine_of_run fun F s cr hs hSB => ?_
  have h1 : irSTATE (natAssn 3 "j" ∗ (natAssn 4 "z" ∗ F)) (s, cr) :=
    irSTATE_cong (sepConj_assoc _ _ _) hs
  have hj : s.vars "j" = some 3 := natAssn_vars h1
  have hz : s.vars "z" = some 4 :=
    natAssn_vars (F := natAssn 3 "j" ∗ F) (irSTATE_cong
      (by rw [sepConj_comm (natAssn 3 "j") (natAssn 4 "z"), sepConj_assoc]) hs)
  have h2 := natAssn_setVar (n := Imp.Bop.apply .add 3 4) h1
  exact ⟨s.setVar "j" (Imp.Bop.apply .add 3 4), _, cr,
    Ir.BigStepB.binop (by simp [hj]) hj hz (by decide),
    irSTATE_cong ((sepConj_assoc _ _ _).symm) h2⟩

/-- **Negative control (T2/D-f)**: no bounded run of the overflowing op
exists — the run *carries* the bound, and the adapter cannot invent
it. -/
theorem no_run_at_bound :
    ¬ ∃ (s' : Ir.State) (κ : Ir.Cost),
      Ir.BigStepB 7 (Com.binop .add "j" "j" "z") bState s' κ := by
  rintro ⟨s', κ, hrun⟩
  cases hrun with
  | binop _ hy hz hb =>
    cases Option.some.inj ((rfl : bState.vars "j" = some 3).symm.trans hy)
    cases Option.some.inj ((rfl : bState.vars "z" = some 4).symm.trans hz)
    exact absurd hb (by decide)

/-! ### Axioms -/

#print axioms nest_bpre
#print axioms nest_bpre_via_run
#print axioms binop_brefine_via_run
#print axioms no_bpre_nested
#print axioms no_brefine_const_junk_at_bound
#print axioms no_run_at_bound

end BoundsGate

end WordSpike

end Lax13Proofs.Refine.Sepref
