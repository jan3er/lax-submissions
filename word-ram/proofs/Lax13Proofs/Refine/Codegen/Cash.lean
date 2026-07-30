import Lax13Proofs.Refine.Codegen.Sim
import Lax13Proofs.Refine.Codegen.Harness
import Lax13Proofs.Refine.Codegen.BoundVcg
import Lax13Proofs.Refine.Sepref.IrOps
import Lax13Proofs.Transfer

/-!
The cashing theorem: from a synthesized `hnRefine` to a statement the
endorsed boundary consumes.

**This file is ours** (ledger **D3**); its specification is
`plans/word-ram/refinement-tower/p5-codegen-design.md` §5.

## What is being cashed

Four things arrive from four different places and have to be spent in
one transaction.

* **The program.** `hnRefine Γ c Γ' d R m` (P4) says that the deep
  `Ir.Com` `c`, started in any state satisfying `Γ`, runs and lands in
  `Γ' ∗ R ra d` — where `R ra d` is a conjunction of `natAssn` and
  `arrayAssn`, that is, *equations* pinning the result cells to the
  abstract result `ra`.
* **The cost.** `hnRefine` does not bound the run's cost outright: it
  says the run is affordable at the balance `cr + Ca` for some `Ca` the
  abstract program admits (`Ca ≤ M ra`). An abstract bound
  `m ≤ SPEC Φ T` therefore does two jobs at once — it bounds `Ca` by
  `T` and it gives `Φ ra`, the abstract postcondition.
* **The bound.** `BigStepB` is what `Sim.lean` consumes and `hnRefine`
  does not produce (design record §5, "the bound is a genuine per-program
  obligation"). `BoundVcg.lean` produces it, from the same initial
  state, and `BigStep.bigStepB_of_eq` — determinism — ties the two
  derivations to one execution without either being re-derived.
* **The exchange rate.** `Sim.lean`'s `cash` prices an IR cost account
  in IMP+ time units. Here it has to be applied to a *balance*
  (`ECost`, `ℕ∞`-valued) rather than to a run's account (`Cost`,
  `ℕ`-valued), so `ecash` is `cash`'s `ℕ∞` twin and `cash_le_ecash` is
  the one lemma that connects them.

## The two export shapes

**(a) `spec_of_hnRefine`** — the primary one, and the shape P7 consumes
(`bfs_spec` at `Lax3Proofs/RamBfs.lean:1064` is a cells-based
`Reasoning.Spec`, no tapes). Simulation only, no harness.

**(b) `solves_of_spec`** — the boundary wrapper: a `Reasoning.Spec` from
`initEnv`, per admissible input, is a `Transfer.Solves`, and
`Solves.computesInTime` finishes. The `initEnv`-shaped `Spec` is what
`Harness.lean`'s three marshal lemmas produce out of a body `Spec`, so
(b) is deliberately *not* re-parameterized over the marshal shapes: the
assembly is `marshal_… ▸ solves_of_spec`, three lines at a call site,
and no new abstraction between them.

## The cost arithmetic, in order

```
κ                            the IR run's account (BigStep)
  ≤ cr + Ca = Ca             affordability, at cr = 0        (hnRefine)
  ≤ T                        Ca ≤ M ra ≤ T                   (SPEC bound)
cash κ ≤ ecash T ≤ N         pricing, then the caller's numeral
```

Every step is an inequality in the safe direction and the first is the
only one that is not visibly so: `leCostECost κ (cr + Ca)` is *exactly*
"the run's account is affordable at that balance", so `cr = 0` is not a
weakening but the tightest choice — the initial credits a caller would
add can only make `κ ≤ cr + Ca` easier, never the conclusion stronger.
The toys' `Γ` owns no `¤¤` conjunct at all, so `cr = 0` is also the only
balance at which `irSTATE (Γ ∗ F) (s₀, cr)` holds (judgment call
P5/D-ae).

## Judgment calls

**P5/D-ad — the initial balance is fixed at `0`, not quantified.**
`hnRefine` quantifies over `cr`; a caller who owns credits could pass
them and get a larger `Ca` allowance. Nothing wants that here: the
credits an abstract program needs are the ones `Ca` accounts for, and a
`Γ` carrying `¤¤` conjuncts would have to *spend* them inside the
program, which for a synthesized program means they were part of the
abstract cost already. Fixing `cr = 0` removes a parameter from every
downstream statement; a future consumer that needs it restates the
theorem with `cr` free and changes `zero_add` to nothing.

**P5/D-ae — the abstract bound is `m ≤ NRest.spec Φ (fun _ => T)`, a
constant-cost `SPEC`.** The source's `SPEC P t` has `t : α → γ`. A
result-dependent bound would make the conclusion's `N` depend on `ra`,
which is existentially quantified in the `Spec` postcondition and so
cannot appear in the cost. A caller with a result-dependent bound takes
the supremum first; that is what a cost bound *is* at this boundary.

**P5/D-af — the readout is a hypothesis, not a shape.** The design
record asks for "the two destination shapes the toys need". Both are
instances of one hypothesis, `hQ`, which is handed the final `irSTATE`
and the agreeing environment and asked for whatever the caller wants to
know. A scalar destination discharges it with `ptoVar_vars` and
`agree.var`, an array destination with `ptoArr_arrs` and `agree.arr`;
`readout_scalar` and `readout_arr` below are those two discharges,
stated once so that a call site is one line either way.
-/

namespace Lax13Proofs.Refine.Codegen

open Lax13Proofs.Refine.Ir Lax13Proofs.Refine.Sepref

/-! ## 1. Pricing a balance

`cash` prices a *run's* account, `Ir.Cost = ACost String ℕ`. A bound on
that account is a bound in `ECost = ACost String ℕ∞`, so the price map
has to be applied there too. `ecash` is the same sum in `ℕ∞`, and
`cash_le_ecash` is the only lemma about it that the cashing theorem
uses; the rest is the arithmetic a caller needs to evaluate `ecash` on a
concrete cost expression.

(`Ir.Val` is a reducible abbreviation of `ℕ`, but `omega` does not see
through it when it is the *declared* type of a variable, so every
statement below that a caller will feed to `omega` is written at `ℕ`.
This is a Lean quirk, not a design decision, and it is recorded here
because it is invisible at the call site and costs an hour to find.) -/

/-- The price of a *balance*: `cash` in `ℕ∞`. -/
def ecash (c : ECost) : ℕ∞ := (Currency.all.map fun k => (weight k : ℕ∞) * c.toFun k).sum

/-- The step behind `cash_le_ecash`: the sum is monotone term by term,
and the cast commutes with it. -/
private theorem cast_sum_le (l : List String) (f : String → ℕ) (g : String → ℕ∞)
    (h : ∀ k, (f k : ℕ∞) ≤ g k) :
    (((l.map fun k => weight k * f k).sum : ℕ) : ℕ∞)
      ≤ (l.map fun k => (weight k : ℕ∞) * g k).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul]
      exact add_le_add (mul_le_mul' le_rfl (h a)) ih

/-- **The bridge.** An account affordable at a balance is priced no
higher than the balance is. -/
theorem cash_le_ecash {κ : Ir.Cost} {c : ECost} (h : leCostECost κ c) :
    (cash κ : ℕ∞) ≤ ecash c :=
  cast_sum_le Currency.all _ _ h

@[simp] theorem ecash_zero : ecash 0 = 0 := by simp [ecash, Currency.all]

@[simp] theorem ecash_add (c d : ECost) : ecash (c + d) = ecash c + ecash d := by
  simp only [ecash, ACost.toFun_add]
  induction Currency.all with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, mul_add]
      ring

@[simp] theorem ecash_nsmul (n : ℕ) (c : ECost) : ecash (n • c) = n * ecash c := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, ecash_add, ih]; push_cast; ring

/-- The price of a single currency's balance: the list is `Nodup`, so
exactly one term survives. -/
theorem ecash_cost {n : String} (hn : n ∈ Currency.all) (x : ℕ∞) :
    ecash (ACost.cost n x) = weight n * x := by
  have key : ∀ l : List String, l.Nodup → n ∈ l →
      (l.map fun k => (weight k : ℕ∞) * (ACost.cost n x).toFun k).sum = weight n * x := by
    intro l
    induction l with
    | nil => intro _ h; exact absurd h (by simp)
    | cons a t ih =>
        intro hnd hmem
        rw [List.nodup_cons] at hnd
        rcases List.mem_cons.1 hmem with rfl | hmem'
        · have hz : ∀ k ∈ t, (weight k : ℕ∞) * (ACost.cost n x).toFun k = 0 := by
            intro k hk
            rw [ACost.toFun_cost_ne (fun h => hnd.1 (by rw [← h]; exact hk)), mul_zero]
          simp only [List.map_cons, List.sum_cons, ACost.toFun_cost_self]
          rw [List.sum_eq_zero (by simpa using fun k hk => hz k hk), add_zero]
        · rw [List.map_cons, List.sum_cons, ih hnd.2 hmem',
            ACost.toFun_cost_ne (fun h => hnd.1 (by rw [h]; exact hmem')), mul_zero, zero_add]
  exact key Currency.all Currency.all_nodup hn

/-- …and at the unit balances the tower's operations are stated at. -/
@[simp] theorem ecash_irUnit_skip : ecash (irUnit Currency.skip) = 1 := by
  rw [irUnit, ecash_cost (by simp [Currency.all])]; simp
@[simp] theorem ecash_irUnit_const : ecash (irUnit Currency.const) = 2 := by
  rw [irUnit, ecash_cost (by simp [Currency.all])]; simp
@[simp] theorem ecash_irUnit_copy : ecash (irUnit Currency.copy) = 2 := by
  rw [irUnit, ecash_cost (by simp [Currency.all])]; simp
@[simp] theorem ecash_irUnit_aget : ecash (irUnit Currency.aget) = 3 := by
  rw [irUnit, ecash_cost (by simp [Currency.all])]; simp
@[simp] theorem ecash_irUnit_aset : ecash (irUnit Currency.aset) = 3 := by
  rw [irUnit, ecash_cost (by simp [Currency.all])]; simp
@[simp] theorem ecash_irUnit_ite : ecash (irUnit Currency.ite) = 4 := by
  rw [irUnit, ecash_cost (by simp [Currency.all])]; simp
@[simp] theorem ecash_irUnit_while : ecash (irUnit Currency.«while») = 4 := by
  rw [irUnit, ecash_cost (by simp [Currency.all])]; simp
@[simp] theorem ecash_irUnit_binop (op : Imp.Bop) : ecash (irUnit (binopCurrency op)) = 4 := by
  rw [irUnit, ecash_cost (binopCurrency_mem_all op), weight_binopCurrency]; simp

/-! ## 2. Reading the abstract bound

`m ≤ SPEC Φ (fun _ => T)` is the whole of the abstract side: it makes
`m` nofail, it pins every affordable result to `Φ`, and it caps the cost
at `T`. -/

/-- A `consume`d return refines the `SPEC` that admits exactly it — the
form a *deterministic* abstract program's cost lemma comes in, and the
one both toys supply. -/
theorem le_spec_of_consume_returnT {α : Type} (x : α) (T : ECost) :
    (NRest.returnT x).consume T ≤ NRest.spec (· = x) (fun _ => T) := by
  rw [NRest.consume_returnT, NRest.spec, NRest.rest_le_rest_iff]
  intro v
  by_cases h : v = x
  · subst h; simp
  · simp [h]

open Classical in
/-- Charging a `SPEC` is charging its cost: the equation an abstract
loop's cost induction runs on. -/
theorem consume_spec {α : Type} (P : α → Prop) (T c : ECost) :
    NRest.consume (NRest.spec P (fun _ => T)) c = NRest.spec P (fun _ => c + T) := by
  rw [NRest.spec, NRest.consume_rest, NRest.spec]
  congr 1
  funext v
  split <;> simp

open Classical in
/-- Slack in a `SPEC`'s cost. -/
theorem spec_mono_cost {α : Type} (P : α → Prop) {T T' : ECost} (h : T ≤ T') :
    NRest.spec P (fun _ => T) ≤ NRest.spec P (fun _ => T') := by
  rw [NRest.spec, NRest.spec, NRest.rest_le_rest_iff]
  intro v
  dsimp only
  split
  · exact WithBot.coe_le_coe.2 h
  · exact le_rfl

/-! ## 2b. Building the initial state

The cashing theorem asks for an `Ir.State` that `Γ` holds of and that
the IMP+ environment agrees with. Both toys build theirs with
`State.ofPairs`, so both facts are read off the association list. -/

private theorem mem_of_lookup {β : Type} {l : List (String × β)} {x : String} {v : β}
    (h : l.lookup x = some v) : (x, v) ∈ l := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 h
  simp

/-- Agreement with a state given by association lists: check the listed
cells and nothing else. -/
theorem agree_ofPairs {vs : List (String × ℕ)} {as : List (String × List ℕ)}
    {σ : Imp.Env} (hv : ∀ p ∈ vs, σ.vars p.1 = p.2) (ha : ∀ p ∈ as, σ.arrs p.1 = p.2) :
    agree (Ir.State.ofPairs vs as) σ :=
  ⟨fun x v hx => hv (x, v) (mem_of_lookup hx), fun a xs hx => ha (a, xs) (mem_of_lookup hx)⟩

/-- …and the value invariant, likewise. -/
theorem stateBound_ofPairs {B : ℕ} {vs : List (String × ℕ)}
    {as : List (String × List ℕ)} (hv : ∀ p ∈ vs, p.2 < B)
    (ha : ∀ p ∈ as, ∀ w ∈ p.2, w < B) : Ir.StateBound B (Ir.State.ofPairs vs as) :=
  ⟨fun x v hx => hv (x, v) (mem_of_lookup hx),
    fun a xs hx => ha (a, xs) (mem_of_lookup hx)⟩

open Classical in
/-- What the bound gives at one admissible result. -/
private theorem bound_read {α : Type} {M : α → WithBot ECost} {Φ : α → Prop} {T : ECost}
    (hm : NRest.rest M ≤ NRest.spec Φ (fun _ => T)) {ra : α} {Ca : ECost}
    (hCa : (Ca : WithBot ECost) ≤ M ra) : Φ ra ∧ Ca ≤ T := by
  have hMle : M ra ≤ (if Φ ra then (T : WithBot ECost) else ⊥) := by
    have := NRest.rest_le_rest_iff.1 (by rwa [NRest.spec] at hm) ra
    simpa using this
  have hΦ : Φ ra := by
    by_contra hne
    rw [if_neg hne] at hMle
    exact WithBot.coe_ne_bot (le_bot_iff.1 (le_trans hCa hMle))
  refine ⟨hΦ, ?_⟩
  rw [if_pos hΦ] at hMle
  exact WithBot.coe_le_coe.1 (le_trans hCa hMle)

/-! ## 3. The cashing theorem (export shape (a)) -/

/-- **`spec_of_hnRefine`.** A synthesized program, an abstract bound, a
state its precondition holds of, and a bounds witness make a
`Reasoning.Spec` about the *embedded* program: started in any IMP+
environment agreeing with the IR's initial state, `embed c` runs within
`N` IMP+ time units to an environment that agrees with a final IR state
in which the result assertion holds.

The readout `hQ` is where the destination shape lives (judgment call
P5/D-af); `readout_scalar` / `readout_arr` below discharge it. -/
theorem spec_of_hnRefine {α κ : Type} {Γ Γ' F : Assn} {c : Ir.Com} {d : κ}
    {R : α → κ → Assn} {m : NRest α ECost} {Φ : α → Prop} {T : ECost}
    {B N : ℕ} {s₀ : Ir.State} {Q : α → Imp.Env → Prop}
    (hnr : hnRefine Γ c Γ' d R m)
    (hm : m ≤ NRest.spec Φ (fun _ => T))
    (hs₀ : irSTATE (Γ ∗ F) (s₀, 0))
    (hSB : Ir.StateBound B s₀)
    (hbd : ∃ s' κ', Ir.BigStepB B c s₀ s' κ')
    (hN : ecash T ≤ (N : ℕ∞))
    (hQ : ∀ (ra : α) (s' : Ir.State) (cr : ECost) (σ' : Imp.Env), Φ ra →
      irSTATE (Γ' ∗ R ra d ∗ F ∗ GC) (s', cr) → agree s' σ' → Q ra σ') :
    Reasoning.Spec B (agree s₀) (embed c) (fun _ σ' => ∃ ra, Φ ra ∧ Q ra σ') N := by
  -- the abstract program does not fail, so it is a `rest`
  cases hmm : m with
  | fail => exact absurd (hmm ▸ hm) (NRest.not_fail_le_rest _)
  | rest M =>
    intro σ hσ
    obtain ⟨ra, Ca, hCa, hwp⟩ := hnRefineD hnr hmm hs₀
    obtain ⟨hΦ, hCaT⟩ := bound_read (hmm ▸ hm) hCa
    rw [zero_add, Ir.wp_def] at hwp
    obtain ⟨s', κ', hstep, hpost, haff⟩ := hwp
    -- one execution: the plain run and the bounds witness coincide
    obtain ⟨s₂, κ₂, hB⟩ := hbd
    have hstepB : Ir.BigStepB B c s₀ s' κ' := hstep.bigStepB_of_eq hB
    obtain ⟨σ', hrun, hag, -, -⟩ := embed_run hstepB hSB hσ
    refine ⟨σ', hrun.mono ?_, ra, hΦ, hQ ra s' _ σ' hΦ hpost hag⟩
    -- the cost: affordable at `Ca`, `Ca ≤ T`, priced, then the numeral
    have hT : leCostECost κ' T := fun x => le_trans (haff x) (ACost.le_def.1 hCaT x)
    have := le_trans (cash_le_ecash hT) hN
    exact_mod_cast this

/-- **The run, on its own** (judgment call **P7/D-bm**). `hnRefine`'s wp
adequacy produces a `BigStep` on the way to `spec_of_hnRefine`'s
conclusion and then consumes it; a consumer that bounds its run *along*
a derivation (`BigStep.bigStepB_of_inv`) needs the derivation first, and
re-deriving it means re-running the adequacy chain by hand. So the
projection is published: same three hypotheses, the run and nothing
else. It is stated separately rather than as an extra conclusion of
`spec_of_hnRefine` because the two are used in the opposite order — the
run is what *builds* that theorem's `hbd`. -/
theorem bigStep_of_hnRefine {α κ : Type} {Γ Γ' F : Assn} {c : Ir.Com} {d : κ}
    {R : α → κ → Assn} {m : NRest α ECost} {Φ : α → Prop} {T : ECost} {s₀ : Ir.State}
    (hnr : hnRefine Γ c Γ' d R m)
    (hm : m ≤ NRest.spec Φ (fun _ => T))
    (hs₀ : irSTATE (Γ ∗ F) (s₀, 0)) :
    ∃ s' κ', Ir.BigStep c s₀ s' κ' := by
  cases hmm : m with
  | fail => exact absurd (hmm ▸ hm) (NRest.not_fail_le_rest _)
  | rest M =>
    obtain ⟨ra, Ca, hCa, hwp⟩ := hnRefineD hnr hmm hs₀
    rw [zero_add, Ir.wp_def] at hwp
    obtain ⟨s', κ', hstep, -, -⟩ := hwp
    exact ⟨s', κ', hstep⟩

/-- …and the two halves joined: the bounds witness `spec_of_hnRefine`
asks for, produced from an invariant rather than from a second
derivation. -/
theorem exists_bigStepB_of_hnRefine {α κ : Type} {Γ Γ' F : Assn} {c : Ir.Com} {d : κ}
    {R : α → κ → Assn} {m : NRest α ECost} {Φ : α → Prop} {T : ECost} {B : ℕ}
    {s₀ : Ir.State} {Q : Ir.State → Prop}
    (hnr : hnRefine Γ c Γ' d R m)
    (hm : m ≤ NRest.spec Φ (fun _ => T))
    (hs₀ : irSTATE (Γ ∗ F) (s₀, 0))
    (hpre : Ir.bpre B c Q s₀) :
    ∃ s' κ', Ir.BigStepB B c s₀ s' κ' := by
  obtain ⟨s', κ', hstep⟩ := bigStep_of_hnRefine hnr hm hs₀
  exact hstep.exists_bigStepB_of_inv hpre

/-! ### The two readouts -/

/-- A scalar destination: the result cell holds the abstract result. -/
theorem readout_scalar {Γ' F : Assn} {a : ℕ} {r : String} {s' : Ir.State} {cr : ECost}
    {σ' : Imp.Env} (h : irSTATE (Γ' ∗ natAssn a r ∗ F ∗ GC) (s', cr)) (hag : agree s' σ') :
    σ'.vars r = a := by
  have h' : irSTATE ((r ↦ᵥ a) ∗ (Γ' ∗ (F ∗ GC))) (s', cr) := by
    have he : (Γ' ∗ natAssn a r ∗ F ∗ GC) = (r ↦ᵥ a) ∗ (Γ' ∗ (F ∗ GC)) := by
      rw [natAssn_def]; ac_rfl
    rwa [he] at h
  exact hag.var (Ir.ptoVar_vars h')

/-- An array destination: the result array holds the abstract result. -/
theorem readout_arr {Γ' F : Assn} {xs : List ℕ} {A : String} {s' : Ir.State} {cr : ECost}
    {σ' : Imp.Env} (h : irSTATE (Γ' ∗ arrayAssn xs A ∗ F ∗ GC) (s', cr)) (hag : agree s' σ') :
    σ'.arrs A = xs := by
  have h' : irSTATE ((A ↦ₐ xs) ∗ (Γ' ∗ (F ∗ GC))) (s', cr) := by
    have he : (Γ' ∗ arrayAssn xs A ∗ F ∗ GC) = (A ↦ₐ xs) ∗ (Γ' ∗ (F ∗ GC)) := by
      rw [arrayAssn_def]; ac_rfl
    rwa [he] at h
  exact hag.arr (Ir.ptoArr_arrs h')

/-! ## 4. The boundary wrapper (export shape (b))

`Transfer.Solves` is three facts: the program compiles under the layout,
admissible inputs fit under the bound, and on every admissible input the
program runs from `initEnv` to the answer within the cost. The third is
exactly what `Harness.lean`'s marshal lemmas produce, so the wrapper is
a repackaging and nothing more.

The array lengths `ext` are chosen per input — an algorithm sizes its
arrays by what it reads, and `Solves` quantifies them existentially for
that reason — so they are existential here too. -/

/-- **`solves_of_spec`.** A `Spec` from `initEnv`, one per admissible
input, is a `Solves`. -/
theorem solves_of_spec {L : Compile.Layout} {c : Imp.Com} {D : Set (List ℕ)}
    {f : List ℕ → List ℕ} {B K : List ℕ → ℕ}
    (hok : Compile.Com.Ok L c) (hinp : ∀ x ∈ D, ∀ v ∈ x, v < B x)
    (hspec : ∀ x ∈ D, ∃ ext : String → ℕ,
      Reasoning.Spec (B x) (fun σ => σ = Imp.initEnv ext x) c
        (fun _ σ' => σ'.out = f x) (K x)) :
    Transfer.Solves L c D f B K where
  ok := hok
  inp := hinp
  run := by
    intro x hx
    obtain ⟨ext, hs⟩ := hspec x hx
    obtain ⟨σ', hrun, hout⟩ := hs _ rfl
    exact ⟨ext, σ', hrun, hout⟩

/-- …and the last step, spelled out: the compiled machine program
computes `f` in `L.const` machine steps per unit of IMP+ cost. -/
theorem computesInTime_of_spec {L : Compile.Layout} {c : Imp.Com} {D : Set (List ℕ)}
    {f : List ℕ → List ℕ} {B K : List ℕ → ℕ} {w : ℕ}
    (hok : Compile.Com.Ok L c) (hinp : ∀ x ∈ D, ∀ v ∈ x, v < B x)
    (hspec : ∀ x ∈ D, ∃ ext : String → ℕ,
      Reasoning.Spec (B x) (fun σ => σ = Imp.initEnv ext x) c
        (fun _ σ' => σ'.out = f x) (K x))
    (hfit : ∀ x ∈ D, L.FitsWords (B x) w) :
    Lax13.RamComputes.ComputesInTime w (Compile.compileProgram L c) D f
      (fun x => L.const * K x) :=
  (solves_of_spec hok hinp hspec).computesInTime hfit

/-! ## 5. Refute before prove

Before any of the above was proved, the cost arithmetic was checked to
run in the right direction on a concrete execution — the design record's
`cash κ ≤ credits` chain is an inequality, and an inequality proved in
the wrong direction is a theorem about nothing.

The check: `Ir/Semantics.lean`'s `countdown` at `n = 2` costs
`2·ir.const-free` … the account its evaluator computes, cashed, is `22`
(`Sim.lean`'s gate), and the balance a caller would have to supply for
the run to be affordable is that same account lifted into `ℕ∞`. So
`ecash` of the lifted account is `cash` of the account — the two price
maps agree where both apply — and the inequality `cash κ ≤ ecash T` is
*tight* at `T = lift κ`, not slack in the wrong direction. -/

section Refute

/-- The lift of a run's account into a balance: what a caller who
supplies exactly the run's cost owns. -/
private def liftOf (κ : Ir.Cost) : ECost := ⟨fun k => (κ.toFun k : ℕ∞)⟩

private theorem leCostECost_liftOf (κ : Ir.Cost) : leCostECost κ (liftOf κ) := fun _ => le_rfl

/-- Tightness: at the lifted account the two price maps agree, so the
cashing inequality is an equality there and cannot be pointing the wrong
way. -/
theorem ecash_liftOf (κ : Ir.Cost) : ecash (liftOf κ) = (cash κ : ℕ∞) := by
  simp only [ecash, cash, liftOf, Nat.cast_list_sum, List.map_map]
  congr 1

/-- The concrete instance: the countdown's own account, both sides. -/
example : ecash (liftOf (Ir.Gate.countdownOut 2).2) = (22 : ℕ∞) := by
  rw [ecash_liftOf, show cash (Ir.Gate.countdownOut 2).2 = 22 from by decide +kernel]
  rfl

-- …and the direction is the one the theorem needs: an account is
-- priced at most at the balance that affords it.
example : (cash (Ir.Gate.countdownOut 2).2 : ℕ∞) ≤ ecash (liftOf (Ir.Gate.countdownOut 2).2) :=
  cash_le_ecash (leCostECost_liftOf _)

end Refute

/-! ## The axiom check -/

#print axioms spec_of_hnRefine
#print axioms solves_of_spec
#print axioms cash_le_ecash

end Lax13Proofs.Refine.Codegen
