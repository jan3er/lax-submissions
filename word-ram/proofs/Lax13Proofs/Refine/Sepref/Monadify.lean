import Lax13Proofs.Refine.Sepref.IdOp
import Lax13Proofs.Refine.NREST.Combinators
import Lax13Proofs.Refine.NREST.Pw

/-!
# Sepref phase two: monadify

Port of `thys/sepref/Sepref_Monadify.thy` of `isabelle_llvm_time`
(Lammich) at the pin recorded in `plans/word-ram/refinement-tower/design.md`
§1 — rev `42dd7f5` — together with the arity/combinator equation
*schema* of `thys/sepref/Sepref_Combinator_Setup.thy`. The verbatim
source text this file is checked against is
`plans/word-ram/refinement-tower/p4-sepref-extracts.md` §4 (the
`EVAL`/`SP`/`PASS` markers) and
`plans/word-ram/refinement-tower/p4-sepref-deep-extracts.md` §6 (the
generated `mcomb` equations); both `.thy` files were read whole at the
pin. Design record §3, P4 row 5:

> phase 2 monadify (`Sepref_Monadify.thy`) → `Sepref/Monadify.lean` | =
> (ANF-ization with explicit evaluation order and duplicate-argument
> splitting)

The source's header says what the phase is for, verbatim:

> In this phase, a monadic program is converted to complete monadic
> form, that is, computation of compound expressions are made visible as
> top-level operations in the monad.
>
> The monadify process is separated into 2 steps.
>
> 1. In a first step, eta-expansion is used to add missing operands to
>    operations and combinators. This way, operators and combinators
>    always occur with the same arity, which simplifies further
>    processing.
> 2. In a second step, computation of compound operands is flattened,
>    introducing new bindings for the intermediate values.

and, on the two databases that drive them:

> Internally, the package first applies rewriting rules from
> `sepref_monadify_arity`, which use eta-expansion to ensure that every
> combinator has enough actual parameters. Moreover, this phase will
> mark recursive calls by the tag `RCALL`.
>
> Next, rewriting rules from `sepref_monadify_comb` are used to add
> `EVAL`-tags to plain expressions that should be evaluated in the
> monad. The `EVAL` tags are flattened using a default simproc that
> generates left-to-right argument order.

## Deliberate absences, with ledger citations

**`RECT` / `RECT'` / `RCALL` have no arity and no combinator
equations.** The source's `dflt_arity` and `dflt_comb` carry three
entries each for them, and this port carries none, by design record
**ledger D6**: "translate targets loop-form only; `RECT` must be refined
to `whileT` before synthesis", because IMP+ `Com` has no
procedures/recursion to compile general recursion into. `RCALL` is
nevertheless *defined* (it is a marker every reader of the source will
look for, and defining it costs one line), and it is what an arity
equation for `RECT` would introduce if D6 were ever lifted; nothing in
this file produces or consumes it. The four `case_list`/`case_option`
entries and the `Let` entries of `dflt_arity`/`dflt_comb`/
`dflt_plain_comb` are demand-driven backlog — see the P4/D-bm flag for
what the abstract programs actually use.

## Judgment calls (P4/D-ba onward is wave B2's range; this file uses
w onward, IdOp.lean holds m–v)

**P4/D-bk — `monadifyCore` is term-level, not goal-level.** The source's
driver is `monadify_tac dbg ctxt`, a `PHASES'` pipeline of six tactics
each of which is a `CONVERSION` on the *abstract-program slot of an
`hn_refine` goal* (`Sepref_Basic.hn_refine_concl_conv_a`,
`dest_hn_refine`). `hnRefine` is another wave's file, so the pipeline
here takes and returns the abstract program itself:

```
monadifyCore (pps : Array Expr) (a : Expr) : MetaM (Expr × Expr)
```

`pps` is what the source's `mark_params` reads out of Γ — the
`hn_ctxt`-tagged conjuncts of the precondition, `strip_star P |>
map_filter (dest_hn_ctxt_opt #> map_option #2)` — supplied by the caller
instead of extracted here. The returned proof has direction
**`a = a'`** (left to right, "the original equals the monadified form"),
which is the direction Lean's rewriting naturally produces and the
direction wave C wants: `hnRefine`'s abstract slot is rewritten
*forwards*, so the proof is used as `h ▸ …` or through the source's own
`hn_refine`-congruence step. Every sub-phase reports through the
`Autoref/Phases.lean` failure envelope (its delta P6) with the source's
own phase name and this pipeline's ordinal:
`sepref: phase 'comb' (priority 30) failed.` + the offending subterm.
The `id_op` phase of `Sepref/IdOp.lean` is priority 10; these six are
20, 30, 40, 50, 60, 70 in the source's own order.

**P4/D-bl — the `EVAL`-flattening simproc becomes an explicit pass, and
its failures are *silent* exactly as the source's are.** The source
registers `monadify_simproc` on the pattern `EVAL$a` with
`proc = K (try o monadify_conv_aux)`: the `try` is load-bearing, because
`monadify` raises `TERM ("monadify: higher-order", …)` when the head of
the tagged application is an abstraction, and swallowing that is
precisely how such an `EVAL` survives to the `check_EVAL` phase, which
is the phase that reports it. `flattenPass` reproduces this: each node
is attempted, a failure leaves the node alone, and `check_EVAL` names
the survivor. (Reproducing the `try` was not obvious and is the reason
gate case (d) exists at all.)

**P4/D-bm — which combinators got equations, and why the rest are
backlog.** The source's `dflt_arity`/`dflt_comb` are written for HOL's
own combinator set (`If`, `Let`, `case_list`, `case_prod`,
`case_option`, `RETURN`, `RECT`, `RECT'`, `RCALL`). Instantiated to what
P1 actually has, and to what the abstract programs actually use, that is
`NRest.returnT`, `NRest.MIf`, `NRest.whileT` and `NRest.whileIET`. The
evidence is `Refine/Examples/Bfs.lean`: `bfsAlg` is built from
`NRest.bindT`, `NRest.consume`, `NRest.returnT`, `NRest.MIf` and
`NRest.whileIET` and nothing else, and `bfsBody` adds `NRest.assert` and
`NRest.spec`; `Refine/Examples/ArrayFill.lean` uses no combinator
outside that set. In particular:

* **`Let` gets no equations.** Lean's `let` is not a constant — it is
  `Expr.letE`, a term-level binder — so `Let$x$f` has no Lean spelling
  to state an equation over, and no abstract program in P1 uses a
  monadic `let` (they use `bindT`, which is what a monadic let *is*).
  If a program ever needs one, `Expr.letE` must first be zeta-expanded
  into a `bindT`, which is a pre-pass, not an equation.
* **`case_prod` gets no equations.** Checked against the actual state
  type: `Bfs.State n` *is* a triple, but `bfsAlg`/`bfsBody` never
  pattern-match it — they use the projections `distArr`/`front`/`level`,
  which are ordinary operations. There is no `case_prod` in either
  example, so an equation for it would be an unexercised claim.
* **`case_list` / `case_option`** likewise: absent from both examples.
* **`whileIT` does not exist in P1.** The brief's `whileIT` is
  `NRest.whileIET` here (`Combinators.lean`): P1 ported the source's
  *energy*-annotated loop, and the plain invariant-only `whileIT` was
  never a separate constant. Both `whileT` and `whileIET` get equations.
* **`NRest.consume` / `assert` / `spec` get no combinator equations**
  and need none: they are *operations*, and an operation's equation is
  what `sepref_register` generates from the `mcomb` schema
  (deep extract §6), which is wave C's — a registration is only useful
  once there is an `hnRefine` rule to consume it. The schema itself is
  ported and proved here (`mcomb1`/`mcomb2`/`mcomb3`), so that wave C
  instantiates a theorem rather than inventing one.

**P4/D-bn — `bindT_returnT` is re-proved at a general carrier.**
`NREST/Pw.lean` states the monad's right identity where the source
states it, at `('b, enat) nrest`: `bindT M returnT = M` for
`M : NRest α ℕ∞`. `remove_pass_simps`(2) is
`bindT$m$(λ₂x. PASS$x) ≡ m`, which the pipeline needs at the *cost*
carrier `ECost = ACost String ℕ∞`. The proof of `Pw.lean`'s version uses
only `consumeB_returnT`, which is already stated at
`[CompleteLattice γ] [AddMonoid γ]`, so it is repeated here at that
generality rather than editing a P1 file mid-wave. Recommend folding
`bindT_returnT_gen` back into `NREST/Pw.lean` as the general form and
deleting this copy when P1 is next touched.

**P4/D-bo — the `SP_cong` / `PR_CONST_cong` barrier is an explicit walk,
because Lean's `@[congr]` will not carry it.** The source's
`lemma SP_cong[cong]: "SP x ≡ SP x"` is a zero-premise congruence rule
whose entire content is "do not rewrite inside `SP`"; it is what stops the
arity and combinator equations from re-firing on their own output, and
therefore what makes the two phases terminate at all. The obvious
rendering — the same statement tagged `@[congr]` — was tried first and
**refuted**: Lean accepts the attribute without complaint and then
rewrites inside `SP` anyway (probe pinned in the gate:
`SP (2+2) = SP 4` is closed by `simp`, which it must not be), and with it
the arity phase diverges on gate case (a) with
`maximum recursion depth`. So the two phases run as `Monadify.rewriteDB`,
a top-down single-node rewriter over the rule database that refuses to
descend into `SP` or `PR_CONST` — the same normal form the source's
simpset-plus-cong reaches, by the same argument. The two lemmas are still
stated, untagged, because the source states them and because they are the
specification `rewriteDB` implements. If a future Lean honours the
attribute, `rewriteDB` can collapse back into a `simp` call.

**P4/D-bp — the markers are polymorphic in the cost carrier where the
source's ML pins `ecost`.** `EVAL`, `PASS`, `monadify_simps`,
`remove_pass_simps` and the comb equations are stated at
`{γ : Type} [Zero γ]` / `[CompleteLattice γ] [AddMonoid γ]`, not at
`ECost`. The source's *lemmas* are polymorphic too; only its ML
term-builders hard-code `(?'a, ecost) nrest` (`@{mk_term "(EVAL$?a)::
(?'a, ecost) nrest"}`), because ML has to write a type down. The Lean
pass reads the carrier off the term it is rewriting instead, so nothing
is pinned and the pipeline works at any carrier. Strictly more general;
recorded because it is a visible difference from the source text.
-/

open Lean Meta Elab

universe u v

namespace Lax13Proofs.Refine.Sepref

/-! ## The marker constants -/

/-- The source's `definition SP where [simp]: "SP x ≡ x"`, with its own
comment:

> Tag to protect content from further application of arity and
> combinator equations. -/
def SP {α : Sort u} (x : α) : α := x

/-- The source's `SP` definition, with the source's own `[simp]`. -/
@[simp] theorem SP_def {α : Sort u} (x : α) : SP x = x := rfl

/-- The source's `lemma SP_cong[cong]: "SP x ≡ SP x"`. Zero premises: the
whole content of the rule is "do not rewrite inside `SP`", which is what
makes the arity and combinator phases terminate. Stated here for
citability, **without** Lean's `@[congr]`, because that attribute does
not give the rule its effect — see delta P4/D-bo and the gate's probe;
`Monadify.rewriteDB` is where the barrier actually lives. -/
theorem SP_cong {α : Sort u} (x : α) : SP x = SP x := rfl

/-- The source's `lemma PR_CONST_cong[cong]: "PR_CONST x ≡ PR_CONST x"`,
the same device for `Sepref/IdOp.lean`'s `PR_CONST`, with the same
caveat. -/
theorem PR_CONST_cong {α : Sort u} (x : α) : PR_CONST x = PR_CONST x := rfl

/-- The source's `definition RCALL where [simp]: "RCALL D ≡ D"`, with
its own comment:

> Tag that marks recursive call.

Defined and never used: the arity equations that would introduce it are
`RECT`'s and `RECT'`'s, which ledger **D6** puts out of scope (see the
header). -/
def RCALL {α : Sort u} (D : α) : α := D

/-- The source's `RCALL` definition, with the source's own `[simp]`. -/
@[simp] theorem RCALL_def {α : Sort u} (D : α) : RCALL D = D := rfl

/-- The source's `definition EVAL where [simp]: "EVAL x ≡ RETURN x"`,
with its own comment:

> Tag that marks evaluation of plain expression for monadify phase.

This is the plain/monadic boundary the whole phase turns on: `EVAL x`
says "`x` is an ordinary expression that must be lifted into the monad
before flattening". Polymorphic in the carrier — delta P4/D-bp. -/
noncomputable def EVAL {α γ : Type} [Zero γ] (x : α) : NRest α γ := NRest.returnT x

/-- The source's `EVAL` definition, with the source's own `[simp]`. -/
@[simp] theorem EVAL_def {α γ : Type} [Zero γ] (x : α) :
    (EVAL x : NRest α γ) = NRest.returnT x := rfl

/-- The source's `definition [simp]: "PASS ≡ RETURN"`, with its own
comment:

> Pass on value, invalidating old one.

Stated with the argument applied (the source eta-contracts; every use is
`PASS$x`), and with `returnT`'s own binder order, which the term-level
pass relies on when it swaps one for the other. -/
noncomputable def PASS {α γ : Type} [Zero γ] (x : α) : NRest α γ := NRest.returnT x

/-- The source's `PASS` definition, with the source's own `[simp]`. -/
@[simp] theorem PASS_def {α γ : Type} [Zero γ] (x : α) :
    (PASS x : NRest α γ) = NRest.returnT x := rfl

/-- The source's `definition COPY :: 'a ⇒ 'a where [simp]: "COPY x ≡ x"`,
with its own comment:

> Marks required copying of parameter. -/
def COPY {α : Sort u} (x : α) : α := x

/-- The source's `COPY` definition, with the source's own `[simp]`. -/
@[simp] theorem COPY_def {α : Sort u} (x : α) : COPY x = x := rfl

/-! ## The monad law the phase needs at the cost carrier (delta P4/D-bn) -/

/-- `NREST/Pw.lean`'s `bindT_returnT` at a general carrier: the monad's
right identity for any `[CompleteLattice γ] [AddMonoid γ]`, which is what
`remove_pass_simps`(2) needs at `ECost`. Same proof as P1's, whose only
ingredient — `consumeB_returnT` — is already general. -/
theorem bindT_returnT_gen {α γ : Type} [CompleteLattice γ] [AddMonoid γ]
    (M : NRest α γ) : NRest.bindT M NRest.returnT = M := by
  cases M with
  | fail => rfl
  | rest X =>
    rw [NRest.bindT_rest_eq_iSup,
      show (⨆ x, NRest.consumeB (NRest.returnT x : NRest α γ) (X x))
          = ⨆ x, NRest.rest (NRest.single x (X x)) from
        iSup_congr fun x => NRest.consumeB_returnT x (X x), NRest.iSup_rest]
    congr 1
    funext w
    rw [iSup_apply]
    refine le_antisymm (iSup_le fun x => ?_) (le_iSup_of_le w ?_)
    · by_cases h : w = x
      · subst h; simp
      · simp [h]
    · simp

/-! ## `monadify_simps`, `remove_pass_simps`, `RET_COPY_PASS_eq`

The source's three lemma groups, in its own tagged spelling. -/

/-- The source's `monadify_simps`(1),
`NREST.bindT$(RETURNT$x)$(λ⇩2x. f x) = f x`: the left identity in tagged
form. This and `monadify_simps`(2) are exactly what the source's
`monadify_conv_aux` discharges each flattening step with. -/
theorem monadify_simps_bind {α β γ : Type} [CompleteLattice γ] [AddMonoid γ]
    (x : α) (f : α → NRest β γ) :
    (NRest.bindT $ᵃ (NRest.returnT $ᵃ x) $ᵃ (λ₂ y => f y)) = f x := by
  show NRest.bindT (NRest.returnT x) (ABS2 fun y => f y) = f x
  exact (NRest.returnT_bindT x _).trans (ABS2_apply _ x)

/-- The source's `monadify_simps`(2), `EVAL$x ≡ RETURN$x`. -/
theorem monadify_simps_eval {α γ : Type} [Zero γ] (x : α) :
    (EVAL $ᵃ x : NRest α γ) = NRest.returnT $ᵃ x := rfl

/-- The source's `remove_pass_simps`(1),
`NREST.bindT$(PASS$x)$(λ⇩2x. f x) ≡ f x`. -/
theorem remove_pass_simps_left {α β γ : Type} [CompleteLattice γ] [AddMonoid γ]
    (x : α) (f : α → NRest β γ) :
    (NRest.bindT $ᵃ (PASS $ᵃ x) $ᵃ (λ₂ y => f y)) = f x := by
  show NRest.bindT (NRest.returnT x) (ABS2 fun y => f y) = f x
  exact (NRest.returnT_bindT x _).trans (ABS2_apply _ x)

/-- The source's `remove_pass_simps`(2), `NREST.bindT$m$(λ⇩2x. PASS$x) ≡ m`.
This is the one that needs `bindT_returnT_gen` (delta P4/D-bn). -/
theorem remove_pass_simps_right {α γ : Type} [CompleteLattice γ] [AddMonoid γ]
    (m : NRest α γ) :
    (NRest.bindT $ᵃ m $ᵃ (λ₂ x => PASS $ᵃ x)) = m := by
  show NRest.bindT m (ABS2 fun x => PASS x) = m
  exact bindT_returnT_gen m

/-- The source's `lemma RET_COPY_PASS_eq: "RETURN$(COPY$p) = PASS$p"` —
the equation the `dup` phase's conversion is discharged by, and the
reason inserting a `COPY` is free. -/
theorem RET_COPY_PASS_eq {α γ : Type} [Zero γ] (p : α) :
    (NRest.returnT $ᵃ (COPY $ᵃ p) : NRest α γ) = PASS $ᵃ p := rfl

/-! ## Arity alignment equations (`sepref_monadify_arity`)

The source's `dflt_arity`, instantiated to P1's combinator set
(delta P4/D-bm). Each is stated exactly as the source states it — the
head bare on the left, `SP`-protected and `λ₂`-eta-expanded on the
right, so that the rule fires once and its own output is protected from
it. Note the source's own parenthesisation: `SP RETURN$x` is
`(SP RETURN)$x`, i.e. `SP` protects the *head*, not the application;
Lean's application binds tighter than `infixl:900` just as Isabelle's
does, so the spelling carries over character for character.

Every one is proved by `rfl`: the source proves them
`by (simp_all only: SP_def APP_def PROTECT2_def RCALL_def)`, and in Lean
all four tags are definitional identities, so the equation is `rfl` up
to eta. -/

/-- The source's `dflt_arity`(1), `RETURN ≡ λ⇩2x. SP RETURN$x`. -/
@[sepref_monadify_arity] theorem arity_returnT {α γ : Type} [Zero γ] :
    (NRest.returnT : α → NRest α γ) = λ₂ x => SP NRest.returnT $ᵃ x := rfl

/-- The source's `dflt_arity`(7), `If ≡ λ⇩2b t e. SP If$b$t$e`, at P1's
monadic branch `NRest.MIf`. -/
@[sepref_monadify_arity] theorem arity_MIf {α γ : Type} [AddMonoid γ] [One γ] :
    (NRest.MIf : Bool → NRest α (ACost String γ) → NRest α (ACost String γ) →
        NRest α (ACost String γ)) =
      λ₂ b t e => SP NRest.MIf $ᵃ b $ᵃ t $ᵃ e := rfl

/-- Our `whileT`'s arity equation, at the shape of the source's own
plain-combinator entries (`If`'s, not `RECT`'s — there is no `D`
parameter to mark with `RCALL`, which is why ledger D6 costs nothing
here). -/
@[sepref_monadify_arity] theorem arity_whileT {α γ : Type} [CompleteLattice γ] [AddMonoid γ] :
    (NRest.whileT : (α → Bool) → (α → NRest α γ) → α → NRest α γ) =
      λ₂ b c s => SP NRest.whileT $ᵃ b $ᵃ c $ᵃ s := rfl

/-- Our `whileIET`'s arity equation. The invariant and energy arguments
are aligned like any others: they are definitionally inert, but the
phase must still see the combinator at full arity. -/
@[sepref_monadify_arity] theorem arity_whileIET {α γ ε : Type}
    [CompleteLattice γ] [AddMonoid γ] :
    (NRest.whileIET : (α → Prop) → (α → ε) → (α → Bool) → (α → NRest α γ) → α → NRest α γ) =
      λ₂ I E b c s => SP NRest.whileIET $ᵃ I $ᵃ E $ᵃ b $ᵃ c $ᵃ s := rfl

/-! ## Combinator equations (`sepref_monadify_comb`)

The source's `dflt_comb` and `evalcomb_PR_CONST`, instantiated the same
way. Each says: before the combinator runs, its *value* arguments must
be evaluated in the monad, left to right; the combinator application
itself is then `SP`-protected so the rule does not re-fire. -/

/-- The source's `dflt_comb`(8),
`RETURN$x ≡ NREST.bindT$(EVAL$x)$(λ⇩2x. SP (RETURN$x))`. -/
@[sepref_monadify_comb] theorem comb_returnT {α γ : Type}
    [CompleteLattice γ] [AddMonoid γ] (x : α) :
    (NRest.returnT $ᵃ x : NRest α γ) =
      NRest.bindT $ᵃ (EVAL $ᵃ x) $ᵃ (λ₂ y => SP (NRest.returnT $ᵃ y)) := by
  simp only [APP_def, PROTECT2_def, SP_def, EVAL_def, NRest.returnT_bindT]

/-- The source's `dflt_comb`(7),
`If$b$t$e ≡ NREST.bindT$(EVAL$b)$(λ⇩2b. (SP If$b$t$e))`, at `NRest.MIf`.
Only the *condition* is evaluated: the branches are already monadic. -/
@[sepref_monadify_comb] theorem comb_MIf {α γ : Type}
    [CompleteLattice γ] [AddMonoid γ] [One γ]
    (b : Bool) (t e : NRest α (ACost String γ)) :
    (NRest.MIf $ᵃ b $ᵃ t $ᵃ e) =
      NRest.bindT $ᵃ (EVAL $ᵃ b) $ᵃ (λ₂ c => SP NRest.MIf $ᵃ c $ᵃ t $ᵃ e) := by
  simp only [APP_def, PROTECT2_def, SP_def, EVAL_def, NRest.returnT_bindT]

/-- Our `whileT`'s combinator equation, at the shape of the source's
`RECT` entry with the recursion argument dropped: the loop's *initial
state* is the value that must be evaluated in the monad. -/
@[sepref_monadify_comb] theorem comb_whileT {α γ : Type}
    [CompleteLattice γ] [AddMonoid γ] (b : α → Bool) (c : α → NRest α γ) (s : α) :
    (NRest.whileT $ᵃ b $ᵃ c $ᵃ s) =
      NRest.bindT $ᵃ (EVAL $ᵃ s) $ᵃ (λ₂ t => SP NRest.whileT $ᵃ b $ᵃ c $ᵃ t) := by
  simp only [APP_def, PROTECT2_def, SP_def, EVAL_def, NRest.returnT_bindT]

/-- Our `whileIET`'s combinator equation. -/
@[sepref_monadify_comb] theorem comb_whileIET {α γ ε : Type}
    [CompleteLattice γ] [AddMonoid γ] (I : α → Prop) (E : α → ε)
    (b : α → Bool) (c : α → NRest α γ) (s : α) :
    (NRest.whileIET $ᵃ I $ᵃ E $ᵃ b $ᵃ c $ᵃ s) =
      NRest.bindT $ᵃ (EVAL $ᵃ s) $ᵃ (λ₂ t => SP NRest.whileIET $ᵃ I $ᵃ E $ᵃ b $ᵃ c $ᵃ t) := by
  simp only [APP_def, PROTECT2_def, SP_def, EVAL_def, NRest.returnT_bindT]

/-- The source's `lemma evalcomb_PR_CONST[sepref_monadify_comb]:
"EVAL$(PR_CONST x) ≡ SP (RETURN$(PR_CONST x))"`: an atomic constant is
already a value, so evaluating it is a `RETURN`, not a flattening. -/
@[sepref_monadify_comb] theorem evalcomb_PR_CONST {α γ : Type} [Zero γ] (x : α) :
    (EVAL $ᵃ (PR_CONST x) : NRest α γ) = SP (NRest.returnT $ᵃ (PR_CONST x)) := rfl

/-! ## The `mcomb` schema (`Sepref_Combinator_Setup.thy`, deep extract §6)

The source's `mk_mcomb` ML function generates these on demand for each
`sepref_register`ed constant; the deep extract quotes the manual forms
for arities one to three. They are the *specification* of what the
`EVAL`-flattening pass below builds, and what wave C's registration
mechanism will instantiate rather than re-derive. Proved, not tagged:
tagging a schematic `c` into `sepref_monadify_comb` would make it fire on
every monadic application. -/

/-- The source's `mk_mcomb1`,
`c$x1 ≡ (⤜)$(EVAL$x1)$(λ⇩2x1. SP (c$x1))`. -/
theorem mcomb1 {α β γ : Type} [CompleteLattice γ] [AddMonoid γ]
    (c : α → NRest β γ) (x₁ : α) :
    (c $ᵃ x₁) = NRest.bindT $ᵃ (EVAL $ᵃ x₁) $ᵃ (λ₂ y₁ => SP (c $ᵃ y₁)) := by
  simp only [APP_def, PROTECT2_def, SP_def, EVAL_def, NRest.returnT_bindT]

/-- The source's `mk_mcomb2`,
`c$x1$x2 ≡ (⤜)$(EVAL$x1)$(λ⇩2x1. (⤜)$(EVAL$x2)$(λ⇩2x2. SP (c$x1$x2)))` —
note the argument order, which is what "generates left-to-right argument
order" in the source's header comment means. -/
theorem mcomb2 {α₁ α₂ β γ : Type} [CompleteLattice γ] [AddMonoid γ]
    (c : α₁ → α₂ → NRest β γ) (x₁ : α₁) (x₂ : α₂) :
    (c $ᵃ x₁ $ᵃ x₂) =
      NRest.bindT $ᵃ (EVAL $ᵃ x₁) $ᵃ (λ₂ y₁ =>
        NRest.bindT $ᵃ (EVAL $ᵃ x₂) $ᵃ (λ₂ y₂ => SP (c $ᵃ y₁ $ᵃ y₂))) := by
  simp only [APP_def, PROTECT2_def, SP_def, EVAL_def, NRest.returnT_bindT]

/-- The source's `mk_mcomb3`. -/
theorem mcomb3 {α₁ α₂ α₃ β γ : Type} [CompleteLattice γ] [AddMonoid γ]
    (c : α₁ → α₂ → α₃ → NRest β γ) (x₁ : α₁) (x₂ : α₂) (x₃ : α₃) :
    (c $ᵃ x₁ $ᵃ x₂ $ᵃ x₃) =
      NRest.bindT $ᵃ (EVAL $ᵃ x₁) $ᵃ (λ₂ y₁ =>
        NRest.bindT $ᵃ (EVAL $ᵃ x₂) $ᵃ (λ₂ y₂ =>
          NRest.bindT $ᵃ (EVAL $ᵃ x₃) $ᵃ (λ₂ y₃ => SP (c $ᵃ y₁ $ᵃ y₂ $ᵃ y₃)))) := by
  simp only [APP_def, PROTECT2_def, SP_def, EVAL_def, NRest.returnT_bindT]

/-! ## The pipeline

The source's `structure Sepref_Monadify`, re-expressed term-level
(delta P4/D-bk). -/

namespace Monadify

open IdOp (simpOnlyContext dbContext patStep isPRCONST?)

/-! ### The failure envelope and the sub-phase chain -/

/-- `Autoref/Phases.lean`'s uniform envelope (its delta P6), with
`sepref` for `autoref` and the source's own phase names. -/
def envelope (name : String) (prio : Nat) (inner : MessageData) : MessageData :=
  m!"sepref: phase '{name}' (priority {prio}) failed.\n{inner}"

/-- One sub-phase's result: the rewritten program and, when it changed,
a proof that the incoming program equals it. -/
abbrev StepResult := Expr × Option Expr

/-- Run one sub-phase under the envelope. -/
def runStep (name : String) (prio : Nat) (k : Expr → MetaM StepResult) (e : Expr) :
    MetaM StepResult := do
  try k e
  catch ex => throwError (envelope name prio ex.toMessageData)

/-- The running state of `monadifyCore`: the current program, and a
proof that the *original* equals it (`none` while nothing has
changed). -/
structure Chain where
  /-- The current program. -/
  cur : Expr
  /-- Proof that the original program equals `cur`. -/
  pf? : Option Expr := none

/-- Extend the chain by one sub-phase's result. -/
def Chain.push (c : Chain) (r : StepResult) : MetaM Chain := do
  match c.pf?, r.2 with
  | none, none => return { cur := r.1, pf? := none }
  | some a, none => return { cur := r.1, pf? := some a }
  | none, some b => return { cur := r.1, pf? := some b }
  | some a, some b => return { cur := r.1, pf? := some (← mkEqTrans a b) }

/-! ### `λ₂` as data

A `λ₂`-protected abstraction reaches this phase in either of two
shapes, and the walks must accept both: `ABS2 (fun x => body)`, which is
what the *notation* elaborates to (`ABS2` is an `abbrev`, so the
application survives), and `fun x => PROTECT2 body DUMMY`, which is what
`Sepref/IdOp.lean`'s `protect` builds. Everything this file *emits* uses
the folded shape, so that a program which needs no change comes back
character for character. -/

/-- Match a `λ₂` abstraction in either shape, returning the binder's
name, domain, binder info and its *unprotected* body under the
binder. -/
def asABS2? (e : Expr) : MetaM (Option (Name × Expr × Expr × BinderInfo)) := do
  if e.isAppOf ``ABS2 then
    match e.getAppArgs with
    | #[_, _, f] =>
      match f with
      | .lam n d b bi => return some (n, d, b, bi)
      | _ =>
        match ← whnfR e with
        | .lam n d b bi =>
          match IdOp.isPROTECT2? b with
          | some (x, _) => return some (n, d, x, bi)
          | none => return none
        | _ => return none
    | _ => return none
  match e with
  | .lam n d b bi =>
    match IdOp.isPROTECT2? b with
    | some (x, _) => return some (n, d, x, bi)
    | none => return none
  | _ => return none

/-- Build `λ₂ x => body` in the folded shape, given the body as a
function of the (already-introduced) local `v`. -/
def mkABS2 (v body : Expr) : MetaM Expr := do
  mkAppM ``ABS2 #[← mkLambdaFVars #[v] body]

/-! ### Proof plumbing -/

/-- Prove `lhs = rhs` with a `simp only` over the named lemmas, falling
back to `rfl`. This is the source's `Refine_Util.f_tac_conv`: compute the
new term, then discharge the equation with a fixed, minimal simp set. -/
def proveEqBySimp (lhs rhs : Expr) (names : Array Name) (what : String) : MetaM Expr := do
  let ty ← mkEq lhs rhs
  let mv ← mkFreshExprSyntheticOpaqueMVar ty
  let (g?, _) ← simpTarget mv.mvarId! (← simpOnlyContext names)
  match g? with
  | none => instantiateMVars mv
  | some g =>
    try
      g.refl
      instantiateMVars mv
    catch _ =>
      throwError "{what}: could not justify the rewrite.\n\
        before:{indentExpr lhs}\nafter:{indentExpr rhs}\n\
        residual goal:{indentD (← Meta.ppGoal g)}"

/-- Prove `lhs = rhs` by `rfl` — used by the sub-phases whose rewrites
are definitional (arity alignment is eta-expansion under identity tags;
`mark_params` swaps `returnT` for `PASS` and `dup` swaps `PASS p` for
`returnT (COPY p)`, and both are the *same definition* under two
names). -/
def proveEqByRfl (lhs rhs : Expr) (what : String) : MetaM Expr := do
  let ty ← mkEq lhs rhs
  unless ← isDefEq lhs rhs do
    throwError "{what}: the rewritten term is not definitionally the term it came from.\n\
      before:{indentExpr lhs}\nafter:{indentExpr rhs}"
  mkExpectedTypeHint (← mkEqRefl lhs) ty

/-- The lemma set that discharges a combinator/flattening pass. The
source's `monadify_conv_aux` uses `@{thms monadify_simps SP_def}` under
`HOL_basic_ss`; a Lean `simp only` set additionally needs the tag
definitions those are stated over (`$ᵃ`, `λ₂`, `PROTECT2`) to reach the
monad law underneath, and the monad law itself at the general carrier. -/
def convLemmas : Array Name :=
  #[``APP_def, ``APP'_def, ``ABS2_apply, ``PROTECT2_def, ``SP_def,
    ``EVAL_def, ``PASS_def, ``COPY_def, ``PR_CONST_def,
    ``NRest.returnT_bindT, ``bindT_returnT_gen]

/-! ### `SP`-blocked rewriting (the source's `SP_cong` / `PR_CONST_cong`) -/

/-- Rewrite a term with one rule database, **never descending into an
`SP` or a `PR_CONST`** — which is the entire content of the source's

```isabelle
lemma SP_cong[cong]: "SP x ≡ SP x"
lemma PR_CONST_cong[cong]: "PR_CONST x ≡ PR_CONST x"
```

and what makes the arity and combinator phases terminate: every
equation's right-hand side wraps its own head in `SP`, so the rule
cannot re-fire on its own output.

Implemented as an explicit walk rather than as `simp` under `@[congr]`
because a Lean congruence theorem of that shape **does not block simp**
(delta P4/D-bo): the probe in the gate below pins the behaviour, and with
`simp` the arity phase diverges immediately (`maximum recursion depth` on
gate case (a)). -/
partial def rewriteDB (db : Name) (e : Expr) : MetaM Expr := do
  if e.isAppOf ``SP || e.isAppOf ``PR_CONST then
    return e
  let mut cur := e
  for _ in [0:8] do
    match ← patStep db cur with
    | some c => cur := c
    | none => break
  if cur.isAppOf ``SP || cur.isAppOf ``PR_CONST then
    return cur
  match cur with
  | .lam n d b bi =>
    withLocalDecl n bi d fun v => do
      mkLambdaFVars #[v] (← rewriteDB db (b.instantiate1 v))
  | .app .. => return mkAppN cur.getAppFn (← cur.getAppArgs.mapM (rewriteDB db))
  | _ => return cur

/-! ### `arity_tac` -/

/-- The source's

```ml
fun arity_tac ctxt = simp_tac arity1_ss THEN' simp_tac arity2_ss
```

with `arity1_ss = HOL_basic_ss addsimps sepref_monadify_arity` under
`SP_cong`/`PR_CONST_cong` (here: `rewriteDB`), and
`arity2_ss = HOL_basic_ss addsimps @{thms beta SP_def}` (here: `simp`,
which is what the source uses and where no blocking is wanted — arity2's
whole job is to *remove* the protection arity1 added).

Every arity equation is an identity up to eta, so the pass is justified
by `rfl`. -/
def arityStep (e : Expr) : MetaM StepResult := do
  let e₁ ← rewriteDB `sepref_monadify_arity e
  let (r, _) ← Meta.simp e₁ (← simpOnlyContext #[``beta, ``SP_def])
  let e₂ := r.expr
  if e₂ == e then return (e, none)
  return (e₂, some (← proveEqByRfl e e₂ "arity"))

/-! ### The `EVAL`-flattening pass (the source's `monadify` + simproc) -/

/-- `NRest.bindT` at the given argument, result and cost types, as a
*partially applied head* so that the tagged spine `bindT $ᵃ m $ᵃ f` can
be built over it. -/
def mkBindTFn (τ β γ : Expr) : MetaM Expr := do
  let i₁ ← synthInstance (← mkAppM ``CompleteLattice #[γ])
  let i₂ ← synthInstance (← mkAppM ``Add #[γ])
  return mkAppN (mkConst ``NRest.bindT) #[τ, β, γ, i₁, i₂]

/-- The source's `monadify` ML function:

```ml
fun monadify t = let
    val (f,args) = Autoref_Tagging.strip_app t
    val _ = not (is_Abs f) orelse raise TERM ("monadify: higher-order",[t])
    val args = map (fn a => @{mk_term "(EVAL$?a):: (?'a, ecost) nrest"}) args
    val argVs = tag_list 0 argTs |> map cr_var
    val res0 = @{mk_term "SP ((RETURNT$?x):: (?'a, ecost) nrest)"}   (* x = f$v1$…$vn *)
    val res = bind_args res0 (argVs ~~ args)
  in res end
```

i.e.: strip the tagged application, `EVAL` each argument, bind them
left to right under `λ₂`-protected binders named `v1 … vn`, and put
`SP (RETURNT (f v1 … vn))` at the bottom. `evalFn` is the `EVAL` head of
the node being rewritten, from which the cost carrier and its `Zero`
instance are read (delta P4/D-bp). -/
partial def monadifyOne (evalFn t : Expr) : MetaM Expr := do
  let evalArgs := evalFn.getAppArgs
  unless evalArgs.size == 3 do
    throwError "monadify: malformed `EVAL` head{indentExpr evalFn}"
  let γ := evalArgs[1]!
  let instZero := evalArgs[2]!
  let (f, args) := Autoref.peelAPP t
  if f.isLambda || f.isAppOf ``ABS2 then
    throwError "monadify: higher-order{indentExpr t}"
  let β ← inferType t
  let rec go (i : Nat) (vs : Array Expr) : MetaM Expr := do
    if h : i < args.size then
      let a := args[i]
      let τ ← inferType a
      withLocalDeclD (Name.mkSimple s!"v{i + 1}") τ fun v => do
        let inner ← go (i + 1) (vs.push v)
        let lam ← mkABS2 v inner
        let evHead := mkAppN (mkConst ``EVAL) #[τ, γ, instZero]
        let m ← mkAppM ``APP #[evHead, a]
        let bfn ← mkBindTFn τ β γ
        mkAppM ``APP #[← mkAppM ``APP #[bfn, m], lam]
    else
      let mut app := f
      for v in vs do
        app ← mkAppM ``APP #[app, v]
      let retHead := mkAppN (mkConst ``NRest.returnT) #[β, γ, instZero]
      mkAppM ``SP #[← mkAppM ``APP #[retHead, app]]
  go 0 #[]

/-- One pass of the source's `monadify_simproc` over the whole term.
Two source behaviours are reproduced exactly:

* the simproc lives in `comb1_ss`, so `SP_cong`/`PR_CONST_cong` keep it
  out of protected subterms;
* `proc = K (try o monadify_conv_aux)` — the `try` is load-bearing. A
  node `monadifyOne` refuses (`monadify: higher-order`) is **left
  alone**, and that is how such an `EVAL` reaches `check_EVAL`, which is
  the phase that reports it (delta P4/D-bl). -/
partial def flattenTerm (e : Expr) : MetaM Expr := do
  if e.isAppOf ``SP || e.isAppOf ``PR_CONST then
    return e
  if let some (fn, t) := Autoref.isAPP? e then
    if fn.isAppOf ``EVAL then
      match ← (try pure (some (← monadifyOne fn t)) catch _ => pure none) with
      | some r => return r
      | none => pure ()
  match e with
  | .lam n d b bi =>
    withLocalDecl n bi d fun v => do
      mkLambdaFVars #[v] (← flattenTerm (b.instantiate1 v))
  | .app .. => return mkAppN e.getAppFn (← e.getAppArgs.mapM flattenTerm)
  | _ => return e

/-! ### `comb_tac` -/

/-- The source's

```ml
fun comb_tac ctxt = simp_tac comb1_ss THEN' simp_tac comb2_ss
```

with `comb1_ss = HOL_basic_ss addsimps sepref_monadify_comb
addsimprocs [monadify_simproc]` under `SP_cong`/`PR_CONST_cong`, and
`comb2_ss = HOL_basic_ss addsimps @{thms SP_def}`. Isabelle interleaves
the database and the simproc inside one traversal; here they alternate to
a fixed point, which reaches the same normal form because `SP`-protection
persists across both (a flattened node is emitted under `SP`, so neither
the database nor a later pass re-enters it) and `SP_def` runs only at the
end.

Unlike arity, this pass is *not* definitional — `comb_returnT` and its
kin are instances of the monad's left identity — so it is justified by
the source's own conversion simp set (`convLemmas`). -/
def combStep (e : Expr) : MetaM StepResult := do
  let mut cur := e
  for _ in [0:64] do
    let a ← rewriteDB `sepref_monadify_comb cur
    let b ← flattenTerm a
    if b == cur then break
    cur := b
  -- `comb2_ss`
  let (r, _) ← Meta.simp cur (← simpOnlyContext #[``SP_def])
  let final := r.expr
  if final == e then return (e, none)
  return (final, some (← proveEqBySimp e final convLemmas "comb"))

/-! ### `check_EVAL` -/

/-- The source's

```ml
fun contains_eval @{mpat "Trueprop (hn_refine _ _ _ _ ?a)"} =
  Term.exists_subterm (fn @{mpat EVAL} => true | _ => false) a
```

run as the `("check_EVAL", K (CONCL_COND' (not o contains_eval)), 0)`
phase. The source's `CONCL_COND'` fails with no message at all; the
supervision-legibility requirement (design record §3, P4 row 7) asks for
the offending subterm, so this one names it and says what to do. -/
def checkEVAL (e : Expr) : MetaM StepResult := do
  -- Report the *tagged application* `EVAL $ᵃ t`, not the bare `EVAL`
  -- head: the head's arguments are implicit, so it prints as `EVAL` and
  -- says nothing about what could not be flattened.
  let tagged := e.find? fun s =>
    match Autoref.isAPP? s with
    | some (fn, _) => fn.isAppOf ``EVAL
    | none => false
  match tagged <|> e.find? (·.isAppOf ``EVAL) with
  | some sub =>
    throwError "an `EVAL` tag survived the combinator phase:{indentExpr sub}\n\
      no `sepref_monadify_comb` equation applies to it.\n\
      Either the operation needs a combinator equation, or the tagged\n\
      application's head is an abstraction (the source's\n\
      `monadify: higher-order`), which this phase cannot flatten."
  | none => return (e, none)

/-! ### `mark_params` -/

/-- The source's `mark_params`:

```ml
fun tr env (t as @{mpat "RETURN$?x"}) =
      if is_Bound x orelse member (op aconv) pps x then @{mk_term env: "PASS$?x"} else t
  | tr env (t1$t2) = tr env t1 $ tr env t2
  | tr env (Abs (x,T,t)) = Abs (x,T,tr (T::env) t)
  | tr _ t = t
```

`pps` is the caller's parameter list (delta P4/D-bk); `locals` are the
binders this walk has opened, which is the source's `is_Bound`. The
`PASS` head is built from `returnT`'s own arguments, so the swap cannot
pick a different carrier or a different `Zero` instance. -/
partial def markParamsTerm (pps locals : Array Expr) (e : Expr) : MetaM Expr := do
  if let some (f, x) := Autoref.isAPP? e then
    if f.isAppOf ``NRest.returnT then
      if locals.contains x || pps.contains x then
        let args := f.getAppArgs
        if args.size == 3 then
          return ← mkAppM ``APP #[mkAppN (mkConst ``PASS) args, x]
  match e with
  | .lam n d b bi =>
    withLocalDecl n bi d fun v => do
      mkLambdaFVars #[v] (← markParamsTerm pps (locals.push v) (b.instantiate1 v))
  | .app .. => return mkAppN e.getAppFn (← e.getAppArgs.mapM (markParamsTerm pps locals))
  | _ => return e

/-- `mark_params` with its justification, which is the source's own:
`simp_tac (HOL_basic_ss addsimps @{thms PASS_def})`, i.e. `PASS` *is*
`returnT`, so the rewrite is definitional. -/
def markParamsStep (pps : Array Expr) (e : Expr) : MetaM StepResult := do
  let e' ← markParamsTerm pps #[] e
  if e' == e then return (e, none)
  return (e', some (← proveEqByRfl e e' "mark_params"))

/-! ### `dup` — the duplicate-argument splitter -/

/-- The source's `dp`:

```ml
fun dp ctxt (@{mpat "NREST.bindT$(PASS$?p)$(?t' AS⇩p (λ_. PROTECT2 _ DUMMY))"}) =
      let val (t',ps) = … dp ctxt (body of t') …
          val dup = member (op aconv) ps p
          val t = if dup then @{mk_term "NREST.bindT$(RETURN$(COPY$?p))$?t'"}
                  else @{mk_term "NREST.bindT$(PASS$?p)$?t'"}
      in (t,p::ps) end
  | dp ctxt (t1$t2) = (#1 (dp ctxt t1) $ #1 (dp ctxt t2),[])
  | dp ctxt (t as (Abs _)) = (apply_under_lambda (#1 oo dp) ctxt t,[])
  | dp _ t = (t,[])
```

The recursion descends the `bindT (PASS p) (λ₂x. …)` *spine* collecting
the parameters passed further in, and turns the **outer** occurrence into
`returnT (COPY p)` when `p` recurs deeper. That direction is the right
one and is easy to get backwards: `PASS` invalidates its argument, so the
*last* use may take ownership and every earlier use must copy.

Parameters collected under a binder that mention that binder cannot be
compared against anything outside it, and are dropped as the source's
`dest_lambda_rc` scoping does. -/
partial def dupTerm (e : Expr) : MetaM (Expr × Array Expr) := do
  if let some (g, t') := Autoref.isAPP? e then
    if let some (bfn, m) := Autoref.isAPP? g then
      if bfn.isAppOf ``NRest.bindT then
        if let some (pfn, p) := Autoref.isAPP? m then
          if pfn.isAppOf ``PASS then
            if let some (n, d, body, bi) ← asABS2? t' then
              let (t'', ps) ← withLocalDecl n bi d fun v => do
                let (b', ps) ← dupTerm (body.instantiate1 v)
                let lam ← mkABS2 v b'
                let fid := v.fvarId!
                return (lam, ps.filter fun q => !q.hasAnyFVar (· == fid))
              let m' ←
                if ps.contains p then
                  let retHead := mkAppN (mkConst ``NRest.returnT) pfn.getAppArgs
                  let τ ← inferType p
                  let copyHead := mkApp (mkConst ``COPY [← getLevel τ]) τ
                  mkAppM ``APP #[retHead, ← mkAppM ``APP #[copyHead, p]]
                else pure m
              let e' ← mkAppM ``APP #[← mkAppM ``APP #[bfn, m'], t'']
              return (e', ps.push p)
  match e with
  | .lam n d b bi =>
    let r ← withLocalDecl n bi d fun v => do
      mkLambdaFVars #[v] (Prod.fst (← dupTerm (b.instantiate1 v)))
    return (r, #[])
  | .app .. =>
    let args ← e.getAppArgs.mapM fun a => Prod.fst <$> dupTerm a
    return (mkAppN e.getAppFn args, #[])
  | _ => return (e, #[])

/-- `dup` with its justification, which is the source's own:
`ALLGOALS (simp_tac (HOL_basic_ss addsimps @{thms RET_COPY_PASS_eq}))`,
and `RET_COPY_PASS_eq` is `rfl` here. -/
def dupStep (e : Expr) : MetaM StepResult := do
  let (e', _) ← dupTerm e
  if e' == e then return (e, none)
  return (e', some (← proveEqByRfl e e' "dup"))

/-! ### `remove_pass` -/

/-- The source's
`fun remove_pass_tac ctxt = simp_tac (HOL_basic_ss addsimps @{thms remove_pass_simps})`. -/
def removePassStep (e : Expr) : MetaM StepResult := do
  let (r, _) ← Meta.simp e
    (← simpOnlyContext #[``remove_pass_simps_left, ``remove_pass_simps_right])
  return (r.expr, r.proof?)

/-! ### The driver -/

/-- **The monadify phase, term-level** (delta P4/D-bk).

The source's

```ml
fun monadify_tac dbg ctxt = PHASES' [
    ("arity", arity_tac, 0), ("comb", comb_tac, 0),
    ("check_EVAL", K (CONCL_COND' (not o contains_eval)), 0),
    ("mark_params", mark_params_tac, 0), ("dup", dup_tac, 0),
    ("remove_pass", remove_pass_tac, 0)
  ] (flag_phases_ctrl ctxt dbg) ctxt
```

**Calling convention for wave C.** `a` must be the abstract program
*after* the `id_op` phase, i.e. tagged: applications are `$ᵃ`,
abstractions are `λ₂` (either shape — see `asABS2?`), atomic constants
are `PR_CONST`. `pps` is the parameter list the source's `mark_params`
reads out of the precondition
(`strip_star P |> map_filter (dest_hn_ctxt_opt #> map_option #2)`),
compared by syntactic equality as the source's `aconv` is. The result is
`(a', h)` with **`h : a = a'`**. Failures arrive as errors carrying
`sepref: phase '<name>' (priority <n>) failed.` followed by the
sub-phase's own message and the offending subterm. -/
def monadifyCore (pps : Array Expr) (a : Expr) : MetaM (Expr × Expr) := do
  let mut c : Chain := { cur := a }
  c ← c.push (← runStep "arity" 20 arityStep c.cur)
  c ← c.push (← runStep "comb" 30 combStep c.cur)
  c ← c.push (← runStep "check_EVAL" 40 checkEVAL c.cur)
  c ← c.push (← runStep "mark_params" 50 (markParamsStep pps) c.cur)
  c ← c.push (← runStep "dup" 60 dupStep c.cur)
  c ← c.push (← runStep "remove_pass" 70 removePassStep c.cur)
  match c.pf? with
  | some p => return (c.cur, p)
  | none => return (c.cur, ← mkEqRefl a)

end Monadify

/-! ## Entry points

`monadifyCore`'s consumer is wave C's `hnRefine`-goal driver. Until it
exists, two exercisers: a command that prints the monadified program,
and a tactic that closes a goal `a = a'`. -/

/-- Print the monadified form of a tagged abstract program. -/
elab "#monadify " t:term : command =>
  Command.liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let (r, _) ← Monadify.monadifyCore #[] (← instantiateMVars e)
    logInfo m!"{r}"

/-- Print the monadified form of a tagged abstract program, with an
explicit parameter list — the source's `pps`, which its `mark_params`
reads out of the `hn_refine` precondition. -/
elab "#monadify_with " "[" ps:term,* "]" t:term : command =>
  Command.liftTermElabM do
    let pps ← ps.getElems.mapM fun p => do
      let e ← Term.elabTerm p none
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let (r, _) ← Monadify.monadifyCore pps (← instantiateMVars e)
    logInfo m!"{r}"

/-- Close a goal `a = ?a'` (or `a = a'` for a hand-written `a'`) by
running the monadify pipeline on `a`. -/
elab "monadify" : tactic => do
  Tactic.liftMetaTactic fun g => do
    let ty ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := ty.eq?
      | throwError "monadify: the goal is not an equation:{indentExpr ty}"
    let (r, pf) ← Monadify.monadifyCore #[] lhs
    unless ← isDefEq rhs r do
      throwError "sepref: the monadified program{indentExpr r}\n\
        is not the goal's right-hand side{indentExpr rhs}"
    g.assign pf
    return []

/-! ## The executable gate (design record ledger D4)

Five pins, written from the source's equations by hand before the
pipeline existed. The programs are tagged by hand rather than run
through `sepref_id_op` first, so that each gate case shows exactly the
input the source's `monadify_tac` would see and nothing else.

The hand-derivations are recorded next to each case, because the value
of the pin is that the *derivation* is checkable, not just the string. -/

namespace MonadifyGate

/-- The gate's cost carrier: `ECost`, as the abstract programs use. -/
abbrev C := ECost

/-- A binary pure operation. -/
def gadd (x y : Nat) : Nat := x + y
/-- An operand. -/
def gx : Nat := 1
/-- A second operand. -/
def gy : Nat := 2
/-- A third operand. -/
def gz : Nat := 3
/-- A parameter, i.e. a term the caller reports in `pps`. -/
def gp : Nat := 4
/-- A boolean condition. -/
def gb : Bool := true
/-- An opaque monadic operation, standing for a `sepref_register`ed one. -/
noncomputable def gm : NRest Nat C := NRest.returnT gx
/-- An opaque monadic continuation. -/
noncomputable def gk (n : Nat) : NRest Nat C := NRest.returnT n

/-! ### (0) The `SP` barrier, probed

Delta P4/D-bo's refutation, pinned so that it cannot silently reverse. If
Lean's `@[congr]` honoured `SP_cong`, `simp` would be unable to see
inside `SP` and the first line would fail; it does not, which is why
`Monadify.rewriteDB` exists. The second line records what `SP` *is* once
a phase is allowed to strip it. -/

example : SP ((2 : Nat) + 2) = SP 4 := by simp

example (x : Nat) : SP x = x := by simp only [SP_def]

/-! ### (a) A compound pure expression, flattened to ANF

Input: `returnT $ᵃ (gadd $ᵃ (gadd $ᵃ gx $ᵃ gy) $ᵃ gz)`.

Hand-derivation.

* **arity**: `arity_returnT` expands the head, `beta` and `SP_def`
  contract it again — `returnT $ᵃ E` is already at full arity, so this
  phase is a no-op, which is what "arity *alignment*" means.
* **comb**: `comb_returnT` fires on `returnT $ᵃ E`, giving
  `bindT $ᵃ (EVAL $ᵃ E) $ᵃ (λ₂ y => SP (returnT $ᵃ y))`. Flattening
  `EVAL $ᵃ E` with `E = gadd $ᵃ A $ᵃ gz`, `A = gadd $ᵃ gx $ᵃ gy`, per
  `mcomb2`: `bindT $ᵃ (EVAL $ᵃ A) $ᵃ (λ₂ v1 => bindT $ᵃ (EVAL $ᵃ gz) $ᵃ
  (λ₂ v2 => SP (returnT $ᵃ (gadd $ᵃ v1 $ᵃ v2))))`, then the same for
  `EVAL $ᵃ A`, and `EVAL $ᵃ c` for a leaf `c` bottoms out at
  `SP (returnT $ᵃ c)` (the source's `bind_args res0 []`). `SP_def` then
  erases every `SP`. Argument order is left to right: `gx`, `gy`, their
  sum, `gz`.
* **check_EVAL**: clean.
* **mark_params** (`pps = []`): the only `returnT $ᵃ x` with `x` a bound
  variable is the outermost continuation's, which becomes `PASS $ᵃ v`.
* **dup**: no `bindT $ᵃ (PASS $ᵃ p) $ᵃ …` spine, so nothing.
* **remove_pass**: `remove_pass_simps_right` collapses
  `bindT $ᵃ M $ᵃ (λ₂ x => PASS $ᵃ x)` to `M`.

Expected: two nested binds for the inner sum, bound first, then `gz`. -/
/--
info: NRest.bindT $ᵃ
    (NRest.bindT $ᵃ (NRest.returnT $ᵃ gx) $ᵃ
      ABS2 fun v1 => NRest.bindT $ᵃ (NRest.returnT $ᵃ gy) $ᵃ ABS2 fun v2 => NRest.returnT $ᵃ (gadd $ᵃ v1 $ᵃ v2)) $ᵃ
  ABS2 fun v1 => NRest.bindT $ᵃ (NRest.returnT $ᵃ gz) $ᵃ ABS2 fun v2 => NRest.returnT $ᵃ (gadd $ᵃ v1 $ᵃ v2)
-/
#guard_msgs in
#monadify (NRest.returnT $ᵃ (gadd $ᵃ (gadd $ᵃ gx $ᵃ gy) $ᵃ gz) : NRest Nat C)

/-! ### (a2) A combinator: only the *condition* is evaluated

Input: `MIf $ᵃ gb $ᵃ gm $ᵃ gm`.

Hand-derivation. `comb_MIf` fires, lifting only the condition into the
monad — the branches are already monadic and must *not* be evaluated
eagerly, which is the whole reason the source states a combinator
equation rather than letting the `mcomb` schema apply. Flattening
`EVAL $ᵃ gb` for the leaf `gb` gives `SP (returnT $ᵃ gb)`, and `SP_def`
erases the protection. Note also what does *not* happen: the rewritten
head is `SP MIf`, not `MIf`, so `comb_MIf` cannot re-fire on its own
output — this pin is the termination argument of delta P4/D-bo observed
at work. -/
-- The binder is named `c`, from `comb_MIf`'s own statement: this rewrite
-- came from the database, not from the flattener, whose binders are
-- `v1 … vn` (the source's `cr_var`).
/-- info: NRest.bindT $ᵃ (NRest.returnT $ᵃ gb) $ᵃ ABS2 fun c => NRest.MIf $ᵃ c $ᵃ gm $ᵃ gm -/
#guard_msgs in
#monadify (NRest.MIf $ᵃ gb $ᵃ gm $ᵃ gm : NRest Nat C)

/-! ### (b) A duplicate argument, split with `COPY`

Input: `returnT $ᵃ (gadd $ᵃ gp $ᵃ gp)`, with `pps = [gp]`.

Hand-derivation. `comb` + flattening give, as in (a),
`bindT $ᵃ (bindT $ᵃ (returnT $ᵃ gp) $ᵃ (λ₂ v1 =>
  bindT $ᵃ (returnT $ᵃ gp) $ᵃ (λ₂ v2 => returnT $ᵃ (gadd $ᵃ v1 $ᵃ v2))))
  $ᵃ (λ₂ v => returnT $ᵃ v)`.
`mark_params` marks both `returnT $ᵃ gp` (because `gp ∈ pps`) and the
outer `returnT $ᵃ v` (because `v` is bound). Now `dup` sees the spine
`bindT $ᵃ (PASS $ᵃ gp) $ᵃ (λ₂ v1 => bindT $ᵃ (PASS $ᵃ gp) $ᵃ …)`: the
inner occurrence collects `gp`, so the **outer** one becomes
`returnT $ᵃ (COPY $ᵃ gp)`. `remove_pass` then eliminates the inner
`PASS` bind by substitution (`remove_pass_simps_left`) and the outermost
one by `remove_pass_simps_right`.

Expected: exactly one `COPY`, on the first of the two uses, and the
second use reading `gp` directly. -/
/-- info: NRest.bindT $ᵃ (NRest.returnT $ᵃ (COPY $ᵃ gp)) $ᵃ ABS2 fun v1 => NRest.returnT $ᵃ (gadd $ᵃ v1 $ᵃ gp) -/
#guard_msgs in
#monadify_with [gp] (NRest.returnT $ᵃ (gadd $ᵃ gp $ᵃ gp) : NRest Nat C)

/-! ### (c) A program already in complete monadic form

Input: `bindT $ᵃ gm $ᵃ (λ₂ s => gk $ᵃ s)`, whose operations are opaque
monadic constants — which is what an abstract program looks like once
its operations are registered. No arity equation applies, no combinator
equation applies, there is no `EVAL` to flatten, no `returnT $ᵃ x` to
mark and no `PASS` to remove. Expected: unchanged, character for
character. -/
/-- info: NRest.bindT $ᵃ gm $ᵃ ABS2 fun s => gk $ᵃ s -/
#guard_msgs in
#monadify (NRest.bindT $ᵃ gm $ᵃ (λ₂ s => gk $ᵃ s) : NRest Nat C)

/-! ### (d) `check_EVAL` reports a survivor

Input: an `EVAL` whose tagged application has an *abstraction* at the
head. The source's `monadify` raises `TERM ("monadify: higher-order")`,
its simproc's `try` swallows the raise, and the tag survives to
`check_EVAL` (delta P4/D-bl). Expected: the `check_EVAL` phase's message,
at its own priority, naming the surviving subterm. -/
/--
error: sepref: phase 'check_EVAL' (priority 40) failed.
an `EVAL` tag survived the combinator phase:
  EVAL $ᵃ ABS2 fun y => gadd $ᵃ y $ᵃ gz
no `sepref_monadify_comb` equation applies to it.
Either the operation needs a combinator equation, or the tagged
application's head is an abstraction (the source's
`monadify: higher-order`), which this phase cannot flatten.
-/
#guard_msgs in
#monadify (EVAL $ᵃ (λ₂ y => gadd $ᵃ y $ᵃ gz) : NRest (Nat → Nat) C)

/-! ### (e) The equations, exercised

Each tagged equation is applied at a concrete instance, so that a
statement which type-checks but cannot fire would be caught. -/

example : (NRest.returnT : Nat → NRest Nat C) = λ₂ x => SP NRest.returnT $ᵃ x :=
  arity_returnT

example (x : Nat) :
    (NRest.returnT $ᵃ x : NRest Nat C)
      = NRest.bindT $ᵃ (EVAL $ᵃ x) $ᵃ (λ₂ y => SP (NRest.returnT $ᵃ y)) :=
  comb_returnT x

example (b : Bool) (t e : NRest Nat C) :
    (NRest.MIf $ᵃ b $ᵃ t $ᵃ e)
      = NRest.bindT $ᵃ (EVAL $ᵃ b) $ᵃ (λ₂ c => SP NRest.MIf $ᵃ c $ᵃ t $ᵃ e) :=
  comb_MIf b t e

example (b : Nat → Bool) (c : Nat → NRest Nat C) (s : Nat) :
    (NRest.whileT $ᵃ b $ᵃ c $ᵃ s)
      = NRest.bindT $ᵃ (EVAL $ᵃ s) $ᵃ (λ₂ t => SP NRest.whileT $ᵃ b $ᵃ c $ᵃ t) :=
  comb_whileT b c s

example (I : Nat → Prop) (E : Nat → Nat) (b : Nat → Bool) (c : Nat → NRest Nat C) (s : Nat) :
    (NRest.whileIET $ᵃ I $ᵃ E $ᵃ b $ᵃ c $ᵃ s)
      = NRest.bindT $ᵃ (EVAL $ᵃ s) $ᵃ
          (λ₂ t => SP NRest.whileIET $ᵃ I $ᵃ E $ᵃ b $ᵃ c $ᵃ t) :=
  comb_whileIET I E b c s

example (m : NRest Nat C) : (NRest.bindT $ᵃ m $ᵃ (λ₂ x => PASS $ᵃ x)) = m :=
  remove_pass_simps_right m

example (p : Nat) : (NRest.returnT $ᵃ (COPY $ᵃ p) : NRest Nat C) = PASS $ᵃ p :=
  RET_COPY_PASS_eq p

-- The tactic form, on the program of case (c).
example :
    (NRest.bindT $ᵃ gm $ᵃ (λ₂ s => gk $ᵃ s) : NRest Nat C)
      = NRest.bindT $ᵃ gm $ᵃ (λ₂ s => gk $ᵃ s) := by
  monadify

end MonadifyGate

end Lax13Proofs.Refine.Sepref
