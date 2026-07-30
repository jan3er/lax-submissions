import Lax13Proofs.Refine.Autoref.Phases

/-!
# Sepref phase one: operation identification

Port of `thys/sepref/Sepref_Id_Op.thy` of `isabelle_llvm_time`
(Lammich) at the pin recorded in `plans/word-ram/refinement-tower/design.md`
§1 — rev `42dd7f5`. The verbatim source text this file is checked
against is `plans/word-ram/refinement-tower/p4-sepref-extracts.md` §5;
the whole `.thy` was read at the pin, and every declaration below quotes
it in its doc-comment. Design record §3, P4 row 4:

> phase 1 operator identification (`Sepref_Id_Op.thy`) → `Sepref/IdOp.lean`,
> `@[sepref_id_rules]` | interface-tagging via `mop`-style monadic ops
> kept; Lean macro/elab pass

The source's own header says what this file is:

> The operation identification phase is adapted from the Autoref tool.
> The basic idea is to have a type system, which works on so called
> interface types (also called conceptual types). Each conceptual type
> denotes an abstract data type, e.g., set, map, priority queue.
>
> Each abstract operation, which must be a constant applied to its
> arguments, is assigned a conceptual type. Additionally, there is a set
> of *pattern rewrite rules*, which are applied to subterms before type
> inference takes place, and which may be backtracked over. This way,
> encodings of abstract operations in Isabelle/HOL, like `λ_. None` for
> the empty map, or `fun_upd m k (Some v)` for map update, can be
> rewritten to abstract operations, and get properly typed.

"Adapted from the Autoref tool" is load-bearing for the *import graph*:
`Sepref_Id_Op.thy` imports `Automatic_Refinement.Autoref_Tagging` and
**not** `Autoref_Id_Ops.thy`. It reuses `PROTECT`/`ANNOT`/`OP`/`APP`/
`ABS` (P2's `Autoref/Tagging.lean`, imported here through
`Autoref/Phases.lean`) and layers `PROTECT2`/`ABS2`/`APP'`/`PR_CONST`/
`UNPROTECT`/`intf_type`/`CTYPE_ANNOT`/`ID` on top — with its own
interface notion. This port keeps that graph exactly (delta P4/D-ba).

## Scope of this file

Everything `Sepref_Id_Op.thy` contains: the protection constants, the
`ID` judgment and its nine-rule calculus, the three rule databases
(`id_rules`, `pat_rules`, `def_pat_rules`, registered in
`Autoref/Attrs.lean`), the source's `Id_Op_Tactical` search discipline
(`SOLVE_FWD` / `DF_SOLVE_FWD`), the `Id_Op.protect` term walk and the
`id_tac` driver, and its default setup (the numeral pattern and the
`nat`/`int` constant typings).

Nothing here mentions `hnRefine`: `Sepref_Id_Op.thy` does not either
(it imports only `Main`, `Refine_Lib`, `Autoref_Tagging` and
`Named_Theorems_Rev`), and the `hn_refine`-goal integration point is
`Sepref/Tool.lean`'s, i.e. another wave's.

## Judgment calls (P4/D-ba onward; wave A owns the earlier letters)

**P4/D-ba — the import graph is the source's, so `opSplit` is repeated
rather than imported.** `Autoref/IdOps.lean` has an `opSplit` (its delta
I3: a Lean application splits at its last non-explicit argument, because
implicit/instance arguments are part of the *operator*, not arguments to
translate). This file needs the same split for `protect`, and does not
import that module — for the reason the source does not import
`Autoref_Id_Ops.thy`: doing so would drag in Autoref's *own* interface
layer, whose `::ᵢ` (`CONST_INTF`) and `:::ᵢ` (`i_ANNOT`) notations
collide token-for-token with this theory's `::ᵢ` (`intf_type`) and
`:::ᵢ` (`CTYPE_ANNOT`) — the source avoids the collision by not
importing, and so do we. The price is fourteen lines of `opSplit`
duplicated with a citation. Fallback if a later wave needs both: hoist
`opSplit` into `Autoref/Phases.lean`, which both files import.

**P4/D-bb — Isabelle's `prop`-typed dummy becomes `Prop`, and `DUMMY`
becomes `True`.** The source has
`definition [simp]: "PROTECT2 x (y::prop) ≡ x"` with
`consts DUMMY :: "prop"`: the second argument lives in Isabelle's
*meta*-logic and exists only so that the tag is not eta-contractible.
Rendered here as `(_y : Prop)` with `DUMMY : Prop := True`. `Prop` is
chosen over `Unit` because it is the closer reading of `prop` and
because the tag then sits in the same universe-polymorphic family as
P2's `PROTECT`/`OP`/`APP` (`Autoref/Tagging.lean` delta T4). `DUMMY` is
a `def`, not an axiom, for the reason `Autoref/Tagging.lean`'s delta T2
gives: the archive's claims are kernel-clean and stay that way. Nothing
reads `DUMMY`'s value; the binder-notation gate below pins that
`λ₂`-protected abstractions elaborate and erase as intended.

**P4/D-bc — `λ₂` *is* ported as a binder, unlike Autoref's `λ''`.**
`Autoref/Tagging.lean` delta T3 declined the source's `binder "λ''"` for
`ABS`, judging a `λ`-initial token's blast radius out of proportion to a
display convenience. Here the judgment goes the other way, because the
artifact is different: every arity and combinator equation of
`Sepref/Monadify.lean` is *stated* with `λ₂`-protected binders, and
without the binder those statements are unreadable walls of `ABS2 fun`.
The token is `λ₂ `, longest-match ahead of `λ`; nothing in the archive
writes `λ` immediately followed by `₂`, and the token only exists in
modules importing this one (currently `Sepref/Monadify.lean`).

**P4/D-bd — `PROTECT2`'s `(#_#)` mixfix is not ported.** The source's
`abbreviation PROTECT2_syn ("'(#_#')")` would need the token `(#`, and
Lean 4's array literal is `#[…]`: the token `(#` would make every
`(#[a, b])` in the archive parse as an open `PROTECT2` bracket. The
`abbreviation` itself is ported (`PROTECT2_syn`); the mixfix is not,
which is Tagging's delta-T3 reasoning applied to a case where the
tokenizer conflict is not hypothetical but certain.

**P4/D-be — the two colliding notations are `scoped`.** `::ᵢ` and
`:::ᵢ` are the source's spellings for `intf_type` and `CTYPE_ANNOT`, and
they are also — in *Autoref*'s theories, which the source never imports
alongside these — the spellings of `CONST_INTF` and `i_ANNOT`. Ours are
declared `scoped` to `Lax13Proofs.Refine.Sepref`, so a wave-C module
that legitimately needs both layers gets both notations in scope and
Lean's overload resolution separates them by the second argument's sort
(an `Interface` *value* for Autoref's, a `Sort` for Sepref's). Recorded
because it is a real ambiguity, resolved rather than removed.

**P4/D-bf — interfaces are Lean `Sort`s, so `ID`'s third argument is
usually recoverable.** The source's interface is `'b itself`, i.e. a HOL
*type*, written `TYPE('T)` at every use; this is Sepref's own choice and
it differs from Autoref's `typedecl interface` (P2's `Interface`
inductive), which is why Autoref's `Interface` is deliberately *not*
reused here. Rendered as a plain `(I : Sort v)` parameter — Lean has no
`itself`, and a `Sort` argument is exactly the information `TYPE('T)`
carries. A consequence worth stating plainly: because tagging is
type-preserving, `ID t t' T` holds with `T = typeof t` for every term
the walk builds, which is precisely the source's own `fallback_rule`
(`ID (c::'a) c TYPE('c)`) and `itype_self`. The `id_rules` database is
therefore what makes the phase do non-trivial work: an entry
`c ::ᵢ I` with `I ≠ typeof c` (the source's `(nat,nat) i_map`-style
conceptual types) overrides the fallback, and `idTerm` consults it
first.

**P4/D-bg — the identification walk is a `MetaM` pass justified by one
`rfl`, and the pattern databases run as one top-down simp pass.** This
is `Autoref/IdOps.lean`'s delta I2 and its `opPatRewrite`, applied to
the same problem for the same substrate reason: resolving `app_rule`
backwards would ask Lean's unifier to solve `?f $ᵃ ?x =?= f x`, the
flex-flex shape the tags exist to avoid, and `ID t t' T` *is* `t = t'`
with every tag a `def` the kernel unfolds. The source's `id_tac`
backtracks over `pat_rules` at every node; here `def_pat_rules` and
`pat_rules` run as two simp passes (definite first, as the source's
`def_rl_net` runs first), then the walk tags what is left. The rules are
ported in full anyway: they are the specification the walk is checked
against, rule by rule, and the correspondence is recorded at each one.

**P4/D-bh — `DF_SOLVE_FWD`'s stuck-state sequence becomes a stuck-state
*log*.** The source returns a lazy `Seq` of stuck goal states when the
`id_debug` flag is set, so that the user can step into them. A `MetaM`
walk has no goal states to hand back; `idOpCore` accumulates the
offending subterms in an `IO.Ref` (the source's own
`Unsynchronized.ref []`) and, under `Config.debug`, reports the whole
list in the failure envelope — depth-first order, deepest first, as the
source's `rev (!stuck_list_ref)` gives. The failure envelope itself is
`Autoref/Phases.lean`'s (its delta P6: every pipeline failure names its
phase and its unmet side condition), with `sepref` in place of
`autoref` and the source's own phase name.

**P4/D-bi — `mk_fallback`'s constant-constraint lookup is dropped.** The
source's `fallback_tac` fires only on `ID (Const (name, cT)) _ _` and
only when `name` has no `id_rules` typing, and it builds the fallback
instance from `Sign.the_const_constraint` — the constant's *declared*
(most general) type, so that the fallback interface is the generic one
rather than the occurrence's instance. Lean has no such two-level split
at the term level (`inferType` gives the occurrence's type, which is
what a later phase needs anyway), so the fallback uses `inferType`. The
`cfg_id_trace_fallback` flag is ported and reports each fallback, which
is what it is for.

**P4/D-bj — the pattern databases are single-step resolution, and the
`ID` fact is one `rfl`.** Two findings, both from refuting the
alternative first (house rule: refute before prove). (i) Reading
`def_pat_rules`/`pat_rules` as *simp sets* — the shape
`Autoref/IdOps.lean`'s `opPatRewrite` uses for `autoref_op_pat` —
diverges: the source's own `pat_numeral` is
`numeral$x ≡ UNPROTECT (numeral$x)`, whose right-hand side contains its
left-hand side, and `simp` hits `maximum recursion depth` on `(4 : ℕ)`.
The source is not doing rewriting-to-fixpoint: it builds a rule *net*
and applies **one** rule per node (`resolve_from_net_tac`), letting the
new head choose the next step — `UNPROTECT`, then `PR_CONST`, then stop.
`patStep` is that. (ii) With patterns applied node-wise, the whole
`ID t t' T` fact is still `rfl`, because every pattern rule in scope is
a definitional identity in Lean, as the source's are in HOL. An
`isDefEq` guard checks it explicitly and says what to do if it ever
fails, so the assumption cannot rot silently.

## Deliberately absent

* `Named_Theorems_Rev`'s *order* guarantee is documented rather than
  reproduced bit for bit: see `Autoref/Attrs.lean`'s P4 section.
* No `hnRefine`, no `hn_ctxt`, no `sepref_register` — none is in
  `Sepref_Id_Op.thy`, and `sepref_register`'s `map_type_eq` tagging
  (deep extract §6) belongs with the combinator setup, i.e. wave C.
-/

open Lean Meta Elab

universe u v w

namespace Lax13Proofs.Refine.Sepref

/-! ## Proper protection of terms

The source's own framing:

> The following constants are meant to encode abstraction and
> application as proper HOL-constants, and thus avoid strange effects
> with HOL's higher-order unification heuristics and automatic beta and
> eta-contraction.
>
> The first step of operation identification is to protect the term by
> replacing all function applications and abstractions by the constants
> defined below. -/

/-- Stand-in for the source's `consts DUMMY :: prop` (delta P4/D-bb): the
inert second argument of `PROTECT2`, whose only job is to keep the tag
from being eta-contracted away. A `def`, not an axiom. -/
def DUMMY : Prop := True

/-- The source's `definition [simp]: "PROTECT2 x (y::prop) ≡ x"`. -/
def PROTECT2 {α : Sort u} (x : α) (_y : Prop) : α := x

/-- The source's `PROTECT2` definition, with the source's own `[simp]`. -/
@[simp] theorem PROTECT2_def {α : Sort u} (x : α) (y : Prop) : PROTECT2 x y = x := rfl

/-- The source's `abbreviation PROTECT2_syn ("'(#_#')")`,
`PROTECT2_syn t ≡ PROTECT2 t DUMMY`. The mixfix `(#_#)` is not ported —
delta P4/D-bd. -/
abbrev PROTECT2_syn {α : Sort u} (t : α) : α := PROTECT2 t DUMMY

/-- The source's
`abbreviation (input) ABS2 :: ('a⇒'b)⇒'a⇒'b (binder "λ⇩2" 10)`,
`ABS2 f ≡ (λx. PROTECT2 (f x) DUMMY)`: protected abstraction, the
second flavour (Autoref's `ABS` is two `PROTECT`s, this one is one
`PROTECT2` *under* the binder, which is what makes it survive
instantiation of the bound variable). An `abbreviation (input)` in the
source, so an `abbrev` here. -/
abbrev ABS2 {α : Sort u} {β : Sort v} (f : α → β) : α → β :=
  fun x => PROTECT2 (f x) DUMMY

/-- The source's `binder "λ⇩2" 10` for `ABS2`, iterating over binders
exactly as an Isabelle binder does: `λ₂ x y => t` is
`ABS2 fun x => ABS2 fun y => t` (delta P4/D-bc). -/
macro "λ₂ " xs:ident+ " => " b:term : term => do
  let mut r := b
  for x in xs.reverse do
    r ← `(ABS2 fun $x => $r)
  return r

/-- The source's `lemma beta: "(λ⇩2x. f x)$x ≡ f x"`. -/
theorem beta {α : Sort u} {β : Sort v} (f : α → β) (x : α) :
    ((λ₂ y => f y) $ᵃ x) = f x := rfl

/-- `λ₂`-abstraction applied to an argument, as a simp *equation*. Lean's
`simp only` cannot take a bare `abbrev` name as an unfolding rule
(`SimpTheorems.addConst` wants a proposition), so the composite of
`ABS2`'s definition and `PROTECT2_def` is stated once here. Same content
as `beta` with the `$ᵃ` already erased; no source counterpart, because
Isabelle's simplifier unfolds `abbreviation`s on sight. -/
@[simp] theorem ABS2_apply {α : Sort u} {β : Sort v} (f : α → β) (x : α) :
    ABS2 f x = f x := rfl

/-- The source's
`definition APP' (infixl "$''" 900) where [simp, autoref_tag_defs]: "f$'a ≡ f a"`,
with its documentation verbatim:

> Another version of `APP`. Treated like `APP` by our tool. Required to
> avoid infinite pattern rewriting in some cases, e.g., map-lookup. -/
def APP' {α : Sort u} {β : Sort v} (f : α → β) (a : α) : β := f a

@[inherit_doc] infixl:900 " $ᵃ' " => APP'

/-- The source's `APP'` definition, with the source's own
`[simp, autoref_tag_defs]`. -/
@[simp, autoref_tag_defs] theorem APP'_def {α : Sort u} {β : Sort v} (f : α → β) (a : α) :
    (f $ᵃ' a) = f a := rfl

/-- The source's `definition [simp, autoref_tag_defs]: "PR_CONST x ≡ x"`,
its "Tag to protect constant", with the source's framing:

> Sometimes, whole terms should be protected from being processed by our
> tool. For example, our tool should not look into numerals. For this
> reason, the `PR_CONST` tag indicates terms that our tool shall handle
> as atomic constants, and never look into them. -/
def PR_CONST {α : Sort u} (x : α) : α := x

/-- The source's `PR_CONST` definition, with the source's own
`[simp, autoref_tag_defs]`. -/
@[simp, autoref_tag_defs] theorem PR_CONST_def {α : Sort u} (x : α) : PR_CONST x = x := rfl

/-- The source's `definition [simp, autoref_tag_defs]: "UNPROTECT x ≡ x"`,
with its documentation verbatim:

> The special form `UNPROTECT` can be used inside pattern rewrite rules.
> It has the effect to revert the protection from its argument, and then
> wrap it into a `PR_CONST`. -/
def UNPROTECT {α : Sort u} (x : α) : α := x

/-- The source's `UNPROTECT` definition, with the source's own
`[simp, autoref_tag_defs]`. -/
@[simp, autoref_tag_defs] theorem UNPROTECT_def {α : Sort u} (x : α) : UNPROTECT x = x := rfl

/-! ## Operation identification

The interface-typing judgment and the identification predicate. Both
take a `Sort` where the source takes `'b itself` — delta P4/D-bf. -/

/-- The source's
`definition intf_type :: 'a ⇒ 'b itself ⇒ bool (infix "::⇩i" 10) where [simp]: "c::⇩iI ≡ True"`,
its "Indicator predicate for conceptual typing of a constant". Carries
no information: it is a *declaration*, read off the shape of the tagged
term, which is why the source makes it `True`. -/
def intf_type {α : Sort u} (_c : α) (_I : Sort v) : Prop := True

@[inherit_doc] scoped infix:10 " ::ᵢ " => intf_type

/-- The source's `intf_type` definition, with the source's own
`[simp]`. -/
@[simp] theorem intf_type_def {α : Sort u} (c : α) (I : Sort v) :
    intf_type c I ↔ True := Iff.rfl

/-- The source's `lemma itypeI: "c::⇩iI"` — the lemma an
`id_rules` declaration instantiates. -/
theorem itypeI {α : Sort u} (c : α) (I : Sort v) : c ::ᵢ I := trivial

/-- The source's `lemma itypeI': "intf_type c TYPE('T)"`, the same
statement with the notation spelled out. -/
theorem itypeI' {α : Sort u} (c : α) (T : Sort v) : intf_type c T := trivial

/-- The source's `lemma itype_self: "(c::'a) ::⇩i TYPE('a)"`: every term
is conceptually typed by its own type. This is the lemma that licenses
`inferType` as the walk's fallback interface (delta P4/D-bf). -/
theorem itype_self {α : Sort u} (c : α) : c ::ᵢ α := trivial

/-- The source's
`definition CTYPE_ANNOT :: 'b ⇒ 'a itself ⇒ 'b (infix ":::⇩i" 10) where [simp]: "c:::⇩iI ≡ c"`:
a conceptual-type annotation written into the term by the user, which
`annot_rule` consumes. -/
def CTYPE_ANNOT {β : Sort v} (c : β) (_I : Sort u) : β := c

@[inherit_doc] scoped infix:10 " :::ᵢ " => CTYPE_ANNOT

/-- The source's `CTYPE_ANNOT` definition, with the source's own
`[simp]`. -/
@[simp] theorem CTYPE_ANNOT_def {β : Sort v} (c : β) (I : Sort u) :
    (c :::ᵢ I) = c := rfl

/-- The source's
`definition ID :: 'a ⇒ 'a ⇒ 'c itself ⇒ bool where [simp]: "ID t t' T ≡ t=t'"`,
its "Wrapper predicate for a conceptual type inference": `ID t t' T`
says term `t` was identified as `t'`, of interface `T`. -/
def ID {α : Sort u} (t t' : α) (_T : Sort v) : Prop := t = t'

/-- The source's `ID` definition, with the source's own `[simp]`. -/
@[simp] theorem ID_def {α : Sort u} (t t' : α) (T : Sort v) :
    ID t t' T ↔ t = t' := Iff.rfl

/-! ### Conceptual typing rules

The source's `subsubsection ‹Conceptual Typing Rules›`, statement for
statement. Every proof is the source's `by simp` on a definitional
identity; delta P4/D-bg records why the implementation walks against
these rather than resolving them, and names the correspondence. -/

/-- The source's `lemma ID_unfold_vars: "ID x y T ⟹ x≡y"`. -/
theorem ID_unfold_vars {α : Sort u} {x y : α} {T : Sort v} (h : ID x y T) : x = y := h

/-- The source's `lemma ID_PR_CONST_trigger: "ID (PR_CONST x) y T ⟹ ID (PR_CONST x) y T"`,
the identity rule whose only job is to give the driver's
`id_pr_const_rename_tac` a resolution trigger keyed on `PR_CONST`. -/
theorem ID_PR_CONST_trigger {α : Sort u} {x y : α} {T : Sort v}
    (h : ID (PR_CONST x) y T) : ID (PR_CONST x) y T := h

/-- The source's `lemma pat_rule: "⟦ p≡p'; ID p' t' T ⟧ ⟹ ID p t' T"` —
the rule every `pat_rules` / `def_pat_rules` entry is composed with
(`thm RS @{thm pat_rule}`). Walk correspondence: the two pattern simp
passes of `idOpCore`. -/
theorem pat_rule {α : Sort u} {p p' t' : α} {T : Sort v}
    (h₁ : p = p') (h₂ : ID p' t' T) : ID p t' T := h₁.trans h₂

/-- The source's
`lemma app_rule: "⟦ ID f f' TYPE('a⇒'b); ID x x' TYPE('a)⟧ ⟹ ID (f$x) (f'$x') TYPE('b)"`.
Walk correspondence: `idTerm`'s `APP` case. -/
theorem app_rule {α : Sort u} {β : Sort v} {f f' : α → β} {x x' : α}
    (hf : ID f f' (α → β)) (hx : ID x x' α) : ID (f $ᵃ x) (f' $ᵃ x') β := by
  have hf' : f = f' := hf
  have hx' : x = x' := hx
  show f x = f' x'
  rw [hf', hx']

/-- The source's
`lemma app'_rule: "⟦ ID f f' TYPE('a⇒'b); ID x x' TYPE('a)⟧ ⟹ ID (f$'x) (f'$x') TYPE('b)"` —
note the conclusion's *right*-hand side uses plain `$`, so identifying
through `APP'` is also what erases it. Walk correspondence: `idTerm`'s
`APP'` case. -/
theorem app'_rule {α : Sort u} {β : Sort v} {f f' : α → β} {x x' : α}
    (hf : ID f f' (α → β)) (hx : ID x x' α) : ID (f $ᵃ' x) (f' $ᵃ x') β := by
  have hf' : f = f' := hf
  have hx' : x = x' := hx
  show f x = f' x'
  rw [hf', hx']

/-- The source's
`lemma abs_rule: "⟦ ⋀x x'. ID x x' TYPE('a) ⟹ ID (t x) (t' x x') TYPE('b) ⟧ ⟹ ID (λ⇩2x. t x) (λ⇩2x'. t' x' x') TYPE('a⇒'b)"`.
Walk correspondence: `idTerm`'s `λ₂` case. -/
theorem abs_rule {α : Sort u} {β : Sort v} {t : α → β} {t' : α → α → β}
    (h : ∀ x x', ID x x' α → ID (t x) (t' x x') β) :
    ID (λ₂ x => t x) (λ₂ x' => t' x' x') (α → β) := by
  show ABS2 (fun x => t x) = ABS2 (fun x' => t' x' x')
  funext x
  show PROTECT2 (t x) DUMMY = PROTECT2 (t' x x) DUMMY
  have : t x = t' x x := h x x rfl
  rw [this]

/-- The source's `lemma id_rule: "c::⇩iI ⟹ ID c c I"`. Walk
correspondence: `idTerm`'s leaf case, after an `id_rules` hit. -/
theorem id_rule {α : Sort u} {c : α} {I : Sort v} (_h : c ::ᵢ I) : ID c c I := rfl

/-- The source's `lemma annot_rule: "ID t t' I ⟹ ID (t:::⇩iI) t' I"`.
Walk correspondence: `idTerm`'s `CTYPE_ANNOT` case, which is also where
the annotation *pins* the interface. -/
theorem annot_rule {α : Sort u} {t t' : α} {I : Sort v} (h : ID t t' I) :
    ID (t :::ᵢ I) t' I := h

/-- The source's `lemma fallback_rule: "ID (c::'a) c TYPE('c)"`. Walk
correspondence: `idTerm`'s leaf case with no `id_rules` hit
(delta P4/D-bi). -/
theorem fallback_rule {α : Sort u} (c : α) (T : Sort w) : ID c c T := rfl

/-- The source's `lemma unprotect_rl1: "ID (PR_CONST x) t T ⟹ ID (UNPROTECT x) t T"`.
Walk correspondence: `idTerm`'s `UNPROTECT` case. -/
theorem unprotect_rl1 {α : Sort u} {x t : α} {T : Sort v}
    (h : ID (PR_CONST x) t T) : ID (UNPROTECT x) t T := h

/-! ## ML-level code

The source's `subsection ‹ML-Level code›` and the `Id_Op` structure,
re-expressed as a `MetaM` pass (deltas P4/D-bg, P4/D-bh). -/

namespace IdOp

/-- The source's two `Attrib.setup_config_bool` flags, `id_debug` and
`id_trace_fallback`, as one record — the shape wave B2 chose for
Autoref's three (`Autoref/Phases.lean`'s `Config`, its delta S5). -/
structure Config where
  /-- The source's `cfg_id_debug`: on failure, report the stuck states
  the depth-first search accumulated (delta P4/D-bh). -/
  debug : Bool := false
  /-- The source's `cfg_id_trace_fallback`: report every application of
  `fallback_rule`. -/
  traceFallback : Bool := false
  deriving Inhabited, Repr

/-- The source's `Unsynchronized.ref []` inside `DF_SOLVE_FWD`: the
stuck-state accumulator. -/
abbrev StuckRef := IO.Ref (Array MessageData)

/-! ### Term matchers -/

/-- Match `PROTECT2 x y`. -/
def isPROTECT2? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``PROTECT2, #[_, x, y]) => some (x, y)
  | _ => none

/-- Match the source's `f$'a` (`APP' f a`). -/
def isAPP'? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``APP', #[_, _, f, x]) => some (f, x)
  | _ => none

/-- Match the source's `c:::⇩iI` (`CTYPE_ANNOT c I`). -/
def isCTYPE? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``CTYPE_ANNOT, #[_, c, I]) => some (c, I)
  | _ => none

/-- Match the source's `PR_CONST x`. -/
def isPRCONST? (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``PR_CONST, #[_, x]) => some x
  | _ => none

/-- Match the source's `UNPROTECT x`. -/
def isUNPROTECT? (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``UNPROTECT, #[_, x]) => some x
  | _ => none

/-- Match a `λ₂`-protected abstraction: a lambda whose body is
`PROTECT2 _ DUMMY`. Returns the *unprotected* body, still under the
binder. -/
def isABS2? (e : Expr) : Option (Name × Expr × Expr × BinderInfo) :=
  match e with
  | .lam n d b bi => do
    let (x, _) ← isPROTECT2? b
    return (n, d, x, bi)
  | _ => none

/-- Match an `ID t t' T` goal. -/
def isIDGoal? (e : Expr) : Option (Expr × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``ID, #[_, t, t', T]) => some (t, t', T)
  | _ => none

/-! ### Simp-set plumbing -/

/-- A `simp only [names]` context. Used for the source's
`put_simpset HOL_basic_ss ctxt addsimps @{thms …}`, which is exactly
"nothing but these lemmas". -/
def simpOnlyContext (names : Array Name) : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  for n in names do
    thms ← thms.addConst n
  Simp.mkContext { decide := false } (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)

/-- A `simp` context over a label-attribute rule database. The source's
`Named_Theorems_Rev.get`; see `Autoref/Attrs.lean`'s P4 section on the
order semantics. -/
def dbContext (db : Name) : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  for n in ← Lean.labelled db do
    thms ← thms.addConst n
  Simp.mkContext { decide := false } (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)

/-- The source's `unprotect_conv`:
`Simplifier.rewrite (HOL_basic_ss addsimps @{thms PROTECT2_def APP_def})`. -/
def unprotect (e : Expr) : MetaM Expr := do
  let (r, _) ← Meta.simp e (← simpOnlyContext #[``PROTECT2_def, ``APP_def])
  return r.expr

/-- A rule database entry's statement, with its *universe* parameters
replaced by fresh level metavariables as well as its term binders. The
level step is not optional: without it a rule stated over `{α : Type u}`
— which `pat_numeral` is — cannot unify with an occurrence at `Type 0`,
and the database silently never fires. (Refuted the version without it:
the numeral gate printed `4 ⤳ 4` instead of `4 ⤳ PR_CONST 4`.) -/
def ruleType (n : Name) : MetaM Expr := do
  let info ← getConstInfo n
  let lvls ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  return info.type.instantiateLevelParams info.levelParams lvls

/-- One step of a pattern database at *this node only* — the source's
`resolve_from_net_tac ctxt def_rl_net` / `… rl_net` against rules
composed with `pat_rule`, which applies **one** rule at the goal's own
term and then recurses through the `ID p' t' T` premise.

Deliberately not a simp pass. `pat_numeral`'s right-hand side contains
its own left-hand side (`numeral$x ≡ UNPROTECT (numeral$x)`), so a
rewrite-to-fixpoint diverges; the source's anti-loop device is exactly
that the *next* step is chosen by the new head (`UNPROTECT`, then
`PR_CONST`), and reproducing that needs single-step resolution.
Refuted the simp reading before settling on this one: it hits
`maximum recursion depth` on `(4 : ℕ)`. -/
def patStep (db : Name) (e : Expr) : MetaM (Option Expr) := do
  for n in ← Lean.labelled db do
    let (_, _, ty) ← forallMetaTelescope (← ruleType n)
    match ty.eq? with
    | some (_, lhs, rhs) =>
      -- `withReducible`: the source matches against a `Tactic.build_net`,
      -- i.e. syntactically up to pattern unification, and never by
      -- unfolding a definition. Without the restriction `pat_numeral`
      -- fires on *every* `ℕ`-valued constant whose body happens to be a
      -- literal — refuted on the gate's own `ga : ℕ := 5`, which came
      -- back as `PR_CONST 5`.
      if ← withReducible (isDefEq lhs e) then
        return some (← instantiateMVars rhs)
    | none => pure ()
  return none

/-! ### `Id_Op.protect` — the term walk -/

/-- `Autoref/IdOps.lean`'s `opSplit`, repeated here rather than imported
(delta P4/D-ba) with its delta I3 rationale: a Lean application splits at
its last non-explicit argument, because implicit and instance arguments
belong to the *operator*, not to the argument spine. `k` is the number
of arguments belonging to the operator. -/
def opSplit (e : Expr) : MetaM Nat := do
  let args := e.getAppArgs
  if args.isEmpty then return 0
  let info ← getFunInfoNArgs e.getAppFn args.size
  let mut k := args.size
  for i in [0:args.size] do
    let j := args.size - 1 - i
    if h : j < info.paramInfo.size then
      if info.paramInfo[j].binderInfo.isExplicit then k := j else break
    else break
  return k

/-- The source's `Id_Op.protect`:

```ml
fun protect env (@{mpat "?t:::⇩i?I"}) = … protect env t …
  | protect _ (t as @{mpat "PR_CONST _"}) = t
  | protect env (t1$t2) = … @{mk_term env: "?t1.0 $ ?t2.0"}
  | protect env (Abs (x,T,t)) = … "PROTECT2 ?t DUMMY" …
  | protect _ t = t
```

i.e. replace every function application by `$ᵃ` and wrap every
abstraction body in `PROTECT2 _ DUMMY`, stopping at `PR_CONST` and
descending through `:::ᵢ`. The application case splits per
delta P4/D-ba. -/
partial def protect (e : Expr) : MetaM Expr := do
  if let some (c, I) := isCTYPE? e then
    return ← mkAppOptM ``CTYPE_ANNOT #[none, some (← protect c), some I]
  if (isPRCONST? e).isSome then
    return e
  match e with
  | .lam n d b bi =>
    withLocalDecl n bi d fun x => do
      let body ← protect (b.instantiate1 x)
      mkLambdaFVars #[x] (← mkAppM ``PROTECT2 #[body, mkConst ``DUMMY])
  | .app .. =>
    let k ← opSplit e
    let args := e.getAppArgs
    if k ≥ args.size then return e
    let mut cur := mkAppN e.getAppFn (args.extract 0 k)
    for a in args.extract k args.size do
      cur ← mkAppM ``APP #[cur, ← protect a]
    return cur
  | _ => return e

/-! ### `id_rules` lookup

The source's `ityping`/`has_type` tables: `id_rules` entries have
conclusion `c ::⇩i TYPE('T)`, indexed by `c`'s head constant. -/

/-- Read the `id_rules` database as a list of `(c, I)` pairs, with the
declaration's own binders instantiated to metavariables so that a
declared typing can be matched against an occurrence. -/
def idRulePairs : MetaM (Array (Expr × Expr)) := do
  let mut out := #[]
  for n in ← Lean.labelled `id_rules do
    let (_, _, ty) ← forallMetaTelescope (← ruleType n)
    match ty.getAppFnArgs with
    | (``intf_type, #[_, c, I]) => out := out.push (c, I)
    | _ => pure ()
  return out

/-- The source's `id_rules`-driven `id_rule` step: does some declared
conceptual typing apply to this term? Returns the declared interface. -/
def idRuleFor? (e : Expr) : MetaM (Option Expr) := do
  for (c, I) in ← idRulePairs do
    -- `withReducible` for the reason `patStep` uses it: the source
    -- indexes `id_rules` in a syntactic net.
    if ← withReducible (isDefEq c e) then
      return some (← instantiateMVars I)
  return none

/-! ### `id_tac` — the identification walk -/

/-- The codomain of a function type, when it has one and it does not
depend on the argument. -/
def codomain? (τ : Expr) : MetaM (Option Expr) := do
  match ← whnf τ with
  | .forallE _ _ b _ => return if b.hasLooseBVars then none else some b
  | _ => return none

/-- The source's `Id_Op.id_tac`, as a walk (deltas P4/D-bg, P4/D-bh):
tag a protected term into identified form and report its interface. The
cases, in the source's `step_tac` order:

* `annot_rule` — a `:::ᵢ` annotation pins the interface;
* `unprotect_rl1` — `UNPROTECT x` unprotects and re-wraps as
  `PR_CONST`;
* `PR_CONST` — an atomic constant, "never look inside";
* `pat_rule` over `def_pat_rules`, then over `pat_rules` — one step
  each, then recurse (`patStep`);
* `app_rule` / `app'_rule` — the `$ᵃ` and `$ᵃ'` spines;
* `abs_rule` — a `λ₂`-protected abstraction;
* `id_rule` — a leaf with a declared typing;
* `fallback_rule` — a leaf without one.

The one reordering against the source's `step_tac`: `do_unprotect_tac`
and `id_pr_const_rename_tac` are tried *before* the two pattern nets
rather than after. The source can afford the other order because its
nets are keyed on the head constant and no pattern rule has head
`UNPROTECT` or `PR_CONST`, so those goals fall through to the unprotect
step anyway; making the order explicit is what keeps the anti-loop
device visible rather than accidental.

Anything else is a stuck state: recorded and reported, never silently
skipped. -/
partial def idTerm (cfg : Config) (stuck : StuckRef) (e : Expr) :
    MetaM (Expr × Expr) := do
  -- `annot_rule`
  if let some (c, I) := isCTYPE? e then
    let (c', _) ← idTerm cfg stuck c
    return (c', I)
  -- `unprotect_rl1`
  if let some x := isUNPROTECT? e then
    let x' ← unprotect x
    return ← idTerm cfg stuck (← mkAppM ``PR_CONST #[x'])
  -- `PR_CONST`: atomic, and typed by `id_rules` if declared
  if (isPRCONST? e).isSome then
    match ← idRuleFor? e with
    | some I => return (e, I)
    | none => return (e, ← inferType e)
  -- `pat_rule` over `def_pat_rules` (the source's `def_rl_net`, first),
  -- then over `pat_rules` — one step, then recurse.
  if let some e' ← patStep `def_pat_rules e then
    return ← idTerm cfg stuck e'
  if let some e' ← patStep `pat_rules e then
    return ← idTerm cfg stuck e'
  -- `app_rule`
  if let some (f, x) := Autoref.isAPP? e then
    let (f', If) ← idTerm cfg stuck f
    let (x', _) ← idTerm cfg stuck x
    let r ← mkAppM ``APP #[f', x']
    match ← codomain? If with
    | some T => return (r, T)
    | none => return (r, ← inferType r)
  -- `app'_rule`: the conclusion re-forms the spine with plain `APP`
  if let some (f, x) := isAPP'? e then
    let (f', If) ← idTerm cfg stuck f
    let (x', _) ← idTerm cfg stuck x
    let r ← mkAppM ``APP #[f', x']
    match ← codomain? If with
    | some T => return (r, T)
    | none => return (r, ← inferType r)
  -- `abs_rule`
  if let some (n, d, body, bi) := isABS2? e then
    let r ← withLocalDecl n bi d fun x => do
      let (b', _) ← idTerm cfg stuck (body.instantiate1 x)
      mkLambdaFVars #[x] (← mkAppM ``PROTECT2 #[b', mkConst ``DUMMY])
    return (r, ← inferType r)
  -- a bare lambda, a `let`, a projection, a metavariable: stuck
  if e.isLambda || e.isLet || e.isProj || e.isMVar then
    stuck.modify (·.push m!"no rule for{indentExpr e}")
    throwError "no `ID` rule for the subterm{indentExpr e}"
  -- `id_rule` / `fallback_rule`
  match ← idRuleFor? e with
  | some I => return (e, I)
  | none =>
    let T ← inferType e
    if cfg.traceFallback then
      logInfo m!"ID_OP: Applying fallback rule: ID{indentExpr e}\nat interface{indentExpr T}"
    return (e, T)

/-! ### The `id_op` phase driver

The failure envelope is `Autoref/Phases.lean`'s (its delta P6), with
`sepref` in place of `autoref`. The Sepref pipeline is its own — the
source drives it through `Refine_Util.PHASES'`, not `Autoref_Phases` —
so the ordinals are the Sepref pipeline's: `id_op` is its first phase.
`Sepref/Monadify.lean` numbers its six sub-phases from 20. -/

/-- The Sepref pipeline's ordinal for this phase. -/
def idPhasePrio : Nat := 10

/-- The source's `Id_Op.id_tac Normal`: `init_tac` (protect the term)
followed by `solve_tac` (`DF_SOLVE_FWD` over `step_tac`). Returns the
identified term, its interface, and a proof of `ID t t' T`.

The proof is `rfl` (delta P4/D-bj): `ID t t' T` *is* `t = t'`, every tag
the walk adds is a `def` the kernel unfolds, and every pattern rule in
scope is a definitional identity — the source's are too
(`op_map_empty ≡ λ_. None` and its kin are *definitions*, and
`pat_numeral`'s two sides differ only by `UNPROTECT`). A pattern rule
that is genuinely propositional would fail the `isDefEq` guard below
with the message the guard prints, which is the signal to upgrade the
walk to thread the pattern equations through congruence. -/
def idOpCore (cfg : Config) (t : Expr) : MetaM (Expr × Expr × Expr) := do
  let stuck : StuckRef ← IO.mkRef #[]
  -- `init_tac`: `protect_conv`.
  let t₀ ← protect t
  try
    let (t', T) ← idTerm cfg stuck t₀
    let ty ← mkAppOptM ``ID #[none, some t, some t', some T]
    unless ← isDefEq t t' do
      throwError "the identified term is not definitionally the term it came from.\n\
        before:{indentExpr t}\nafter:{indentExpr t'}"
    let pf ← mkExpectedTypeHint (← mkEqRefl t) ty
    return (t', T, pf)
  catch ex =>
    let inner := ex.toMessageData
    let ss ← stuck.get
    if cfg.debug && !ss.isEmpty then
      let trace := MessageData.joinSep ss.toList m!"\n"
      throwError "sepref: phase 'id_op' (priority {idPhasePrio}) failed.\n{inner}\n\
        stuck states ({ss.size}), depth-first order:{indentD trace}"
    else
      throwError "sepref: phase 'id_op' (priority {idPhasePrio}) failed.\n{inner}"

end IdOp

/-! ### The `sepref_id_op` entry points

The source's Isar-level entry is
`apply (tactic ‹Id_Op.id_tac Id_Op.Normal @{context} 1›)` on a goal
`ID t ?t' (?T::?'d itself)` (its commented-out example, quoted in the
`.thy`). Two entry points here: a tactic for exactly that goal shape,
and a command for inspecting the result — the command is what the gate
below pins, because a `#guard_msgs`-checkable string is worth more to
supervision than a schematic goal. -/

open IdOp in
/-- The source's `Id_Op.id_tac Normal`, on a goal `ID t ?t' T`. With
`dbg`, the source's `id_debug` flag; with `trace`, its
`id_trace_fallback`. -/
elab "sepref_id_op" d:(" dbg")? tr:(" trace")? : tactic => do
  Tactic.liftMetaTactic fun g => do
    let ty ← instantiateMVars (← g.getType)
    let some (t, t', T) := isIDGoal? ty
      | throwError "sepref_id_op: the goal is not of the form `ID t ?t' T`:{indentExpr ty}"
    let cfg : IdOp.Config := { debug := d.isSome, traceFallback := tr.isSome }
    let (r, I, pf) ← idOpCore cfg t
    unless ← isDefEq T I do
      throwError "sepref: phase 'id_op' (priority {idPhasePrio}) left work undone.\n\
        the goal's interface{indentExpr T}\nis not the identified one{indentExpr I}"
    unless ← isDefEq t' r do
      throwError "sepref: phase 'id_op' (priority {idPhasePrio}) left work undone.\n\
        the goal's identified term{indentExpr t'}\nis not the one the walk built{indentExpr r}"
    g.assign pf
    return []

open IdOp in
/-- Inspect the `id_op` phase on a closed term: prints
`t ⤳ t' : T`. With `dbg`, the source's `id_debug` flag. -/
elab "#sepref_id_op" d:(" dbg")? t:term : command =>
  Command.liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let (r, I, _) ← IdOp.idOpCore { debug := d.isSome } e
    logInfo m!"{e} ⤳ {r} : {I}"

/-! ## Default setup

The source's `subsection ‹Default Setup›`. Its `subsubsection ‹Numerals›`
carries the source's own TODO verbatim ("Either remove, or also add
numerals 0 and 1!"). Lean's numeric literals are
`@OfNat.ofNat α n inst`, and `Autoref/IdOps.lean`'s delta I3 records that
the operator/argument split already makes such a literal a *leaf*; the
`def_pat_rules` entry below is nevertheless ported at the source's
statement, over `OfNat.ofNat`, so that a literal is identified as an
atomic `PR_CONST` rather than as an operator with an interface. -/

/-- The source's `lemma pat_numeral[def_pat_rules]: "numeral$x ≡ UNPROTECT (numeral$x)"`,
at Lean's numeral constant. -/
@[def_pat_rules] theorem pat_numeral {α : Type u} (n : Nat) [inst : OfNat α n] :
    (@OfNat.ofNat α n inst) = UNPROTECT (@OfNat.ofNat α n inst) := rfl

/-- The source's `lemma id_nat_const[id_rules]: "(PR_CONST (a::nat)) ::⇩i TYPE(nat)"`. -/
@[id_rules] theorem id_nat_const (a : Nat) : (PR_CONST a) ::ᵢ Nat := trivial

/-- The source's `lemma id_int_const[id_rules]: "(PR_CONST (a::int)) ::⇩i TYPE(int)"`. -/
@[id_rules] theorem id_int_const (a : Int) : (PR_CONST a) ::ᵢ Int := trivial

/-! ## The executable gate (design record ledger D4)

Two things can go wrong here and neither is mathematics: a notation can
parse the wrong tree, and the walk can build a term that is not the one
it started from. The first half of the gate checks parses the way
`Autoref/Tagging.lean`'s does — state the tagged form, state the plain
form, ask the tag simp set to identify them, which it can only do if the
tagged form parsed as intended. The second half runs the phase and pins
its output with `#guard_msgs`.

The expected forms were written from the source's rules by hand before
the walk existed. -/

namespace Gate

variable {α β γ : Type}

/-! ### Parses -/

-- The protection constants all erase.
example (x : α) (y : Prop) : PROTECT2 x y = x := by simp
example (x : α) : PROTECT2_syn x = x := by simp
example (f : α → β) (a : α) : (f $ᵃ' a) = f a := by simp
example (x : α) : PR_CONST x = x := by simp
example (x : α) : UNPROTECT x = x := by simp

-- `λ₂` is a binder that iterates, exactly as the source's does.
example (f : α → β) : (λ₂ x => f x) = f := by funext x; simp
example (f : α → β → γ) : (λ₂ x y => f x y) = f := by funext x y; simp

-- `λ₂` and `$ᵃ` interact as `beta` says.
example (f : α → β) (x : α) : ((λ₂ y => f y) $ᵃ x) = f x := beta f x

-- `$ᵃ'` is `infixl 900`, like `$ᵃ`.
example (f : α → α → β) (a b : α) : (f $ᵃ' a $ᵃ' b) = f a b := by simp

-- `::ᵢ` at the source's precedence 10, over a `Sort` (delta P4/D-bf);
-- it is a declaration, so it holds of everything.
example (x : α) : x ::ᵢ Nat := by simp
example (x : α) : x ::ᵢ α := itype_self x

-- `:::ᵢ` at precedence 10, and it erases.
example (x : α) : (x :::ᵢ Nat) = x := by simp

-- `ID` is equality with an interface riding along.
example (x : α) : ID x x Nat := by simp
example (x y : α) (h : ID x y Nat) : x = y := ID_unfold_vars h

/-! ### The rules, exercised

Each is applied at a concrete instance, so that a statement that
type-checks but cannot be *used* would be caught. -/

example (f : α → β) (x : α) : ID (f $ᵃ x) (f $ᵃ x) β :=
  app_rule (fallback_rule f (α → β)) (fallback_rule x α)

example (f : α → β) (x : α) : ID (f $ᵃ' x) (f $ᵃ x) β :=
  app'_rule (fallback_rule f (α → β)) (fallback_rule x α)

example (t : α → β) : ID (λ₂ x => t x) (λ₂ x => t x) (α → β) :=
  abs_rule (t' := fun _ x => t x) fun x x' h => by
    have : x = x' := h
    subst this; rfl

example (x : α) : ID (x :::ᵢ Nat) x Nat := annot_rule (fallback_rule x Nat)

example (x : α) : ID (UNPROTECT x) (PR_CONST x) Nat :=
  unprotect_rl1 (fallback_rule (PR_CONST x) Nat)

example (x : Nat) : ID (PR_CONST x) (PR_CONST x) Nat := id_rule (id_nat_const x)

example (p p' t' : α) (h : p = p') : ID p t' Nat → ID p t' Nat := fun h' =>
  pat_rule h (h.symm ▸ h')

/-! ### The phase, pinned

`#sepref_id_op` prints `t ⤳ t' : T`. The expected right-hand sides are
hand-derived: `protect` turns every explicit application into `$ᵃ` and
every abstraction into `fun x => PROTECT2 … DUMMY`, `def_pat_rules`
rewrites a numeral into `UNPROTECT`, `unprotect_rl1` re-wraps it as
`PR_CONST`, and `id_nat_const` types it. -/

-- A command elaborator does not see section `variable`s, so the gate's
-- operator and operands are named `def`s.
/-- An operator for the gate: a binary operation on `ℕ`. -/
def gf (x y : Nat) : Nat := x * y + 1
/-- An operand for the gate. -/
def ga : Nat := 5
/-- A second operand for the gate. -/
def gb : Nat := 7

-- A first-order application: two `$ᵃ`s, left-associated, and the
-- interface is the codomain (`app_rule` twice).
/-- info: gf ga gb ⤳ gf $ᵃ ga $ᵃ gb : ℕ -/
#guard_msgs in
#sepref_id_op gf ga gb

-- A literal is *not* an operator: `pat_numeral` sends it through
-- `UNPROTECT` to `PR_CONST`, and `id_nat_const` gives it `ℕ`.
/-- info: 4 ⤳ PR_CONST 4 : ℕ -/
#guard_msgs in
#sepref_id_op (4 : Nat)

-- A nested application: the inner spine is identified inside the outer.
/-- info: gf ga (gf ga gb) ⤳ gf $ᵃ ga $ᵃ (gf $ᵃ ga $ᵃ gb) : ℕ -/
#guard_msgs in
#sepref_id_op gf ga (gf ga gb)

-- An abstraction: `protect` puts a `PROTECT2 _ DUMMY` under the binder
-- and `abs_rule` walks under it.
/-- info: fun x => gf x gb ⤳ fun x => PROTECT2 (gf $ᵃ x $ᵃ gb) DUMMY : ℕ → ℕ -/
#guard_msgs in
#sepref_id_op fun x => gf x gb

-- An explicit interface annotation pins the interface, and `annot_rule`
-- erases the annotation from the identified term.
/-- info: ga :::ᵢ Bool ⤳ ga : Bool -/
#guard_msgs in
#sepref_id_op (ga :::ᵢ Bool)

-- The tactic form, on the goal shape the source's own example uses.
example : ID (gf ga gb) (gf $ᵃ ga $ᵃ gb) Nat := by sepref_id_op

/-! ### A stuck state, pinned

The source's `id_debug` flag exists so that a failure hands back the
states the depth-first search got stuck in rather than failing silently.
A `let` has no `ID` rule in `Sepref_Id_Op.thy` — `step_tac`'s seven
alternatives cover annotations, applications, abstractions, constants
and the two protection tags, and nothing else — so it is the smallest
honest stuck state. Both the plain and the `dbg` failure are pinned, and
the difference between them *is* the flag's content. -/

/--
error: sepref: phase 'id_op' (priority 10) failed.
no `ID` rule for the subterm
  let y := 1;
  y + y
-/
#guard_msgs in
#sepref_id_op (let y : Nat := 1; y + y)

-- The same failure under the source's `id_debug` flag: the stuck states
-- the depth-first search accumulated are handed back, deepest first.
/--
error: sepref: phase 'id_op' (priority 10) failed.
no `ID` rule for the subterm
  let y := 1;
  y + y
stuck states (1), depth-first order:
  no rule for
    let y := 1;
    y + y
-/
#guard_msgs in
#sepref_id_op dbg (let y : Nat := 1; y + y)

end Gate

end Lax13Proofs.Refine.Sepref
