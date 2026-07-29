import Lax13Proofs.Refine.Autoref.Attrs

/-!
The tag layer: term protection, annotation, and interface types.

Port of `thys/Automatic_Refinement/Tool/Autoref_Tagging.thy` and the
interface-type head of `thys/Automatic_Refinement/Tool/Autoref_Id_Ops.thy`
of AFP `Automatic_Refinement` (Lammich) at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1 — AFP for Isabelle2025-2,
release 2026-02-06. The verbatim source text this file is checked
against is `plans/word-ram/refinement-tower/p2-autoref-extracts.md` §3;
everything below quotes it in its doc-comments.

Nothing here mentions `NRest` or any relator: the tag layer is pure
term plumbing, one layer below both, and the import list is
`Autoref/Attrs.lean` and nothing else.

## What this layer is for (the extract's closing "Role" paragraph)

> `APP`/`OP`/`ANNOT`/`PROTECT`/`ABS` exist purely so Autoref's (and,
> downstream, Sepref's) term-rewriting passes have a syntax-directed
> handle on application, abstraction, and "stop looking here" boundaries
> that survives Isabelle's automatic beta/eta contraction and
> higher-order unification — every rewrite rule in the pipeline is
> stated over tagged terms, never raw HOL applications. `CONST_INTF`/
> `ID_OP` sit one layer up: they carry the *conceptual type* (interface)
> assigned to a tagged term through the identification phase, so that by
> the time Autoref reaches relator inference, every subterm's abstract
> interface is already fixed data, not something to re-derive.

and, on why the device is not weakened by the move to Lean:

> Design.md's Lean counterpart (`Autoref/Tool.lean`, phases under source
> names, design.md P2 row 4) needs an analogous protection device only
> insofar as Lean's own HOU is weaker than Isabelle's, not stronger
> (design.md §2, substrate delta 3) — the `hn_ctxt`-style tagging
> discipline is *more* load-bearing under Lean, per design.md fidelity
> note under P4.

## The source, verbatim

`Autoref_Tagging.thy`:

```isabelle
text ‹General protection tag›
definition PROTECT where [simp, autoref_tag_defs]: "PROTECT x ≡ x"

text ‹General annotation tag›
typedecl annot
definition ANNOT :: "'a ⇒ annot ⇒ 'a"
  where [simp, autoref_tag_defs]: "ANNOT x a ≡ x"

text ‹Operation-tag, Autoref does not look beyond this›
definition OP where [simp, autoref_tag_defs]: "OP x ≡ x"

text ‹Protected function application›
definition APP (infixl "$" 900) where [simp, autoref_tag_defs]: "f$a ≡ f a"

text ‹Protected abstraction›
abbreviation ABS :: "('a⇒'b)⇒'a⇒'b" (binder "λ''" 10)
  where "ABS f ≡ PROTECT (λx. PROTECT (f x))"

text ‹Relator annotation›
consts rel_annot :: "('c×'a) set ⇒ annot"
abbreviation rel_ANNOT :: "'a ⇒ ('c × 'a) set ⇒ 'a" (infix ":::" 10)
  where "t:::R ≡ ANNOT t (rel_annot R)"

text ‹Indirect annotation›
typedecl rel_name
consts ind_annot :: "rel_name ⇒ annot"
abbreviation ind_ANNOT :: "'a ⇒ rel_name ⇒ 'a" (infix "::#" 10)
  where "t::#s ≡ ANNOT t (ind_annot s)"
```

`Autoref_Id_Ops.thy`:

```isabelle
typedecl interface

definition intfAPP
  :: "(interface ⇒ _) ⇒ interface ⇒ _"
  where "intfAPP f x ≡ f x"

consts i_fun :: "interface ⇒ interface ⇒ interface"
abbreviation i_fun_app (infixr "→⇩i" 60) where "i1→⇩ii2 ≡ ⟨i1,i2⟩⇩ii_fun"

text ‹Declaration of interface-type for constant›
definition CONST_INTF :: "'a ⇒ interface ⇒ bool" (infixr "::⇩i" 10)
  where [simp]: "c::⇩i I ≡ True"

text ‹
  Predicate for operation identification. ‹ID_OP t t' I› means
  that term ‹t› has been annotated as ‹t'›, and its interface
  is ‹I›.
›
definition ID_OP :: "'a ⇒ 'a ⇒ interface ⇒ bool"
  where [simp]: "ID_OP t t' I ≡ t=t'"
```

## Substrate deltas and departures, each flagged

**T1 — `Tagging.lean` is a module the design record does not list.**
Design record §7's P2 skeleton is `Autoref/{Relators,Param,Solver,Tool}`.
The tag layer is split out into a fifth module rather than folded into
`Tool.lean` for one reason: `Tool.lean` is the *phase driver*
(`Autoref_Phases`/`Autoref_Translate`), the tags are *object-language
constants* that every rule in wave C is stated over, and wave C's rule
files must import the constants without importing the driver. Keeping
`Tool.lean` free for the driver is the whole point; the source itself
splits the same way (`Autoref_Tagging.thy` is its own theory, imported
by `Autoref_Id_Ops.thy`, imported by `Autoref_Tool.thy`). Recorded here
as a departure from §7's file list, not from the source.

**T2 — `typedecl` and `consts` are rendered without axioms.** Isabelle's
`typedecl annot` / `typedecl rel_name` / `typedecl interface` introduce
opaque nonempty types, and `consts rel_annot` / `ind_annot` / `i_fun`
introduce uninterpreted constants — both are axiomatic devices. Adding
axioms is not available to us (the archive's headline claims are
kernel-clean and stay that way), so each is rendered as a small
inductive:

* `RelName` is a `String`-carrying structure. The source's inhabitants
  of `rel_name` arise from users writing `consts my_name :: rel_name`;
  `RelName.mk "my_name"` is that, with decidable equality thrown in.
* `Interface` is the free term algebra `const (name : String) | app`,
  which is exactly what the source's interface terms *are*: user-declared
  constants (`i_std`, `i_nat`, `consts i_graph :: interface ⇒ interface`)
  applied to each other through `intfAPP`. `i_fun` becomes the
  constructor application `app (app (const "i_fun") i₁) i₂`, so
  `i₁ →ᵢ i₂` is an injective marker — which is what every phase treats
  it as, and what the source can only assume.
* `Annot` is `rel | ind (s : RelName)`. Here one bit of information is
  dropped on purpose: `rel_annot`'s argument `R : Set (γ × α)` cannot be
  stored in a `Type`-valued `Annot` without lifting `Annot` to `Type 1`,
  and lifting it would put a `Type 1` argument on `ANNOT`, which every
  tagged term in the pipeline carries. It is not needed: `rel_annot R`
  is an *application term*, so `R` is present in the syntax tree that
  the phases match on, exactly as it is in the source, where
  `rel_annot` likewise has no defining equation. The price is that
  `rel_annot R = rel_annot R'` is provable here and merely unprovable
  there; nothing in the pipeline asks.

  For the same reason `rel_annot` and `ind_annot` are the two
  definitions in this file that get **no** `[simp]` tag and no
  `autoref_tag_defs` entry: the source's `consts` cannot be unfolded at
  all, and a simp set that erased the annotation would erase the point.

**T3 — notation spellings.** Three of the source's infixes are taken
verbatim (`:::` at 10, `::#` at 10, both Lean-legal tokens); three are
not Lean-legal and are respelled at the source's own precedence and
associativity:

| source | here | why |
|---|---|---|
| `f$a`, `infixl 900` | `f $ᵃ a`, `infixl:900` | `$` is Lean 4's antiquotation marker. `ᵃ` for *autoref application*; the `ᵣ` subscript is already spoken for by `Relators.lean`'s `→ᵣ` / `×ᵣ` |
| `i1→⇩ii2`, `infixr 60` | `i₁ →ᵢ i₂`, `infixr:60` | subscript-i rendered as `ᵢ` |
| `c::⇩i I`, `infixr 10` | `c ::ᵢ I`, `infixr:10` | same |

The source's `binder "λ''"` for `ABS` is **not** ported. It would add a
`term`-level syntax beginning with `λ` to a module the archive root
imports, and the blast radius of a tokenizer interaction with Lean's own
`λ` is out of proportion to a display convenience: `ABS f` is the
artifact, and it is written `ABS fun x => …`. Revisit if a wave-C rule
statement turns out to be unreadable without it.

**T4 — `Sort u`, not `Type`.** HOL has one universe of types and `bool`
lives in it, so `PROTECT`/`OP`/`APP`/`ANNOT`/`CONST_INTF`/`ID_OP` are
applied to propositions as freely as to data. In Lean that is the
`Prop`/`Type` split, so the tag constants are universe-polymorphic over
`Sort`. This is the direction of *more* generality, and it is the only
rendering under which the tags can protect a `Prop`-valued side
condition — which is precisely what wave C's `SIDE_PRECOND`-shaped rules
will need. `rel_annot`/`rel_ANNOT` are the exception: their relation
argument forces `Type` on the annotated type, as in `Relators.lean`.

**T5 — what is deliberately absent.** `GEN_OP`, `SIDE_PRECOND`, the
`PRIO_TAG_*` family and everything else from `Autoref_Fix_Rel.thy` is
**not** defined here, in any form. No verbatim extract of that theory
exists yet — a separate extraction is fetching it for wave C — and the
fidelity charter forbids guessing at a source statement that has not
been read. The two places those constants are *visible* in what we do
have (`GEN_OP eq (=) (R→R→Id) ⟹ …` and `SIDE_PRECOND (l'≠[]) ⟹ …` in
`p2-tutorial-extracts.md` §3) show their consuming position only, not
their definitions.

Also absent, for the same reason it is absent from `Relators.lean`
(delta R1): the source's `⟨i1,i2⟩⇩i` *notation* for iterated `intfAPP`.
`intfAPP` itself is ported verbatim; `relAPP`-style argument-tagging
syntax exists to defeat Isabelle's higher-order unifier and has no Lean
counterpart to defeat.
-/

universe u v

namespace Lax13Proofs.Refine

/-! ### General protection tags (`Autoref_Tagging.thy`) -/

/-- The source's `PROTECT x ≡ x`, its "General protection tag": a
definitional identity whose only job is to stop a rewriting pass from
looking inside. -/
def PROTECT {α : Sort u} (x : α) : α := x

/-- The source's `PROTECT_def`, with the source's own
`[simp, autoref_tag_defs]`. -/
@[simp, autoref_tag_defs] theorem PROTECT_def {α : Sort u} (x : α) : PROTECT x = x := rfl

/-- Stand-in for the source's `typedecl rel_name` (delta T2): the names
under which a relator can be referred to *indirectly*, i.e. before the
relator itself has been chosen. The source's inhabitants come from users
writing `consts my_name :: rel_name`; here they are strings. -/
structure RelName where
  /-- The name itself. -/
  name : String
deriving DecidableEq, Repr, Inhabited

/-- Stand-in for the source's `typedecl annot` (delta T2), the type of
the annotations `ANNOT` carries. Its two constructors are the source's
two `consts` into `annot`: `rel_annot` (a relator annotation, whose
relation argument is recovered from the *term* `rel_annot R`, not from
this value) and `ind_annot` (an indirect annotation, naming a relator). -/
inductive Annot where
  /-- The source's `rel_annot`, argument erased — see delta T2. -/
  | rel : Annot
  /-- The source's `ind_annot s`. -/
  | ind (s : RelName) : Annot
deriving DecidableEq, Repr, Inhabited

/-- The source's `ANNOT x a ≡ x`, its "General annotation tag": carries
an `Annot` alongside a term without changing it. -/
def ANNOT {α : Sort u} (x : α) (_a : Annot) : α := x

/-- The source's `ANNOT_def`, with the source's own
`[simp, autoref_tag_defs]`. -/
@[simp, autoref_tag_defs] theorem ANNOT_def {α : Sort u} (x : α) (a : Annot) :
    ANNOT x a = x := rfl

/-- The source's `OP x ≡ x`, its "Operation-tag, Autoref does not look
beyond this": the boundary marking a term as *the* operation being
translated. -/
def OP {α : Sort u} (x : α) : α := x

/-- The source's `OP_def`, with the source's own
`[simp, autoref_tag_defs]`. -/
@[simp, autoref_tag_defs] theorem OP_def {α : Sort u} (x : α) : OP x = x := rfl

/-- The source's `APP (infixl "$" 900)`, its "Protected function
application": application that survives beta contraction because it is
not, syntactically, an application. -/
def APP {α : Sort u} {β : Sort v} (f : α → β) (a : α) : β := f a

@[inherit_doc] infixl:900 " $ᵃ " => APP

/-- The source's `APP_def`, with the source's own
`[simp, autoref_tag_defs]`. -/
@[simp, autoref_tag_defs] theorem APP_def {α : Sort u} {β : Sort v} (f : α → β) (a : α) :
    (f $ᵃ a) = f a := rfl

/-- The source's `ABS f ≡ PROTECT (λx. PROTECT (f x))`, its "Protected
abstraction". An `abbreviation` in the source, so an `abbrev` here: it
is meant to be seen through by everything except the rewriting passes,
which see the `PROTECT`s. -/
abbrev ABS {α : Sort u} {β : Sort v} (f : α → β) : α → β :=
  PROTECT (fun x => PROTECT (f x))

/-! ### Relator and indirect annotation -/

/-- The source's `consts rel_annot :: ('c×'a) set ⇒ annot`. Not tagged
`[simp]` and not in `autoref_tag_defs`: the source's constant has no
defining equation, and the phases read `R` off the application term
(delta T2). -/
def rel_annot {γ α : Type} (_R : Set (γ × α)) : Annot := .rel

/-- The source's `rel_ANNOT :: 'a ⇒ ('c × 'a) set ⇒ 'a (infix ":::" 10)`,
`t:::R ≡ ANNOT t (rel_annot R)`: "translate `t` at relator `R`". -/
abbrev rel_ANNOT {γ α : Type} (t : α) (R : Set (γ × α)) : α := ANNOT t (rel_annot R)

@[inherit_doc] infix:10 " ::: " => rel_ANNOT

/-- The source's `consts ind_annot :: rel_name ⇒ annot`. Not tagged, for
the reason `rel_annot` is not (delta T2). -/
def ind_annot (s : RelName) : Annot := .ind s

/-- The source's `ind_ANNOT :: 'a ⇒ rel_name ⇒ 'a (infix "::#" 10)`,
`t::#s ≡ ANNOT t (ind_annot s)`: "translate `t` at the relator named
`s`", the relator itself still to be resolved. -/
abbrev ind_ANNOT {α : Sort u} (t : α) (s : RelName) : α := ANNOT t (ind_annot s)

@[inherit_doc] infix:10 " ::# " => ind_ANNOT

/-! ### The interface layer (`Autoref_Id_Ops.thy`)

Interfaces are the *conceptual types* the identification phase assigns:
`i_std` for a type that needs no refinement, `i_nat`, `i_set`,
`⟨i_nat⟩i_graph`, `i₁ →ᵢ i₂`. They are one layer above the relators —
an interface says *what a term means*, a relator says *how it is
represented* — and fixing them first is what stops relator inference
from having to re-derive them (the Role paragraph in the header). -/

/-- Stand-in for the source's `typedecl interface` (delta T2): the free
term algebra over user-declared interface constants. The source's
`consts i_std :: interface` is `Interface.const "i_std"` here, and its
`consts i_graph :: interface ⇒ interface` is
`fun i => Interface.app (Interface.const "i_graph") i`. -/
inductive Interface where
  /-- A user-declared interface constant, e.g. `i_std`, `i_nat`. -/
  | const (name : String) : Interface
  /-- Interface application, the value side of the source's `intfAPP`. -/
  | app (f x : Interface) : Interface
deriving DecidableEq, Repr, Inhabited

/-- The source's `intfAPP f x ≡ f x`, the interface-level counterpart of
`Relators.thy`'s `relAPP`. Ported verbatim (the *notation*
`⟨i1,i2⟩⇩i` around it is not — delta T5). Untagged, exactly as in the
source, which gives it no `[simp]`. -/
def intfAPP {β : Sort v} (f : Interface → β) (x : Interface) : β := f x

/-- The source's `consts i_fun :: interface ⇒ interface ⇒ interface`,
the interface of a function. A constructor application here rather than
an uninterpreted constant (delta T2), so it is injective by
construction. -/
def i_fun (i₁ i₂ : Interface) : Interface :=
  .app (.app (.const "i_fun") i₁) i₂

/-- The source's `i_fun_app (infixr "→⇩i" 60)`,
`i1→⇩ii2 ≡ ⟨i1,i2⟩⇩ii_fun`, which unfolds to
`intfAPP (intfAPP i_fun i1) i2`. -/
abbrev i_fun_app (i₁ i₂ : Interface) : Interface := intfAPP (intfAPP i_fun i₁) i₂

@[inherit_doc] infixr:60 " →ᵢ " => i_fun_app

/-- The source's `CONST_INTF :: 'a ⇒ interface ⇒ bool (infixr "::⇩i" 10)`,
`c::⇩i I ≡ True`: "the constant `c` has been declared to have interface
`I`". The proposition carries no information — it is a *declaration*,
read off the shape of the tagged term, which is why the source makes it
`True` and tags it `[simp]`. -/
def CONST_INTF {α : Sort u} (_c : α) (_I : Interface) : Prop := True

@[inherit_doc] infixr:10 " ::ᵢ " => CONST_INTF

/-- The source's `CONST_INTF` definition, with the source's own
`[simp]`. -/
@[simp] theorem CONST_INTF_def {α : Sort u} (c : α) (I : Interface) :
    (c ::ᵢ I) ↔ True := Iff.rfl

/-- The source's `ID_OP`, with its documentation verbatim:

> Predicate for operation identification. `ID_OP t t' I` means that term
> `t` has been annotated as `t'`, and its interface is `I`. -/
def ID_OP {α : Sort u} (t t' : α) (_I : Interface) : Prop := t = t'

/-- The source's `ID_OP` definition, with the source's own `[simp]`. -/
@[simp] theorem ID_OP_def {α : Sort u} (t t' : α) (I : Interface) :
    ID_OP t t' I ↔ t = t' := Iff.rfl

/-! ### The executable gate (design record ledger D4)

The tag layer has no content to refute — every definition here is a
definitional identity, and its unfolding lemma is `rfl`. What *can* go
wrong is the notation: a precedence that parses the wrong tree, or a
token that shadows another. So the gate checks the parse, not the
math — each `example` states the tagged form and the untagged form and
asks `simp` (i.e. the `autoref_tag_defs` set) to identify them, which it
can only do if the tagged form parsed as intended. -/

namespace Sanity

variable {α β γ : Type}

-- `PROTECT`/`OP`/`ANNOT`/`APP` all erase under their own simp set.
example (x : α) : PROTECT x = x := by simp
example (x : α) : OP x = x := by simp
example (x : α) (a : Annot) : ANNOT x a = x := by simp
example (f : α → β) (a : α) : (f $ᵃ a) = f a := by simp

-- `ABS` is two `PROTECT`s deep, and erases to the function itself.
example (f : α → β) : ABS f = f := by simp

-- `$ᵃ` is `infixl 900`, so it binds tighter than everything and
-- associates left: `f $ᵃ a $ᵃ b` is `(f a) b`.
example (f : α → α → β) (a b : α) : (f $ᵃ a $ᵃ b) = f a b := by simp

-- `:::` is `infix 10`, so it binds *looser* than `=` (50): the source's
-- own convention, and the reason every use in the source's rule
-- statements is parenthesised (`(OP hd ::: ⟨R⟩list_rel → R)$l'`).
example (R : Set (γ × α)) (x : α) : (x ::: R) = x := by simp

-- The tagged form of the extract's `autoref_hd` conclusion,
-- `(hd l, (OP hd ::: ⟨R⟩list_rel → R)$l') ∈ R`, parses to the raw
-- application it is meant to protect.
example (R : Set ((List γ → γ) × (List α → α))) (f : List α → α) (l : List α) :
    ((OP f ::: R) $ᵃ l) = f l := by simp

-- `::#` at the same precedence, over a `RelName`.
example (x : α) : (x ::# ⟨"i_map_rel"⟩) = x := by simp

-- `→ᵢ` is `infixr 60`: `i₁ →ᵢ i₂ →ᵢ i₃` is `i₁ →ᵢ (i₂ →ᵢ i₃)`.
#guard (Interface.const "a" →ᵢ Interface.const "b" →ᵢ Interface.const "c")
  == (Interface.const "a" →ᵢ (Interface.const "b" →ᵢ Interface.const "c"))
#guard !((Interface.const "a" →ᵢ Interface.const "b" →ᵢ Interface.const "c")
  == ((Interface.const "a" →ᵢ Interface.const "b") →ᵢ Interface.const "c"))

-- Interfaces are injective markers here, unlike the source's opaque
-- constants (delta T2): distinct interfaces are *decidably* distinct.
#guard !(Interface.const "i_nat" == Interface.const "i_std")
#guard !((Interface.const "i_nat" →ᵢ Interface.const "i_nat") == Interface.const "i_nat")

-- `RelName` likewise.
#guard !(RelName.mk "i_map" == RelName.mk "i_set")

-- `CONST_INTF` is a declaration, not a fact: it holds of everything.
example (x : α) (I : Interface) : x ::ᵢ I := by simp

-- `ID_OP` is equality with an interface riding along.
example (x : α) (I : Interface) : ID_OP x x I := by simp

example (x y : α) (I : Interface) (h : ID_OP x y I) : x = y := by simpa using h

end Sanity

end Lax13Proofs.Refine
