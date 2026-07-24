import Mathlib.ModelTheory.Semantics
import Mathlib.Logic.Embedding.Basic

/-!
---
title: First-order transductions
type: definition
---
A (non-copying) first-order transduction from structures of a language
*L* to structures of a relational language *L'* consists of a number *k*
of unary *color* predicates, a *domain* formula, and one formula per
relation symbol of *L'*, all over *L* expanded by the colors. Applied to
an *L*-structure together with an arbitrary coloring of its elements,
the transduction outputs the *L'*-structure whose universe is the set of
elements satisfying the domain formula and whose relations are defined
by the interpreting formulas.

A class *C* of structures transduces a class *D* if a single
transduction produces every member of *D*, up to isomorphism, from some
colored member of *C*.

# Formalization notes

Languages, formulas and semantics are mathlib's: a formula with `r` free
variables is a `Formula (Fin r)`, realized via `Formula.Realize`. The
color expansion is the sum of `L` with a language of `k` unary relation
symbols; `RealizeIn` confines the instance plumbing (mathlib treats
structures as instances, this submission treats them as data) to a
single definition.

In `Transduces`, the embedding `f` carries the isomorphism: its range
must be exactly the set defined by the domain formula, and each target
relation must be defined by its interpreting formula. The target
language is required to be relational because a transduction interprets
relations only; function symbols on the target side would be silently
unconstrained. Since colorings are existentially quantified, taking an
*arbitrary* induced substructure instead of a definable one yields the
same transduces relation — a fresh color can serve as the domain
formula. Only non-copying transductions are defined; the results of this
submission need nothing more.
-/

namespace Lax5.Transductions

open FirstOrder

universe u v u' v'

/-- A class of finite structures of the language `L`: for each `n`, a
predicate on the `L`-structures over the canonical `n`-element type. -/
abbrev StructureClass (L : Language.{u, v}) : Type (max u v) :=
  ∀ n : ℕ, L.Structure (Fin n) → Prop

/-- The relation symbols of the color language: `k` unary predicates. -/
inductive ColorRel (k : ℕ) : ℕ → Type
  | color (i : Fin k) : ColorRel k 1

/-- The language consisting of `k` unary color predicates and nothing
else. -/
def colorLanguage (k : ℕ) : Language :=
  ⟨fun _ => Empty, ColorRel k⟩
  deriving Language.IsRelational

/-- The language `L` expanded by `k` unary color predicates. -/
abbrev withColors (L : Language.{u, v}) (k : ℕ) : Language :=
  L.sum (colorLanguage k)

/-- The color sets `colors` as a structure of the color language:
`.color i` holds of the elements of `colors i`. -/
@[implicit_reducible]
def colorStructure {M : Type*} {k : ℕ} (colors : Fin k → Set M) :
    (colorLanguage k).Structure M where
  RelMap | .color i => fun x => x 0 ∈ colors i

/-- The formula `φ` of the colored language holds of the tuple `v` in
the `L`-structure `M` expanded by the color sets `colors`. -/
def RealizeIn {L : Language.{u, v}} {n k : ℕ} (M : L.Structure (Fin n))
    (colors : Fin k → Set (Fin n)) {α : Type*}
    (φ : (withColors L k).Formula α) (v : α → Fin n) : Prop :=
  letI := M
  letI := colorStructure colors
  φ.Realize v

/-- A non-copying transduction from `L`-structures to `L'`-structures:
finitely many unary colors, a domain formula selecting the output
universe, and one formula per relation symbol of the target language. -/
structure Transduction (L : Language.{u, v}) (L' : Language.{u', v'}) where
  /-- The number of unary color predicates. -/
  colors : ℕ
  /-- The formula selecting the elements of the output structure. -/
  domain : (withColors L colors).Formula (Fin 1)
  /-- The formula interpreting each relation symbol of the target. -/
  rel : ∀ {r : ℕ}, L'.Relations r → (withColors L colors).Formula (Fin r)

/-- `C` transduces `D`: a single transduction produces every member of
`D` from some colored member of `C`, up to isomorphism — the embedding
`f` identifies the output structure with the substructure of elements
selected by the domain formula. -/
def Transduces {L : Language.{u, v}} {L' : Language.{u', v'}}
    [L'.IsRelational] (C : StructureClass L) (D : StructureClass L') :
    Prop :=
  ∃ T : Transduction L L',
    ∀ (m : ℕ) (N : L'.Structure (Fin m)), D m N →
      ∃ (n : ℕ) (M : L.Structure (Fin n)), C n M ∧
        ∃ (colors : Fin T.colors → Set (Fin n)) (f : Fin m ↪ Fin n),
          (∀ x : Fin n,
            x ∈ Set.range f ↔ RealizeIn M colors T.domain ![x]) ∧
          ∀ {r : ℕ} (R : L'.Relations r) (v : Fin r → Fin m),
            N.RelMap R v ↔ RealizeIn M colors (T.rel R) (f ∘ v)

end Lax5.Transductions
