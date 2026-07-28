import Lax3.ColoredGraphs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image

/-!
---
title: Distance logic and distance rank
type: definition
---
Distance logic extends first-order logic by two families of *distance
atoms* — the distance between two variables is at most *r*, and the
distance from a variable to a color class is smaller than *r* — and by
*local quantification*, an existential quantifier that ranges only over
the vertices within a given radius of a recorded set of the variables
in scope. As a logic it
is no stronger than first-order logic: over a fixed signature, "the
distance between *x* and *y* is at most *r*" is already first-order
expressible, and a local quantifier is an ordinary quantifier
conjoined with such a distance test. What the extra syntax buys is a
finer rank measure.

That measure is *distance rank*. A formula has distance rank (*k*, *q*)
when it has at most *k* free variables, quantifier rank at most *q*,
every distance atom in it has radius at most ρ⁻(*k*, *q*), and every
local quantifier in it guards at radius at most ρ⁺(*k*+1, *q*−1), where
ρ⁻ and ρ⁺ are the two *horizon functions*. The two functions decrease
fast enough as one traverses the quantifiers of a formula inwards that
the radii do too: the region a subformula can see shrinks strictly at
every quantifier. This is exactly the control the locality theorem of
`Lax3.Locality` needs — it rewrites a formula of distance rank (*k*,
*q*) into a boolean combination of *local* formulas and scatter
sentences of the *same* distance rank, which ordinary quantifier rank
could not express.

This is the logic distFO of the source note (arXiv:2606.23180, §2.1),
interpreted over the finite colored graphs of `Lax3.ColoredGraphs` —
see the discussion there for what fixing the signature does and does
not cost. Its distance is the walk distance of that file, which for a
colored graph is the distance in its Gaifman graph.

A formula is *local* when it never uses unrestricted quantification.
Semantic locality is the corresponding property of meaning rather than
of shape: a formula is semantically *r*-local when its truth on a tuple
is unchanged by discarding every vertex further than *r* from that
tuple.

# Formalization notes

The horizon functions are the source's concrete pair, ρ⁻(*k*, *q*) =
9^((*k*+*q*+1)*q*) and ρ⁺(*k*, *q*) = 9^((*k*+*q*)(*q*+1)), rather than
an arbitrary pair satisfying the source's inequalities (1). The
statements on this surface are then about a definite logic with
definite radii and can be read without carrying a parameter through
every one of them. The proofs behind those statements use nothing about
the pair beyond the two inequalities of (1), and are written against an
abstract bundle of them; that bundle is an implementation detail and is
not part of the concept surface.

The distance rank is a *predicate* on formulas, not a second type
index. Its rank argument is independent of the type index: `DRank k' q
φ` may be asserted of a `φ : DistFO L k` for any `k' ` — the source's
"at most *k* free variables" is `k ≤ k'`, and demanding equality would
force a reindexing of the syntax at every step of every proof, for no
gain. The source's Observations 4 and 6, which say that rank is
preserved along the schedule, become monotonicity lemmas of this
predicate.

**Deviation, deliberate: the local guard radius is bounded, not
pinned.** The source's grammar admits the local quantifier only at the
exact radius ρ⁺(*k*+1, *q*−1); here `DRank` requires `r ≤ ρ⁺(k'+1, q)`
at rank (`k'`, `q`+1). The source's own Observation 4 — every formula
of distance rank (*k*+1, *q*−1) with at most *k* free variables also
has distance rank (*k*, *q*) — is false for the exact reading as
stated: a local quantifier of a (*k*+1, *q*−1)-formula guards at
ρ⁺(*k*+2, *q*−2), which is not the radius ρ⁺(*k*+1, *q*−1) that a
(*k*, *q*)-formula is allowed. The source absorbs the mismatch
silently, by reading a guarded quantifier as an unrestricted quantifier
over a conjunction with binary distance atoms — a rewriting, not an
identity of formulas. With the bound in place the observation is a
plain monotonicity lemma about `DRank`, proved where it is used and not
here. The relaxation only adds sound inputs: a smaller guard radius
means the quantifier ranges over fewer vertices, so every syntactic
bound the locality proof draws from a guard still holds.

Satisfaction is total, environments are `Fin k → Fin n`, and binders
extend the environment at the last position; see `Lax3.FirstOrder` for
that discussion, which applies verbatim.

The guard of a local quantifier carries its variable set in the
syntax: `exL r g φ` ranges over the vertices within distance *r* of
the variables in the finite set `g`. This is the source's guard
dist(x̄, *y*) ≤ *r* = ⋁_{x ∈ x̄} dist(*x*, *y*) ≤ *r* read as the
source writes it: the set x̄ is chosen when the formula is formed
("we write φ(x̄) to indicate that x̄ *contains* the free variables of
φ") and does not change when the formula later occurs inside a larger
one. Recording the set is what makes that stability true here as
well — placing a one-variable formula at a bound variable of a wider
formula, as the locality theorem's proof and the normal form's
written-out scatter sentences both do, keeps its guards reading that
one variable, and renaming is sound with no side conditions because
the guard set travels along. A guard over everything in scope is the
special case `g = univ`; the earlier revision of this file had only
that case, which widens a formula's guards whenever the context
grows, and under which the placement just described is unsound. With
`g = ∅` the guard is an empty disjunction, so the quantifier is
vacuously false — in particular a local quantifier over a sentence's
empty context has no vertex to be local to, and the locality
theorem's sentence case produces scatter sentences precisely because
local quantification cannot help there.

The unary distance atom is strict, dist(*x*, *Y*) < *r*, as in the
source; the binary one is not. The asymmetry is the source's and is
kept — a translation that quietly aligned them would make the
statements here no longer the statements of the source note. Unary
distance atoms are carried at all only for faithfulness: the algorithm
never manufactures one, and its formulas stay in the fragment without
them.

`SatWithin` is the source's relativization *A*[*N_r*(ā)] ⊨ φ(ā),
written with the carrier kept: the induced substructure lives on the
same vertex type `Fin n`, and the restriction to `D` is imposed by the
definition instead of by a subtype. That matches the uniform vertex
numbering every structure of this submission carries, and matches
Lax12's `deleteVerts`, which also isolates rather than removes. Inside
`D` the atoms are the induced ones: an edge survives only if both its
endpoints do, a color class is intersected with `D`, and a distance
atom measures along walks that stay in `D`. Satisfaction and
relativization to the full vertex set agree, but `SatWithin univ` is
*not* how `Sat` is defined — the agreement is a lemma, proved where the
two are compared, so that each definition can be read and audited on
its own.

`rename` is here because the sentences of `Lax3.Locality` need to place
a one-variable formula at each of several bound variables. It is a
definition only; the lemmas relating it to satisfaction belong with the
proofs that use them.
-/

namespace Lax3.DistFO

open Lax3.ColoredGraphs

/-- The lower horizon function ρ⁻ of the source: the largest radius a
distance atom of distance rank `(k, q)` may carry. -/
def rhoMinus (k q : ℕ) : ℕ := 9 ^ ((k + q + 1) * q)

/-- The upper horizon function ρ⁺ of the source: the largest radius a
local quantifier may guard at, one rank level in. -/
def rhoPlus (k q : ℕ) : ℕ := 9 ^ ((k + q) * (q + 1))

-- the logic and the module carrying it have the same name on purpose
set_option linter.dupNamespace false in
/-- Formulas of distance logic over `L`-colored graphs, with `k` free
variables. Variables are `Fin k`, and both quantifiers bind the *new
last* index. Beyond the atoms of first-order logic there are colors and
the two distance atoms, and beyond unrestricted quantification there is
local quantification, which ranges over the vertices within a given
radius of the free variables. -/
inductive DistFO (L : ℕ) : ℕ → Type
  /-- The vertices `i` and `j` are adjacent. -/
  | adj {k : ℕ} (i j : Fin k) : DistFO L k
  /-- The vertices `i` and `j` are equal. -/
  | eq {k : ℕ} (i j : Fin k) : DistFO L k
  /-- The vertex `i` has color `c`. -/
  | color {k : ℕ} (c : Fin L) (i : Fin k) : DistFO L k
  /-- Binary distance atom: the distance between `i` and `j` is at most
  `r`. -/
  | distLe {k : ℕ} (r : ℕ) (i j : Fin k) : DistFO L k
  /-- Unary distance atom: the distance from `i` to the color class `c`
  is smaller than `r`. -/
  | distColorLt {k : ℕ} (r : ℕ) (c : Fin L) (i : Fin k) : DistFO L k
  /-- Negation. -/
  | not {k : ℕ} (φ : DistFO L k) : DistFO L k
  /-- Conjunction. -/
  | and {k : ℕ} (φ ψ : DistFO L k) : DistFO L k
  /-- Unrestricted quantification: there is a vertex satisfying `φ`,
  bound at the last index. -/
  | exU {k : ℕ} (φ : DistFO L (k + 1)) : DistFO L k
  /-- Local quantification: there is a vertex within distance `r` of
  some variable in the guard set `g` satisfying `φ`, bound at the last
  index. The radius and the guard set are part of the syntax; which
  radii are admissible at a given distance rank is the business of
  `DRank`, and the guard set is unconstrained there, as in the
  source. -/
  | exL {k : ℕ} (r : ℕ) (g : Finset (Fin k)) (φ : DistFO L (k + 1)) : DistFO L k

variable {L n : ℕ}

/-- Satisfaction of a formula in the `L`-colored graph `(G, col)` under
the environment `m`. A binary distance atom is a walk-length bound, a
unary one asks for a color-class vertex strictly nearer than `r`, and a
local quantifier ranges over the vertices within `r` of some variable
in its guard set — an empty condition, hence unsatisfiable, when the
set is empty. -/
def Sat (G : SimpleGraph (Fin n)) (col : Coloring n L) :
    {k : ℕ} → (Fin k → Fin n) → DistFO L k → Prop
  | _, m, .adj i j => G.Adj (m i) (m j)
  | _, m, .eq i j => m i = m j
  | _, m, .color c i => m i ∈ col c
  | _, m, .distLe r i j => WithinDist G r (m i) (m j)
  | _, m, .distColorLt r c i => ∃ y ∈ col c, ∃ w : G.Walk (m i) y, w.length < r
  | _, m, .not φ => ¬ Sat G col m φ
  | _, m, .and φ ψ => Sat G col m φ ∧ Sat G col m ψ
  | _, m, .exU φ => ∃ v : Fin n, Sat G col (Fin.snoc m v) φ
  | _, m, .exL r g φ =>
      ∃ v : Fin n, (∃ i ∈ g, WithinDist G r (m i) v) ∧ Sat G col (Fin.snoc m v) φ

/-- Renaming of variables along `f`. Under a binder the renaming is
lifted to `Fin (k + 1) → Fin (k' + 1)` by sending the bound variable —
the last index — to the new last index. The guard set of a local
quantifier is mapped along `f`, so a guard keeps naming the same
variables it named before. -/
def rename : {k k' : ℕ} → (Fin k → Fin k') → DistFO L k → DistFO L k'
  | _, _, f, .adj i j => .adj (f i) (f j)
  | _, _, f, .eq i j => .eq (f i) (f j)
  | _, _, f, .color c i => .color c (f i)
  | _, _, f, .distLe r i j => .distLe r (f i) (f j)
  | _, _, f, .distColorLt r c i => .distColorLt r c (f i)
  | _, _, f, .not φ => .not (rename f φ)
  | _, _, f, .and φ ψ => .and (rename f φ) (rename f ψ)
  | _, k', f, .exU φ => .exU (rename (Fin.snoc (fun i => (f i).castSucc) (Fin.last k')) φ)
  | _, k', f, .exL r g φ =>
      .exL r (g.image f) (rename (Fin.snoc (fun i => (f i).castSucc) (Fin.last k')) φ)

/-- `DRank k' q φ` says that `φ` has distance rank `(k', q)`: its
quantifier rank is at most `q`, every distance atom in it has radius at
most `ρ⁻` of the rank in force there, and every local quantifier guards
at radius at most `ρ⁺` of the rank one level in. The rank argument
`k'` is a bound on the number of free variables and is independent of
the type index. -/
inductive DRank {L : ℕ} : ℕ → ℕ → {k : ℕ} → DistFO L k → Prop
  /-- An adjacency atom has every distance rank. -/
  | adj {k' q k : ℕ} (i j : Fin k) : DRank k' q (.adj i j)
  /-- An equality atom has every distance rank. -/
  | eq {k' q k : ℕ} (i j : Fin k) : DRank k' q (.eq i j)
  /-- A color atom has every distance rank. -/
  | color {k' q k : ℕ} (c : Fin L) (i : Fin k) : DRank k' q (.color c i)
  /-- A binary distance atom has distance rank `(k', q)` when its
  radius is at most `ρ⁻(k', q)`. -/
  | distLe {k' q k : ℕ} {r : ℕ} (i j : Fin k) (hr : r ≤ rhoMinus k' q) :
      DRank k' q (.distLe r i j)
  /-- A unary distance atom has distance rank `(k', q)` when its radius
  is at most `ρ⁻(k', q)`. -/
  | distColorLt {k' q k : ℕ} {r : ℕ} (c : Fin L) (i : Fin k) (hr : r ≤ rhoMinus k' q) :
      DRank k' q (.distColorLt r c i)
  /-- Negation preserves the distance rank. -/
  | not {k' q k : ℕ} {φ : DistFO L k} (h : DRank k' q φ) : DRank k' q (.not φ)
  /-- Conjunction preserves the distance rank. -/
  | and {k' q k : ℕ} {φ ψ : DistFO L k} (h : DRank k' q φ) (h' : DRank k' q ψ) :
      DRank k' q (.and φ ψ)
  /-- An unrestricted quantifier has distance rank `(k', q + 1)` when
  its body has distance rank `(k' + 1, q)`. -/
  | exU {k' q k : ℕ} {φ : DistFO L (k + 1)} (h : DRank (k' + 1) q φ) :
      DRank k' (q + 1) (.exU φ)
  /-- A local quantifier has distance rank `(k', q + 1)` when its body
  has distance rank `(k' + 1, q)` and it guards at radius at most
  `ρ⁺(k' + 1, q)`. The guard set is unconstrained. -/
  | exL {k' q k : ℕ} {r : ℕ} {g : Finset (Fin k)} {φ : DistFO L (k + 1)}
      (h : DRank (k' + 1) q φ) (hr : r ≤ rhoPlus (k' + 1) q) : DRank k' (q + 1) (.exL r g φ)

/-- A formula is local when it uses no unrestricted quantification. -/
def IsLocal : {k : ℕ} → DistFO L k → Prop
  | _, .adj _ _ => True
  | _, .eq _ _ => True
  | _, .color _ _ => True
  | _, .distLe _ _ _ => True
  | _, .distColorLt _ _ _ => True
  | _, .not φ => IsLocal φ
  | _, .and φ ψ => IsLocal φ ∧ IsLocal ψ
  | _, .exU _ => False
  | _, .exL _ _ φ => IsLocal φ

/-- The vertices `u` and `v` are within distance `d` *inside* `D`: some
walk from `u` to `v` has length at most `d` and stays in `D`. This is
the walk distance of the substructure induced on `D`, with the carrier
kept. -/
def WithinDistIn {V : Type*} (D : Set V) (G : SimpleGraph V) (d : ℕ) (u v : V) : Prop :=
  ∃ w : G.Walk u v, w.length ≤ d ∧ ∀ x ∈ w.support, x ∈ D

/-- Satisfaction in the substructure induced on `D`, with the carrier
kept: quantifiers range over `D`, an edge counts only if both endpoints
lie in `D`, color classes are intersected with `D`, and distances are
measured along walks inside `D`. -/
def SatWithin (D : Set (Fin n)) (G : SimpleGraph (Fin n)) (col : Coloring n L) :
    {k : ℕ} → (Fin k → Fin n) → DistFO L k → Prop
  | _, m, .adj i j => G.Adj (m i) (m j) ∧ m i ∈ D ∧ m j ∈ D
  | _, m, .eq i j => m i = m j
  | _, m, .color c i => m i ∈ col c ∧ m i ∈ D
  | _, m, .distLe r i j => WithinDistIn D G r (m i) (m j)
  | _, m, .distColorLt r c i =>
      ∃ y, y ∈ col c ∧ y ∈ D ∧ ∃ w : G.Walk (m i) y, w.length < r ∧ ∀ x ∈ w.support, x ∈ D
  | _, m, .not φ => ¬ SatWithin D G col m φ
  | _, m, .and φ ψ => SatWithin D G col m φ ∧ SatWithin D G col m ψ
  | _, m, .exU φ => ∃ v ∈ D, SatWithin D G col (Fin.snoc m v) φ
  | _, m, .exL r g φ =>
      ∃ v ∈ D, (∃ i ∈ g, WithinDistIn D G r (m i) v) ∧ SatWithin D G col (Fin.snoc m v) φ

/-- A formula is semantically `r`-local when its truth on a tuple never
depends on the vertices further than `r` from that tuple: satisfaction
in the graph and satisfaction in the substructure induced on the union
of the `r`-balls around the tuple agree, in every colored graph and at
every tuple. -/
def SemanticallyLocal (r : ℕ) {k : ℕ} (φ : DistFO L k) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
    Sat G col m φ ↔ SatWithin (⋃ i, ball G r (m i)) G col m φ

end Lax3.DistFO
