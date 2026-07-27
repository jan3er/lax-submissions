import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic

/-!
The type algebra: the finitely many *q-types* of a boundaried subset of
a graph, and the type of a given subset.

This is the engine of Courcelle's theorem, and it replaces tree automata
and Hintikka normal forms both. The types of rank `q` on `r` marked
vertices and `s` set variables are defined by recursion on `q`: a
rank-`0` type is the atomic diagram of the marks, and a rank-`q+1` type
is that diagram together with the *set of* rank-`q` types reachable by
one vertex move and the set reachable by one set move. A formula of rank
at most `q` will be shown (next milestone) to depend on nothing else,
and the family is finite, so the finiteness that a linear-time table
needs is a two-line induction rather than a syntactic normal form.

Three decisions shape the file.

*The ambient-subset formulation.* Structures are never glued. A graph
`G : SimpleGraph (Fin n)` is fixed once and for all, and a boundaried
structure is a *subset* `X : Set (Fin n)` of it, with marks
`m : Fin r → Fin n` (in `X`, where it matters) and a set assignment
`A : Fin s → Set (Fin n)`. Gluing is then literally `X ∪ Y` in the same
ambient graph, under the hypotheses that `X ∩ Y` is marked and that `G`
has no edge between `X \ Y` and `Y \ X`. So there are no pushouts, no
quotients and no isomorphism invariance anywhere: `T` is pure data,
defined without reference to any graph, and every statement about `typ`
is per-ambient. Deviating from this is what makes the composition lemma
a research project instead of an induction.

*Sets of types are characteristic functions into `Bool`.* The recursion
would like to say `Finset (T q (r+1) s)`, but a `Finset` needs a
`DecidableEq` instance for a type that the same recursion is still
defining. Functions into `Bool` carry the same data and need nothing:
`Fintype` and `DecidableEq` for `T q r s` then follow by one induction
on `q`, computably, which is why the cardinalities below can be
`#eval`ed. The instances are produced together, bundled in `FinDec`,
because each step needs both of them at the level below.

*`typ` is noncomputable, on purpose.* Its two move components ask
whether some vertex of `X`, or some subset of `X`, has a given type;
these are classical existentials and are not decided here. Nothing
downstream needs `typ` to compute — the table of the eventual program is
finite data extracted from a `Fintype`, and the program is generated
from that data (plan decision C5). Only `T` itself, and its instances,
stay computable.

What is *not* here: the MSO syntax and its semantics, adequacy, the mark
lemmas, and composition. The idiom those will use is worth naming now,
though, because it is what the definitions are shaped for: every theorem
about types is a *congruence* — "if two boundaried subsets have the same
type then ⟨something⟩ agrees on them" — never the construction of a
function on types. The function (the table) comes at the end, from
`Fintype` and choice.
-/

namespace Lax11Proofs.MsoTypes

/-! ### The atomic diagram

Rank `0` is the quantifier-free information about the marks: which pairs
are adjacent, which pairs are equal, and which mark lies in which set of
the assignment. MSO₁ has exactly these three atoms (plan decision C1),
so this is the whole atomic layer, and the only place an MSO₂ variant
would ever touch. -/

/-- The atomic diagram of `r` marked vertices against `s` set variables:
the adjacency, equality and membership patterns. -/
@[ext]
structure Atomic (r s : ℕ) where
  /-- Which marks are adjacent in the ambient graph. -/
  adj : Fin r → Fin r → Bool
  /-- Which marks are the same vertex. -/
  eq : Fin r → Fin r → Bool
  /-- Which mark lies in which set of the assignment. -/
  mem : Fin r → Fin s → Bool
  deriving DecidableEq, Fintype

/-! ### The types of rank `q`

`T q r s` is defined by recursion on `q` alone; the mark and set counts
move (a vertex move increases `r`, a set move increases `s`), which is
why they are arguments of the recursion rather than parameters. -/

/-- The `q`-types on `r` marks and `s` set variables: an atomic diagram
at rank `0`, and at rank `q+1` a diagram together with the set of
rank-`q` types obtained by marking one more vertex and the set obtained
by naming one more set — both as characteristic functions. -/
def T : ℕ → ℕ → ℕ → Type
  | 0, r, s => Atomic r s
  | q + 1, r, s => Atomic r s × (T q (r + 1) s → Bool) × (T q r (s + 1) → Bool)

/-- `T (q+1) r s` spelled out. Only used to make type ascriptions
readable; it is reducibly the same type. -/
abbrev Layer (q r s : ℕ) : Type :=
  Atomic r s × (T q (r + 1) s → Bool) × (T q r (s + 1) → Bool)

theorem T_zero (r s : ℕ) : T 0 r s = Atomic r s := rfl

theorem T_succ (q r s : ℕ) : T (q + 1) r s = Layer q r s := rfl

/-! #### Finiteness

The two instances are built in one recursion, because the step needs
`Fintype` *and* `DecidableEq` one rank down — the first to enumerate the
characteristic functions, the second to compare them. -/

/-- A carrier's two instances, bundled so that one recursion produces
both. -/
structure FinDec (α : Type) where
  /-- The carrier is finite. -/
  fintype : Fintype α
  /-- Equality on the carrier is decidable. -/
  decEq : DecidableEq α

/-- One step of the instance recursion: from the instances of the two
lower type sets, the instances of a layer over them. -/
def FinDec.layer {α β : Type} (r s : ℕ) (a : FinDec α) (b : FinDec β) :
    FinDec (Atomic r s × (α → Bool) × (β → Bool)) := by
  letI := a.fintype; letI := a.decEq; letI := b.fintype; letI := b.decEq
  exact ⟨inferInstance, inferInstance⟩

/-- Every `T q r s` is a finite type with decidable equality. -/
def finDec : (q r s : ℕ) → FinDec (T q r s)
  | 0, r, s => (⟨inferInstance, inferInstance⟩ : FinDec (Atomic r s))
  | q + 1, r, s => FinDec.layer r s (finDec q (r + 1) s) (finDec q r (s + 1))

instance instFintypeT (q r s : ℕ) : Fintype (T q r s) := (finDec q r s).fintype

instance instDecidableEqT (q r s : ℕ) : DecidableEq (T q r s) := (finDec q r s).decEq

/-! #### Constructor and projections

`T` is a `def`, not a structure, so the layer's three components get
names by hand. Everything below goes through these, never through
`Prod.fst`. -/

/-- The type of rank `q+1` with the given diagram and move sets. -/
def T.mk {q r s : ℕ} (a : Atomic r s) (v : T q (r + 1) s → Bool)
    (w : T q r (s + 1) → Bool) : T (q + 1) r s := (a, v, w)

/-- The atomic diagram inside a type of any rank. -/
def T.diagram : {q r s : ℕ} → T q r s → Atomic r s
  | 0, _, _, t => t
  | _ + 1, _, _, t => (t : Layer _ _ _).1

/-- The rank-`q` types reachable from a rank-`q+1` type by marking one
more vertex. -/
def T.vMoves {q r s : ℕ} (t : T (q + 1) r s) : T q (r + 1) s → Bool :=
  (t : Layer q r s).2.1

/-- The rank-`q` types reachable from a rank-`q+1` type by naming one
more set. -/
def T.sMoves {q r s : ℕ} (t : T (q + 1) r s) : T q r (s + 1) → Bool :=
  (t : Layer q r s).2.2

@[simp] theorem T.diagram_mk {q r s : ℕ} (a : Atomic r s) (v : T q (r + 1) s → Bool)
    (w : T q r (s + 1) → Bool) : (T.mk a v w).diagram = a := rfl

@[simp] theorem T.vMoves_mk {q r s : ℕ} (a : Atomic r s) (v : T q (r + 1) s → Bool)
    (w : T q r (s + 1) → Bool) : (T.mk a v w).vMoves = v := rfl

@[simp] theorem T.sMoves_mk {q r s : ℕ} (a : Atomic r s) (v : T q (r + 1) s → Bool)
    (w : T q r (s + 1) → Bool) : (T.mk a v w).sMoves = w := rfl

/-- A type of rank `q+1` is its diagram together with its two move
sets. -/
@[ext]
theorem T.ext {q r s : ℕ} {t u : T (q + 1) r s} (hd : t.diagram = u.diagram)
    (hv : t.vMoves = u.vMoves) (hs : t.sMoves = u.sMoves) : t = u :=
  Prod.ext hd (Prod.ext hv hs)

/-! #### Cardinalities

Sanity only: the instances are computable, so tiny cardinalities can be
checked against the recursion by hand. `T 0 r s` has `2^(2r² + rs)`
elements, and `T 1 0 0` has `1 · 2^(card (T 0 1 0)) · 2^(card (T 0 0 1))
= 2^4 · 2^1 = 32`. Nothing anywhere needs these numbers — only
finiteness is ever used. -/

#guard Fintype.card (Atomic 1 1) = 8
#guard Fintype.card (T 0 1 1) = 8
#guard Fintype.card (T 0 2 1) = 1024
#guard Fintype.card (T 0 1 0) = 4
#guard Fintype.card (T 0 0 1) = 1
#guard Fintype.card (T 1 0 0) = 32

/-! ### The type of a boundaried subset

Fix the ambient graph. A boundaried subset is `X` with marks `m` and a
set assignment `A`; its `q`-type is read off by the recursion, with the
vertex move ranging over `X` and the set move over the subsets of `X`.
New marks and new sets are appended at the *end* (`Fin.snoc`), which is
the convention the composition lemma's concatenated mark tuples want. -/

variable {n : ℕ}

open Classical in
/-- The atomic diagram of marks `m` and set assignment `A` in `G`. -/
noncomputable def Atomic.of (G : SimpleGraph (Fin n)) {r s : ℕ} (m : Fin r → Fin n)
    (A : Fin s → Set (Fin n)) : Atomic r s where
  adj i j := decide (G.Adj (m i) (m j))
  eq i j := decide (m i = m j)
  mem i j := decide (m i ∈ A j)

open Classical in
/-- The `q`-type of the subset `X` of `G` with marks `m` and set
assignment `A`. Noncomputable by design (plan decision C5): the two
move components are classical existentials. -/
noncomputable def typ (G : SimpleGraph (Fin n)) (X : Set (Fin n)) :
    (q : ℕ) → {r s : ℕ} → (Fin r → Fin n) → (Fin s → Set (Fin n)) → T q r s
  | 0, _, _, m, A => Atomic.of G m A
  | q + 1, _, _, m, A =>
      T.mk (Atomic.of G m A)
        (fun t => decide (∃ v ∈ X, typ G X q (Fin.snoc m v) A = t))
        (fun t => decide (∃ S ⊆ X, typ G X q m (Fin.snoc A S) = t))

variable {G : SimpleGraph (Fin n)} {X : Set (Fin n)} {q r s : ℕ}
  {m : Fin r → Fin n} {A : Fin s → Set (Fin n)}

@[simp] theorem Atomic.of_adj (i j : Fin r) :
    (Atomic.of G m A).adj i j = true ↔ G.Adj (m i) (m j) := by
  simp [Atomic.of]

@[simp] theorem Atomic.of_eq (i j : Fin r) :
    (Atomic.of G m A).eq i j = true ↔ m i = m j := by
  simp [Atomic.of]

@[simp] theorem Atomic.of_mem (i : Fin r) (j : Fin s) :
    (Atomic.of G m A).mem i j = true ↔ m i ∈ A j := by
  simp [Atomic.of]

theorem typ_zero (G : SimpleGraph (Fin n)) (X : Set (Fin n)) (m : Fin r → Fin n)
    (A : Fin s → Set (Fin n)) : typ G X 0 m A = Atomic.of G m A := rfl

/-- The diagram of a type is the diagram of the structure, at every
rank. -/
@[simp] theorem diagram_typ : (typ G X q m A).diagram = Atomic.of G m A := by
  cases q with
  | zero => rfl
  | succ q => rfl

/-- A rank-`q` type is a vertex move of `typ G X (q+1) m A` exactly when
some vertex of `X`, marked last, realizes it. -/
@[simp] theorem vMoves_typ (t : T q (r + 1) s) :
    (typ G X (q + 1) m A).vMoves t = true ↔
      ∃ v ∈ X, typ G X q (Fin.snoc m v) A = t := by
  simp [typ]

/-- A rank-`q` type is a set move of `typ G X (q+1) m A` exactly when
some subset of `X`, named last, realizes it. -/
@[simp] theorem sMoves_typ (t : T q r (s + 1)) :
    (typ G X (q + 1) m A).sMoves t = true ↔
      ∃ S ⊆ X, typ G X q m (Fin.snoc A S) = t := by
  simp [typ]

/-- Marking a vertex of `X` realizes a vertex move: the witness
direction of `vMoves_typ`, which is the half every adequacy proof
uses. -/
theorem vMoves_typ_snoc {v : Fin n} (hv : v ∈ X) :
    (typ G X (q + 1) m A).vMoves (typ G X q (Fin.snoc m v) A) = true :=
  vMoves_typ _ |>.mpr ⟨v, hv, rfl⟩

/-- Naming a subset of `X` realizes a set move. -/
theorem sMoves_typ_snoc {S : Set (Fin n)} (hS : S ⊆ X) :
    (typ G X (q + 1) m A).sMoves (typ G X q m (Fin.snoc A S)) = true :=
  sMoves_typ _ |>.mpr ⟨S, hS, rfl⟩

/-- An empty region has no vertex moves. There is always the set move
`∅`, so `sMoves` is never empty — a rank-`q+1` type is not a type of a
structure unless its set moves are nonempty. -/
theorem vMoves_typ_empty (t : T q (r + 1) s) :
    (typ G ∅ (q + 1) m A).vMoves t = false := by
  simp [Bool.eq_false_iff]

/-- Smoke test: ambient adjacency really does reach the diagram. On the
complete graph on two vertices, the two marks are adjacent and
distinct. -/
example (A : Fin 0 → Set (Fin 2)) :
    (Atomic.of (⊤ : SimpleGraph (Fin 2)) (fun i : Fin 2 => i) A).adj 0 1 = true ∧
      (Atomic.of (⊤ : SimpleGraph (Fin 2)) (fun i : Fin 2 => i) A).eq 0 1 = false := by
  refine ⟨by simp, ?_⟩
  simp [Bool.eq_false_iff]

/-! ### The assignment matters only inside the region

The first induction on `q`, and the first one that the composition lemma
will consume: the type of `X` does not see the part of the assignment
that lies outside `X`. This is what lets a set move in a union be split
as `S ↦ (S ∩ X, S ∩ Y)` — the two halves are then honest assignments for
the two sides, and the sides cannot tell them apart from `S`. -/

theorem Atomic.of_congr_inter (G : SimpleGraph (Fin n)) (X : Set (Fin n))
    (m : Fin r → Fin n) (A A' : Fin s → Set (Fin n)) (hm : ∀ i, m i ∈ X)
    (hA : ∀ j, A j ∩ X = A' j ∩ X) : Atomic.of G m A = Atomic.of G m A' := by
  refine Atomic.ext rfl rfl (funext fun i => funext fun j => ?_)
  have h := Set.ext_iff.mp (hA j) (m i)
  simp only [Set.mem_inter_iff, and_iff_left (hm i)] at h
  simp [Atomic.of, h]

/-- Two assignments that agree inside `X` give the marked subset `X` the
same type, at every rank. -/
theorem typ_congr_inter (G : SimpleGraph (Fin n)) (X : Set (Fin n)) :
    ∀ (q : ℕ) {r s : ℕ} (m : Fin r → Fin n) (A A' : Fin s → Set (Fin n)),
      (∀ i, m i ∈ X) → (∀ j, A j ∩ X = A' j ∩ X) →
      typ G X q m A = typ G X q m A' := by
  intro q
  induction q with
  | zero => intro r s m A A' hm hA; exact Atomic.of_congr_inter G X m A A' hm hA
  | succ q ih =>
      intro r s m A A' hm hA
      refine T.ext ?_ (funext fun t => ?_) (funext fun t => ?_)
      · simpa using Atomic.of_congr_inter G X m A A' hm hA
      · refine Bool.eq_iff_iff.mpr ?_
        simp only [vMoves_typ]
        refine exists_congr fun v => and_congr_right fun hv => ?_
        rw [ih (Fin.snoc m v) A A' (fun i => Fin.lastCases (by simpa using hv)
          (fun i => by simpa using hm i) i) hA]
      · refine Bool.eq_iff_iff.mpr ?_
        simp only [sMoves_typ]
        refine exists_congr fun S => and_congr_right fun hS => ?_
        refine iff_of_eq (congrArg (· = t) ?_)
        refine ih m (Fin.snoc A S) (Fin.snoc A' S) hm fun j => ?_
        refine Fin.lastCases (by simp) (fun j => by simpa using hA j) j

end Lax11Proofs.MsoTypes
