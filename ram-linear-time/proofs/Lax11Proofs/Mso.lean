import Lax11Proofs.MsoTypes

/-!
Monadic second-order logic on graphs: the syntax, and the semantics that
is the new trust object.

This is the *draft* of what plan step 5 will copy out to the endorsement
surface verbatim, so it is written to be read: seven constructors and a
fifteen-line recursion, and nothing else. Everything that a formalization
of MSO usually drags along — substitution, capture avoidance, a `Closed`
predicate, well-formedness side conditions — is absent by construction.

*Well-scoped de Bruijn* (plan decision C2). `MSO r s` is the type of
formulas with `r` free vertex variables and `s` free set variables, so
`Sat` is total over a pair of environments `Fin r → Fin n` and
`Fin s → Set (Fin n)`: there is no partial valuation, no default value,
and no junk to audit. The indices are the same `r` and `s` that index the
type algebra's `T q r s`, which is what makes the adequacy induction line
up argument for argument. The one price is that de Bruijn indices are not
textbook notation; the honest alternative — named variables — needs
capture-avoiding substitution *in the trusted surface*, which is a far
worse object to audit than an index.

Two conventions worth stating, because a reader checking the semantics
against a paper will want them.

*Variables are levels, not indices.* A quantifier extends the environment
with `Fin.snoc`, i.e. at the *last* position, so the outermost bound
variable of a formula is `0` and the innermost is `Fin.last`. This is the
convention `typ` already uses for its moves (`MsoTypes`), and it is why
adequacy needs no shifting anywhere.

*Only `¬`, `∧` and `∃` are constructors.* Disjunction, implication and
universal quantification are abbreviations at the point of use, not
syntax: every one of them would add a case to the trusted recursion and
a case to every induction, and buy nothing that `not`/`and` does not
already give. `MSO₁` is the whole scope (plan decision C1): quantification
over vertices and vertex sets, with adjacency, equality and membership as
the atoms.

Finally, `SatIn` — satisfaction *relativized to a region* — is the
workhorse the type algebra actually talks about; `Sat` is the special case
of the whole graph (`satIn_univ`). The surface will carry `Sat` alone.
-/

namespace Lax11Proofs.MsoTypes

/-! ### Syntax -/

/-- Formulas of monadic second-order logic over the adjacency signature,
with `r` free vertex variables and `s` free set variables. Vertex
variables are `Fin r`, set variables are `Fin s`, and a quantifier binds
the *new last* index (`Fin.snoc` convention). -/
inductive MSO : ℕ → ℕ → Type
  /-- The vertices `i` and `j` are adjacent. -/
  | adj {r s : ℕ} (i j : Fin r) : MSO r s
  /-- The vertices `i` and `j` are equal. -/
  | eq {r s : ℕ} (i j : Fin r) : MSO r s
  /-- The vertex `i` belongs to the set `X`. -/
  | mem {r s : ℕ} (i : Fin r) (X : Fin s) : MSO r s
  /-- Negation. -/
  | not {r s : ℕ} (φ : MSO r s) : MSO r s
  /-- Conjunction. -/
  | and {r s : ℕ} (φ ψ : MSO r s) : MSO r s
  /-- There is a vertex satisfying `φ`, bound at index `Fin.last r`. -/
  | exV {r s : ℕ} (φ : MSO (r + 1) s) : MSO r s
  /-- There is a set of vertices satisfying `φ`, bound at index
  `Fin.last s`. -/
  | exS {r s : ℕ} (φ : MSO r (s + 1)) : MSO r s

/-- The quantifier rank: the nesting depth of quantifiers, counting both
kinds. This is the parameter the type algebra is indexed by. -/
def rank : {r s : ℕ} → MSO r s → ℕ
  | _, _, .adj _ _ => 0
  | _, _, .eq _ _ => 0
  | _, _, .mem _ _ => 0
  | _, _, .not φ => rank φ
  | _, _, .and φ ψ => max (rank φ) (rank ψ)
  | _, _, .exV φ => rank φ + 1
  | _, _, .exS φ => rank φ + 1

@[simp] theorem rank_adj {r s : ℕ} (i j : Fin r) : rank (MSO.adj (s := s) i j) = 0 := rfl

@[simp] theorem rank_eq {r s : ℕ} (i j : Fin r) : rank (MSO.eq (s := s) i j) = 0 := rfl

@[simp] theorem rank_mem {r s : ℕ} (i : Fin r) (X : Fin s) : rank (MSO.mem i X) = 0 := rfl

@[simp] theorem rank_not {r s : ℕ} (φ : MSO r s) : rank φ.not = rank φ := rfl

@[simp] theorem rank_and {r s : ℕ} (φ ψ : MSO r s) :
    rank (φ.and ψ) = max (rank φ) (rank ψ) := rfl

@[simp] theorem rank_exV {r s : ℕ} (φ : MSO (r + 1) s) : rank φ.exV = rank φ + 1 := rfl

@[simp] theorem rank_exS {r s : ℕ} (φ : MSO r (s + 1)) : rank φ.exS = rank φ + 1 := rfl

/-! ### Semantics

The trust object. `Sat G m A φ` says that `φ` holds in the graph `G`
under the vertex environment `m` and the set environment `A`. Every case
is one line, no case has a side condition, and the recursion is
structural in the formula. -/

variable {n : ℕ}

/-- Satisfaction of an MSO formula in the graph `G`, under a vertex
environment `m` and a set environment `A`. -/
def Sat (G : SimpleGraph (Fin n)) :
    {r s : ℕ} → (Fin r → Fin n) → (Fin s → Set (Fin n)) → MSO r s → Prop
  | _, _, m, _, .adj i j => G.Adj (m i) (m j)
  | _, _, m, _, .eq i j => m i = m j
  | _, _, m, A, .mem i X => m i ∈ A X
  | _, _, m, A, .not φ => ¬ Sat G m A φ
  | _, _, m, A, .and φ ψ => Sat G m A φ ∧ Sat G m A ψ
  | _, _, m, A, .exV φ => ∃ v : Fin n, Sat G (Fin.snoc m v) A φ
  | _, _, m, A, .exS φ => ∃ S : Set (Fin n), Sat G m (Fin.snoc A S) φ

/-- Satisfaction relativized to a region `X`: the atoms are read in the
ambient graph `G`, but both quantifiers range over `X` only — vertices
in `X`, sets contained in `X`. This is the notion the type algebra
computes (`typ` moves over exactly these), and it is the whole graph's
satisfaction when `X` is everything (`satIn_univ`). -/
def SatIn (G : SimpleGraph (Fin n)) (X : Set (Fin n)) :
    {r s : ℕ} → (Fin r → Fin n) → (Fin s → Set (Fin n)) → MSO r s → Prop
  | _, _, m, _, .adj i j => G.Adj (m i) (m j)
  | _, _, m, _, .eq i j => m i = m j
  | _, _, m, A, .mem i Y => m i ∈ A Y
  | _, _, m, A, .not φ => ¬ SatIn G X m A φ
  | _, _, m, A, .and φ ψ => SatIn G X m A φ ∧ SatIn G X m A ψ
  | _, _, m, A, .exV φ => ∃ v ∈ X, SatIn G X (Fin.snoc m v) A φ
  | _, _, m, A, .exS φ => ∃ S ⊆ X, SatIn G X m (Fin.snoc A S) φ

variable {G : SimpleGraph (Fin n)} {X : Set (Fin n)} {r s : ℕ}
  {m : Fin r → Fin n} {A : Fin s → Set (Fin n)}

@[simp] theorem satIn_adj (i j : Fin r) :
    SatIn G X m A (MSO.adj (s := s) i j) ↔ G.Adj (m i) (m j) := Iff.rfl

@[simp] theorem satIn_eq (i j : Fin r) :
    SatIn G X m A (MSO.eq (s := s) i j) ↔ m i = m j := Iff.rfl

@[simp] theorem satIn_mem (i : Fin r) (Y : Fin s) :
    SatIn G X m A (MSO.mem i Y) ↔ m i ∈ A Y := Iff.rfl

@[simp] theorem satIn_not (φ : MSO r s) :
    SatIn G X m A φ.not ↔ ¬ SatIn G X m A φ := Iff.rfl

@[simp] theorem satIn_and (φ ψ : MSO r s) :
    SatIn G X m A (φ.and ψ) ↔ SatIn G X m A φ ∧ SatIn G X m A ψ := Iff.rfl

@[simp] theorem satIn_exV (φ : MSO (r + 1) s) :
    SatIn G X m A φ.exV ↔ ∃ v ∈ X, SatIn G X (Fin.snoc m v) A φ := Iff.rfl

@[simp] theorem satIn_exS (φ : MSO r (s + 1)) :
    SatIn G X m A φ.exS ↔ ∃ S ⊆ X, SatIn G X m (Fin.snoc A S) φ := Iff.rfl

@[simp] theorem sat_exV (φ : MSO (r + 1) s) :
    Sat G m A φ.exV ↔ ∃ v : Fin n, Sat G (Fin.snoc m v) A φ := Iff.rfl

@[simp] theorem sat_exS (φ : MSO r (s + 1)) :
    Sat G m A φ.exS ↔ ∃ S : Set (Fin n), Sat G m (Fin.snoc A S) φ := Iff.rfl

/-- Relativizing to the whole graph is not a relativization: the region
form and the plain form agree at `X = univ`. This is the bridge between
the surface's `Sat` and the type algebra's `SatIn`. -/
theorem satIn_univ : ∀ {r s : ℕ} (φ : MSO r s) (m : Fin r → Fin n)
    (A : Fin s → Set (Fin n)), SatIn G Set.univ m A φ ↔ Sat G m A φ
  | _, _, .adj _ _, _, _ => Iff.rfl
  | _, _, .eq _ _, _, _ => Iff.rfl
  | _, _, .mem _ _, _, _ => Iff.rfl
  | _, _, .not φ, m, A => not_congr (satIn_univ φ m A)
  | _, _, .and φ ψ, m, A => and_congr (satIn_univ φ m A) (satIn_univ ψ m A)
  | _, _, .exV φ, m, A => by
      simp only [satIn_exV, sat_exV, Set.mem_univ, true_and]
      exact exists_congr fun v => satIn_univ φ _ A
  | _, _, .exS φ, m, A => by
      simp only [satIn_exS, sat_exS, Set.subset_univ, true_and]
      exact exists_congr fun S => satIn_univ φ m _

/-! ### Smoke tests

Two hand-checked sentences on the two-vertex complete graph, to catch a
semantics that type-checks and means something else. `∃x∃y adj x y` holds
there; `∃X ∀x (x ∈ X)`, spelled with the available constructors as
`∃X ¬∃x ¬(x ∈ X)`, holds in any graph, witnessed by `univ`. -/

/-- The two-vertex complete graph has an edge. -/
example : Sat (⊤ : SimpleGraph (Fin 2)) Fin.elim0 Fin.elim0
    (MSO.exV (MSO.exV (MSO.adj 0 1))) := by
  refine ⟨0, 1, ?_⟩
  show (⊤ : SimpleGraph (Fin 2)).Adj _ _
  simp only [SimpleGraph.top_adj]
  decide

/-- The empty graph on two vertices has none. -/
example : Sat (⊥ : SimpleGraph (Fin 2)) Fin.elim0 Fin.elim0
    (MSO.not (MSO.exV (MSO.exV (MSO.adj 0 1)))) := by
  rintro ⟨u, v, h⟩
  exact h

/-- Some set contains every vertex. -/
example : Sat (⊤ : SimpleGraph (Fin 2)) Fin.elim0 Fin.elim0
    (MSO.exS (MSO.not (MSO.exV (MSO.not (MSO.mem 0 0))))) := by
  refine ⟨Set.univ, ?_⟩
  rintro ⟨v, h⟩
  exact h (Set.mem_univ _)

/-- The rank of that last sentence is `2`: the negations are free. -/
example : rank ((MSO.exS (MSO.not (MSO.exV (MSO.not (MSO.mem 0 0)))) : MSO 0 0)) = 2 := rfl

end Lax11Proofs.MsoTypes
