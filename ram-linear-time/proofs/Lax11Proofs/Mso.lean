import Lax11.Mso
import Lax11Proofs.MsoTypes

/-!
Monadic second-order logic on graphs: the syntax, and the semantics that
is the new trust object.

`MSO`, `rank` and `Sat` **live on the endorsement surface**, in
`concepts/Lax11/Mso.lean`, and are re-exported here under the names the
development already uses: seven constructors and a fifteen-line
recursion, and nothing else. Everything that a formalization of MSO
usually drags along — substitution, capture avoidance, a `Closed`
predicate, well-formedness side conditions — is absent by construction.
What this file adds is the machinery the proofs need and the surface
does not carry: the `rank` equations, the relativized `SatIn`, and the
bridge between them.

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
of the whole graph (`satIn_univ`). The surface carries `Sat` alone.
-/

namespace Lax11Proofs.MsoTypes

/-! ### Syntax

The syntax, the quantifier rank and satisfaction are the surface
definitions of `Lax11.Mso`; the constructors are re-exported too, so
that every use site below reads as if they were declared here. -/

export Lax11.Mso (MSO MSO.adj MSO.eq MSO.mem MSO.not MSO.and MSO.exV MSO.exS rank Sat)

@[simp] theorem rank_adj {r s : ℕ} (i j : Fin r) : rank (MSO.adj (s := s) i j) = 0 := rfl

@[simp] theorem rank_eq {r s : ℕ} (i j : Fin r) : rank (MSO.eq (s := s) i j) = 0 := rfl

@[simp] theorem rank_mem {r s : ℕ} (i : Fin r) (X : Fin s) : rank (MSO.mem i X) = 0 := rfl

@[simp] theorem rank_not {r s : ℕ} (φ : MSO r s) : rank φ.not = rank φ := rfl

@[simp] theorem rank_and {r s : ℕ} (φ ψ : MSO r s) :
    rank (φ.and ψ) = max (rank φ) (rank ψ) := rfl

@[simp] theorem rank_exV {r s : ℕ} (φ : MSO (r + 1) s) : rank φ.exV = rank φ + 1 := rfl

@[simp] theorem rank_exS {r s : ℕ} (φ : MSO r (s + 1)) : rank φ.exS = rank φ + 1 := rfl

/-! ### Semantics

The trust object, `Sat G m A φ` — that `φ` holds in the graph `G` under
the vertex environment `m` and the set environment `A` — is on the
surface. What is defined here is its relativization to a region, which
is what the type algebra computes. -/

variable {n : ℕ}

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
