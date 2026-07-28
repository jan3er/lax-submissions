import Lax3.Locality
import Mathlib.Data.List.FinRange

/-!
---
title: Normal form for distance logic
type: theorem
---
For *q* ≥ 1, every formula of distance logic of distance rank
(*k*, *q*) is equivalent to a boolean combination of *local* formulas
of distance rank (*k*, *q*) and explicit sentences "there are *t*
vertices, pairwise at distance more than *r*, all satisfying β", where
*t* ≤ *k* + *q*, the formula β is local of distance rank
(*k*+1, *q*−1), the radius satisfies *r* ≤ ρ⁻(*k*, *q*), and β is
semantically (*r*/4)-local. This is Corollary 7 of the source note
(arXiv:2606.23180), the analogue for distance logic of Gaifman's
normal form: it is the locality theorem of `Lax3.Locality` with the
scatter sentences written out in the logic itself.

The step from the theorem to the corollary is the maximum-size scatter
choice: with it, "the distinguished maximal scattered set has at least
*t* elements" says no more and no less than "some *r*-scattered set of
*t* vertices satisfies β", and the latter is a sentence of distance
logic. No choice appears in the statement below, because after that
replacement there is nothing left for one to be attached to.

# Formalization notes

`scatterFml` is the source's sentence (3) written out. Its distance
condition is "larger than *r*", the negation of the binary distance
atom "at most *r*" — the strict inequality of the source has no atom
of its own and needs none. The empty conjunction is `verum`, a formula
that holds in every colored graph, so `scatterFml` is defined at every
`t` including `0`, where it is vacuously true, as the source's
sentence is. `verum` costs one unrestricted quantifier, which no
statement here notices: nothing constrains the distance rank of
`scatterFml` itself, and the rank conditions of the normal form are
conditions on the parameters `r`, `t`, β. Placing β at each bound
variable is what `DistFO.rename` is for.

The locality radius of β is `σ.r / 4` in ℕ, which rounds down. That
makes the claim slightly stronger than the source's real-valued *r*/4
and it is still sound: the radius window of a scatter sentence of
distance rank (*k*, *q*) guarantees 4ρ⁻(*k*+*i*, *q*−*i*) ≤ *r*, so
ρ⁻(*k*+*i*, *q*−*i*) ≤ ⌊*r*/4⌋, and β is semantically
ρ⁻(*k*+*i*, *q*−*i*)-local.

The boolean combination reuses the `BC` reification and the
`ScatterSentence` record of the locality concept as the carrier of the
parameter triple (*r*, *t*, β); here the record is only data — its
satisfaction is *not* used, each atom being evaluated through
`scatterFml` instead. Effectiveness is deliberately absent, for the
reasons recorded in `Lax3.Locality`.
-/

namespace Lax3.NormalForm

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality

variable {L : ℕ}

/-- A formula that holds in every colored graph under every
environment: no vertex differs from itself. -/
def verum {k : ℕ} : DistFO L k :=
  .not (.exU (.not (.eq (Fin.last k) (Fin.last k))))

/-- The conjunction of a list of formulas; the empty conjunction is
`verum`. -/
def conj {k : ℕ} : List (DistFO L k) → DistFO L k
  | [] => verum
  | φ :: φs => .and φ (conj φs)

/-- `k` unrestricted quantifiers in front of a formula with `k` free
variables, leaving a sentence. -/
def exUs : {k : ℕ} → DistFO L k → DistFO L 0
  | 0, φ => φ
  | _ + 1, φ => exUs (.exU φ)

/-- The source's scatter sentence written out in distance logic: there
are `t` vertices, pairwise at distance larger than `r`, each satisfying
`β`. Distance larger than `r` is the negation of the binary distance
atom of radius `r`, and `β` is placed at each bound variable by
renaming. -/
def scatterFml (r t : ℕ) (β : DistFO L 1) : DistFO L 0 :=
  exUs (conj
    (((List.finRange t).flatMap fun i =>
        (List.finRange t).filterMap fun j =>
          if i = j then none else some (DistFO.not (DistFO.distLe r i j))) ++
      (List.finRange t).map fun i => rename (fun _ : Fin 1 => i) β))

/-- **Normal form for distance logic** (Corollary 7 of
arXiv:2606.23180). For `q ≥ 1`, every formula of distance rank `(k, q)`
is equivalent to a boolean combination of local formulas of distance
rank `(k, q)` and sentences `scatterFml r t β` — there are `t` vertices,
pairwise at distance larger than `r`, all satisfying `β` — where
`t ≤ k + q`, the formula `β` is local of distance rank `(k + 1, q - 1)`,
the radius satisfies `r ≤ ρ⁻(k, q)`, and `β` is semantically
`r / 4`-local. -/
axiom normalForm {k q : ℕ} (hq : 1 ≤ q) (φ : DistFO L k) (hφ : DistFO.DRank k q φ) :
    ∃ b : BC (DistFO L k ⊕ ScatterSentence L),
      (∀ ψ : DistFO L k, Sum.inl ψ ∈ b.atoms → DistFO.IsLocal ψ ∧ DistFO.DRank k q ψ) ∧
      (∀ σ : ScatterSentence L, Sum.inr σ ∈ b.atoms →
        σ.t ≤ k + q ∧ DistFO.IsLocal σ.β ∧ DistFO.DRank (k + 1) (q - 1) σ.β ∧
          σ.r ≤ rhoMinus k q ∧ DistFO.SemanticallyLocal (σ.r / 4) σ.β) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
        DistFO.Sat G col m φ ↔
          b.eval (Sum.elim (DistFO.Sat G col m)
            (fun σ => DistFO.Sat G col Fin.elim0 (scatterFml σ.r σ.t σ.β)))

end Lax3.NormalForm
