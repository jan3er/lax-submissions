import Lax3.FirstOrder
import Lax3Proofs.SyntaxLemmas

/-!
The reduction of plain first-order logic into distance logic: the
embedding `toDistFO`, which sends a formula of `Lax3.FirstOrder` to the
formula of `Lax3.DistFO` of the same shape, reading the quantifier as an
unrestricted one and mentioning no color and no distance atom.

Only the two statements that make the embedding a reduction are proved
here — satisfaction is preserved, and quantifier rank `q` becomes
distance rank `(k', q)` at every free-variable bound `k'` — and both are
two-line-per-case inductions. They are that short because the two logics
agree clause by clause on the fragment the image lives in: the `adj`,
`eq`, `not`, `and` and `exU` clauses of `Lax3.DistFO.Sat` are the
clauses of `Lax3.FirstOrder.Sat` verbatim, so the semantic induction is
a congruence and nothing else. The rank bookkeeping is just as thin: the
`exU` constructor of `DRank` charges an unrestricted quantifier exactly
one rank level, which is what `rank` charges a quantifier, and the
distance-atom side conditions — the only part of `DRank` with arithmetic
in it — are never reached, since the image carries no distance atom and
no local quantifier. In particular no monotonicity of `DRank` is needed:
at a conjunction the two conjuncts already have rank at most the `max`,
so the induction hypotheses apply at the very same bound.

This is the entry point the model-checking headline uses. A statement of
the model-checking problem may mention plain first-order sentences and
graphs and nothing else; `toDistFO` is how such a sentence is handed to
the distance-logic engine that the locality theorem and the normal form
are stated for, with its quantifier rank turned into the rank measure
that engine tracks.
-/

namespace Lax3Proofs.Reduction

open Lax3.ColoredGraphs Lax3.DistFO Lax3Proofs.SyntaxLemmas
open Lax3.FirstOrder (FO rank)

variable {L n : ℕ}

/-! ### Unfolding the first-order side

One `rfl`-lemma per clause of `Lax3.FirstOrder.Sat` and of
`Lax3.FirstOrder.rank`, for the reason spelled out in
`Lax3Proofs.SyntaxLemmas`: handing a concept-side definition to a tactic
would record its match auxiliaries under the concept's namespace. The
distance-logic side needs no new lemmas of this kind — the `sat_*`
family of `Lax3Proofs.SyntaxLemmas` already has them.
-/

section Unfolding

variable {G : SimpleGraph (Fin n)} {k : ℕ} {m : Fin k → Fin n}

/-- Satisfaction of a first-order adjacency atom. -/
theorem foSat_adj (i j : Fin k) :
    Lax3.FirstOrder.Sat G m (.adj i j) ↔ G.Adj (m i) (m j) := Iff.rfl

/-- Satisfaction of a first-order equality atom. -/
theorem foSat_eq (i j : Fin k) :
    Lax3.FirstOrder.Sat G m (.eq i j) ↔ m i = m j := Iff.rfl

/-- Satisfaction of a first-order negation. -/
theorem foSat_not (φ : FO k) :
    Lax3.FirstOrder.Sat G m (.not φ) ↔ ¬ Lax3.FirstOrder.Sat G m φ := Iff.rfl

/-- Satisfaction of a first-order conjunction. -/
theorem foSat_and (φ ψ : FO k) :
    Lax3.FirstOrder.Sat G m (.and φ ψ) ↔
      Lax3.FirstOrder.Sat G m φ ∧ Lax3.FirstOrder.Sat G m ψ := Iff.rfl

/-- Satisfaction of a first-order quantification. -/
theorem foSat_ex (φ : FO (k + 1)) :
    Lax3.FirstOrder.Sat G m (.ex φ) ↔
      ∃ v : Fin n, Lax3.FirstOrder.Sat G (Fin.snoc m v) φ := Iff.rfl

/-- The quantifier rank of an adjacency atom. -/
theorem rank_adj (i j : Fin k) : rank (.adj i j : FO k) = 0 := rfl

/-- The quantifier rank of an equality atom. -/
theorem rank_eq (i j : Fin k) : rank (.eq i j : FO k) = 0 := rfl

/-- The quantifier rank of a negation. -/
theorem rank_not (φ : FO k) : rank (.not φ) = rank φ := rfl

/-- The quantifier rank of a conjunction. -/
theorem rank_and (φ ψ : FO k) : rank (.and φ ψ) = max (rank φ) (rank ψ) := rfl

/-- The quantifier rank of a quantification. -/
theorem rank_ex (φ : FO (k + 1)) : rank (.ex φ) = rank φ + 1 := rfl

end Unfolding

/-! ### The embedding -/

/-- The reduction of plain first-order logic into distance logic: every
formula of `Lax3.FirstOrder` becomes the formula of `Lax3.DistFO` of the
same shape, with the quantifier read as an unrestricted one. The image
mentions no color, so the number of colors is arbitrary, and it carries
no distance atom and no local quantifier. -/
def toDistFO {L : ℕ} : {k : ℕ} → FO k → DistFO L k
  | _, .adj i j => .adj i j
  | _, .eq i j => .eq i j
  | _, .not φ => .not (toDistFO φ)
  | _, .and φ ψ => .and (toDistFO φ) (toDistFO ψ)
  | _, .ex φ => .exU (toDistFO φ)

/-! ### Satisfaction and rank -/

/-- The reduction preserves satisfaction: a first-order formula holds in
a graph under an environment exactly when its image holds in that graph,
under any coloring, under the same environment. Every case is the
matching pair of clauses of the two definitions of satisfaction; the
coloring is inert because the image has no color atom. -/
theorem sat_toDistFO {k : ℕ} (G : SimpleGraph (Fin n)) (col : Coloring n L)
    (m : Fin k → Fin n) (φ : FO k) :
    Sat G col m (toDistFO φ) ↔ Lax3.FirstOrder.Sat G m φ := by
  induction φ with
  | adj i j => exact Iff.rfl
  | eq i j => exact Iff.rfl
  | not φ ih => simp only [toDistFO, sat_not, foSat_not, ih m]
  | and φ ψ ihφ ihψ => simp only [toDistFO, sat_and, foSat_and, ihφ m, ihψ m]
  | ex φ ih =>
    simp only [toDistFO, sat_exU, foSat_ex]
    exact exists_congr fun v => ih (Fin.snoc m v)

/-- The reduction turns quantifier rank into distance rank: a formula of
quantifier rank at most `q` has image of distance rank `(k', q)`, at
every free-variable bound `k'`. The atoms of the image have every
distance rank, and its quantifiers are unrestricted, so the horizon
conditions of `DRank` are vacuous and the whole content is that `exU`
charges one rank level, exactly as `rank` does. -/
theorem drank_toDistFO {k k' q : ℕ} (φ : FO k) (hq : rank φ ≤ q) :
    DRank (L := L) k' q (toDistFO φ) := by
  induction φ generalizing k' q with
  | adj i j => exact .adj i j
  | eq i j => exact .eq i j
  | not φ ih => rw [rank_not] at hq; exact .not (ih hq)
  | and φ ψ ihφ ihψ =>
    rw [rank_and, max_le_iff] at hq
    exact .and (ihφ hq.1) (ihψ hq.2)
  | ex φ ih =>
    rw [rank_ex] at hq
    obtain _ | q := q
    · omega
    · exact .exU (ih (by omega))

end Lax3Proofs.Reduction
