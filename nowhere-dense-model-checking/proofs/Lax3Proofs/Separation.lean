import Lax3Proofs.SyntaxLemmas
import Lax3Proofs.SemLocal

/-!
The source's separation lemma (arXiv:2606.23180, `lem:far-ltp`): a
*local* formula of distance rank `(k, q)` whose variables are split into
two blocks that lie further than ρ⁻(k, q) apart is, under that far-apart
assumption, equivalent to a disjunction of conjunctions `α(x̄) ∧ β(ȳ)`
of local formulas of the same distance rank, one factor per block.

The disjunction is produced as a *list of pairs*: `separate` returns a
`List (DistFO L a × DistFO L b)` whose first components live in the
`x̄`-side context `Fin a` and whose second components live in the
`ȳ`-side context `Fin b`. Each side's formulas are therefore written in
its own reindexed context — the guard set of a local quantifier of an
output formula is a set of that side's variables — so no `UsesOnly`
bookkeeping and no `rename` occurs anywhere in the statement, and the
guards of the source's per-side formulas are literally the guards here.
The split itself is a pair of injections `e₁ : Fin a → Fin K`,
`e₂ : Fin b → Fin K` with disjoint images covering `Fin K`.

The proof is the source's structural induction, generalizing the split
(and hence the far-apart hypothesis) at every step.

* An atom whose variables lie on one side is rebuilt on that side and
  paired with an always-true atom on the other. An atom with one
  variable on each side is refuted by the far-apart hypothesis, its
  radius being at most ρ⁻(k, q) — one for adjacency, zero for equality,
  the syntactic radius for a binary distance atom — so its list of
  disjuncts is empty.
* Conjunction takes pairwise products of the two lists, negation the
  disjunctive normal form of the negated list: for each way of choosing,
  in every pair of the list, a side to refute, one pair of conjunctions
  (`negPairs`).
* At a local quantifier the input guard `∃ i ∈ g, dist(x_i, z) ≤ r` is
  split by *which side the guard variable `i` lies on*, not by where the
  witness sits. Both cases recurse on the body with the bound variable
  added to the guarding side — the split `(x̄z ; ȳ)` or `(x̄ ; ȳz)` — and
  wrap each returned disjunct in a local quantifier over the side's
  reading of `g`, at the same radius; the output list is the two lists
  appended. Farness for the extended split is the triangle inequality
  against `Horizon.rhoPlus_add_rhoMinus_le`: the witness is within
  r ≤ ρ⁺(k+1, q−1) of the guarding side, and ρ⁺(k+1, q−1) +
  ρ⁻(k+1, q−1) ≤ ρ⁻(k, q). `IsLocal` discharges the unrestricted
  quantifier.

# Formalization notes

**Deviation: both blocks are assumed nonempty (`1 ≤ a`, `1 ≤ b`).** The
one-sided atom cases and the disjunctive normal form of a negation all
need an always-true *local* formula of the relevant distance rank on the
other side, and at arity 0 there is none at all: every atom takes a
variable, and a local quantifier over an empty context is unsatisfiable
(and needs quantifier rank at least one, which rank `(·, 0)` does not
have). With one variable in scope `x = x` is an always-true local atom
of every distance rank, which is `alwaysTrue`. The caller of this lemma
in the locality theorem splits `k + 1` variables as `a = k ≥ 1` against
the single capsule variable `b = 1`, so the hypothesis costs nothing
there.

**Deviation from the design record: the local-quantifier case splits on
the guard variable, not on the witness.** With the guard set recorded in
the syntax, the disjunction over the guard is already a disjunction over
variables, each of which lies on a known side; the source's three-way
split of the witness into "near x̄", "near ȳ" and "in the annulus" — and
with it the annulus atoms of the source's (eq1) — is then not needed.
The two resulting cases are the source's cases 1 and 2 with a smaller
guard; case 3 is subsumed, because a witness guarded from the x̄-side is
handled by the first case whatever its distance to ȳ.

The negation case is a recursion over the list rather than the design
record's `bigAnd` over subsets: `negPairs` chooses a side to refute one
pair at a time, which makes its correctness lemma a short induction and
needs no list-indexed conjunction operator.

No tactic here is handed a concept-side definition. `Sat`, `IsLocal` and
`rename` are taken apart through the clause lemmas of
`Lax3Proofs.SyntaxLemmas` or definitionally, by `exact` against the
unfolded shape; the definitions of this file are of course unfolded
freely. Every radius inequality goes through `Lax3Proofs.Horizon`.
-/

namespace Lax3Proofs.Separation

open Lax3.ColoredGraphs Lax3.DistFO
open Lax3Proofs.Horizon Lax3Proofs.SemLocal Lax3Proofs.SyntaxLemmas Lax3Proofs.WalkDistance

variable {L n : ℕ} {G : SimpleGraph (Fin n)} {col : Coloring n L}

/-! ### An always-true local atom

Both sides of a separation must carry a formula even when the input
formula says nothing about them. On a nonempty context the equality atom
`x₀ = x₀` is such a formula: local, true everywhere, and of every
distance rank.
-/

/-- The always-true local atom of a nonempty context: `x₀ = x₀`. -/
def alwaysTrue {L a : ℕ} (ha : 1 ≤ a) : DistFO L a := .eq ⟨0, ha⟩ ⟨0, ha⟩

/-- `alwaysTrue` is true in every graph under every environment. -/
theorem sat_alwaysTrue {a : ℕ} {ha : 1 ≤ a} {m : Fin a → Fin n} :
    Sat G col m (alwaysTrue ha : DistFO L a) := rfl

/-- `alwaysTrue` is local. -/
theorem isLocal_alwaysTrue {L a : ℕ} (ha : 1 ≤ a) : IsLocal (alwaysTrue ha : DistFO L a) :=
  trivial

/-- `alwaysTrue` has every distance rank. -/
theorem drank_alwaysTrue {L a : ℕ} (ha : 1 ≤ a) (k q : ℕ) :
    DRank k q (alwaysTrue ha : DistFO L a) := .eq _ _

/-! ### List algebra of separated pairs

A separation is carried by a list of pairs, read as the disjunction of
the conjunctions of its entries. Conjunction of two such disjunctions is
the pairwise product, negation is a choice of a side to refute in each
pair, and a local quantifier is wrapped around one component of each
pair.
-/

/-- The disjunctive normal form of the negation of a list of pairs: one
pair of conjunctions per way of choosing, in every pair of the list, a
side to refute. -/
def negPairs {L a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    List (DistFO L a × DistFO L b) → List (DistFO L a × DistFO L b)
  | [] => [(alwaysTrue ha, alwaysTrue hb)]
  | p :: P =>
      (negPairs ha hb P).flatMap fun c => [(p.1.not.and c.1, c.2), (c.1, p.2.not.and c.2)]

/-- `negPairs` preserves locality and distance rank. -/
theorem drank_negPairs {a b k q : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (P : List (DistFO L a × DistFO L b))
    (hP : ∀ p ∈ P, IsLocal p.1 ∧ DRank k q p.1 ∧ IsLocal p.2 ∧ DRank k q p.2) :
    ∀ c ∈ negPairs ha hb P, IsLocal c.1 ∧ DRank k q c.1 ∧ IsLocal c.2 ∧ DRank k q c.2 := by
  induction P with
  | nil =>
    intro c hc
    simp only [negPairs, List.mem_singleton] at hc
    subst hc
    exact ⟨isLocal_alwaysTrue ha, drank_alwaysTrue ha k q,
      isLocal_alwaysTrue hb, drank_alwaysTrue hb k q⟩
  | cons p P ih =>
    intro c hc
    simp only [negPairs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hc
    obtain ⟨d, hd, hcd⟩ := hc
    obtain ⟨hd1, hd2, hd3, hd4⟩ := ih (fun p' hp' => hP p' (List.mem_cons.mpr (Or.inr hp'))) d hd
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hP p (List.mem_cons.mpr (Or.inl rfl))
    rcases hcd with rfl | rfl
    · exact ⟨⟨hp1, hd1⟩, .and (.not hp2) hd2, hd3, hd4⟩
    · exact ⟨hd1, hd2, ⟨hp3, hd3⟩, .and (.not hp4) hd4⟩

/-- `negPairs` is the negation: some pair of the negated list holds
exactly when no pair of the original one does. -/
theorem sat_negPairs {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (m₁ : Fin a → Fin n)
    (m₂ : Fin b → Fin n) (P : List (DistFO L a × DistFO L b)) :
    (∃ c ∈ negPairs ha hb P, Sat G col m₁ c.1 ∧ Sat G col m₂ c.2) ↔
      ∀ p ∈ P, ¬ (Sat G col m₁ p.1 ∧ Sat G col m₂ p.2) := by
  induction P with
  | nil =>
    constructor
    · intro _ p hp
      simp at hp
    · intro _
      exact ⟨(alwaysTrue ha, alwaysTrue hb), by simp [negPairs], sat_alwaysTrue, sat_alwaysTrue⟩
  | cons p P ih =>
    constructor
    · rintro ⟨c, hc, hc1, hc2⟩ p' hp'
      simp only [negPairs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hc
      obtain ⟨d, hd, hcd⟩ := hc
      have hkey : (Sat G col m₁ d.1 ∧ Sat G col m₂ d.2) ∧
          ¬ (Sat G col m₁ p.1 ∧ Sat G col m₂ p.2) := by
        rcases hcd with rfl | rfl
        · exact ⟨⟨hc1.2, hc2⟩, fun h => hc1.1 h.1⟩
        · exact ⟨⟨hc1, hc2.2⟩, fun h => hc2.1 h.2⟩
      rcases List.mem_cons.mp hp' with rfl | hp''
      · exact hkey.2
      · exact ih.mp ⟨d, hd, hkey.1⟩ p' hp''
    · intro h
      obtain ⟨d, hd, hd1, hd2⟩ := ih.mpr fun p' hp' => h p' (List.mem_cons.mpr (Or.inr hp'))
      have hp := h p (List.mem_cons.mpr (Or.inl rfl))
      by_cases h1 : Sat G col m₁ p.1
      · refine ⟨(d.1, p.2.not.and d.2), ?_, hd1, fun h2 => hp ⟨h1, h2⟩, hd2⟩
        simp only [negPairs, List.mem_flatMap, List.mem_cons]
        exact ⟨d, hd, Or.inr (Or.inl rfl)⟩
      · refine ⟨(p.1.not.and d.1, d.2), ?_, ⟨h1, hd1⟩, hd2⟩
        simp only [negPairs, List.mem_flatMap, List.mem_cons]
        exact ⟨d, hd, Or.inl rfl⟩

/-- The conjunction of two lists of pairs: all pairwise products. -/
def prodPairs {L a b : ℕ} (P Q : List (DistFO L a × DistFO L b)) :
    List (DistFO L a × DistFO L b) :=
  P.flatMap fun p => Q.map fun c => (p.1.and c.1, p.2.and c.2)

/-- `prodPairs` preserves locality and distance rank. -/
theorem drank_prodPairs {a b k q : ℕ} (P Q : List (DistFO L a × DistFO L b))
    (hP : ∀ p ∈ P, IsLocal p.1 ∧ DRank k q p.1 ∧ IsLocal p.2 ∧ DRank k q p.2)
    (hQ : ∀ c ∈ Q, IsLocal c.1 ∧ DRank k q c.1 ∧ IsLocal c.2 ∧ DRank k q c.2) :
    ∀ d ∈ prodPairs P Q, IsLocal d.1 ∧ DRank k q d.1 ∧ IsLocal d.2 ∧ DRank k q d.2 := by
  intro d hd
  simp only [prodPairs, List.mem_flatMap, List.mem_map] at hd
  obtain ⟨p, hp, c, hc, rfl⟩ := hd
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hP p hp
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hQ c hc
  exact ⟨⟨hp1, hc1⟩, .and hp2 hc2, ⟨hp3, hc3⟩, .and hp4 hc4⟩

/-- `prodPairs` is the conjunction. -/
theorem sat_prodPairs {a b : ℕ} (m₁ : Fin a → Fin n) (m₂ : Fin b → Fin n)
    (P Q : List (DistFO L a × DistFO L b)) :
    (∃ d ∈ prodPairs P Q, Sat G col m₁ d.1 ∧ Sat G col m₂ d.2) ↔
      (∃ p ∈ P, Sat G col m₁ p.1 ∧ Sat G col m₂ p.2) ∧
        (∃ c ∈ Q, Sat G col m₁ c.1 ∧ Sat G col m₂ c.2) := by
  constructor
  · rintro ⟨d, hd, hd1, hd2⟩
    simp only [prodPairs, List.mem_flatMap, List.mem_map] at hd
    obtain ⟨p, hp, c, hc, rfl⟩ := hd
    exact ⟨⟨p, hp, hd1.1, hd2.1⟩, ⟨c, hc, hd1.2, hd2.2⟩⟩
  · rintro ⟨⟨p, hp, hp1, hp2⟩, c, hc, hc1, hc2⟩
    refine ⟨(p.1.and c.1, p.2.and c.2), ?_, ⟨hp1, hc1⟩, ⟨hp2, hc2⟩⟩
    simp only [prodPairs, List.mem_flatMap, List.mem_map]
    exact ⟨p, hp, c, hc, rfl⟩

/-- Wrapping a local quantifier around the `x̄`-side of every pair. -/
def wrapLeft {L a b : ℕ} (r : ℕ) (g : Finset (Fin a))
    (Q : List (DistFO L (a + 1) × DistFO L b)) : List (DistFO L a × DistFO L b) :=
  Q.map fun c => (.exL r g c.1, c.2)

/-- Wrapping a local quantifier around the `ȳ`-side of every pair. -/
def wrapRight {L a b : ℕ} (r : ℕ) (g : Finset (Fin b))
    (Q : List (DistFO L a × DistFO L (b + 1))) : List (DistFO L a × DistFO L b) :=
  Q.map fun c => (c.1, .exL r g c.2)

/-! ### The two sides of a split under a binder

A split of `Fin K` into two blocks is extended to `Fin (K + 1)` by
giving the newly bound variable to one of the two blocks: that block's
embedding gains the new last index (`embSnoc`), the other block's
embedding is merely shifted (`embCast`).
-/

/-- A side embedding extended by the newly bound variable. -/
def embSnoc {a K : ℕ} (e : Fin a → Fin K) : Fin (a + 1) → Fin (K + 1) :=
  Fin.snoc (fun i => (e i).castSucc) (Fin.last K)

/-- A side embedding shifted past a binder it does not take. -/
def embCast {a K : ℕ} (e : Fin a → Fin K) : Fin a → Fin (K + 1) :=
  fun i => (e i).castSucc

/-- `embSnoc` on an old variable. -/
theorem embSnoc_castSucc {a K : ℕ} (e : Fin a → Fin K) (i : Fin a) :
    embSnoc e i.castSucc = (e i).castSucc := by
  simp [embSnoc]

/-- `embSnoc` on the newly bound variable. -/
theorem embSnoc_last {a K : ℕ} (e : Fin a → Fin K) : embSnoc e (Fin.last a) = Fin.last K := by
  simp [embSnoc]

/-- `embCast` is the shift of a side embedding. -/
theorem embCast_apply {a K : ℕ} (e : Fin a → Fin K) (i : Fin a) :
    embCast e i = (e i).castSucc := rfl

/-- Extending an injective side embedding keeps it injective. -/
theorem injective_embSnoc {a K : ℕ} {e : Fin a → Fin K} (h : Function.Injective e) :
    Function.Injective (embSnoc e) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rfl
    | cast j' =>
      rw [embSnoc_last, embSnoc_castSucc] at hij
      exact absurd hij.symm (Fin.castSucc_ne_last (e j'))
  | cast i' =>
    induction j using Fin.lastCases with
    | last =>
      rw [embSnoc_castSucc, embSnoc_last] at hij
      exact absurd hij (Fin.castSucc_ne_last (e i'))
    | cast j' =>
      rw [embSnoc_castSucc, embSnoc_castSucc] at hij
      exact congrArg Fin.castSucc (h (Fin.castSucc_injective K hij))

/-- Shifting an injective side embedding keeps it injective. -/
theorem injective_embCast {a K : ℕ} {e : Fin a → Fin K} (h : Function.Injective e) :
    Function.Injective (embCast e) :=
  fun _ _ hij => h (Fin.castSucc_injective K hij)

/-- The two blocks of an extended split are still disjoint, the bound
variable going to the first block. -/
theorem embSnoc_ne_embCast {a b K : ℕ} {e₁ : Fin a → Fin K} {e₂ : Fin b → Fin K}
    (hdis : ∀ i j, e₁ i ≠ e₂ j) : ∀ (i : Fin (a + 1)) (j : Fin b),
      embSnoc e₁ i ≠ embCast e₂ j := by
  intro i j
  induction i using Fin.lastCases with
  | last =>
    rw [embSnoc_last, embCast_apply]
    exact fun hc => absurd hc.symm (Fin.castSucc_ne_last (e₂ j))
  | cast i' =>
    rw [embSnoc_castSucc, embCast_apply]
    exact fun hc => hdis i' j (Fin.castSucc_injective K hc)

/-- The two blocks of an extended split are still disjoint, the bound
variable going to the second block. -/
theorem embCast_ne_embSnoc {a b K : ℕ} {e₁ : Fin a → Fin K} {e₂ : Fin b → Fin K}
    (hdis : ∀ i j, e₁ i ≠ e₂ j) : ∀ (i : Fin a) (j : Fin (b + 1)),
      embCast e₁ i ≠ embSnoc e₂ j := by
  intro i j
  induction j using Fin.lastCases with
  | last =>
    rw [embSnoc_last, embCast_apply]
    exact fun hc => absurd hc (Fin.castSucc_ne_last (e₁ i))
  | cast j' =>
    rw [embSnoc_castSucc, embCast_apply]
    exact fun hc => hdis i j' (Fin.castSucc_injective K hc)

/-- The two blocks of an extended split still cover, the bound variable
going to the first block. -/
theorem cover_embSnoc_embCast {a b K : ℕ} {e₁ : Fin a → Fin K} {e₂ : Fin b → Fin K}
    (hcov : ∀ v, (∃ i, e₁ i = v) ∨ (∃ j, e₂ j = v)) :
    ∀ w : Fin (K + 1), (∃ i, embSnoc e₁ i = w) ∨ (∃ j, embCast e₂ j = w) := by
  intro w
  induction w using Fin.lastCases with
  | last => exact Or.inl ⟨Fin.last a, embSnoc_last e₁⟩
  | cast u =>
    rcases hcov u with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨i.castSucc, by rw [embSnoc_castSucc, hi]⟩
    · exact Or.inr ⟨j, by rw [embCast_apply, hj]⟩

/-- The two blocks of an extended split still cover, the bound variable
going to the second block. -/
theorem cover_embCast_embSnoc {a b K : ℕ} {e₁ : Fin a → Fin K} {e₂ : Fin b → Fin K}
    (hcov : ∀ v, (∃ i, e₁ i = v) ∨ (∃ j, e₂ j = v)) :
    ∀ w : Fin (K + 1), (∃ i, embCast e₁ i = w) ∨ (∃ j, embSnoc e₂ j = w) := by
  intro w
  induction w using Fin.lastCases with
  | last => exact Or.inr ⟨Fin.last b, embSnoc_last e₂⟩
  | cast u =>
    rcases hcov u with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨i, by rw [embCast_apply, hi]⟩
    · exact Or.inr ⟨j.castSucc, by rw [embSnoc_castSucc, hj]⟩

/-- Reindexing an extended environment along an extended side embedding
extends the reindexed environment. -/
theorem snoc_comp_embSnoc {K a : ℕ} (e : Fin a → Fin K) (m : Fin K → Fin n) (v : Fin n) :
    (Fin.snoc m v : Fin (K + 1) → Fin n) ∘ embSnoc e =
      (Fin.snoc (m ∘ e) v : Fin (a + 1) → Fin n) :=
  snoc_comp_renameLift e m v

/-- Reindexing an extended environment along a shifted side embedding
forgets the extension. -/
theorem snoc_comp_embCast {K a : ℕ} (e : Fin a → Fin K) (m : Fin K → Fin n) (v : Fin n) :
    (Fin.snoc m v : Fin (K + 1) → Fin n) ∘ embCast e = m ∘ e := by
  funext i
  show (Fin.snoc m v : Fin (K + 1) → Fin n) ((e i).castSucc) = m (e i)
  rw [Fin.snoc_castSucc]

/-! ### Farness one rank level in

The far-apart hypothesis is re-established for the extended split at the
smaller radius ρ⁻(k+1, q−1): the old variables keep it because ρ⁻ grows
along the antidiagonal, and the newly bound variable keeps it because it
sits within the guard radius ρ⁺(k+1, q−1) of the block it was guarded
from, and ρ⁺(k+1, q−1) + ρ⁻(k+1, q−1) ≤ ρ⁻(k, q).
-/

/-- Farness of the extended split when the bound variable is guarded
from the first block. -/
theorem far_embSnoc_embCast {K a b k q r : ℕ} {m : Fin K → Fin n} {e₁ : Fin a → Fin K}
    {e₂ : Fin b → Fin K} {v : Fin n} {i₀ : Fin a}
    (hfar : ∀ i j, ¬ WithinDist G (rhoMinus k (q + 1)) (m (e₁ i)) (m (e₂ j)))
    (hr : r ≤ rhoPlus (k + 1) q) (hv : WithinDist G r (m (e₁ i₀)) v) :
    ∀ (i : Fin (a + 1)) (j : Fin b),
      ¬ WithinDist G (rhoMinus (k + 1) q)
        ((Fin.snoc m v : Fin (K + 1) → Fin n) (embSnoc e₁ i))
        ((Fin.snoc m v : Fin (K + 1) → Fin n) (embCast e₂ j)) := by
  intro i j
  rw [embCast_apply, Fin.snoc_castSucc]
  induction i using Fin.lastCases with
  | last =>
    rw [embSnoc_last, Fin.snoc_last]
    intro hc
    refine hfar i₀ j (withinDist_mono_radius ?_ (withinDist_trans hv hc))
    have := rhoPlus_add_rhoMinus_le k q
    omega
  | cast i' =>
    rw [embSnoc_castSucc, Fin.snoc_castSucc]
    exact fun hc => hfar i' j (withinDist_mono_radius (rhoMinus_succ_left_le k q) hc)

/-- Farness of the extended split when the bound variable is guarded
from the second block. -/
theorem far_embCast_embSnoc {K a b k q r : ℕ} {m : Fin K → Fin n} {e₁ : Fin a → Fin K}
    {e₂ : Fin b → Fin K} {v : Fin n} {j₀ : Fin b}
    (hfar : ∀ i j, ¬ WithinDist G (rhoMinus k (q + 1)) (m (e₁ i)) (m (e₂ j)))
    (hr : r ≤ rhoPlus (k + 1) q) (hv : WithinDist G r (m (e₂ j₀)) v) :
    ∀ (i : Fin a) (j : Fin (b + 1)),
      ¬ WithinDist G (rhoMinus (k + 1) q)
        ((Fin.snoc m v : Fin (K + 1) → Fin n) (embCast e₁ i))
        ((Fin.snoc m v : Fin (K + 1) → Fin n) (embSnoc e₂ j)) := by
  intro i j
  rw [embCast_apply, Fin.snoc_castSucc]
  induction j using Fin.lastCases with
  | last =>
    rw [embSnoc_last, Fin.snoc_last]
    intro hc
    refine hfar i j₀ (withinDist_mono_radius ?_ (withinDist_trans hc (withinDist_symm hv)))
    have := rhoPlus_add_rhoMinus_le k q
    omega
  | cast j' =>
    rw [embSnoc_castSucc, Fin.snoc_castSucc]
    exact fun hc => hfar i j' (withinDist_mono_radius (rhoMinus_succ_left_le k q) hc)

/-! ### The separation predicate -/

/-- `Separates k q φ e₁ e₂ P` says that the list of pairs `P` separates
`φ` along the split `(e₁, e₂)` at distance rank `(k, q)`: every entry of
`P` is a pair of local formulas of that rank, one per side, and whenever
the two blocks are further than ρ⁻(k, q) apart, `φ` holds exactly when
some entry of `P` holds, each side read in its own reindexed
environment. -/
def Separates {L K a b : ℕ} (k q : ℕ) (φ : DistFO L K) (e₁ : Fin a → Fin K)
    (e₂ : Fin b → Fin K) (P : List (DistFO L a × DistFO L b)) : Prop :=
  (∀ p ∈ P, IsLocal p.1 ∧ DRank k q p.1 ∧ IsLocal p.2 ∧ DRank k q p.2) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin K → Fin n),
      (∀ i j, ¬ WithinDist G (rhoMinus k q) (m (e₁ i)) (m (e₂ j))) →
      (Sat G col m φ ↔ ∃ p ∈ P, Sat G col (m ∘ e₁) p.1 ∧ Sat G col (m ∘ e₂) p.2)

/-- A formula living entirely on the first block separates as the single
pair `(α, x₀ = x₀)`. -/
theorem exists_separates_left {K a b k q : ℕ} {φ : DistFO L K} {e₁ : Fin a → Fin K}
    {e₂ : Fin b → Fin K} (hb : 1 ≤ b) {α : DistFO L a} (hlocα : IsLocal α)
    (hrankα : DRank k q α)
    (h : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin K → Fin n),
      Sat G col m φ ↔ Sat G col (m ∘ e₁) α) :
    ∃ P, Separates k q φ e₁ e₂ P := by
  refine ⟨[(α, alwaysTrue hb)], ?_, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨hlocα, hrankα, isLocal_alwaysTrue hb, drank_alwaysTrue hb k q⟩
  · intro n G col m _
    rw [h n G col m]
    constructor
    · exact fun hs => ⟨(α, alwaysTrue hb), List.mem_singleton.mpr rfl, hs, sat_alwaysTrue⟩
    · rintro ⟨p, hp, hp1, -⟩
      simp only [List.mem_singleton] at hp
      subst hp
      exact hp1

/-- A formula living entirely on the second block separates as the
single pair `(x₀ = x₀, β)`. -/
theorem exists_separates_right {K a b k q : ℕ} {φ : DistFO L K} {e₁ : Fin a → Fin K}
    {e₂ : Fin b → Fin K} (ha : 1 ≤ a) {β : DistFO L b} (hlocβ : IsLocal β)
    (hrankβ : DRank k q β)
    (h : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin K → Fin n),
      Sat G col m φ ↔ Sat G col (m ∘ e₂) β) :
    ∃ P, Separates k q φ e₁ e₂ P := by
  refine ⟨[(alwaysTrue ha, β)], ?_, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨isLocal_alwaysTrue ha, drank_alwaysTrue ha k q, hlocβ, hrankβ⟩
  · intro n G col m _
    rw [h n G col m]
    constructor
    · exact fun hs => ⟨(alwaysTrue ha, β), List.mem_singleton.mpr rfl, sat_alwaysTrue, hs⟩
    · rintro ⟨p, hp, -, hp2⟩
      simp only [List.mem_singleton] at hp
      subst hp
      exact hp2

/-- A formula that the far-apart hypothesis refutes separates as the
empty disjunction. -/
theorem exists_separates_nil {K a b k q : ℕ} {φ : DistFO L K} {e₁ : Fin a → Fin K}
    {e₂ : Fin b → Fin K}
    (h : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin K → Fin n),
      (∀ i j, ¬ WithinDist G (rhoMinus k q) (m (e₁ i)) (m (e₂ j))) → ¬ Sat G col m φ) :
    ∃ P, Separates k q φ e₁ e₂ P := by
  refine ⟨[], ?_, ?_⟩
  · intro p hp
    simp at hp
  · intro n G col m hfar
    constructor
    · exact fun hs => absurd hs (h n G col m hfar)
    · rintro ⟨p, hp, -⟩
      simp at hp

/-! ### The separation lemma -/

/-- The side reading of a guard set: the variables of that side whose
image the guard set names. It is well defined as a preimage because a
side embedding is injective. -/
noncomputable def sidePreimage {a K : ℕ} (g : Finset (Fin K)) (e : Fin a → Fin K)
    (h : Function.Injective e) : Finset (Fin a) :=
  g.preimage e h.injOn

/-- Membership in the side reading of a guard set. -/
theorem mem_sidePreimage {a K : ℕ} {g : Finset (Fin K)} {e : Fin a → Fin K}
    {h : Function.Injective e} {i : Fin a} : i ∈ sidePreimage g e h ↔ e i ∈ g :=
  Finset.mem_preimage

/-- The induction behind `separate`, with the split, the rank and the
far-apart hypothesis quantified inside so that the induction hypothesis
is available at the extended split and the smaller rank of a body. -/
private theorem exists_separates {L : ℕ} :
    ∀ {K : ℕ} (φ : DistFO L K) (k q : ℕ) {a b : ℕ} (e₁ : Fin a → Fin K) (e₂ : Fin b → Fin K),
      IsLocal φ → DRank k q φ → 1 ≤ a → 1 ≤ b →
      Function.Injective e₁ → Function.Injective e₂ →
      (∀ i j, e₁ i ≠ e₂ j) → (∀ v, (∃ i, e₁ i = v) ∨ (∃ j, e₂ j = v)) →
      ∃ P, Separates k q φ e₁ e₂ P := by
  intro K φ
  induction φ with
  | adj i j =>
    intro k q a b e₁ e₂ _ _ ha hb _ _ _ hcov
    rcases hcov i with ⟨i₀, hi₀⟩ | ⟨j₀, hj₀⟩
    · subst hi₀
      rcases hcov j with ⟨i₁, hi₁⟩ | ⟨j₁, hj₁⟩
      · subst hi₁
        exact exists_separates_left hb (isLocal_adj i₀ i₁) (.adj i₀ i₁) fun _ _ _ _ => Iff.rfl
      · subst hj₁
        refine exists_separates_nil (k := k) (q := q) fun _ _ _ m hfar hs => ?_
        exact hfar i₀ j₁ (withinDist_mono_radius (one_le_rhoMinus k q) (withinDist_of_adj hs))
    · subst hj₀
      rcases hcov j with ⟨i₁, hi₁⟩ | ⟨j₁, hj₁⟩
      · subst hi₁
        refine exists_separates_nil (k := k) (q := q) fun _ _ _ m hfar hs => ?_
        exact hfar i₁ j₀ (withinDist_mono_radius (one_le_rhoMinus k q)
          (withinDist_symm (withinDist_of_adj hs)))
      · subst hj₁
        exact exists_separates_right ha (isLocal_adj j₀ j₁) (.adj j₀ j₁) fun _ _ _ _ => Iff.rfl
  | eq i j =>
    intro k q a b e₁ e₂ _ _ ha hb _ _ _ hcov
    rcases hcov i with ⟨i₀, hi₀⟩ | ⟨j₀, hj₀⟩
    · subst hi₀
      rcases hcov j with ⟨i₁, hi₁⟩ | ⟨j₁, hj₁⟩
      · subst hi₁
        exact exists_separates_left hb (isLocal_eq i₀ i₁) (.eq i₀ i₁) fun _ _ _ _ => Iff.rfl
      · subst hj₁
        refine exists_separates_nil (k := k) (q := q) fun _ G _ m hfar hs => ?_
        exact hfar i₀ j₁ (withinDist_of_eq G _ hs)
    · subst hj₀
      rcases hcov j with ⟨i₁, hi₁⟩ | ⟨j₁, hj₁⟩
      · subst hi₁
        refine exists_separates_nil (k := k) (q := q) fun _ G _ m hfar hs => ?_
        exact hfar i₁ j₀ (withinDist_of_eq G _ hs.symm)
      · subst hj₁
        exact exists_separates_right ha (isLocal_eq j₀ j₁) (.eq j₀ j₁) fun _ _ _ _ => Iff.rfl
  | color c i =>
    intro k q a b e₁ e₂ _ _ ha hb _ _ _ hcov
    rcases hcov i with ⟨i₀, hi₀⟩ | ⟨j₀, hj₀⟩
    · subst hi₀
      exact exists_separates_left hb (isLocal_color c i₀) (.color c i₀) fun _ _ _ _ => Iff.rfl
    · subst hj₀
      exact exists_separates_right ha (isLocal_color c j₀) (.color c j₀) fun _ _ _ _ => Iff.rfl
  | distLe r i j =>
    intro k q a b e₁ e₂ _ hrank ha hb _ _ _ hcov
    have hr := le_rhoMinus_of_distLe hrank
    rcases hcov i with ⟨i₀, hi₀⟩ | ⟨j₀, hj₀⟩
    · subst hi₀
      rcases hcov j with ⟨i₁, hi₁⟩ | ⟨j₁, hj₁⟩
      · subst hi₁
        exact exists_separates_left hb (isLocal_distLe r i₀ i₁) (.distLe i₀ i₁ hr)
          fun _ _ _ _ => Iff.rfl
      · subst hj₁
        refine exists_separates_nil (k := k) (q := q) fun _ _ _ m hfar hs => ?_
        exact hfar i₀ j₁ (withinDist_mono_radius hr hs)
    · subst hj₀
      rcases hcov j with ⟨i₁, hi₁⟩ | ⟨j₁, hj₁⟩
      · subst hi₁
        refine exists_separates_nil (k := k) (q := q) fun _ _ _ m hfar hs => ?_
        exact hfar i₁ j₀ (withinDist_mono_radius hr (withinDist_symm hs))
      · subst hj₁
        exact exists_separates_right ha (isLocal_distLe r j₀ j₁) (.distLe j₀ j₁ hr)
          fun _ _ _ _ => Iff.rfl
  | distColorLt r c i =>
    intro k q a b e₁ e₂ _ hrank ha hb _ _ _ hcov
    have hr := le_rhoMinus_of_distColorLt hrank
    rcases hcov i with ⟨i₀, hi₀⟩ | ⟨j₀, hj₀⟩
    · subst hi₀
      exact exists_separates_left hb (isLocal_distColorLt r c i₀) (.distColorLt c i₀ hr)
        fun _ _ _ _ => Iff.rfl
    · subst hj₀
      exact exists_separates_right ha (isLocal_distColorLt r c j₀) (.distColorLt c j₀ hr)
        fun _ _ _ _ => Iff.rfl
  | not ψ ih =>
    intro k q a b e₁ e₂ hloc hrank ha hb h₁ h₂ hdis hcov
    obtain ⟨P, hP1, hP2⟩ :=
      ih k q e₁ e₂ ((isLocal_not ψ).mp hloc) (drank_of_not hrank) ha hb h₁ h₂ hdis hcov
    refine ⟨negPairs ha hb P, drank_negPairs ha hb P hP1, ?_⟩
    intro n G col m hfar
    rw [sat_not, hP2 n G col m hfar, sat_negPairs ha hb (m ∘ e₁) (m ∘ e₂) P]
    constructor
    · exact fun h p hp hx => h ⟨p, hp, hx⟩
    · rintro h ⟨p, hp, hx⟩
      exact h p hp hx
  | and ψ χ ihψ ihχ =>
    intro k q a b e₁ e₂ hloc hrank ha hb h₁ h₂ hdis hcov
    obtain ⟨P, hP1, hP2⟩ := ihψ k q e₁ e₂ ((isLocal_and ψ χ).mp hloc).1
      (drank_of_and_left hrank) ha hb h₁ h₂ hdis hcov
    obtain ⟨Q, hQ1, hQ2⟩ := ihχ k q e₁ e₂ ((isLocal_and ψ χ).mp hloc).2
      (drank_of_and_right hrank) ha hb h₁ h₂ hdis hcov
    refine ⟨prodPairs P Q, drank_prodPairs P Q hP1 hQ1, ?_⟩
    intro n G col m hfar
    rw [sat_and, hP2 n G col m hfar, hQ2 n G col m hfar]
    exact (sat_prodPairs (m ∘ e₁) (m ∘ e₂) P Q).symm
  | exU ψ _ =>
    intro _ _ _ _ _ _ hloc _ _ _ _ _ _ _
    exact absurd hloc (isLocal_exU ψ).mp
  | exL r g ψ ih =>
    intro k q a b e₁ e₂ hloc hrank ha hb h₁ h₂ hdis hcov
    obtain ⟨q', rfl, hψ, hr⟩ := exists_drank_of_exL hrank
    have hlocψ : IsLocal ψ := (isLocal_exL r g ψ).mp hloc
    obtain ⟨QA, hQA1, hQA2⟩ := ih (k + 1) q' (embSnoc e₁) (embCast e₂) hlocψ hψ
      (by omega) hb (injective_embSnoc h₁) (injective_embCast h₂)
      (embSnoc_ne_embCast hdis) (cover_embSnoc_embCast hcov)
    obtain ⟨QB, hQB1, hQB2⟩ := ih (k + 1) q' (embCast e₁) (embSnoc e₂) hlocψ hψ
      ha (by omega) (injective_embCast h₁) (injective_embSnoc h₂)
      (embCast_ne_embSnoc hdis) (cover_embCast_embSnoc hcov)
    refine ⟨wrapLeft r (sidePreimage g e₁ h₁) QA ++ wrapRight r (sidePreimage g e₂ h₂) QB,
      ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · simp only [wrapLeft, List.mem_map] at hp
        obtain ⟨c, hc, rfl⟩ := hp
        obtain ⟨hc1, hc2, hc3, hc4⟩ := hQA1 c hc
        exact ⟨hc1, .exL hc2 hr, hc3, DRank.antidiagonal hc4⟩
      · simp only [wrapRight, List.mem_map] at hp
        obtain ⟨c, hc, rfl⟩ := hp
        obtain ⟨hc1, hc2, hc3, hc4⟩ := hQB1 c hc
        exact ⟨hc1, DRank.antidiagonal hc2, hc3, .exL hc4 hr⟩
    · intro n G col m hfar
      constructor
      · intro hs
        rw [sat_exL] at hs
        obtain ⟨v, ⟨i, hig, hiv⟩, hsat⟩ := hs
        rcases hcov i with ⟨i₀, hi₀⟩ | ⟨j₀, hj₀⟩
        · subst hi₀
          rw [hQA2 n G col (Fin.snoc m v) (far_embSnoc_embCast hfar hr hiv),
            snoc_comp_embSnoc, snoc_comp_embCast] at hsat
          obtain ⟨c, hc, hc1, hc2⟩ := hsat
          refine ⟨(.exL r (sidePreimage g e₁ h₁) c.1, c.2),
            List.mem_append_left _ ?_, ?_, hc2⟩
          · simp only [wrapLeft, List.mem_map]
            exact ⟨c, hc, rfl⟩
          · exact ⟨v, ⟨i₀, mem_sidePreimage.mpr hig, hiv⟩, hc1⟩
        · subst hj₀
          rw [hQB2 n G col (Fin.snoc m v) (far_embCast_embSnoc hfar hr hiv),
            snoc_comp_embCast, snoc_comp_embSnoc] at hsat
          obtain ⟨c, hc, hc1, hc2⟩ := hsat
          refine ⟨(c.1, .exL r (sidePreimage g e₂ h₂) c.2),
            List.mem_append_right _ ?_, hc1, ?_⟩
          · simp only [wrapRight, List.mem_map]
            exact ⟨c, hc, rfl⟩
          · exact ⟨v, ⟨j₀, mem_sidePreimage.mpr hig, hiv⟩, hc2⟩
      · rintro ⟨p, hp, hp1, hp2⟩
        rcases List.mem_append.mp hp with hp | hp
        · simp only [wrapLeft, List.mem_map] at hp
          obtain ⟨c, hc, rfl⟩ := hp
          obtain ⟨v, ⟨i₀, hi₀g, hi₀v⟩, hc1⟩ := hp1
          refine ⟨v, ⟨e₁ i₀, mem_sidePreimage.mp hi₀g, hi₀v⟩, ?_⟩
          rw [hQA2 n G col (Fin.snoc m v) (far_embSnoc_embCast hfar hr hi₀v),
            snoc_comp_embSnoc, snoc_comp_embCast]
          exact ⟨c, hc, hc1, hp2⟩
        · simp only [wrapRight, List.mem_map] at hp
          obtain ⟨c, hc, rfl⟩ := hp
          obtain ⟨v, ⟨j₀, hj₀g, hj₀v⟩, hc2⟩ := hp2
          refine ⟨v, ⟨e₂ j₀, mem_sidePreimage.mp hj₀g, hj₀v⟩, ?_⟩
          rw [hQB2 n G col (Fin.snoc m v) (far_embCast_embSnoc hfar hr hj₀v),
            snoc_comp_embCast, snoc_comp_embSnoc]
          exact ⟨c, hc, hp1, hc2⟩

/-- **The separation lemma** (the source's `lem:far-ltp`). A local
formula of distance rank `(k, q)` whose variables are split into two
blocks — two injections with disjoint images covering the context — is,
whenever the two blocks lie further apart than ρ⁻(k, q), equivalent to a
finite disjunction of conjunctions `α(x̄) ∧ β(ȳ)` of local formulas of
distance rank `(k, q)`, each side written in its own reindexed context.
Both blocks are assumed nonempty, which is what lets a formula about one
block be paired with an always-true formula about the other. -/
theorem separate {L K a b k q : ℕ} (φ : DistFO L K) (hloc : IsLocal φ)
    (hφ : DRank k q φ) (ha : 1 ≤ a) (hb : 1 ≤ b) (e₁ : Fin a → Fin K) (e₂ : Fin b → Fin K)
    (h₁ : Function.Injective e₁) (h₂ : Function.Injective e₂)
    (hdis : ∀ i j, e₁ i ≠ e₂ j) (hcov : ∀ v, (∃ i, e₁ i = v) ∨ (∃ j, e₂ j = v)) :
    ∃ P : List (DistFO L a × DistFO L b),
      (∀ p ∈ P, IsLocal p.1 ∧ DRank k q p.1 ∧ IsLocal p.2 ∧ DRank k q p.2) ∧
      ∀ n (G : SimpleGraph (Fin n)) col (m : Fin K → Fin n),
        (∀ i j, ¬ WithinDist G (rhoMinus k q) (m (e₁ i)) (m (e₂ j))) →
        (Sat G col m φ ↔ ∃ p ∈ P, Sat G col (m ∘ e₁) p.1 ∧ Sat G col (m ∘ e₂) p.2) :=
  exists_separates φ k q e₁ e₂ hloc hφ ha hb h₁ h₂ hdis hcov

end Lax3Proofs.Separation
