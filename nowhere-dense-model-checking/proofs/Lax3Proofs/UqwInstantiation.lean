import Lax12.NowhereDenseUQW
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
**`hQ`, the mathematics of the campaign, derived.**

`RamDriverRoot.driverRoot_decides_sentence` carries exactly one
hypothesis that is not about the machine: uniform quasi-wideness of the
arena at radius `2 · cap`, together with `hℓ : ℓ = N (2 s + 2)` fixing
the round budget. This file produces both from Lax12's endorsed theorem
that nowhere dense classes are uniformly quasi-wide.

# The statement

`SplitterMargin` is the driver's `hQ` verbatim: for every point set `Pt`
of at least `N (2 s + 2)` vertices there is a separator `S` of at most
`s` vertices and a set `Bd ⊆ Pt \ S` of at least `2 s + 2` vertices that
is distance-`2 · cap` independent in `G − S`.

Two things about its shape are load-bearing, and both are inherited from
`Lax12.UniformQuasiWideness.UniformlyQuasiWide` rather than chosen here.

* **The quantifier order.** `N` and `s` are produced *before* the member
  `G` — they depend on the class and the radius alone. They have to be:
  the driver's round budget `ℓ = N (2 s + 2)` and the recursion depth are
  compiled into the program text, which is one program for the whole
  class.
* **The self-reference in `N (2 s + 2)`.** The requested independent-set
  size is `2 s + 2`, two more than twice the separator bound the same
  quantifier produced. This is the splitter game's own arithmetic — a
  batch of `2 s + 2` vertices survives a round in which Splitter deletes
  at most `s` — and it is legitimate because uniform quasi-wideness fixes
  `s` uniformly in the requested size, so `s` may be read off first and
  the size chosen afterwards. On a merely *quasi*-wide class, where `s`
  is allowed to depend on the requested size, this instantiation does not
  exist; that uniformity is the whole content of the "uniform".

# The vocabulary is shared

`DistIndependent` and `deleteVerts` in the driver's `hQ` are Lax12's own:
`Lax3.SplitterGame` and `Lax3.ScatterSentences` import
`Lax12.UniformQuasiWideness` and use its definitions unchanged, so no
bridging lemma is needed and none is proved here. Both live at
`Type*`-generality in Lax12 and are used at `Fin n` on both sides.

# What enters the dependency cone

One endorsed Lax12 axiom, by design:
`Lax12.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense`. It is the
hard direction of the source's Theorem 3.2 and is exactly the interface
this campaign was built to consume.

# Falsification gate

The authored statement is `SplitterMargin`, and the check that matters
is that the separator is load-bearing: `not_distIndependent_star` refutes
the variant with `S` dropped, on the three-vertex star — a tree, hence a
member of a nowhere dense class — where every two-element subset of the
vertex set has a walk of length at most `2` between two of its members,
so no `Bd` of size `2` is distance-`2` independent in `G` itself. The
deletion in `deleteVerts G S` is therefore not decoration.
-/

namespace Lax3Proofs.UqwInstantiation

open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.UniformQuasiWideness

/-! ### The driver's hypothesis, named -/

/-- **`hQ`**: the driver's campaign hypothesis, verbatim. Every point set
of at least `N (2 s + 2)` vertices has a separator of at most `s`
vertices after which it still contains `2 s + 2` vertices pairwise more
than `2 · cap` apart. -/
def SplitterMargin {n : ℕ} (G : SimpleGraph (Fin n)) (N : ℕ → ℕ) (s cap : ℕ) : Prop :=
  ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
    ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
      DistIndependent (deleteVerts G S) (2 * cap) Bd

/-! ### The derivation -/

/-- **The campaign's mathematics, from Lax12.** On a nowhere dense class
and at every locality radius `cap` there are a threshold function `N` and
a separator bound `s`, depending on the class and the radius alone, such
that every member satisfies the driver's `hQ`.

This is `Lax12.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense` at the
radius `2 · cap` and the requested size `2 s + 2`. -/
theorem hQ_of_nowhereDense (C : GraphClass) (hC : NowhereDense C) (cap : ℕ) :
    ∃ (N : ℕ → ℕ) (s : ℕ),
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → SplitterMargin G N s cap := by
  obtain ⟨N, s, h⟩ := Lax12.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense C hC (2 * cap)
  exact ⟨N, s, fun n G hG Pt hPt => h (2 * s + 2) n G hG Pt hPt⟩

/-- **The same, with the round budget named.** The driver takes `hℓ : ℓ =
N (2 s + 2)` alongside `hQ`; this is the pair, with `ℓ` existentially
quantified and the defining equation carried. -/
theorem exists_roundBudget (C : GraphClass) (hC : NowhereDense C) (cap : ℕ) :
    ∃ (N : ℕ → ℕ) (s ℓ : ℕ), ℓ = N (2 * s + 2) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → SplitterMargin G N s cap := by
  obtain ⟨N, s, h⟩ := hQ_of_nowhereDense C hC cap
  exact ⟨N, s, N (2 * s + 2), rfl, h⟩

/-- **The flat form**: the round budget as the only threshold. A consumer
that has already fixed `ℓ` reads `hQ` as "every point set of at least `ℓ`
vertices splits", which is how `RamDriverCluster.levelImplements` uses it
after `hℓ` is substituted. -/
theorem exists_flat_margin (C : GraphClass) (hC : NowhereDense C) (cap : ℕ) :
    ∃ (s ℓ : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ Pt : Set (Fin n), ℓ ≤ Pt.ncard →
        ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
          DistIndependent (deleteVerts G S) (2 * cap) Bd := by
  obtain ⟨N, s, ℓ, hℓ, h⟩ := exists_roundBudget C hC cap
  exact ⟨s, ℓ, fun n G hG Pt hPt => h n G hG Pt (hℓ ▸ hPt)⟩

/-- Monotonicity in the point set: a larger `Pt` still splits, since the
threshold is a lower bound on its size. Stated for the consumer that
enlarges the arena between rounds. -/
theorem SplitterMargin.mono {n : ℕ} {G : SimpleGraph (Fin n)} {N : ℕ → ℕ} {s cap : ℕ}
    (h : SplitterMargin G N s cap) {Pt Pt' : Set (Fin n)} (hsub : Pt ⊆ Pt')
    (hPt : N (2 * s + 2) ≤ Pt.ncard) :
    ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt' \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
      DistIndependent (deleteVerts G S) (2 * cap) Bd := by
  obtain ⟨S, Bd, hS, hBd, hcard, hind⟩ := h Pt hPt
  exact ⟨S, Bd, hS, hBd.trans (Set.diff_subset_diff_left hsub), hcard, hind⟩

/-! ### Falsification: the separator is load-bearing

The one authored shape is `SplitterMargin`, and the reading it must not
have is the one without `S`. The three-vertex star `0 — 1 — 2` is a tree,
so it belongs to nowhere dense classes, and its whole vertex set has
`ncard 3`; but any two of its vertices are joined by a walk of length at
most `2`, so it contains no distance-`2` independent set of size `2` at
all. Deleting the centre — which is what `deleteVerts G S` with `S = {1}`
does — is exactly what makes `{0, 2}` distance-`2` independent. -/

section Falsification

/-- The three-vertex star with centre `1`. -/
def star3 : SimpleGraph (Fin 3) where
  Adj u v := (u = 1 ∧ v ≠ 1) ∨ (v = 1 ∧ u ≠ 1)
  symm := by
    intro u v h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
  loopless := ⟨by
    intro v h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact h2 h1⟩

/-- Every two distinct vertices of the star are joined by a walk of
length at most `2`: adjacent ones directly, the two leaves through the
centre. -/
theorem star3_walk (u v : Fin 3) (huv : u ≠ v) : ∃ p : star3.Walk u v, p.length ≤ 2 := by
  by_cases hu : u = 1
  · subst hu
    exact ⟨(SimpleGraph.Adj.toWalk (Or.inl ⟨rfl, fun h => huv h.symm⟩)), by simp⟩
  · by_cases hv : v = 1
    · subst hv
      exact ⟨(SimpleGraph.Adj.toWalk (Or.inr ⟨rfl, hu⟩)), by simp⟩
    · refine ⟨SimpleGraph.Walk.cons (Or.inr ⟨rfl, hu⟩)
        (SimpleGraph.Adj.toWalk (Or.inl ⟨rfl, hv⟩)), by simp⟩

/-- **Refuted**: without the separator there is no margin. No two-element
subset of the star's vertex set is distance-`2` independent, so the
variant of `SplitterMargin` that asks for `DistIndependent G (2 * cap) Bd`
instead of `DistIndependent (deleteVerts G S) (2 * cap) Bd` is false at
`cap = 1` for every threshold and every separator bound. -/
theorem not_distIndependent_star (Bd : Set (Fin 3)) (h : 2 ≤ Bd.ncard) :
    ¬ DistIndependent star3 2 Bd := by
  intro hind
  obtain ⟨u, hu, v, hv, huv⟩ := (Set.one_lt_ncard (Set.toFinite Bd)).1 h
  obtain ⟨p, hp⟩ := star3_walk u v huv
  exact absurd (hind hu hv huv p) (by omega)

/-- And the separator repairs it: deleting the centre makes the two
leaves distance-`2` independent, so the margin itself is not vacuous on
this graph. -/
theorem distIndependent_star_deleteVerts :
    DistIndependent (deleteVerts star3 {1}) 2 ({0, 2} : Set (Fin 3)) := by
  have hbot : ∀ u v : Fin 3, ¬ (deleteVerts star3 {1}).Adj u v := by
    intro u v h
    obtain ⟨hadj, hu, hv⟩ := h
    rcases hadj with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hu (by simpa using h1)
    · exact hv (by simpa using h1)
  intro u _ v _ huv p
  cases p with
  | nil => exact absurd rfl huv
  | cons h _ => exact absurd h (hbot _ _)

-- the arithmetic of the self-reference, on the smallest margins
#guard 2 * 0 + 2 = 2
#guard 2 * 3 + 2 = 8

end Falsification

end Lax3Proofs.UqwInstantiation
