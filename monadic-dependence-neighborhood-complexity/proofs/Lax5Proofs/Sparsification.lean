import Lax5.Transductions
import Lax5Proofs.SetSystems
import Mathlib.ModelTheory.Graph
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
The sparsification invariant of DMMPT26 Appendix A, together with the
R1 definability encoding, and the statements of the sparsification step
(Lemma 25) and its iteration (Lemma 26).

A `k`-sparsification of the pair `(A, B)` in a graph `G` keeps a
restricted core `A₀ ⊆ A`, a surviving side `B₀ ⊆ B`, and `k` labelling
functions `f j : B₀ → A` such that a vertex of `B₀` is determined by
its neighborhood trace on the core together with its label tuple. The
associated partition of the paper is the fiber partition of the tuple
map `b ↦ (f 0 b, …, f (k-1) b)`; parts are indexed by label tuples
throughout, so no partition structure is ever materialized.

# The R1 encoding

The paper tracks *complexity*: the labelling functions are definable by
formulas of quantifier rank `≤ c` over some expansion by `c` unary
predicates, and Lemma 23 then needs "finitely many formulas of rank
`≤ c` up to equivalence" to guess the defining tuple. Instead, the
defining formulas are produced *explicitly*, by recursion on `k`
(`sparsFormulas`): step `j` speaks about five fresh unary predicates —
the new core `A₁`, the target set `A₁'`, the new support `B₁`, the
untwinned representatives `B*`, and a sign flag `S` — and otherwise
only about the adjacency relation and the earlier formulas. The sign
of the merge direction is read off the emptiness of `S`, so for each
`k` there is exactly *one* formula tuple, and the transduction of
Lemma 23 has nothing to guess. `Definable` states that the labelling
functions of a sparsification are realized by this fixed tuple under
*some* choice of the `5k` color sets.

The intended color semantics (established when Lemma 25's proof
discharges the definability clause): with `b` free variable `0` and `a`
free variable `1`, the step formula says — `b ∈ B₁`, `a ∈ A₁'`, and
there is `b' ∈ B*` in the same part as `b` (equal earlier labels,
expressed by the earlier formulas) whose trace on `A₁` agrees with that
of `b` off `a` and differs at `a` in the direction prescribed by the
sign flag; `a` is then the unique merge-neighbor of `b` selected by the
sampling step, i.e. `f_{k+1} b = a`.
-/

namespace Lax5Proofs

open FirstOrder Lax5.Transductions

variable {n : ℕ}

/-- The neighborhood trace of `b` on `X`: the vertices of `X` adjacent
to `b`, as a finset. -/
noncomputable def trace (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (b : Fin n) : Finset (Fin n) :=
  letI := Classical.decRel G.Adj
  X.filter (G.Adj b)

/-- A `k`-sparsification of the pair `(A, B)` in `G` (DMMPT26,
Appendix A): a core `A₀ ⊆ A`, a support `B₀ ⊆ B`, and `k` labelling
functions into `A` such that every vertex of the support is determined
by its trace on the core together with its label tuple. -/
structure Sparsification (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (k : ℕ) where
  /-- The restricted core `A₀` on which traces are compared. -/
  core : Finset (Fin n)
  core_subset : core ⊆ A
  /-- The surviving side `B₀`. -/
  supp : Finset (Fin n)
  supp_subset : supp ⊆ B
  /-- The labelling functions `f 1, …, f k : B₀ → A` (total maps whose
  values matter only on `supp`). -/
  f : Fin k → Fin n → Fin n
  f_mem : ∀ (j : Fin k), ∀ b ∈ supp, f j b ∈ A
  /-- Trace on the core plus label tuple determine the vertex. -/
  inj : ∀ b ∈ supp, ∀ b' ∈ supp,
    trace G core b = trace G core b' → (∀ j, f j b = f j b') → b = b'

namespace Sparsification

variable {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)} {k : ℕ}

/-- The label tuple of `b`. -/
def tup (S : Sparsification G A B k) (b : Fin n) : Fin k → Fin n :=
  fun j => S.f j b

/-- The part of the associated partition with label tuple `τ`. -/
def part (S : Sparsification G A B k) (τ : Fin k → Fin n) :
    Finset (Fin n) :=
  S.supp.filter fun b => S.tup b = τ

/-- The set system a part induces on the core. -/
noncomputable def partTraces (S : Sparsification G A B k)
    (τ : Fin k → Fin n) : Finset (Finset (Fin n)) :=
  (S.part τ).image (trace G S.core)

/-- The label tuples realized on the support: the index set of the
associated partition. -/
def labels (S : Sparsification G A B k) : Finset (Fin k → Fin n) :=
  S.supp.image S.tup

/-- The size of the sparsification. -/
def size (S : Sparsification G A B k) : ℕ := S.supp.card

/-- The number of parts of the associated partition. -/
def partsCount (S : Sparsification G A B k) : ℕ := S.labels.card

/-- A sparsification is terminal if its size is at most twice the
number of parts. -/
def Terminal (S : Sparsification G A B k) : Prop :=
  S.size ≤ 2 * S.partsCount

/-- The dimension of the sparsification is at most `d`: every part
induces a set system of VC dimension at most `d` on the core. -/
def DimLE (S : Sparsification G A B k) (d : ℕ) : Prop :=
  ∀ b ∈ S.supp, (S.partTraces (S.tup b)).vcDim ≤ d

/-- Within a part, traces on the core are pairwise distinct, so a part
has exactly as many traces as vertices. -/
theorem card_partTraces (S : Sparsification G A B k)
    (τ : Fin k → Fin n) :
    (S.partTraces τ).card = (S.part τ).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  obtain ⟨hxs, hxt⟩ := Finset.mem_filter.1 hx
  obtain ⟨hys, hyt⟩ := Finset.mem_filter.1 hy
  exact S.inj x hxs y hys hxy fun j => by
    have := hxt.trans hyt.symm
    exact congrFun this j

/-- The trivial `0`-sparsification of a twin-free pair. -/
def trivial (htf : ∀ b ∈ B, ∀ b' ∈ B, trace G A b = trace G A b' → b = b') :
    Sparsification G A B 0 where
  core := A
  core_subset := Finset.Subset.refl A
  supp := B
  supp_subset := Finset.Subset.refl B
  f := fun j => j.elim0
  f_mem := fun j => j.elim0
  inj := fun b hb b' hb' ht _ => htf b hb b' hb' ht

end Sparsification

/-! ## The R1 formula tuple -/

/-- Inclusion of color languages along `k ≤ k'`. -/
def colorLHom {k k' : ℕ} (h : k ≤ k') :
    colorLanguage k →ᴸ colorLanguage k' where
  onFunction := fun {m} (f : (colorLanguage k).Functions m) => f.elim
  onRelation := fun {m} (r : ColorRel k m) => match r with
    | .color i => .color (i.castLE h)

/-- Push a colored-graph formula along an inclusion of color
languages. -/
def liftFormula {k k' : ℕ} (h : k ≤ k') {β : Type*}
    (φ : (withColors Language.graph k).Formula β) :
    (withColors Language.graph k').Formula β :=
  (Language.LHom.sumMap (Language.LHom.id Language.graph)
    (colorLHom h)).onFormula φ

/-- The adjacency atom of the colored graph language. -/
def adjAtom {K m : ℕ} {β : Type*}
    (t₁ t₂ : (withColors Language.graph K).Term (β ⊕ Fin m)) :
    (withColors Language.graph K).BoundedFormula β m :=
  Language.Relations.boundedFormula₂ (Sum.inl Language.adj) t₁ t₂

/-- The `i`-th color atom of the colored graph language. -/
def colorAtom {K m : ℕ} {β : Type*} (i : Fin K)
    (t : (withColors Language.graph K).Term (β ⊕ Fin m)) :
    (withColors Language.graph K).BoundedFormula β m :=
  Language.Relations.boundedFormula₁ (Sum.inr (ColorRel.color i)) t

/-- The formula defining the labelling function added by sparsification
step `j` (`0`-indexed), given the formulas of the earlier steps. Free
variable `0` is the `B`-side vertex `b`, free variable `1` the `A`-side
vertex `a`. Step `j` owns the color slots `5j, …, 5j+4`: the new core
`A₁`, the target set `A₁'`, the new support `B₁`, the representatives
`B*`, and the sign flag `S`. -/
noncomputable def mergeFormula (j : ℕ)
    (ψ : Fin j → (withColors Language.graph (5 * j + 5)).Formula (Fin 2)) :
    (withColors Language.graph (5 * j + 5)).Formula (Fin 2) :=
  let sCore : Fin (5 * j + 5) := ⟨5 * j, by omega⟩
  let sTgt : Fin (5 * j + 5) := ⟨5 * j + 1, by omega⟩
  let sSupp : Fin (5 * j + 5) := ⟨5 * j + 2, by omega⟩
  let sReps : Fin (5 * j + 5) := ⟨5 * j + 3, by omega⟩
  let sSign : Fin (5 * j + 5) := ⟨5 * j + 4, by omega⟩
  -- `b` and `a` as terms at quantifier depth `m`
  let b : ∀ {m : ℕ}, (withColors Language.graph (5 * j + 5)).Term
      (Fin 2 ⊕ Fin m) := fun {_} => Language.Term.var (Sum.inl 0)
  let a : ∀ {m : ℕ}, (withColors Language.graph (5 * j + 5)).Term
      (Fin 2 ⊕ Fin m) := fun {_} => Language.Term.var (Sum.inl 1)
  -- inside `∃ b'` (depth 1): `b'` is `&0`
  -- equal earlier labels: for each `i < j` some `z` satisfies
  -- `ψ i (b, z)` and `ψ i (b', z)`
  let samePart : (withColors Language.graph (5 * j + 5)).BoundedFormula
      (Fin 2) 1 :=
    Language.BoundedFormula.iInf fun i : Fin j =>
      (Language.BoundedFormula.relabel
          (![Sum.inl 0, Sum.inr 1] : Fin 2 → Fin 2 ⊕ Fin 2) (ψ i) ⊓
        Language.BoundedFormula.relabel
          (![Sum.inr 0, Sum.inr 1] : Fin 2 → Fin 2 ⊕ Fin 2) (ψ i)).ex
  -- traces of `b` and `b'` agree on the new core off `a`
  let traceEqOffA : (withColors Language.graph (5 * j + 5)).BoundedFormula
      (Fin 2) 1 :=
    ((colorAtom sCore (&1) ⊓ ∼((&1).bdEqual a)) ⟹
      (adjAtom b (&1)).iff (adjAtom (&0) (&1))).all
  -- the sign flag is nonempty iff the merge is positive at `a`
  let signPos : (withColors Language.graph (5 * j + 5)).BoundedFormula
      (Fin 2) 1 :=
    (colorAtom sSign (&1)).ex
  let posCase := signPos ⟹ (adjAtom b a ⊓ ∼(adjAtom (&0) a))
  let negCase := ∼signPos ⟹ (∼(adjAtom b a) ⊓ adjAtom (&0) a)
  let inner := colorAtom sReps (&0) ⊓ samePart ⊓ traceEqOffA ⊓
    posCase ⊓ negCase
  colorAtom sSupp b ⊓ colorAtom sTgt a ⊓ inner.ex

/-- The fixed formula tuple of the R1 encoding: the formula defining
the `j`-th labelling function of a `k`-step sparsification, over the
graph language with `5k` colors. Independent of the graph and of the
sparsification — only the color sets vary. -/
noncomputable def sparsFormulas :
    (k : ℕ) → Fin k → (withColors Language.graph (5 * k)).Formula (Fin 2)
  | 0 => fun i => i.elim0
  | k + 1 => fun j =>
    if h : (j : ℕ) < k then
      liftFormula (by omega) (sparsFormulas k ⟨j, h⟩)
    else
      mergeFormula k fun i => liftFormula (by omega) (sparsFormulas k i)

/-- Realization of a lifted formula only depends on the restricted
colors. -/
theorem realizeIn_liftFormula {k k' : ℕ} (h : k ≤ k')
    (M : Language.graph.Structure (Fin n))
    (colors : Fin k' → Set (Fin n)) {β : Type*}
    (φ : (withColors Language.graph k).Formula β) (v : β → Fin n) :
    RealizeIn M colors (liftFormula h φ) v ↔
      RealizeIn M (fun i => colors (i.castLE h)) φ v := by
  letI := M
  letI := colorStructure colors
  letI := colorStructure fun i => colors (i.castLE h)
  haveI : (colorLHom h).IsExpansionOn (Fin n) :=
    ⟨fun f => f.elim, fun R x => by cases R; rfl⟩
  exact Language.LHom.realize_onFormula
    (Language.LHom.sumMap (Language.LHom.id Language.graph) (colorLHom h)) φ

namespace Sparsification

variable {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)} {k : ℕ}

/-- The sparsification is definable (R1 form): some choice of the `5k`
color sets realizes all labelling functions through the fixed formula
tuple `sparsFormulas k`. -/
def Definable (S : Sparsification G A B k) : Prop :=
  ∃ colors : Fin (5 * k) → Set (Fin n),
    ∀ j : Fin k, ∀ b ∈ S.supp, ∀ a : Fin n,
      S.f j b = a ↔
        RealizeIn G.structure colors (sparsFormulas k j) ![b, a]

/-- The trivial `0`-sparsification is definable: there is nothing to
define. -/
theorem definable_trivial
    (htf : ∀ b ∈ B, ∀ b' ∈ B, trace G A b = trace G A b' → b = b') :
    (Sparsification.trivial htf).Definable :=
  ⟨fun i => i.elim0, fun j => j.elim0⟩

end Sparsification

/-! ## Lemma 25 (step) and Lemma 26 (iterate) -/

/-- The size loss of one sparsification step, as a function of the
dimension bound `d` and the `A`-side cardinality: one application of
Lemma 19 (factor `2 ln |A| + 2`), the positive/negative split (factor
`2`), Corollary 9 (factor `d`), and Lemma 12 (factor
`150 (ln |A| + 1)`). -/
noncomputable def stepLoss (d : ℕ) (x : ℝ) : ℝ :=
  600 * (d + 1) * (Real.log x + 2) ^ 2

/-- Lemma 25 of DMMPT26: a nonterminal `k`-sparsification of dimension
at most `d` can be improved to a `(k+1)`-sparsification of dimension at
most `d - 1`, losing only a `stepLoss` factor in size and staying
definable. -/
theorem Sparsification.step {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {k d : ℕ}
    (S : Sparsification G A B k) (hd : S.DimLE d) (hnt : ¬ S.Terminal)
    (hdef : S.Definable) :
    ∃ S' : Sparsification G A B (k + 1),
      S'.DimLE (d - 1) ∧ S'.Definable ∧
      (S.size : ℝ) ≤ stepLoss d A.card * S'.size := by
  sorry

theorem one_le_stepLoss (d : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ stepLoss d x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  simp only [stepLoss]
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

theorem stepLoss_le_stepLoss {d d' : ℕ} (h : d ≤ d') {x : ℝ}
    (hx : 1 ≤ x) : stepLoss d x ≤ stepLoss d' x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hdd : (d : ℝ) ≤ (d' : ℝ) := Nat.cast_le.2 h
  simp only [stepLoss]
  nlinarith [sq_nonneg (Real.log x + 2)]

/-- A sparsification of dimension `0` is terminal: every part carries
at most one trace, hence at most one vertex. -/
theorem Sparsification.terminal_of_dimLE_zero {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {k : ℕ} (S : Sparsification G A B k)
    (h : S.DimLE 0) : S.Terminal := by
  classical
  have hsum : S.supp.card = ∑ τ ∈ S.labels, (S.part τ).card :=
    Finset.card_eq_sum_card_fiberwise fun b hb =>
      Finset.mem_image_of_mem _ hb
  have hle : ∀ τ ∈ S.labels, (S.part τ).card ≤ 1 := by
    intro τ hτ
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hτ
    calc (S.part (S.tup b)).card
        = (S.partTraces (S.tup b)).card := (S.card_partTraces _).symm
      _ ≤ 1 := SetSystems.card_le_one_of_vcDim_eq_zero
          (Nat.le_zero.1 (h b hb))
  have hcount : S.size ≤ S.partsCount := by
    show S.supp.card ≤ S.labels.card
    calc S.supp.card = ∑ τ ∈ S.labels, (S.part τ).card := hsum
      _ ≤ ∑ _τ ∈ S.labels, 1 := Finset.sum_le_sum hle
      _ = S.labels.card := by simp
  show S.size ≤ 2 * S.partsCount
  omega

/-- Iteration core of Lemma 26: from any definable sparsification of
dimension at most `d`, at most `d` applications of Lemma 25 reach a
terminal one, each costing a `stepLoss d` factor. -/
private theorem exists_terminal_of_dimLE {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} (hA : 1 ≤ A.card) :
    ∀ (d k : ℕ) (S : Sparsification G A B k), S.Definable → S.DimLE d →
      ∃ i, k ≤ i ∧ i ≤ k + d ∧ ∃ S' : Sparsification G A B i,
        S'.Definable ∧ S'.Terminal ∧
        (S.size : ℝ) ≤ stepLoss d A.card ^ d * S'.size := by
  have hx1 : (1 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA
  intro d
  induction d with
  | zero =>
    intro k S hdef hdim
    exact ⟨k, le_refl _, by omega, S, hdef,
      S.terminal_of_dimLE_zero hdim, by simp⟩
  | succ d ih =>
    intro k S hdef hdim
    have hsl1 : (1 : ℝ) ≤ stepLoss (d + 1) (A.card : ℝ) :=
      one_le_stepLoss _ hx1
    by_cases hterm : S.Terminal
    · refine ⟨k, le_refl _, by omega, S, hdef, hterm, ?_⟩
      have hpow : (1 : ℝ) ≤ stepLoss (d + 1) (A.card : ℝ) ^ (d + 1) :=
        one_le_pow₀ hsl1
      nlinarith [Nat.cast_nonneg (α := ℝ) S.size]
    · obtain ⟨S', hdim', hdef', hloss⟩ := S.step hdim hterm hdef
      obtain ⟨i, hki, hikd, S'', hdef'', hterm'', hsize''⟩ :=
        ih (k + 1) S' hdef' hdim'
      refine ⟨i, by omega, by omega, S'', hdef'', hterm'', ?_⟩
      have hslm : stepLoss d (A.card : ℝ) ≤ stepLoss (d + 1) (A.card : ℝ) :=
        stepLoss_le_stepLoss (by omega) hx1
      have hsl0 : (0 : ℝ) ≤ stepLoss d (A.card : ℝ) :=
        le_trans zero_le_one (one_le_stepLoss _ hx1)
      calc (S.size : ℝ)
          ≤ stepLoss (d + 1) (A.card : ℝ) * S'.size := hloss
        _ ≤ stepLoss (d + 1) (A.card : ℝ) *
              (stepLoss d (A.card : ℝ) ^ d * S''.size) := by
            have := mul_le_mul_of_nonneg_left hsize''
              (le_trans zero_le_one hsl1)
            exact this
        _ ≤ stepLoss (d + 1) (A.card : ℝ) *
              (stepLoss (d + 1) (A.card : ℝ) ^ d * S''.size) := by
            have hpowle : stepLoss d (A.card : ℝ) ^ d ≤
                stepLoss (d + 1) (A.card : ℝ) ^ d :=
              pow_le_pow_left₀ hsl0 hslm d
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hpowle (Nat.cast_nonneg _))
              (le_trans zero_le_one hsl1)
        _ = stepLoss (d + 1) (A.card : ℝ) ^ (d + 1) * S''.size := by ring

/-- Lemma 26 of DMMPT26: a twin-free pair whose trace system has VC
dimension at most `d` admits a definable terminal `i`-sparsification,
`i ≤ d`, of size at least `|B| / stepLoss^d`. -/
theorem exists_terminal_sparsification {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {d : ℕ}
    (htf : ∀ b ∈ B, ∀ b' ∈ B, trace G A b = trace G A b' → b = b')
    (hvc : (B.image (trace G A)).vcDim ≤ d) (hA : 1 < A.card) :
    ∃ i ≤ d, ∃ S : Sparsification G A B i,
      S.Definable ∧ S.Terminal ∧
      (B.card : ℝ) ≤ stepLoss d A.card ^ d * S.size := by
  have hdim : (Sparsification.trivial htf).DimLE d := by
    intro b hb
    refine le_trans (Finset.vcDim_mono ?_) hvc
    intro F hF
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hF
    exact Finset.mem_image_of_mem _ (Finset.filter_subset _ _ hb')
  obtain ⟨i, -, hid, S, hdef, hterm, hsize⟩ :=
    exists_terminal_of_dimLE (by omega) d 0 (.trivial htf)
      (Sparsification.definable_trivial htf) hdim
  exact ⟨i, by omega, S, hdef, hterm, hsize⟩

end Lax5Proofs
