import Lax5.Transductions
import Lax5Proofs.SetSystems
import Lax5Proofs.Sampling
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

/-- Restricting a trace from `X` to a subset `Y` is the trace on `Y`. -/
theorem trace_inter_eq_of_subset (G : SimpleGraph (Fin n))
    (X Y : Finset (Fin n)) (hYX : Y ⊆ X) (b : Fin n) :
    trace G X b ∩ Y = trace G Y b := by
  ext x
  simp only [trace, Finset.mem_inter, Finset.mem_filter]
  aesop

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

/-- Membership in the trace system of a part, unpacked to a vertex of
the support with the prescribed label tuple. -/
theorem mem_partTraces_iff (S : Sparsification G A B k)
    (τ : Fin k → Fin n) (F : Finset (Fin n)) :
    F ∈ S.partTraces τ ↔
      ∃ b ∈ S.supp, S.tup b = τ ∧ trace G S.core b = F := by
  simp [partTraces, part]
  aesop

/-- The part trace systems partition the support cardinality. -/
theorem sum_card_partTraces (S : Sparsification G A B k) :
    ∑ τ ∈ S.labels, (S.partTraces τ).card = S.size := by
  have hsum : S.supp.card = ∑ τ ∈ S.labels, (S.part τ).card :=
    Finset.card_eq_sum_card_fiberwise fun b hb =>
      Finset.mem_image_of_mem _ hb
  simp only [size]
  rw [hsum]
  exact Finset.sum_congr rfl fun τ _ => S.card_partTraces τ

/-- A nonterminal sparsification has a core with at least two vertices;
otherwise every part has at most the two possible traces on the core. -/
theorem one_lt_core_card_of_not_terminal (S : Sparsification G A B k)
    (hnt : ¬ S.Terminal) : 1 < S.core.card := by
  classical
  by_contra hcard
  push Not at hcard
  have hle : ∀ τ ∈ S.labels, (S.partTraces τ).card ≤ 2 := by
    intro τ hτ
    calc
      (S.partTraces τ).card ≤ S.core.powerset.card :=
        Finset.card_le_card fun F hF => Finset.mem_powerset.2 <| by
          obtain ⟨b, hb, ht, rfl⟩ := (S.mem_partTraces_iff τ F).1 hF
          exact Finset.filter_subset _ _
      _ = 2 ^ S.core.card := Finset.card_powerset _
      _ ≤ 2 := by interval_cases S.core.card <;> norm_num
  apply hnt
  show S.size ≤ 2 * S.partsCount
  rw [← S.sum_card_partTraces]
  simp only [partsCount]
  calc
    ∑ τ ∈ S.labels, (S.partTraces τ).card ≤
        ∑ _τ ∈ S.labels, 2 := Finset.sum_le_sum hle
    _ = 2 * S.labels.card := by simp [mul_comm]

/-- The dense Hamming restriction supplied by Lemma 19, specialized to
the trace systems of the parts of a nonterminal sparsification. -/
theorem exists_core_hamming_dense (S : Sparsification G A B k)
    (hnt : ¬ S.Terminal) :
    ∃ X ⊆ S.core,
      (S.size : ℝ) ≤ (2 * Real.log S.core.card + 2) *
        ∑ τ ∈ S.labels,
          (SetSystems.hammingEdgeCount
            ((S.partTraces τ).image (· ∩ X)) : ℝ) := by
  classical
  have hground : ∀ τ ∈ S.labels, ∀ F ∈ S.partTraces τ, F ⊆ S.core := by
    intro τ hτ F hF
    obtain ⟨b, hb, ht, rfl⟩ := (S.mem_partTraces_iff τ F).1 hF
    exact Finset.filter_subset _ _
  have hm : 2 * S.labels.card <
      ∑ τ ∈ S.labels, (S.partTraces τ).card := by
    rw [S.sum_card_partTraces]
    exact Nat.lt_of_not_ge hnt
  obtain ⟨X, hX, hdense⟩ :=
    SetSystems.exists_subset_hamming_dense S.labels S.partTraces
      S.core hground (S.one_lt_core_card_of_not_terminal hnt) hm
  refine ⟨X, hX, ?_⟩
  have hsum : (∑ τ ∈ S.labels, ((S.partTraces τ).card : ℝ)) =
      (S.size : ℝ) := by
    exact_mod_cast S.sum_card_partTraces
  rwa [hsum] at hdense

/-- The trace family of one part after restriction to `X`. -/
noncomputable def restrictedPartTraces (S : Sparsification G A B k)
    (X : Finset (Fin n)) (τ : Fin k → Fin n) : Finset (Finset (Fin n)) :=
  (S.partTraces τ).image (· ∩ X)

/-- Keys `(old label tuple, restricted trace)` realized by the support. -/
noncomputable def traceKeys (S : Sparsification G A B k) (X : Finset (Fin n)) :
    Finset ((Fin k → Fin n) × Finset (Fin n)) :=
  S.labels.biUnion fun τ =>
    (S.restrictedPartTraces X τ).image (Prod.mk τ)

/-- Positive or negative merge incidence between a coordinate and a
restricted trace key. -/
noncomputable def MergeAt (S : Sparsification G A B k) (X : Finset (Fin n))
    (positive : Bool) (a : Fin n)
    (q : (Fin k → Fin n) × Finset (Fin n)) : Prop :=
  if positive then SetSystems.VPos (S.restrictedPartTraces X q.1) a q.2
  else SetSystems.VNeg (S.restrictedPartTraces X q.1) a q.2

noncomputable instance (S : Sparsification G A B k) (X : Finset (Fin n))
    (positive : Bool) (a : Fin n)
    (q : (Fin k → Fin n) × Finset (Fin n)) :
    Decidable (S.MergeAt X positive a q) := by
  unfold MergeAt
  infer_instance

/-- Restricted trace keys non-isolated in the chosen merge direction. -/
noncomputable def mergeKeys (S : Sparsification G A B k) (X : Finset (Fin n))
    (positive : Bool) : Finset ((Fin k → Fin n) × Finset (Fin n)) :=
  (S.traceKeys X).filter fun q => ∃ a ∈ X, S.MergeAt X positive a q

/-- All keys non-isolated in the Hamming graph of their restricted part
trace system. -/
noncomputable def nonisolatedKeys (S : Sparsification G A B k)
    (X : Finset (Fin n)) :
    Finset ((Fin k → Fin n) × Finset (Fin n)) :=
  S.labels.biUnion fun τ =>
    (SetSystems.nonIsolated (S.restrictedPartTraces X τ)).image (Prod.mk τ)

/-- Coordinates actually incident with the chosen oriented merge keys. -/
noncomputable def mergeCoords (S : Sparsification G A B k)
    (X : Finset (Fin n)) (positive : Bool) : Finset (Fin n) :=
  X.filter fun a => ∃ q ∈ S.mergeKeys X positive, S.MergeAt X positive a q

/-- Trace keys are equivalently obtained by mapping every support vertex
to its old label tuple and its trace on the restricted core. -/
theorem traceKeys_eq_image (S : Sparsification G A B k)
    (X : Finset (Fin n)) (hX : X ⊆ S.core) :
    S.traceKeys X = S.supp.image fun b => (S.tup b, trace G X b) := by
  classical
  ext q
  constructor
  · intro hq
    rw [traceKeys] at hq
    obtain ⟨τ, hτ, hqτ⟩ := Finset.mem_biUnion.1 hq
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hqτ
    rw [restrictedPartTraces] at hF
    obtain ⟨T, hT, hTF⟩ := Finset.mem_image.1 hF
    obtain ⟨b, hb, ht, hTb⟩ := (S.mem_partTraces_iff τ T).1 hT
    refine Finset.mem_image.2 ⟨b, hb, ?_⟩
    apply Prod.ext
    · exact ht
    · rw [← hTF, ← hTb]
      exact (trace_inter_eq_of_subset G S.core X hX b).symm
  · intro hq
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hq
    rw [traceKeys, Finset.mem_biUnion]
    refine ⟨S.tup b, Finset.mem_image_of_mem _ hb, ?_⟩
    refine Finset.mem_image.2 ⟨trace G X b, ?_, rfl⟩
    rw [restrictedPartTraces]
    refine Finset.mem_image.2 ⟨trace G S.core b, ?_, ?_⟩
    · exact (S.mem_partTraces_iff _ _).2 ⟨b, hb, rfl, rfl⟩
    · exact trace_inter_eq_of_subset G S.core X hX b

/-- The indexed union defining `nonisolatedKeys` is disjoint in its
first coordinate, so its cardinality is the sum of the fiber sizes. -/
theorem card_nonisolatedKeys (S : Sparsification G A B k)
    (X : Finset (Fin n)) :
    (S.nonisolatedKeys X).card =
      ∑ τ ∈ S.labels,
        (SetSystems.nonIsolated (S.restrictedPartTraces X τ)).card := by
  classical
  rw [nonisolatedKeys, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun τ hτ => ?_
    exact Finset.card_image_of_injective _ fun F F' h =>
      congrArg Prod.snd h
  · intro τ hτ τ' hτ' hne
    change Disjoint
      ((SetSystems.nonIsolated (S.restrictedPartTraces X τ)).image (Prod.mk τ))
      ((SetSystems.nonIsolated (S.restrictedPartTraces X τ')).image (Prod.mk τ'))
    rw [Finset.disjoint_left]
    intro q hq hq'
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨F', hF', heq⟩ := Finset.mem_image.1 hq'
    exact hne (congrArg Prod.fst heq).symm

/-- Every non-isolated restricted trace is incident in at least one of
the two oriented merge relations. -/
theorem nonisolatedKeys_subset_merge (S : Sparsification G A B k)
    (X : Finset (Fin n)) :
    S.nonisolatedKeys X ⊆ S.mergeKeys X true ∪ S.mergeKeys X false := by
  classical
  intro q hq
  rw [nonisolatedKeys] at hq
  obtain ⟨τ, hτ, hqτ⟩ := Finset.mem_biUnion.1 hq
  obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hqτ
  have hF' : F ∈ S.restrictedPartTraces X τ ∧
      ∃ a ∈ (S.restrictedPartTraces X τ).sup id,
        SetSystems.VPos (S.restrictedPartTraces X τ) a F ∨
          SetSystems.VNeg (S.restrictedPartTraces X τ) a F := by
    simpa only [SetSystems.nonIsolated, Finset.mem_filter] using hF
  obtain ⟨hFfam, a, hasup, hmerge⟩ := hF'
  have haX : a ∈ X := by
    obtain ⟨T, hTfam, haT⟩ := Finset.mem_sup.1 hasup
    rw [restrictedPartTraces] at hTfam
    obtain ⟨T', hT', rfl⟩ := Finset.mem_image.1 hTfam
    exact Finset.inter_subset_right haT
  have hkey : (τ, F) ∈ S.traceKeys X := by
    rw [traceKeys, Finset.mem_biUnion]
    exact ⟨τ, hτ, Finset.mem_image.2 ⟨F, hFfam, rfl⟩⟩
  rw [Finset.mem_union]
  rcases hmerge with hpos | hneg
  · left
    rw [mergeKeys, Finset.mem_filter]
    exact ⟨hkey, a, haX, by simpa [MergeAt] using hpos⟩
  · right
    rw [mergeKeys, Finset.mem_filter]
    exact ⟨hkey, a, haX, by simpa [MergeAt] using hneg⟩

/-- Corollary 9, summed over the parts: one of the two oriented merge
relations contains enough non-isolated trace keys to support all Hamming
edges, up to the factor `2d`. -/
theorem exists_merge_direction (S : Sparsification G A B k) {d : ℕ}
    (hd : S.DimLE d) (X : Finset (Fin n)) :
    ∃ positive : Bool,
      ∑ τ ∈ S.labels,
          SetSystems.hammingEdgeCount (S.restrictedPartTraces X τ) ≤
        2 * d * (S.mergeKeys X positive).card := by
  classical
  have hvc : ∀ τ ∈ S.labels, (S.restrictedPartTraces X τ).vcDim ≤ d := by
    intro τ hτ
    obtain ⟨b, hb, ht⟩ := Finset.mem_image.1 hτ
    subst τ
    exact le_trans
      (SetSystems.vcDim_image_inter_le (S.partTraces (S.tup b)) X)
      (hd b hb)
  have hedge :
      ∑ τ ∈ S.labels,
          SetSystems.hammingEdgeCount (S.restrictedPartTraces X τ) ≤
        d * (S.nonisolatedKeys X).card := by
    rw [S.card_nonisolatedKeys X, Finset.mul_sum]
    exact Finset.sum_le_sum fun τ hτ =>
      le_trans
        (SetSystems.hammingEdgeCount_le_vcDim_mul_card_nonIsolated
          (S.restrictedPartTraces X τ))
        (Nat.mul_le_mul_right _ (hvc τ hτ))
  have hni : (S.nonisolatedKeys X).card ≤
      (S.mergeKeys X true).card + (S.mergeKeys X false).card :=
    le_trans (Finset.card_le_card (S.nonisolatedKeys_subset_merge X))
      (Finset.card_union_le _ _)
  by_cases hdir : (S.mergeKeys X true).card ≤ (S.mergeKeys X false).card
  · refine ⟨false, le_trans hedge ?_⟩
    nlinarith
  · refine ⟨true, le_trans hedge ?_⟩
    push Not at hdir
    nlinarith

/-- Dense restriction, orientation, and Lemma 12 combined. The surviving
trace keys have a unique neighbor in a sampled set of merge coordinates,
with the quantitative loss used by `stepLoss`. -/
theorem exists_sampled_merge (S : Sparsification G A B k) {d : ℕ}
    (hd : S.DimLE d) (hnt : ¬ S.Terminal) :
    ∃ X ⊆ S.core, ∃ positive : Bool,
      ∃ X' ⊆ S.mergeCoords X positive,
      ∃ Y' ⊆ S.mergeKeys X positive,
        (S.size : ℝ) ≤
          (600 * (d + 1) * (Real.log A.card + 2) ^ 2) * Y'.card ∧
        ∀ q ∈ Y', ∃! a, a ∈ X' ∧ S.MergeAt X positive a q := by
  classical
  obtain ⟨X, hX, hdense⟩ := S.exists_core_hamming_dense hnt
  obtain ⟨positive, hedge⟩ := S.exists_merge_direction hd X
  have hedgeR :
      (∑ τ ∈ S.labels,
          (SetSystems.hammingEdgeCount (S.restrictedPartTraces X τ) : ℝ)) ≤
        2 * d * (S.mergeKeys X positive).card := by
    exact_mod_cast hedge
  have hpre : (S.size : ℝ) ≤
      (2 * Real.log S.core.card + 2) *
        (2 * d * (S.mergeKeys X positive).card) :=
    le_trans hdense (mul_le_mul_of_nonneg_left hedgeR <| by
      have := Real.log_nonneg (show (1 : ℝ) ≤ S.core.card by
        exact_mod_cast (S.one_lt_core_card_of_not_terminal hnt).le)
      linarith)
  have hcoord : ∀ a ∈ S.mergeCoords X positive,
      ∃ q ∈ S.mergeKeys X positive, S.MergeAt X positive a q := by
    intro a ha
    exact (Finset.mem_filter.1 ha).2
  have hkey : ∀ q ∈ S.mergeKeys X positive,
      ∃ a ∈ S.mergeCoords X positive, S.MergeAt X positive a q := by
    intro q hq
    obtain ⟨hqt, a, haX, hmerge⟩ := Finset.mem_filter.1 hq
    exact ⟨a, Finset.mem_filter.2 ⟨haX, q, hq, hmerge⟩, hmerge⟩
  obtain ⟨X', hX', Y', hY', hsample, hunique⟩ :=
    Sampling.exists_unique_neighbor_subsets
      (S.mergeCoords X positive) (S.mergeKeys X positive)
      (S.MergeAt X positive) hcoord hkey
  refine ⟨X, hX, positive, X', hX', Y', hY', ?_, hunique⟩
  have hsizepos : (0 : ℝ) < S.size := by
    have hs : 0 < S.size := by
      by_contra hs
      apply hnt
      show S.size ≤ 2 * S.partsCount
      omega
    exact_mod_cast hs
  have hYpos : 0 < (S.mergeKeys X positive).card := by
    by_contra hY
    have hY0 : (S.mergeKeys X positive).card = 0 := Nat.eq_zero_of_not_pos hY
    rw [hY0, Nat.cast_zero, mul_zero, mul_zero] at hpre
    linarith
  have hCpos : 0 < (S.mergeCoords X positive).card := by
    obtain ⟨q, hq⟩ := Finset.card_pos.1 hYpos
    obtain ⟨a, ha, hmerge⟩ := hkey q hq
    exact Finset.card_pos.2 ⟨a, ha⟩
  have hcoreA : S.core.card ≤ A.card :=
    Finset.card_le_card S.core_subset
  have hcoordA : (S.mergeCoords X positive).card ≤ A.card :=
    Finset.card_le_card <| (Finset.filter_subset _ _).trans (hX.trans S.core_subset)
  have hlogCore : Real.log S.core.card ≤ Real.log A.card :=
    Real.log_le_log (by exact_mod_cast (S.one_lt_core_card_of_not_terminal hnt).le)
      (by exact_mod_cast hcoreA)
  have hlogCoord : Real.log (S.mergeCoords X positive).card ≤ Real.log A.card :=
    Real.log_le_log (by exact_mod_cast hCpos)
      (by exact_mod_cast hcoordA)
  have hlogCore0 : 0 ≤ Real.log S.core.card :=
    Real.log_nonneg (by exact_mod_cast (S.one_lt_core_card_of_not_terminal hnt).le)
  have hlogCoord0 : 0 ≤ Real.log (S.mergeCoords X positive).card :=
    Real.log_nonneg (by exact_mod_cast hCpos)
  have hlogA0 : 0 ≤ Real.log A.card := le_trans hlogCore0 hlogCore
  calc
    (S.size : ℝ) ≤
        (2 * Real.log S.core.card + 2) *
          (2 * d * (S.mergeKeys X positive).card) := hpre
    _ ≤ (2 * Real.log S.core.card + 2) *
          (2 * d * (150 * (Real.log (S.mergeCoords X positive).card + 1) *
            Y'.card)) := by
      gcongr
    _ ≤ (600 * (d + 1) * (Real.log A.card + 2) ^ 2) * Y'.card := by
      have hfac : (d : ℝ) * (Real.log S.core.card + 1) *
          (Real.log (S.mergeCoords X positive).card + 1) ≤
          ((d : ℝ) + 1) * (Real.log A.card + 2) *
            (Real.log A.card + 2) := by
        gcongr <;> nlinarith
      calc
        (2 * Real.log ↑S.core.card + 2) *
              (2 * ↑d *
                (150 * (Real.log ↑(S.mergeCoords X positive).card + 1) *
                  ↑Y'.card)) =
            600 * ((d : ℝ) * (Real.log S.core.card + 1) *
              (Real.log (S.mergeCoords X positive).card + 1)) * Y'.card := by
                ring
        _ ≤ 600 * (((d : ℝ) + 1) * (Real.log A.card + 2) *
              (Real.log A.card + 2)) * Y'.card := by
                gcongr
        _ = 600 * ((d : ℝ) + 1) * (Real.log ↑A.card + 2) ^ 2 *
              ↑Y'.card := by ring

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

set_option maxHeartbeats 800000 in
/-- Semantic form of the formula used for a new sparsification label.
The five fresh colors mark, in order, the new core, target labels,
support, trace representatives, and the sign of the merge. -/
theorem realizeIn_mergeFormula {k : ℕ} (G : SimpleGraph (Fin n))
    (colors : Fin (5 * k + 5) → Set (Fin n))
    (ψ : Fin k → (withColors Language.graph (5 * k + 5)).Formula (Fin 2))
    (b a : Fin n) :
    RealizeIn G.structure colors (mergeFormula k ψ) ![b, a] ↔
      b ∈ colors ⟨5 * k + 2, by omega⟩ ∧
      a ∈ colors ⟨5 * k + 1, by omega⟩ ∧
      ∃ b', b' ∈ colors ⟨5 * k + 3, by omega⟩ ∧
        (∀ i, ∃ z, RealizeIn G.structure colors (ψ i) ![b, z] ∧
          RealizeIn G.structure colors (ψ i) ![b', z]) ∧
        (∀ x, x ∈ colors ⟨5 * k, by omega⟩ → x ≠ a →
          (G.Adj b x ↔ G.Adj b' x)) ∧
        ((colors ⟨5 * k + 4, by omega⟩).Nonempty →
          G.Adj b a ∧ ¬ G.Adj b' a) ∧
        (¬(colors ⟨5 * k + 4, by omega⟩).Nonempty →
          ¬ G.Adj b a ∧ G.Adj b' a) := by
  letI := G.structure
  letI := colorStructure colors
  have hψ' (i : Fin k) (v : Fin 2 → Fin n) (xs : Fin 0 → Fin n) :
      Language.BoundedFormula.Realize (ψ i) v xs ↔
        RealizeIn G.structure colors (ψ i) ![v 0, v 1] := by
    rw [Language.Formula.boundedFormula_realize_eq_realize]
    change RealizeIn G.structure colors (ψ i) v ↔ _
    have hv : v = ![v 0, v 1] := by
      funext j
      fin_cases j <;> rfl
    rw [hv]
    simp
  have hcolor (i : Fin (5 * k + 5)) (v : Fin 1 → Fin n) :
      @Language.Structure.RelMap (withColors Language.graph (5 * k + 5))
        _ _ 1 (Sum.inr (ColorRel.color i)) v ↔ v 0 ∈ colors i := Iff.rfl
  have hadj (v : Fin 2 → Fin n) :
      @Language.Structure.RelMap (withColors Language.graph (5 * k + 5))
        _ _ 2 (Sum.inl Language.adj) v ↔ G.Adj (v 0) (v 1) := Iff.rfl
  simp [mergeFormula, RealizeIn, Language.Formula.Realize,
      Language.BoundedFormula.Realize, colorAtom, adjAtom,
      Language.Relations.boundedFormula₁, Language.Relations.boundedFormula₂,
      Language.Relations.boundedFormula, Language.Term.bdEqual, hcolor,
      hadj, Function.comp_def, Fin.snoc, Set.Nonempty, eq_comm]
  simp only [hψ']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Sum.elim_inl, Sum.elim_inr]
  simp only [show (0 : Fin 1) = Fin.last 0 by rfl,
    show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) by rfl,
    show (1 : Fin 2) = Fin.last 1 by rfl, Fin.snoc_castSucc, Fin.snoc_last,
    and_assoc]

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

set_option maxHeartbeats 1200000 in
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
  classical
  obtain ⟨X, hX, positive, X', hX', Y', hY', hloss, hunique⟩ :=
    S.exists_sampled_merge hd hnt
  have hYkeys : Y' ⊆ S.traceKeys X :=
    hY'.trans (Finset.filter_subset _ _)
  have allRep_exists (q : ↑(S.traceKeys X)) :
      ∃ b ∈ S.supp, (S.tup b, trace G X b) = q := by
    apply Finset.mem_image.1
    rw [← S.traceKeys_eq_image X hX]
    exact q.property
  let allRep : (q : ↑(S.traceKeys X)) → Fin n := fun q =>
    Classical.choose (allRep_exists q)
  have allRep_mem (q : ↑(S.traceKeys X)) : allRep q ∈ S.supp :=
    (Classical.choose_spec (allRep_exists q)).1
  have allRep_key (q : ↑(S.traceKeys X)) :
      (S.tup (allRep q), trace G X (allRep q)) = q :=
    (Classical.choose_spec (allRep_exists q)).2
  let rep : (q : ↑Y') → Fin n := fun q =>
    allRep ⟨q, hYkeys q.property⟩
  have rep_mem (q : ↑Y') : rep q ∈ S.supp :=
    allRep_mem ⟨q, hYkeys q.property⟩
  have rep_key (q : ↑Y') :
      (S.tup (rep q), trace G X (rep q)) = q :=
    allRep_key ⟨q, hYkeys q.property⟩
  have label_mem (q : ↑Y') : q.val.1 ∈ S.labels := by
    rw [← congrArg Prod.fst (rep_key q)]
    exact Finset.mem_image_of_mem _ (rep_mem q)
  have rep_inj : Function.Injective rep := by
    intro q q' heq
    apply Subtype.ext
    calc
      q.val = (S.tup (rep q), trace G X (rep q)) := (rep_key q).symm
      _ = (S.tup (rep q'), trace G X (rep q')) := by rw [heq]
      _ = q'.val := rep_key q'
  let supp' : Finset (Fin n) := Y'.attach.image rep
  have mem_supp'_iff (b : Fin n) :
      b ∈ supp' ↔ ∃ q : ↑Y', rep q = b := by
    simp [supp']
  let newF : Fin n → Fin n := fun b =>
    if hb : ∃ q : ↑Y', rep q = b then
      Classical.choose (hunique hb.choose hb.choose.property)
    else b
  have newF_spec (q : ↑Y') :
      newF (rep q) ∈ X' ∧
        S.MergeAt X positive (newF (rep q)) q := by
    let hex : ∃ q' : ↑Y', rep q' = rep q := ⟨q, rfl⟩
    simp only [newF, dif_pos hex]
    have hqq : hex.choose = q := rep_inj hex.choose_spec
    simpa [hqq] using
      (Classical.choose_spec (hunique hex.choose hex.choose.property)).1
  have newF_unique (q : ↑Y') (a : Fin n) :
      a ∈ X' ∧ S.MergeAt X positive a q → newF (rep q) = a := by
    intro ha
    exact (hunique q q.property).unique (newF_spec q) ha
  let f' : Fin (k + 1) → Fin n → Fin n :=
    Fin.snoc S.f newF
  let S' : Sparsification G A B (k + 1) :=
    { core := X
      core_subset := hX.trans S.core_subset
      supp := supp'
      supp_subset := by
        intro b hb
        obtain ⟨q, rfl⟩ := (mem_supp'_iff b).1 hb
        exact S.supp_subset (rep_mem q)
      f := f'
      f_mem := by
        intro j b hb
        obtain ⟨q, rfl⟩ := (mem_supp'_iff b).1 hb
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa [f'] using S.core_subset
            (hX (Finset.filter_subset _ _ (hX' (newF_spec q).1)))
        · simpa [f'] using S.f_mem i (rep q) (rep_mem q)
      inj := by
        intro b hb b' hb' htrace hf
        obtain ⟨q, rfl⟩ := (mem_supp'_iff b).1 hb
        obtain ⟨q', rfl⟩ := (mem_supp'_iff b').1 hb'
        congr 1
        apply Subtype.ext
        apply Prod.ext
        · funext i
          have hi := hf (Fin.castSucc i)
          rw [← congrArg Prod.fst (rep_key q),
            ← congrArg Prod.fst (rep_key q')]
          simpa [f'] using hi
        · rw [← congrArg Prod.snd (rep_key q),
            ← congrArg Prod.snd (rep_key q')]
          exact htrace }
  refine ⟨S', ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨q, rfl⟩ := (mem_supp'_iff b).1 hb
    have hqmerge := (newF_spec q).2
    have hpart : S'.partTraces (S'.tup (rep q)) ⊆
        (S.restrictedPartTraces X q.val.1).filter
          (if positive then SetSystems.VPos (S.restrictedPartTraces X q.val.1)
            (newF (rep q))
          else SetSystems.VNeg (S.restrictedPartTraces X q.val.1)
            (newF (rep q))) := by
      intro F hF
      obtain ⟨b', hb', htup, rfl⟩ :=
        (S'.mem_partTraces_iff _ _).1 hF
      obtain ⟨q', rfl⟩ := (mem_supp'_iff b').1 hb'
      have hold : S.tup (rep q') = S.tup (rep q) := by
        funext i
        have hi := congrFun htup (Fin.castSucc i)
        simpa [S', f', Sparsification.tup, Fin.snoc] using hi
      have hnew : newF (rep q') = newF (rep q) := by
        have hi := congrFun htup (Fin.last k)
        simpa [S', f', Sparsification.tup, Fin.snoc] using hi
      have hqq1 : q'.val.1 = q.val.1 := by
        rw [← congrArg Prod.fst (rep_key q'),
          ← congrArg Prod.fst (rep_key q)]
        exact hold
      have hmerge' := (newF_spec q').2
      rw [Finset.mem_filter]
      constructor
      · rw [restrictedPartTraces]
        refine Finset.mem_image.2 ⟨trace G S.core (rep q'), ?_, ?_⟩
        · exact (S.mem_partTraces_iff _ _).2
            ⟨rep q', rep_mem q',
              (congrArg Prod.fst (rep_key q')).trans hqq1, rfl⟩
        · exact trace_inter_eq_of_subset G S.core X hX (rep q')
      · have htraceq : trace G X (rep q') = q'.val.2 :=
          congrArg Prod.snd (rep_key q')
        cases hp : positive
        · change SetSystems.VNeg (S.restrictedPartTraces X q.val.1)
              (newF (rep q)) (trace G X (rep q'))
          unfold MergeAt at hmerge'
          simp only [hp, Bool.false_eq] at hmerge'
          rw [htraceq, ← hqq1, ← hnew]
          exact hmerge'
        · change SetSystems.VPos (S.restrictedPartTraces X q.val.1)
              (newF (rep q)) (trace G X (rep q'))
          unfold MergeAt at hmerge'
          simp only [hp, if_true] at hmerge'
          rw [htraceq, ← hqq1, ← hnew]
          exact hmerge'
    obtain ⟨b0, hb0, ht0⟩ := Finset.mem_image.1 (label_mem q)
    have hvc : (S.restrictedPartTraces X q.val.1).vcDim ≤ d := by
      rw [← ht0]
      exact le_trans (SetSystems.vcDim_image_inter_le _ _) (hd b0 hb0)
    cases hp : positive
    · have hpart' : S'.partTraces (S'.tup (rep q)) ⊆
          (S.restrictedPartTraces X q.val.1).filter
            (SetSystems.VNeg (S.restrictedPartTraces X q.val.1)
              (newF (rep q))) := by
        intro F hF
        simpa [hp] using hpart hF
      apply le_trans (Finset.vcDim_mono hpart')
      have hm := hqmerge
      unfold MergeAt at hm
      simp only [hp, Bool.false_eq] at hm
      have hlt := SetSystems.vcDim_filter_vNeg_lt
        ⟨q.val.2, Finset.mem_filter.2 ⟨hm.1, hm⟩⟩
      omega
    · have hpart' : S'.partTraces (S'.tup (rep q)) ⊆
          (S.restrictedPartTraces X q.val.1).filter
            (SetSystems.VPos (S.restrictedPartTraces X q.val.1)
              (newF (rep q))) := by
        intro F hF
        simpa [hp] using hpart hF
      apply le_trans (Finset.vcDim_mono hpart')
      have hm := hqmerge
      unfold MergeAt at hm
      simp only [hp, if_true] at hm
      have hlt := SetSystems.vcDim_filter_vPos_lt
        ⟨q.val.2, Finset.mem_filter.2 ⟨hm.1, hm⟩⟩
      omega
  · obtain ⟨oldColors, holdColors⟩ := hdef
    let colors : Fin (5 * (k + 1)) → Set (Fin n) := fun i =>
      if hi : (i : ℕ) < 5 * k then oldColors ⟨i, hi⟩
      else if i = ⟨5 * k, by omega⟩ then ↑X
      else if i = ⟨5 * k + 1, by omega⟩ then ↑X'
      else if i = ⟨5 * k + 2, by omega⟩ then ↑supp'
      else if i = ⟨5 * k + 3, by omega⟩ then Set.range allRep
      else if positive then Set.univ else ∅
    refine ⟨colors, ?_⟩
    intro j b hb a
    obtain ⟨q, rfl⟩ := (mem_supp'_iff b).1 hb
    have hlift (i : Fin k) (b : Fin n) (hb : b ∈ S.supp) (z : Fin n) :
        RealizeIn G.structure colors
            (liftFormula (by omega) (sparsFormulas k i)) ![b, z] ↔
          S.f i b = z := by
      rw [realizeIn_liftFormula]
      simpa [colors] using (holdColors i b hb z).symm
    refine Fin.lastCases ?_ (fun i => ?_) j
    · have hsem := realizeIn_mergeFormula G colors
          (fun i => liftFormula (by omega) (sparsFormulas k i)) (rep q) a
      have hformula : sparsFormulas (k + 1) (Fin.last k) =
          mergeFormula k (fun i => liftFormula (by omega)
            (sparsFormulas k i)) := by simp [sparsFormulas]
      rw [hformula]
      rw [hsem]
      have hlast : S'.f (Fin.last k) (rep q) = newF (rep q) := by
        simp [S', f']
      rw [hlast]
      constructor
      · intro hfa
        subst a
        refine ⟨by simpa [colors, supp'], by simpa [colors] using (newF_spec q).1,
          ?_⟩
        have hm := (newF_spec q).2
        rcases positive with _ | _
        · obtain ⟨hF, haF, hpartner⟩ := hm
          let q' : ↑(S.traceKeys X) :=
            ⟨(q.val.1, insert (newF (rep q)) q.val.2), by
              rw [traceKeys, Finset.mem_biUnion]
              exact ⟨q.val.1, label_mem q,
                Finset.mem_image.2 ⟨_, hpartner, rfl⟩⟩⟩
          refine ⟨allRep q', by simpa [colors] using Set.mem_range_self q',
            ?_, ?_, ?_, ?_⟩
          · intro i
            refine ⟨S.f i (rep q), (hlift i _ (rep_mem q) _).2 rfl, ?_⟩
            apply (hlift i _ (allRep_mem q') _).2
            have hall := congrArg Prod.fst (allRep_key q')
            have hrep := congrArg Prod.fst (rep_key q)
            exact congrFun (hall.trans hrep.symm) i
          · intro x hx hxa
            have ht := congrArg Prod.snd (allRep_key q')
            have htr := congrArg Prod.snd (rep_key q)
            simp only [trace, Finset.ext_iff, Finset.mem_filter] at ht htr
            specialize ht x; specialize htr x
            have hins : x ∈ insert (newF (rep q)) q.val.2 ↔ x ∈ q.val.2 := by
              simp [hxa]
            rw [hins] at ht
            have hxX : x ∈ X := by simpa [colors] using hx
            constructor
            · intro hadj
              exact ((htr.trans ht.symm).1 ⟨hxX, hadj⟩).2
            · intro hadj
              exact ((htr.trans ht.symm).2 ⟨hxX, hadj⟩).2
          · intro hs
            exfalso
            simpa [colors] using hs
          · intro _
            have haX0 : newF (rep q) ∈ X :=
              Finset.filter_subset _ _ (hX' (newF_spec q).1)
            constructor
            · intro hadj
              apply haF
              rw [← congrArg Prod.snd (rep_key q)]
              exact Finset.mem_filter.2 ⟨haX0, hadj⟩
            · have ht : newF (rep q) ∈ trace G X (allRep q') := by
                have htq : trace G X (allRep q') = q'.val.2 :=
                  congrArg Prod.snd (allRep_key q')
                rw [htq]
                exact Finset.mem_insert_self _ _
              exact (Finset.mem_filter.1 ht).2
        · obtain ⟨hF, haF, hpartner⟩ := hm
          let q' : ↑(S.traceKeys X) :=
            ⟨(q.val.1, q.val.2.erase (newF (rep q))), by
              rw [traceKeys, Finset.mem_biUnion]
              exact ⟨q.val.1, label_mem q,
                Finset.mem_image.2 ⟨_, hpartner, rfl⟩⟩⟩
          refine ⟨allRep q', by simpa [colors] using Set.mem_range_self q',
            ?_, ?_, ?_, ?_⟩
          · intro i
            refine ⟨S.f i (rep q), (hlift i _ (rep_mem q) _).2 rfl, ?_⟩
            apply (hlift i _ (allRep_mem q') _).2
            have hall := congrArg Prod.fst (allRep_key q')
            have hrep := congrArg Prod.fst (rep_key q)
            exact congrFun (hall.trans hrep.symm) i
          · intro x hx hxa
            have ht := congrArg Prod.snd (allRep_key q')
            have htr := congrArg Prod.snd (rep_key q)
            simp only [trace, Finset.ext_iff, Finset.mem_filter] at ht htr
            specialize ht x; specialize htr x
            have herase : x ∈ q.val.2.erase (newF (rep q)) ↔ x ∈ q.val.2 := by
              simp [hxa]
            rw [herase] at ht
            have hxX : x ∈ X := by simpa [colors] using hx
            constructor
            · intro hadj
              exact ((htr.trans ht.symm).1 ⟨hxX, hadj⟩).2
            · intro hadj
              exact ((htr.trans ht.symm).2 ⟨hxX, hadj⟩).2
          · intro _
            have haX0 : newF (rep q) ∈ X :=
              Finset.filter_subset _ _ (hX' (newF_spec q).1)
            constructor
            · have ht : newF (rep q) ∈ trace G X (rep q) := by
                have htq : trace G X (rep q) = q.val.2 :=
                  congrArg Prod.snd (rep_key q)
                rw [htq]
                exact haF
              exact (Finset.mem_filter.1 ht).2
            · intro hadj
              have ht : newF (rep q) ∈ trace G X (allRep q') :=
                Finset.mem_filter.2 ⟨haX0, hadj⟩
              have htq : trace G X (allRep q') = q'.val.2 :=
                congrArg Prod.snd (allRep_key q')
              rw [htq] at ht
              exact (Finset.mem_erase.1 ht).1 rfl
          · intro hs
            exfalso
            apply hs
            exact ⟨rep q, by simp [colors]⟩
      · rintro ⟨hbs, haX', b', hb'rep, hsame, htrace, hpos, hneg⟩
        have hb'rep' : b' ∈ Set.range allRep := by
          simpa [colors] using hb'rep
        obtain ⟨qb, rfl⟩ := hb'rep'
        have hsameLabels : S.tup (allRep qb) = q.val.1 := by
          have heq : S.tup (rep q) = S.tup (allRep qb) := by
            funext i
            obtain ⟨z, hz, hz'⟩ := hsame i
            exact ((hlift i _ (rep_mem q) z).1 hz).trans
              ((hlift i _ (allRep_mem qb) z).1 hz').symm
          exact heq.symm.trans (congrArg Prod.fst (rep_key q))
        have htraceX (x : Fin n) (hx : x ∈ X) (hxa : x ≠ a) :
            G.Adj (rep q) x ↔ G.Adj (allRep qb) x := by
          exact htrace x (by simpa [colors] using hx) hxa
        have hrepTrace : trace G X (rep q) = q.val.2 :=
          congrArg Prod.snd (rep_key q)
        have hF : q.val.2 ∈ S.restrictedPartTraces X q.val.1 := by
          rw [restrictedPartTraces]
          refine Finset.mem_image.2 ⟨trace G S.core (rep q), ?_, ?_⟩
          · exact (S.mem_partTraces_iff _ _).2
              ⟨rep q, rep_mem q, congrArg Prod.fst (rep_key q), rfl⟩
          · exact (trace_inter_eq_of_subset G S.core X hX (rep q)).trans hrepTrace
        have haX'mem : a ∈ X' := by simpa [colors] using haX'
        apply newF_unique q a
        constructor
        · exact haX'mem
        · rcases positive with _ | _
          · simp only [MergeAt, Bool.false_eq, SetSystems.VNeg]
            refine ⟨hF, ?_, ?_⟩
            · intro haq
              have hat : a ∈ trace G X (rep q) := by simpa [hrepTrace] using haq
              exact (hneg (by simp [colors])).1 (Finset.mem_filter.1 hat).2
            · rw [restrictedPartTraces]
              refine Finset.mem_image.2 ⟨trace G S.core (allRep qb), ?_, ?_⟩
              · exact (S.mem_partTraces_iff _ _).2
                  ⟨allRep qb, allRep_mem qb, hsameLabels, rfl⟩
              · rw [trace_inter_eq_of_subset G S.core X hX (allRep qb)]
                ext x
                simp only [trace, Finset.mem_filter, Finset.mem_insert]
                by_cases hxa : x = a
                · subst x
                  have haX : a ∈ X :=
                    Finset.filter_subset _ _ (hX' haX'mem)
                  have hadj := (hneg (by simp [colors])).2
                  simp [haX, hadj]
                · have hxq : x ∈ q.val.2 ↔ x ∈ X ∧ G.Adj (rep q) x := by
                    rw [← hrepTrace]
                    simp [trace]
                  rw [or_iff_right hxa, hxq]
                  constructor
                  · rintro ⟨hx, hadj⟩
                    exact ⟨hx, (htraceX x hx hxa).2 hadj⟩
                  · rintro ⟨hx, hadj⟩
                    exact ⟨hx, (htraceX x hx hxa).1 hadj⟩
          · simp only [MergeAt, if_true, SetSystems.VPos]
            refine ⟨hF, ?_, ?_⟩
            · have haX : a ∈ X :=
                  Finset.filter_subset _ _ (hX' haX'mem)
              have hat : a ∈ trace G X (rep q) :=
                Finset.mem_filter.2 ⟨haX, (hpos ⟨rep q, by simp [colors]⟩).1⟩
              rw [hrepTrace] at hat
              exact hat
            · have hsign : (colors ⟨5 * k + 4, by omega⟩).Nonempty :=
                ⟨rep q, by simp [colors]⟩
              rw [restrictedPartTraces]
              refine Finset.mem_image.2 ⟨trace G S.core (allRep qb), ?_, ?_⟩
              · exact (S.mem_partTraces_iff _ _).2
                  ⟨allRep qb, allRep_mem qb, hsameLabels, rfl⟩
              · rw [trace_inter_eq_of_subset G S.core X hX (allRep qb)]
                ext x
                simp only [trace, Finset.mem_filter, Finset.mem_erase]
                by_cases hxa : x = a
                · subst x
                  have hsign : (colors ⟨5 * k + 4, by omega⟩).Nonempty :=
                    ⟨rep q, by simp [colors]⟩
                  have hadj := (hpos hsign).2
                  simp [hadj]
                · have hxq : x ∈ q.val.2 ↔ x ∈ X ∧ G.Adj (rep q) x := by
                    rw [← hrepTrace]
                    simp [trace]
                  rw [hxq]
                  constructor
                  · rintro ⟨hx, hadj⟩
                    exact ⟨hxa, hx, (htraceX x hx hxa).2 hadj⟩
                  · rintro ⟨-, hx, hadj⟩
                    exact ⟨hx, (htraceX x hx hxa).1 hadj⟩
    · have hformula : sparsFormulas (k + 1) (Fin.castSucc i) =
          liftFormula (by omega) (sparsFormulas k i) := by simp [sparsFormulas]
      rw [hformula]
      rw [realizeIn_liftFormula]
      simpa [S', f', Fin.snoc, colors] using
        (holdColors i (rep q) (rep_mem q) a)
  · simpa [stepLoss, S', Sparsification.size, supp',
      Finset.card_image_of_injective _ rep_inj] using hloss

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
