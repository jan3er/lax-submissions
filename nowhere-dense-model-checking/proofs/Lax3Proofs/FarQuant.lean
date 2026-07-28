import Lax3.Locality
import Lax3Proofs.SyntaxLemmas
import Lax3Proofs.SemLocal
import Lax3Proofs.Clusters
import Lax3Proofs.ScatterCore
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset

/-!
Far quantification (arXiv:2606.23180, Lem. `submain`): a quantifier
that ranges only over the vertices *far* from a tuple is a boolean
combination of local formulas and scatter sentences of the surrounding
distance rank.

Fix a local one-variable formula `β` of distance rank `(k + 1, q)` and
`k` free variables `ȳ`. The statement to be rewritten is

    ∃ x, dist(x, ȳ) > ρ⁻(k + 1, q) ∧ β(x),

and `farQuant` produces a boolean combination of local formulas and
scatter sentences, all of distance rank `(k, q + 1)`, equivalent to it
in every colored graph under every environment. It is the one step of
the locality theorem at which a quantifier ranging arbitrarily far away
is discharged, and the only one that manufactures scatter sentences.

The combinatorial content is `Lax3Proofs.ScatterCore.scatterCore`,
which runs against a cluster system for the tuple at radius
`r = ρ⁻(k + 1, q)` (`Lax3Proofs.Clusters`): the far quantification holds
exactly when either some vertex of `X = {x | β(x)}` sits in the margin
`r < dist(x, ȳ) ≤ ρ⁺(k + 1, q)`, or fewer clusters meet `X` than a
maximal `4R`-scattered subset of `X` has elements. What this file adds
is the *syntax*: both alternatives, and the cluster system itself, are
expressed in the logic.

A cluster system is not a function of the tuple — the source's Vitali
iteration makes choices — so the formula cannot name the one the proof
uses. Instead every *configuration* (a scale exponent `t < k`, a set `I`
of surviving indices, a retraction `sel` onto it) gets a **recognition
formula**, the conjunction of the distance atoms `dist(yᵢ, y_{sel i}) ≤
R` and their negations `dist(yᵢ, y_j) > 8R` at `R = r · 9 ^ t` that say
exactly that this configuration *is* a cluster system for the tuple, and
the boolean combination is the disjunction over configurations of
recognition ∧ branch. Every tuple recognizes at least one configuration
(`nonempty_clusterSystem`) and every recognized configuration decides
the far quantification the same way, so the disjunction is equivalent to
any one of its recognized disjuncts. This is the source's "the number
`R` and the partition can be determined by tests of the form
`dist(aᵢ, a_j) ≤ d`", with the tests written out.

The two branch alternatives are, per configuration:

* the margin formula `∃^{ρ⁺} x, (⋀ᵢ dist(yᵢ, x) > r) ∧ β(x)`, a single
  local quantifier whose guard radius `ρ⁺(k + 1, q)` is exactly what
  distance rank `(k, q + 1)` allows and whose distance atoms are
  budget-exact at `ρ⁻(k + 1, q)`;
* the counting alternative, a disjunction over the subsets `T` of the
  surviving indices of: the cluster tests `∃^{r} x ∈ N_r(sel⁻¹ i), β(x)`
  are true exactly for `i ∈ T`, and the scatter sentence `⟨4R, β,
  |T| + 1⟩` holds. A cluster test is one local quantifier whose *guard
  set* is a fiber of `sel` — the source's `⋁_{aᵢ ∈ P} ∃x dist(x, aᵢ) ≤
  r ∧ β(x)` written as a single guarded quantifier, which the guard sets
  of `Lax3.DistFO` make available.

All radii come out of `Lax3Proofs.Horizon` and the two arithmetic
helpers below; nothing here unfolds `9 ^ _` or the horizon functions.
Boolean combinations are built from `Lax3.Locality.BC` through the small
algebra of `bcOr`, `bcAny`, `bcAll` at the head of the file, whose
`eval` and `atoms` lemmas are what the side conditions of the statement
are read off from.

# Formalization notes

The enumeration of configurations and of the subsets of the surviving
indices goes through `Finset.toList`, which is noncomputable, so `cands`,
`branch` and `full` are noncomputable definitions. Nothing is lost: the
statement of `farQuant`, like that of `Lax3.Locality.locality` it feeds,
asserts that a boolean combination *exists*, and reading a combination
back out of that existential is noncomputable in the Lean sense whatever
the witness is. Effectiveness in the source's sense is a property of the
rewriting *procedure*, which is the business of the algorithm and its
machine model, not of this construction.

The scale of a configuration is carried as an exponent `t : Fin k` and
the radius as `r · 9 ^ t`, matching `Lax3Proofs.Clusters.ClusterSystem`
rather than the source's interval `r ≤ R ≤ 9 ^ (k-1) · r`: the
disjunction has to range over an explicitly indexed finite set of radii,
which the exponent form supplies and the interval form does not. A
configuration is exactly the data half of a cluster system — scale,
surviving set, retraction — with the two distance conditions removed,
since those are what the recognition formula says and hence must not be
assumed of a configuration the formula is built for.
-/

namespace Lax3Proofs.FarQuant

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax3Proofs.Horizon Lax3Proofs.WalkDistance Lax3Proofs.Clusters
open Lax3Proofs.SyntaxLemmas Lax3Proofs.ScatterCore

attribute [local simp] sat_eq sat_distLe sat_not sat_and sat_exL
  isLocal_eq isLocal_distLe isLocal_not isLocal_and isLocal_exL

/-! ### An algebra of boolean combinations

`Lax3.Locality.BC` has only the constructors `atom`, `tru`, `not` and
`and`; disjunction and the two list-indexed connectives are defined
here, with the `eval` and `atoms` lemmas the assembly needs. The clause
lemmas for `BC.eval` and `BC.atoms` come first: handing those
concept-side definitions to `simp` or `rw` would record their match
splitters under the concept's namespace, which a proofs package may not
do.
-/

universe u

section BCAlgebra

variable {α : Type u} {v : α → Prop} {a : α}

/-- Evaluating an atom. -/
theorem eval_atom (b : α) : BC.eval v (.atom b) ↔ v b := Iff.rfl

/-- Evaluating the empty combination. -/
theorem eval_tru : BC.eval v (BC.tru : BC α) ↔ True := Iff.rfl

/-- Evaluating a negation. -/
theorem eval_not (b : BC α) : BC.eval v (.not b) ↔ ¬ BC.eval v b := Iff.rfl

/-- Evaluating a conjunction. -/
theorem eval_and (b c : BC α) : BC.eval v (.and b c) ↔ BC.eval v b ∧ BC.eval v c := Iff.rfl

/-- The atoms of an atom. -/
theorem atoms_atom (b : α) : (BC.atom b).atoms = [b] := rfl

/-- The atoms of the empty combination. -/
theorem atoms_tru : (BC.tru : BC α).atoms = [] := rfl

/-- The atoms of a negation. -/
theorem atoms_not (b : BC α) : (BC.not b).atoms = b.atoms := rfl

/-- The atoms of a conjunction. -/
theorem atoms_and (b c : BC α) : (BC.and b c).atoms = b.atoms ++ c.atoms := rfl

/-- Disjunction of two boolean combinations. -/
def bcOr (b c : BC α) : BC α := .not (.and (.not b) (.not c))

/-- Evaluating a disjunction. -/
theorem eval_bcOr (b c : BC α) : BC.eval v (bcOr b c) ↔ BC.eval v b ∨ BC.eval v c := by
  classical
  simp only [bcOr, eval_not, eval_and, not_and_or, not_not]

/-- The atoms of a disjunction. -/
theorem atoms_bcOr (b c : BC α) : (bcOr b c).atoms = b.atoms ++ c.atoms := rfl

/-- The disjunction of a list of boolean combinations. -/
def bcAny : List (BC α) → BC α
  | [] => .not .tru
  | b :: bs => bcOr b (bcAny bs)

/-- Evaluating a disjunction over a list. -/
theorem eval_bcAny (l : List (BC α)) : BC.eval v (bcAny l) ↔ ∃ b ∈ l, BC.eval v b := by
  induction l with
  | nil => simp [bcAny, eval_not, eval_tru]
  | cons b bs ih => simp [bcAny, eval_bcOr, ih]

/-- The atoms of a disjunction over a list. -/
theorem mem_atoms_bcAny (l : List (BC α)) :
    a ∈ (bcAny l).atoms ↔ ∃ b ∈ l, a ∈ b.atoms := by
  induction l with
  | nil => simp [bcAny, atoms_not, atoms_tru]
  | cons b bs ih => simp [bcAny, atoms_bcOr, ih]

/-- The conjunction of a list of boolean combinations. -/
def bcAll : List (BC α) → BC α
  | [] => .tru
  | b :: bs => .and b (bcAll bs)

/-- Evaluating a conjunction over a list. -/
theorem eval_bcAll (l : List (BC α)) : BC.eval v (bcAll l) ↔ ∀ b ∈ l, BC.eval v b := by
  induction l with
  | nil => simp [bcAll, eval_tru]
  | cons b bs ih => simp [bcAll, eval_and, ih]

/-- The atoms of a conjunction over a list. -/
theorem mem_atoms_bcAll (l : List (BC α)) :
    a ∈ (bcAll l).atoms ↔ ∃ b ∈ l, a ∈ b.atoms := by
  induction l with
  | nil => simp [bcAll, atoms_tru]
  | cons b bs ih => simp [bcAll, atoms_and, ih]

/-- Evaluating a conjunction indexed by a range. -/
theorem eval_bcAll_finRange {j : ℕ} (f : Fin j → BC α) :
    BC.eval v (bcAll ((List.finRange j).map f)) ↔ ∀ i, BC.eval v (f i) := by
  rw [eval_bcAll]
  simp [List.mem_map]

/-- The atoms of a conjunction indexed by a range. -/
theorem mem_atoms_bcAll_finRange {j : ℕ} (f : Fin j → BC α) :
    a ∈ (bcAll ((List.finRange j).map f)).atoms ↔ ∃ i, a ∈ (f i).atoms := by
  rw [mem_atoms_bcAll]
  simp [List.mem_map]

end BCAlgebra

/-! ### Conjunctions of formulas

The distance logic has no truth constant, so a list of formulas is
conjoined *over a base formula* rather than over `⊤`; where a genuinely
empty conjunction is wanted the base is the trivially true equality atom
`yᵢ₀ = yᵢ₀`, which every distance rank admits.
-/

section Conjunctions

variable {L n k : ℕ} {G : SimpleGraph (Fin n)} {col : Coloring n L} {m : Fin k → Fin n}

/-- The conjunction of a list of formulas over a base formula. -/
def andList (φ₀ : DistFO L k) : List (DistFO L k) → DistFO L k
  | [] => φ₀
  | ψ :: ψs => .and ψ (andList φ₀ ψs)

/-- Satisfaction of a conjunction over a list. -/
theorem sat_andList (φ₀ : DistFO L k) (l : List (DistFO L k)) :
    Sat G col m (andList φ₀ l) ↔ (∀ ψ ∈ l, Sat G col m ψ) ∧ Sat G col m φ₀ := by
  induction l with
  | nil => simp [andList]
  | cons ψ ψs ih => simp only [andList, sat_and, ih, List.forall_mem_cons, and_assoc]

/-- Locality of a conjunction over a list. -/
theorem isLocal_andList (φ₀ : DistFO L k) (l : List (DistFO L k)) :
    IsLocal (andList φ₀ l) ↔ (∀ ψ ∈ l, IsLocal ψ) ∧ IsLocal φ₀ := by
  induction l with
  | nil => simp [andList]
  | cons ψ ψs ih => simp only [andList, isLocal_and, ih, List.forall_mem_cons, and_assoc]

/-- The distance rank of a conjunction over a list. -/
theorem drank_andList {k' q : ℕ} {φ₀ : DistFO L k} (h₀ : DRank k' q φ₀) :
    ∀ l : List (DistFO L k), (∀ ψ ∈ l, DRank k' q ψ) → DRank k' q (andList φ₀ l)
  | [], _ => h₀
  | ψ :: ψs, h =>
    .and (h ψ (by simp)) (drank_andList h₀ ψs fun ψ' hψ' => h ψ' (by simp [hψ']))

/-- Satisfaction of a conjunction indexed by a range of variables. -/
theorem sat_andList_finRange {j : ℕ} (φ₀ : DistFO L k) (f : Fin j → DistFO L k) :
    Sat G col m (andList φ₀ ((List.finRange j).map f)) ↔
      (∀ i, Sat G col m (f i)) ∧ Sat G col m φ₀ := by
  rw [sat_andList]
  simp [List.mem_map]

/-- Locality of a conjunction indexed by a range of variables. -/
theorem isLocal_andList_finRange {j : ℕ} (φ₀ : DistFO L k) (f : Fin j → DistFO L k) :
    IsLocal (andList φ₀ ((List.finRange j).map f)) ↔ (∀ i, IsLocal (f i)) ∧ IsLocal φ₀ := by
  rw [isLocal_andList]
  simp [List.mem_map]

/-- The distance rank of a conjunction indexed by a range of variables. -/
theorem drank_andList_finRange {j k' q : ℕ} {φ₀ : DistFO L k} {f : Fin j → DistFO L k}
    (h₀ : DRank k' q φ₀) (h : ∀ i, DRank k' q (f i)) :
    DRank k' q (andList φ₀ ((List.finRange j).map f)) :=
  drank_andList h₀ _ (by
    intro ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hψ
    exact h i)

end Conjunctions

/-! ### Radii

The radius bounds the construction needs, on top of the
`Lax3Proofs.Horizon` lemmas: a scaled radius `x · 9 ^ t` with `t < k`,
multiplied by eight, or by four and increased by `x`, stays below
`9 ^ (k + 1) · x`; and at `x = ρ⁻(k + 1, q)` that bound is `ρ⁺(k + 1, q)`,
hence below `ρ⁻(k, q + 1)`. These are the source's two displayed
inequalities `9 ^ (k-1) · 8 · r ≤ ρ⁻(k, q)` and `4R + r ≤ ρ⁺(k + 1, q)`.
-/

/-- Eight times a scaled radius stays below the next power of nine. -/
theorem eight_mul_scale_le {t k x : ℕ} (ht : t + 1 ≤ k) :
    8 * (x * 9 ^ t) ≤ 9 ^ (k + 1) * x := by
  have h1 : (9 : ℕ) ^ t * 8 ≤ 9 ^ (k + 1) := by
    calc (9 : ℕ) ^ t * 8 ≤ 9 ^ t * 9 := Nat.mul_le_mul_left _ (by norm_num)
      _ = 9 ^ (t + 1) := (pow_succ 9 t).symm
      _ ≤ 9 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 8 * (x * 9 ^ t) = 9 ^ t * 8 * x := by ring
    _ ≤ 9 ^ (k + 1) * x := Nat.mul_le_mul_right x h1

/-- Four times a scaled radius, plus the radius, stays below the next
power of nine. -/
theorem four_mul_scale_add_le {t k x : ℕ} (ht : t + 1 ≤ k) :
    4 * (x * 9 ^ t) + x ≤ 9 ^ (k + 1) * x := by
  have hp : 1 ≤ (9 : ℕ) ^ t := Nat.one_le_pow _ _ (by norm_num)
  have h1 : (9 : ℕ) ^ t * 4 + 1 ≤ 9 ^ (k + 1) := by
    calc (9 : ℕ) ^ t * 4 + 1 ≤ 9 ^ t * 9 := by omega
      _ = 9 ^ (t + 1) := (pow_succ 9 t).symm
      _ ≤ 9 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 4 * (x * 9 ^ t) + x = (9 ^ t * 4 + 1) * x := by ring
    _ ≤ 9 ^ (k + 1) * x := Nat.mul_le_mul_right x h1

/-- A scaled radius is at least the radius it scales. -/
theorem le_scale (x t : ℕ) : x ≤ x * 9 ^ t := by
  have h : 1 ≤ (9 : ℕ) ^ t := Nat.one_le_pow _ _ (by norm_num)
  calc x = x * 1 := (Nat.mul_one x).symm
    _ ≤ x * 9 ^ t := Nat.mul_le_mul_left _ h

/-- The guard horizon one rank level in, as a multiple of the atom
horizon. -/
theorem nine_pow_mul_rhoMinus_le_rhoMinus (k q : ℕ) :
    9 ^ (k + 1) * rhoMinus (k + 1) q ≤ rhoMinus k (q + 1) := by
  rw [← rhoPlus_eq]
  exact rhoPlus_le_rhoMinus k q

/-- The recognition radii of a configuration of scale `t < k` fit under
the atom horizon of the outer rank. -/
theorem eight_scale_le_rhoMinus {k q t : ℕ} (ht : t + 1 ≤ k) :
    8 * (rhoMinus (k + 1) q * 9 ^ t) ≤ rhoMinus k (q + 1) :=
  le_trans (eight_mul_scale_le ht) (nine_pow_mul_rhoMinus_le_rhoMinus k q)

/-- The margin condition of `scatterCore` at the horizon radii. -/
theorem four_scale_add_le_rhoPlus {k q t : ℕ} (ht : t + 1 ≤ k) :
    4 * (rhoMinus (k + 1) q * 9 ^ t) + rhoMinus (k + 1) q ≤ rhoPlus (k + 1) q := by
  rw [rhoPlus_eq]
  exact four_mul_scale_add_le ht

/-! ### The formulas

Four families: the capsule embedding of `β` at the bound variable, the
recognition formula of a configuration, the margin formula, and the
cluster tests.
-/

section Formulas

variable {L n k : ℕ} {G : SimpleGraph (Fin n)} {col : Coloring n L}

/-- The capsule embedding: the one-variable formula `β`, placed at the
variable a binder has just bound. -/
def capsule (k : ℕ) (β : DistFO L 1) : DistFO L (k + 1) :=
  rename (fun _ => Fin.last k) β

/-- The capsule embedding is sound: at an environment extended by `v`,
the embedded formula says of `v` what `β` says. -/
theorem sat_capsule (β : DistFO L 1) (m : Fin k → Fin n) (v : Fin n) :
    Sat G col (Fin.snoc m v) (capsule k β) ↔ Sat G col (fun _ => v) β := by
  rw [capsule, sat_rename]
  have h : (Fin.snoc m v : Fin (k + 1) → Fin n) ∘ (fun _ : Fin 1 => Fin.last k) =
      fun _ => v := by
    funext i
    simp
  rw [h]

/-- The capsule embedding preserves locality. -/
theorem isLocal_capsule (β : DistFO L 1) (hβ : IsLocal β) : IsLocal (capsule k β) :=
  (isLocal_rename β _).2 hβ

/-- The capsule embedding preserves distance rank. -/
theorem drank_capsule {k' q : ℕ} (β : DistFO L 1) (hβ : DRank k' q β) :
    DRank k' q (capsule k β) :=
  DRank.rename hβ _

/-- The far test of a pair of indices: two surviving indices are farther
apart than `8R`. For a pair that is not a pair of distinct surviving
indices the test is the trivially true atom. -/
def farAtom (R : ℕ) (I : Finset (Fin k)) (i₀ i j : Fin k) : DistFO L k :=
  if i ∈ I ∧ j ∈ I ∧ i ≠ j then .not (.distLe (8 * R) i j) else .eq i₀ i₀

/-- The conjunction of the far tests. -/
def farConj (R : ℕ) (I : Finset (Fin k)) (i₀ : Fin k) : DistFO L k :=
  andList (.eq i₀ i₀) ((List.finRange k).map fun i =>
    andList (.eq i₀ i₀) ((List.finRange k).map fun j => farAtom R I i₀ i j))

/-- The recognition formula of a configuration `(R, I, sel)`: every
entry is within `R` of its representative, and two distinct surviving
entries are farther apart than `8R`. -/
def recog (R : ℕ) (I : Finset (Fin k)) (sel : Fin k → Fin k) (i₀ : Fin k) : DistFO L k :=
  andList (farConj R I i₀) ((List.finRange k).map fun i => .distLe R i (sel i))

/-- The margin formula: some vertex within `H` of the tuple, but farther
than `r` from all of it, satisfies `β`. -/
def marginFml (r H : ℕ) (β : DistFO L 1) : DistFO L k :=
  .exL H Finset.univ
    (andList (capsule k β)
      ((List.finRange k).map fun i => .not (.distLe r i.castSucc (Fin.last k))))

/-- The cluster test of a surviving index: some vertex within `r` of an
entry the selection map sends to `i` satisfies `β`. The guard set of the
local quantifier is the fiber of `sel` over `i`. -/
def clusterFml (r : ℕ) (sel : Fin k → Fin k) (i : Fin k) (β : DistFO L 1) : DistFO L k :=
  .exL r (Finset.univ.filter fun j => sel j = i) (capsule k β)

variable {m : Fin k → Fin n} {R r H : ℕ} {I : Finset (Fin k)} {sel : Fin k → Fin k}
  {i₀ : Fin k} {β : DistFO L 1}

/-- Satisfaction of a far test. -/
theorem sat_farAtom (i j : Fin k) :
    Sat G col m (farAtom R I i₀ i j) ↔
      (i ∈ I → j ∈ I → i ≠ j → ¬ WithinDist G (8 * R) (m i) (m j)) := by
  by_cases h : i ∈ I ∧ j ∈ I ∧ i ≠ j
  · rw [farAtom, if_pos h]
    simp only [sat_not, sat_distLe]
    exact ⟨fun hw _ _ _ => hw, fun hw => hw h.1 h.2.1 h.2.2⟩
  · rw [farAtom, if_neg h]
    simp only [sat_eq]
    exact ⟨fun _ hi hj hij => absurd ⟨hi, hj, hij⟩ h, fun _ => trivial⟩

/-- Satisfaction of the recognition formula: the configuration is a
cluster system for the tuple. -/
theorem sat_recog :
    Sat G col m (recog R I sel i₀) ↔
      (∀ i, WithinDist G R (m i) (m (sel i))) ∧
        ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬ WithinDist G (8 * R) (m i) (m j) := by
  rw [recog, sat_andList_finRange, farConj]
  simp only [sat_andList_finRange, sat_farAtom, sat_distLe, sat_eq, and_true]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun i hi j hj hij => h₂ i j hi hj hij⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun i j hi hj hij => h₂ i hi j hj hij⟩

/-- The recognition formula is local. -/
theorem isLocal_recog : IsLocal (recog R I sel i₀ : DistFO L k) := by
  rw [recog, isLocal_andList_finRange]
  refine ⟨fun i => trivial, ?_⟩
  rw [farConj, isLocal_andList_finRange]
  refine ⟨fun i => ?_, trivial⟩
  rw [isLocal_andList_finRange]
  refine ⟨fun j => ?_, trivial⟩
  rw [farAtom]
  split <;> trivial

/-- The distance rank of the recognition formula: its radii are the
radius of the configuration and eight times it. -/
theorem drank_recog {k' q : ℕ} (hR : 8 * R ≤ rhoMinus k' q) :
    DRank k' q (recog R I sel i₀ : DistFO L k) := by
  have hR' : R ≤ rhoMinus k' q := le_trans (by omega) hR
  rw [recog]
  refine drank_andList_finRange ?_ fun i => .distLe _ _ hR'
  rw [farConj]
  refine drank_andList_finRange (.eq _ _) fun i => ?_
  refine drank_andList_finRange (.eq _ _) fun j => ?_
  rw [farAtom]
  split
  · exact .not (.distLe _ _ hR)
  · exact .eq _ _

/-- Satisfaction of the margin formula. -/
theorem sat_marginFml :
    Sat G col m (marginFml r H β) ↔
      ∃ x, (∃ i, WithinDist G H (m i) x) ∧ (∀ i, ¬ WithinDist G r (m i) x) ∧
        Sat G col (fun _ => x) β := by
  rw [marginFml]
  simp only [sat_exL, sat_andList_finRange, sat_capsule, sat_not, sat_distLe,
    Fin.snoc_castSucc, Fin.snoc_last, Finset.mem_univ, true_and]

/-- The margin formula is local. -/
theorem isLocal_marginFml (hβ : IsLocal β) : IsLocal (marginFml r H β : DistFO L k) := by
  rw [marginFml, isLocal_exL, isLocal_andList_finRange]
  exact ⟨fun i => trivial, isLocal_capsule β hβ⟩

/-- The distance rank of the margin formula: its guard radius is the
guard horizon and its distance atoms are budget-exact. -/
theorem drank_marginFml {k' q : ℕ} (hβ : DRank (k' + 1) q β)
    (hr : r ≤ rhoMinus (k' + 1) q) (hH : H ≤ rhoPlus (k' + 1) q) :
    DRank k' (q + 1) (marginFml r H β : DistFO L k) := by
  rw [marginFml]
  exact .exL (drank_andList_finRange (drank_capsule β hβ) fun i => .not (.distLe _ _ hr)) hH

/-- Satisfaction of a cluster test: the cluster of `i` meets the set
defined by `β`. -/
theorem sat_clusterFml (i : Fin k) :
    Sat G col m (clusterFml r sel i β) ↔
      ({x | Sat G col (fun _ => x) β} ∩ cluster G r m sel i).Nonempty := by
  rw [clusterFml]
  simp only [sat_exL, sat_capsule, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, ⟨j, hj, hjv⟩, hv⟩
    exact ⟨v, hv, mem_cluster.2 ⟨j, hj, hjv⟩⟩
  · rintro ⟨v, hv, hvc⟩
    obtain ⟨j, hj, hjv⟩ := mem_cluster.1 hvc
    exact ⟨v, ⟨j, hj, hjv⟩, hv⟩

/-- A cluster test is local. -/
theorem isLocal_clusterFml (i : Fin k) (hβ : IsLocal β) :
    IsLocal (clusterFml r sel i β : DistFO L k) := by
  rw [clusterFml, isLocal_exL]
  exact isLocal_capsule β hβ

/-- The distance rank of a cluster test. -/
theorem drank_clusterFml {k' q : ℕ} (i : Fin k) (hβ : DRank (k' + 1) q β)
    (hr : r ≤ rhoPlus (k' + 1) q) :
    DRank k' (q + 1) (clusterFml r sel i β : DistFO L k) := by
  rw [clusterFml]
  exact .exL (drank_capsule β hβ) hr

end Formulas

/-! ### The boolean combination

The combination is the disjunction over configurations of
`recognition ∧ branch`; a branch is the margin formula or the counting
alternative, and the counting alternative is the disjunction over
subsets `T` of the surviving indices of `pattern ∧ scatter sentence`.
-/

section Assembly

variable {L n k : ℕ} {G : SimpleGraph (Fin n)} {col : Coloring n L}

/-- The truth of a scatter sentence, spelled out. Like the clause
lemmas of `Lax3Proofs.SyntaxLemmas`, this is here so that no tactic is
handed the concept-side definition. -/
theorem sat_scatterSentence (choice : ScatterChoice) (R' : ℕ) (β : DistFO L 1) (c : ℕ) :
    ScatterSentence.Sat choice G col ⟨R', β, c⟩ ↔
      c ≤ choice.size G R' {a | Sat G col (fun _ => a) β} := Iff.rfl

/-- The counting pattern of a subset `T` of the surviving indices: the
cluster tests hold exactly at the indices in `T`. -/
def pattern (r : ℕ) (I T : Finset (Fin k)) (sel : Fin k → Fin k) (β : DistFO L 1) :
    BC (DistFO L k ⊕ ScatterSentence L) :=
  bcAll ((List.finRange k).map fun i =>
    if i ∈ I then
      (if i ∈ T then .atom (.inl (clusterFml r sel i β))
        else .not (.atom (.inl (clusterFml r sel i β))))
    else .tru)

/-- The counting branch of a subset: its pattern holds, and the scatter
value at radius `R'` exceeds its cardinality. -/
def countBranch (r R' : ℕ) (I T : Finset (Fin k)) (sel : Fin k → Fin k) (β : DistFO L 1) :
    BC (DistFO L k ⊕ ScatterSentence L) :=
  .and (pattern r I T sel β) (.atom (.inr ⟨R', β, T.card + 1⟩))

/-- The branch of a configuration: the margin formula, or the counting
alternative over all subsets of the surviving indices. -/
noncomputable def branch (r H R : ℕ) (I : Finset (Fin k)) (sel : Fin k → Fin k)
    (β : DistFO L 1) : BC (DistFO L k ⊕ ScatterSentence L) :=
  bcOr (.atom (.inl (marginFml r H β)))
    (bcAny (I.powerset.toList.map fun T => countBranch r (4 * R) I T sel β))

/-- The configurations a cluster system can have: a scale exponent below
`k`, a set of surviving indices, and a retraction onto it. -/
noncomputable def cands (k : ℕ) : List (Fin k × Finset (Fin k) × (Fin k → Fin k)) :=
  (Finset.univ.filter fun d => (∀ i, d.2.2 i ∈ d.2.1) ∧ ∀ i ∈ d.2.1, d.2.2 i = i).toList

/-- Membership in the list of configurations. -/
theorem mem_cands {d : Fin k × Finset (Fin k) × (Fin k → Fin k)} :
    d ∈ cands k ↔ (∀ i, d.2.2 i ∈ d.2.1) ∧ ∀ i ∈ d.2.1, d.2.2 i = i := by
  classical
  rw [cands, Finset.mem_toList, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The boolean combination `farQuant` produces: over all
configurations, the recognition formula of the configuration together
with its branch. -/
noncomputable def full (r H : ℕ) (i₀ : Fin k) (β : DistFO L 1) :
    BC (DistFO L k ⊕ ScatterSentence L) :=
  bcAny ((cands k).map fun d =>
    .and (.atom (.inl (recog (r * 9 ^ (d.1 : ℕ)) d.2.1 d.2.2 i₀)))
      (branch r H (r * 9 ^ (d.1 : ℕ)) d.2.1 d.2.2 β))

/-! ### Evaluation -/

/-- Evaluating a counting pattern: the cluster tests hold exactly at the
indices of `T`. -/
theorem eval_pattern (choice : ScatterChoice) (r : ℕ) (I T : Finset (Fin k))
    (sel : Fin k → Fin k) (β : DistFO L 1) (m : Fin k → Fin n) :
    BC.eval (Sum.elim (Sat G col m) (ScatterSentence.Sat choice G col))
        (pattern r I T sel β) ↔
      ∀ i ∈ I, (i ∈ T ↔ Sat G col m (clusterFml r sel i β)) := by
  rw [pattern, eval_bcAll_finRange]
  refine forall_congr' fun i => ?_
  by_cases hI : i ∈ I
  · by_cases hT : i ∈ T <;>
      simp [hI, hT, eval_atom, eval_not]
  · simp [hI, eval_tru]

/-- Evaluating the counting alternative: fewer clusters meet the set
defined by `β` than the scatter value at the radius `R'`. -/
theorem eval_counting (choice : ScatterChoice) (r R' : ℕ) (I : Finset (Fin k))
    (sel : Fin k → Fin k) (β : DistFO L 1) (m : Fin k → Fin n) (s : ℕ)
    (hs : choice.size G R' {x | Sat G col (fun _ => x) β} = s) :
    BC.eval (Sum.elim (Sat G col m) (ScatterSentence.Sat choice G col))
        (bcAny (I.powerset.toList.map fun T => countBranch r R' I T sel β)) ↔
      {i | i ∈ I ∧ ({x | Sat G col (fun _ => x) β} ∩ cluster G r m sel i).Nonempty}.ncard < s := by
  classical
  rw [eval_bcAny]
  have hcard :
      {i | i ∈ I ∧ ({x | Sat G col (fun _ => x) β} ∩ cluster G r m sel i).Nonempty}.ncard =
        (I.filter fun i =>
          ({x | Sat G col (fun _ => x) β} ∩ cluster G r m sel i).Nonempty).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp
  rw [hcard]
  constructor
  · rintro ⟨b, hb, hbe⟩
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hb
    rw [Finset.mem_toList, Finset.mem_powerset] at hT
    rw [countBranch, eval_and, eval_pattern, eval_atom, Sum.elim_inr,
      sat_scatterSentence, hs] at hbe
    obtain ⟨hpat, hsc⟩ := hbe
    have hTeq : T = I.filter fun i =>
        ({x | Sat G col (fun _ => x) β} ∩ cluster G r m sel i).Nonempty := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · intro hi
        exact ⟨hT hi, (sat_clusterFml i).1 ((hpat i (hT hi)).1 hi)⟩
      · rintro ⟨hiI, hne⟩
        exact (hpat i hiI).2 ((sat_clusterFml i).2 hne)
    rw [← hTeq]
    omega
  · intro hlt
    refine ⟨_, List.mem_map.2 ⟨I.filter fun i =>
      ({x | Sat G col (fun _ => x) β} ∩ cluster G r m sel i).Nonempty, ?_, rfl⟩, ?_⟩
    · rw [Finset.mem_toList, Finset.mem_powerset]
      exact Finset.filter_subset _ _
    · rw [countBranch, eval_and, eval_pattern, eval_atom, Sum.elim_inr,
        sat_scatterSentence, hs]
      refine ⟨fun i hi => ?_, by omega⟩
      rw [sat_clusterFml, Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩

/-- The branch of a *recognized* configuration decides the far
quantification: this is `Lax3Proofs.ScatterCore.scatterCore`, with both
of its alternatives read off the syntax. -/
theorem eval_branch_iff (choice : ScatterChoice) {q' : ℕ} (β : DistFO L 1) (m : Fin k → Fin n)
    (C : ClusterSystem G (rhoMinus (k + 1) q') m) :
    BC.eval (Sum.elim (Sat G col m) (ScatterSentence.Sat choice G col))
        (branch (rhoMinus (k + 1) q') (rhoPlus (k + 1) q') C.R C.I C.sel β) ↔
      ∃ x, (∀ i, ¬ WithinDist G (rhoMinus (k + 1) q') (m i) x) ∧
        Sat G col (fun _ => x) β := by
  classical
  obtain ⟨S, hSX, hSmax, hScard⟩ := choice.spec G (4 * C.R) {x | Sat G col (fun _ => x) β}
  have hmargin : 4 * C.R + rhoMinus (k + 1) q' ≤ rhoPlus (k + 1) q' := by
    rw [ClusterSystem.R_eq]
    exact four_scale_add_le_rhoPlus C.ht
  have key := scatterCore C (Set.toFinite S) hSmax hmargin
  have h2a : Sat G col m (marginFml (rhoMinus (k + 1) q') (rhoPlus (k + 1) q') β) ↔
      ∃ x ∈ {x | Sat G col (fun _ => x) β},
        (∃ i, WithinDist G (rhoPlus (k + 1) q') (m i) x) ∧
          ∀ i, ¬ WithinDist G (rhoMinus (k + 1) q') (m i) x := by
    rw [sat_marginFml]
    exact exists_congr fun x =>
      ⟨fun h => ⟨h.2.2, h.1, h.2.1⟩, fun h => ⟨h.2.1, h.2.2, h.1⟩⟩
  rw [branch, eval_bcOr, eval_atom, Sum.elim_inl, h2a,
    eval_counting choice _ _ _ _ _ _ S.ncard hScard.symm, ← key]
  exact exists_congr fun x => and_comm

/-! ### The atoms -/

/-- Every atom of the combination is a recognition formula, the margin
formula, a cluster test, or one of the scatter sentences. -/
theorem mem_atoms_full {r H : ℕ} {i₀ : Fin k} {β : DistFO L 1}
    {a : DistFO L k ⊕ ScatterSentence L} (h : a ∈ (full r H i₀ β).atoms) :
    (∃ (t : Fin k) (I : Finset (Fin k)) (sel : Fin k → Fin k),
        a = Sum.inl (recog (r * 9 ^ (t : ℕ)) I sel i₀)) ∨
      a = Sum.inl (marginFml r H β) ∨
      (∃ (sel : Fin k → Fin k) (i : Fin k), a = Sum.inl (clusterFml r sel i β)) ∨
      ∃ (t : Fin k) (c : ℕ), c ≤ k ∧ a = Sum.inr ⟨4 * (r * 9 ^ (t : ℕ)), β, c + 1⟩ := by
  classical
  rw [full, mem_atoms_bcAny] at h
  obtain ⟨b, hb, ha⟩ := h
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 hb
  rw [atoms_and, List.mem_append, atoms_atom, List.mem_singleton] at ha
  rcases ha with rfl | ha
  · exact Or.inl ⟨d.1, d.2.1, d.2.2, rfl⟩
  rw [branch, atoms_bcOr, List.mem_append, atoms_atom, List.mem_singleton] at ha
  rcases ha with rfl | ha
  · exact Or.inr (Or.inl rfl)
  rw [mem_atoms_bcAny] at ha
  obtain ⟨b', hb', ha⟩ := ha
  obtain ⟨T, -, rfl⟩ := List.mem_map.1 hb'
  rw [countBranch, atoms_and, List.mem_append, atoms_atom, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · rw [pattern, mem_atoms_bcAll_finRange] at ha
    obtain ⟨i, hi⟩ := ha
    refine Or.inr (Or.inr (Or.inl ⟨d.2.2, i, ?_⟩))
    split_ifs at hi <;>
      simp only [atoms_not, atoms_atom, atoms_tru, List.mem_singleton,
        List.not_mem_nil] at hi <;>
      simp [hi]
  · exact Or.inr (Or.inr (Or.inr ⟨d.1, T.card, by simpa using Finset.card_le_univ T, rfl⟩))

/-- The formula atoms of the combination are local of the outer distance
rank. -/
theorem isLocal_drank_of_inl_mem_atoms_full {q' : ℕ} {i₀ : Fin k} {β : DistFO L 1}
    (hloc : IsLocal β) (hβ : DRank (k + 1) q' β) (ψ : DistFO L k)
    (h : Sum.inl ψ ∈ (full (rhoMinus (k + 1) q') (rhoPlus (k + 1) q') i₀ β).atoms) :
    IsLocal ψ ∧ DRank k (q' + 1) ψ := by
  rcases mem_atoms_full h with ⟨t, I, sel, ht⟩ | ht | ⟨sel, i, ht⟩ | ⟨t, c, -, ht⟩
  · obtain rfl := Sum.inl.inj ht
    exact ⟨isLocal_recog, drank_recog (eight_scale_le_rhoMinus t.isLt)⟩
  · obtain rfl := Sum.inl.inj ht
    exact ⟨isLocal_marginFml hloc, drank_marginFml hβ le_rfl le_rfl⟩
  · obtain rfl := Sum.inl.inj ht
    exact ⟨isLocal_clusterFml i hloc, drank_clusterFml i hβ (rhoMinus_le_rhoPlus _ _)⟩
  · exact absurd ht (by simp)

/-- The scatter-sentence atoms of the combination have the outer
distance rank: at most `k + 1` witnesses, and a radius in the source's
window around `4ρ⁻(k + 1, q)`. -/
theorem drank_of_inr_mem_atoms_full {q' : ℕ} {i₀ : Fin k} {β : DistFO L 1}
    (hloc : IsLocal β) (hβ : DRank (k + 1) q' β) (σ : ScatterSentence L)
    (h : Sum.inr σ ∈ (full (rhoMinus (k + 1) q') (rhoPlus (k + 1) q') i₀ β).atoms) :
    σ.DRank k (q' + 1) := by
  rcases mem_atoms_full h with ⟨t, I, sel, ht⟩ | ht | ⟨sel, i, ht⟩ | ⟨t, c, hc, ht⟩
  · exact absurd ht (by simp)
  · exact absurd ht (by simp)
  · exact absurd ht (by simp)
  · obtain rfl := Sum.inr.inj ht
    rw [scatterSentence_drank_iff]
    refine ⟨by show c + 1 ≤ k + (q' + 1); omega, 1, le_rfl, by omega, hloc, hβ, ?_, ?_⟩
    · exact Nat.mul_le_mul_left _ (le_scale _ _)
    · exact le_trans (Nat.le_add_right _ _) (four_mul_scale_add_le t.isLt)

end Assembly

/-! ### The lemma -/

/-- **Far quantification** (Lem. `submain` of arXiv:2606.23180). For a
local one-variable formula `β` of distance rank `(k + 1, q)`, the
statement *some vertex farther than ρ⁻(k + 1, q) from the tuple
satisfies `β`* is a boolean combination of local formulas and scatter
sentences of distance rank `(k, q + 1)`.

The combination is `full`: over all configurations of a cluster system
for the tuple at radius ρ⁻(k + 1, q), the recognition formula of the
configuration conjoined with its branch. Every tuple recognizes some
configuration, by `Lax3Proofs.Clusters.nonempty_clusterSystem`, and a
recognized configuration decides the statement by `eval_branch_iff`, so
the disjunction is equivalent to the statement. -/
theorem farQuant {L : ℕ} (choice : ScatterChoice) {k q' : ℕ} (hk : 1 ≤ k)
    (β : DistFO L 1) (hloc : IsLocal β) (hβ : DRank (k + 1) q' β) :
    ∃ bc : BC (DistFO L k ⊕ ScatterSentence L),
      (∀ ψ : DistFO L k, Sum.inl ψ ∈ bc.atoms → IsLocal ψ ∧ DRank k (q' + 1) ψ) ∧
      (∀ σ : ScatterSentence L, Sum.inr σ ∈ bc.atoms → σ.DRank k (q' + 1)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
        ((∃ x, (∀ i, ¬ WithinDist G (rhoMinus (k + 1) q') (m i) x) ∧
            Sat G col (fun _ => x) β) ↔
          bc.eval (Sum.elim (Sat G col m) (ScatterSentence.Sat choice G col))) := by
  classical
  refine ⟨full (rhoMinus (k + 1) q') (rhoPlus (k + 1) q') ⟨0, hk⟩ β,
    fun ψ h => isLocal_drank_of_inl_mem_atoms_full hloc hβ ψ h,
    fun σ h => drank_of_inr_mem_atoms_full hloc hβ σ h, ?_⟩
  intro n G col m
  rw [full, eval_bcAny]
  constructor
  · intro hfar
    obtain ⟨C⟩ := nonempty_clusterSystem G (rhoMinus (k + 1) q') hk m
    refine ⟨_, List.mem_map.2 ⟨(⟨C.t, C.ht⟩, C.I, C.sel), mem_cands.2 ⟨C.sel_mem, C.sel_id⟩, rfl⟩,
      ?_⟩
    rw [eval_and, eval_atom, Sum.elim_inl]
    exact ⟨sat_recog.2 ⟨C.sel_close, C.far⟩, (eval_branch_iff choice β m C).2 hfar⟩
  · rintro ⟨b, hb, hbe⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hb
    rw [eval_and, eval_atom, Sum.elim_inl] at hbe
    obtain ⟨hmem, hid⟩ := mem_cands.1 hd
    obtain ⟨hclose, hfar⟩ := sat_recog.1 hbe.1
    exact (eval_branch_iff choice β m
      { t := (d.1 : ℕ), ht := d.1.isLt, I := d.2.1, sel := d.2.2, sel_mem := hmem,
        sel_id := hid, sel_close := hclose, far := hfar }).1 hbe.2

end Lax3Proofs.FarQuant
