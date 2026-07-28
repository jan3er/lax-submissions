import Lax3.NormalForm
import Lax3Proofs.SyntaxLemmas
import Lax3Proofs.SemLocal
import Lax3Proofs.ScatterCore

/-!
Correctness of `Lax3.NormalForm.scatterFml`, the source's scatter
sentence written out in distance logic, under the maximum-size scatter
choice: `sat_scatterFml` says that

    Sat G col Fin.elim0 (scatterFml r t β) ↔
      ScatterSentence.Sat maxChoice G col ⟨r, β, t⟩,

with no rank and no locality hypothesis. Both readings say "some
`r`-scattered set of `t` vertices satisfies `β`" — the left one by
quantifying `t` vertices and writing the pairwise distance conditions and
the `t` placements of `β` as a conjunction, the right one by comparing
`t` with the largest size of an `r`-scattered subset of the set `β`
defines. Everything in between is bookkeeping: `Fin.snoc` for the
quantifier block, list membership for the conjunction, and `Set.ncard`
arithmetic against `sSup` for the two counting directions.

The placement of `β` at the `i`-th bound variable is a `rename`, and the
guard-set surface of `Lax3.DistFO` makes `sat_rename` unconditional, so
no side condition on `β` enters — in particular the theorem holds for a
`β` with local quantifiers, whose guards keep naming the one variable
they named before the placement.

The file also carries the three side conditions the `normalForm`
assembly must produce for each scatter sentence it emits, all read off
the distance rank of the sentence: `drank_succ_pred_of_drank`
(`β` has distance rank `(k+1, q−1)`), `r_le_rhoMinus_of_drank` (the
radius stays below ρ⁻(k, q), the high end of the source's radius window
climbed back along the antidiagonal) and
`semanticallyLocal_div_four_of_drank` (`β` is semantically `r/4`-local,
the low end of the window fed to `Lax3Proofs.SemLocal`).

No concept-side definition is handed to a tactic here: `verum`, `conj`,
`exUs`, `scatterFml`, `Sat`, `ScatterSentence.Sat`, `ScatterChoice.size`,
`maxChoice`, `SemanticallyLocal` and the rest are taken apart through the
`rfl`-lemmas of the unfolding section, as in `Lax3Proofs.SyntaxLemmas`.
Radius inequalities go through `Lax3Proofs.Horizon`; nothing here unfolds
`9 ^ _`.
-/

namespace Lax3Proofs.ScatterFml

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality Lax3.NormalForm
open Lax3Proofs.Horizon Lax3Proofs.WalkDistance
open Lax3Proofs.SyntaxLemmas Lax3Proofs.SemLocal Lax3Proofs.ScatterCore
open Lax12.UniformQuasiWideness

variable {L n : ℕ}

/-! ### Unfolding the concept-side definitions

One `rfl`-lemma per clause of each concept-side definition this file
takes apart, exactly as in the unfolding section of
`Lax3Proofs.SyntaxLemmas` and for the same reason: a tactic handed one of
these definitions would manufacture its match splitters and record them
under the concept's namespace.
-/

section Unfolding

variable {G : SimpleGraph (Fin n)} {col : Coloring n L} {k : ℕ}

/-- `verum` spelled out: no vertex differs from itself. -/
theorem verum_eq : (verum : DistFO L k) = .not (.exU (.not (.eq (Fin.last k) (Fin.last k)))) :=
  rfl

/-- The empty conjunction. -/
theorem conj_nil : conj ([] : List (DistFO L k)) = verum := rfl

/-- A nonempty conjunction. -/
theorem conj_cons (φ : DistFO L k) (φs : List (DistFO L k)) :
    conj (φ :: φs) = .and φ (conj φs) := rfl

/-- A sentence needs no quantifier block. -/
theorem exUs_zero (φ : DistFO L 0) : exUs φ = φ := rfl

/-- One quantifier of the block, peeled from the inside. -/
theorem exUs_succ (φ : DistFO L (k + 1)) : exUs φ = exUs (DistFO.exU φ) := rfl

/-- The written-out scatter sentence, spelled out. -/
theorem scatterFml_eq (r t : ℕ) (β : DistFO L 1) :
    scatterFml r t β =
      exUs (conj
        (((List.finRange t).flatMap fun i =>
            (List.finRange t).filterMap fun j =>
              if i = j then none else some (DistFO.not (DistFO.distLe r i j))) ++
          (List.finRange t).map fun i => rename (fun _ : Fin 1 => i) β)) := rfl

/-- Satisfaction of a scatter sentence, spelled out. -/
theorem scatterSentence_sat_iff (choice : ScatterChoice) (G : SimpleGraph (Fin n))
    (col : Coloring n L) (r t : ℕ) (β : DistFO L 1) :
    ScatterSentence.Sat choice G col ⟨r, β, t⟩ ↔
      t ≤ choice.size G r {a | Sat G col (fun _ => a) β} := Iff.rfl

/-- The maximum-size scatter choice, spelled out. -/
theorem maxChoice_size (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    maxChoice.size G r X =
      sSup {c | ∃ S : Set (Fin n), S ⊆ X ∧ DistIndependent G r S ∧ S.ncard = c} := rfl

/-- Semantic locality, spelled out. -/
theorem semanticallyLocal_iff (r : ℕ) (φ : DistFO L k) :
    SemanticallyLocal r φ ↔
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
        Sat G col m φ ↔ SatWithin (⋃ i, ball G r (m i)) G col m φ := Iff.rfl

end Unfolding

/-! ### Satisfaction of the pieces -/

variable {G : SimpleGraph (Fin n)} {col : Coloring n L}

/-- `verum` holds in every colored graph under every environment. -/
theorem sat_verum {k : ℕ} (m : Fin k → Fin n) : Sat G col m (verum : DistFO L k) := by
  rw [verum_eq, sat_not]
  rintro ⟨v, hv⟩
  exact hv rfl

/-- Satisfaction of a list conjunction. -/
theorem sat_conj {k : ℕ} (m : Fin k → Fin n) (l : List (DistFO L k)) :
    Sat G col m (conj l) ↔ ∀ φ ∈ l, Sat G col m φ := by
  induction l with
  | nil => exact iff_of_true (conj_nil ▸ sat_verum m) (by simp)
  | cons φ φs ih => simp [conj_cons, sat_and, ih]

/-- Satisfaction of a block of unrestricted quantifiers: the sentence
holds exactly when some environment satisfies the body. The induction is
on the arity, and `Fin.snoc_init_self` is what makes the step an
equivalence: every environment of arity `k + 1` is an extension of its
own initial segment. -/
theorem sat_exUs : ∀ {t : ℕ} (φ : DistFO L t),
    Sat G col Fin.elim0 (exUs φ) ↔ ∃ m : Fin t → Fin n, Sat G col m φ := by
  intro t
  induction t with
  | zero =>
    intro φ
    rw [exUs_zero]
    refine ⟨fun h => ⟨Fin.elim0, h⟩, ?_⟩
    rintro ⟨m, hm⟩
    rwa [show m = Fin.elim0 from funext fun i => i.elim0] at hm
  | succ t ih =>
    intro φ
    rw [exUs_succ, ih (DistFO.exU φ)]
    simp only [sat_exU]
    constructor
    · rintro ⟨m, v, hv⟩
      exact ⟨Fin.snoc m v, hv⟩
    · rintro ⟨m, hm⟩
      exact ⟨Fin.init m, m (Fin.last t), by rwa [Fin.snoc_init_self]⟩

/-- The conjuncts of the written-out scatter sentence, read off: an
environment satisfies all of them exactly when its `t` values are
pairwise farther than `r` apart and each satisfies `β`. The placements of
`β` are renamings, so `sat_rename` disposes of them with no side
condition. -/
theorem sat_conjuncts (r t : ℕ) (β : DistFO L 1) (m : Fin t → Fin n) :
    (∀ φ ∈ (((List.finRange t).flatMap fun i =>
          (List.finRange t).filterMap fun j =>
            if i = j then none else some (DistFO.not (DistFO.distLe (L := L) r i j))) ++
        (List.finRange t).map fun i => rename (fun _ : Fin 1 => i) β),
        Sat G col m φ) ↔
      ((∀ i j : Fin t, i ≠ j → ¬ WithinDist G r (m i) (m j)) ∧
        ∀ i : Fin t, Sat G col (fun _ => m i) β) := by
  constructor
  · intro h
    constructor
    · intro i j hij
      have hmem : DistFO.not (DistFO.distLe (L := L) r i j) ∈
          ((List.finRange t).flatMap fun i =>
            (List.finRange t).filterMap fun j =>
              if i = j then none else some (DistFO.not (DistFO.distLe (L := L) r i j))) := by
        rw [List.mem_flatMap]
        refine ⟨i, List.mem_finRange i, ?_⟩
        rw [List.mem_filterMap]
        exact ⟨j, List.mem_finRange j, by rw [if_neg hij]⟩
      have := h _ (List.mem_append_left _ hmem)
      rwa [sat_not, sat_distLe] at this
    · intro i
      have hmem : rename (fun _ : Fin 1 => i) β ∈
          ((List.finRange t).map fun i => rename (fun _ : Fin 1 => i) β) :=
        List.mem_map_of_mem (List.mem_finRange i)
      have := h _ (List.mem_append_right _ hmem)
      rwa [sat_rename] at this
  · rintro ⟨hfar, hβ⟩ φ hφ
    rcases List.mem_append.mp hφ with hφ | hφ
    · rw [List.mem_flatMap] at hφ
      obtain ⟨i, -, hφ⟩ := hφ
      rw [List.mem_filterMap] at hφ
      obtain ⟨j, -, hj⟩ := hφ
      by_cases hij : i = j
      · rw [if_pos hij] at hj
        exact absurd hj (by simp)
      · rw [if_neg hij, Option.some_inj] at hj
        subst hj
        rw [sat_not, sat_distLe]
        exact hfar i j hij
    · rw [List.mem_map] at hφ
      obtain ⟨i, -, hi⟩ := hφ
      subst hi
      rw [sat_rename]
      exact hβ i

/-- The written-out scatter sentence, read semantically: it holds exactly
when `t` vertices, pairwise farther than `r` apart, all satisfy `β`. -/
theorem sat_scatterFml_iff_exists (r t : ℕ) (β : DistFO L 1) :
    Sat G col Fin.elim0 (scatterFml r t β) ↔
      ∃ m : Fin t → Fin n,
        (∀ i j : Fin t, i ≠ j → ¬ WithinDist G r (m i) (m j)) ∧
        ∀ i : Fin t, Sat G col (fun _ => m i) β := by
  rw [scatterFml_eq, sat_exUs]
  exact exists_congr fun m => (sat_conj m _).trans (sat_conjuncts r t β m)

/-! ### The maximum-size scatter choice

`maxChoice.size G r X` is the supremum of the sizes of the `r`-scattered
subsets of `X`. That set of sizes is nonempty and bounded by the number
of vertices, which is all the two counting directions need; the argument
is the one inside `maxChoice`'s own definition.
-/

/-- The set of sizes of `r`-scattered subsets of `X`, whose supremum the
maximum-size scatter choice is. -/
def scatterSizes (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) : Set ℕ :=
  {c | ∃ S : Set (Fin n), S ⊆ X ∧ DistIndependent G r S ∧ S.ncard = c}

/-- The empty set is scattered, so a size is always available. -/
theorem scatterSizes_nonempty (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    (scatterSizes G r X).Nonempty :=
  ⟨0, ∅, Set.empty_subset _, Set.pairwise_empty _, Set.ncard_empty _⟩

/-- No subset of the vertices has more than `n` elements. -/
theorem bddAbove_scatterSizes (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    BddAbove (scatterSizes G r X) := by
  refine ⟨n, ?_⟩
  rintro c ⟨S, -, -, rfl⟩
  calc S.ncard ≤ (Set.univ : Set (Fin n)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ S) Set.finite_univ
    _ = n := by simp

/-- A scattered subset is no larger than the maximum-size scatter value. -/
theorem ncard_le_maxChoice_size (G : SimpleGraph (Fin n)) {r : ℕ} {S X : Set (Fin n)}
    (hSX : S ⊆ X) (hS : DistIndependent G r S) : S.ncard ≤ maxChoice.size G r X :=
  le_csSup (bddAbove_scatterSizes G r X) ⟨S, hSX, hS, rfl⟩

/-- The maximum-size scatter value is attained by a scattered subset: over
`Fin n` the supremum is a maximum. -/
theorem exists_scattered_ncard_eq (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)) :
    ∃ S : Set (Fin n), S ⊆ X ∧ DistIndependent G r S ∧ S.ncard = maxChoice.size G r X :=
  Nat.sSup_mem (scatterSizes_nonempty G r X) (bddAbove_scatterSizes G r X)

/-- A set of `t` vertices, enumerated injectively by `Fin t`. -/
theorem exists_injective_of_ncard_eq {t : ℕ} (T : Set (Fin n)) (h : T.ncard = t) :
    ∃ m : Fin t → Fin n, Function.Injective m ∧ ∀ i, m i ∈ T := by
  have hT : T.Finite := Set.toFinite T
  have hcard : hT.toFinset.card = t := (Set.ncard_eq_toFinset_card T hT).symm.trans h
  let e : ↥hT.toFinset ≃ Fin t := hT.toFinset.equivFin.trans (finCongr hcard)
  refine ⟨fun i => (e.symm i : Fin n), fun i j hij => ?_,
    fun i => hT.mem_toFinset.mp (e.symm i).2⟩
  exact e.symm.injective (Subtype.ext hij)

/-! ### Correctness of the written-out scatter sentence -/

/-- **The written-out scatter sentence is the scatter sentence.** Under
the maximum-size scatter choice, the sentence "there are `t` vertices,
pairwise at distance larger than `r`, all satisfying `β`" of
`Lax3.NormalForm.scatterFml` holds exactly when the scatter sentence
`⟨r, β, t⟩` does. This is the step from the locality theorem to the
normal form: with the maximum-size choice the scatter value is definable
in the logic itself.

Forward, the `t` witnesses form an `r`-scattered subset of the set `β`
defines — they are pairwise farther than `r` apart, hence in particular
distinct — of size exactly `t`, so the supremum is at least `t`.
Backward, the supremum is attained over `Fin n`, so a scattered subset of
size at least `t` exists; any `t` of its elements enumerate a satisfying
environment. -/
theorem sat_scatterFml (r t : ℕ) (β : DistFO L 1) (G : SimpleGraph (Fin n))
    (col : Coloring n L) :
    Sat G col Fin.elim0 (scatterFml r t β) ↔
      ScatterSentence.Sat maxChoice G col ⟨r, β, t⟩ := by
  rw [sat_scatterFml_iff_exists, scatterSentence_sat_iff]
  constructor
  · rintro ⟨m, hfar, hβ⟩
    have hinj : Function.Injective m := by
      intro i j hij
      by_contra hne
      exact hfar i j hne (withinDist_of_eq G r hij)
    have hsub : Set.range m ⊆ {a | Sat G col (fun _ => a) β} := by
      rintro _ ⟨i, rfl⟩
      exact hβ i
    have hind : DistIndependent G r (Set.range m) := by
      rw [distIndependent_iff_not_withinDist]
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
      exact hfar i j fun h => hne (by rw [h])
    have hcard : (Set.range m).ncard = t := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj]
      simp
    exact hcard ▸ ncard_le_maxChoice_size G hsub hind
  · intro ht
    obtain ⟨S, hSX, hSind, hScard⟩ :=
      exists_scattered_ncard_eq G r {a | Sat G col (fun _ => a) β}
    obtain ⟨T, hTS, hTcard⟩ := Set.exists_subset_card_eq (hScard ▸ ht)
    obtain ⟨m, hminj, hmT⟩ := exists_injective_of_ncard_eq T hTcard
    refine ⟨m, fun i j hij => ?_, fun i => hSX (hTS (hmT i))⟩
    exact distIndependent_iff_not_withinDist.mp hSind (m i) (hTS (hmT i)) (m j)
      (hTS (hmT j)) fun h => hij (hminj h)

/-! ### The side conditions of the normal form

A scatter sentence of distance rank `(k, q)` carries a witness `i` with
`1 ≤ i ≤ q` at which its formula `β` is local of rank `(k + i, q − i)`
and its radius lies in the window
`4ρ⁻(k + i, q − i) ≤ r ≤ 9 ^ (k + i) · ρ⁻(k + i, q − i)`. The three
lemmas below climb that witness back to the rank `(k, q)` at which the
normal form states its conditions. All radius arithmetic goes through
`Lax3Proofs.Horizon`.
-/

/-- Climbing the antidiagonal: trading `j` free variables for `j`
quantifiers never shrinks the ρ⁻-horizon. -/
theorem rhoMinus_antidiagonal_le (k q : ℕ) :
    ∀ j : ℕ, j ≤ q → rhoMinus (k + j) (q - j) ≤ rhoMinus k q := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hk : k + (j + 1) = k + j + 1 := by omega
    have hq : q - (j + 1) + 1 = q - j := by omega
    have hstep : rhoMinus (k + (j + 1)) (q - (j + 1)) ≤ rhoMinus (k + j) (q - j) := by
      rw [hk, ← hq]
      exact rhoMinus_succ_left_le (k + j) (q - (j + 1))
    exact hstep.trans (ih (by omega))

/-- The high end of a scatter sentence's radius window, climbed back: at
a witness `1 ≤ i ≤ q` the value ρ⁺(k + i, q − i) is still below
ρ⁻(k, q). -/
theorem rhoPlus_antidiagonal_le {k q i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ q) :
    rhoPlus (k + i) (q - i) ≤ rhoMinus k q := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hk : k + (i' + 1) = k + i' + 1 := by omega
  have hq : q - (i' + 1) + 1 = q - i' := by omega
  have hstep : rhoPlus (k + (i' + 1)) (q - (i' + 1)) ≤ rhoMinus (k + i') (q - i') := by
    rw [hk, ← hq]
    exact rhoPlus_le_rhoMinus (k + i') (q - (i' + 1))
  exact hstep.trans (rhoMinus_antidiagonal_le k q i' (by omega))

/-- Iterating the source's Observation 4: `j` trades of a free variable
for a quantifier. -/
theorem drank_antidiagonal_iter {kk : ℕ} {φ : DistFO L kk} (k' : ℕ) :
    ∀ (j q : ℕ), DRank (k' + j) q φ → DRank k' (q + j) φ := by
  intro j
  induction j with
  | zero => intro q h; simpa using h
  | succ j ih =>
    intro q h
    rw [show k' + (j + 1) = k' + j + 1 from by omega] at h
    have h'' := ih (q + 1) (DRank.antidiagonal h)
    rwa [show q + 1 + j = q + (j + 1) from by omega] at h''

/-- The number of witnesses a scatter sentence of distance rank `(k, q)`
demands. -/
theorem t_le_of_drank {σ : ScatterSentence L} {k q : ℕ} (h : σ.DRank k q) : σ.t ≤ k + q :=
  (scatterSentence_drank_iff.mp h).1

/-- The formula of a scatter sentence of distance rank `(k, q)` is
local. -/
theorem isLocal_beta_of_drank {σ : ScatterSentence L} {k q : ℕ} (h : σ.DRank k q) :
    IsLocal σ.β := by
  rw [scatterSentence_drank_iff] at h
  obtain ⟨-, -, -, -, hloc, -, -, -⟩ := h
  exact hloc

/-- The formula of a scatter sentence of distance rank `(k, q)` with
`q ≥ 1` has distance rank `(k + 1, q − 1)`: the rank witness `i` is
climbed back by `i − 1` trades. -/
theorem drank_succ_pred_of_drank {σ : ScatterSentence L} {k q : ℕ}
    (h : σ.DRank k q) (hq : 1 ≤ q) : DRank (k + 1) (q - 1) σ.β := by
  rw [scatterSentence_drank_iff] at h
  obtain ⟨-, i, h1, h2, -, hrank, -, -⟩ := h
  rw [show k + i = k + 1 + (i - 1) from by omega] at hrank
  have h'' := drank_antidiagonal_iter (k + 1) (i - 1) (q - i) hrank
  rwa [show q - i + (i - 1) = q - 1 from by omega] at h''

/-- The radius of a scatter sentence of distance rank `(k, q)` stays below
ρ⁻(k, q): the high end of the source's radius window is ρ⁺ at the witness
rank, which climbs back below ρ⁻(k, q). -/
theorem r_le_rhoMinus_of_drank {σ : ScatterSentence L} {k q : ℕ} (h : σ.DRank k q) :
    σ.r ≤ rhoMinus k q := by
  rw [scatterSentence_drank_iff] at h
  obtain ⟨-, i, h1, h2, -, -, -, hhigh⟩ := h
  refine hhigh.trans ?_
  rw [← rhoPlus_eq]
  exact rhoPlus_antidiagonal_le h1 h2

/-- The formula of a scatter sentence of distance rank `(k, q)` is
semantically `r / 4`-local. The low end of the radius window gives
`4ρ⁻(k + i, q − i) ≤ r`, hence `ρ⁻(k + i, q − i) ≤ ⌊r/4⌋`, and `β` is
semantically ρ⁻(k + i, q − i)-local by `Lax3Proofs.SemLocal`; a larger
radius only enlarges the substructure the truth value is read in. -/
theorem semanticallyLocal_div_four_of_drank {σ : ScatterSentence L} {k q : ℕ}
    (h : σ.DRank k q) : SemanticallyLocal (σ.r / 4) σ.β := by
  rw [scatterSentence_drank_iff] at h
  obtain ⟨-, i, -, -, hloc, hrank, hlow, -⟩ := h
  have hle : rhoMinus (k + i) (q - i) ≤ σ.r / 4 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  rw [semanticallyLocal_iff]
  intro N G col m
  exact sat_iff_satWithin_of_ball_subset' G col hloc hrank m
    fun j => (ball_mono_radius G (m j) hle).trans
      (Set.subset_iUnion (fun i => ball G (σ.r / 4) (m i)) j)

end Lax3Proofs.ScatterFml
