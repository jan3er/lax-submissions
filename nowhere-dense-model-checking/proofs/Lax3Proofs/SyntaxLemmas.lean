import Lax3.ScatterSentences
import Lax3Proofs.Horizon

/-!
Syntax-level lemmas about the distance logic of `Lax3.DistFO`: the
agreement of satisfaction with its relativization to the full vertex
set, the behaviour of `rename` under satisfaction, the monotonicity of
distance rank in each of its two arguments and along the antidiagonal —
the source's Observations 4 and 6 — and the free-variable bookkeeping
predicate `UsesOnly` together with its congruence lemma.

The rank lemmas are the ones the notes of `Lax3.DistFO` promise.
Everything here lives under `Lax3Proofs.SyntaxLemmas`, as the archive
requires of a proofs package, so the rank lemmas are named
`DRank.mono_left` and so on and are used qualified — dot notation on a
rank derivation is not available. For the same reason no tactic in this
file is handed a concept-side definition: `Sat`, `SatWithin`, `rename`,
`IsLocal` and the rest are taken apart through the `rfl`-lemmas of the
unfolding section below, which record nothing outside this namespace.
Nothing here unfolds `9 ^ _`; every radius side condition is discharged
by a lemma of `Lax3Proofs.Horizon`.

# The guard of a local quantifier reads the whole context

Two statements one expects here are false, for a single reason, and are
carried in a weakened form. Satisfaction of a local quantifier is

    Sat G col m (.exL r φ) = ∃ v, (∃ i, WithinDist G r (m i) v) ∧ …

and the `∃ i` there ranges over the *whole* context `Fin k`, not over
the variables that occur in the body: the guard is the disjunction over
every variable in scope, which is what the notes of `Lax3.DistFO` fix it
to be. Two consequences.

* Satisfaction is not invariant under renaming: `Sat G col m (rename f
  φ) ↔ Sat G col (m ∘ f) φ` fails already for the empty renaming
  `Fin 0 → Fin 1` and a local quantification of a tautology, since the
  renamed formula's guard has a variable to be near and the original's
  has none. See `not_forall_sat_rename`.
* Satisfaction does not depend only on the variables a formula uses:
  `UsesOnly s φ` and agreement of two environments on `s` do not imply
  agreement of satisfaction, because the guards still read the
  coordinates outside `s`. See `not_forall_sat_congr_of_usesOnly`.

Both lemmas are therefore stated with an extra hypothesis making the
guards of the two sides agree. What the inductions consume is only that
the two environments are reached by the same vertices at every radius,
and the congruence `sat_congr_of_usesOnly` is stated with exactly that;
the sufficient condition a caller usually has at hand is that the two
environments have the same image, which is how `sat_rename` and
`satWithin_rename` are stated (`Set.range (m ∘ f) = Set.range m`) and
what the corollaries `sat_congr_of_usesOnly_of_range_eq` and
`sat_rename_of_surjective` package.

This is not a defect of the concept surface but the shape of the
source's own reading: when the source moves a formula between contexts
it reads a guarded quantifier as an unrestricted quantifier conjoined
with binary distance atoms, as the notes of `Lax3.DistFO` record. An
assembly step that places a one-variable formula at a bound variable
must therefore write out the guard it means, rather than expect `rename`
to preserve meaning. Rank and locality, which are pure syntax, are
preserved: see `DRank.rename` and `isLocal_rename`.
-/

namespace Lax3Proofs.SyntaxLemmas

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3Proofs.Horizon

variable {L n : ℕ}

/-! ### Unfolding the concept-side definitions

One `rfl`-lemma per clause of each concept-side definition this file
takes apart. Handing a definition of `Lax3.DistFO` itself to `simp`,
`rw` or `unfold` would make the tactic manufacture the auxiliary
declarations of that definition — its match splitters — and record them,
from this module, under the concept's namespace, which a proofs package
may not do. `Iff.rfl` and `rfl` elaborate by definitional unfolding and
record nothing. The clause lemmas for `Sat`, `SatWithin`, `rename` and
`IsLocal` are `local simp` lemmas, so the inductions below are plain
`simp` calls.
-/

section Unfolding

variable {D : Set (Fin n)} {G : SimpleGraph (Fin n)} {col : Coloring n L} {k : ℕ}
  {m : Fin k → Fin n}

/-- Being within a distance is having a short enough walk. -/
theorem withinDist_iff {V : Type*} {G : SimpleGraph V} {d : ℕ} {u v : V} :
    WithinDist G d u v ↔ ∃ w : G.Walk u v, w.length ≤ d := Iff.rfl

/-- Being within a distance inside a set is having a short enough walk
that stays in the set. -/
theorem withinDistIn_iff {V : Type*} {D : Set V} {G : SimpleGraph V} {d : ℕ} {u v : V} :
    WithinDistIn D G d u v ↔ ∃ w : G.Walk u v, w.length ≤ d ∧ ∀ x ∈ w.support, x ∈ D := Iff.rfl

/-- Satisfaction of an adjacency atom. -/
theorem sat_adj (i j : Fin k) :
    Sat G col m (.adj i j) ↔ G.Adj (m i) (m j) := Iff.rfl

/-- Satisfaction of an equality atom. -/
theorem sat_eq (i j : Fin k) :
    Sat G col m (.eq i j) ↔ m i = m j := Iff.rfl

/-- Satisfaction of a color atom. -/
theorem sat_color (c : Fin L) (i : Fin k) :
    Sat G col m (.color c i) ↔ m i ∈ col c := Iff.rfl

/-- Satisfaction of a binary distance atom. -/
theorem sat_distLe (r : ℕ) (i j : Fin k) :
    Sat G col m (.distLe r i j) ↔ WithinDist G r (m i) (m j) := Iff.rfl

/-- Satisfaction of a unary distance atom. -/
theorem sat_distColorLt (r : ℕ) (c : Fin L) (i : Fin k) :
    Sat G col m (.distColorLt r c i) ↔ ∃ y ∈ col c, ∃ w : G.Walk (m i) y, w.length < r := Iff.rfl

/-- Satisfaction of a negation. -/
theorem sat_not (φ : DistFO L k) :
    Sat G col m (.not φ) ↔ ¬ Sat G col m φ := Iff.rfl

/-- Satisfaction of a conjunction. -/
theorem sat_and (φ ψ : DistFO L k) :
    Sat G col m (.and φ ψ) ↔ Sat G col m φ ∧ Sat G col m ψ := Iff.rfl

/-- Satisfaction of an unrestricted quantification. -/
theorem sat_exU (φ : DistFO L (k + 1)) :
    Sat G col m (.exU φ) ↔ ∃ v : Fin n, Sat G col (Fin.snoc m v) φ := Iff.rfl

/-- Satisfaction of a local quantification: the guard ranges over every
variable of the context. -/
theorem sat_exL (r : ℕ) (φ : DistFO L (k + 1)) :
    Sat G col m (.exL r φ) ↔
      ∃ v : Fin n, (∃ i, WithinDist G r (m i) v) ∧ Sat G col (Fin.snoc m v) φ := Iff.rfl

/-- Relativized satisfaction of an adjacency atom. -/
theorem satWithin_adj (i j : Fin k) :
    SatWithin D G col m (.adj i j) ↔ G.Adj (m i) (m j) ∧ m i ∈ D ∧ m j ∈ D := Iff.rfl

/-- Relativized satisfaction of an equality atom. -/
theorem satWithin_eq (i j : Fin k) :
    SatWithin D G col m (.eq i j) ↔ m i = m j := Iff.rfl

/-- Relativized satisfaction of a color atom. -/
theorem satWithin_color (c : Fin L) (i : Fin k) :
    SatWithin D G col m (.color c i) ↔ m i ∈ col c ∧ m i ∈ D := Iff.rfl

/-- Relativized satisfaction of a binary distance atom. -/
theorem satWithin_distLe (r : ℕ) (i j : Fin k) :
    SatWithin D G col m (.distLe r i j) ↔ WithinDistIn D G r (m i) (m j) := Iff.rfl

/-- Relativized satisfaction of a unary distance atom. -/
theorem satWithin_distColorLt (r : ℕ) (c : Fin L) (i : Fin k) :
    SatWithin D G col m (.distColorLt r c i) ↔
      ∃ y, y ∈ col c ∧ y ∈ D ∧ ∃ w : G.Walk (m i) y, w.length < r ∧ ∀ x ∈ w.support, x ∈ D :=
  Iff.rfl

/-- Relativized satisfaction of a negation. -/
theorem satWithin_not (φ : DistFO L k) :
    SatWithin D G col m (.not φ) ↔ ¬ SatWithin D G col m φ := Iff.rfl

/-- Relativized satisfaction of a conjunction. -/
theorem satWithin_and (φ ψ : DistFO L k) :
    SatWithin D G col m (.and φ ψ) ↔ SatWithin D G col m φ ∧ SatWithin D G col m ψ := Iff.rfl

/-- Relativized satisfaction of an unrestricted quantification. -/
theorem satWithin_exU (φ : DistFO L (k + 1)) :
    SatWithin D G col m (.exU φ) ↔ ∃ v ∈ D, SatWithin D G col (Fin.snoc m v) φ := Iff.rfl

/-- Relativized satisfaction of a local quantification. -/
theorem satWithin_exL (r : ℕ) (φ : DistFO L (k + 1)) :
    SatWithin D G col m (.exL r φ) ↔
      ∃ v ∈ D, (∃ i, WithinDistIn D G r (m i) v) ∧ SatWithin D G col (Fin.snoc m v) φ := Iff.rfl

variable {k' : ℕ} (f : Fin k → Fin k')

/-- Renaming an adjacency atom. -/
theorem rename_adj (i j : Fin k) :
    rename f (.adj i j) = (.adj (f i) (f j) : DistFO L k') := rfl

/-- Renaming an equality atom. -/
theorem rename_eq (i j : Fin k) :
    rename f (.eq i j) = (.eq (f i) (f j) : DistFO L k') := rfl

/-- Renaming a color atom. -/
theorem rename_color (c : Fin L) (i : Fin k) :
    rename f (.color c i) = (.color c (f i) : DistFO L k') := rfl

/-- Renaming a binary distance atom. -/
theorem rename_distLe (r : ℕ) (i j : Fin k) :
    rename f (.distLe r i j) = (.distLe r (f i) (f j) : DistFO L k') := rfl

/-- Renaming a unary distance atom. -/
theorem rename_distColorLt (r : ℕ) (c : Fin L) (i : Fin k) :
    rename f (.distColorLt r c i) = (.distColorLt r c (f i) : DistFO L k') := rfl

/-- Renaming a negation. -/
theorem rename_not (φ : DistFO L k) :
    rename f (.not φ) = .not (rename f φ) := rfl

/-- Renaming a conjunction. -/
theorem rename_and (φ ψ : DistFO L k) :
    rename f (.and φ ψ) = .and (rename f φ) (rename f ψ) := rfl

/-- Renaming an unrestricted quantification lifts the renaming to the
bound variable. -/
theorem rename_exU (φ : DistFO L (k + 1)) :
    rename f (.exU φ) =
      .exU (rename (Fin.snoc (fun i => (f i).castSucc) (Fin.last k')) φ) := rfl

/-- Renaming a local quantification lifts the renaming to the bound
variable and keeps the radius. -/
theorem rename_exL (r : ℕ) (φ : DistFO L (k + 1)) :
    rename f (.exL r φ) =
      .exL r (rename (Fin.snoc (fun i => (f i).castSucc) (Fin.last k')) φ) := rfl

/-- An adjacency atom is local. -/
theorem isLocal_adj (i j : Fin k) : IsLocal (.adj i j : DistFO L k) := trivial

/-- An equality atom is local. -/
theorem isLocal_eq (i j : Fin k) : IsLocal (.eq i j : DistFO L k) := trivial

/-- A color atom is local. -/
theorem isLocal_color (c : Fin L) (i : Fin k) :
    IsLocal (.color c i : DistFO L k) := trivial

/-- A binary distance atom is local. -/
theorem isLocal_distLe (r : ℕ) (i j : Fin k) :
    IsLocal (.distLe r i j : DistFO L k) := trivial

/-- A unary distance atom is local. -/
theorem isLocal_distColorLt (r : ℕ) (c : Fin L) (i : Fin k) :
    IsLocal (.distColorLt r c i : DistFO L k) := trivial

/-- Locality of a negation. -/
theorem isLocal_not (φ : DistFO L k) :
    IsLocal (.not φ) ↔ IsLocal φ := Iff.rfl

/-- Locality of a conjunction. -/
theorem isLocal_and (φ ψ : DistFO L k) :
    IsLocal (.and φ ψ) ↔ IsLocal φ ∧ IsLocal ψ := Iff.rfl

/-- An unrestricted quantification is never local. -/
theorem isLocal_exU (φ : DistFO L (k + 1)) :
    IsLocal (.exU φ) ↔ False := Iff.rfl

/-- Locality of a local quantification. -/
theorem isLocal_exL (r : ℕ) (φ : DistFO L (k + 1)) :
    IsLocal (.exL r φ) ↔ IsLocal φ := Iff.rfl

/-- The distance rank of a scatter sentence, spelled out. -/
theorem scatterSentence_drank_iff {σ : ScatterSentence L} {k q : ℕ} :
    σ.DRank k q ↔ σ.t ≤ k + q ∧ ∃ i, 1 ≤ i ∧ i ≤ q ∧ IsLocal σ.β ∧
      DRank (k + i) (q - i) σ.β ∧
      4 * rhoMinus (k + i) (q - i) ≤ σ.r ∧ σ.r ≤ 9 ^ (k + i) * rhoMinus (k + i) (q - i) :=
  Iff.rfl

end Unfolding

attribute [local simp]
  sat_adj sat_eq sat_color sat_distLe sat_distColorLt sat_not sat_and sat_exU sat_exL
  satWithin_adj satWithin_eq satWithin_color satWithin_distLe satWithin_distColorLt
  satWithin_not satWithin_and satWithin_exU satWithin_exL
  rename_adj rename_eq rename_color rename_distLe rename_distColorLt
  rename_not rename_and rename_exU rename_exL
  isLocal_adj isLocal_eq isLocal_color isLocal_distLe isLocal_distColorLt
  isLocal_not isLocal_and isLocal_exU isLocal_exL

/-! ### Environments -/

/-- Two tuples with the same image satisfy the same existential
statements about their entries. This is the shape in which the image of
an environment enters: the guard of a local quantifier is an existential
statement over the entries of the environment. -/
theorem exists_congr_of_range_eq {α : Type*} {k k' : ℕ} {m : Fin k → α} {m' : Fin k' → α}
    (h : Set.range m = Set.range m') (P : α → Prop) :
    (∃ i, P (m i)) ↔ (∃ i, P (m' i)) := by
  constructor
  · rintro ⟨i, hi⟩
    have hmem : m i ∈ Set.range m' := by rw [← h]; exact Set.mem_range_self i
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, by rw [hj]; exact hi⟩
  · rintro ⟨i, hi⟩
    have hmem : m' i ∈ Set.range m := by rw [h]; exact Set.mem_range_self i
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, by rw [hj]; exact hi⟩

/-- An existential statement about the entries of an extended tuple
splits into the old entries and the new one. -/
theorem exists_snoc_iff {α : Type*} {k : ℕ} (m : Fin k → α) (u : α) (P : α → Prop) :
    (∃ i, P ((Fin.snoc m u : Fin (k + 1) → α) i)) ↔ (∃ i, P (m i)) ∨ P u := by
  rw [Fin.exists_fin_succ']
  simp

/-- The environment identity behind every binder case of a renaming
lemma: extending an environment and then reindexing along the lifted
renaming is reindexing and then extending. -/
theorem snoc_comp_renameLift {k k' : ℕ} (f : Fin k → Fin k') (m : Fin k' → Fin n) (v : Fin n) :
    (Fin.snoc m v : Fin (k' + 1) → Fin n) ∘
        (Fin.snoc (fun i => (f i).castSucc) (Fin.last k') : Fin (k + 1) → Fin (k' + 1)) =
      (Fin.snoc (m ∘ f) v : Fin (k + 1) → Fin n) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

/-- The image of an extended environment. -/
theorem range_snoc_eq_of_range_eq {k k' : ℕ} {f : Fin k → Fin k'} {m : Fin k' → Fin n}
    (hf : Set.range (m ∘ f) = Set.range m) (v : Fin n) :
    Set.range ((Fin.snoc m v : Fin (k' + 1) → Fin n) ∘
        (Fin.snoc (fun i => (f i).castSucc) (Fin.last k') : Fin (k + 1) → Fin (k' + 1))) =
      Set.range (Fin.snoc m v : Fin (k' + 1) → Fin n) := by
  rw [snoc_comp_renameLift, Fin.range_snoc, Fin.range_snoc, hf]

/-! ### Satisfaction and the trivial relativization -/

/-- Staying inside the full vertex set is no condition on a walk. -/
theorem withinDistIn_univ {V : Type*} {G : SimpleGraph V} {d : ℕ} {u v : V} :
    WithinDistIn Set.univ G d u v ↔ WithinDist G d u v := by
  simp [withinDistIn_iff, withinDist_iff]

/-- Satisfaction agrees with its relativization to the full vertex set.
The notes of `Lax3.DistFO` defer this agreement to the place where the
two definitions are compared; this is that place. -/
theorem sat_iff_satWithin_univ (G : SimpleGraph (Fin n)) (col : Coloring n L)
    {k : ℕ} (m : Fin k → Fin n) (φ : DistFO L k) :
    Sat G col m φ ↔ SatWithin Set.univ G col m φ := by
  induction φ with
  | adj i j => simp
  | eq i j => simp
  | color c i => simp
  | distLe r i j => simp [withinDistIn_univ]
  | distColorLt r c i => simp
  | not φ ih => simp [ih]
  | and φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | exU φ ih => simp [ih]
  | exL r φ ih => simp [ih, withinDistIn_univ]

/-! ### Renaming -/

/-- Renaming preserves locality: it moves variables and touches no
quantifier. -/
theorem isLocal_rename {k : ℕ} (φ : DistFO L k) {k' : ℕ} (f : Fin k → Fin k') :
    IsLocal (rename f φ) ↔ IsLocal φ := by
  induction φ generalizing k' with
  | adj i j => simp
  | eq i j => simp
  | color c i => simp
  | distLe r i j => simp
  | distColorLt r c i => simp
  | not φ ih => simp [ih]
  | and φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | exU φ ih => simp
  | exL r φ ih => simp [ih]

/-- Renaming preserves distance rank: it moves variables and touches no
radius. -/
theorem DRank.rename {k k'' q : ℕ} {φ : DistFO L k}
    (h : DRank k'' q φ) {k' : ℕ} (f : Fin k → Fin k') : DRank k'' q (rename f φ) := by
  induction h generalizing k' with
  | adj i j => simp only [rename_adj]; exact .adj _ _
  | eq i j => simp only [rename_eq]; exact .eq _ _
  | color c i => simp only [rename_color]; exact .color _ _
  | distLe i j hr => simp only [rename_distLe]; exact .distLe _ _ hr
  | distColorLt c i hr => simp only [rename_distColorLt]; exact .distColorLt _ _ hr
  | not _ ih => simp only [rename_not]; exact .not (ih f)
  | and _ _ ih ih' => simp only [rename_and]; exact .and (ih f) (ih' f)
  | exU _ ih => simp only [rename_exU]; exact .exU (ih _)
  | exL _ hr ih => simp only [rename_exL]; exact .exL (ih _) hr

/-- Renaming is sound for satisfaction as soon as it does not change the
image of the environment. The hypothesis is what the guard of a local
quantifier needs: that guard ranges over every variable in scope, so a
renaming into a context whose environment reaches further changes the
meaning of the formula — see `not_forall_sat_rename`. -/
theorem sat_rename {G : SimpleGraph (Fin n)} {col : Coloring n L} {k : ℕ} (φ : DistFO L k)
    {k' : ℕ} (f : Fin k → Fin k') (m : Fin k' → Fin n)
    (hf : Set.range (m ∘ f) = Set.range m) :
    Sat G col m (rename f φ) ↔ Sat G col (m ∘ f) φ := by
  induction φ generalizing k' with
  | adj i j => simp
  | eq i j => simp
  | color c i => simp
  | distLe r i j => simp
  | distColorLt r c i => simp
  | not φ ih => simp [ih f m hf]
  | and φ ψ ihφ ihψ => simp [ihφ f m hf, ihψ f m hf]
  | exU φ ih =>
    simp only [rename_exU, sat_exU]
    refine exists_congr fun v => ?_
    rw [ih _ (Fin.snoc m v) (range_snoc_eq_of_range_eq hf v), snoc_comp_renameLift]
  | exL r φ ih =>
    simp only [rename_exL, sat_exL]
    refine exists_congr fun v => and_congr
      (exists_congr_of_range_eq hf.symm fun u => WithinDist G r u v) ?_
    rw [ih _ (Fin.snoc m v) (range_snoc_eq_of_range_eq hf v), snoc_comp_renameLift]

/-- Renaming along a surjection is sound for satisfaction: a surjection
cannot enlarge the image of the environment. -/
theorem sat_rename_of_surjective {G : SimpleGraph (Fin n)} {col : Coloring n L} {k : ℕ}
    (φ : DistFO L k) {k' : ℕ} {f : Fin k → Fin k'} (hf : Function.Surjective f)
    (m : Fin k' → Fin n) :
    Sat G col m (rename f φ) ↔ Sat G col (m ∘ f) φ := by
  refine sat_rename φ f m (Set.Subset.antisymm (Set.range_comp_subset_range f m) ?_)
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, rfl⟩ := hf i
  exact ⟨j, rfl⟩

/-- The relativized form of `sat_rename`, under the same hypothesis on
the image of the environment. The far-quantification assembly needs both
forms. -/
theorem satWithin_rename {D : Set (Fin n)} {G : SimpleGraph (Fin n)} {col : Coloring n L} {k : ℕ}
    (φ : DistFO L k) {k' : ℕ} (f : Fin k → Fin k') (m : Fin k' → Fin n)
    (hf : Set.range (m ∘ f) = Set.range m) :
    SatWithin D G col m (rename f φ) ↔ SatWithin D G col (m ∘ f) φ := by
  induction φ generalizing k' with
  | adj i j => simp
  | eq i j => simp
  | color c i => simp
  | distLe r i j => simp
  | distColorLt r c i => simp
  | not φ ih => simp [ih f m hf]
  | and φ ψ ihφ ihψ => simp [ihφ f m hf, ihψ f m hf]
  | exU φ ih =>
    simp only [rename_exU, satWithin_exU]
    refine exists_congr fun v => and_congr_right fun _ => ?_
    rw [ih _ (Fin.snoc m v) (range_snoc_eq_of_range_eq hf v), snoc_comp_renameLift]
  | exL r φ ih =>
    simp only [rename_exL, satWithin_exL]
    refine exists_congr fun v => and_congr_right fun _ => and_congr
      (exists_congr_of_range_eq hf.symm fun u => WithinDistIn D G r u v) ?_
    rw [ih _ (Fin.snoc m v) (range_snoc_eq_of_range_eq hf v), snoc_comp_renameLift]

/-! ### Monotonicity of distance rank

The source's Observation 4 — *every distFO formula of distance rank
(k+1, q−1) with at most k free variables also has distance rank (k, q)*
— is `DRank.antidiagonal` below; `DRank.mono_left` and
`DRank.mono_right` are the two coordinate directions it is assembled
from. All three are monotonicity lemmas of the rank *predicate*, which
is how the notes of `Lax3.DistFO` say the observation is to be read.
-/

/-- Distance rank is monotone in the free-variable bound: allowing more
free variables only widens the horizon a distance atom may reach. -/
theorem DRank.mono_left {k : ℕ} {φ : DistFO L k} {k' k'' q : ℕ}
    (h : DRank k' q φ) (hk : k' ≤ k'') : DRank k'' q φ := by
  induction h generalizing k'' with
  | adj i j => exact .adj i j
  | eq i j => exact .eq i j
  | color c i => exact .color c i
  | distLe i j hr => exact .distLe i j (hr.trans (rhoMinus_mono hk le_rfl))
  | distColorLt c i hr => exact .distColorLt c i (hr.trans (rhoMinus_mono hk le_rfl))
  | not _ ih => exact .not (ih hk)
  | and _ _ ih ih' => exact .and (ih hk) (ih' hk)
  | exU _ ih => exact .exU (ih (by omega))
  | exL _ hr ih => exact .exL (ih (by omega)) (hr.trans (rhoPlus_mono (by omega) le_rfl))

/-- Distance rank is monotone in the quantifier-rank bound: allowing
more quantifiers only widens the horizon a distance atom may reach. -/
theorem DRank.mono_right {k : ℕ} {φ : DistFO L k} {k' q q' : ℕ}
    (h : DRank k' q φ) (hq : q ≤ q') : DRank k' q' φ := by
  induction h generalizing q' with
  | adj i j => exact .adj i j
  | eq i j => exact .eq i j
  | color c i => exact .color c i
  | distLe i j hr => exact .distLe i j (hr.trans (rhoMinus_mono le_rfl hq))
  | distColorLt c i hr => exact .distColorLt c i (hr.trans (rhoMinus_mono le_rfl hq))
  | not _ ih => exact .not (ih hq)
  | and _ _ ih ih' => exact .and (ih hq) (ih' hq)
  | exU _ ih =>
    obtain _ | q'' := q'
    · omega
    · exact .exU (ih (by omega))
  | exL _ hr ih =>
    obtain _ | q'' := q'
    · omega
    · exact .exL (ih (by omega)) (hr.trans (rhoPlus_mono le_rfl (by omega)))

/-- The source's Observation 4: *every distFO formula of distance rank
(k+1, q−1) with at most k free variables also has distance rank (k, q)*.
Trading a free variable for a quantifier never shrinks a horizon, so
every radius bound of the derivation survives the trade. -/
theorem DRank.antidiagonal {k : ℕ} {φ : DistFO L k} {k' q : ℕ}
    (h : DRank (k' + 1) q φ) : DRank k' (q + 1) φ := by
  generalize ha : k' + 1 = a at h
  induction h generalizing k' with
  | adj i j => exact .adj i j
  | eq i j => exact .eq i j
  | color c i => exact .color c i
  | distLe i j hr => subst ha; exact .distLe i j (hr.trans (rhoMinus_succ_left_le k' _))
  | distColorLt c i hr => subst ha; exact .distColorLt c i (hr.trans (rhoMinus_succ_left_le k' _))
  | not _ ih => subst ha; exact .not (ih rfl)
  | and _ _ ih ih' => subst ha; exact .and (ih rfl) (ih' rfl)
  | exU _ ih => subst ha; exact .exU (ih rfl)
  | exL _ hr ih =>
    subst ha
    exact .exL (ih rfl) (hr.trans (rhoPlus_succ_left_le (k' + 1) _))

/-! ### Scatter rank and the variables a formula uses -/

/-- The source's Observation 6: *every scatter sentence of distance rank
(k+1, q−1) is also a scatter sentence of distance rank (k, q)*. The rank
witness of the shifted sentence is the old one moved by one: the radius
window and the rank of `β` are the same two numbers, since
`(k+1) + i = k + (i+1)` and `q − i = (q+1) − (i+1)`. -/
theorem ScatterSentence.DRank.antidiagonal
    {σ : ScatterSentence L} {k q : ℕ} (h : σ.DRank (k + 1) q) : σ.DRank k (q + 1) := by
  rw [scatterSentence_drank_iff] at h ⊢
  obtain ⟨ht, i, hi1, hiq, hloc, hrank, hlow, hhigh⟩ := h
  refine ⟨by omega, i + 1, by omega, by omega, ?_⟩
  have hk : k + (i + 1) = k + 1 + i := by omega
  have hq : q + 1 - (i + 1) = q - i := by omega
  rw [hk, hq]
  exact ⟨hloc, hrank, hlow, hhigh⟩

/-- `UsesOnly s φ` says that every variable occurring in `φ` lies in
`s`. Under a binder the set is shifted and the newly bound last variable
is added to it. This is the syntactic side of variable bookkeeping only:
by `not_forall_sat_congr_of_usesOnly` it does *not* by itself confine
satisfaction to the coordinates in `s`, because the guard of a local
quantifier reads the whole environment. -/
def UsesOnly : {k : ℕ} → Set (Fin k) → DistFO L k → Prop
  | _, s, .adj i j => i ∈ s ∧ j ∈ s
  | _, s, .eq i j => i ∈ s ∧ j ∈ s
  | _, s, .color _ i => i ∈ s
  | _, s, .distLe _ i j => i ∈ s ∧ j ∈ s
  | _, s, .distColorLt _ _ i => i ∈ s
  | _, s, .not φ => UsesOnly s φ
  | _, s, .and φ ψ => UsesOnly s φ ∧ UsesOnly s ψ
  | k, s, .exU φ => UsesOnly (Fin.castSucc '' s ∪ {Fin.last k}) φ
  | k, s, .exL _ φ => UsesOnly (Fin.castSucc '' s ∪ {Fin.last k}) φ

/-- A shifted variable belongs to a shifted set only if it did before:
the newly bound variable is not a shifted one. -/
theorem mem_of_castSucc_mem_snocSet {k : ℕ} {s : Set (Fin k)} {j : Fin k}
    (h : j.castSucc ∈ Fin.castSucc '' s ∪ ({Fin.last k} : Set (Fin (k + 1)))) : j ∈ s := by
  rcases h with ⟨a, ha, hja⟩ | h
  · rwa [Fin.castSucc_injective _ hja] at ha
  · exact absurd (Set.mem_singleton_iff.mp h) (Fin.castSucc_ne_last j)

/-- Two environments agreeing on `s` agree, after a common extension, on
the set a binder extends `s` to. -/
theorem snoc_agree_of_agree {k : ℕ} {s : Set (Fin k)} {m m' : Fin k → Fin n}
    (hm : ∀ i ∈ s, m i = m' i) (v : Fin n) :
    ∀ i ∈ Fin.castSucc '' s ∪ ({Fin.last k} : Set (Fin (k + 1))),
      (Fin.snoc m v : Fin (k + 1) → Fin n) i = (Fin.snoc m' v : Fin (k + 1) → Fin n) i := by
  intro i
  induction i using Fin.lastCases with
  | last => intro _; simp
  | cast j => intro hi; simpa using hm j (mem_of_castSucc_mem_snocSet hi)

/-- The set a binder extends the full variable set to is again the full
variable set. -/
theorem castSucc_image_univ_union_last (k : ℕ) :
    Fin.castSucc '' (Set.univ : Set (Fin k)) ∪ {Fin.last k} = Set.univ := by
  ext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

/-- Every formula uses only the variables it has: the sanity anchor of
`UsesOnly`. -/
theorem usesOnly_univ {k : ℕ} (φ : DistFO L k) : UsesOnly Set.univ φ := by
  induction φ with
  | adj i j => simp [UsesOnly]
  | eq i j => simp [UsesOnly]
  | color c i => simp [UsesOnly]
  | distLe r i j => simp [UsesOnly]
  | distColorLt r c i => simp [UsesOnly]
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | exU φ ih => rw [UsesOnly, castSucc_image_univ_union_last]; exact ih
  | exL r φ ih => rw [UsesOnly, castSucc_image_univ_union_last]; exact ih

/-- `UsesOnly` is monotone in the variable set. -/
theorem UsesOnly.mono {k : ℕ} {s s' : Set (Fin k)} {φ : DistFO L k}
    (h : UsesOnly s φ) (hss : s ⊆ s') : UsesOnly s' φ := by
  induction φ with
  | adj i j => simp only [UsesOnly] at h ⊢; exact ⟨hss h.1, hss h.2⟩
  | eq i j => simp only [UsesOnly] at h ⊢; exact ⟨hss h.1, hss h.2⟩
  | color c i => simp only [UsesOnly] at h ⊢; exact hss h
  | distLe r i j => simp only [UsesOnly] at h ⊢; exact ⟨hss h.1, hss h.2⟩
  | distColorLt r c i => simp only [UsesOnly] at h ⊢; exact hss h
  | not φ ih => simp only [UsesOnly] at h ⊢; exact ih h hss
  | and φ ψ ihφ ihψ => simp only [UsesOnly] at h ⊢; exact ⟨ihφ h.1 hss, ihψ h.2 hss⟩
  | exU φ ih =>
    simp only [UsesOnly] at h ⊢
    exact ih h (Set.union_subset_union (Set.image_mono hss) (subset_refl _))
  | exL r φ ih =>
    simp only [UsesOnly] at h ⊢
    exact ih h (Set.union_subset_union (Set.image_mono hss) (subset_refl _))

/-- Two environments that are reached by the same vertices at every
radius keep that property under a common extension. This is the
hypothesis the congruence lemma below consumes at a local quantifier. -/
theorem guard_congr_snoc {G : SimpleGraph (Fin n)} {k : ℕ} {m m' : Fin k → Fin n}
    (hg : ∀ (r : ℕ) (v : Fin n), (∃ i, WithinDist G r (m i) v) ↔ (∃ i, WithinDist G r (m' i) v))
    (u : Fin n) (r : ℕ) (v : Fin n) :
    (∃ i, WithinDist G r ((Fin.snoc m u : Fin (k + 1) → Fin n) i) v) ↔
      (∃ i, WithinDist G r ((Fin.snoc m' u : Fin (k + 1) → Fin n) i) v) := by
  rw [exists_snoc_iff m u fun x => WithinDist G r x v,
    exists_snoc_iff m' u fun x => WithinDist G r x v, hg r v]

/-- Environments with the same image are reached by the same vertices at
every radius. -/
theorem guard_congr_of_range_eq {G : SimpleGraph (Fin n)} {k : ℕ} {m m' : Fin k → Fin n}
    (hr : Set.range m = Set.range m') (r : ℕ) (v : Fin n) :
    (∃ i, WithinDist G r (m i) v) ↔ (∃ i, WithinDist G r (m' i) v) :=
  exists_congr_of_range_eq hr fun u => WithinDist G r u v

/-- Satisfaction depends on an environment only through the variables
the formula uses — provided the two environments are reached by the same
vertices at every radius, which is what the guard of a local quantifier
reads. Without that hypothesis the statement is false, by
`not_forall_sat_congr_of_usesOnly`. The hypothesis is consumed only at a
local quantifier and only through its guard, which is why it is stated
about the guards themselves rather than about the environments; for the
common case of two environments with the same image, use
`sat_congr_of_usesOnly_of_range_eq`. -/
theorem sat_congr_of_usesOnly {G : SimpleGraph (Fin n)} {col : Coloring n L} {k : ℕ}
    {s : Set (Fin k)} {φ : DistFO L k} (h : UsesOnly s φ) {m m' : Fin k → Fin n}
    (hm : ∀ i ∈ s, m i = m' i)
    (hg : ∀ (r : ℕ) (v : Fin n), (∃ i, WithinDist G r (m i) v) ↔ (∃ i, WithinDist G r (m' i) v)) :
    Sat G col m φ ↔ Sat G col m' φ := by
  induction φ with
  | adj i j =>
    simp only [UsesOnly] at h
    simp only [sat_adj, hm i h.1, hm j h.2]
  | eq i j =>
    simp only [UsesOnly] at h
    simp only [sat_eq, hm i h.1, hm j h.2]
  | color c i =>
    simp only [UsesOnly] at h
    simp only [sat_color, hm i h]
  | distLe r i j =>
    simp only [UsesOnly] at h
    simp only [sat_distLe, hm i h.1, hm j h.2]
  | distColorLt r c i =>
    simp only [UsesOnly] at h
    simp only [sat_distColorLt]
    rw [hm i h]
  | not φ ih =>
    simp only [UsesOnly] at h
    simp only [sat_not, ih h hm hg]
  | and φ ψ ihφ ihψ =>
    simp only [UsesOnly] at h
    simp only [sat_and, ihφ h.1 hm hg, ihψ h.2 hm hg]
  | exU φ ih =>
    simp only [UsesOnly] at h
    simp only [sat_exU]
    exact exists_congr fun v => ih h (snoc_agree_of_agree hm v) (guard_congr_snoc hg v)
  | exL r φ ih =>
    simp only [UsesOnly] at h
    simp only [sat_exL]
    exact exists_congr fun v => and_congr (hg r v)
      (ih h (snoc_agree_of_agree hm v) (guard_congr_snoc hg v))

/-- Satisfaction depends on an environment only through the variables
the formula uses, for two environments with the same image. The
hypothesis on the image is what makes the guards of the local
quantifiers agree; it cannot be dropped, by
`not_forall_sat_congr_of_usesOnly`. -/
theorem sat_congr_of_usesOnly_of_range_eq {G : SimpleGraph (Fin n)} {col : Coloring n L} {k : ℕ}
    {s : Set (Fin k)} {φ : DistFO L k} (h : UsesOnly s φ) {m m' : Fin k → Fin n}
    (hm : ∀ i ∈ s, m i = m' i) (hr : Set.range m = Set.range m') :
    Sat G col m φ ↔ Sat G col m' φ :=
  sat_congr_of_usesOnly h hm (guard_congr_of_range_eq hr)

/-! ### The unconditional forms are false

The two counterexamples the module docstring describes. Both run in an
edgeless graph, where `WithinDist G 0 u v` is `u = v`, and both turn on
the guard of a local quantifier ranging over the whole context.
-/

/-- Being within distance zero is being equal. -/
theorem withinDist_zero {V : Type*} {G : SimpleGraph V} {u v : V} :
    WithinDist G 0 u v ↔ u = v := by
  constructor
  · rintro ⟨w, hw⟩
    cases w with
    | nil => rfl
    | cons h p => simp [SimpleGraph.Walk.length_cons] at hw
  · rintro rfl
    exact ⟨.nil, le_rfl⟩

/-- Satisfaction is *not* invariant under renaming. The empty renaming
`Fin 0 → Fin 1` sends the sentence "there is a vertex near one of my
free variables satisfying `x = x`" — which is false, a sentence having
no free variable to be near — to a one-variable formula whose guard has
the variable of the larger context to be near, and which is therefore
true. -/
theorem not_forall_sat_rename :
    ¬ ∀ (L n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (k k' : ℕ)
        (f : Fin k → Fin k') (m : Fin k' → Fin n) (φ : DistFO L k),
        Sat G col m (rename f φ) ↔ Sat G col (m ∘ f) φ := by
  intro hall
  have key := hall 1 1 ⊥ (fun _ => Set.univ) 0 1 Fin.elim0 (fun _ => 0)
    (.exL 0 (.eq 0 0))
  simp only [rename_exL, rename_eq, sat_exL, sat_eq] at key
  obtain ⟨-, ⟨i, -⟩, -⟩ := key.mp ⟨0, ⟨0, ⟨.nil, le_rfl⟩⟩, by trivial⟩
  exact i.elim0

/-- Satisfaction does *not* depend only on the variables a formula uses.
The formula "there is a vertex near one of my free variables carrying
color 0" uses no free variable at all, yet in the edgeless graph on two
vertices, with color class `{1}`, it holds of the identity environment
and fails of the constant one — two environments that agree on the empty
variable set. -/
theorem not_forall_sat_congr_of_usesOnly :
    ¬ ∀ (L n k : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (s : Set (Fin k))
        (φ : DistFO L k) (m m' : Fin k → Fin n), UsesOnly s φ → (∀ i ∈ s, m i = m' i) →
        (Sat G col m φ ↔ Sat G col m' φ) := by
  intro hall
  have key := hall 1 2 2 ⊥ (fun _ => {1}) ∅ (.exL 0 (.color 0 (Fin.last 2)))
    (fun i => i) (fun _ => 0) (by simp [UsesOnly]) (by simp)
  simp only [sat_exL, sat_color] at key
  obtain ⟨v, ⟨i, hi⟩, hv⟩ :=
    key.mp ⟨1, ⟨1, ⟨.nil, le_rfl⟩⟩, by rw [Set.mem_singleton_iff, Fin.snoc_last]⟩
  rw [withinDist_zero] at hi
  simp only [Set.mem_singleton_iff, Fin.snoc_last] at hv
  exact absurd (hi.trans hv) (by decide)

end Lax3Proofs.SyntaxLemmas
