import Lax2Proofs.Source.TwinWidth.Matrix.GridMinor
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Finset.Fin

/-!
# Marcus-Tardos theorem

This file records the exact finite-matrix statements needed later in the
twin-width grid theorem.  Section 2 of Marcus--Tardos proves the
Füredi--Hajnal forbidden permutation matrix theorem by a block recursion; the
grid-minor density theorem used by twin-width is then a corollary.

The first part of the file formalizes the ordered-submatrix language of Section
2: containment, avoidance, permutation matrices, and the extremal function
`f(n,P)`.
-/

namespace Lax2Proofs.TwinWidth
namespace Matrix

/-! ## Forbidden permutation matrices -/

/-- `A` contains the pattern `P` if some order-preserving choice of rows and
columns of `A` has `true` entries wherever `P` has `true` entries.

This matches Marcus--Tardos containment: extra `true` entries in the selected
submatrix are allowed. -/
def ContainsPattern {n m k l : ℕ}
    (A : _root_.Matrix (Fin n) (Fin m) Bool)
    (P : _root_.Matrix (Fin k) (Fin l) Bool) : Prop :=
  ∃ row : Fin k ↪o Fin n, ∃ col : Fin l ↪o Fin m,
    ∀ i j, P i j = true → A (row i) (col j) = true

/-- A matrix avoids a pattern if it does not contain it as an ordered
submatrix. -/
def AvoidsPattern {n m k l : ℕ}
    (A : _root_.Matrix (Fin n) (Fin m) Bool)
    (P : _root_.Matrix (Fin k) (Fin l) Bool) : Prop :=
  ¬ ContainsPattern A P

/-- A Boolean matrix is a permutation matrix when every row has its unique
`true` entry in the column prescribed by a permutation. -/
def IsPermutationMatrix {k : ℕ} (P : _root_.Matrix (Fin k) (Fin k) Bool) : Prop :=
  ∃ π : Equiv.Perm (Fin k), ∀ i j, P i j = decide (j = π i)

/-- The permutation matrix associated with a permutation of `Fin k`. -/
def permutationMatrix {k : ℕ} (π : Equiv.Perm (Fin k)) :
    _root_.Matrix (Fin k) (Fin k) Bool :=
  fun i j => decide (j = π i)

theorem isPermutationMatrix_permutationMatrix {k : ℕ} (π : Equiv.Perm (Fin k)) :
    IsPermutationMatrix (permutationMatrix π) :=
  ⟨π, by intro i j; rfl⟩

/-- The finite set of square Boolean matrices of order `n` avoiding `P`. -/
noncomputable def avoidingMatrices {k : ℕ}
    (P : _root_.Matrix (Fin k) (Fin k) Bool) (n : ℕ) :
    Finset (_root_.Matrix (Fin n) (Fin n) Bool) :=
  by
    classical
    exact Finset.univ.filter fun A => AvoidsPattern A P

/-- The extremal function `f(n,P)`: the largest number of true entries in an
`n × n` matrix avoiding `P`. -/
noncomputable def forbiddenExtremal {k : ℕ}
    (P : _root_.Matrix (Fin k) (Fin k) Bool) (n : ℕ) : ℕ :=
  by
    classical
    exact Nat.findGreatest
      (fun q => ∃ A : _root_.Matrix (Fin n) (Fin n) Bool,
        AvoidsPattern A P ∧ (oneEntries A).card = q)
      (n * n)

/-- Every matrix has at most `n * m` true entries. -/
theorem oneEntries_card_le {n m : ℕ}
    (A : _root_.Matrix (Fin n) (Fin m) Bool) :
    (oneEntries A).card ≤ n * m := by
  classical
  calc
    (oneEntries A).card ≤ (Finset.univ : Finset (Fin n × Fin m)).card := by
      exact Finset.card_le_card (by
        intro p hp
        simp [oneEntries] at hp ⊢)
    _ = n * m := by simp [Fintype.card_prod]

theorem forbiddenExtremal_le_square {k n : ℕ}
    (P : _root_.Matrix (Fin k) (Fin k) Bool) :
    forbiddenExtremal P n ≤ n * n := by
  classical
  exact Nat.findGreatest_le
    (P := fun q => ∃ A : _root_.Matrix (Fin n) (Fin n) Bool,
      AvoidsPattern A P ∧ (oneEntries A).card = q)
    (n * n)

/-- The all-false Boolean matrix. -/
def zeroBoolMatrix (n m : ℕ) : _root_.Matrix (Fin n) (Fin m) Bool :=
  fun _ _ => false

@[simp] theorem oneEntries_zeroBoolMatrix (n m : ℕ) :
    oneEntries (zeroBoolMatrix n m) = ∅ := by
  classical
  ext p
  simp [oneEntries, zeroBoolMatrix]

/-- A nonempty permutation pattern is avoided by the all-false matrix. -/
theorem zeroBoolMatrix_avoids_permutation {n k : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k)) :
    AvoidsPattern (zeroBoolMatrix n n) (permutationMatrix π) := by
  intro h
  rcases h with ⟨row, col, hcontains⟩
  let i : Fin k := ⟨0, hk⟩
  have htrue := hcontains i (π i) (by simp [permutationMatrix])
  simp [zeroBoolMatrix] at htrue

/-- The extremal value is realized by some avoiding matrix, for nonempty
permutation patterns. -/
theorem exists_forbiddenExtremal_eq {k n : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k)) :
    ∃ A : _root_.Matrix (Fin n) (Fin n) Bool,
      AvoidsPattern A (permutationMatrix π) ∧
        (oneEntries A).card = forbiddenExtremal (permutationMatrix π) n := by
  classical
  let P := fun q => ∃ A : _root_.Matrix (Fin n) (Fin n) Bool,
    AvoidsPattern A (permutationMatrix π) ∧ (oneEntries A).card = q
  have h0 : P 0 := by
    refine ⟨zeroBoolMatrix n n, zeroBoolMatrix_avoids_permutation hk π, ?_⟩
    simp
  simpa [forbiddenExtremal, P] using
    Nat.findGreatest_spec (P := P) (m := 0) (n := n * n) (Nat.zero_le _) h0

/-- Every avoiding matrix has at most the extremal number of true entries. -/
theorem oneEntries_card_le_forbiddenExtremal {k n : ℕ}
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin n) (Fin n) Bool)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (oneEntries A).card ≤ forbiddenExtremal (permutationMatrix π) n := by
  classical
  by_contra hle
  have hgt : forbiddenExtremal (permutationMatrix π) n < (oneEntries A).card :=
    Nat.lt_of_not_ge hle
  have hbound : (oneEntries A).card ≤ n * n := oneEntries_card_le A
  exact Nat.findGreatest_is_greatest
    (P := fun q => ∃ B : _root_.Matrix (Fin n) (Fin n) Bool,
      AvoidsPattern B (permutationMatrix π) ∧ (oneEntries B).card = q)
    (n := n * n) hgt hbound ⟨A, hA, rfl⟩

/-! ## Cropping square matrices -/

/-- The order embedding of an initial segment `Fin m` into `Fin n`. -/
def finCastLEOrderEmb {m n : ℕ} (hmn : m ≤ n) : Fin m ↪o Fin n :=
  OrderEmbedding.ofStrictMono (Fin.castLE hmn) (by
    intro a b hab
    exact Fin.mk_lt_mk.mpr (by simpa using hab))

/-- The upper-left `m × m` submatrix of an `n × n` matrix. -/
def cropMatrix {m n : ℕ} (hmn : m ≤ n)
    (A : _root_.Matrix (Fin n) (Fin n) Bool) :
    _root_.Matrix (Fin m) (Fin m) Bool :=
  fun i j => A (Fin.castLE hmn i) (Fin.castLE hmn j)

/-- Containment in a crop lifts to containment in the original matrix. -/
theorem cropMatrix_lifts_containment {m n k l : ℕ} (hmn : m ≤ n)
    (A : _root_.Matrix (Fin n) (Fin n) Bool)
    (P : _root_.Matrix (Fin k) (Fin l) Bool)
    (h : ContainsPattern (cropMatrix hmn A) P) :
    ContainsPattern A P := by
  rcases h with ⟨row, col, hcontains⟩
  let row' : Fin k ↪o Fin n :=
    OrderEmbedding.ofStrictMono (fun i => Fin.castLE hmn (row i)) (by
      intro i j hij
      exact Fin.mk_lt_mk.mpr (by simpa using row.strictMono hij))
  let col' : Fin l ↪o Fin n :=
    OrderEmbedding.ofStrictMono (fun j => Fin.castLE hmn (col j)) (by
      intro i j hij
      exact Fin.mk_lt_mk.mpr (by simpa using col.strictMono hij))
  exact ⟨row', col', by
    intro i j hij
    simpa [row', col', cropMatrix] using hcontains i j hij⟩

/-- Avoidance is inherited by upper-left crops. -/
theorem cropMatrix_avoids {m n k l : ℕ} (hmn : m ≤ n)
    {A : _root_.Matrix (Fin n) (Fin n) Bool}
    {P : _root_.Matrix (Fin k) (Fin l) Bool}
    (hA : AvoidsPattern A P) :
    AvoidsPattern (cropMatrix hmn A) P := by
  intro h
  exact hA (cropMatrix_lifts_containment hmn A P h)

/-- Restrict a `Fin n` value to `Fin m`, using `0` only outside the initial
segment.  Lemmas below use it on entries known to lie inside the segment. -/
def finRestrict {m n : ℕ} (hm : 0 < m) (x : Fin n) : Fin m :=
  if h : x.1 < m then ⟨x.1, h⟩ else ⟨0, hm⟩

theorem castLE_finRestrict {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {x : Fin n} (hx : x.1 < m) :
    Fin.castLE hmn (finRestrict hm x) = x := by
  ext
  simp [finRestrict, hx]

theorem insideEntries_card_le_forbiddenExtremal {k m n : ℕ}
    (π : Equiv.Perm (Fin k)) (hm : 0 < m) (hmn : m ≤ n)
    (A : _root_.Matrix (Fin n) (Fin n) Bool)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    ((oneEntries A).filter fun p => p.1.1 < m ∧ p.2.1 < m).card ≤
      forbiddenExtremal (permutationMatrix π) m := by
  classical
  let inside := (oneEntries A).filter fun p => p.1.1 < m ∧ p.2.1 < m
  let B := cropMatrix hmn A
  let toCrop := fun p : Fin n × Fin n => (finRestrict hm p.1, finRestrict hm p.2)
  have hmaps : Set.MapsTo toCrop inside (oneEntries B) := by
    intro p hp
    have hp' : p ∈ oneEntries A ∧ (p.1.1 < m ∧ p.2.1 < m) := by
      simpa [inside] using hp
    have htrue : A p.1 p.2 = true := (mem_oneEntries_iff A p).mp hp'.1
    have hrow := castLE_finRestrict hm hmn hp'.2.1
    have hcol := castLE_finRestrict hm hmn hp'.2.2
    exact (mem_oneEntries_iff B (toCrop p)).mpr (by
      simpa [B, cropMatrix, toCrop, hrow, hcol] using htrue)
  have hinj : (inside : Set (Fin n × Fin n)).InjOn toCrop := by
    intro p hp r hr hpr
    have hp' : p ∈ oneEntries A ∧ (p.1.1 < m ∧ p.2.1 < m) := by
      simpa [inside] using hp
    have hr' : r ∈ oneEntries A ∧ (r.1.1 < m ∧ r.2.1 < m) := by
      simpa [inside] using hr
    have hrow : p.1 = r.1 := by
      have hrowFin : (toCrop p).1 = (toCrop r).1 := congrArg Prod.fst hpr
      have hval := congrArg Fin.val hrowFin
      apply Fin.ext
      simpa [toCrop, finRestrict, hp'.2.1, hr'.2.1] using hval
    have hcol : p.2 = r.2 := by
      have hcolFin : (toCrop p).2 = (toCrop r).2 := congrArg Prod.snd hpr
      have hval := congrArg Fin.val hcolFin
      apply Fin.ext
      simpa [toCrop, finRestrict, hp'.2.2, hr'.2.2] using hval
    exact Prod.ext hrow hcol
  calc
    inside.card ≤ (oneEntries B).card :=
      Finset.card_le_card_of_injOn toCrop hmaps hinj
    _ ≤ forbiddenExtremal (permutationMatrix π) m :=
      oneEntries_card_le_forbiddenExtremal π B (cropMatrix_avoids hmn hA)

theorem highFinset_card {m n : ℕ} (hmn : m < n) :
    ((Finset.univ : Finset (Fin n)).filter fun i => m ≤ i.1).card = n - m := by
  let a : Fin n := ⟨m, hmn⟩
  have hset : ((Finset.univ : Finset (Fin n)).filter fun i => m ≤ i.1) =
      Finset.Ici a := by
    ext i
    simp [a, Finset.mem_Ici, Fin.le_iff_val_le_val]
  rw [hset]
  simp [a, Fin.card_Ici]

theorem boundaryPairs_card_le {m n : ℕ} (hmn : m < n) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter
      fun p => ¬ (p.1.1 < m ∧ p.2.1 < m)).card ≤ 2 * (n - m) * n := by
  classical
  let R : Finset (Fin n × Fin n) :=
    (Finset.univ.filter fun p : Fin n × Fin n => m ≤ p.1.1)
  let C : Finset (Fin n × Fin n) :=
    (Finset.univ.filter fun p : Fin n × Fin n => m ≤ p.2.1)
  have hcover :
      ((Finset.univ : Finset (Fin n × Fin n)).filter
        fun p => ¬ (p.1.1 < m ∧ p.2.1 < m)) ⊆ R ∪ C := by
    intro p hp
    have hpnot : ¬ (p.1.1 < m ∧ p.2.1 < m) := by simpa using hp
    by_cases hrow : p.1.1 < m
    · have hcol : m ≤ p.2.1 := Nat.le_of_not_gt (by
        intro h
        exact hpnot ⟨hrow, h⟩)
      simp [R, C, hcol]
    · have hrow' : m ≤ p.1.1 := Nat.le_of_not_gt hrow
      simp [R, C, hrow']
  let rowSet : Finset (Fin n) := Finset.univ.filter fun i => m ≤ i.1
  have hRsub : R ⊆ rowSet.product (Finset.univ : Finset (Fin n)) := by
    intro p hp
    have hp' : m ≤ p.1.1 := by simpa [R] using hp
    exact Finset.mem_product.mpr ⟨by simp [rowSet, hp'], Finset.mem_univ _⟩
  have hCsub : C ⊆ (Finset.univ : Finset (Fin n)).product rowSet := by
    intro p hp
    have hp' : m ≤ p.2.1 := by simpa [C] using hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, by simp [rowSet, hp']⟩
  have hrowSet_card : rowSet.card = n - m := by
    simpa [rowSet] using highFinset_card hmn
  have hRcard : R.card ≤ (n - m) * n := by
    calc
      R.card ≤ (rowSet.product (Finset.univ : Finset (Fin n))).card :=
        Finset.card_le_card hRsub
      _ = rowSet.card * n := by simp
      _ = (n - m) * n := by simp [hrowSet_card]
  have hCcard : C.card ≤ (n - m) * n := by
    calc
      C.card ≤ ((Finset.univ : Finset (Fin n)).product rowSet).card :=
        Finset.card_le_card hCsub
      _ = n * rowSet.card := by simp
      _ = (n - m) * n := by simp [hrowSet_card, Nat.mul_comm]
  calc
    ((Finset.univ : Finset (Fin n × Fin n)).filter
        fun p => ¬ (p.1.1 < m ∧ p.2.1 < m)).card ≤ (R ∪ C).card :=
      Finset.card_le_card hcover
    _ ≤ R.card + C.card := Finset.card_union_le R C
    _ ≤ (n - m) * n + (n - m) * n := Nat.add_le_add hRcard hCcard
    _ = 2 * (n - m) * n := by ring

/-- Cropping to an initial `m × m` submatrix loses at most the boundary rows
and columns. -/
theorem forbiddenExtremal_le_crop_add_boundary {k m n : ℕ}
    (π : Equiv.Perm (Fin k)) (hk : 0 < k) (hm : 0 < m) (hmn : m ≤ n) (hmn' : m < n) :
    forbiddenExtremal (permutationMatrix π) n ≤
      forbiddenExtremal (permutationMatrix π) m + 2 * (n - m) * n := by
  classical
  obtain ⟨A, hA, hcard⟩ := exists_forbiddenExtremal_eq (n := n) hk π
  let inside := (oneEntries A).filter fun p => p.1.1 < m ∧ p.2.1 < m
  let outside := (oneEntries A).filter fun p => ¬ (p.1.1 < m ∧ p.2.1 < m)
  have hsplit : (oneEntries A).card = inside.card + outside.card := by
    simpa [inside, outside, Nat.add_comm] using
      (Finset.card_filter_add_card_filter_not
        (s := oneEntries A) (p := fun p : Fin n × Fin n => p.1.1 < m ∧ p.2.1 < m)).symm
  have hinside : inside.card ≤ forbiddenExtremal (permutationMatrix π) m := by
    simpa [inside] using insideEntries_card_le_forbiddenExtremal π hm hmn A hA
  have houtside : outside.card ≤ 2 * (n - m) * n := by
    calc
      outside.card ≤
          ((Finset.univ : Finset (Fin n × Fin n)).filter
            fun p => ¬ (p.1.1 < m ∧ p.2.1 < m)).card :=
        Finset.card_le_card (by
          intro p hp
          have hp' : p ∈ oneEntries A ∧ ¬ (p.1.1 < m ∧ p.2.1 < m) := by
            simpa [outside] using hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hp'.2)
      _ ≤ 2 * (n - m) * n := boundaryPairs_card_le hmn'
  calc
    forbiddenExtremal (permutationMatrix π) n = (oneEntries A).card := hcard.symm
    _ = inside.card + outside.card := hsplit
    _ ≤ forbiddenExtremal (permutationMatrix π) m + 2 * (n - m) * n :=
      Nat.add_le_add hinside houtside

/-- The block-recursion statement of Marcus--Tardos Lemma 7.

For a `k × k` permutation matrix `P`, the extremal function at `q * k^2` is
bounded in terms of the extremal function at `q`.  This is the paper's
`n / k^2` recurrence, stated with the quotient `q` explicit to avoid dependent
casts between `Fin n` and `Fin (q * k^2)`.

The binomial factor is `choose (k^2) k`: each block has side length `k^2`, and
Lemma 5 chooses `k` active columns from those `k^2` columns. -/
def FurediHajnalRecursion : Prop :=
  ∀ {k q : ℕ} (P : _root_.Matrix (Fin k) (Fin k) Bool),
    2 ≤ k → IsPermutationMatrix P →
      forbiddenExtremal P (q * k ^ 2) ≤
        (k - 1) ^ 2 * forbiddenExtremal P q +
          2 * k ^ 3 * Nat.choose (k ^ 2) k * (q * k ^ 2)

/-- The explicit linear bound of Marcus--Tardos Theorem 8, with the constant
appearing in the paper. -/
def FurediHajnalExplicitBound : Prop :=
  ∀ {k n : ℕ} (P : _root_.Matrix (Fin k) (Fin k) Bool),
    2 ≤ k → IsPermutationMatrix P →
      forbiddenExtremal P n ≤ 2 * k ^ 4 * Nat.choose (k ^ 2) k * n

/-- The qualitative Füredi--Hajnal theorem for permutation matrices. -/
def FurediHajnalTheorem : Prop :=
  ∀ {k : ℕ} (P : _root_.Matrix (Fin k) (Fin k) Bool),
    2 ≤ k → IsPermutationMatrix P → ∃ c : ℕ, ∀ n, forbiddenExtremal P n ≤ c * n

theorem furediHajnalTheorem_of_explicitBound
    (h : FurediHajnalExplicitBound) : FurediHajnalTheorem := by
  intro k P hk hP
  exact ⟨2 * k ^ 4 * Nat.choose (k ^ 2) k, fun n => h P hk hP⟩

/-! ## Block decomposition from Section 2 -/

/-- Rows belonging to the `I`-th consecutive block when a `q * s` square matrix
is partitioned into `q × q` blocks of side length `s`. -/
def blockRows (q s : ℕ) (I : Fin q) : Finset (Fin (q * s)) :=
  Finset.univ.filter fun r => I.1 * s ≤ r.1 ∧ r.1 < (I.1 + 1) * s

/-- Columns belonging to the `J`-th consecutive block. -/
def blockCols (q s : ℕ) (J : Fin q) : Finset (Fin (q * s)) :=
  Finset.univ.filter fun c => J.1 * s ≤ c.1 ∧ c.1 < (J.1 + 1) * s

/-- The block index of a row or column in a `q × q` block decomposition with
side length `s`. -/
def blockIndex (q s : ℕ) (x : Fin (q * s)) : Fin q :=
  ⟨x.1 / s, Nat.div_lt_of_lt_mul
    (lt_of_lt_of_le x.2 (le_of_eq (Nat.mul_comm q s)))⟩

/-- A row belongs to the block selected by its quotient index. -/
theorem blockIndex_mem_blockRows {q s : ℕ} (hs : 0 < s) (x : Fin (q * s)) :
    x ∈ blockRows q s (blockIndex q s x) := by
  have hlow : (x.1 / s) * s ≤ x.1 := Nat.div_mul_le_self x.1 s
  have hupper : x.1 < (x.1 / s + 1) * s := by
    calc
      x.1 = s * (x.1 / s) + x.1 % s := (Nat.div_add_mod x.1 s).symm
      _ < s * (x.1 / s) + s := Nat.add_lt_add_left (Nat.mod_lt x.1 hs) _
      _ = (x.1 / s + 1) * s := by ring
  simpa [blockRows, blockIndex] using ⟨hlow, hupper⟩

/-- A column belongs to the block selected by its quotient index. -/
theorem blockIndex_mem_blockCols {q s : ℕ} (hs : 0 < s) (x : Fin (q * s)) :
    x ∈ blockCols q s (blockIndex q s x) := by
  have hlow : (x.1 / s) * s ≤ x.1 := Nat.div_mul_le_self x.1 s
  have hupper : x.1 < (x.1 / s + 1) * s := by
    calc
      x.1 = s * (x.1 / s) + x.1 % s := (Nat.div_add_mod x.1 s).symm
      _ < s * (x.1 / s) + s := Nat.add_lt_add_left (Nat.mod_lt x.1 hs) _
      _ = (x.1 / s + 1) * s := by ring
  simpa [blockCols, blockIndex] using ⟨hlow, hupper⟩

/-- The block containing a matrix entry. -/
def entryBlockIndex {q s : ℕ} (p : Fin (q * s) × Fin (q * s)) : Fin q × Fin q :=
  (blockIndex q s p.1, blockIndex q s p.2)

/-- The `(I,J)` block contains a true entry. -/
def BlockNonempty {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (I J : Fin q) : Prop :=
  ∃ r ∈ blockRows q s I, ∃ c ∈ blockCols q s J, A r c = true

/-- True entries lying in a specific block. -/
noncomputable def blockEntries {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (I J : Fin q) : Finset (Fin (q * s) × Fin (q * s)) :=
  by
    classical
    exact Finset.univ.filter fun p =>
      p.1 ∈ blockRows q s I ∧ p.2 ∈ blockCols q s J ∧ A p.1 p.2 = true

/-- The compressed block matrix `B` of Marcus--Tardos Lemma 4.  Its entry is
`true` precisely when the corresponding block of `A` is nonempty. -/
noncomputable def blockCompression {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) :
    _root_.Matrix (Fin q) (Fin q) Bool :=
  by
    classical
    exact fun I J => decide (BlockNonempty A I J)

/-- Columns of a block containing at least one true entry. -/
noncomputable def activeBlockCols {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (I J : Fin q) : Finset (Fin (q * s)) :=
  by
    classical
    exact (blockCols q s J).filter fun c =>
      ∃ r ∈ blockRows q s I, A r c = true

/-- Rows of a block containing at least one true entry. -/
noncomputable def activeBlockRows {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (I J : Fin q) : Finset (Fin (q * s)) :=
  by
    classical
    exact (blockRows q s I).filter fun r =>
      ∃ c ∈ blockCols q s J, A r c = true

/-- A block is wide when its true entries appear in at least `threshold`
different columns.  In Section 2 the threshold is `k`. -/
def BlockWide {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) (I J : Fin q) : Prop :=
  threshold ≤ (activeBlockCols A I J).card

/-- A block is tall when its true entries appear in at least `threshold`
different rows.  In Section 2 the threshold is `k`. -/
def BlockTall {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) (I J : Fin q) : Prop :=
  threshold ≤ (activeBlockRows A I J).card

/-- The row blocks in a fixed block column that are wide. -/
noncomputable def wideBlocksInColumn {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) (J : Fin q) : Finset (Fin q) :=
  by
    classical
    exact Finset.univ.filter fun I => BlockWide A threshold I J

/-- The column blocks in a fixed block row that are tall. -/
noncomputable def tallBlocksInRow {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) (I : Fin q) : Finset (Fin q) :=
  by
    classical
    exact Finset.univ.filter fun J => BlockTall A threshold I J

/-- The `X₃` blocks from Marcus--Tardos Lemma 7: nonempty blocks that are
neither wide nor tall. -/
noncomputable def nonemptyNarrowBlocks {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) : Finset (Fin q × Fin q) :=
  by
    classical
    exact Finset.univ.filter fun p =>
      BlockNonempty A p.1 p.2 ∧ ¬ BlockWide A threshold p.1 p.2 ∧
        ¬ BlockTall A threshold p.1 p.2

/-- All wide blocks of a block decomposition. -/
noncomputable def wideBlocks {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) : Finset (Fin q × Fin q) :=
  by
    classical
    exact Finset.univ.filter fun p => BlockWide A threshold p.1 p.2

/-- All tall blocks of a block decomposition. -/
noncomputable def tallBlocks {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) : Finset (Fin q × Fin q) :=
  by
    classical
    exact Finset.univ.filter fun p => BlockTall A threshold p.1 p.2

/-- A chosen set of `threshold` active columns in a wide block.

For non-wide blocks this returns `∅`; all lemmas below use it only on wide
blocks. -/
noncomputable def chosenActiveCols {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) (I J : Fin q) : Finset (Fin (q * s)) :=
  by
    classical
    exact if h : BlockWide A threshold I J then
      Classical.choose (Finset.powersetCard_nonempty.mpr h)
    else
      ∅

/-- A chosen set of `threshold` active rows in a tall block.

For non-tall blocks this returns `∅`; all lemmas below use it only on tall
blocks. -/
noncomputable def chosenActiveRows {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (threshold : ℕ) (I J : Fin q) : Finset (Fin (q * s)) :=
  by
    classical
    exact if h : BlockTall A threshold I J then
      Classical.choose (Finset.powersetCard_nonempty.mpr h)
    else
      ∅

theorem mem_blockCompression_iff {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I J : Fin q) :
    blockCompression A I J = true ↔ BlockNonempty A I J := by
  classical
  simp [blockCompression]

theorem activeBlockCols_subset_blockCols {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I J : Fin q) :
    activeBlockCols A I J ⊆ blockCols q s J := by
  classical
  intro c hc
  exact (by
    simpa [activeBlockCols] using hc : c ∈ blockCols q s J ∧
      ∃ r ∈ blockRows q s I, A r c = true).1

theorem activeBlockRows_subset_blockRows {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I J : Fin q) :
    activeBlockRows A I J ⊆ blockRows q s I := by
  classical
  intro r hr
  exact (by
    simpa [activeBlockRows] using hr : r ∈ blockRows q s I ∧
      ∃ c ∈ blockCols q s J, A r c = true).1

theorem blockEntries_subset_active_product {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I J : Fin q) :
    blockEntries A I J ⊆ (activeBlockRows A I J).product (activeBlockCols A I J) := by
  classical
  intro p hp
  have hp' : p.1 ∈ blockRows q s I ∧ p.2 ∈ blockCols q s J ∧ A p.1 p.2 = true := by
    simpa [blockEntries] using hp
  exact Finset.mem_product.mpr
    ⟨by
      simp [activeBlockRows, hp'.1]
      exact ⟨p.2, hp'.2.1, hp'.2.2⟩,
     by
      simp [activeBlockCols, hp'.2.1]
      exact ⟨p.1, hp'.1, hp'.2.2⟩⟩

theorem blockEntries_card_le_active_mul {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I J : Fin q) :
    (blockEntries A I J).card ≤
      (activeBlockRows A I J).card * (activeBlockCols A I J).card := by
  classical
  calc
    (blockEntries A I J).card ≤
        ((activeBlockRows A I J).product (activeBlockCols A I J)).card :=
      Finset.card_le_card (blockEntries_subset_active_product A I J)
    _ = (activeBlockRows A I J).card * (activeBlockCols A I J).card := by simp

theorem blockEntries_card_le_of_not_wide_not_tall {q s k : ℕ} (_hk : 0 < k)
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I J : Fin q)
    (hwide : ¬ BlockWide A k I J) (htall : ¬ BlockTall A k I J) :
    (blockEntries A I J).card ≤ (k - 1) ^ 2 := by
  have hcols_lt : (activeBlockCols A I J).card < k := Nat.lt_of_not_ge hwide
  have hrows_lt : (activeBlockRows A I J).card < k := Nat.lt_of_not_ge htall
  have hcols_le : (activeBlockCols A I J).card ≤ k - 1 := Nat.le_pred_of_lt hcols_lt
  have hrows_le : (activeBlockRows A I J).card ≤ k - 1 := Nat.le_pred_of_lt hrows_lt
  calc
    (blockEntries A I J).card ≤
        (activeBlockRows A I J).card * (activeBlockCols A I J).card :=
      blockEntries_card_le_active_mul A I J
    _ ≤ (k - 1) * (k - 1) := Nat.mul_le_mul hrows_le hcols_le
    _ = (k - 1) ^ 2 := by ring

theorem chosenActiveCols_mem_powersetCard {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (hwide : BlockWide A threshold I J) :
    chosenActiveCols A threshold I J ∈
      (activeBlockCols A I J).powersetCard threshold := by
  classical
  simp [chosenActiveCols, hwide,
    Classical.choose_spec (Finset.powersetCard_nonempty.mpr hwide)]

theorem chosenActiveCols_subset_active {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (hwide : BlockWide A threshold I J) :
    chosenActiveCols A threshold I J ⊆ activeBlockCols A I J :=
  (Finset.mem_powersetCard.mp (chosenActiveCols_mem_powersetCard A hwide)).1

theorem chosenActiveCols_card {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (hwide : BlockWide A threshold I J) :
    (chosenActiveCols A threshold I J).card = threshold :=
  (Finset.mem_powersetCard.mp (chosenActiveCols_mem_powersetCard A hwide)).2

theorem chosenActiveCols_subset_blockCols {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (hwide : BlockWide A threshold I J) :
    chosenActiveCols A threshold I J ⊆ blockCols q s J :=
  (chosenActiveCols_subset_active A hwide).trans (activeBlockCols_subset_blockCols A I J)

theorem chosenActiveRows_mem_powersetCard {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (htall : BlockTall A threshold I J) :
    chosenActiveRows A threshold I J ∈
      (activeBlockRows A I J).powersetCard threshold := by
  classical
  simp [chosenActiveRows, htall,
    Classical.choose_spec (Finset.powersetCard_nonempty.mpr htall)]

theorem chosenActiveRows_subset_active {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (htall : BlockTall A threshold I J) :
    chosenActiveRows A threshold I J ⊆ activeBlockRows A I J :=
  (Finset.mem_powersetCard.mp (chosenActiveRows_mem_powersetCard A htall)).1

theorem chosenActiveRows_card {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (htall : BlockTall A threshold I J) :
    (chosenActiveRows A threshold I J).card = threshold :=
  (Finset.mem_powersetCard.mp (chosenActiveRows_mem_powersetCard A htall)).2

theorem chosenActiveRows_subset_blockRows {q s threshold : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    {I J : Fin q} (htall : BlockTall A threshold I J) :
    chosenActiveRows A threshold I J ⊆ blockRows q s I :=
  (chosenActiveRows_subset_active A htall).trans (activeBlockRows_subset_blockRows A I J)

/-- A finite pigeonhole principle in the form needed for Lemma 5.  If a finite
set is larger than `(k - 1)` times the number of fibers of a map, then one fiber
has at least `k` elements. -/
theorem exists_fiber_card_ge_of_sub_one_mul_image_card_lt
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) {k : ℕ}
    (hlarge : (k - 1) * (S.image f).card < S.card) :
    ∃ b ∈ S.image f, k ≤ (S.filter fun a => f a = b).card := by
  classical
  by_contra h
  push Not at h
  have hfiber : ∀ b ∈ S.image f, (S.filter fun a => f a = b).card ≤ k - 1 := by
    intro b hb
    exact Nat.le_pred_of_lt (h b hb)
  have hcard := Finset.card_le_mul_card_image (s := S) (f := f) (n := k - 1) hfiber
  exact not_lt_of_ge hcard hlarge

/-- Membership in `blockRows` is exactly the defining pair of inequalities. -/
theorem mem_blockRows_iff {q s : ℕ} (I : Fin q) (r : Fin (q * s)) :
    r ∈ blockRows q s I ↔ I.1 * s ≤ r.1 ∧ r.1 < (I.1 + 1) * s := by
  simp [blockRows]

/-- Membership in `blockCols` is exactly the defining pair of inequalities. -/
theorem mem_blockCols_iff {q s : ℕ} (J : Fin q) (c : Fin (q * s)) :
    c ∈ blockCols q s J ↔ J.1 * s ≤ c.1 ∧ c.1 < (J.1 + 1) * s := by
  simp [blockCols]

/-- Each row block has side length `s`. -/
theorem blockRows_card {q s : ℕ} (I : Fin q) :
    (blockRows q s I).card = s := by
  classical
  refine Finset.card_eq_of_bijective (s := blockRows q s I) (n := s)
    (fun a ha => (⟨I.1 * s + a, ?_⟩ : Fin (q * s))) ?_ ?_ ?_
  · have hIq : I.1 + 1 ≤ q := Nat.succ_le_of_lt I.2
    have hbound : I.1 * s + s ≤ q * s := by
      simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.mul_le_mul_right s hIq)
    exact lt_of_lt_of_le (Nat.add_lt_add_left ha _) hbound
  · intro r hr
    have hr' := (mem_blockRows_iff I r).mp hr
    refine ⟨r.1 - I.1 * s, ?_, ?_⟩
    · have hupper : r.1 < I.1 * s + s := by
        simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hr'.2
      have hsub := (Nat.sub_lt_sub_iff_right hr'.1).2 hupper
      simpa [Nat.add_sub_cancel_left] using hsub
    · ext
      exact Nat.add_sub_cancel' hr'.1
  · intro a ha
    exact (mem_blockRows_iff I _).mpr ⟨Nat.le_add_right _ _, by
      simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.add_lt_add_left ha (I.1 * s))⟩
  · intro a ha b hb h
    exact Nat.add_left_cancel (Fin.ext_iff.mp h)

/-- Each column block has side length `s`. -/
theorem blockCols_card {q s : ℕ} (J : Fin q) :
    (blockCols q s J).card = s := by
  classical
  refine Finset.card_eq_of_bijective (s := blockCols q s J) (n := s)
    (fun a ha => (⟨J.1 * s + a, ?_⟩ : Fin (q * s))) ?_ ?_ ?_
  · have hJq : J.1 + 1 ≤ q := Nat.succ_le_of_lt J.2
    have hbound : J.1 * s + s ≤ q * s := by
      simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.mul_le_mul_right s hJq)
    exact lt_of_lt_of_le (Nat.add_lt_add_left ha _) hbound
  · intro c hc
    have hc' := (mem_blockCols_iff J c).mp hc
    refine ⟨c.1 - J.1 * s, ?_, ?_⟩
    · have hupper : c.1 < J.1 * s + s := by
        simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hc'.2
      have hsub := (Nat.sub_lt_sub_iff_right hc'.1).2 hupper
      simpa [Nat.add_sub_cancel_left] using hsub
    · ext
      exact Nat.add_sub_cancel' hc'.1
  · intro a ha
    exact (mem_blockCols_iff J _).mpr ⟨Nat.le_add_right _ _, by
      simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.add_lt_add_left ha (J.1 * s))⟩
  · intro a ha b hb h
    exact Nat.add_left_cancel (Fin.ext_iff.mp h)

/-- Any entry in an earlier row block is above any entry in a later row block. -/
theorem blockRows_lt_of_lt {q s : ℕ} {I J : Fin q} {r t : Fin (q * s)}
    (hIJ : I < J) (hr : r ∈ blockRows q s I) (ht : t ∈ blockRows q s J) :
    r < t := by
  have hr' := (mem_blockRows_iff I r).mp hr
  have ht' := (mem_blockRows_iff J t).mp ht
  exact Fin.mk_lt_mk.mpr (lt_of_lt_of_le hr'.2 (by
    exact le_trans (Nat.mul_le_mul_right s (Nat.succ_le_of_lt hIJ)) ht'.1))

/-- Any entry in an earlier column block is left of any entry in a later column
block. -/
theorem blockCols_lt_of_lt {q s : ℕ} {I J : Fin q} {r t : Fin (q * s)}
    (hIJ : I < J) (hr : r ∈ blockCols q s I) (ht : t ∈ blockCols q s J) :
    r < t := by
  have hr' := (mem_blockCols_iff I r).mp hr
  have ht' := (mem_blockCols_iff J t).mp ht
  exact Fin.mk_lt_mk.mpr (lt_of_lt_of_le hr'.2 (by
    exact le_trans (Nat.mul_le_mul_right s (Nat.succ_le_of_lt hIJ)) ht'.1))

/-- The permutation-matrix case of Marcus--Tardos Lemma 4: if the compressed
block matrix contains a permutation matrix, then the original matrix contains
it. -/
theorem blockCompression_lifts_permutation_containment {q s k : ℕ}
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (h : ContainsPattern (blockCompression A) (permutationMatrix π)) :
    ContainsPattern A (permutationMatrix π) := by
  classical
  rcases h with ⟨row, col, hcontains⟩
  have hblock : ∀ i : Fin k, BlockNonempty A (row i) (col (π i)) := by
    intro i
    exact (mem_blockCompression_iff A (row i) (col (π i))).mp
      (hcontains i (π i) (by simp [permutationMatrix]))
  choose pickedRow pickedRow_mem pickedCol pickedCol_mem picked_true using hblock
  let row' : Fin k ↪o Fin (q * s) :=
    OrderEmbedding.ofStrictMono pickedRow (by
      intro i j hij
      exact blockRows_lt_of_lt (row.strictMono hij) (pickedRow_mem i) (pickedRow_mem j))
  let col' : Fin k ↪o Fin (q * s) :=
    OrderEmbedding.ofStrictMono (fun j : Fin k => pickedCol (π.symm j)) (by
      intro i j hij
      have hci : pickedCol (π.symm i) ∈ blockCols q s (col i) := by
        simpa using pickedCol_mem (π.symm i)
      have hcj : pickedCol (π.symm j) ∈ blockCols q s (col j) := by
        simpa using pickedCol_mem (π.symm j)
      exact blockCols_lt_of_lt (col.strictMono hij) hci hcj)
  refine ⟨row', col', ?_⟩
  intro i j hP
  have hj : j = π i := by
    simpa [permutationMatrix] using hP
  subst j
  simpa [row', col'] using picked_true i

/-- Marcus--Tardos Lemma 4, packaged as the avoidance form that follows from
`BlockCompressionLiftsPermutationContainment`. -/
theorem blockCompression_avoids_permutation
    {q s k : ℕ} (π : Equiv.Perm (Fin k))
    {A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool}
    (hA : AvoidsPattern A (permutationMatrix π)) :
    AvoidsPattern (blockCompression A) (permutationMatrix π) := by
  intro hB
  exact hA (blockCompression_lifts_permutation_containment π A hB)

/-- The number of nonempty narrow blocks is bounded by the number of true
entries in the compressed block matrix. -/
theorem nonemptyNarrowBlocks_card_le_blockCompression_ones {q s k : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) :
    (nonemptyNarrowBlocks A k).card ≤ (oneEntries (blockCompression A)).card := by
  classical
  refine Finset.card_le_card ?_
  intro p hp
  have hp' : BlockNonempty A p.1 p.2 ∧ ¬ BlockWide A k p.1 p.2 ∧
      ¬ BlockTall A k p.1 p.2 := by
    simpa [nonemptyNarrowBlocks] using hp
  exact (mem_oneEntries_iff (blockCompression A) p).mpr
    ((mem_blockCompression_iff A p.1 p.2).mpr hp'.1)

/-- The `X₃` bound used in Lemma 7: nonempty blocks that are neither wide nor
tall are bounded by the extremal number of the compressed matrix. -/
theorem nonemptyNarrowBlocks_card_le_forbiddenExtremal {q s k : ℕ}
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (nonemptyNarrowBlocks A k).card ≤
      forbiddenExtremal (permutationMatrix π) q := by
  exact le_trans (nonemptyNarrowBlocks_card_le_blockCompression_ones A)
    (oneEntries_card_le_forbiddenExtremal π (blockCompression A)
      (blockCompression_avoids_permutation π hA))

/-- If `k` row blocks in one block column share an ordered family of `k` active
columns, then the original matrix contains the corresponding permutation
matrix.  This is the constructive core of Marcus--Tardos Lemma 5; the remaining
part of Lemma 5 is the finite pigeonhole argument that produces these common
columns from too many wide blocks. -/
theorem contains_permutation_of_common_active_columns {q s k : ℕ}
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (J : Fin q) (rows : Fin k ↪o Fin q)
    (cols : Fin k ↪o Fin (q * s))
    (hactive : ∀ i : Fin k, cols (π i) ∈ activeBlockCols A (rows i) J) :
    ContainsPattern A (permutationMatrix π) := by
  classical
  have hrow_exists :
      ∀ i : Fin k, ∃ r ∈ blockRows q s (rows i), A r (cols (π i)) = true := by
    intro i
    have h := hactive i
    exact (by
      simpa [activeBlockCols] using h :
        cols (π i) ∈ blockCols q s J ∧
          ∃ r ∈ blockRows q s (rows i), A r (cols (π i)) = true).2
  choose pickedRow pickedRow_mem picked_true using hrow_exists
  let row' : Fin k ↪o Fin (q * s) :=
    OrderEmbedding.ofStrictMono pickedRow (by
      intro i j hij
      exact blockRows_lt_of_lt (rows.strictMono hij) (pickedRow_mem i) (pickedRow_mem j))
  refine ⟨row', cols, ?_⟩
  intro i j hP
  have hj : j = π i := by
    simpa [permutationMatrix] using hP
  subst j
  simpa [row'] using picked_true i

/-- Row/column dual of `contains_permutation_of_common_active_columns`: if `k`
column blocks in one block row share an ordered family of `k` active rows, then
the original matrix contains the corresponding permutation matrix. -/
theorem contains_permutation_of_common_active_rows {q s k : ℕ}
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (I : Fin q) (cols : Fin k ↪o Fin q)
    (rows : Fin k ↪o Fin (q * s))
    (hactive : ∀ j : Fin k, rows (π.symm j) ∈ activeBlockRows A I (cols j)) :
    ContainsPattern A (permutationMatrix π) := by
  classical
  have hcol_exists :
      ∀ j : Fin k, ∃ c ∈ blockCols q s (cols j), A (rows (π.symm j)) c = true := by
    intro j
    have h := hactive j
    exact (by
      simpa [activeBlockRows] using h :
        rows (π.symm j) ∈ blockRows q s I ∧
          ∃ c ∈ blockCols q s (cols j), A (rows (π.symm j)) c = true).2
  choose pickedCol pickedCol_mem picked_true using hcol_exists
  let col' : Fin k ↪o Fin (q * s) :=
    OrderEmbedding.ofStrictMono pickedCol (by
      intro i j hij
      exact blockCols_lt_of_lt (cols.strictMono hij) (pickedCol_mem i) (pickedCol_mem j))
  refine ⟨rows, col', ?_⟩
  intro i j hP
  have hj : j = π i := by
    simpa [permutationMatrix] using hP
  subst j
  simpa [col'] using picked_true (π i)

/-- Marcus--Tardos Lemma 5 in block language.  For a matrix avoiding a
`k × k` permutation matrix, a fixed block column has fewer than
`k * (#block columns choose k)` wide blocks.

In the paper's application the block side length is `s = k^2`, and
`#blockCols = s`, giving the displayed bound `k * (k^2 choose k)`. -/
theorem wideBlocksInColumn_card_lt {q s k : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (J : Fin q)
    (hks : k ≤ (blockCols q s J).card)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (wideBlocksInColumn A k J).card <
      k * Nat.choose (blockCols q s J).card k := by
  classical
  let W := wideBlocksInColumn A k J
  let chooseCols := fun I : Fin q => chosenActiveCols A k I J
  let C := Nat.choose (blockCols q s J).card k
  have hCpos : 0 < C := Nat.choose_pos hks
  by_contra hlt
  have hge : k * C ≤ W.card := le_of_not_gt hlt
  have himage_subset :
      W.image chooseCols ⊆ (blockCols q s J).powersetCard k := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨I, hIW, rfl⟩
    have hwide : BlockWide A k I J := by
      simpa [W, wideBlocksInColumn] using hIW
    exact Finset.mem_powersetCard.mpr
      ⟨chosenActiveCols_subset_blockCols A hwide, chosenActiveCols_card A hwide⟩
  have himage_card_le : (W.image chooseCols).card ≤ C := by
    calc
      (W.image chooseCols).card ≤ ((blockCols q s J).powersetCard k).card :=
        Finset.card_le_card himage_subset
      _ = C := by simp [C, Finset.card_powersetCard]
  have hlarge : (k - 1) * (W.image chooseCols).card < W.card := by
    have hle : (k - 1) * (W.image chooseCols).card ≤ (k - 1) * C :=
      Nat.mul_le_mul_left _ himage_card_le
    have hltKC : (k - 1) * C < k * C := by
      exact Nat.mul_lt_mul_of_pos_right (Nat.pred_lt hk.ne') hCpos
    exact lt_of_le_of_lt hle (lt_of_lt_of_le hltKC hge)
  obtain ⟨commonCols, hcommon_image, hfiber_card⟩ :=
    exists_fiber_card_ge_of_sub_one_mul_image_card_lt W chooseCols hlarge
  have hcommon_powerset : commonCols ∈ (blockCols q s J).powersetCard k :=
    himage_subset hcommon_image
  have hcommon_card : commonCols.card = k :=
    (Finset.mem_powersetCard.mp hcommon_powerset).2
  let fiber := W.filter fun I => chooseCols I = commonCols
  have hfiber_card : k ≤ fiber.card := by
    simpa [fiber] using hfiber_card
  obtain ⟨rowSet, hrowSet_mem⟩ := Finset.powersetCard_nonempty.mpr hfiber_card
  have hrowSet_subset_fiber : rowSet ⊆ fiber := (Finset.mem_powersetCard.mp hrowSet_mem).1
  have hrowSet_card : rowSet.card = k := (Finset.mem_powersetCard.mp hrowSet_mem).2
  let rows : Fin k ↪o Fin q := rowSet.orderEmbOfFin hrowSet_card
  let cols : Fin k ↪o Fin (q * s) := commonCols.orderEmbOfFin hcommon_card
  have hactive : ∀ i : Fin k, cols (π i) ∈ activeBlockCols A (rows i) J := by
    intro i
    have hrow_mem : rows i ∈ rowSet := Finset.orderEmbOfFin_mem rowSet hrowSet_card i
    have hfiber_mem : rows i ∈ fiber := hrowSet_subset_fiber hrow_mem
    have hW_mem : rows i ∈ W := by
      exact (by
        simpa [fiber] using hfiber_mem : rows i ∈ W ∧ chooseCols (rows i) = commonCols).1
    have hchoose_eq : chooseCols (rows i) = commonCols := by
      exact (by
        simpa [fiber] using hfiber_mem : rows i ∈ W ∧ chooseCols (rows i) = commonCols).2
    have hwide : BlockWide A k (rows i) J := by
      simpa [W, wideBlocksInColumn] using hW_mem
    have hcol_common : cols (π i) ∈ commonCols :=
      Finset.orderEmbOfFin_mem commonCols hcommon_card (π i)
    have hcol_chosen : cols (π i) ∈ chooseCols (rows i) := by
      simpa [hchoose_eq] using hcol_common
    exact chosenActiveCols_subset_active A hwide hcol_chosen
  exact hA (contains_permutation_of_common_active_columns π A J rows cols hactive)

/-- Proposition wrapper for Lemma 5. -/
def MarcusTardosLemma5 : Prop :=
  ∀ {q s k : ℕ} (_hk : 0 < k) (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (J : Fin q),
    k ≤ (blockCols q s J).card →
      AvoidsPattern A (permutationMatrix π) →
        (wideBlocksInColumn A k J).card <
          k * Nat.choose (blockCols q s J).card k

theorem marcusTardosLemma5 : MarcusTardosLemma5 :=
  fun hk π A J hks hA => wideBlocksInColumn_card_lt hk π A J hks hA

/-- Marcus--Tardos Lemma 5 with the paper-style bound `k * (s choose k)`,
using that every block column has side length `s`. -/
theorem wideBlocksInColumn_card_lt_choose_side {q s k : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (J : Fin q)
    (hks : k ≤ s)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (wideBlocksInColumn A k J).card < k * Nat.choose s k := by
  simpa [blockCols_card J] using
    wideBlocksInColumn_card_lt hk π A J (by simpa [blockCols_card J] using hks) hA

/-- Total number of wide blocks, bounded by summing Lemma 5 over all block
columns. -/
theorem wideBlocks_card_le {q s k : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (hks : k ≤ s)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (wideBlocks A k).card ≤ q * (k * Nat.choose s k) := by
  classical
  let f : Fin q × Fin q → Fin q := Prod.snd
  have hfiber : ∀ J ∈ (wideBlocks A k).image f,
      ((wideBlocks A k).filter fun p => f p = J).card ≤ k * Nat.choose s k := by
    intro J hJ
    have hsub :
        ((wideBlocks A k).filter fun p => f p = J).card ≤
          (wideBlocksInColumn A k J).card := by
      let F := (wideBlocks A k).filter fun p => f p = J
      have hcard_image : F.card = (F.image Prod.fst).card := by
        exact (Finset.card_image_of_injOn (s := F) (f := Prod.fst) (by
          intro a ha b hb hab
          have ha' : a ∈ wideBlocks A k ∧ f a = J := by simpa [F] using ha
          have hb' : b ∈ wideBlocks A k ∧ f b = J := by simpa [F] using hb
          ext
          · exact congrArg Fin.val hab
          · exact congrArg Fin.val (ha'.2.trans hb'.2.symm))).symm
      rw [hcard_image]
      refine Finset.card_le_card ?_
      intro I hI
      rcases Finset.mem_image.mp hI with ⟨p, hpF, rfl⟩
      have hp' : p ∈ wideBlocks A k ∧ f p = J := by simpa [F] using hpF
      have hwide : BlockWide A k p.1 p.2 := by simpa [wideBlocks] using hp'.1
      simpa [wideBlocksInColumn, ← hp'.2] using hwide
    exact le_trans hsub (Nat.le_of_lt (wideBlocksInColumn_card_lt_choose_side hk π A J hks hA))
  calc
    (wideBlocks A k).card ≤ (k * Nat.choose s k) * ((wideBlocks A k).image f).card :=
      Finset.card_le_mul_card_image (s := wideBlocks A k) (f := f)
        (n := k * Nat.choose s k) hfiber
    _ ≤ (k * Nat.choose s k) * q := by
      exact Nat.mul_le_mul_left _ (by simpa using Finset.card_le_univ ((wideBlocks A k).image f))
    _ = q * (k * Nat.choose s k) := by ring

/-- Proposition wrapper for the global wide-block count obtained by summing
Marcus--Tardos Lemma 5 over all block columns. -/
def MarcusTardosWideBlockCount : Prop :=
  ∀ {q s k : ℕ} (_hk : 0 < k) (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool),
    k ≤ s →
      AvoidsPattern A (permutationMatrix π) →
        (wideBlocks A k).card ≤ q * (k * Nat.choose s k)

theorem marcusTardosWideBlockCount : MarcusTardosWideBlockCount :=
  fun hk π A hks hA => wideBlocks_card_le hk π A hks hA

/-- Marcus--Tardos Lemma 6 in block language.  For a matrix avoiding a
`k × k` permutation matrix, a fixed block row has fewer than
`k * (#block rows choose k)` tall blocks. -/
theorem tallBlocksInRow_card_lt {q s k : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I : Fin q)
    (hks : k ≤ (blockRows q s I).card)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (tallBlocksInRow A k I).card <
      k * Nat.choose (blockRows q s I).card k := by
  classical
  let T := tallBlocksInRow A k I
  let chooseRows := fun J : Fin q => chosenActiveRows A k I J
  let C := Nat.choose (blockRows q s I).card k
  have hCpos : 0 < C := Nat.choose_pos hks
  by_contra hlt
  have hge : k * C ≤ T.card := le_of_not_gt hlt
  have himage_subset :
      T.image chooseRows ⊆ (blockRows q s I).powersetCard k := by
    intro R hR
    rcases Finset.mem_image.mp hR with ⟨J, hJT, rfl⟩
    have htall : BlockTall A k I J := by
      simpa [T, tallBlocksInRow] using hJT
    exact Finset.mem_powersetCard.mpr
      ⟨chosenActiveRows_subset_blockRows A htall, chosenActiveRows_card A htall⟩
  have himage_card_le : (T.image chooseRows).card ≤ C := by
    calc
      (T.image chooseRows).card ≤ ((blockRows q s I).powersetCard k).card :=
        Finset.card_le_card himage_subset
      _ = C := by simp [C, Finset.card_powersetCard]
  have hlarge : (k - 1) * (T.image chooseRows).card < T.card := by
    have hle : (k - 1) * (T.image chooseRows).card ≤ (k - 1) * C :=
      Nat.mul_le_mul_left _ himage_card_le
    have hltKC : (k - 1) * C < k * C := by
      exact Nat.mul_lt_mul_of_pos_right (Nat.pred_lt hk.ne') hCpos
    exact lt_of_le_of_lt hle (lt_of_lt_of_le hltKC hge)
  obtain ⟨commonRows, hcommon_image, hfiber_card⟩ :=
    exists_fiber_card_ge_of_sub_one_mul_image_card_lt T chooseRows hlarge
  have hcommon_powerset : commonRows ∈ (blockRows q s I).powersetCard k :=
    himage_subset hcommon_image
  have hcommon_card : commonRows.card = k :=
    (Finset.mem_powersetCard.mp hcommon_powerset).2
  let fiber := T.filter fun J => chooseRows J = commonRows
  have hfiber_card : k ≤ fiber.card := by
    simpa [fiber] using hfiber_card
  obtain ⟨colSet, hcolSet_mem⟩ := Finset.powersetCard_nonempty.mpr hfiber_card
  have hcolSet_subset_fiber : colSet ⊆ fiber := (Finset.mem_powersetCard.mp hcolSet_mem).1
  have hcolSet_card : colSet.card = k := (Finset.mem_powersetCard.mp hcolSet_mem).2
  let cols : Fin k ↪o Fin q := colSet.orderEmbOfFin hcolSet_card
  let rows : Fin k ↪o Fin (q * s) := commonRows.orderEmbOfFin hcommon_card
  have hactive : ∀ j : Fin k, rows (π.symm j) ∈ activeBlockRows A I (cols j) := by
    intro j
    have hcol_mem : cols j ∈ colSet := Finset.orderEmbOfFin_mem colSet hcolSet_card j
    have hfiber_mem : cols j ∈ fiber := hcolSet_subset_fiber hcol_mem
    have hT_mem : cols j ∈ T := by
      exact (by
        simpa [fiber] using hfiber_mem : cols j ∈ T ∧ chooseRows (cols j) = commonRows).1
    have hchoose_eq : chooseRows (cols j) = commonRows := by
      exact (by
        simpa [fiber] using hfiber_mem : cols j ∈ T ∧ chooseRows (cols j) = commonRows).2
    have htall : BlockTall A k I (cols j) := by
      simpa [T, tallBlocksInRow] using hT_mem
    have hrow_common : rows (π.symm j) ∈ commonRows :=
      Finset.orderEmbOfFin_mem commonRows hcommon_card (π.symm j)
    have hrow_chosen : rows (π.symm j) ∈ chooseRows (cols j) := by
      simpa [hchoose_eq] using hrow_common
    exact chosenActiveRows_subset_active A htall hrow_chosen
  exact hA (contains_permutation_of_common_active_rows π A I cols rows hactive)

/-- Proposition wrapper for Lemma 6. -/
def MarcusTardosLemma6 : Prop :=
  ∀ {q s k : ℕ} (_hk : 0 < k) (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I : Fin q),
    k ≤ (blockRows q s I).card →
      AvoidsPattern A (permutationMatrix π) →
        (tallBlocksInRow A k I).card <
          k * Nat.choose (blockRows q s I).card k

theorem marcusTardosLemma6 : MarcusTardosLemma6 :=
  fun hk π A I hks hA => tallBlocksInRow_card_lt hk π A I hks hA

/-- Marcus--Tardos Lemma 6 with the paper-style bound `k * (s choose k)`,
using that every block row has side length `s`. -/
theorem tallBlocksInRow_card_lt_choose_side {q s k : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I : Fin q)
    (hks : k ≤ s)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (tallBlocksInRow A k I).card < k * Nat.choose s k := by
  simpa [blockRows_card I] using
    tallBlocksInRow_card_lt hk π A I (by simpa [blockRows_card I] using hks) hA

/-- Total number of tall blocks, bounded by summing Lemma 6 over all block
rows. -/
theorem tallBlocks_card_le {q s k : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (hks : k ≤ s)
    (hA : AvoidsPattern A (permutationMatrix π)) :
    (tallBlocks A k).card ≤ q * (k * Nat.choose s k) := by
  classical
  let f : Fin q × Fin q → Fin q := Prod.fst
  have hfiber : ∀ I ∈ (tallBlocks A k).image f,
      ((tallBlocks A k).filter fun p => f p = I).card ≤ k * Nat.choose s k := by
    intro I hI
    have hsub :
        ((tallBlocks A k).filter fun p => f p = I).card ≤
          (tallBlocksInRow A k I).card := by
      let F := (tallBlocks A k).filter fun p => f p = I
      have hcard_image : F.card = (F.image Prod.snd).card := by
        exact (Finset.card_image_of_injOn (s := F) (f := Prod.snd) (by
          intro a ha b hb hab
          have ha' : a ∈ tallBlocks A k ∧ f a = I := by simpa [F] using ha
          have hb' : b ∈ tallBlocks A k ∧ f b = I := by simpa [F] using hb
          ext
          · exact congrArg Fin.val (ha'.2.trans hb'.2.symm)
          · exact congrArg Fin.val hab)).symm
      rw [hcard_image]
      refine Finset.card_le_card ?_
      intro J hJ
      rcases Finset.mem_image.mp hJ with ⟨p, hpF, rfl⟩
      have hp' : p ∈ tallBlocks A k ∧ f p = I := by simpa [F] using hpF
      have htall : BlockTall A k p.1 p.2 := by simpa [tallBlocks] using hp'.1
      simpa [tallBlocksInRow, ← hp'.2] using htall
    exact le_trans hsub (Nat.le_of_lt (tallBlocksInRow_card_lt_choose_side hk π A I hks hA))
  calc
    (tallBlocks A k).card ≤ (k * Nat.choose s k) * ((tallBlocks A k).image f).card :=
      Finset.card_le_mul_card_image (s := tallBlocks A k) (f := f)
        (n := k * Nat.choose s k) hfiber
    _ ≤ (k * Nat.choose s k) * q := by
      exact Nat.mul_le_mul_left _ (by simpa using Finset.card_le_univ ((tallBlocks A k).image f))
    _ = q * (k * Nat.choose s k) := by ring

/-- Proposition wrapper for the global tall-block count obtained by summing
Marcus--Tardos Lemma 6 over all block rows. -/
def MarcusTardosTallBlockCount : Prop :=
  ∀ {q s k : ℕ} (_hk : 0 < k) (π : Equiv.Perm (Fin k))
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool),
    k ≤ s →
      AvoidsPattern A (permutationMatrix π) →
        (tallBlocks A k).card ≤ q * (k * Nat.choose s k)

theorem marcusTardosTallBlockCount : MarcusTardosTallBlockCount :=
  fun hk π A hks hA => tallBlocks_card_le hk π A hks hA

/-! ## Local block-capacity bounds for Lemma 7 -/

/-- A single block contains at most `s^2` true entries. -/
theorem blockEntries_card_le_side_square {q s : ℕ}
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) (I J : Fin q) :
    (blockEntries A I J).card ≤ s ^ 2 := by
  classical
  calc
    (blockEntries A I J).card ≤
        (activeBlockRows A I J).card * (activeBlockCols A I J).card :=
      blockEntries_card_le_active_mul A I J
    _ ≤ (blockRows q s I).card * (blockCols q s J).card :=
      Nat.mul_le_mul
        (Finset.card_le_card (activeBlockRows_subset_blockRows A I J))
        (Finset.card_le_card (activeBlockCols_subset_blockCols A I J))
    _ = s ^ 2 := by
      simp [blockRows_card I, blockCols_card J, pow_two]

/-- In the paper's block size `s = k^2`, a single block has capacity
`k^4`. -/
theorem blockEntries_card_le_paper_side {q k : ℕ}
    (A : _root_.Matrix (Fin (q * k ^ 2)) (Fin (q * k ^ 2)) Bool)
    (I J : Fin q) :
    (blockEntries A I J).card ≤ k ^ 4 := by
  simpa [pow_mul, Nat.pow_mul, pow_two, pow_succ, Nat.mul_assoc] using
    (blockEntries_card_le_side_square A I J)

/-- Entries whose containing block lies in a prescribed block set are bounded
by a uniform per-block capacity times the number of blocks. -/
theorem entriesInBlocks_card_le {q s capacity : ℕ} (hs : 0 < s)
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool)
    (Blocks : Finset (Fin q × Fin q))
    (hcap : ∀ b ∈ Blocks, (blockEntries A b.1 b.2).card ≤ capacity) :
    ((oneEntries A).filter fun p => entryBlockIndex p ∈ Blocks).card ≤
      capacity * Blocks.card := by
  classical
  let E := (oneEntries A).filter fun p => entryBlockIndex p ∈ Blocks
  have hfiber : ∀ b ∈ E.image entryBlockIndex,
      (E.filter fun p => entryBlockIndex p = b).card ≤ capacity := by
    intro b hb
    have hbBlocks : b ∈ Blocks := by
      rcases Finset.mem_image.mp hb with ⟨p, hp, rfl⟩
      exact (by
        simpa [E] using hp : p ∈ oneEntries A ∧ entryBlockIndex p ∈ Blocks).2
    refine le_trans (Finset.card_le_card ?_) (hcap b hbBlocks)
    intro p hp
    have hp' : p ∈ E ∧ entryBlockIndex p = b := by
      simpa using hp
    have hpE : p ∈ oneEntries A ∧ entryBlockIndex p ∈ Blocks := by
      simpa [E] using hp'.1
    have htrue : A p.1 p.2 = true := (mem_oneEntries_iff A p).mp hpE.1
    have hrowIndex : blockIndex q s p.1 = b.1 := by
      simpa [entryBlockIndex] using congrArg Prod.fst hp'.2
    have hcolIndex : blockIndex q s p.2 = b.2 := by
      simpa [entryBlockIndex] using congrArg Prod.snd hp'.2
    have hrow : p.1 ∈ blockRows q s b.1 := by
      simpa [hrowIndex] using blockIndex_mem_blockRows (q := q) (s := s) hs p.1
    have hcol : p.2 ∈ blockCols q s b.2 := by
      simpa [hcolIndex] using blockIndex_mem_blockCols (q := q) (s := s) hs p.2
    simp [blockEntries, hrow, hcol, htrue]
  calc
    E.card ≤ capacity * (E.image entryBlockIndex).card :=
      Finset.card_le_mul_card_image (s := E) (f := entryBlockIndex)
        (n := capacity) hfiber
    _ ≤ capacity * Blocks.card := by
      refine Nat.mul_le_mul_left _ (Finset.card_le_card ?_)
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨p, hp, rfl⟩
      exact (by
        simpa [E] using hp : p ∈ oneEntries A ∧ entryBlockIndex p ∈ Blocks).2

/-- Every true entry is charged to a wide block, a tall block, or a nonempty
block that is neither wide nor tall. -/
theorem oneEntries_card_le_block_classification {q s k : ℕ} (hs : 0 < s)
    (hk : 0 < k)
    (A : _root_.Matrix (Fin (q * s)) (Fin (q * s)) Bool) :
    (oneEntries A).card ≤
      s ^ 2 * (wideBlocks A k).card +
        s ^ 2 * (tallBlocks A k).card +
          (k - 1) ^ 2 * (nonemptyNarrowBlocks A k).card := by
  classical
  let W := (oneEntries A).filter fun p => entryBlockIndex p ∈ wideBlocks A k
  let T := (oneEntries A).filter fun p => entryBlockIndex p ∈ tallBlocks A k
  let N := (oneEntries A).filter fun p => entryBlockIndex p ∈ nonemptyNarrowBlocks A k
  have hcover : oneEntries A ⊆ (W ∪ T) ∪ N := by
    intro p hp
    have htrue : A p.1 p.2 = true := (mem_oneEntries_iff A p).mp hp
    let b := entryBlockIndex p
    have hrow : p.1 ∈ blockRows q s b.1 := by
      simpa [b, entryBlockIndex] using blockIndex_mem_blockRows (q := q) (s := s) hs p.1
    have hcol : p.2 ∈ blockCols q s b.2 := by
      simpa [b, entryBlockIndex] using blockIndex_mem_blockCols (q := q) (s := s) hs p.2
    have hnonempty : BlockNonempty A b.1 b.2 :=
      ⟨p.1, hrow, p.2, hcol, htrue⟩
    by_cases hwide : BlockWide A k b.1 b.2
    · simp [W, b, wideBlocks, hp, hwide]
    · by_cases htall : BlockTall A k b.1 b.2
      · simp [T, b, tallBlocks, hp, htall]
      · simp [N, b, nonemptyNarrowBlocks, hp, hnonempty, hwide, htall]
  have hW : W.card ≤ s ^ 2 * (wideBlocks A k).card :=
    entriesInBlocks_card_le hs A (wideBlocks A k) (by
      intro b _
      exact blockEntries_card_le_side_square A b.1 b.2)
  have hT : T.card ≤ s ^ 2 * (tallBlocks A k).card :=
    entriesInBlocks_card_le hs A (tallBlocks A k) (by
      intro b _
      exact blockEntries_card_le_side_square A b.1 b.2)
  have hN : N.card ≤ (k - 1) ^ 2 * (nonemptyNarrowBlocks A k).card :=
    entriesInBlocks_card_le hs A (nonemptyNarrowBlocks A k) (by
      intro b hb
      have hb' : BlockNonempty A b.1 b.2 ∧ ¬ BlockWide A k b.1 b.2 ∧
          ¬ BlockTall A k b.1 b.2 := by
        simpa [nonemptyNarrowBlocks] using hb
      exact blockEntries_card_le_of_not_wide_not_tall hk
        A b.1 b.2 hb'.2.1 hb'.2.2)
  calc
    (oneEntries A).card ≤ ((W ∪ T) ∪ N).card := Finset.card_le_card hcover
    _ ≤ (W ∪ T).card + N.card := Finset.card_union_le (W ∪ T) N
    _ ≤ (W.card + T.card) + N.card := Nat.add_le_add_right (Finset.card_union_le W T) _
    _ ≤ (s ^ 2 * (wideBlocks A k).card + s ^ 2 * (tallBlocks A k).card) +
          (k - 1) ^ 2 * (nonemptyNarrowBlocks A k).card :=
      Nat.add_le_add (Nat.add_le_add hW hT) hN
    _ = s ^ 2 * (wideBlocks A k).card +
        s ^ 2 * (tallBlocks A k).card +
          (k - 1) ^ 2 * (nonemptyNarrowBlocks A k).card := by ring

/-- Marcus--Tardos Lemma 7: the block recursion for the Füredi--Hajnal
extremal function. -/
theorem furediHajnalRecursion : FurediHajnalRecursion := by
  intro k q P hk hP
  rcases hP with ⟨π, hπ⟩
  have hP_eq : P = permutationMatrix π := by
    ext i j
    exact hπ i j
  subst P
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  have hs : 0 < k ^ 2 := pow_pos hkpos 2
  have hks : k ≤ k ^ 2 := by
    calc
      k = k * 1 := by ring
      _ ≤ k * k := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hkpos)
      _ = k ^ 2 := by ring
  obtain ⟨A, hA, hcard⟩ :=
    exists_forbiddenExtremal_eq (n := q * k ^ 2) hkpos π
  let C := Nat.choose (k ^ 2) k
  have hclass :
      (oneEntries A).card ≤
        (k ^ 2) ^ 2 * (wideBlocks A k).card +
          (k ^ 2) ^ 2 * (tallBlocks A k).card +
            (k - 1) ^ 2 * (nonemptyNarrowBlocks A k).card := by
    simpa using oneEntries_card_le_block_classification
      (q := q) (s := k ^ 2) (k := k) hs hkpos A
  have hwide :
      (wideBlocks A k).card ≤ q * (k * C) := by
    simpa [C] using wideBlocks_card_le hkpos π A hks hA
  have htall :
      (tallBlocks A k).card ≤ q * (k * C) := by
    simpa [C] using tallBlocks_card_le hkpos π A hks hA
  have hnarrow :
      (nonemptyNarrowBlocks A k).card ≤
        forbiddenExtremal (permutationMatrix π) q := by
    exact nonemptyNarrowBlocks_card_le_forbiddenExtremal π A hA
  calc
    forbiddenExtremal (permutationMatrix π) (q * k ^ 2)
        = (oneEntries A).card := hcard.symm
    _ ≤ (k ^ 2) ^ 2 * (wideBlocks A k).card +
          (k ^ 2) ^ 2 * (tallBlocks A k).card +
            (k - 1) ^ 2 * (nonemptyNarrowBlocks A k).card := hclass
    _ ≤ (k ^ 2) ^ 2 * (q * (k * C)) +
          (k ^ 2) ^ 2 * (q * (k * C)) +
            (k - 1) ^ 2 * forbiddenExtremal (permutationMatrix π) q := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.mul_le_mul_left _ hwide)
          (Nat.mul_le_mul_left _ htall))
        (Nat.mul_le_mul_left _ hnarrow)
    _ = (k - 1) ^ 2 * forbiddenExtremal (permutationMatrix π) q +
          2 * k ^ 3 * C * (q * k ^ 2) := by ring
    _ = (k - 1) ^ 2 * forbiddenExtremal (permutationMatrix π) q +
          2 * k ^ 3 * Nat.choose (k ^ 2) k * (q * k ^ 2) := by simp [C]

theorem furediHajnal_polynomial_factor_le {k : ℕ} (hk : 2 ≤ k) :
    (k - 1) ^ 2 + k + 1 ≤ k ^ 2 := by
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  have hsub : 2 + t - 1 = t + 1 := by omega
  rw [hsub]
  calc
    (t + 1) ^ 2 + (2 + t) + 1 = t ^ 2 + 3 * t + 4 := by ring
    _ ≤ t ^ 2 + 4 * t + 4 := by omega
    _ = (2 + t) ^ 2 := by ring

theorem furediHajnal_base_coefficient_le {k : ℕ} (hk : 2 ≤ k) :
    k ^ 2 ≤ 2 * k ^ 4 * Nat.choose (k ^ 2) k := by
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  have hs : 0 < k ^ 2 := pow_pos hkpos 2
  have hks : k ≤ k ^ 2 := by
    calc
      k = k * 1 := by ring
      _ ≤ k * k := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hkpos)
      _ = k ^ 2 := by ring
  have hCpos : 0 < Nat.choose (k ^ 2) k := Nat.choose_pos hks
  have hC : 1 ≤ Nat.choose (k ^ 2) k := Nat.succ_le_of_lt hCpos
  have hs1 : 1 ≤ k ^ 2 := Nat.succ_le_of_lt hs
  calc
    k ^ 2 = k ^ 2 * 1 := by ring
    _ ≤ k ^ 2 * k ^ 2 := Nat.mul_le_mul_left _ hs1
    _ = k ^ 4 := by ring
    _ = 1 * k ^ 4 := by ring
    _ ≤ (2 * Nat.choose (k ^ 2) k) * k ^ 4 := by
      exact Nat.mul_le_mul_right _ (by
        calc
          1 ≤ Nat.choose (k ^ 2) k := hC
          _ ≤ 2 * Nat.choose (k ^ 2) k := by
            exact Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
    _ = 2 * k ^ 4 * Nat.choose (k ^ 2) k := by ring

/-- Marcus--Tardos Theorem 8 for a concrete permutation matrix. -/
theorem furediHajnalExplicitBound_permutation {k : ℕ}
    (π : Equiv.Perm (Fin k)) (hk : 2 ≤ k) :
    ∀ n, forbiddenExtremal (permutationMatrix π) n ≤
      2 * k ^ 4 * Nat.choose (k ^ 2) k * n := by
  classical
  let C := Nat.choose (k ^ 2) k
  let B := 2 * k ^ 4 * C
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  have hs : 0 < k ^ 2 := pow_pos hkpos 2
  have hks : k ≤ k ^ 2 := by
    calc
      k = k * 1 := by ring
      _ ≤ k * k := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hkpos)
      _ = k ^ 2 := by ring
  have hCpos : 0 < C := by
    simpa [C] using Nat.choose_pos hks
  have hC : 1 ≤ C := Nat.succ_le_of_lt hCpos
  have hk2gt1 : 1 < k ^ 2 := by
    calc
      1 < 2 := by decide
      _ ≤ k := hk
      _ ≤ k ^ 2 := hks
  have hpoly : (k - 1) ^ 2 + k + 1 ≤ k ^ 2 :=
    furediHajnal_polynomial_factor_le hk
  have hpoly' : (k - 1) ^ 2 + k ≤ k ^ 2 :=
    le_trans (Nat.le_add_right _ _) hpoly
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hsmall : n ≤ k ^ 2
      · have hsquare : forbiddenExtremal (permutationMatrix π) n ≤ n * n :=
          forbiddenExtremal_le_square (permutationMatrix π)
        have hnB : n * n ≤ B * n := by
          calc
            n * n ≤ k ^ 2 * n := Nat.mul_le_mul_right n hsmall
            _ ≤ B * n := Nat.mul_le_mul_right n (by
              simpa [B, C] using furediHajnal_base_coefficient_le hk)
        exact le_trans hsquare (by simpa [B, C] using hnB)
      · have hn_gt : k ^ 2 < n := Nat.lt_of_not_ge hsmall
        let q := n / k ^ 2
        let n0 := q * k ^ 2
        have hnpos : 0 < n := lt_trans hs hn_gt
        have hq_lt : q < n := Nat.div_lt_self hnpos hk2gt1
        have hqpos : 0 < q := Nat.div_pos (le_of_lt hn_gt) hs
        have hn0pos : 0 < n0 := Nat.mul_pos hqpos hs
        have hn0le : n0 ≤ n := by
          simpa [n0, q] using Nat.div_mul_le_self n (k ^ 2)
        have hrec :
            forbiddenExtremal (permutationMatrix π) n0 ≤
              (k - 1) ^ 2 * forbiddenExtremal (permutationMatrix π) q +
                2 * k ^ 3 * C * n0 := by
          simpa [n0, C] using
            furediHajnalRecursion (P := permutationMatrix π) (k := k) (q := q)
              hk (isPermutationMatrix_permutationMatrix π)
        have hiq :
            forbiddenExtremal (permutationMatrix π) q ≤ B * q := ih q hq_lt
        by_cases hrem : n % k ^ 2 = 0
        · have hn_eq : n = n0 := by
            calc
              n = k ^ 2 * (n / k ^ 2) + n % k ^ 2 :=
                (Nat.div_add_mod n (k ^ 2)).symm
              _ = q * k ^ 2 := by simp [q, hrem, Nat.mul_comm]
          rw [hn_eq]
          calc
            forbiddenExtremal (permutationMatrix π) n0 ≤
                (k - 1) ^ 2 * forbiddenExtremal (permutationMatrix π) q +
                  2 * k ^ 3 * C * n0 := hrec
            _ ≤ (k - 1) ^ 2 * (B * q) + 2 * k ^ 3 * C * n0 := by
              exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hiq) _
            _ = 2 * k ^ 4 * C * q * ((k - 1) ^ 2 + k) := by
              simp [B, n0]
              ring
            _ ≤ 2 * k ^ 4 * C * q * (k ^ 2) := by
              exact Nat.mul_le_mul_left _ hpoly'
            _ = B * n0 := by
              simp [B, n0]
              ring
        · have hdecomp : n0 + n % k ^ 2 = n := by
            calc
              n0 + n % k ^ 2 = k ^ 2 * (n / k ^ 2) + n % k ^ 2 := by
                simp [n0, q, Nat.mul_comm]
              _ = n := Nat.div_add_mod n (k ^ 2)
          have hmodpos : 0 < n % k ^ 2 := Nat.pos_of_ne_zero hrem
          have hn0lt : n0 < n := by
            exact lt_of_lt_of_eq (Nat.lt_add_of_pos_right hmodpos) hdecomp
          have hdiff_eq : n - n0 = n % k ^ 2 := by
            calc
              n - n0 = (n0 + n % k ^ 2) - n0 := by rw [hdecomp]
              _ = n % k ^ 2 := Nat.add_sub_cancel_left _ _
          have hdiff_le : n - n0 ≤ k ^ 2 := by
            rw [hdiff_eq]
            exact le_of_lt (Nat.mod_lt n hs)
          have hcrop :
              forbiddenExtremal (permutationMatrix π) n ≤
                forbiddenExtremal (permutationMatrix π) n0 + 2 * (n - n0) * n :=
            forbiddenExtremal_le_crop_add_boundary π hkpos hn0pos hn0le hn0lt
          have hmain :
              (k - 1) ^ 2 * (B * q) + 2 * k ^ 3 * C * n0 ≤
                2 * k ^ 2 * C * ((k - 1) ^ 2 + k) * n := by
            calc
              (k - 1) ^ 2 * (B * q) + 2 * k ^ 3 * C * n0 =
                  2 * k ^ 2 * C * ((k - 1) ^ 2 + k) * n0 := by
                simp [B, n0]
                ring
              _ ≤ 2 * k ^ 2 * C * ((k - 1) ^ 2 + k) * n := by
                exact Nat.mul_le_mul_left _ hn0le
          have hboundary :
              2 * (n - n0) * n ≤ 2 * k ^ 2 * C * n := by
            calc
              2 * (n - n0) * n ≤ 2 * k ^ 2 * n := by
                exact Nat.mul_le_mul_right n (Nat.mul_le_mul_left 2 hdiff_le)
              _ ≤ 2 * k ^ 2 * C * n := by
                exact Nat.mul_le_mul_right n (by
                  calc
                    2 * k ^ 2 = 2 * k ^ 2 * 1 := by ring
                    _ ≤ 2 * k ^ 2 * C := Nat.mul_le_mul_left _ hC)
          calc
            forbiddenExtremal (permutationMatrix π) n ≤
                forbiddenExtremal (permutationMatrix π) n0 + 2 * (n - n0) * n := hcrop
            _ ≤ ((k - 1) ^ 2 * forbiddenExtremal (permutationMatrix π) q +
                  2 * k ^ 3 * C * n0) + 2 * (n - n0) * n := by
              exact Nat.add_le_add_right hrec _
            _ ≤ ((k - 1) ^ 2 * (B * q) + 2 * k ^ 3 * C * n0) +
                  2 * (n - n0) * n := by
              exact Nat.add_le_add_right
                (Nat.add_le_add_right (Nat.mul_le_mul_left _ hiq) _) _
            _ ≤ 2 * k ^ 2 * C * ((k - 1) ^ 2 + k) * n + 2 * k ^ 2 * C * n :=
              Nat.add_le_add hmain hboundary
            _ = 2 * k ^ 2 * C * ((k - 1) ^ 2 + k + 1) * n := by ring_nf
            _ ≤ 2 * k ^ 2 * C * (k ^ 2) * n := by
              exact Nat.mul_le_mul_right n (Nat.mul_le_mul_left (2 * k ^ 2 * C) hpoly)
            _ = B * n := by
              change 2 * k ^ 2 * C * (k ^ 2) * n = (2 * k ^ 4 * C) * n
              ring

/-- Marcus--Tardos Theorem 8: the explicit linear Füredi--Hajnal bound. -/
theorem furediHajnalExplicitBound : FurediHajnalExplicitBound := by
  intro k n P hk hP
  rcases hP with ⟨π, hπ⟩
  have hP_eq : P = permutationMatrix π := by
    ext i j
    exact hπ i j
  subst P
  exact furediHajnalExplicitBound_permutation π hk n

/-- The qualitative Füredi--Hajnal theorem, i.e. Theorem 1 of
Marcus--Tardos, obtained from the explicit Section 2 bound. -/
theorem furediHajnalTheorem : FurediHajnalTheorem :=
  furediHajnalTheorem_of_explicitBound furediHajnalExplicitBound

/-- A number `c` is a Marcus-Tardos constant for grid size `t` if density
`c * max n m` forces a `t`-grid minor in every positive-size finite Boolean
matrix.

The explicit `0 < max n m` hypothesis avoids the degenerate `0 × 0` case,
where `c * max n m ≤ 0` is true for every `c` but no positive grid division can
exist. -/
def IsMarcusTardosConstant (t c : ℕ) : Prop :=
  ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool),
    0 < max n m → c * max n m ≤ (oneEntries M).card → HasGridMinor M t

/-- Marcus--Tardos constants are upward closed. -/
theorem IsMarcusTardosConstant.mono {t c C : ℕ}
    (h : IsMarcusTardosConstant t c) (hc : c ≤ C) :
    IsMarcusTardosConstant t C := by
  intro n m M hpos hden
  exact h M hpos (le_trans (Nat.mul_le_mul_right (max n m) hc) hden)

/-- The Marcus-Tardos theorem in the form needed for the twin-width grid
theorem. -/
def MarcusTardosTheorem : Prop :=
  ∀ t : ℕ, ∃ c : ℕ, IsMarcusTardosConstant t c

/-- The `t = 0` case is immediate from the vacuous grid-minor convention. -/
theorem isMarcusTardosConstant_zero (c : ℕ) :
    IsMarcusTardosConstant 0 c := by
  intro n m M _ _
  exact hasGridMinor_zero M

/-- The all-false `1 × 1` matrix has no positive grid minor. -/
theorem not_hasGridMinor_zeroBoolMatrix_one_of_pos {t : ℕ} (ht : 0 < t) :
    ¬ HasGridMinor (zeroBoolMatrix 1 1) t := by
  intro hgrid
  rcases hgrid with ht0 | hgrid
  · omega
  · rcases hgrid with ⟨R, C, hcell⟩
    let i : Fin t := ⟨0, ht⟩
    let j : Fin t := ⟨0, ht⟩
    rcases hcell i j with ⟨r, _hr, c, _hc, htrue⟩
    simp [zeroBoolMatrix] at htrue

/-- A Marcus--Tardos constant for a positive grid size is positive. -/
theorem IsMarcusTardosConstant.pos {t c : ℕ}
    (hMT : IsMarcusTardosConstant t c) (ht : 0 < t) : 0 < c := by
  by_contra hc
  have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
  have hden : c * max 1 1 ≤ (oneEntries (zeroBoolMatrix 1 1)).card := by
    simp [hc0, oneEntries, zeroBoolMatrix]
  exact not_hasGridMinor_zeroBoolMatrix_one_of_pos ht
    (hMT (zeroBoolMatrix 1 1) (by decide) hden)

/-- The `t = 0` instance of Marcus-Tardos. -/
theorem marcus_tardos_zero : ∃ c : ℕ, IsMarcusTardosConstant 0 c :=
  ⟨0, isMarcusTardosConstant_zero 0⟩

/-- A one-entry witness gives the `t = 1` grid minor.  This is the local base
case used by any full proof of Marcus-Tardos. -/
theorem hasGridMinor_one_of_density_one {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (h : 1 ≤ (oneEntries M).card) :
    HasGridMinor M 1 := by
  exact hasGridMinor_one_of_oneEntries_nonempty M (Finset.card_pos.mp h)

/-- Density `1 * max n m` already forces a `1`-grid minor. -/
theorem isMarcusTardosConstant_one : IsMarcusTardosConstant 1 1 := by
  intro n m M hpos hden
  have hmax : 1 ≤ max n m := Nat.succ_le_of_lt hpos
  have hone : 1 ≤ (oneEntries M).card := by
    calc
      1 ≤ 1 * max n m := by simpa using hmax
      _ ≤ (oneEntries M).card := hden
  exact hasGridMinor_one_of_density_one M hone

/-- The full Marcus-Tardos theorem can be used through this eliminator once its
proof is supplied. -/
theorem marcus_tardos_of_theorem
    (hMT : MarcusTardosTheorem) (t : ℕ) :
    ∃ c : ℕ, IsMarcusTardosConstant t c :=
  hMT t

/-! ## Grid-pattern form of Marcus--Tardos -/

/-- The permutation pattern whose `t × t` block division has one `true` entry
in every block.  Under the equivalence `Fin t × Fin t ≃ Fin (t*t)`, it swaps
the two coordinates. -/
def gridPermutation (t : ℕ) : Equiv.Perm (Fin (t * t)) :=
  ((finProdFinEquiv : Fin t × Fin t ≃ Fin (t * t)).symm.trans
      (Equiv.prodComm (Fin t) (Fin t))).trans
    (finProdFinEquiv : Fin t × Fin t ≃ Fin (t * t))

/-- The grid permutation pattern is a permutation matrix. -/
theorem isPermutationMatrix_gridPermutation (t : ℕ) :
    IsPermutationMatrix (permutationMatrix (gridPermutation t)) :=
  isPermutationMatrix_permutationMatrix (gridPermutation t)

/-! ### Extending selected grid rows and columns to divisions -/

/-- The row/column index in `Fin (t*t)` corresponding to the grid coordinate
`(i,j)`.  The equivalence `finProdFinEquiv` orders these coordinates by
consecutive row blocks. -/
def gridIndex (t : ℕ) (i j : Fin t) : Fin (t * t) :=
  (finProdFinEquiv : Fin t × Fin t ≃ Fin (t * t)) (i, j)

@[simp] theorem gridIndex_val (t : ℕ) (i j : Fin t) :
    (gridIndex t i j : ℕ) = j.1 + t * i.1 := by
  rfl

@[simp] theorem gridPermutation_gridIndex (t : ℕ) (i j : Fin t) :
    gridPermutation t (gridIndex t i j) = gridIndex t j i := by
  simp [gridPermutation, gridIndex]

theorem gridIndex_le_iff {t : ℕ} {i j a b : Fin t} :
    gridIndex t i j ≤ gridIndex t a b ↔ i < a ∨ i = a ∧ j ≤ b := by
  rw [Fin.le_iff_val_le_val]
  simp [gridIndex]
  have htpos : 0 < t := lt_of_le_of_lt (Nat.zero_le j.1) j.2
  have hdiv_left (x y : Fin t) : (y.1 + t * x.1) / t = x.1 := by
    calc
      (y.1 + t * x.1) / t = y.1 / t + x.1 :=
        Nat.add_mul_div_left y.1 x.1 htpos
      _ = 0 + x.1 := by rw [Nat.div_eq_of_lt y.2]
      _ = x.1 := by simp
  constructor
  · intro h
    have hia_le : i ≤ a := by
      rw [Fin.le_iff_val_le_val]
      have hdiv := Nat.div_le_div_right (c := t) h
      simpa [hdiv_left] using hdiv
    by_cases hia : i = a
    · right
      refine ⟨hia, ?_⟩
      subst a
      rw [Fin.le_iff_val_le_val]
      omega
    · left
      exact lt_of_le_of_ne hia_le hia
  · rintro (hia | ⟨rfl, hjb⟩)
    · rw [Fin.lt_def] at hia
      have hj_lt : j.1 < t := j.2
      exact le_of_lt <| calc
        j.1 + t * i.1 < t + t * i.1 := Nat.add_lt_add_right hj_lt _
        _ = t * (i.1 + 1) := by ring
        _ ≤ t * a.1 := Nat.mul_le_mul_left t (Nat.succ_le_of_lt hia)
        _ ≤ b.1 + t * a.1 := Nat.le_add_left _ _
    · rw [Fin.le_iff_val_le_val] at hjb
      omega

theorem gridIndex_lt_iff {t : ℕ} {i j a b : Fin t} :
    gridIndex t i j < gridIndex t a b ↔ i < a ∨ i = a ∧ j < b := by
  rw [lt_iff_le_not_ge, gridIndex_le_iff, gridIndex_le_iff]
  constructor
  · rintro ⟨hleft, hnot⟩
    rcases hleft with hia | ⟨rfl, hjb⟩
    · exact Or.inl hia
    · right
      refine ⟨rfl, lt_of_le_of_ne hjb ?_⟩
      intro hbj
      exact hnot (Or.inr ⟨rfl, le_of_eq hbj.symm⟩)
  · rintro (hia | ⟨rfl, hjb⟩)
    · refine ⟨Or.inl hia, ?_⟩
      rintro (hai | ⟨heq, _⟩)
      · exact not_lt_of_ge hia.le hai
      · exact (ne_of_lt hia) heq.symm
    · refine ⟨Or.inr ⟨rfl, hjb.le⟩, ?_⟩
      rintro (hji | ⟨_, hbj⟩)
      · exact (not_lt_of_ge le_rfl) hji
      · exact not_lt_of_ge hbj hjb

/-- Count the number of selected starts not exceeding a row or column.  The
associated division index is this count minus one, with the initial segment
before the first start assigned to block `0`. -/
noncomputable def startDivisionIndex {n t : ℕ} (ht : 0 < t)
    (start : Fin t → Fin n) (x : Fin n) : Fin t :=
  ⟨((Finset.univ.filter fun i : Fin t => start i ≤ x).card - 1), by
    have hcard :
        (Finset.univ.filter fun i : Fin t => start i ≤ x).card ≤ t := by
      calc
        (Finset.univ.filter fun i : Fin t => start i ≤ x).card ≤
            (Finset.univ : Finset (Fin t)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = t := by simp
    omega⟩

theorem startDivisionIndex_mono {n t : ℕ} (ht : 0 < t)
    (start : Fin t → Fin n) :
    ∀ ⦃a b : Fin n⦄, a ≤ b →
      startDivisionIndex ht start a ≤ startDivisionIndex ht start b := by
  intro a b hab
  rw [Fin.le_iff_val_le_val]
  have hsubset :
      (Finset.univ.filter fun i : Fin t => start i ≤ a) ⊆
        (Finset.univ.filter fun i : Fin t => start i ≤ b) := by
    intro i hi
    have hia : start i ≤ a := by simpa using hi
    exact by
      simp [le_trans hia hab]
  exact Nat.sub_le_sub_right (Finset.card_le_card hsubset) 1

theorem starts_filter_eq_Iic {n t : ℕ} {start : Fin t → Fin n}
    (hstart : StrictMono start) (j : Fin t) :
    (Finset.univ.filter fun i : Fin t => start i ≤ start j) = Finset.Iic j := by
  ext i
  constructor
  · intro hi
    have hle : start i ≤ start j := by simpa using hi
    have hij : i ≤ j := by
      by_contra hnot
      have hji : j < i := lt_of_not_ge hnot
      exact (not_lt_of_ge hle) (hstart hji)
    simpa using hij
  · intro hi
    have hij : i ≤ j := by simpa using hi
    simp [hstart.monotone hij]

@[simp] theorem startDivisionIndex_start {n t : ℕ} (ht : 0 < t)
    {start : Fin t → Fin n} (hstart : StrictMono start) (j : Fin t) :
    startDivisionIndex ht start (start j) = j := by
  apply Fin.ext
  change ((Finset.univ.filter fun i : Fin t => start i ≤ start j).card - 1) = j.1
  rw [starts_filter_eq_Iic hstart j]
  simp

/-- A division generated by a strictly increasing sequence of starts.  The
first block also absorbs rows/columns before the first selected start. -/
noncomputable def divisionOfStarts {n t : ℕ} (ht : 0 < t)
    (start : Fin t → Fin n) (hstart : StrictMono start) : Division n t :=
  Division.ofMonotoneSurjective (startDivisionIndex ht start)
    (fun _ _ hab => startDivisionIndex_mono ht start hab)
    (fun j => ⟨start j, startDivisionIndex_start ht hstart j⟩)

@[simp] theorem mem_divisionOfStarts_part {n t : ℕ} (ht : 0 < t)
    {start : Fin t → Fin n} (hstart : StrictMono start)
    (j : Fin t) (x : Fin n) :
    x ∈ (divisionOfStarts ht start hstart).part j ↔
      startDivisionIndex ht start x = j := by
  simp [divisionOfStarts]

theorem start_mem_divisionOfStarts_part {n t : ℕ} (ht : 0 < t)
    {start : Fin t → Fin n} (hstart : StrictMono start) (j : Fin t) :
    start j ∈ (divisionOfStarts ht start hstart).part j := by
  rw [mem_divisionOfStarts_part]
  exact startDivisionIndex_start ht hstart j

theorem grid_row_starts_strictMono {t n : ℕ} (ht : 0 < t)
    (row : Fin (t * t) ↪o Fin n) :
    StrictMono (fun i : Fin t => row (gridIndex t i ⟨0, ht⟩)) := by
  intro i j hij
  exact row.strictMono ((gridIndex_lt_iff).mpr (Or.inl hij))

theorem grid_col_starts_strictMono {t n : ℕ} (ht : 0 < t)
    (col : Fin (t * t) ↪o Fin n) :
    StrictMono (fun j : Fin t => col (gridIndex t j ⟨0, ht⟩)) := by
  intro i j hij
  exact col.strictMono ((gridIndex_lt_iff).mpr (Or.inl hij))

theorem grid_row_selected_mem_part {t n : ℕ} (ht : 0 < t)
    (row : Fin (t * t) ↪o Fin n) (i j : Fin t) :
    row (gridIndex t i j) ∈
      (divisionOfStarts ht
        (fun a : Fin t => row (gridIndex t a ⟨0, ht⟩))
        (grid_row_starts_strictMono ht row)).part i := by
  have hfilter :
      (Finset.univ.filter fun a : Fin t =>
          row (gridIndex t a ⟨0, ht⟩) ≤ row (gridIndex t i j)) =
        Finset.Iic i := by
    ext a
    constructor
    · intro ha
      have hle : gridIndex t a ⟨0, ht⟩ ≤ gridIndex t i j :=
        row.le_iff_le.mp (by simpa using ha)
      rcases (gridIndex_le_iff.mp hle) with hai | ⟨hai, _⟩
      · simpa using hai.le
      · simp [hai]
    · intro ha
      have hai : a ≤ i := by simpa using ha
      have hle : gridIndex t a ⟨0, ht⟩ ≤ gridIndex t i j := by
        rcases lt_or_eq_of_le hai with hai' | rfl
        · exact (gridIndex_le_iff).mpr (Or.inl hai')
        · exact (gridIndex_le_iff).mpr
            (Or.inr ⟨rfl, Fin.le_iff_val_le_val.mpr (Nat.zero_le _)⟩)
      simpa using row.monotone hle
  rw [mem_divisionOfStarts_part]
  apply Fin.ext
  change ((Finset.univ.filter fun a : Fin t =>
    row (gridIndex t a ⟨0, ht⟩) ≤ row (gridIndex t i j)).card - 1) = i.1
  rw [hfilter]
  simp

theorem grid_col_selected_mem_part {t n : ℕ} (ht : 0 < t)
    (col : Fin (t * t) ↪o Fin n) (i j : Fin t) :
    col (gridIndex t j i) ∈
      (divisionOfStarts ht
        (fun b : Fin t => col (gridIndex t b ⟨0, ht⟩))
        (grid_col_starts_strictMono ht col)).part j := by
  simpa using grid_row_selected_mem_part (n := n) ht col j i

/-- Containment of the grid permutation pattern produces the division-based
grid minor used elsewhere in this development. -/
theorem hasGridMinor_of_contains_gridPermutation {t n m : ℕ}
    (ht : 0 < t)
    (A : _root_.Matrix (Fin n) (Fin m) Bool)
    (h : ContainsPattern A (permutationMatrix (gridPermutation t))) :
    HasGridMinor A t := by
  classical
  rcases h with ⟨row, col, hcontains⟩
  refine Or.inr ?_
  let R : Division n t :=
    divisionOfStarts ht
      (fun i : Fin t => row (gridIndex t i ⟨0, ht⟩))
      (grid_row_starts_strictMono ht row)
  let C : Division m t :=
    divisionOfStarts ht
      (fun j : Fin t => col (gridIndex t j ⟨0, ht⟩))
      (grid_col_starts_strictMono ht col)
  refine ⟨R, C, ?_⟩
  intro i j
  refine ⟨row (gridIndex t i j), ?_, col (gridIndex t j i), ?_, ?_⟩
  · exact grid_row_selected_mem_part ht row i j
  · exact grid_col_selected_mem_part ht col i j
  · have hpat :
        permutationMatrix (gridPermutation t) (gridIndex t i j) (gridIndex t j i) = true := by
      simp [permutationMatrix]
    simpa [gridPermutation_gridIndex] using hcontains (gridIndex t i j) (gridIndex t j i) hpat

/-- Pad a rectangular matrix to a square matrix of side `max n m`, filling the
new rows and columns with `false`. -/
def padToSquare {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool) :
    _root_.Matrix (Fin (max n m)) (Fin (max n m)) Bool :=
  fun r c =>
    if hr : r.1 < n then
      if hc : c.1 < m then
        M ⟨r.1, hr⟩ ⟨c.1, hc⟩
      else
        false
    else
      false

theorem padToSquare_eq_true_iff {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (r c : Fin (max n m)) :
    padToSquare M r c = true ↔
      ∃ (hr : r.1 < n) (hc : c.1 < m),
        M ⟨r.1, hr⟩ ⟨c.1, hc⟩ = true := by
  unfold padToSquare
  by_cases hr : r.1 < n
  · by_cases hc : c.1 < m
    · simp [hr, hc]
    · simp [hr, hc]
  · simp [hr]

@[simp] theorem padToSquare_castLE {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool) (r : Fin n) (c : Fin m) :
    padToSquare M (Fin.castLE (le_max_left n m) r)
      (Fin.castLE (le_max_right n m) c) = M r c := by
  simp [padToSquare]

theorem oneEntries_padToSquare {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool) :
    oneEntries (padToSquare M) =
      (oneEntries M).map
        ⟨fun p : Fin n × Fin m =>
          (Fin.castLE (le_max_left n m) p.1, Fin.castLE (le_max_right n m) p.2),
          by
            intro p q hpq
            apply Prod.ext
            · apply Fin.ext
              exact congrArg (fun x : Fin (max n m) × Fin (max n m) => (x.1 : Fin (max n m)).1) hpq
            · apply Fin.ext
              exact congrArg (fun x : Fin (max n m) × Fin (max n m) => (x.2 : Fin (max n m)).1) hpq⟩ := by
  classical
  let e : (Fin n × Fin m) ↪ (Fin (max n m) × Fin (max n m)) :=
    ⟨fun p => (Fin.castLE (le_max_left n m) p.1, Fin.castLE (le_max_right n m) p.2),
      by
        intro p q hpq
        apply Prod.ext
        · apply Fin.ext
          exact congrArg (fun x : Fin (max n m) × Fin (max n m) => (x.1 : Fin (max n m)).1) hpq
        · apply Fin.ext
          exact congrArg (fun x : Fin (max n m) × Fin (max n m) => (x.2 : Fin (max n m)).1) hpq⟩
  change oneEntries (padToSquare M) = (oneEntries M).map e
  ext p
  constructor
  · intro hp
    have hptrue : padToSquare M p.1 p.2 = true := (mem_oneEntries_iff (padToSquare M) p).mp hp
    rcases (padToSquare_eq_true_iff M p.1 p.2).mp hptrue with ⟨hr, hc, hM⟩
    refine Finset.mem_map.mpr ⟨(⟨p.1.1, hr⟩, ⟨p.2.1, hc⟩), ?_, ?_⟩
    · exact (mem_oneEntries_iff M _).mpr hM
    · apply Prod.ext <;> apply Fin.ext <;> rfl
  · intro hp
    rcases Finset.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact (mem_oneEntries_iff (padToSquare M) _).mpr (by
      change padToSquare M (Fin.castLE (le_max_left n m) q.1)
        (Fin.castLE (le_max_right n m) q.2) = true
      simpa using (mem_oneEntries_iff M q).mp hq)

@[simp] theorem oneEntries_padToSquare_card {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool) :
    (oneEntries (padToSquare M)).card = (oneEntries M).card := by
  rw [oneEntries_padToSquare]
  simp

theorem containsPattern_of_padToSquare_contains_gridPermutation {t n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (h : ContainsPattern (padToSquare M) (permutationMatrix (gridPermutation t))) :
    ContainsPattern M (permutationMatrix (gridPermutation t)) := by
  classical
  rcases h with ⟨row, col, hcontains⟩
  have hrow_inside : ∀ a : Fin (t * t), (row a).1 < n := by
    intro a
    have hpat :
        permutationMatrix (gridPermutation t) a (gridPermutation t a) = true := by
      simp [permutationMatrix]
    have htrue := hcontains a (gridPermutation t a) hpat
    rcases (padToSquare_eq_true_iff M (row a) (col (gridPermutation t a))).mp htrue
      with ⟨hr, _hc, _hM⟩
    exact hr
  have hcol_inside : ∀ b : Fin (t * t), (col b).1 < m := by
    intro b
    let a : Fin (t * t) := (gridPermutation t).symm b
    have hpat : permutationMatrix (gridPermutation t) a b = true := by
      simp [permutationMatrix, a]
    have htrue := hcontains a b hpat
    rcases (padToSquare_eq_true_iff M (row a) (col b)).mp htrue with ⟨_hr, hc, _hM⟩
    exact hc
  let row' : Fin (t * t) ↪o Fin n :=
    OrderEmbedding.ofStrictMono (fun a => ⟨(row a).1, hrow_inside a⟩) (by
      intro a b hab
      rw [Fin.lt_def]
      exact row.strictMono hab)
  let col' : Fin (t * t) ↪o Fin m :=
    OrderEmbedding.ofStrictMono (fun a => ⟨(col a).1, hcol_inside a⟩) (by
      intro a b hab
      rw [Fin.lt_def]
      exact col.strictMono hab)
  refine ⟨row', col', ?_⟩
  intro i j hij
  have htrue := hcontains i j hij
  rcases (padToSquare_eq_true_iff M (row i) (col j)).mp htrue with ⟨hr, hc, hM⟩
  simpa [row', col'] using hM

/-- The explicit Füredi--Hajnal constant attached to the grid permutation
pattern of order `t*t`.  We add one in the density theorem below to turn the
non-strict extremal upper bound into a strict contradiction. -/
def gridPatternFurediHajnalConstant (t : ℕ) : ℕ :=
  2 * (t * t) ^ 4 * Nat.choose ((t * t) ^ 2) (t * t)

theorem gridPattern_size_ge_two {t : ℕ} (ht : 2 ≤ t) : 2 ≤ t * t := by
  have htpos : 0 < t := lt_of_lt_of_le (by decide : 0 < 2) ht
  exact le_trans ht (by
    calc
      t = t * 1 := by ring
      _ ≤ t * t := Nat.mul_le_mul_left t (Nat.succ_le_of_lt htpos))

/-- Füredi--Hajnal, specialized to the grid permutation pattern. -/
theorem oneEntries_card_le_gridPatternFurediHajnalConstant {t n : ℕ}
    (ht : 2 ≤ t)
    (A : _root_.Matrix (Fin n) (Fin n) Bool)
    (hA : AvoidsPattern A (permutationMatrix (gridPermutation t))) :
    (oneEntries A).card ≤ gridPatternFurediHajnalConstant t * n := by
  calc
    (oneEntries A).card ≤
        forbiddenExtremal (permutationMatrix (gridPermutation t)) n :=
      oneEntries_card_le_forbiddenExtremal (gridPermutation t) A hA
    _ ≤ gridPatternFurediHajnalConstant t * n :=
      furediHajnalExplicitBound (permutationMatrix (gridPermutation t))
        (gridPattern_size_ge_two ht) (isPermutationMatrix_gridPermutation t)

/-- A positive square matrix with density above the Füredi--Hajnal bound
contains the grid permutation pattern.  This is the direct Section 2
Marcus--Tardos/Füredi--Hajnal proof specialized to the pattern used for grid
minors. -/
theorem contains_gridPermutation_of_dense_square {t n : ℕ}
    (ht : 2 ≤ t) (hn : 0 < n)
    (A : _root_.Matrix (Fin n) (Fin n) Bool)
    (hden : (gridPatternFurediHajnalConstant t + 1) * n ≤ (oneEntries A).card) :
    ContainsPattern A (permutationMatrix (gridPermutation t)) := by
  classical
  by_contra hcontains
  have havoid : AvoidsPattern A (permutationMatrix (gridPermutation t)) := hcontains
  have hupper :
      (oneEntries A).card ≤ gridPatternFurediHajnalConstant t * n :=
    oneEntries_card_le_gridPatternFurediHajnalConstant ht A havoid
  have hstrict :
      gridPatternFurediHajnalConstant t * n <
        (gridPatternFurediHajnalConstant t + 1) * n := by
    exact Nat.mul_lt_mul_of_pos_right
      (Nat.lt_succ_self (gridPatternFurediHajnalConstant t)) hn
  exact (not_le_of_gt (lt_of_lt_of_le hstrict hden)) hupper

/-- Positive-square grid form of Marcus--Tardos.  The theorem is parameterized
by the order-theoretic bridge from containment of the grid permutation pattern
to the division-based `HasGridMinor` predicate. -/
theorem hasGridMinor_of_dense_square
    (hgrid :
      ∀ {t n : ℕ} (A : _root_.Matrix (Fin n) (Fin n) Bool),
        ContainsPattern A (permutationMatrix (gridPermutation t)) → HasGridMinor A t)
    {t n : ℕ} (ht : 2 ≤ t) (hn : 0 < n)
    (A : _root_.Matrix (Fin n) (Fin n) Bool)
    (hden : (gridPatternFurediHajnalConstant t + 1) * n ≤ (oneEntries A).card) :
    HasGridMinor A t :=
  hgrid A (contains_gridPermutation_of_dense_square ht hn A hden)

/-- Positive-square grid form of Marcus--Tardos with the containment/grid-minor
bridge proved above. -/
theorem hasGridMinor_of_dense_square_explicit {t n : ℕ}
    (ht : 2 ≤ t) (hn : 0 < n)
    (A : _root_.Matrix (Fin n) (Fin n) Bool)
    (hden : (gridPatternFurediHajnalConstant t + 1) * n ≤ (oneEntries A).card) :
    HasGridMinor A t :=
  hasGridMinor_of_contains_gridPermutation (lt_of_lt_of_le (by decide : 0 < 2) ht) A
    (contains_gridPermutation_of_dense_square ht hn A hden)

/-- The explicit Marcus--Tardos constant obtained from the formalized
Füredi--Hajnal bound and the grid-permutation bridge. -/
theorem isMarcusTardosConstant_gridPattern {t : ℕ} (ht : 2 ≤ t) :
    IsMarcusTardosConstant t (gridPatternFurediHajnalConstant t + 1) := by
  intro n m M hpos hden
  have hpad_den :
      (gridPatternFurediHajnalConstant t + 1) * max n m ≤
        (oneEntries (padToSquare M)).card := by
    simpa using hden
  have hcontains :
      ContainsPattern (padToSquare M) (permutationMatrix (gridPermutation t)) :=
    contains_gridPermutation_of_dense_square ht hpos (padToSquare M) hpad_den
  exact hasGridMinor_of_contains_gridPermutation
    (lt_of_lt_of_le (by decide : 0 < 2) ht) M
    (containsPattern_of_padToSquare_contains_gridPermutation M hcontains)

/-- An explicit Marcus--Tardos constant for the finite rectangular grid-minor
statement.  The cases `0` and `1` are elementary; for `t ≥ 2` this uses the
Füredi--Hajnal constant of the `t × t` grid permutation pattern, plus one to
make the extremal contradiction strict. -/
def marcusTardosConstant (t : ℕ) : ℕ :=
  match t with
  | 0 => 0
  | Nat.succ 0 => 1
  | Nat.succ (Nat.succ s) => gridPatternFurediHajnalConstant (s + 2) + 1

/-- The explicit constant `marcusTardosConstant t` satisfies the
Marcus--Tardos density conclusion for grid size `t`.  This is the most useful
fully explicit interface for downstream bounds. -/
theorem isMarcusTardosConstant_marcusTardosConstant :
    ∀ t : ℕ, IsMarcusTardosConstant t (marcusTardosConstant t) := by
  intro t
  cases t with
  | zero =>
      exact isMarcusTardosConstant_zero 0
  | succ t =>
      cases t with
      | zero =>
          exact isMarcusTardosConstant_one
      | succ s =>
          exact isMarcusTardosConstant_gridPattern (t := s + 2) (by omega)

/-- Marcus--Tardos in the finite rectangular grid-minor form used by the
twin-width proof. -/
theorem marcusTardosTheorem : MarcusTardosTheorem := by
  intro t
  exact ⟨marcusTardosConstant t, isMarcusTardosConstant_marcusTardosConstant t⟩

/-- Direct existential interface for the main Marcus--Tardos statement. -/
theorem marcusTardos (t : ℕ) : ∃ c : ℕ, IsMarcusTardosConstant t c :=
  marcusTardosTheorem t

/-- Contract theorem for `MarcusTardosContract.marcus_tardos_grid_minor_density`.

For every grid order `t`, some constant `c` makes density `c * max n m` force a
`t`-grid minor in every positive-size finite Boolean matrix. -/
theorem marcus_tardos_grid_minor_density :
    ∀ t : ℕ, ∃ c : ℕ,
      ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool),
        0 < max n m →
          c * max n m ≤ (oneEntries M).card →
            HasGridMinor M t := by
  simpa [MarcusTardosTheorem, IsMarcusTardosConstant] using marcusTardosTheorem

end Matrix
end Lax2Proofs.TwinWidth
