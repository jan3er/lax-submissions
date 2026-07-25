import Lax5.Transductions
import Mathlib.ModelTheory.Graph

/-!
Back-and-forth systems and rank-bounded formula agreement.

An `EFSystem` over a colored graph is a budget-indexed family of
positions — finite lists of matched vertex pairs — that preserve the
atoms of the colored-graph language and admit one-point forward and
backward extensions at the cost of one budget level.  The agreement
theorem is the only formula induction of the Adler–Adler development:
a position at budget `j` transfers the truth of every formula of
quantifier rank at most `j` whose free variables are assigned along
the position's pairs.
-/

namespace Lax5Proofs.EFAgreement

open FirstOrder Lax5.Transductions

/-! ### Quantifier rank -/

/-- Quantifier rank of a bounded formula. -/
def qrank {L : Language} {α : Type*} : ∀ {m : ℕ}, L.BoundedFormula α m → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => max (qrank φ) (qrank ψ)
  | _, .all φ => qrank φ + 1

/-! ### EF systems over a colored graph -/

variable {n k : ℕ}

/-- The pairs of a position preserve the atoms of the colored-graph
language: adjacency, equality, and colors. -/
structure AtomPreserving (G : SimpleGraph (Fin n))
    (colors : Fin k → Set (Fin n)) (p : List (Fin n × Fin n)) : Prop where
  adj : ∀ {a b a' b'}, (a, b) ∈ p → (a', b') ∈ p → (G.Adj a a' ↔ G.Adj b b')
  eq : ∀ {a b a' b'}, (a, b) ∈ p → (a', b') ∈ p → (a = a' ↔ b = b')
  color : ∀ {a b} (i : Fin k), (a, b) ∈ p → (a ∈ colors i ↔ b ∈ colors i)

/-- A back-and-forth system: budget-indexed positions with atom
preservation and one-point extensions in both directions. -/
structure EFSystem (G : SimpleGraph (Fin n))
    (colors : Fin k → Set (Fin n)) where
  /-- The positions at each budget. -/
  F : ℕ → List (Fin n × Fin n) → Prop
  /-- Positions preserve atoms. -/
  atoms : ∀ {j p}, F j p → AtomPreserving G colors p
  /-- Forward extension. -/
  forth : ∀ {j p}, F (j + 1) p → ∀ x, ∃ y, F j ((x, y) :: p)
  /-- Backward extension. -/
  back : ∀ {j p}, F (j + 1) p → ∀ y, ∃ x, F j ((x, y) :: p)

/-! ### Semantics packaging -/

/-- Realization of a bounded formula of the colored-graph language over
a colored graph (the `RealizeIn` instance packaging, for bounded
formulas). -/
def RealizeB (G : SimpleGraph (Fin n)) (colors : Fin k → Set (Fin n))
    {α : Type*} {m : ℕ} (φ : (withColors Language.graph k).BoundedFormula α m)
    (v : α → Fin n) (xs : Fin m → Fin n) : Prop :=
  letI := G.structure
  letI := colorStructure colors
  φ.Realize v xs

/-- Every term of a relational language is a variable. -/
theorem term_eq_var {L : Language} [L.IsRelational] {β : Type*}
    (t : L.Term β) : ∃ b, t = .var b := by
  cases t with
  | var b => exact ⟨b, rfl⟩
  | func f _ => exact isEmptyElim f

/-- Atomic relations transfer along the pairs of an atom-preserving
position. -/
theorem relMap_transfer {G : SimpleGraph (Fin n)}
    {colors : Fin k → Set (Fin n)} {p : List (Fin n × Fin n)}
    (hp : AtomPreserving G colors p) :
    ∀ {l : ℕ} (R : (withColors Language.graph k).Relations l)
      (val val' : Fin l → Fin n), (∀ i, (val i, val' i) ∈ p) →
      (letI := G.structure; letI := colorStructure colors;
        (Language.Structure.RelMap R val ↔ Language.Structure.RelMap R val'))
  | 0, Sum.inl R, _, _, _ => nomatch R
  | 0, Sum.inr R, _, _, _ => nomatch R
  | 1, Sum.inl R, _, _, _ => nomatch R
  | 1, Sum.inr (.color i), val, val', h => hp.color i (h 0)
  | 2, Sum.inl R, val, val', h => by
    cases R
    exact hp.adj (h 0) (h 1)
  | 2, Sum.inr R, _, _, _ => nomatch R
  | l + 3, Sum.inl R, _, _, _ => nomatch R
  | l + 3, Sum.inr R, _, _, _ => nomatch R

/-! ### The agreement theorem -/

/-- Formula agreement along an EF system: a position at budget `j`
transfers the truth of every formula of quantifier rank at most `j`
whose free and bound variables are assigned along the position's
pairs. -/
theorem agreement {G : SimpleGraph (Fin n)} {colors : Fin k → Set (Fin n)}
    (S : EFSystem G colors) {α : Type*} {m : ℕ}
    (φ : (withColors Language.graph k).BoundedFormula α m) :
    ∀ {j : ℕ}, qrank φ ≤ j → ∀ {p}, S.F j p →
      ∀ {v w : α → Fin n} {xs ys : Fin m → Fin n},
        (∀ a, (v a, w a) ∈ p) → (∀ i, (xs i, ys i) ∈ p) →
        (RealizeB G colors φ v xs ↔ RealizeB G colors φ w ys) := by
  induction φ with
  | falsum =>
    intro j _ p hp v w xs ys hv hxs
    exact Iff.rfl
  | equal t₁ t₂ =>
    intro j _ p hp v w xs ys hv hxs
    letI := G.structure
    letI := colorStructure colors
    obtain ⟨b₁, rfl⟩ := term_eq_var t₁
    obtain ⟨b₂, rfl⟩ := term_eq_var t₂
    have hpair : ∀ b : α ⊕ Fin _,
        (Sum.elim v xs b, Sum.elim w ys b) ∈ p := by
      rintro (a | i)
      · exact hv a
      · exact hxs i
    unfold RealizeB
    simp only [Language.BoundedFormula.Realize, Language.Term.realize_var]
    exact (S.atoms hp).eq (hpair b₁) (hpair b₂)
  | rel R ts =>
    intro j _ p hp v w xs ys hv hxs
    letI := G.structure
    letI := colorStructure colors
    have hpair : ∀ b : α ⊕ Fin _,
        (Sum.elim v xs b, Sum.elim w ys b) ∈ p := by
      rintro (a | i)
      · exact hv a
      · exact hxs i
    unfold RealizeB
    simp only [Language.BoundedFormula.Realize]
    have hval : ∀ i, ((ts i).realize (Sum.elim v xs),
        (ts i).realize (Sum.elim w ys)) ∈ p := by
      intro i
      obtain ⟨b, hb⟩ := term_eq_var (ts i)
      rw [hb]
      simpa only [Language.Term.realize_var] using hpair b
    exact relMap_transfer (S.atoms hp) R _ _ hval
  | imp φ ψ ihφ ihψ =>
    intro j hq p hp v w xs ys hv hxs
    have hφ : qrank φ ≤ j := le_trans (le_max_left _ _) hq
    have hψ : qrank ψ ≤ j := le_trans (le_max_right _ _) hq
    unfold RealizeB
    simp only [Language.BoundedFormula.Realize]
    constructor
    · intro h h1
      exact (ihψ hψ hp hv hxs).mp (h ((ihφ hφ hp hv hxs).mpr h1))
    · intro h h1
      exact (ihψ hψ hp hv hxs).mpr (h ((ihφ hφ hp hv hxs).mp h1))
  | all φ ih =>
    intro j hq p hp v w xs ys hv hxs
    match j, hq with
    | j + 1, hq =>
      have hφ : qrank φ ≤ j := by
        have : qrank (φ.all) = qrank φ + 1 := rfl
        omega
      unfold RealizeB
      simp only [Language.BoundedFormula.Realize]
      constructor
      · intro h y
        obtain ⟨x, hx⟩ := S.back hp y
        have hpairs : ∀ i, ((Fin.snoc xs x : Fin _ → Fin n) i,
            (Fin.snoc ys y : Fin _ → Fin n) i) ∈ (x, y) :: p := by
          intro i
          refine Fin.lastCases ?_ (fun i' => ?_) i
          · simp only [Fin.snoc_last]
            exact List.mem_cons_self ..
          · simp only [Fin.snoc_castSucc]
            exact List.mem_cons_of_mem _ (hxs i')
        exact (ih hφ hx (fun a => List.mem_cons_of_mem _ (hv a)) hpairs).mp
          (h x)
      · intro h x
        obtain ⟨y, hy⟩ := S.forth hp x
        have hpairs : ∀ i, ((Fin.snoc xs x : Fin _ → Fin n) i,
            (Fin.snoc ys y : Fin _ → Fin n) i) ∈ (x, y) :: p := by
          intro i
          refine Fin.lastCases ?_ (fun i' => ?_) i
          · simp only [Fin.snoc_last]
            exact List.mem_cons_self ..
          · simp only [Fin.snoc_castSucc]
            exact List.mem_cons_of_mem _ (hxs i')
        exact (ih hφ hy (fun a => List.mem_cons_of_mem _ (hv a)) hpairs).mpr
          (h y)

/-- Agreement for formulas, phrased against the submission's
`RealizeIn`. -/
theorem realizeIn_agreement {G : SimpleGraph (Fin n)}
    {colors : Fin k → Set (Fin n)} (S : EFSystem G colors)
    {α : Type*} (φ : (withColors Language.graph k).Formula α) {j : ℕ}
    (hφ : qrank φ ≤ j) {p : List (Fin n × Fin n)} (hp : S.F j p)
    {v w : α → Fin n} (hv : ∀ a, (v a, w a) ∈ p) :
    RealizeIn G.structure colors φ v ↔ RealizeIn G.structure colors φ w := by
  have := agreement S φ hφ hp (xs := default) (ys := default) hv
    (fun i => i.elim0)
  exact this

end Lax5Proofs.EFAgreement
