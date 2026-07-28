import Lax3.Locality
import Mathlib.Data.List.Sublists

/-!
The algebra of the reified boolean combinations `BC` of
`Lax3.Locality`: clause lemmas for `BC.eval` and `BC.atoms`, the derived
connectives (`fls`, `or`, `bigAnd`, `bigOr`), the two functorial
operations (`map` along a map of atoms, `subst` replacing each atom by a
combination), the interpretation of a combination back inside an atom
type carrying its own connectives (`interp`), and — the reason the file
exists — the *sum case split*: how a combination whose atoms are drawn
from `α ⊕ γ` is evaluated by first fixing the truth pattern of its
`γ`-atoms.

Nothing here mentions distance logic; `α` and `γ` are arbitrary.

# How the locality assembly consumes this file

The assembly of the locality theorem meets, at an existential
quantifier, a goal of the shape

    ∃ v, BC.eval (Sum.elim (Sat G col (Fin.snoc m v)) (scatter atoms)) b

with `b : BC (DistFO L (k+1) ⊕ ScatterSentence L)`. The scatter atoms are
*sentences*: their truth does not depend on `v`. So the finitely many
truth patterns of the `γ`-side of `b` may be enumerated once and for all,
outside the quantifier. That is `exists_eval_sum_iff`: the goal becomes a
disjunction, over the patterns `τ ∈ assignments b`, of

    BC.eval (scatter atoms) (patternBC τ b) ∧ ∃ v, BC.eval … (collapse τ b)

where `collapse τ b : BC (DistFO L (k+1))` is `b` with every scatter atom
replaced by the truth value `τ` assigns it, and `patternBC τ b :
BC (ScatterSentence L)` is the conjunction of scatter atoms and their
negations that asserts the pattern.

The second conjunct is then closed up: `interp` turns the pure-formula
combination `collapse τ b` into a single formula (with `interp_prop`
carrying locality and rank through), `.exL` binds `v`, and the result is
one atom — or, more generally, one `BC` — over `DistFO L k`. Feeding that
`w τ` back in, `eval_pullOut` rebuilds a single
`BC (DistFO L k ⊕ ScatterSentence L)` and `mem_atoms_pullOut_left`,
`mem_atoms_pullOut_right` return its atoms to the side conditions of the
theorem.

`BC.eval` and `BC.atoms` are concept-side definitions and are never
handed to a tactic; the `local simp` clause lemmas of the unfolding
section below are the sanctioned interface, exactly as in
`Lax3Proofs.SyntaxLemmas`.
-/

namespace Lax3Proofs.BCAlgebra

open Lax3.Locality

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ### Unfolding the concept-side definitions

One `rfl`-lemma per clause of `BC.eval` and `BC.atoms`. Handing either
definition to `simp`, `rw` or `unfold` would manufacture its match
splitters under the concept's namespace, which a proofs package may not
do; `Iff.rfl` and `rfl` record nothing.
-/

section Unfolding

variable {p : α → Prop}

/-- Evaluation of an atom. -/
theorem eval_atom (a : α) : BC.eval p (.atom a) ↔ p a := Iff.rfl

/-- Evaluation of the empty combination. -/
theorem eval_tru : BC.eval p (.tru : BC α) ↔ True := Iff.rfl

/-- Evaluation of a negation. -/
theorem eval_not (b : BC α) : BC.eval p b.not ↔ ¬ BC.eval p b := Iff.rfl

/-- Evaluation of a conjunction. -/
theorem eval_and (b c : BC α) : BC.eval p (b.and c) ↔ BC.eval p b ∧ BC.eval p c := Iff.rfl

/-- The atoms of an atom. -/
theorem atoms_atom (a : α) : (BC.atom a).atoms = [a] := rfl

/-- The atoms of the empty combination. -/
theorem atoms_tru : (BC.tru : BC α).atoms = [] := rfl

/-- The atoms of a negation. -/
theorem atoms_not (b : BC α) : b.not.atoms = b.atoms := rfl

/-- The atoms of a conjunction. -/
theorem atoms_and (b c : BC α) : (b.and c).atoms = b.atoms ++ c.atoms := rfl

end Unfolding

attribute [local simp]
  eval_atom eval_tru eval_not eval_and atoms_atom atoms_tru atoms_not atoms_and

/-! ### Evaluation depends only on the atoms -/

/-- Two truth assignments agreeing on the atoms of a combination give it
the same truth value. -/
theorem eval_congr {p q : α → Prop} (b : BC α) (h : ∀ a ∈ b.atoms, (p a ↔ q a)) :
    BC.eval p b ↔ BC.eval q b := by
  induction b with
  | atom a => exact h a (by simp)
  | tru => simp
  | not b ih => exact not_congr (ih h)
  | and b c ihb ihc =>
    exact and_congr (ihb fun a ha => h a (by simp [ha]))
      (ihc fun a ha => h a (by simp [ha]))

/-! ### Derived connectives -/

/-- The always-false combination. -/
def fls : BC α := .not .tru

/-- Evaluation of falsity. -/
theorem eval_fls {p : α → Prop} : BC.eval p (fls : BC α) ↔ False := by simp [fls]

/-- Falsity has no atoms. -/
theorem atoms_fls : (fls : BC α).atoms = [] := rfl

/-- Disjunction, as the de Morgan abbreviation the concept's docstring
names. -/
def or (b c : BC α) : BC α := .not (.and b.not c.not)

/-- Evaluation of a disjunction. -/
theorem eval_or {p : α → Prop} (b c : BC α) :
    BC.eval p (or b c) ↔ BC.eval p b ∨ BC.eval p c := by
  simp only [or, eval_not, eval_and]
  tauto

/-- The atoms of a disjunction. -/
theorem atoms_or (b c : BC α) : (or b c).atoms = b.atoms ++ c.atoms := rfl

/-- The conjunction of a list of combinations. -/
def bigAnd : List (BC α) → BC α
  | [] => .tru
  | b :: bs => .and b (bigAnd bs)

/-- The empty conjunction. -/
theorem bigAnd_nil : bigAnd ([] : List (BC α)) = .tru := rfl

/-- A nonempty conjunction. -/
theorem bigAnd_cons (b : BC α) (bs : List (BC α)) :
    bigAnd (b :: bs) = .and b (bigAnd bs) := rfl

/-- Evaluation of a list conjunction. -/
theorem eval_bigAnd {p : α → Prop} (l : List (BC α)) :
    BC.eval p (bigAnd l) ↔ ∀ b ∈ l, BC.eval p b := by
  induction l with
  | nil => simp [bigAnd_nil]
  | cons b bs ih => simp [bigAnd_cons, ih]

/-- The atoms of a list conjunction. -/
theorem atoms_bigAnd (l : List (BC α)) : (bigAnd l).atoms = l.flatMap BC.atoms := by
  induction l with
  | nil => simp [bigAnd_nil]
  | cons b bs ih => simp [bigAnd_cons, ih]

/-- Membership in the atoms of a list conjunction. -/
theorem mem_atoms_bigAnd {l : List (BC α)} {a : α} :
    a ∈ (bigAnd l).atoms ↔ ∃ b ∈ l, a ∈ b.atoms := by
  rw [atoms_bigAnd, List.mem_flatMap]

/-- The disjunction of a list of combinations. -/
def bigOr : List (BC α) → BC α
  | [] => fls
  | b :: bs => or b (bigOr bs)

/-- The empty disjunction. -/
theorem bigOr_nil : bigOr ([] : List (BC α)) = fls := rfl

/-- A nonempty disjunction. -/
theorem bigOr_cons (b : BC α) (bs : List (BC α)) :
    bigOr (b :: bs) = or b (bigOr bs) := rfl

/-- Evaluation of a list disjunction. -/
theorem eval_bigOr {p : α → Prop} (l : List (BC α)) :
    BC.eval p (bigOr l) ↔ ∃ b ∈ l, BC.eval p b := by
  induction l with
  | nil => simp [bigOr_nil, eval_fls]
  | cons b bs ih => simp [bigOr_cons, eval_or, ih]

/-- The atoms of a list disjunction. -/
theorem atoms_bigOr (l : List (BC α)) : (bigOr l).atoms = l.flatMap BC.atoms := by
  induction l with
  | nil => simp [bigOr_nil, atoms_fls]
  | cons b bs ih => simp [bigOr_cons, atoms_or, ih]

/-- Membership in the atoms of a list disjunction. -/
theorem mem_atoms_bigOr {l : List (BC α)} {a : α} :
    a ∈ (bigOr l).atoms ↔ ∃ b ∈ l, a ∈ b.atoms := by
  rw [atoms_bigOr, List.mem_flatMap]

/-! ### Mapping and substituting atoms -/

/-- Relabelling the atoms of a combination along `f`. -/
def map (f : α → β) : BC α → BC β
  | .atom a => .atom (f a)
  | .tru => .tru
  | .not b => .not (map f b)
  | .and b c => .and (map f b) (map f c)

/-- Evaluation of a relabelled combination: the valuation travels the
other way. -/
theorem eval_map {q : β → Prop} (f : α → β) (b : BC α) :
    BC.eval q (map f b) ↔ BC.eval (q ∘ f) b := by
  induction b with
  | atom a => simp [map]
  | tru => simp [map]
  | not b ih => simp [map, ih]
  | and b c ihb ihc => simp [map, ihb, ihc]

/-- The atoms of a relabelled combination. -/
theorem atoms_map (f : α → β) (b : BC α) : (map f b).atoms = b.atoms.map f := by
  induction b with
  | atom a => simp [map]
  | tru => simp [map]
  | not b ih => simp [map, ih]
  | and b c ihb ihc => simp [map, ihb, ihc]

/-- Evaluating a combination relabelled into the left summand. -/
theorem eval_map_inl {p : α → Prop} {q : γ → Prop} (b : BC α) :
    BC.eval (Sum.elim p q) (map Sum.inl b) ↔ BC.eval p b := by
  rw [eval_map]
  rfl

/-- Evaluating a combination relabelled into the right summand. -/
theorem eval_map_inr {p : α → Prop} {q : γ → Prop} (b : BC γ) :
    BC.eval (Sum.elim p q) (map Sum.inr b) ↔ BC.eval q b := by
  rw [eval_map]
  rfl

/-- Substitution: each atom is replaced by a combination. -/
def subst (f : α → BC β) : BC α → BC β
  | .atom a => f a
  | .tru => .tru
  | .not b => .not (subst f b)
  | .and b c => .and (subst f b) (subst f c)

/-- Evaluation composes along a substitution. -/
theorem eval_subst {q : β → Prop} (f : α → BC β) (b : BC α) :
    BC.eval q (subst f b) ↔ BC.eval (fun a => BC.eval q (f a)) b := by
  induction b with
  | atom a => simp [subst]
  | tru => simp [subst]
  | not b ih => simp [subst, ih]
  | and b c ihb ihc => simp [subst, ihb, ihc]

/-- The atoms of a substitution instance. -/
theorem atoms_subst (f : α → BC β) (b : BC α) :
    (subst f b).atoms = b.atoms.flatMap fun a => (f a).atoms := by
  induction b with
  | atom a => simp [subst]
  | tru => simp [subst]
  | not b ih => simp [subst, ih]
  | and b c ihb ihc => simp [subst, ihb, ihc]

/-! ### Interpreting a combination inside its atom type

When the atoms themselves carry connectives — as formulas of distance
logic do — a combination collapses to a single atom. This is how the
assembly turns a boolean combination of local formulas back into one
local formula before binding a quantifier in front of it.
-/

/-- Collapse a combination to a single atom, using connectives `t`, `n`,
`c` of the atom type. -/
def interp (t : α) (n : α → α) (c : α → α → α) : BC α → α
  | .atom a => a
  | .tru => t
  | .not b => n (interp t n c b)
  | .and b₁ b₂ => c (interp t n c b₁) (interp t n c b₂)

/-- The collapse is sound for any valuation under which the atom-level
connectives behave as connectives. -/
theorem eval_interp {p : α → Prop} {t : α} {n : α → α} {c : α → α → α}
    (ht : p t) (hn : ∀ x, p (n x) ↔ ¬ p x) (hc : ∀ x y, p (c x y) ↔ p x ∧ p y) (b : BC α) :
    p (interp t n c b) ↔ BC.eval p b := by
  induction b with
  | atom a => simp [interp]
  | tru => simp [interp, ht]
  | not b ih => rw [interp, hn, ih, eval_not]
  | and b₁ b₂ ih₁ ih₂ => rw [interp, hc, ih₁, ih₂, eval_and]

/-- A property of atoms closed under the atom-level connectives and
holding at every atom of a combination holds at its collapse. This is how
locality and distance rank travel through the collapse. -/
theorem interp_prop {P : α → Prop} {t : α} {n : α → α} {c : α → α → α}
    (ht : P t) (hn : ∀ x, P x → P (n x)) (hc : ∀ x y, P x → P y → P (c x y))
    (b : BC α) (hb : ∀ a ∈ b.atoms, P a) : P (interp t n c b) := by
  induction b with
  | atom a => exact hb a (by simp)
  | tru => exact ht
  | not b ih => exact hn _ (ih hb)
  | and b₁ b₂ ih₁ ih₂ =>
    exact hc _ _ (ih₁ fun a ha => hb a (by simp [ha])) (ih₂ fun a ha => hb a (by simp [ha]))

/-! ### The sum case split

A combination over `α ⊕ γ` is evaluated by `Sum.elim p q`. Fixing a truth
pattern `τ : γ → Bool` for the right atoms turns it into a combination
over `α` alone; there are finitely many patterns that matter, since only
the right atoms *occurring in the combination* are read.
-/

/-- The right atoms of a combination over a sum type. -/
def rightAtoms (b : BC (α ⊕ γ)) : List γ := b.atoms.filterMap Sum.getRight?

/-- Membership in the right atoms. -/
theorem mem_rightAtoms {b : BC (α ⊕ γ)} {g : γ} :
    g ∈ rightAtoms b ↔ Sum.inr g ∈ b.atoms := by
  simp only [rightAtoms, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hxg⟩
    rcases x with a | g'
    · simp at hxg
    · rw [show g' = g by simpa using hxg] at hx
      exact hx
  · exact fun h => ⟨Sum.inr g, h, by simp⟩

/-- `b` with every right atom replaced by the truth value `τ` assigns it. -/
def collapse (τ : γ → Bool) (b : BC (α ⊕ γ)) : BC α :=
  subst (Sum.elim (fun a => .atom a) fun g => if τ g then .tru else fls) b

/-- Collapsing is sound as soon as the pattern `τ` agrees with the actual
truth values `q` on the right atoms that occur. -/
theorem eval_collapse {τ : γ → Bool} {p : α → Prop} {q : γ → Prop} (b : BC (α ⊕ γ))
    (hτ : ∀ g, Sum.inr g ∈ b.atoms → (τ g = true ↔ q g)) :
    BC.eval (Sum.elim p q) b ↔ BC.eval p (collapse τ b) := by
  rw [collapse, eval_subst]
  refine eval_congr b ?_
  rintro (a | g) ha
  · exact Iff.rfl
  · show q g ↔ BC.eval p (if τ g then BC.tru else fls)
    by_cases h : τ g = true
    · rw [if_pos h]
      exact iff_of_true ((hτ g ha).mp h) (by simp)
    · rw [if_neg h]
      exact iff_of_false (fun hq => h ((hτ g ha).mpr hq)) (by simp [eval_fls])

/-- The atoms of a collapse are exactly the left atoms of the original
combination. -/
theorem mem_atoms_collapse {τ : γ → Bool} {b : BC (α ⊕ γ)} {a : α} :
    a ∈ (collapse τ b).atoms ↔ Sum.inl a ∈ b.atoms := by
  induction b with
  | atom x =>
    rcases x with x | g
    · simp [collapse, subst]
    · by_cases h : τ g = true
      · simp [collapse, subst, if_pos h]
      · simp [collapse, subst, if_neg h, fls]
  | tru => simp [collapse, subst]
  | not b ih => exact ih
  | and b c ihb ihc =>
    show a ∈ ((collapse τ b).atoms ++ (collapse τ c).atoms) ↔
      Sum.inl a ∈ (b.atoms ++ c.atoms)
    simp [ihb, ihc]

/-- The combination over `γ` asserting the truth pattern `τ` on the right
atoms of `b`. -/
def patternBC (τ : γ → Bool) (b : BC (α ⊕ γ)) : BC γ :=
  bigAnd ((rightAtoms b).map fun g => if τ g then .atom g else (BC.atom g).not)

/-- The pattern combination says exactly that `τ` agrees with the truth
values on the right atoms that occur. -/
theorem eval_patternBC {τ : γ → Bool} {q : γ → Prop} (b : BC (α ⊕ γ)) :
    BC.eval q (patternBC τ b) ↔ ∀ g, Sum.inr g ∈ b.atoms → (τ g = true ↔ q g) := by
  rw [patternBC, eval_bigAnd]
  simp only [List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h g hg
    have hmem : g ∈ rightAtoms b := mem_rightAtoms.mpr hg
    have hval := h _ g hmem rfl
    by_cases hτ : τ g = true
    · rw [if_pos hτ, eval_atom] at hval
      exact iff_of_true hτ hval
    · rw [if_neg hτ, eval_not, eval_atom] at hval
      exact iff_of_false hτ hval
  · rintro h x g hg rfl
    have hval := h g (mem_rightAtoms.mp hg)
    by_cases hτ : τ g = true
    · rw [if_pos hτ, eval_atom]
      exact hval.mp hτ
    · rw [if_neg hτ, eval_not, eval_atom]
      exact fun hq => hτ (hval.mpr hq)

/-- The atoms of the pattern combination are the right atoms of `b`. -/
theorem atoms_patternBC {τ : γ → Bool} (b : BC (α ⊕ γ)) :
    (patternBC τ b).atoms = rightAtoms b := by
  rw [patternBC, atoms_bigAnd]
  induction rightAtoms b with
  | nil => simp
  | cons g gs ih =>
    by_cases h : τ g = true
    · simp [if_pos h, ih]
    · simp [if_neg h, ih]

/-- Membership in the atoms of the pattern combination. -/
theorem mem_atoms_patternBC {τ : γ → Bool} {b : BC (α ⊕ γ)} {g : γ} :
    g ∈ (patternBC τ b).atoms ↔ Sum.inr g ∈ b.atoms := by
  rw [atoms_patternBC, mem_rightAtoms]

/-! ### Finitely many patterns

The patterns that matter are the assignments determined by a sublist of
the right atoms; the list of them is what the assembly traverses to build
a disjunction.
-/

/-- Every truth assignment on a list agrees, on that list, with the
indicator of one of its sublists. -/
theorem exists_sublist_agree (l : List γ) (q : γ → Prop) :
    ∃ s : List γ, s.Sublist l ∧ ∀ g ∈ l, (g ∈ s ↔ q g) := by
  classical
  refine ⟨l.filter fun g => decide (q g), List.filter_sublist, fun g hg => ?_⟩
  simp [List.mem_filter, hg]

/-- The finitely many truth patterns of the right atoms of `b` that a
combination can distinguish: the indicators of the sublists of its right
atoms. -/
noncomputable def assignments (b : BC (α ⊕ γ)) : List (γ → Bool) :=
  (rightAtoms b).sublists.map fun s g => @decide (g ∈ s) (Classical.propDecidable _)

/-- The enumeration is exhaustive: whatever the actual truth values `q`
of the right atoms, some listed pattern agrees with them on the right
atoms of `b`. -/
theorem exists_mem_assignments (b : BC (α ⊕ γ)) (q : γ → Prop) :
    ∃ τ ∈ assignments b, ∀ g, Sum.inr g ∈ b.atoms → (τ g = true ↔ q g) := by
  obtain ⟨s, hsub, hs⟩ := exists_sublist_agree (rightAtoms b) q
  refine ⟨fun g => @decide (g ∈ s) (Classical.propDecidable _), ?_, ?_⟩
  · rw [assignments]
    exact List.mem_map.mpr ⟨s, List.mem_sublists.mpr hsub, rfl⟩
  · intro g hg
    simp only [decide_eq_true_eq]
    exact hs g (mem_rightAtoms.mpr hg)

/-! ### Pulling the right atoms out of a quantifier

The right atoms of a combination are evaluated by a valuation `q` that
does not depend on the quantified variable, so the finitely many patterns
of them commute with the quantifier.
-/

/-- **The case split.** An existential over a combination whose right
atoms are evaluated uniformly is the disjunction, over the finitely many
patterns of those atoms, of "the pattern holds" and "the collapsed
combination is satisfiable". -/
theorem exists_eval_sum_iff {ι : Type*} (b : BC (α ⊕ γ)) (p : ι → α → Prop) (q : γ → Prop) :
    (∃ v : ι, BC.eval (Sum.elim (p v) q) b) ↔
      ∃ τ ∈ assignments b,
        BC.eval q (patternBC τ b) ∧ ∃ v : ι, BC.eval (p v) (collapse τ b) := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨τ, hτmem, hτ⟩ := exists_mem_assignments b q
    exact ⟨τ, hτmem, (eval_patternBC b).mpr hτ, v, (eval_collapse b hτ).mp hv⟩
  · rintro ⟨τ, -, hpat, v, hv⟩
    exact ⟨v, (eval_collapse b ((eval_patternBC b).mp hpat)).mpr hv⟩

/-- The combination the case split rebuilds, given for each pattern a
combination `w τ` over the new left atoms standing for "the collapsed
combination is satisfiable". -/
noncomputable def pullOut {δ : Type*} (b : BC (α ⊕ γ)) (w : (γ → Bool) → BC δ) : BC (δ ⊕ γ) :=
  bigOr ((assignments b).map fun τ => (map Sum.inl (w τ)).and (map Sum.inr (patternBC τ b)))

/-- **The case split, rebuilt as one combination.** -/
theorem eval_pullOut {ι : Type*} {δ : Type*} (b : BC (α ⊕ γ)) (w : (γ → Bool) → BC δ)
    (p : ι → α → Prop) (q : γ → Prop) (p' : δ → Prop)
    (hw : ∀ τ, BC.eval p' (w τ) ↔ ∃ v : ι, BC.eval (p v) (collapse τ b)) :
    (∃ v : ι, BC.eval (Sum.elim (p v) q) b) ↔ BC.eval (Sum.elim p' q) (pullOut b w) := by
  rw [pullOut, eval_bigOr, exists_eval_sum_iff b p q]
  simp only [List.mem_map, exists_exists_and_eq_and, eval_and, eval_map_inl, eval_map_inr, hw]
  exact exists_congr fun τ => and_congr_right fun _ => and_comm

/-- The left atoms of the rebuilt combination come from the `w τ`. -/
theorem mem_atoms_pullOut_left {δ : Type*} {b : BC (α ⊕ γ)} {w : (γ → Bool) → BC δ} {d : δ} :
    Sum.inl d ∈ (pullOut b w).atoms ↔ ∃ τ ∈ assignments b, d ∈ (w τ).atoms := by
  rw [pullOut, mem_atoms_bigOr]
  simp only [List.mem_map, exists_exists_and_eq_and, atoms_and, List.mem_append, atoms_map,
    List.mem_map]
  refine exists_congr fun τ => and_congr_right fun _ => ?_
  constructor
  · rintro (⟨d', hd', hde⟩ | ⟨g, -, hge⟩)
    · exact (Sum.inl_injective hde) ▸ hd'
    · exact absurd hge (by simp)
  · exact fun h => Or.inl ⟨d, h, rfl⟩

/-- The right atoms of the rebuilt combination are right atoms of the
original one. -/
theorem mem_atoms_pullOut_right {δ : Type*} {b : BC (α ⊕ γ)} {w : (γ → Bool) → BC δ} {g : γ}
    (h : Sum.inr g ∈ (pullOut b w).atoms) : Sum.inr g ∈ b.atoms := by
  rw [pullOut, mem_atoms_bigOr] at h
  simp only [List.mem_map, exists_exists_and_eq_and, atoms_and, List.mem_append, atoms_map,
    List.mem_map] at h
  obtain ⟨τ, -, (⟨d, -, hde⟩ | ⟨g', hg', hge⟩)⟩ := h
  · exact absurd hde (by simp)
  · exact mem_atoms_patternBC.mp ((Sum.inr_injective hge) ▸ hg')

end Lax3Proofs.BCAlgebra
