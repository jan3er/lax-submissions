import Lax3Proofs.Evaluator

/-!
The **construction-time formula tables**: for every depth of the
model-checking recursion, the finite list of one-variable formulas whose
truth values the RAM driver tabulates, closed under the evaluator's step
and carrying the rank facts the correctness walk consumes. Everything
here is data and lemmas about data — no program, no arena, no run.

# What is tabled, and why it is finite

The abstract evaluator of `Lax3Proofs.Evaluator` never invents a formula
during a run: at each cluster step it relativizes the formula it holds
to the cluster (`Lax3Proofs.Relativize.rel`, one new color), isolates the
batch (`Lax3Proofs.Isolate.iso`, one new color per batch vertex and
capped distance and one per old color and capped distance), and hands the
result to the locality theorem, which decomposes it into local atoms and
scatter sentences. The formulas that reach the *next* depth are therefore
determined by the formulas at this depth alone — the arena is nowhere
involved. `tablesAt` is that determination, run ahead of time:

* `tablesAt 0` is the list of scatter formulas of the top sentence's
  boolean combination — the only one-variable formulas the sentence
  evaluator ever asks a table about;
* `tablesAt (j + 1)` collects, for each tabled `β`, the local atoms of
  the step formula `stepFml j β` *and* the formulas of its scatter
  atoms, all over the depth-`(j + 1)` signature `sigL (j + 1)`.

The lists are constants in the input size: they depend only on the top
sentence and on the three fixed parameters `q_top`, `cap`, `mb`. No size
bound is proved here — `List` is the whole finiteness statement the
driver needs, and the tables are indexed by position.

# Why padding fixes the signature

`Evaluator.stepFormula` packs the isolation palette at batch size
`W.ncard`, which depends on the graph and on the batch Splitter happened
to choose; the palette it produces is not a function of the depth alone,
so it cannot index a table laid out before the run. The driver removes
the dependence by *padding*: it always enumerates a batch by exactly `mb`
entries, repeating entries when the batch is smaller. The per-depth
signature is then the graph-independent `sigL`, and `stepFml` is the
evaluator's step at that fixed size.

Padding is invisible to the isolation rewrite. `Lax3Proofs.Isolate`
reads a batch enumeration `w` only through `Set.range w` — the isolated
arena is `deleteVerts A (Set.range w)` and the profile slots record
distances to the vertices `w j` — and repeating entries does not change
the range (`range_comp_of_surjective` below). So `Isolate.sat_iso`
applies to a padded enumeration verbatim, with the same isolated arena
and the same profile colorings, and the driver's step is the evaluator's
step read at a larger, constant batch size.

# Sharing the evaluator's choices

Both the evaluator's non-local phase and its sentence phase branch on a
`dite` whose condition is an existence statement about the distance rank
of the formula in hand, and both feed `Classical.choose` of that
condition to `Lax3Proofs.Assembly.locality`, again under
`Classical.choose`. The boolean combination a table entry is built from
must be *that* combination, not another one with the same properties.

`bcOf`/`bcAtomsOf` therefore branch on the very same propositions —
`∃ q', q' + 1 ≤ q_top ∧ DRank 1 q' ψ` for the non-local phase,
`∃ q', q' ≤ q_top ∧ DRank 0 q' φ` for the sentence phase — and apply the
very same `Classical.choose`. Since a choice depends on its proof only up
to proof irrelevance, the combinations are literally the same term, which
is what `tablesNonlocal_iff_eval_bcOf` and `sentenceEval_iff_eval_bcOf₀`
record: the evaluator's value at a formula *is* the evaluation of the
table's own combination over the evaluator's local tables. A driver
correctness proof may consequently cite `bcOf_spec` for the atoms'
locality and rank and `Evaluator.tablesNonlocal_iff_sat` for the truth
value, with no obligation to reconcile two boolean combinations.

# The rank invariant

Every tabled formula is local and carries a distance rank `(k', q')` with
`1 ≤ k'` and `k' + q' ≤ q_top` — the invariant
`Lax3Proofs.Evaluator.LocalCorrect` runs on. It travels through the
*boolean combination*, not through the rewrites: `Isolate.iso` does not
preserve locality (its local-quantifier case adds an unrestricted
quantifier), but the atoms the locality theorem returns are local by
construction. The ranks come out of the theorem too — local atoms at
`(1, q₀)` with `q₀ + 1 ≤ q_top`, scatter formulas at `(1 + i, q₀ - i)`
with the same sum — after the rank of the incoming formula is normalized
to arity one down the antidiagonal, exactly as the evaluator's own dite
demands (`Evaluator.drank_one_of_drank`).

# Formalization notes

The evaluator's palette internals are public and are reused rather than
restated: `Evaluator.isoPalette`, `Evaluator.slotOld`, `Evaluator.slotPd`,
`Evaluator.slotPu` and `Evaluator.drank_one_of_drank`. `sigL` is defined
so that its successor clause *is* `isoPalette` at batch size `mb`, so the
slot maps typecheck at the depth-indexed signature with no cast.

`Lax3.Locality.BC.atoms` is already a `List`, so the two sides of a
combination over a sum type are extracted with `List.filterMap`:
`Lax3Proofs.BCAlgebra.rightAtoms` for the scatter atoms and `leftAtoms`
below for the local ones. No concept-side definition is handed to a
tactic anywhere: `Sat`, `DRank`, `IsLocal`, `BC.eval`, `BC.atoms` and the
scatter definitions are taken apart through the clause lemmas of
`Lax3Proofs.SyntaxLemmas` and `Lax3Proofs.BCAlgebra`; the definitions
introduced here are unfolded freely.
-/

namespace Lax3Proofs.FormulaTables

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.FirstOrder (FO)
open Lax3Proofs.SyntaxLemmas

/-! ### The left atoms of a boolean combination

`Lax3Proofs.BCAlgebra` already reads off the right atoms of a
combination over a sum type as a list; the left atoms are the mirror
image, and the driver needs both as lists, since it addresses a table by
position.
-/

universe u w

section LeftAtoms

variable {α : Type u} {γ : Type w}

/-- The left atoms of a combination over a sum type, as a list. -/
def leftAtoms (b : BC (α ⊕ γ)) : List α := b.atoms.filterMap Sum.getLeft?

/-- Membership in the left atoms. -/
theorem mem_leftAtoms {b : BC (α ⊕ γ)} {a : α} :
    a ∈ leftAtoms b ↔ Sum.inl a ∈ b.atoms := by
  simp only [leftAtoms, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hxa⟩
    rcases x with a' | g
    · rw [show a' = a by simpa using hxa] at hx
      exact hx
    · simp at hxa
  · exact fun h => ⟨Sum.inl a, h, by simp⟩

end LeftAtoms

/-! ### Padding a batch enumeration

The one fact that makes a padded enumeration interchangeable with the
enumeration it pads: the isolation rewrite reads an enumeration only
through its range, and repeating entries leaves the range alone.
-/

/-- Precomposing with a surjection does not change the range. With
`pad : Fin mb → Fin m` surjective this is the statement that padding a
batch enumeration to the fixed width `mb` by repetition isolates the same
vertex set and records the same profiles, so `Lax3Proofs.Isolate.sat_iso`
applies to the padded enumeration verbatim. -/
theorem range_comp_of_surjective {ι κ : Type*} {α : Type*} (w : κ → α) {pad : ι → κ}
    (hpad : Function.Surjective pad) : Set.range (w ∘ pad) = Set.range w := by
  rw [Set.range_comp, hpad.range_eq, Set.image_univ]

/-! ### The signature of each depth

Relativization adds the cluster as one new color; isolation adds one
color per padded batch entry and capped distance and one per incoming
color and capped distance. Both together are the evaluator's
`isoPalette`, read at the padded batch size `mb`.
-/

/-- The signature the driver's formulas live over at depth `j`: the empty
palette at the root, and one relativization step followed by one
isolation step at batch size `mb` per depth. -/
def sigL (cap mb : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => Evaluator.isoPalette (sigL cap mb j + 1) mb cap

/-- The root signature is empty: a plain first-order sentence mentions no
color. -/
theorem sigL_zero (cap mb : ℕ) : sigL cap mb 0 = 0 := rfl

/-- One depth of palette growth, spelled out: the relativization marker,
the batch profiles and the color profiles. -/
theorem sigL_succ (cap mb j : ℕ) :
    sigL cap mb (j + 1) =
      (sigL cap mb j + 1) + (mb * (cap + 1) + (sigL cap mb j + 1) * (cap + 1)) := rfl

/-! ### The slot maps of each depth

The three slot families of `Lax3Proofs.Evaluator`, instantiated at the
depth-indexed signature. Nothing is restated: `Evaluator.slotOld`,
`Evaluator.slotPd` and `Evaluator.slotPu` are public, and `sigL (j + 1)`
is by definition the palette they address.
-/

/-- Where an incoming color of depth `j` — the relativized palette, one
wider than `sigL j` — sits at depth `j + 1`. -/
def oldSlots (cap mb j : ℕ) : Fin (sigL cap mb j + 1) → Fin (sigL cap mb (j + 1)) :=
  @Evaluator.slotOld (sigL cap mb j + 1) mb cap

/-- Where the distance profile of the padded batch entry `i` at radius
`a` sits at depth `j + 1`. -/
def pdSlots (cap mb j : ℕ) : Fin mb → Fin (cap + 1) → Fin (sigL cap mb (j + 1)) :=
  @Evaluator.slotPd (sigL cap mb j + 1) mb cap

/-- Where the distance profile of the color class `c` at radius `b` sits
at depth `j + 1`. -/
def puSlots (cap mb j : ℕ) : Fin (sigL cap mb j + 1) → Fin (cap + 1) →
    Fin (sigL cap mb (j + 1)) :=
  @Evaluator.slotPu (sigL cap mb j + 1) mb cap

/-! ### The step on formulas -/

/-- **The evaluator's step, at the padded batch size.** Relativize to the
cluster — the old colors along `Fin.castSucc`, the cluster itself as the
marker `Fin.last` — and then isolate the batch at the three slot families
of the depth. This is `Evaluator.stepFormula` with `W.ncard` replaced by
the constant `mb`; the driver runs this one, and the evaluator's is the
semantic template it is read against. -/
def stepFml (cap mb j : ℕ) (β : DistFO (sigL cap mb j) 1) : DistFO (sigL cap mb (j + 1)) 1 :=
  Lax3Proofs.Isolate.iso (oldSlots cap mb j) (pdSlots cap mb j) (puSlots cap mb j)
    (Lax3Proofs.Relativize.rel Fin.castSucc (Fin.last (sigL cap mb j)) β)

/-- **The step preserves distance rank exactly**: both rewrites do, by
`Lax3Proofs.Relativize.drank_rel` and `Lax3Proofs.Isolate.drank_iso`.
Locality is *not* preserved — the isolation rewrite turns a local
quantifier into a disjunction with an unrestricted one — which is why the
invariant of the tables travels through the boolean combination instead.
-/
theorem drank_stepFml {cap mb j k' q' : ℕ} {β : DistFO (sigL cap mb j) 1}
    (h : DRank k' q' β) : DRank k' q' (stepFml cap mb j β) :=
  Lax3Proofs.Isolate.drank_iso (Lax3Proofs.Relativize.drank_rel _ _ h)

/-! ### The boolean combination of a formula

The evaluator's non-local phase branches on
`∃ q', q' + 1 ≤ q_top ∧ DRank 1 q' ψ` and, in the positive branch, feeds
`Classical.choose` of that condition to the locality theorem under a
second `Classical.choose`. Everything in this section reproduces those
two choices verbatim, so that the table and the evaluator are talking
about the same combination.
-/

section BC

variable {L : ℕ}

/-- The quantifier rank the evaluator's non-local dite chooses for a
formula. -/
noncomputable def chosenRank (q_top : ℕ) (ψ : DistFO L 1)
    (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ) : ℕ :=
  Classical.choose h

/-- The chosen rank leaves a level for the locality theorem to spend. -/
theorem chosenRank_add_one_le {q_top : ℕ} {ψ : DistFO L 1}
    (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ) : chosenRank q_top ψ h + 1 ≤ q_top :=
  (Classical.choose_spec h).1

/-- The formula has the chosen rank at arity one. -/
theorem drank_chosenRank {q_top : ℕ} {ψ : DistFO L 1}
    (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ) : DRank 1 (chosenRank q_top ψ h) ψ :=
  (Classical.choose_spec h).2

/-- The boolean combination the evaluator's non-local phase chooses for a
formula: `Lax3Proofs.Assembly.locality` at the greedy scatter choice, at
the rank the dite chose. -/
noncomputable def bcOf (q_top : ℕ) (ψ : DistFO L 1)
    (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ) :
    BC (DistFO L 1 ⊕ ScatterSentence L) :=
  Classical.choose (Assembly.locality greedyChoice ψ (drank_chosenRank h))

/-- **The three facts the locality theorem attaches to the chosen
combination**, re-exposed in the shape a consumer uses: its local atoms
are local of the chosen rank, its scatter atoms have the chosen rank, and
it evaluates to the formula's truth value in every colored graph. -/
theorem bcOf_spec (q_top : ℕ) (ψ : DistFO L 1)
    (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ) :
    (∀ γ : DistFO L 1, Sum.inl γ ∈ (bcOf q_top ψ h).atoms →
        IsLocal γ ∧ DRank 1 (chosenRank q_top ψ h) γ) ∧
      (∀ σ : ScatterSentence L, Sum.inr σ ∈ (bcOf q_top ψ h).atoms →
        σ.DRank 1 (chosenRank q_top ψ h)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin 1 → Fin n),
        Sat G col m ψ ↔
          (bcOf q_top ψ h).eval
            (Sum.elim (Sat G col m) (ScatterSentence.Sat greedyChoice G col)) :=
  Classical.choose_spec (Assembly.locality greedyChoice ψ (drank_chosenRank h))

open Classical in
/-- **The atoms of a formula's boolean combination, as two lists**: the
local atoms and the scatter atoms of the combination the evaluator
chooses. Outside the rank condition the evaluator's own value is junk,
and so is this: the pair of empty lists. -/
noncomputable def bcAtomsOf (q_top : ℕ) (ψ : DistFO L 1) :
    List (DistFO L 1) × List (ScatterSentence L) :=
  if h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ then
    (leftAtoms (bcOf q_top ψ h), BCAlgebra.rightAtoms (bcOf q_top ψ h))
  else ([], [])

/-- Inside the rank condition the two lists are the two sides of the
chosen combination. -/
theorem bcAtomsOf_pos {q_top : ℕ} {ψ : DistFO L 1}
    (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ) :
    bcAtomsOf q_top ψ =
      (leftAtoms (bcOf q_top ψ h), BCAlgebra.rightAtoms (bcOf q_top ψ h)) :=
  dif_pos h

/-- Outside the rank condition both lists are empty. -/
theorem bcAtomsOf_neg {q_top : ℕ} {ψ : DistFO L 1}
    (h : ¬ ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ) : bcAtomsOf q_top ψ = ([], []) :=
  dif_neg h

/-- The local list is the left atoms of the chosen combination. -/
theorem mem_bcAtomsOf_left {q_top : ℕ} {ψ : DistFO L 1}
    (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ) {γ : DistFO L 1} :
    γ ∈ (bcAtomsOf q_top ψ).1 ↔ Sum.inl γ ∈ (bcOf q_top ψ h).atoms := by
  rw [bcAtomsOf_pos h]
  exact mem_leftAtoms

/-- The scatter list is the right atoms of the chosen combination. -/
theorem mem_bcAtomsOf_right {q_top : ℕ} {ψ : DistFO L 1}
    (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ) {σ : ScatterSentence L} :
    σ ∈ (bcAtomsOf q_top ψ).2 ↔ Sum.inr σ ∈ (bcOf q_top ψ h).atoms := by
  rw [bcAtomsOf_pos h]
  exact BCAlgebra.mem_rightAtoms

/-- **Every tabled local atom is local of the chosen rank.** -/
theorem isLocal_and_drank_of_mem_bcAtomsOf {q_top : ℕ} {ψ : DistFO L 1}
    (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ) {γ : DistFO L 1}
    (hγ : γ ∈ (bcAtomsOf q_top ψ).1) : IsLocal γ ∧ DRank 1 (chosenRank q_top ψ h) γ :=
  (bcOf_spec q_top ψ h).1 γ ((mem_bcAtomsOf_left h).mp hγ)

/-- **Every tabled scatter atom has the chosen rank.** -/
theorem drank_of_mem_bcAtomsOf {q_top : ℕ} {ψ : DistFO L 1}
    (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ) {σ : ScatterSentence L}
    (hσ : σ ∈ (bcAtomsOf q_top ψ).2) : σ.DRank 1 (chosenRank q_top ψ h) :=
  (bcOf_spec q_top ψ h).2.1 σ ((mem_bcAtomsOf_right h).mp hσ)

/-- **The chosen combination computes the formula's truth value.** -/
theorem sat_iff_eval_bcOf {q_top : ℕ} {ψ : DistFO L 1}
    (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ) {n : ℕ} (G : SimpleGraph (Fin n))
    (col : Coloring n L) (m : Fin 1 → Fin n) :
    Sat G col m ψ ↔
      (bcOf q_top ψ h).eval
        (Sum.elim (Sat G col m) (ScatterSentence.Sat greedyChoice G col)) :=
  (bcOf_spec q_top ψ h).2.2 n G col m

/-! ### The same, at arity zero

The top sentence is 0-ary and its locality choice is the evaluator's
*sentence* dite, whose condition is `∃ q', q' ≤ q_top ∧ DRank 0 q' φ` —
one level cheaper, since no local table has to be paid for. Its scatter
atoms are the only place a one-variable formula enters at depth zero.
-/

/-- The quantifier rank the evaluator's sentence dite chooses. -/
noncomputable def chosenRank₀ (q_top : ℕ) (φ : DistFO L 0)
    (h : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ) : ℕ :=
  Classical.choose h

/-- The chosen sentence rank is below the top rank. -/
theorem chosenRank₀_le {q_top : ℕ} {φ : DistFO L 0}
    (h : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ) : chosenRank₀ q_top φ h ≤ q_top :=
  (Classical.choose_spec h).1

/-- The sentence has the chosen rank at arity zero. -/
theorem drank_chosenRank₀ {q_top : ℕ} {φ : DistFO L 0}
    (h : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ) : DRank 0 (chosenRank₀ q_top φ h) φ :=
  (Classical.choose_spec h).2

/-- The boolean combination the evaluator's sentence phase chooses. -/
noncomputable def bcOf₀ (q_top : ℕ) (φ : DistFO L 0)
    (h : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ) :
    BC (DistFO L 0 ⊕ ScatterSentence L) :=
  Classical.choose (Assembly.locality greedyChoice φ (drank_chosenRank₀ h))

/-- The locality theorem's three facts about the chosen sentence
combination. -/
theorem bcOf₀_spec (q_top : ℕ) (φ : DistFO L 0)
    (h : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ) :
    (∀ γ : DistFO L 0, Sum.inl γ ∈ (bcOf₀ q_top φ h).atoms →
        IsLocal γ ∧ DRank 0 (chosenRank₀ q_top φ h) γ) ∧
      (∀ σ : ScatterSentence L, Sum.inr σ ∈ (bcOf₀ q_top φ h).atoms →
        σ.DRank 0 (chosenRank₀ q_top φ h)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin 0 → Fin n),
        Sat G col m φ ↔
          (bcOf₀ q_top φ h).eval
            (Sum.elim (Sat G col m) (ScatterSentence.Sat greedyChoice G col)) :=
  Classical.choose_spec (Assembly.locality greedyChoice φ (drank_chosenRank₀ h))

open Classical in
/-- The atoms of the top sentence's boolean combination, as two lists:
the local sentences — which the evaluator decides outright, with no table
— and the scatter sentences, whose formulas are what depth zero tables. -/
noncomputable def bcAtomsOf₀ (q_top : ℕ) (φ : DistFO L 0) :
    List (DistFO L 0) × List (ScatterSentence L) :=
  if h : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ then
    (leftAtoms (bcOf₀ q_top φ h), BCAlgebra.rightAtoms (bcOf₀ q_top φ h))
  else ([], [])

/-- Inside the rank condition the two lists are the two sides of the
chosen sentence combination. -/
theorem bcAtomsOf₀_pos {q_top : ℕ} {φ : DistFO L 0}
    (h : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ) :
    bcAtomsOf₀ q_top φ =
      (leftAtoms (bcOf₀ q_top φ h), BCAlgebra.rightAtoms (bcOf₀ q_top φ h)) :=
  dif_pos h

/-- Outside the rank condition both lists are empty. -/
theorem bcAtomsOf₀_neg {q_top : ℕ} {φ : DistFO L 0}
    (h : ¬ ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ) : bcAtomsOf₀ q_top φ = ([], []) :=
  dif_neg h

/-- The scatter list of a sentence is the right atoms of its chosen
combination. -/
theorem mem_bcAtomsOf₀_right {q_top : ℕ} {φ : DistFO L 0}
    (h : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ) {σ : ScatterSentence L} :
    σ ∈ (bcAtomsOf₀ q_top φ).2 ↔ Sum.inr σ ∈ (bcOf₀ q_top φ h).atoms := by
  rw [bcAtomsOf₀_pos h]
  exact BCAlgebra.mem_rightAtoms

/-- The local list of a sentence is the left atoms of its chosen
combination. -/
theorem mem_bcAtomsOf₀_left {q_top : ℕ} {φ : DistFO L 0}
    (h : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ) {γ : DistFO L 0} :
    γ ∈ (bcAtomsOf₀ q_top φ).1 ↔ Sum.inl γ ∈ (bcOf₀ q_top φ h).atoms := by
  rw [bcAtomsOf₀_pos h]
  exact mem_leftAtoms

/-- **Every tabled scatter atom of the top sentence has the chosen
rank.** -/
theorem drank_of_mem_bcAtomsOf₀ {q_top : ℕ} {φ : DistFO L 0}
    (h : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ) {σ : ScatterSentence L}
    (hσ : σ ∈ (bcAtomsOf₀ q_top φ).2) : σ.DRank 0 (chosenRank₀ q_top φ h) :=
  (bcOf₀_spec q_top φ h).2.1 σ ((mem_bcAtomsOf₀_right h).mp hσ)

/-- **Every local atom of the top sentence is a local sentence of the
chosen rank.** -/
theorem isLocal_and_drank_of_mem_bcAtomsOf₀ {q_top : ℕ} {φ : DistFO L 0}
    (h : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ) {γ : DistFO L 0}
    (hγ : γ ∈ (bcAtomsOf₀ q_top φ).1) : IsLocal γ ∧ DRank 0 (chosenRank₀ q_top φ h) γ :=
  (bcOf₀_spec q_top φ h).1 γ ((mem_bcAtomsOf₀_left h).mp hγ)

/-- **The chosen sentence combination computes the sentence's truth
value.** -/
theorem sat_iff_eval_bcOf₀ {q_top : ℕ} {φ : DistFO L 0}
    (h : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ) {n : ℕ} (G : SimpleGraph (Fin n))
    (col : Coloring n L) (m : Fin 0 → Fin n) :
    Sat G col m φ ↔
      (bcOf₀ q_top φ h).eval
        (Sum.elim (Sat G col m) (ScatterSentence.Sat greedyChoice G col)) :=
  (bcOf₀_spec q_top φ h).2.2 n G col m

end BC

/-! ### The evaluator evaluates the very same combination

Both bridges are `rfl` after the evaluator's dite is taken: the
conditions are the same propositions and the choices are the same
choices, so the driver's tables and the evaluator's recursion cannot
disagree about which boolean combination a formula was decomposed into.
-/

section Sharing

variable {q_top cap mb b n L : ℕ} {A : SimpleGraph (Fin n)} {col : Coloring n L}

/-- **The non-local phase evaluates the table's own combination.** -/
theorem tablesNonlocal_iff_eval_bcOf {ψ : DistFO L 1}
    (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' ψ) (v : Fin n) :
    Evaluator.tablesNonlocal q_top cap mb b A col ψ v ↔
      (bcOf q_top ψ h).eval
        (Sum.elim (fun γ => Evaluator.tablesLocal q_top cap mb b A col γ v)
          (fun σ : ScatterSentence L => σ.t ≤ greedyChoice.size A σ.r
            {a | Evaluator.tablesLocal q_top cap mb b A col σ.β a})) := by
  rw [Evaluator.tablesNonlocal, dif_pos h]
  exact Iff.rfl

/-- **The sentence phase evaluates the table's own combination.** -/
theorem sentenceEval_iff_eval_bcOf₀ {φ : DistFO L 0}
    (h : ∃ q' : ℕ, q' ≤ q_top ∧ DRank 0 q' φ) :
    Evaluator.sentenceEval q_top cap mb b A col φ ↔
      (bcOf₀ q_top φ h).eval
        (Sum.elim Evaluator.localSentenceEval
          (fun σ : ScatterSentence L => σ.t ≤ greedyChoice.size A σ.r
            {a | Evaluator.tablesLocal q_top cap mb b A col σ.β a})) := by
  rw [Evaluator.sentenceEval, dif_pos h]
  exact Iff.rfl

end Sharing

/-! ### The tables -/

/-- The one-variable formulas of depth `j` the driver tabulates: at the
root, the formulas of the top sentence's scatter atoms; at depth `j + 1`,
for every formula tabled at depth `j`, the local atoms of its step
formula together with the formulas of that formula's scatter atoms.

The list depends on the top sentence `φ` and on the three fixed
parameters only — never on a graph — which is what makes it a
construction-time object. -/
noncomputable def tablesAt (q_top cap mb : ℕ) (φ : FO 0) :
    (j : ℕ) → List (DistFO (sigL cap mb j) 1)
  | 0 => (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2.map (·.β)
  | j + 1 =>
      (tablesAt q_top cap mb φ j).flatMap fun β =>
        (bcAtomsOf q_top (stepFml cap mb j β)).1 ++
          (bcAtomsOf q_top (stepFml cap mb j β)).2.map (·.β)

section Tables

variable {q_top cap mb : ℕ} {φ : FO 0}

/-- The root table: the formulas of the top sentence's scatter atoms. -/
theorem tablesAt_zero :
    tablesAt q_top cap mb φ 0 =
      (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2.map (·.β) := rfl

/-- One depth of the table: the local atoms and the scatter formulas of
the step formula of every entry. -/
theorem tablesAt_succ (j : ℕ) :
    tablesAt q_top cap mb φ (j + 1) =
      (tablesAt q_top cap mb φ j).flatMap (fun β =>
        (bcAtomsOf q_top (stepFml cap mb j β)).1 ++
          (bcAtomsOf q_top (stepFml cap mb j β)).2.map (·.β)) := rfl

/-! ### The invariant -/

/-- What a tabled formula is guaranteed to be: local, and of a distance
rank with at least one free variable whose two coordinates sum to at most
the top rank. This is exactly the hypothesis
`Lax3Proofs.Evaluator.LocalCorrect` quantifies over, so a table entry may
be handed to the evaluator's local tables without further ado. -/
def TableRank (q_top : ℕ) {L : ℕ} (β : DistFO L 1) : Prop :=
  IsLocal β ∧ ∃ k' q' : ℕ, 1 ≤ k' ∧ k' + q' ≤ q_top ∧ DRank k' q' β

/-- The invariant, spelled out. -/
theorem tableRank_iff {L : ℕ} {β : DistFO L 1} :
    TableRank q_top β ↔
      IsLocal β ∧ ∃ k' q' : ℕ, 1 ≤ k' ∧ k' + q' ≤ q_top ∧ DRank k' q' β := Iff.rfl

/-- The formula of a scatter sentence of distance rank `(k, q)` with
`k + q ≤ q_top` satisfies the table invariant: the rank witness `i` of
the scatter rank moves one coordinate to the other, leaving the sum —
and hence the bound — alone, and it is at least one, which is where the
free variable comes from. -/
theorem tableRank_beta_of_drank {L k q : ℕ} {σ : ScatterSentence L} (h : σ.DRank k q)
    (hq : k + q ≤ q_top) : TableRank q_top σ.β := by
  obtain ⟨-, i, hi1, hiq, hloc, hrank, -, -⟩ := scatterSentence_drank_iff.mp h
  exact ⟨hloc, k + i, q - i, by omega, by omega, hrank⟩

/-- The rank condition the evaluator's non-local dite tests, discharged
from the table invariant: a tabled formula's step formula has the same
rank, and a rank with a free variable to spare normalizes to arity one
down the antidiagonal. -/
theorem hasRank_stepFml {j : ℕ} {β : DistFO (sigL cap mb j) 1} (h : TableRank q_top β) :
    ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' (stepFml cap mb j β) := by
  obtain ⟨-, k', q', hk1, hsum, hrank⟩ := h
  obtain ⟨i, rfl⟩ : ∃ i, k' = i + 1 := ⟨k' - 1, by omega⟩
  exact ⟨i + q', by omega, Evaluator.drank_one_of_drank (drank_stepFml hrank)⟩

/-- **The table invariant.** Every tabled formula is local and carries a
distance rank `(k', q')` with `1 ≤ k'` and `k' + q' ≤ q_top`.

Induction on the depth. At the root the entries are the formulas of the
top sentence's scatter atoms, whose rank the locality theorem bounds by
the chosen sentence rank. At depth `j + 1` the entries come out of the
boolean combination of a step formula: locality is the locality theorem's
own guarantee about its local atoms — the step itself does *not* preserve
it — and the ranks are the chosen rank `q₀`, at `(1, q₀)` for a local
atom and at `(1 + i, q₀ - i)` for a scatter formula, both summing to
`1 + q₀ ≤ q_top`. -/
theorem tableRank_of_mem_tablesAt :
    ∀ (j : ℕ), ∀ β ∈ tablesAt q_top cap mb φ j, TableRank q_top β := by
  intro j
  induction j with
  | zero =>
    intro β hβ
    rw [tablesAt_zero] at hβ
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hβ
    by_cases h : ∃ q' : ℕ, q' ≤ q_top ∧
        DRank 0 q' (Reduction.toDistFO (L := sigL cap mb 0) φ)
    · exact tableRank_beta_of_drank (drank_of_mem_bcAtomsOf₀ h hσ)
        (by have := chosenRank₀_le h; omega)
    · rw [bcAtomsOf₀_neg h] at hσ
      exact absurd hσ (List.not_mem_nil)
  | succ j ih =>
    intro β hβ
    rw [tablesAt_succ] at hβ
    obtain ⟨γ, hγ, hmem⟩ := List.mem_flatMap.mp hβ
    have hcond := hasRank_stepFml (cap := cap) (mb := mb) (j := j) (ih γ hγ)
    have hq₀ := chosenRank_add_one_le hcond
    rcases List.mem_append.mp hmem with h | h
    · obtain ⟨hloc, hrank⟩ := isLocal_and_drank_of_mem_bcAtomsOf hcond h
      exact ⟨hloc, 1, chosenRank q_top (stepFml cap mb j γ) hcond, le_rfl, by omega, hrank⟩
    · obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp h
      exact tableRank_beta_of_drank (drank_of_mem_bcAtomsOf hcond hσ) (by omega)

/-! ### Closure

What the driver's correctness cites when it walks from a table entry to
the entries its step produced: both kinds of atom of a step formula are
tabled one depth down. The positional forms are the same facts read as
indices, which is what a table-indexed program consumes.
-/

/-- **The local atoms of a step formula are tabled one depth down.** -/
theorem bcLocals_subset_tablesAt_succ {j : ℕ} {β : DistFO (sigL cap mb j) 1}
    (hβ : β ∈ tablesAt q_top cap mb φ j) :
    (bcAtomsOf q_top (stepFml cap mb j β)).1 ⊆ tablesAt q_top cap mb φ (j + 1) := by
  intro γ hγ
  rw [tablesAt_succ]
  exact List.mem_flatMap.mpr ⟨β, hβ, List.mem_append.mpr (Or.inl hγ)⟩

/-- **The scatter formulas of a step formula are tabled one depth
down.** -/
theorem bcBetas_subset_tablesAt_succ {j : ℕ} {β : DistFO (sigL cap mb j) 1}
    (hβ : β ∈ tablesAt q_top cap mb φ j) :
    (bcAtomsOf q_top (stepFml cap mb j β)).2.map (·.β) ⊆
      tablesAt q_top cap mb φ (j + 1) := by
  intro γ hγ
  rw [tablesAt_succ]
  exact List.mem_flatMap.mpr ⟨β, hβ, List.mem_append.mpr (Or.inr hγ)⟩

/-- The scatter closure at a single atom, the form a walk over the atoms
uses. -/
theorem mem_tablesAt_succ_of_mem_bcAtomsOf_right {j : ℕ} {β : DistFO (sigL cap mb j) 1}
    (hβ : β ∈ tablesAt q_top cap mb φ j) {σ : ScatterSentence (sigL cap mb (j + 1))}
    (hσ : σ ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2) :
    σ.β ∈ tablesAt q_top cap mb φ (j + 1) :=
  bcBetas_subset_tablesAt_succ hβ (List.mem_map.mpr ⟨σ, hσ, rfl⟩)

/-- The position of a local atom of a step formula in the table one depth
down. -/
theorem exists_idx_of_mem_bcAtomsOf_left {j : ℕ} {β : DistFO (sigL cap mb j) 1}
    (hβ : β ∈ tablesAt q_top cap mb φ j) {γ : DistFO (sigL cap mb (j + 1)) 1}
    (hγ : γ ∈ (bcAtomsOf q_top (stepFml cap mb j β)).1) :
    ∃ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ (j + 1)).length),
      (tablesAt q_top cap mb φ (j + 1))[i] = γ :=
  List.mem_iff_getElem.mp (bcLocals_subset_tablesAt_succ hβ hγ)

/-- The position of the formula of a scatter atom of a step formula in
the table one depth down. -/
theorem exists_idx_of_mem_bcAtomsOf_right {j : ℕ} {β : DistFO (sigL cap mb j) 1}
    (hβ : β ∈ tablesAt q_top cap mb φ j) {σ : ScatterSentence (sigL cap mb (j + 1))}
    (hσ : σ ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2) :
    ∃ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ (j + 1)).length),
      (tablesAt q_top cap mb φ (j + 1))[i] = σ.β :=
  List.mem_iff_getElem.mp (mem_tablesAt_succ_of_mem_bcAtomsOf_right hβ hσ)

/-- The position of the formula of a scatter atom of the *top sentence*
in the root table — the driver's entry point. -/
theorem exists_idx_of_mem_bcAtomsOf₀_right {σ : ScatterSentence (sigL cap mb 0)}
    (hσ : σ ∈ (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2) :
    ∃ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ 0).length),
      (tablesAt q_top cap mb φ 0)[i] = σ.β := by
  refine List.mem_iff_getElem.mp ?_
  rw [tablesAt_zero]
  exact List.mem_map.mpr ⟨σ, hσ, rfl⟩

end Tables

end Lax3Proofs.FormulaTables
