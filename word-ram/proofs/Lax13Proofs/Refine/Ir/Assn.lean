import Lax13Proofs.Refine.Ir.Semantics

/-!
The IR's separation algebra and its assertion language.

Port of the PCM/assertion surface the artifact's VCG is built on, at the
pin recorded in `plans/word-ram/refinement-tower/design.md` §1
(`isabelle_llvm_time` @ `42dd7f5`), from the three files the P3 extracts
quote verbatim
(`plans/word-ram/refinement-tower/p3-sl-deep-extracts.md` §§2, 4 and
`p3-ir-sl-extracts.md` §2):

* AFP `Separation_Algebra` (Klein–Kolanski), imported by the artifact as
  `Separation_Algebra.Sep_Tactics` — the class stack
  `pre_sep_algebra` → `sep_algebra`, `sep_conj` (`**`), `sep_empty`
  (`□`), `sep_impl`, `sep_true`;
* `thys/lib/Sep_Algebra_Add.thy` — `stronger_sep_algebra`,
  `unique_zero_sep_algebra`, `tsa_opt`, `pred_lift` (`↑`), `EXACT`,
  `pure_part`;
* `thys/vcg/Sep_Generic_Wp.thy` — `FST` / `SND`, the credit assertion
  `$c ≡ SND (EXACT c)`, `GC ≡ SND sep_true`, `STATE` / `POSTCOND`; and
  `thys/vcg/LLVM_Shallow_RS.thy` — `ll_astate = llvm_amemory × ecost`,
  `ll_α`, `llSTATE`, `ll_pto`;
* `thys/lib/Frame_Infer.thy` — `entails` (`⊢`) and its lemma block,
  which the AFP class surface does *not* contain (the extract says so
  twice); wave C's `Ir/SepSolver.lean` consumes it.

The carrier is the one place ledger **D2** is spent: the source's
`ll_astate` is "LLVM memory × credit balance" and ownership carves an
*address* space; ours is "(scalar cells × array cells) × credit balance"
and ownership carves the *name* space. Everything else — the class
stack, `FST`/`SND`, `$`, `GC`, `EXACT`, `↑`, `STATE` — ports with no
shape change at all, which is exactly what the extract's closing "Port
notes" predicted ("the locale, the credit machinery, the frame solver
and the VCG driver are all address-agnostic").

## Judgment calls

**D-j — the class surface is ported as typeclasses, and the carrier is
built compositionally from instances.** The design record's watch item
prefers monomorphic over clever polymorphism, and the alternative was a
single hand-rolled `Assn` with all laws proved once at the concrete
carrier. Typeclasses win here for a reason that is not cleverness: the
source's own carrier is a *product of products of maps*, its instances
are declared exactly that way (`Sep_Algebra_Add.thy` instantiates `fun`,
`option`, `prod` and `tsa_opt`), and `FST`/`SND` — which the credit
machinery is *stated* in terms of — are polymorphic over the two halves
of a product by construction. A monomorphic development would have to
re-prove the associativity/commutativity block once per component and
would leave `FST`/`SND` unable to be stated at all. The polymorphism is
therefore the source's, not ours: four `Prop`-classes, no data, one
instance per type former, and every downstream file sees exactly one
carrier (`AState`).

**D-k — `sep_conj`'s associativity block is proved at `SepAlgebra`, the
class the AFP proves it at.** `StrongerSepAlgebra` would make it two
lines, and the extract notes that every instance in the artifact is in
fact `stronger_sep_algebra`; the weaker proof is kept because it is the
AFP's and because it is what makes `SepAlgebra` a class with content
rather than a way-point.

**D-l — the pure lift is written `⌜Φ⌝` and the credit assertion `¤c`.**
The source writes `↑Φ`; `↑` is Lean's coercion prefix and cannot be
re-bound, so the pure lift takes the bracket spelling every Lean
separation logic uses. The source's `$c` / `$$ name n` are likewise
unavailable — `$` is Lean's anonymous-constructor/antiquotation token —
so the credit assertions are spelled `¤c` / `¤¤ name n`. `□`, `∗`, `⊢`,
`##` are the source's own tokens, all of them Lean-legal. `x ↦ᵥ n` / `a ↦ₐ xs` are ours: the
source's `↿ll_pto x p` is a `dr_assn`-wrapped points-to over addresses
and there is no name-indexed spelling to inherit.

**D-m — an array is *one* cell, not a family.** The source's `ll_range`
is a `sep_set_img` (finite `**`-fold) of single-cell `ll_pto`s over an
address range, because an LLVM array *is* an address range and ownership
of it can be split index by index. Our arrays are named objects: no IR
op can split one (design record §6 has no `alloc`, no pointer
arithmetic, no sub-array), and P5's lowering never needs a sub-range. So
`a ↦ₐ xs` owns a single `tsa_opt`-shaped cell whose value is the whole
list, and carries the length as `xs.length`. `sep_set_img` is not
ported: it has no consumer here, and the index side condition it exists
to support (`p' -ₐ p ∈ I`) is `i < xs.length` in `Triples.lean` — which
is what the extract's port notes prescribe.

**D-n — the abstraction `α` is a bijection.** The source's
`ll_α ≡ lift_α_cost llvm_α` composes a real abstraction function
(`llvm_α`, which turns a concrete block-structured memory into a
separation-algebra element) with a lift that pairs it with the balance.
Ours (`irα`) only re-tags: `Option`-valued partial maps become
`Tsa`-valued ones (`none ↦ ZERO`, `some v ↦ TRIV v`) and the balance is
paired on. That is the whole of it — the IR's `State` is already the
PCM's underlying data (judgment call D-g of `Semantics.lean` chose the
partial-function representation *for* this), so `irα` does the job of
`lift_α_cost` alone and `llvm_α`'s job is empty. The re-tagging is not
cosmetic: `Tsa` is the type the artifact proves `unique_zero` for, and
`Option` is the one it does not.

## The executable gate (ledger D4)

`Gate` below checks the PCM laws by computation at a decidable finite
image of the carrier (`Tsa ℕ` at sampled values, cells restricted to a
name list), with Plausible over sampled cell contents, and carries the
two negative controls the wave asks for: overlapping names do *not*
compose, and credit assertions with different balances are different
assertions.
-/

namespace Lax13Proofs.Refine.Ir

/-! ## 1. The separation-algebra class stack

AFP `Separation_Algebra` (`pre_sep_algebra`, `sep_algebra`) and the
artifact's own two additions (`stronger_sep_algebra`,
`unique_zero_sep_algebra`, `Sep_Algebra_Add.thy`), in the order the
source stacks them. HOL's `class … = zero + plus + fixes sep_disj`
becomes a data class for `##` plus `Prop`-classes for the axioms, with
`Zero`/`Add` as instance arguments — the mathlib idiom `ACost.lean`
already uses for the source's `ordered_comm_monoid_add` sort. -/

/-- The source's disjointness relation `##`, as its own data class (HOL
declares it as a `fixes` of `pre_sep_algebra`; Lean keeps `Zero`/`Add`
from mathlib and adds only this one operation). -/
class SepDisj (α : Type) where
  /-- Two resources are disjoint: they can be combined. -/
  sepDisj : α → α → Prop

@[inherit_doc SepDisj.sepDisj] infix:60 " ## " => SepDisj.sepDisj

/-- AFP `pre_sep_algebra`: a partial commutative monoid whose partiality
is carried by `##`. -/
class PreSepAlgebra (α : Type) [Zero α] [Add α] [SepDisj α] : Prop where
  /-- The source's `sep_disj_zero`. -/
  sep_disj_zero (x : α) : x ## 0
  /-- The source's `sep_disj_commuteI`. -/
  sep_disj_commuteI {x y : α} : x ## y → y ## x
  /-- The source's `sep_add_zero`. -/
  sep_add_zero (x : α) : x + 0 = x
  /-- The source's `sep_add_commute`. -/
  sep_add_commute {x y : α} : x ## y → x + y = y + x
  /-- The source's `sep_add_assoc`. -/
  sep_add_assoc {x y z : α} : x ## y → y ## z → x ## z → x + y + z = x + (y + z)

export PreSepAlgebra (sep_disj_zero sep_disj_commuteI sep_add_zero sep_add_commute sep_add_assoc)

/-- AFP `sep_algebra`: `pre_sep_algebra` plus the two disjointness
laws that make `sep_conj` associative. -/
class SepAlgebra (α : Type) [Zero α] [Add α] [SepDisj α] : Prop extends PreSepAlgebra α where
  /-- The source's `sep_disj_addD1`. -/
  sep_disj_addD1 {x y z : α} : x ## y + z → y ## z → x ## y
  /-- The source's `sep_disj_addI1`. -/
  sep_disj_addI1 {x y z : α} : x ## y + z → y ## z → x + y ## z

export SepAlgebra (sep_disj_addD1 sep_disj_addI1)

/-- `Sep_Algebra_Add.thy`'s `stronger_sep_algebra`: one disjointness law
from which `sep_algebra`'s two follow. Every instance below is in this
class; the extract records that the artifact's own are too. -/
class StrongerSepAlgebra (α : Type) [Zero α] [Add α] [SepDisj α] : Prop
    extends PreSepAlgebra α where
  /-- The source's `sep_add_disj_eq`. -/
  sep_add_disj_eq {x y z : α} : y ## z → (x ## y + z ↔ x ## y ∧ x ## z)

export StrongerSepAlgebra (sep_add_disj_eq)

/-- The source's `subclass sep_algebra by standard auto`. -/
instance StrongerSepAlgebra.toSepAlgebra {α : Type} [Zero α] [Add α] [SepDisj α]
    [StrongerSepAlgebra α] : SepAlgebra α where
  toPreSepAlgebra := inferInstance
  sep_disj_addD1 h hyz := ((sep_add_disj_eq hyz).1 h).1
  sep_disj_addI1 := by
    intro x y z h hyz
    have hxy : x ## y := ((sep_add_disj_eq hyz).1 h).1
    have hxz : x ## z := ((sep_add_disj_eq hyz).1 h).2
    exact sep_disj_commuteI
      ((sep_add_disj_eq hxy).2 ⟨sep_disj_commuteI hxz, sep_disj_commuteI hyz⟩)

/-- `Sep_Algebra_Add.thy`'s `unique_zero_sep_algebra`: nothing overlaps
itself but the empty resource. This is the class the artifact pushes
every named-cell instance into, and it is what makes ownership of a name
exclusive. -/
class UniqueZeroSepAlgebra (α : Type) [Zero α] [Add α] [SepDisj α] : Prop
    extends StrongerSepAlgebra α where
  /-- The source's `unique_zero`. -/
  unique_zero {x : α} : x ## x → x = 0

export UniqueZeroSepAlgebra (unique_zero)

/-! ### The derived disjointness lemmas

AFP `sep_algebra`'s `begin … end` block, the part `sep_conj_assoc`
actually consumes (judgment call D-k). -/

section Derived

variable {α : Type} [Zero α] [Add α] [SepDisj α]

theorem sep_disj_commute [PreSepAlgebra α] {x y : α} : x ## y ↔ y ## x :=
  ⟨sep_disj_commuteI, sep_disj_commuteI⟩

theorem sep_zero_disj [PreSepAlgebra α] (x : α) : (0 : α) ## x :=
  sep_disj_commuteI (sep_disj_zero x)

theorem sep_zero_add [PreSepAlgebra α] (x : α) : 0 + x = x := by
  rw [sep_add_commute (sep_zero_disj x), sep_add_zero]

/-- The source's `sep_disj_addD2`. -/
theorem sep_disj_addD2 [SepAlgebra α] {x y z : α} (h : x ## y + z) (hyz : y ## z) : x ## z := by
  rw [sep_add_commute hyz] at h
  exact sep_disj_addD1 h (sep_disj_commuteI hyz)

/-- The source's `sep_add_disjD`. -/
theorem sep_add_disjD [SepAlgebra α] {x y z : α} (h : x + y ## z) (hxy : x ## y) :
    x ## z ∧ y ## z := by
  have h' : z ## x + y := sep_disj_commuteI h
  exact ⟨sep_disj_commuteI (sep_disj_addD1 h' hxy),
    sep_disj_commuteI (sep_disj_addD2 h' hxy)⟩

/-- The converse of `sep_disj_addI1`, derived: it is what the forward
direction of `sepConj_assoc` needs. -/
theorem sep_disj_addI1' [SepAlgebra α] {x y z : α} (h : x + y ## z) (hxy : x ## y) :
    x ## y + z := by
  have hyz : y ## z := (sep_add_disjD h hxy).2
  have h1 : z ## x + y := sep_disj_commuteI h
  have h2 : z ## y + x := by rwa [sep_add_commute hxy] at h1
  have h3 : z + y ## x := sep_disj_addI1 h2 (sep_disj_commuteI hxy)
  have h4 : x ## z + y := sep_disj_commuteI h3
  rwa [sep_add_commute (sep_disj_commuteI hyz)] at h4

end Derived

/-! ## 2. The assertion connectives

AFP `sep_algebra`'s `sep_conj` / `sep_empty` / `sep_impl` / `sep_true`,
`Sep_Algebra_Add.thy`'s `pred_lift` / `EXACT` / `pure_part`, and
`Frame_Infer.thy`'s `entails`. -/

section Connectives

variable {α : Type} [Zero α] [Add α] [SepDisj α]

/-- The source's `sep_conj`, written `**` / `∧*` there and `∗` here
(design record §5 uses `∗`). -/
def sepConj [SepAlgebra α] (P Q : α → Prop) : α → Prop :=
  fun h => ∃ x y, x ## y ∧ h = x + y ∧ P x ∧ Q y

@[inherit_doc] infixr:60 " ∗ " => sepConj

/-- The source's `sep_empty`, `□`. -/
def emp : α → Prop := fun h => h = 0

@[inherit_doc] notation:max "□" => emp

/-- The source's `sep_impl`, `⟶*`. Ported for surface completeness; the
frame inferencer of wave C does not consume it. -/
def sepImp [SepAlgebra α] (P Q : α → Prop) : α → Prop :=
  fun h => ∀ h', h ## h' → P h' → Q (h + h')

/-- The source's `sep_true`. -/
def sepTrue : α → Prop := fun _ => True

/-- The source's `sep_false`. -/
def sepFalse : α → Prop := fun _ => False

/-- `Sep_Algebra_Add.thy`'s `pred_lift`, the source's `↑Φ`: the pure
fact `Φ`, owning nothing (judgment call D-l). -/
def predLift (Φ : Prop) : α → Prop := fun h => Φ ∧ □ h

@[inherit_doc] notation:max "⌜" Φ "⌝" => predLift Φ

/-- `Sep_Algebra_Add.thy`'s `EXACT h`: the resource is *precisely* `h`. -/
def EXACT (h : α) : α → Prop := fun h' => h' = h

/-- `Sep_Algebra_Add.thy`'s `pure_part`: the assertion is satisfiable. -/
def purePart (P : α → Prop) : Prop := ∃ h, P h

/-- The source's `EXS x. Q x`, existential quantification inside an
assertion. -/
def sepEx {β : Type} (P : β → α → Prop) : α → Prop := fun h => ∃ x, P x h

@[inherit_doc sepEx] syntax "∃ᵃ" ident ", " term : term

macro_rules | `(∃ᵃ $x:ident, $p) => `(sepEx (fun $x => $p))

/-- `Frame_Infer.thy`'s `entails`, `⊢` — *not* part of the AFP class
surface (the extract flags this twice); it is the artifact's own
addition on the same carrier. -/
def entails (P Q : α → Prop) : Prop := ∀ h, P h → Q h

@[inherit_doc] infix:25 " ⊢ " => entails

end Connectives

/-! ### The laws of `∗`, `□`, `⌜⌝`, `EXACT` and `⊢` -/

section ZeroLaws

variable {α : Type} [Zero α]

/-- `Sep_Algebra_Add.thy`'s `EXACT_zero`. -/
@[simp] theorem EXACT_zero : EXACT (0 : α) = □ := rfl

@[simp] theorem predLift_true : (⌜True⌝ : α → Prop) = □ := by
  funext h; exact propext ⟨fun h' => h'.2, fun h' => ⟨trivial, h'⟩⟩

end ZeroLaws

section Laws

variable {α : Type} [Zero α] [Add α] [SepDisj α] [SepAlgebra α]

theorem sepConj_def (P Q : α → Prop) (h : α) :
    (P ∗ Q) h ↔ ∃ x y, x ## y ∧ h = x + y ∧ P x ∧ Q y := Iff.rfl

/-- The source's `sep_conj_commute`. -/
theorem sepConj_comm (P Q : α → Prop) : P ∗ Q = Q ∗ P := by
  have key : ∀ (P Q : α → Prop) h, (P ∗ Q) h → (Q ∗ P) h := by
    rintro P Q h ⟨x, y, hd, rfl, hp, hq⟩
    exact ⟨y, x, sep_disj_commuteI hd, sep_add_commute hd, hq, hp⟩
  funext h; exact propext ⟨key P Q h, key Q P h⟩

/-- The source's `sep_conj_assoc` (judgment call D-k: proved at
`SepAlgebra`, as the AFP does). -/
theorem sepConj_assoc (P Q R : α → Prop) : (P ∗ Q) ∗ R = P ∗ (Q ∗ R) := by
  funext h
  refine propext ⟨?_, ?_⟩
  · rintro ⟨-, z, hd1, rfl, ⟨x, y, hxy, rfl, hp, hq⟩, hr⟩
    obtain ⟨hxz, hyz⟩ := sep_add_disjD hd1 hxy
    exact ⟨x, y + z, sep_disj_addI1' hd1 hxy, sep_add_assoc hxy hyz hxz,
      hp, ⟨y, z, hyz, rfl, hq, hr⟩⟩
  · rintro ⟨x, -, hd1, rfl, hp, ⟨y, z, hyz, rfl, hq, hr⟩⟩
    have hxy : x ## y := sep_disj_addD1 hd1 hyz
    have hxz : x ## z := sep_disj_addD2 hd1 hyz
    exact ⟨x + y, z, sep_disj_addI1 hd1 hyz, (sep_add_assoc hxy hyz hxz).symm,
      ⟨x, y, hxy, rfl, hp, hq⟩, hr⟩

theorem sepConj_left_comm (P Q R : α → Prop) : P ∗ (Q ∗ R) = Q ∗ (P ∗ R) := by
  rw [← sepConj_assoc, sepConj_comm P Q, sepConj_assoc]

/-- The source's `sep_conj_empty` / `sep_conj_empty'`. -/
@[simp] theorem emp_sepConj (P : α → Prop) : □ ∗ P = P := by
  funext h
  refine propext ⟨?_, ?_⟩
  · rintro ⟨x, y, -, rfl, hx, hy⟩
    rw [show x = 0 from hx, sep_zero_add]; exact hy
  · intro hp; exact ⟨0, h, sep_zero_disj h, (sep_zero_add h).symm, rfl, hp⟩

@[simp] theorem sepConj_emp (P : α → Prop) : P ∗ □ = P := by
  rw [sepConj_comm, emp_sepConj]

/-- The source's `sep_conj_impl` in its entailment form. -/
theorem conj_entails_mono {P P' Q Q' : α → Prop} (hp : P ⊢ P') (hq : Q ⊢ Q') :
    P ∗ Q ⊢ P' ∗ Q' := by
  rintro h ⟨x, y, hd, rfl, hx, hy⟩
  exact ⟨x, y, hd, rfl, hp x hx, hq y hy⟩

theorem sepConj_mono_left {P P' Q : α → Prop} (hp : P ⊢ P') : P ∗ Q ⊢ P' ∗ Q :=
  conj_entails_mono hp fun _ h => h

theorem sepConj_mono_right {P Q Q' : α → Prop} (hq : Q ⊢ Q') : P ∗ Q ⊢ P ∗ Q' :=
  conj_entails_mono (fun _ h => h) hq

/-- `Sep_Algebra_Add.thy`'s `EXACT_split`. -/
theorem EXACT_split {a b : α} (h : a ## b) : EXACT (a + b) = EXACT a ∗ EXACT b := by
  funext c
  refine propext ⟨?_, ?_⟩
  · rintro rfl; exact ⟨a, b, h, rfl, rfl, rfl⟩
  · rintro ⟨x, y, -, rfl, rfl, rfl⟩; rfl


/-- The shape every points-to extraction below is an instance of: an
`EXACT` conjunct splits the state into its own resource and a frame. -/
theorem EXACT_sepConj_iff {a : α} {F : α → Prop} {h : α} :
    (EXACT a ∗ F) h ↔ ∃ b, a ## b ∧ h = a + b ∧ F b := by
  constructor
  · rintro ⟨x, y, hd, rfl, rfl, hy⟩; exact ⟨y, hd, rfl, hy⟩
  · rintro ⟨b, hd, rfl, hb⟩; exact ⟨a, b, hd, rfl, rfl, hb⟩

/-- `Sep_Generic_Wp.thy`'s `STATE_extract`, first two clauses, at the
level of the assertion: a pure conjunct is extracted from a `∗`. -/
@[simp] theorem predLift_sepConj_iff {Φ : Prop} {P : α → Prop} {h : α} :
    (⌜Φ⌝ ∗ P) h ↔ Φ ∧ P h := by
  constructor
  · rintro ⟨x, y, -, rfl, ⟨hΦ, hx⟩, hy⟩
    rw [show x = 0 from hx, sep_zero_add]
    exact ⟨hΦ, hy⟩
  · rintro ⟨hΦ, hp⟩
    exact ⟨0, h, sep_zero_disj h, (sep_zero_add h).symm, ⟨hΦ, rfl⟩, hp⟩


/-- Existentials commute with `∗` — the rewrite the while rule uses to
open the body's postcondition. -/
theorem sepEx_sepConj {β : Type} (P : β → α → Prop) (F : α → Prop) :
    (∃ᵃ x, P x) ∗ F = ∃ᵃ x, (P x ∗ F) := by
  funext h
  refine propext ⟨?_, ?_⟩
  · rintro ⟨u, v, hd, rfl, ⟨x, hx⟩, hv⟩; exact ⟨x, u, v, hd, rfl, hx, hv⟩
  · rintro ⟨x, u, v, hd, rfl, hx, hv⟩; exact ⟨u, v, hd, rfl, ⟨x, hx⟩, hv⟩

end Laws

/-! ### `Frame_Infer.thy`'s entailment block

The entailment connective is not part of the AFP class surface, and its
basic lemmas need no algebra at all. -/

section Entails

variable {α : Type}

@[refl] theorem entails_refl (P : α → Prop) : P ⊢ P := fun _ h => h

@[simp] theorem entails_false (Q : α → Prop) : (sepFalse : α → Prop) ⊢ Q := fun _ h => h.elim

@[simp] theorem entails_true (P : α → Prop) : P ⊢ (sepTrue : α → Prop) := fun _ _ => trivial

theorem entails_trans {P Q R : α → Prop} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=
  fun h hp => h₂ h (h₁ h hp)

theorem entails_exI {β : Type} {P : α → Prop} {Q : β → α → Prop} {x : β} (h : P ⊢ Q x) :
    P ⊢ ∃ᵃ y, Q y :=
  fun s hs => ⟨x, h s hs⟩

theorem pure_partI {P : α → Prop} {h : α} (hp : P h) : purePart P := ⟨h, hp⟩

theorem entails_pureI {P Q : α → Prop} (h : purePart P → P ⊢ Q) : P ⊢ Q :=
  fun s hs => h ⟨s, hs⟩ s hs

end Entails

section EntailsSep

variable {α : Type} [Zero α] [Add α] [SepDisj α] [SepAlgebra α]

/-- `Frame_Infer.thy`'s `entails_mp`. -/
theorem entails_mp {P Q Q' F : α → Prop} (h : Q ⊢ Q') (h' : P ⊢ Q ∗ F) : P ⊢ Q' ∗ F :=
  entails_trans h' (conj_entails_mono h (entails_refl F))

end EntailsSep

/-! ## 3. The instances the carrier is built from

`Sep_Algebra_Add.thy` instantiates `tsa_opt`, `fun`, `prod` (and
`option`, which the port notes say to skip in favour of `tsa_opt`). The
credit half is the artifact's `ecost` component of `ll_astate`, whose
`##` is total: credits always compose, and adding them is the monoid
addition `ACost.lean` already provides. -/

/-- `Sep_Algebra_Add.thy`'s `tsa_opt`: "empty, or exactly one owned
value". The port notes prescribe this over `Option`, because `tsa_opt`
is the type the artifact proves `unique_zero` for. -/
inductive Tsa (γ : Type) where
  /-- Nothing is owned. -/
  | zero
  /-- The value `v` is owned. -/
  | triv (v : γ)
  deriving DecidableEq, Repr

namespace Tsa

variable {γ : Type}

instance instZero : Zero (Tsa γ) := ⟨.zero⟩

/-- The source's `a+b ≡ (case (a,b) of (ZERO,x) ⇒ x | (x,ZERO) ⇒ x)`;
HOL leaves the two-owned case unspecified, Lean must be total, and the
value chosen there is never reached under `##`. -/
instance instAdd : Add (Tsa γ) := ⟨fun a b => match a with | .zero => b | .triv v => .triv v⟩

/-- The source's `sep_disj_tsa_opt`: `a ## b ⟷ a = ZERO ∨ b = ZERO`. -/
instance instSepDisj : SepDisj (Tsa γ) := ⟨fun a b => a = 0 ∨ b = 0⟩

/-- `0` is `ZERO`; the constructor is the normal form the checks and
proofs below reduce to. -/
@[simp] theorem zero_eq : (0 : Tsa γ) = .zero := rfl

theorem disj_def {a b : Tsa γ} : a ## b ↔ a = .zero ∨ b = .zero := Iff.rfl

@[simp] theorem zero_add (a : Tsa γ) : Tsa.zero + a = a := rfl

@[simp] theorem triv_add (v : γ) (a : Tsa γ) : Tsa.triv v + a = Tsa.triv v := rfl

@[simp] theorem add_zero (a : Tsa γ) : a + Tsa.zero = a := by cases a <;> rfl

@[simp] theorem triv_ne_zero' (v : γ) : Tsa.triv v ≠ Tsa.zero := by simp

theorem triv_ne_zero (v : γ) : Tsa.triv v ≠ 0 := triv_ne_zero' v

@[simp] theorem zero_disj (a : Tsa γ) : Tsa.zero ## a := Or.inl rfl

@[simp] theorem disj_zero (a : Tsa γ) : a ## Tsa.zero := Or.inr rfl

theorem eq_zero_of_disj_triv {a : Tsa γ} {v : γ} (h : a ## Tsa.triv v) : a = 0 := by
  rcases h with h | h
  · exact h
  · exact absurd h (triv_ne_zero v)

instance instUniqueZeroSepAlgebra : UniqueZeroSepAlgebra (Tsa γ) where
  sep_disj_zero _ := Or.inr rfl
  sep_disj_commuteI h := h.symm
  sep_add_zero x := by cases x <;> rfl
  sep_add_commute := by intro x y h; cases x <;> cases y <;> simp_all [disj_def]
  sep_add_assoc := by intro x y z hxy hyz hxz; cases x <;> cases y <;> cases z <;>
    simp_all [disj_def]
  sep_add_disj_eq := by intro x y z hyz; cases x <;> cases y <;> cases z <;> simp [disj_def]
  unique_zero h := by rcases h with h | h <;> exact h

/-- The tag of a partial map's value: `none ↦ ZERO`, `some v ↦ TRIV v`.
This is the whole of the abstraction function `irα` (judgment call
D-n). -/
def ofOption : Option γ → Tsa γ
  | none => .zero
  | some v => .triv v

@[simp] theorem ofOption_none : ofOption (none : Option γ) = 0 := rfl

@[simp] theorem ofOption_some (v : γ) : ofOption (some v) = .triv v := rfl

theorem ofOption_eq_triv_iff {o : Option γ} {v : γ} : ofOption o = .triv v ↔ o = some v := by
  cases o <;> simp [ofOption]

theorem ofOption_eq_zero_iff {o : Option γ} : ofOption o = 0 ↔ o = none := by
  cases o <;> simp [ofOption]

theorem ne_none_of_ofOption_eq_triv {o : Option γ} {v : γ} (h : ofOption o = .triv v) :
    o ≠ none := by
  rw [ofOption_eq_triv_iff] at h; simp [h]

end Tsa

/-! ### Maps and pairs

`Sep_Algebra_Add.thy`'s `fun` and `prod` instances. `Zero` and `Add`
come from mathlib's `Pi`/`Prod` instances — the statements are the
source's, the algebra is mathlib's (fidelity note: the *shape*
`(f + g) x = f x + g x`, `0 x = 0` is identical, so nothing is
re-proved that mathlib already has). -/

instance instSepDisjPi {ι γ : Type} [SepDisj γ] : SepDisj (ι → γ) :=
  ⟨fun f g => ∀ x, f x ## g x⟩

theorem sepDisj_pi_def {ι γ : Type} [SepDisj γ] {f g : ι → γ} :
    f ## g ↔ ∀ x, f x ## g x := Iff.rfl

instance instUniqueZeroSepAlgebraPi {ι γ : Type} [Zero γ] [Add γ] [SepDisj γ]
    [UniqueZeroSepAlgebra γ] : UniqueZeroSepAlgebra (ι → γ) where
  sep_disj_zero f x := sep_disj_zero (f x)
  sep_disj_commuteI h x := sep_disj_commuteI (h x)
  sep_add_zero f := funext fun x => sep_add_zero (f x)
  sep_add_commute h := funext fun x => sep_add_commute (h x)
  sep_add_assoc h₁ h₂ h₃ := funext fun x => sep_add_assoc (h₁ x) (h₂ x) (h₃ x)
  sep_add_disj_eq h := by
    constructor
    · intro h' ; exact ⟨fun x => ((sep_add_disj_eq (h x)).1 (h' x)).1,
        fun x => ((sep_add_disj_eq (h x)).1 (h' x)).2⟩
    · rintro ⟨h₁, h₂⟩ x; exact (sep_add_disj_eq (h x)).2 ⟨h₁ x, h₂ x⟩
  unique_zero h := funext fun x => unique_zero (h x)

instance instSepDisjProd {α β : Type} [SepDisj α] [SepDisj β] : SepDisj (α × β) :=
  ⟨fun p q => p.1 ## q.1 ∧ p.2 ## q.2⟩

theorem sepDisj_prod_def {α β : Type} [SepDisj α] [SepDisj β] {p q : α × β} :
    p ## q ↔ p.1 ## q.1 ∧ p.2 ## q.2 := Iff.rfl

instance instStrongerSepAlgebraProd {α β : Type} [Zero α] [Add α] [SepDisj α]
    [StrongerSepAlgebra α] [Zero β] [Add β] [SepDisj β] [StrongerSepAlgebra β] :
    StrongerSepAlgebra (α × β) where
  sep_disj_zero p := ⟨sep_disj_zero p.1, sep_disj_zero p.2⟩
  sep_disj_commuteI h := ⟨sep_disj_commuteI h.1, sep_disj_commuteI h.2⟩
  sep_add_zero p := Prod.ext (sep_add_zero p.1) (sep_add_zero p.2)
  sep_add_commute h := Prod.ext (sep_add_commute h.1) (sep_add_commute h.2)
  sep_add_assoc h₁ h₂ h₃ :=
    Prod.ext (sep_add_assoc h₁.1 h₂.1 h₃.1) (sep_add_assoc h₁.2 h₂.2 h₃.2)
  sep_add_disj_eq h := by
    constructor
    · intro h'
      exact ⟨⟨((sep_add_disj_eq h.1).1 h'.1).1, ((sep_add_disj_eq h.2).1 h'.2).1⟩,
        ⟨((sep_add_disj_eq h.1).1 h'.1).2, ((sep_add_disj_eq h.2).1 h'.2).2⟩⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨(sep_add_disj_eq h.1).2 ⟨h₁.1, h₂.1⟩, (sep_add_disj_eq h.2).2 ⟨h₁.2, h₂.2⟩⟩

/-- The credit half of `ll_astate`: credits *always* compose, and
composing them is addition. This is the one component that is not
`unique_zero` — owning credits twice is owning twice the credits. -/
instance instSepDisjACost {κ γ : Type} : SepDisj (ACost κ γ) := ⟨fun _ _ => True⟩

@[simp] theorem sepDisj_acost {κ γ : Type} (a b : ACost κ γ) : a ## b := trivial

instance instStrongerSepAlgebraACost {κ γ : Type} [AddCommMonoid γ] :
    StrongerSepAlgebra (ACost κ γ) where
  sep_disj_zero _ := trivial
  sep_disj_commuteI _ := trivial
  sep_add_zero := _root_.add_zero
  sep_add_commute _ := add_comm _ _
  sep_add_assoc _ _ _ := add_assoc _ _ _
  sep_add_disj_eq _ := by simp

/-! ## 4. `FST` and `SND`

`Sep_Generic_Wp.thy`, verbatim: lift an assertion over one half of a
product state, forcing the other half to `0`. This is how `$c` and `GC`
(which own only credits) compose by `∗` with points-to assertions (which
own only cells). -/

section FstSnd

variable {α β : Type}

/-- The source's `FST`. -/
def FST [Zero β] (P : α → Prop) : α × β → Prop := fun p => P p.1 ∧ p.2 = 0

/-- The source's `SND`. -/
def SND [Zero α] (P : β → Prop) : α × β → Prop := fun p => p.1 = 0 ∧ P p.2

variable [Zero α] [Add α] [SepDisj α] [StrongerSepAlgebra α]
variable [Zero β] [Add β] [SepDisj β] [StrongerSepAlgebra β]

/-- The source's `FST_conj_conv`. -/
theorem FST_sepConj (P Q : α → Prop) : (FST P ∗ FST Q : α × β → Prop) = FST (P ∗ Q) := by
  funext p
  refine propext ⟨?_, ?_⟩
  · rintro ⟨x, y, hd, rfl, ⟨hx, hx0⟩, ⟨hy, hy0⟩⟩
    exact ⟨⟨x.1, y.1, hd.1, rfl, hx, hy⟩, by rw [Prod.snd_add, hx0, hy0, sep_add_zero]⟩
  · rintro ⟨⟨x, y, hd, hxy, hx, hy⟩, hp0⟩
    refine ⟨(x, 0), (y, 0), ⟨hd, sep_disj_zero 0⟩, ?_, ⟨hx, rfl⟩, ⟨hy, rfl⟩⟩
    exact Prod.ext (by simpa using hxy) (by simpa [sep_zero_add] using hp0)

/-- The source's `SND_conj_conv`. -/
theorem SND_sepConj (P Q : β → Prop) : (SND P ∗ SND Q : α × β → Prop) = SND (P ∗ Q) := by
  funext p
  refine propext ⟨?_, ?_⟩
  · rintro ⟨x, y, hd, rfl, ⟨hx0, hx⟩, ⟨hy0, hy⟩⟩
    exact ⟨by rw [Prod.fst_add, hx0, hy0, sep_add_zero], ⟨x.2, y.2, hd.2, rfl, hx, hy⟩⟩
  · rintro ⟨hp0, ⟨x, y, hd, hxy, hx, hy⟩⟩
    refine ⟨(0, x), (0, y), ⟨sep_disj_zero 0, hd⟩, ?_, ⟨rfl, hx⟩, ⟨rfl, hy⟩⟩
    exact Prod.ext (by simpa [sep_zero_add] using hp0) (by simpa using hxy)

/-- A `FST` and a `SND` assertion compose to the obvious pair
assertion — the reason the credit machinery can be stated separately
from the state machinery at all. -/
theorem FST_SND_sepConj_iff (P : α → Prop) (Q : β → Prop) (p : α × β) :
    (FST P ∗ SND Q) p ↔ P p.1 ∧ Q p.2 := by
  constructor
  · rintro ⟨x, y, -, rfl, ⟨hx, hx0⟩, ⟨hy0, hy⟩⟩
    rw [Prod.fst_add, Prod.snd_add, hy0, hx0, sep_add_zero, sep_zero_add]
    exact ⟨hx, hy⟩
  · rintro ⟨hp, hq⟩
    refine ⟨(p.1, 0), (0, p.2), ⟨sep_disj_zero p.1, sep_zero_disj p.2⟩, ?_, ⟨hp, rfl⟩, ⟨rfl, hq⟩⟩
    exact Prod.ext (by simp [sep_add_zero]) (by simp [sep_zero_add])

end FstSnd

section FstSndZero

variable {α β : Type} [Zero α] [Zero β]

@[simp] theorem FST_emp : (FST □ : α × β → Prop) = □ := by
  funext p
  refine propext ⟨?_, ?_⟩
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
  · rintro rfl; exact ⟨rfl, rfl⟩

@[simp] theorem SND_emp : (SND □ : α × β → Prop) = □ := by
  funext p
  refine propext ⟨?_, ?_⟩
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
  · rintro rfl; exact ⟨rfl, rfl⟩

end FstSndZero

/-! ## 5. The IR's carrier

`ll_astate = llvm_amemory × ecost` at named cells (ledger D2): the
scalar cells, the array cells, and the credit balance. -/

/-- A map from names to owned values: the source's memory component, at
names. -/
abbrev Cells (γ : Type) : Type := String → Tsa γ

/-- The cells owning exactly the name `x`, holding `v`. -/
def Cells.single {γ : Type} (x : String) (v : γ) : Cells γ :=
  fun y => if y = x then .triv v else 0

/-- The cells with the name `x` given up. -/
def Cells.erase {γ : Type} (V : Cells γ) (x : String) : Cells γ :=
  fun y => if y = x then 0 else V y

/-- The cells with the name `x` set to `v`. -/
def Cells.update {γ : Type} (V : Cells γ) (x : String) (v : γ) : Cells γ :=
  fun y => if y = x then .triv v else V y

namespace Cells

variable {γ : Type}

@[simp] theorem single_self (x : String) (v : γ) : single x v x = .triv v := by simp [single]

@[simp] theorem single_ne {x y : String} (h : y ≠ x) (v : γ) : single x v y = 0 := by
  simp [single, h]

@[simp] theorem erase_self (V : Cells γ) (x : String) : V.erase x x = 0 := by simp [erase]

@[simp] theorem erase_ne {x y : String} (h : y ≠ x) (V : Cells γ) : V.erase x y = V y := by
  simp [erase, h]

@[simp] theorem update_self (V : Cells γ) (x : String) (v : γ) : (V.update x v) x = .triv v := by
  simp [update]

@[simp] theorem update_ne {x y : String} (h : y ≠ x) (V : Cells γ) (v : γ) :
    (V.update x v) y = V y := by simp [update, h]

@[simp] theorem erase_update (V : Cells γ) (x : String) (v : γ) :
    (V.update x v).erase x = V.erase x := by
  funext y
  rcases eq_or_ne y x with rfl | h
  · simp
  · simp [h]

/-- The decomposition every points-to extraction turns on: owning `x`
splits the map into the single cell and the rest. -/
theorem single_add_erase {V : Cells γ} {x : String} {v : γ} (h : V x = .triv v) :
    single x v + V.erase x = V := by
  funext y
  rcases eq_or_ne y x with rfl | hy
  · simpa using h.symm
  · simp [hy]

theorem single_disj_erase (V : Cells γ) (x : String) (v : γ) : single x v ## V.erase x := by
  intro y
  rcases eq_or_ne y x with rfl | hy
  · simp
  · simp [hy]

end Cells

/-- The heap's ownership component: one `tsa_opt` cell per index of the
reserved heap array (decision D-A1 of
`plans/word-ram/tower-expansion/p4.5-design.md` §4.3). This is the
per-index granularity judgment call D-m declined for *named* arrays —
`ll_range`, at the one name that has it. `Refine/Ir/Heap.lean` carries
the range assertion `p ↦ₕ xs` built on it. -/
abbrev HCells : Type := ℕ → Tsa Val

/-- The IR's assertion-level state: the source's `ll_astate`, with named
cells in place of an address-indexed memory (ledger D2). The memory half
is scalars, named arrays and the reserved heap (decision D-A1); the
credit half is unchanged, so `¤c` and `GC` still read `SND`. -/
abbrev AState : Type := (Cells Val × Cells (List Val) × HCells) × ECost

/-- The IR's assertions: the source's `ll_assn`. -/
abbrev Assn : Type := AState → Prop

/-- The scalar cells of a state. -/
def vcells (s : State) : Cells Val := fun x => Tsa.ofOption (s.vars x)

/-- The one reserved array name the P4.5 heap lives at (design note
§4.3, decision D-A1). It is named in exactly this one place; every use
site goes through this definition, never through the literal.

The name is *unownable* in the whole-name view below (`acells` sends it
to `Tsa.zero`), which is what makes the heap's per-index view a genuine
separating conjunct rather than a second view of the same resource. See
`Refine/Ir/Heap.lean` for the range assertion and for the theorem
(`not_irSTATE_ptoArr_heapName`) that discharges the disjointness this
partition buys. -/
def heapName : String := "$heap"

/-- The array cells of a state — *except* the reserved heap name, which
this view does not own (decision D-A1). Ownership of the heap is
per-index and lives in the `HCells` component; if the name were ownable
here as well, the two views would not be disjoint in the underlying
`Ir.State` and framing a range across a whole-name `aset` would be
unsound. -/
def acells (s : State) : Cells (List Val) :=
  fun a => if a = heapName then 0 else Tsa.ofOption (s.arrs a)

/-- The per-index view of the reserved heap array. An index outside the
array — or a state with no heap array at all — owns nothing. -/
def hcells (s : State) : HCells :=
  fun i => Tsa.ofOption ((s.arrs heapName).bind (fun xs => xs[i]?))

/-- The abstraction function: the source's `ll_α ≡ lift_α_cost llvm_α`.
Judgment call D-n — ours re-tags the two partial maps, adds the reserved
array's per-index view (decision D-A1) and pairs on the balance, and
that is all it does. -/
def irα (p : State × ECost) : AState := ((vcells p.1, acells p.1, hcells p.1), p.2)

@[simp] theorem vcells_apply (s : State) (x : String) : vcells s x = Tsa.ofOption (s.vars x) := rfl

@[simp] theorem acells_apply {a : String} (h : a ≠ heapName) (s : State) :
    acells s a = Tsa.ofOption (s.arrs a) := by simp [acells, h]

/-- The heap name owns nothing in the whole-name view: the soundness
side of decision D-A1. -/
@[simp] theorem acells_heapName (s : State) : acells s heapName = 0 := by simp [acells]

/-- Whatever a cell of the whole-name view holds, it is not the heap
name — the form the extraction lemmas below consume. -/
theorem ne_heapName_of_acells_eq_triv {s : State} {a : String} {xs : List Val}
    (h : acells s a = .triv xs) : a ≠ heapName := by
  rintro rfl; rw [acells_heapName] at h; exact absurd h (by simp)

@[simp] theorem vcells_setVar (s : State) (x : String) (v : Val) :
    vcells (s.setVar x v) = (vcells s).update x v := by
  funext y
  rcases eq_or_ne y x with rfl | h
  · simp [Cells.update]
  · simp [Cells.update, h]

@[simp] theorem acells_setVar (s : State) (x : String) (v : Val) :
    acells (s.setVar x v) = acells s := rfl

@[simp] theorem vcells_setArr (s : State) (a : String) (xs : List Val) :
    vcells (s.setArr a xs) = vcells s := rfl

@[simp] theorem acells_setArr {a : String} (ha : a ≠ heapName) (s : State) (xs : List Val) :
    acells (s.setArr a xs) = (acells s).update a xs := by
  funext b
  rcases eq_or_ne b a with rfl | h
  · simp [Cells.update, acells, ha]
  · rcases eq_or_ne b heapName with rfl | hb
    · simp [Cells.update, h, acells]
    · simp [Cells.update, h, acells, hb]

/-- Writing the reserved heap array is invisible to the whole-name view.
This is the equation that lets `Heap.lean`'s write triple keep the array
frame untouched. -/
@[simp] theorem acells_setArr_heapName (s : State) (xs : List Val) :
    acells (s.setArr heapName xs) = acells s := by
  funext b
  rcases eq_or_ne b heapName with rfl | hb
  · simp
  · simp [acells, hb, State.setArr]

theorem hcells_apply (s : State) (i : ℕ) :
    hcells s i = Tsa.ofOption ((s.arrs heapName).bind (fun xs => xs[i]?)) := rfl

/-- A state with no heap array owns no heap. -/
theorem hcells_of_none {s : State} (h : s.arrs heapName = none) : hcells s = 0 := by
  funext i; simp [hcells, h]

@[simp] theorem hcells_setVar (s : State) (x : String) (v : Val) :
    hcells (s.setVar x v) = hcells s := rfl

/-- Writing any *other* array leaves the heap view alone — the equation
that keeps every landed array triple valid at the widened carrier. -/
@[simp] theorem hcells_setArr {a : String} (ha : a ≠ heapName) (s : State) (xs : List Val) :
    hcells (s.setArr a xs) = hcells s := by
  funext i
  simp [hcells, State.arrs_setArr, Ne.symm ha]

/-- …and writing the heap array replaces the whole view. -/
@[simp] theorem hcells_setArr_heapName (s : State) (ys : List Val) :
    hcells (s.setArr heapName ys) = fun i => Tsa.ofOption ys[i]? := by
  funext i
  simp [hcells, State.arrs_setArr]

@[simp] theorem irα_mk (s : State) (cr : ECost) :
    irα (s, cr) = ((vcells s, acells s, hcells s), cr) := rfl

/-! ## 6. The assertion vocabulary of the IR

`¤c` (the source's `$c`), `GC`, and the two points-to assertions. -/

/-- The source's `time_credits_assn`: `($c) ≡ SND (EXACT c)`. -/
def credits (c : ECost) : Assn := SND (EXACT c)

@[inherit_doc] prefix:900 "¤" => credits

/-- The artifact's `ll_cost_assn`, `$$ name n ≡ $lift_acost (cost name n)`, written `¤¤`:
`n` units of one currency, as credits. This is what every op triple of
`Triples.lean` is priced in. -/
def costCredits (n : String) (k : ℕ) : Assn := ¤(ACost.cost n (k : ℕ∞))

@[inherit_doc costCredits] notation:max "¤¤" n:max k:max => costCredits n k

/-- The source's `GC ≡ SND sep_true`: the absorber of leftover credits. -/
def GC : Assn := SND sepTrue

/-- `x ↦ᵥ v`: the scalar cell `x` exists and holds `v`, and this
assertion owns the name. The source's `ll_pto` at a name instead of an
address (ledger D2), through the same `FST` (a points-to carries no
credits of its own). -/
def ptoVar (x : String) (v : Val) : Assn := FST (FST (EXACT (Cells.single x v)))

@[inherit_doc] infix:70 " ↦ᵥ " => ptoVar

/-- `a ↦ₐ xs`: the array `a` exists and holds `xs`, and this assertion
owns the name *and* the length (judgment call D-m: one cell, not a
family). It owns no heap cell: the extra `FST` is decision D-A1's third
memory component, and `a = heapName` is unsatisfiable here by
`acells_heapName`. -/
def ptoArr (a : String) (xs : List Val) : Assn := FST (SND (FST (EXACT (Cells.single a xs))))

@[inherit_doc] infix:70 " ↦ₐ " => ptoArr

/-! ### `GC` and the credit laws (`Sep_Generic_Wp.thy`) -/

@[simp] theorem GC_absorb : GC ∗ GC = GC := by
  show SND sepTrue ∗ SND sepTrue = SND sepTrue
  rw [SND_sepConj]
  congr 1
  funext c
  exact propext ⟨fun _ => trivial, fun _ => ⟨c, 0, trivial, (sep_add_zero c).symm, trivial, trivial⟩⟩

theorem entails_GC (c : ECost) : ¤c ⊢ GC := by
  rintro p ⟨h0, rfl⟩; exact ⟨h0, trivial⟩

theorem empty_ent_GC : (□ : Assn) ⊢ GC := by
  rintro p rfl; exact ⟨rfl, trivial⟩

/-- Credits split and merge: the law `Triples.lean`'s per-iteration
accounting runs on. -/
theorem credits_add (c c' : ECost) : ¤(c + c') = (¤c ∗ ¤c') := by
  show SND (EXACT (c + c')) = SND (EXACT c) ∗ SND (EXACT c')
  rw [SND_sepConj, EXACT_split (sepDisj_acost c c')]

@[simp] theorem credits_zero : ¤(0 : ECost) = (□ : Assn) := by
  rw [credits, EXACT_zero, SND_emp]

theorem costCredits_def (n : String) (k : ℕ) : ¤¤n k = ¤(ACost.cost n (k : ℕ∞)) := rfl

/-! ### Extraction: what ownership of a name gives you

The three lemmas every triple in `Triples.lean` is proved by. Each is an
`EXACT`-split (`EXACT_sepConj_iff`) read through `FST`/`SND`. -/

/-- What a points-to assertion says on the nose: it owns exactly the one
cell, no arrays, no heap and no credits. -/
theorem ptoVar_apply {x : String} {v : Val} {V : Cells Val} {Ar : Cells (List Val)}
    {H : HCells} {cr : ECost} :
    (x ↦ᵥ v) ((V, Ar, H), cr) ↔ V = Cells.single x v ∧ Ar = 0 ∧ H = 0 ∧ cr = 0 :=
  ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, congrArg Prod.fst h2, congrArg Prod.snd h2, h3⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, Prod.ext h2 h3⟩, h4⟩⟩

theorem ptoArr_apply {a : String} {xs : List Val} {V : Cells Val} {Ar : Cells (List Val)}
    {H : HCells} {cr : ECost} :
    (a ↦ₐ xs) ((V, Ar, H), cr) ↔ V = 0 ∧ Ar = Cells.single a xs ∧ H = 0 ∧ cr = 0 :=
  ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩⟩

theorem credits_apply {k : ECost} {V : Cells Val} {Ar : Cells (List Val)} {H : HCells}
    {cr : ECost} : (¤k) ((V, Ar, H), cr) ↔ V = 0 ∧ Ar = 0 ∧ H = 0 ∧ cr = k :=
  ⟨fun ⟨h1, h2⟩ => ⟨congrArg Prod.fst h1, congrArg (fun p => p.2.1) h1,
      congrArg (fun p => p.2.2) h1, h2⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨Prod.ext h1 (Prod.ext h2 h3), h4⟩⟩

theorem ptoVar_sepConj_iff {x : String} {v : Val} {F : Assn} {V : Cells Val}
    {Ar : Cells (List Val)} {H : HCells} {cr : ECost} :
    ((x ↦ᵥ v) ∗ F) ((V, Ar, H), cr) ↔ V x = .triv v ∧ F ((V.erase x, Ar, H), cr) := by
  constructor
  · rintro ⟨⟨⟨pv, pa, ph⟩, pc⟩, ⟨⟨qv, qa, qh⟩, qc⟩, hd, hpq, hp, hq⟩
    obtain ⟨hp1, hp2, hp3, hp4⟩ := ptoVar_apply.1 hp
    subst hp1; subst hp2; subst hp3; subst hp4
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at hpq
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hpq
    have hqx : qv x = 0 := by
      have hx : Cells.single x v x ## qv x := hd.1.1 x
      rw [Cells.single_self] at hx
      exact Tsa.eq_zero_of_disj_triv (sep_disj_commuteI hx)
    refine ⟨by simp [hqx], ?_⟩
    have e1 : (Cells.single x v + qv).erase x = qv := by
      funext y
      rcases eq_or_ne y x with rfl | hy
      · simp [hqx]
      · simp [hy]
    rw [e1, sep_zero_add, sep_zero_add, sep_zero_add]
    exact hq
  · rintro ⟨hVx, hF⟩
    refine ⟨((Cells.single x v, 0, 0), 0), ((V.erase x, Ar, H), cr),
      ⟨⟨Cells.single_disj_erase V x v, fun b => Tsa.zero_disj _, fun i => Tsa.zero_disj _⟩,
        trivial⟩, ?_, ⟨⟨rfl, rfl⟩, rfl⟩, hF⟩
    show ((V, Ar, H), cr) = ((Cells.single x v, 0, 0), 0) + ((V.erase x, Ar, H), cr)
    rw [Prod.mk_add_mk, Prod.mk_add_mk, Prod.mk_add_mk, Cells.single_add_erase hVx,
      sep_zero_add, sep_zero_add, sep_zero_add]

theorem ptoArr_sepConj_iff {a : String} {xs : List Val} {F : Assn} {V : Cells Val}
    {Ar : Cells (List Val)} {H : HCells} {cr : ECost} :
    ((a ↦ₐ xs) ∗ F) ((V, Ar, H), cr) ↔ Ar a = .triv xs ∧ F ((V, Ar.erase a, H), cr) := by
  constructor
  · rintro ⟨⟨⟨pv, pa, ph⟩, pc⟩, ⟨⟨qv, qa, qh⟩, qc⟩, hd, hpq, hp, hq⟩
    obtain ⟨hp1, hp2, hp3, hp4⟩ := ptoArr_apply.1 hp
    subst hp1; subst hp2; subst hp3; subst hp4
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at hpq
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hpq
    have hqa : qa a = 0 := by
      have hx : Cells.single a xs a ## qa a := hd.1.2.1 a
      rw [Cells.single_self] at hx
      exact Tsa.eq_zero_of_disj_triv (sep_disj_commuteI hx)
    refine ⟨by simp [hqa], ?_⟩
    have e1 : (Cells.single a xs + qa).erase a = qa := by
      funext b
      rcases eq_or_ne b a with rfl | hb
      · simp [hqa]
      · simp [hb]
    rw [e1, sep_zero_add, sep_zero_add, sep_zero_add]
    exact hq
  · rintro ⟨hAra, hF⟩
    refine ⟨((0, Cells.single a xs, 0), 0), ((V, Ar.erase a, H), cr),
      ⟨⟨fun y => Tsa.zero_disj _, Cells.single_disj_erase Ar a xs, fun i => Tsa.zero_disj _⟩,
        trivial⟩, ?_, ⟨⟨rfl, rfl, rfl⟩, rfl⟩, hF⟩
    show ((V, Ar, H), cr) = ((0, Cells.single a xs, 0), 0) + ((V, Ar.erase a, H), cr)
    rw [Prod.mk_add_mk, Prod.mk_add_mk, Prod.mk_add_mk, Cells.single_add_erase hAra,
      sep_zero_add, sep_zero_add, sep_zero_add]

theorem credits_sepConj_iff {k : ECost} {F : Assn} {V : Cells Val} {Ar : Cells (List Val)}
    {H : HCells} {cr : ECost} :
    ((¤k) ∗ F) ((V, Ar, H), cr) ↔ ∃ cr₂, cr = k + cr₂ ∧ F ((V, Ar, H), cr₂) := by
  constructor
  · rintro ⟨⟨⟨pv, pa, ph⟩, pc⟩, ⟨⟨qv, qa, qh⟩, qc⟩, hd, hpq, hp, hq⟩
    obtain ⟨hp1, hp2, hp3, hp4⟩ := credits_apply.1 hp
    subst hp1; subst hp2; subst hp3; subst hp4
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at hpq
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hpq
    refine ⟨qc, rfl, ?_⟩
    rw [sep_zero_add, sep_zero_add, sep_zero_add]
    exact hq
  · rintro ⟨cr₂, rfl, hF⟩
    refine ⟨((0, 0, 0), k), ((V, Ar, H), cr₂),
      ⟨⟨fun _ => Tsa.zero_disj _, fun _ => Tsa.zero_disj _, fun _ => Tsa.zero_disj _⟩,
        trivial⟩, ?_, ⟨rfl, rfl⟩, hF⟩
    show ((V, Ar, H), k + cr₂) = ((0, 0, 0), k) + ((V, Ar, H), cr₂)
    rw [Prod.mk_add_mk, Prod.mk_add_mk, Prod.mk_add_mk, sep_zero_add, sep_zero_add, sep_zero_add]

/-! ### Negative controls at the assertion level

Ownership of a name is exclusive, and credits are not fungible with
nothing. -/

/-- Two assertions cannot both own the same scalar name. -/
@[simp] theorem ptoVar_sepConj_self (x : String) (v w : Val) :
    ((x ↦ᵥ v) ∗ (x ↦ᵥ w)) = (sepFalse : Assn) := by
  funext h
  obtain ⟨⟨V, Ar, H⟩, cr⟩ := h
  refine propext ⟨?_, fun h' => h'.elim⟩
  rw [ptoVar_sepConj_iff]
  rintro ⟨-, h2⟩
  rw [ptoVar_apply] at h2
  have hx := congrFun h2.1 x
  simp at hx

/-- Two assertions cannot both own the same array name. -/
@[simp] theorem ptoArr_sepConj_self (a : String) (xs ys : List Val) :
    ((a ↦ₐ xs) ∗ (a ↦ₐ ys)) = (sepFalse : Assn) := by
  funext h
  obtain ⟨⟨V, Ar, H⟩, cr⟩ := h
  refine propext ⟨?_, fun h' => h'.elim⟩
  rw [ptoArr_sepConj_iff]
  rintro ⟨-, h2⟩
  rw [ptoArr_apply] at h2
  have ha := congrFun h2.2.1 a
  simp at ha

/-- Distinct names compose, and the composite owns both. -/
theorem ptoVar_sepConj_ne {x y : String} (h : x ≠ y) (v w : Val) (V : Cells Val)
    (Ar : Cells (List Val)) (H : HCells) (cr : ECost)
    (hx : V x = .triv v) (hy : V y = .triv w)
    (hrest : ∀ z, z ≠ x → z ≠ y → V z = 0) (hAr : Ar = 0) (hH : H = 0) (hcr : cr = 0) :
    ((x ↦ᵥ v) ∗ (y ↦ᵥ w)) ((V, Ar, H), cr) := by
  rw [ptoVar_sepConj_iff]
  refine ⟨hx, ?_⟩
  rw [ptoVar_apply]
  refine ⟨?_, hAr, hH, hcr⟩
  funext z
  rcases eq_or_ne z x with rfl | hzx
  · simp [Cells.single_ne h]
  rcases eq_or_ne z y with rfl | hzy
  · simp [hzx, hy]
  · simp [hzx, hzy, hrest z hzx hzy]

/-- Credit assertions with different balances are different assertions:
credits are not fungible. -/
theorem credits_injective : Function.Injective credits := by
  intro c c' h
  have : (¤c) ((0, 0, 0), c) := ⟨rfl, rfl⟩
  rw [h] at this
  exact this.2

/-- `∗` is associative, as an `ac_rfl`-usable fact. -/
instance instAssociativeSepConj {α : Type} [Zero α] [Add α] [SepDisj α] [SepAlgebra α] :
    Std.Associative (sepConj (α := α)) := ⟨sepConj_assoc⟩

/-- `∗` is commutative, as an `ac_rfl`-usable fact: together with the
instance above this is what lets a permutation of conjuncts be closed by
`ac_rfl` instead of by hand. -/
instance instCommutativeSepConj {α : Type} [Zero α] [Add α] [SepDisj α] [SepAlgebra α] :
    Std.Commutative (sepConj (α := α)) := ⟨sepConj_comm⟩

/-! ## 7. `STATE` and `POSTCOND`

`Sep_Generic_Wp.thy` verbatim, with the IR's abbreviations in place of
`llSTATE` / `llPOST`. -/

/-- The source's `STATE α P s ≡ P (α s)`. -/
def STATE {σ A : Type} (α : σ → A) (P : A → Prop) (s : σ) : Prop := P (α s)

/-- The source's `POSTCOND`: definitionally `STATE`, tagged so a VCG can
tell a postcondition target from a precondition. -/
def POSTCOND {σ A : Type} (α : σ → A) (P : A → Prop) (s : σ) : Prop := STATE α P s

theorem POSTCOND_def {σ A : Type} (α : σ → A) (P : A → Prop) (s : σ) :
    POSTCOND α P s = STATE α P s := rfl

/-- The source's `llSTATE`. -/
abbrev irSTATE : Assn → State × ECost → Prop := STATE irα

/-- The source's `llPOST`. -/
abbrev irPOST : Assn → State × ECost → Prop := POSTCOND irα

theorem STATE_def {σ A : Type} (α : σ → A) (P : A → Prop) (s : σ) :
    STATE α P s = P (α s) := rfl

/-- `Sep_Generic_Wp.thy`'s `STATE_extract`, all four clauses. -/
@[simp] theorem STATE_pure {σ A : Type} [Zero A] (α : σ → A) (Φ : Prop) (s : σ) :
    STATE α ⌜Φ⌝ s ↔ Φ ∧ STATE α □ s := Iff.rfl

@[simp] theorem STATE_pure_sepConj {σ A : Type} [Zero A] [Add A] [SepDisj A] [SepAlgebra A]
    (α : σ → A) (Φ : Prop) (P : A → Prop) (s : σ) :
    STATE α (⌜Φ⌝ ∗ P) s ↔ Φ ∧ STATE α P s := predLift_sepConj_iff

@[simp] theorem STATE_ex {σ A β : Type} (α : σ → A) (Q : β → A → Prop) (s : σ) :
    STATE α (∃ᵃ x, Q x) s ↔ ∃ x, STATE α (Q x) s := Iff.rfl

@[simp] theorem STATE_false {σ A : Type} (α : σ → A) (s : σ) :
    STATE α (sepFalse : A → Prop) s ↔ False := Iff.rfl

/-- `Sep_Generic_Wp.thy`'s `start_entailsE`: the rule that turns a state
fact into an entailment goal. -/
theorem start_entailsE {σ A : Type} {α : σ → A} {P P' : A → Prop} {s : σ}
    (h : STATE α P s) (hent : P ⊢ P') : STATE α P' s :=
  hent _ h

/-! ### The IR's extraction lemmas, at `irSTATE`

These four are the entire interface `Triples.lean` uses to get from an
assertion to a fact about an `Ir.State`, and back. -/

/-- Owning `x ↦ᵥ v` means the cell exists and holds `v`. -/
theorem ptoVar_vars {x : String} {v : Val} {F : Assn} {s : State} {cr : ECost}
    (h : irSTATE ((x ↦ᵥ v) ∗ F) (s, cr)) : s.vars x = some v := by
  have h' : ((x ↦ᵥ v) ∗ F) ((vcells s, acells s, hcells s), cr) := h
  rw [ptoVar_sepConj_iff] at h'
  exact Tsa.ofOption_eq_triv_iff.1 h'.1

/-- …and writing it preserves the frame. -/
theorem ptoVar_setVar {x : String} {v n : Val} {F : Assn} {s : State} {cr : ECost}
    (h : irSTATE ((x ↦ᵥ v) ∗ F) (s, cr)) : irSTATE ((x ↦ᵥ n) ∗ F) (s.setVar x n, cr) := by
  have h' : ((x ↦ᵥ v) ∗ F) ((vcells s, acells s, hcells s), cr) := h
  rw [ptoVar_sepConj_iff] at h'
  show ((x ↦ᵥ n) ∗ F)
    ((vcells (s.setVar x n), acells (s.setVar x n), hcells (s.setVar x n)), cr)
  rw [vcells_setVar, acells_setVar, hcells_setVar, ptoVar_sepConj_iff, Cells.erase_update]
  exact ⟨by simp, h'.2⟩

/-- Owning `a ↦ₐ xs` means the array exists and holds `xs` — length
included, which is the whole reason the IR needs no `len` op. The
statement is unchanged by decision D-A1: owning a name in this view
already forces `a ≠ heapName`, so no side condition appears. -/
theorem ptoArr_arrs {a : String} {xs : List Val} {F : Assn} {s : State} {cr : ECost}
    (h : irSTATE ((a ↦ₐ xs) ∗ F) (s, cr)) : s.arrs a = some xs := by
  have h' : ((a ↦ₐ xs) ∗ F) ((vcells s, acells s, hcells s), cr) := h
  rw [ptoArr_sepConj_iff] at h'
  have h1 := h'.1
  rw [acells_apply (ne_heapName_of_acells_eq_triv h'.1)] at h1
  exact Tsa.ofOption_eq_triv_iff.1 h1

/-- …and writing it preserves the frame. -/
theorem ptoArr_setArr {a : String} {xs ys : List Val} {F : Assn} {s : State} {cr : ECost}
    (h : irSTATE ((a ↦ₐ xs) ∗ F) (s, cr)) : irSTATE ((a ↦ₐ ys) ∗ F) (s.setArr a ys, cr) := by
  have h' : ((a ↦ₐ xs) ∗ F) ((vcells s, acells s, hcells s), cr) := h
  rw [ptoArr_sepConj_iff] at h'
  have hne : a ≠ heapName := ne_heapName_of_acells_eq_triv h'.1
  show ((a ↦ₐ ys) ∗ F)
    ((vcells (s.setArr a ys), acells (s.setArr a ys), hcells (s.setArr a ys)), cr)
  rw [vcells_setArr, acells_setArr hne, hcells_setArr hne, ptoArr_sepConj_iff,
    Cells.erase_update]
  exact ⟨by simp, h'.2⟩

/-- Owning `¤k` splits the balance. -/
theorem credits_split {k : ECost} {F : Assn} {s : State} {cr : ECost}
    (h : irSTATE ((¤k) ∗ F) (s, cr)) : ∃ cr₂, cr = k + cr₂ ∧ irSTATE F (s, cr₂) := by
  have h' : ((¤k) ∗ F) ((vcells s, acells s, hcells s), cr) := h
  rw [credits_sepConj_iff] at h'
  exact h'

/-- …and paying it back rebuilds the assertion. -/
theorem credits_merge {k : ECost} {F : Assn} {s : State} {cr₂ : ECost}
    (h : irSTATE F (s, cr₂)) : irSTATE ((¤k) ∗ F) (s, k + cr₂) := by
  show ((¤k) ∗ F) ((vcells s, acells s, hcells s), k + cr₂)
  rw [credits_sepConj_iff]
  exact ⟨cr₂, rfl, h⟩

/-! ### Rotation

Bringing a conjunct to the front, which is all the reordering the op
triples of `Triples.lean` need (wave C's `SepSolver` replaces this by
the source's rotate-and-match search). -/

/-- Swap the first two conjuncts of a right-nested `∗`. -/
theorem irSTATE_rot {A B C : Assn} {p : State × ECost} (h : irSTATE (A ∗ (B ∗ C)) p) :
    irSTATE (B ∗ (A ∗ C)) p := by rwa [sepConj_left_comm] at h

/-- Bring the third conjunct of a right-nested `∗` to the front. -/
theorem irSTATE_rot3 {A B C D : Assn} {p : State × ECost} (h : irSTATE (A ∗ (B ∗ (C ∗ D))) p) :
    irSTATE (C ∗ (A ∗ (B ∗ D))) p := by
  rw [sepConj_left_comm B C, sepConj_left_comm A C] at h
  exact h

/-! ## 8. The gate (ledger D4)

The PCM laws, checked by computation on a decidable image of the
carrier, with Plausible over sampled cells, plus the two negative
controls. Nothing here is used by another module. -/

namespace Gate

open Plausible

/-- `##` on `Tsa`, as a `Bool` — the laws below are checked on this, and
`disjB_iff` says it is the relation. -/
def disjB {γ : Type} [DecidableEq γ] (a b : Tsa γ) : Bool := a == 0 || b == 0

theorem disjB_iff {γ : Type} [DecidableEq γ] {a b : Tsa γ} : disjB a b = true ↔ a ## b := by
  simp [disjB, Tsa.disj_def]

/-- A sample of `Tsa ℕ`: `zero` one time in three, an owned value
otherwise. -/
def tsaOf (n : ℕ) : Tsa ℕ := if n % 3 = 0 then .zero else .triv (n % 3)

/-- Three representative resources: empty, and two different owned
values. -/
def tsaSample : List (Tsa ℕ) := [.zero, .triv 1, .triv 2]

-- `x ## 0` and `x + 0 = x`.
#guard tsaSample.all fun a => disjB a 0 && (a + 0 == a)

-- `##` is symmetric, and `+` commutes on disjoint resources.
#guard tsaSample.all fun a => tsaSample.all fun b =>
  (disjB a b == disjB b a) && (!disjB a b || (a + b == b + a))

-- Associativity, on triples that are pairwise disjoint.
#guard tsaSample.all fun a => tsaSample.all fun b => tsaSample.all fun c =>
  !(disjB a b && disjB b c && disjB a c) || ((a + b) + c == a + (b + c))

-- `sep_add_disj_eq`, the `stronger_sep_algebra` law.
#guard tsaSample.all fun a => tsaSample.all fun b => tsaSample.all fun c =>
  !disjB b c || (disjB a (b + c) == (disjB a b && disjB a c))

-- `unique_zero`: nothing overlaps itself but the empty resource.
#guard tsaSample.all fun a => !disjB a a || (a == 0)

-- Negative control: two owned values do *not* compose.
#guard !disjB (Tsa.triv 1) (Tsa.triv 2)
#guard !disjB (Tsa.triv 1) (Tsa.triv 1)

-- The same laws on sampled resources.
#test ∀ m n : ℕ, disjB (tsaOf m) (tsaOf n) = disjB (tsaOf n) (tsaOf m)
#test ∀ m n : ℕ, !disjB (tsaOf m) (tsaOf n) || (tsaOf m + tsaOf n == tsaOf n + tsaOf m)
#test ∀ m n k : ℕ, !disjB (tsaOf n) (tsaOf k) ||
  (disjB (tsaOf m) (tsaOf n + tsaOf k) == (disjB (tsaOf m) (tsaOf n) && disjB (tsaOf m) (tsaOf k)))
#test ∀ m : ℕ, !disjB (tsaOf m) (tsaOf m) || (tsaOf m == 0)

/-! ### Cells: disjointness of names, on a finite name list -/

/-- Disjointness of two cell maps, restricted to a list of names. -/
def disjOnB {γ : Type} [DecidableEq γ] (names : List String) (V W : Cells γ) : Bool :=
  names.all fun x => disjB (V x) (W x)

/-- The names the checks below range over. -/
def names : List String := ["a", "b", "c"]

-- Distinct names compose…
#guard disjOnB names (Cells.single "a" (1 : Val)) (Cells.single "b" (2 : Val))

-- …the same name does not (the negative control the wave asks for).
#guard !disjOnB names (Cells.single "a" (1 : Val)) (Cells.single "a" (2 : Val))
#guard !disjOnB names (Cells.single "a" (1 : Val)) (Cells.single "a" (1 : Val))

-- A single cell composes with its own erasure, and reassembles.
#guard names.all fun x =>
  disjB ((Cells.single "a" (1 : Val)) x) ((Cells.single "a" (1 : Val)).erase "a" x)
#guard names.all fun x =>
  (Cells.single "a" (1 : Val) + (Cells.single "a" (1 : Val)).erase "a") x
    == Cells.single "a" (1 : Val) x

-- Sampled: a cell map and its erasure at the same name are disjoint,
-- and adding the single cell back is the identity.
#test ∀ n : ℕ, names.all fun x =>
  disjB ((Cells.single "a" (n % 5 : Val)) x) ((Cells.single "a" (n % 5 : Val)).erase "a" x)

/-! ### Credits

`ECost` is a function type, so equality of credit assertions is checked
currency by currency, exactly as `Semantics.lean`'s cost vectors are. -/

/-- A credit balance, currency by currency, over the IR's sixteen. -/
def creditVector (c : ECost) : List (String × ℕ∞) :=
  Currency.all.map fun n => (n, c.toFun n)

#guard creditVector (ACost.cost Currency.aget (1 : ℕ∞) + ACost.cost Currency.aset (2 : ℕ∞))
  = [("ir.skip", 0), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 1), ("ir.aset", 2),
     ("ir.ite", 0), ("ir.while", 0), ("ir.add", 0), ("ir.sub", 0), ("ir.mul", 0),
     ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
     ("ir.shiftr", 0)]

-- Credits always compose: the balance of `$c ∗ $c'` is `c + c'`.
#test ∀ m n : ℕ, creditVector (ACost.cost Currency.aget ((m % 7 : ℕ) : ℕ∞)
    + ACost.cost Currency.aget ((n % 7 : ℕ) : ℕ∞))
  = creditVector (ACost.cost Currency.aget (((m % 7) + (n % 7) : ℕ) : ℕ∞))

/-- The negative control at the assertion level: different balances are
different assertions. -/
example : (¤(ACost.cost Currency.aget (1 : ℕ∞))) ≠ (¤(ACost.cost Currency.aget (2 : ℕ∞))) := by
  intro h
  have := credits_injective h
  have := congrArg (fun c => ACost.toFun c Currency.aget) this
  simp at this

/-- The negative control on names: an assertion owning `x` twice is
unsatisfiable. -/
example (x : String) (v w : Val) : ¬ purePart ((x ↦ᵥ v) ∗ (x ↦ᵥ w)) := by
  rintro ⟨h, hh⟩
  rw [ptoVar_sepConj_self] at hh
  exact hh.elim

/-- Ownership really does read the state: `x ↦ᵥ v ∗ F` at a concrete
state forces the cell's value. -/
example : irSTATE (("x" ↦ᵥ 3) ∗ (□ : Assn))
    (State.ofPairs [("x", 3)] [], 0) → (State.ofPairs [("x", 3)] []).vars "x" = some 3 :=
  ptoVar_vars

end Gate

end Lax13Proofs.Refine.Ir
