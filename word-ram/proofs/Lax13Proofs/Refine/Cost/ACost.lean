import Mathlib.Tactic

/-!
The currency type of the refinement tower.

Port of `thys/cost/Abstract_Cost.thy` and `thys/cost/Enat_Cost.thy` of
`isabelle_llvm_time` (Haslbeck–Lammich, ESOP'21 artifact) at the pin
recorded in `plans/word-ram/refinement-tower/design.md` §1,
github.com/lammich/isabelle_llvm_time @ 42dd7f5. The verbatim source is
quoted in `plans/word-ram/refinement-tower/source-extracts.md`:

```isabelle
datatype ('a, 'b) acost = acostC (the_acost: "'a ⇒ 'b")
"zero_acost = acostC (λ_. 0)"
"plus_acost (acostC a) (acostC b) = acostC (λx. a x + b x)"
"less_eq_acost a b = (∀x. the_acost a x ≤ the_acost b x)"
"cost n x = acostC ((the_acost 0)(n := x))"
```

A cost is a *vector of currencies*: an abstract program does not pay in
one resource but in a named bundle of them, and every algebraic
operation on costs is the pointwise one. The whole point of keeping the
currencies apart all the way down is architectural — collapsing them
into a single time unit happens exactly once, in the cashing theorem at
the codegen boundary (design record F4), and until then a cost is a
readable per-phase account.

Substrate deltas against the source, all recorded in the design record:

* `enat` becomes `ℕ∞`; `ecost = (string, enat) acost` becomes
  `ECost := ACost String ℕ∞` (§3 P1 row).
* Currency names stay `String` (fidelity note F1): exchange rates are
  then data, not types.
* The carrier is a plain function, *not* `Finsupp` (fidelity note F2).
  The source's own `wfR` finite-support predicate is what later
  `timerefine` lemmas are stated against, and their shapes depend on the
  carrier being a total function.
* HOL's sort constraints on the datatype become instance arguments on
  the *operations*: `ACost` itself is class-free, so the same type
  carries the `ℕ`-valued and the `ℕ∞`-valued instances without
  duplication.
* The source's `OrderedAddCommMonoid`-style bundling is spelled in the
  current mathlib idiom `AddCommMonoid` + `PartialOrder` +
  `IsOrderedAddMonoid` — mathlib retired the bundled class.

The lattice structure is obtained by pulling back the `Pi` instances
along `ACost.toFun` with `Function.Injective.completeLattice`, which
keeps the `LE`/`LT` instances declared here (it takes them as
parameters), so no order diamond is introduced: the `PartialOrder`
coming out of `CompleteLattice` is the one declared below.

## Relocated here by P2 wave A

`NREST/BackwardsReasoning.lean`'s delta B2 recorded that the cost
carrier's *subtractive* structure had been parked in that file only
because this one was frozen for P1's third slice. It now lives here,
names, statements and proofs unchanged: HOL's `minus` class `ResSub`
(written `-ᵣ`, with its `ℕ∞` instance, its `enat_resSub_*` lemmas and
the `#guard` counterexample that records *why* it is not mathlib's
`Sub` — delta B1 there), the pointwise `ACost` instances `instResSub`,
`instSub` and `instMul`, and `ACost.toFun_iInf`. The resource type
classes that are *stated over* `-ᵣ` (`Needname`, `Drm`, `NeednameZero`
and their instances) stay in `BackwardsReasoning.lean`, which is where
`NREST_Type_Classes.thy` puts them.
-/

namespace Lax13Proofs.Refine

/-! ### HOL's `minus` class, and why it cannot be mathlib's `Sub`

Relocated here by P2 wave A from `NREST/BackwardsReasoning.lean`, whose
delta B2 recorded that this is pure cost-carrier material parked one
file too far down because `ACost.lean` was frozen for P1's third slice.
Names, statements and proofs are unchanged; `BackwardsReasoning.lean`
reaches them through its existing import chain. -/

/-- HOL's `minus` type class: the subtraction the `needname`/`drm`
classes of `NREST_Type_Classes.thy` are stated over. Written `-ᵣ`.

**Substrate delta B1.** mathlib's `Sub ℕ∞` is *truncated* subtraction,
so `⊤ - ⊤ = 0`. Isabelle's `enat` subtraction is
`a - b = (case a of enat x ⇒ (case b of enat y ⇒ enat (x-y) | ∞ ⇒ 0) | ∞ ⇒ ∞)`,
so `∞ - ∞ = ∞`, and the whole `gwp` theory rests on the `needname`
axiom `top - a = top`. Under mathlib's `-` the ported
`minus_p_m_bindT` is refutable (see `NREST/BackwardsReasoning.lean`'s
module header). The operation is therefore declared as its own class —
HOL's `minus` is its own class too — and mathlib's `Sub` is left
alone. -/
class ResSub (γ : Type) where
  /-- The source's `a - b` on a resource algebra. -/
  resSub : γ → γ → γ

@[inherit_doc] infixl:65 " -ᵣ " => ResSub.resSub

/-- Isabelle's `enat` subtraction, verbatim: `∞ - b = ∞`, truncated
subtraction below `∞`. -/
instance instResSubENat : ResSub ℕ∞ := ⟨fun a b => if a = ⊤ then ⊤ else a - b⟩

theorem enat_resSub_def (a b : ℕ∞) : a -ᵣ b = if a = ⊤ then ⊤ else a - b := rfl

@[simp] theorem enat_top_resSub (b : ℕ∞) : (⊤ : ℕ∞) -ᵣ b = ⊤ := by
  simp [enat_resSub_def]

/-- Below `∞` the source's subtraction *is* mathlib's. -/
theorem enat_resSub_of_ne_top {a : ℕ∞} (h : a ≠ ⊤) (b : ℕ∞) : a -ᵣ b = a - b := by
  simp [enat_resSub_def, h]

@[simp] theorem enat_resSub_zero (a : ℕ∞) : a -ᵣ (0 : ℕ∞) = a := by
  rcases eq_or_ne a ⊤ with rfl | h
  · simp
  · rw [enat_resSub_of_ne_top h, tsub_zero]

-- Delta B1, checked by computation: the two subtractions differ, and the
-- source's is the one the `needname` axiom asks for.
#guard ((⊤ : ℕ∞) -ᵣ (⊤ : ℕ∞)) = (⊤ : ℕ∞)
#guard ((⊤ : ℕ∞) - (⊤ : ℕ∞)) = (0 : ℕ∞)
#guard ((5 : ℕ∞) -ᵣ (2 : ℕ∞)) = (3 : ℕ∞)
#guard ((2 : ℕ∞) -ᵣ (5 : ℕ∞)) = (0 : ℕ∞)

/-- A cost: a valuation of the currencies `κ` in the resource algebra
`γ`. The source's `('a, 'b) acost = acostC (the_acost: 'a ⇒ 'b)`. -/
@[ext]
structure ACost (κ γ : Type) where
  /-- The amount of each currency this cost charges; the source's
  `the_acost`. -/
  toFun : κ → γ

namespace ACost

variable {κ γ : Type}

/-- `toFun` is injective — the structure is a wrapper and nothing else.
Every algebraic instance below is pulled back along it. -/
theorem toFun_injective : Function.Injective (ACost.toFun : ACost κ γ → κ → γ) := by
  rintro ⟨a⟩ ⟨b⟩ h; exact congrArg _ h

@[simp] theorem toFun_mk (f : κ → γ) : (ACost.mk f).toFun = f := rfl

@[simp] theorem mk_toFun (a : ACost κ γ) : ACost.mk a.toFun = a := rfl

/-! ### The additive structure, pointwise -/

instance instZero [Zero γ] : Zero (ACost κ γ) := ⟨⟨fun _ => 0⟩⟩

@[simp] theorem toFun_zero [Zero γ] (k : κ) : (0 : ACost κ γ).toFun k = 0 := rfl

instance instAdd [Add γ] : Add (ACost κ γ) := ⟨fun a b => ⟨fun k => a.toFun k + b.toFun k⟩⟩

@[simp] theorem toFun_add [Add γ] (a b : ACost κ γ) (k : κ) :
    (a + b).toFun k = a.toFun k + b.toFun k := rfl

instance instSMulNat [SMul ℕ γ] : SMul ℕ (ACost κ γ) := ⟨fun n a => ⟨fun k => n • a.toFun k⟩⟩

@[simp] theorem toFun_nsmul [SMul ℕ γ] (n : ℕ) (a : ACost κ γ) (k : κ) :
    (n • a).toFun k = n • a.toFun k := rfl

instance instAddMonoid [AddMonoid γ] : AddMonoid (ACost κ γ) :=
  Function.Injective.addMonoid ACost.toFun toFun_injective rfl (fun _ _ => rfl) (fun _ _ => rfl)

instance instAddCommMonoid [AddCommMonoid γ] : AddCommMonoid (ACost κ γ) :=
  Function.Injective.addCommMonoid ACost.toFun toFun_injective rfl (fun _ _ => rfl)
    (fun _ _ => rfl)

/-! ### The subtractive and multiplicative structure, pointwise

The source's `minus_acost_alt` and the `times_acost_def` of its
`acost :: needname_zero` instantiation. Relocated here by P2 wave A;
`NREST/BackwardsReasoning.lean`'s delta B2 is what parked them there. -/

/-- The source's subtraction on `acost`, pointwise. -/
instance instResSub [ResSub γ] : ResSub (ACost κ γ) :=
  ⟨fun a b => ⟨fun k => a.toFun k -ᵣ b.toFun k⟩⟩

@[simp] theorem toFun_resSub [ResSub γ] (a b : ACost κ γ) (k : κ) :
    (a -ᵣ b).toFun k = a.toFun k -ᵣ b.toFun k := rfl

/-- mathlib's `Sub`, pointwise. This is *not* the source's `minus` on a
resource algebra (delta B1); it exists because the `While` rule's energy
annotations live in `ACost κ ℕ`, where the two agree. -/
instance instSub [Sub γ] : Sub (ACost κ γ) :=
  ⟨fun a b => ⟨fun k => a.toFun k - b.toFun k⟩⟩

@[simp] theorem toFun_sub [Sub γ] (a b : ACost κ γ) (k : κ) :
    (a - b).toFun k = a.toFun k - b.toFun k := rfl

/-- The source's `times_acost_def`, from the `acost :: needname_zero`
instantiation: `a * b = acostC (λx. the_acost a x * the_acost b x)`. -/
instance instMul [Mul γ] : Mul (ACost κ γ) :=
  ⟨fun a b => ⟨fun k => a.toFun k * b.toFun k⟩⟩

@[simp] theorem toFun_mul [Mul γ] (a b : ACost κ γ) (k : κ) :
    (a * b).toFun k = a.toFun k * b.toFun k := rfl

/-! ### The order, pointwise -/

instance instLE [LE γ] : LE (ACost κ γ) := ⟨fun a b => a.toFun ≤ b.toFun⟩

/-- The source's `less_eq_acost`: `≤` is currency-by-currency. -/
theorem le_def [LE γ] {a b : ACost κ γ} : a ≤ b ↔ ∀ k, a.toFun k ≤ b.toFun k := Iff.rfl

/-- `<` is spelled the way every `Preorder` spells it, so that the
pullback of the `Pi` order below keeps *this* instance rather than
introducing a second one. -/
instance instLT [LE γ] : LT (ACost κ γ) := ⟨fun a b => a ≤ b ∧ ¬ b ≤ a⟩

theorem lt_def [LE γ] {a b : ACost κ γ} : a < b ↔ a ≤ b ∧ ¬ b ≤ a := Iff.rfl

theorem toFun_lt_toFun [Preorder γ] {a b : ACost κ γ} : a.toFun < b.toFun ↔ a < b :=
  lt_iff_le_not_ge

instance instPreorder [Preorder γ] : Preorder (ACost κ γ) :=
  Function.Injective.preorder ACost.toFun Iff.rfl toFun_lt_toFun

instance instPartialOrder [PartialOrder γ] : PartialOrder (ACost κ γ) :=
  Function.Injective.partialOrder ACost.toFun toFun_injective Iff.rfl toFun_lt_toFun

/-- The source's `ordered_comm_monoid_add` sort constraint, in the
current mathlib spelling. -/
instance instIsOrderedAddMonoid [AddCommMonoid γ] [PartialOrder γ] [IsOrderedAddMonoid γ] :
    IsOrderedAddMonoid (ACost κ γ) where
  add_le_add_left _ _ h _ k := add_le_add_left (le_def.mp h k) _
  add_le_add_right _ _ h _ k := add_le_add_right (le_def.mp h k) _

/-! ### The complete lattice, pointwise -/

instance instMax [Max γ] : Max (ACost κ γ) := ⟨fun a b => ⟨fun k => a.toFun k ⊔ b.toFun k⟩⟩

@[simp] theorem toFun_sup [Max γ] (a b : ACost κ γ) (k : κ) :
    (a ⊔ b).toFun k = a.toFun k ⊔ b.toFun k := rfl

instance instMin [Min γ] : Min (ACost κ γ) := ⟨fun a b => ⟨fun k => a.toFun k ⊓ b.toFun k⟩⟩

@[simp] theorem toFun_inf [Min γ] (a b : ACost κ γ) (k : κ) :
    (a ⊓ b).toFun k = a.toFun k ⊓ b.toFun k := rfl

instance instTop [Top γ] : Top (ACost κ γ) := ⟨⟨fun _ => ⊤⟩⟩

@[simp] theorem toFun_top [Top γ] (k : κ) : (⊤ : ACost κ γ).toFun k = ⊤ := rfl

instance instBot [Bot γ] : Bot (ACost κ γ) := ⟨⟨fun _ => ⊥⟩⟩

@[simp] theorem toFun_bot [Bot γ] (k : κ) : (⊥ : ACost κ γ).toFun k = ⊥ := rfl

instance instSupSet [SupSet γ] : SupSet (ACost κ γ) :=
  ⟨fun S => ⟨fun k => ⨆ a ∈ S, a.toFun k⟩⟩

@[simp] theorem toFun_sSup [SupSet γ] (S : Set (ACost κ γ)) (k : κ) :
    (sSup S).toFun k = ⨆ a ∈ S, a.toFun k := rfl

instance instInfSet [InfSet γ] : InfSet (ACost κ γ) :=
  ⟨fun S => ⟨fun k => ⨅ a ∈ S, a.toFun k⟩⟩

@[simp] theorem toFun_sInf [InfSet γ] (S : Set (ACost κ γ)) (k : κ) :
    (sInf S).toFun k = ⨅ a ∈ S, a.toFun k := rfl

/-- The lattice, pulled back along `toFun` from the `Pi` instance. The
pullback keeps the `LE`/`LT` instances declared above (it takes them as
parameters), so the `PartialOrder` reachable through this instance is
`instPartialOrder` and no order diamond appears. -/
instance instCompleteLattice [CompleteLattice γ] : CompleteLattice (ACost κ γ) :=
  Function.Injective.completeLattice ACost.toFun toFun_injective Iff.rfl toFun_lt_toFun
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun S => by funext k; simp)
    (fun S => by funext k; simp)
    rfl rfl

/-- `⨆`, currency by currency. -/
@[simp] theorem toFun_iSup [CompleteLattice γ] {ι : Sort*} (F : ι → ACost κ γ) (k : κ) :
    (⨆ i, F i).toFun k = ⨆ i, (F i).toFun k := by
  rw [iSup, toFun_sSup, iSup_range]

/-- `⨅`, currency by currency; the `⨆` counterpart is `ACost.lean`'s
`toFun_iSup`, which that file needed and this one needs the dual of. -/
@[simp] theorem toFun_iInf [CompleteLattice γ] {ι : Sort*} (F : ι → ACost κ γ) (k : κ) :
    (⨅ i, F i).toFun k = ⨅ i, (F i).toFun k := by
  rw [iInf, toFun_sInf, iInf_range]

/-! ### One unit of one currency -/

/-- `cost n x`: the cost that charges `x` of the currency `n` and
nothing of any other. The source's
`cost n x = acostC ((the_acost 0)(n := x))`, with HOL's function update
rendered as `Function.update`. -/
def cost [DecidableEq κ] [Zero γ] (n : κ) (x : γ) : ACost κ γ :=
  ⟨Function.update (0 : ACost κ γ).toFun n x⟩

@[simp] theorem toFun_cost_self [DecidableEq κ] [Zero γ] (n : κ) (x : γ) :
    (cost n x).toFun n = x := by
  simp [cost]

@[simp] theorem toFun_cost_ne [DecidableEq κ] [Zero γ] {m n : κ} (h : m ≠ n) (x : γ) :
    (cost n x).toFun m = 0 := by
  simp [cost, Function.update_of_ne h]

theorem toFun_cost [DecidableEq κ] [Zero γ] (n : κ) (x : γ) (m : κ) :
    (cost n x).toFun m = if m = n then x else 0 := by
  rcases eq_or_ne m n with rfl | h
  · simp
  · simp [h]

@[simp] theorem cost_zero [DecidableEq κ] [Zero γ] (n : κ) : cost n (0 : γ) = 0 := by
  ext m; rw [toFun_cost]; split <;> simp

/-- Adding two amounts of the *same* currency. -/
theorem cost_add_cost [DecidableEq κ] [AddMonoid γ] (n : κ) (x y : γ) :
    cost n x + cost n y = cost n (x + y) := by
  ext m; rw [toFun_add, toFun_cost, toFun_cost, toFun_cost]; split <;> simp

end ACost

/-- The abstract cost carrier of the tower: the source's
`ecost = (string, enat) acost`. Currency names are strings (F1) and the
amounts live in `ℕ∞`, so a specification may name an unbounded cost
without leaving the carrier. -/
abbrev ECost := ACost String ℕ∞

end Lax13Proofs.Refine
