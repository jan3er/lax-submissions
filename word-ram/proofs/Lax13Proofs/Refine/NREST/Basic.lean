import Lax13Proofs.Refine.Cost.ACost

/-!
The NREST monad: nondeterministic results carrying a resource valuation.

Port of the core of `thys/nrest/NREST.thy` of `isabelle_llvm_time`
(Haslbeck–Lammich, ESOP'21 artifact) at the pin recorded in
`plans/word-ram/refinement-tower/design.md` §1,
github.com/lammich/isabelle_llvm_time @ 42dd7f5; the AFP `NREST` entry
(Isabelle2025-2) carries the same core. The verbatim source is quoted in
`plans/word-ram/refinement-tower/source-extracts.md`:

```isabelle
datatype ('a,'b) nrest = FAILi | REST "'a ⇒ ('b::{complete_lattice,monoid_add}) option"
"RETURNT x ≡ REST (λe. if e=x then Some 0 else None)"
"SPEC P t = REST (λv. if P v then Some (t v) else None)"
fun less_eq_nrest where
  "_ ≤ FAILi ⟷ True" | "(REST a) ≤ (REST b) ⟷ a ≤ b" | "FAILi ≤ (REST _) ⟷ False"
"consume M t ≡ case M of FAILi ⇒ FAILT | REST X ⇒ REST (map_option ((+) t) o (X))"
"bindT M f ≡ case M of FAILi ⇒ FAILT | REST X ⇒ Sup {consume (f x) t1 |x t1. X x = Some t1}"
"iASSERT ret Φ ≡ if Φ then ret () else top"   "ASSERT ≡ iASSERT RETURNT"
```

## Substrate decisions

**The result map.** Isabelle's `'a ⇒ 'b option`, ordered pointwise with
`None` at the bottom, *is* mathlib's `α → WithBot γ`: `WithBot γ` is
`Option γ` with exactly that order, and mathlib already proves it a
complete lattice, as it proves `α → _` one. So the entire lattice
structure of result maps is imported rather than re-derived, and only
the `FAILi`-on-top layer is built here. This is the substrate decision
fixed by the supervisor for P1; it is a change of *spelling*, not of
content — `Some t` reads `(t : WithBot γ)` and `None` reads `⊥`.

**Class constraints.** HOL puts sort constraints
`'b :: {complete_lattice, monoid_add}` on the datatype itself. Lean's
natural rendering puts them on the *operations*: `NRest α γ` is
class-free, and `returnT` asks for `Zero γ`, `consume` for `Add γ`,
`bindT` for `CompleteLattice γ` and `Add γ`, exactly as much as each
needs. One type therefore carries the `ℕ`-valued and the `ℕ∞`-valued
uses without duplication, and the monomorphic statements the source
makes at `enat` (see `Pw.lean`) can be stated at their own carriers.

**The complete lattice.** `NRest α γ` is order-isomorphic to
`WithTop (α → WithBot γ)`, but mathlib has no
`CompleteLattice (WithTop β)` instance for a complete lattice `β` (only
the `WithBot` direction and the mixed `WithTop (WithBot _)` one), so
there is nothing to transport across. The instance is therefore built
the source's own way: `sSup` is defined by the source's formula
(`FAILi` if it occurs in the set, otherwise the pointwise supremum of
the result maps), and `completeLatticeOfSup` turns the `IsLUB` proof
into the lattice. `⊤`, `⊥`, `⊔`, `⊓` are supplied explicitly rather
than left to that constructor's set-comprehension defaults, so that
`⊤ = fail` and `⊥ = rest ⊥` hold by `rfl` and the binary operations are
plain matches rather than suprema over set comprehensions — which is
what makes the sanity layer's executable twins one-line agreements
(design record ledger D4).

Per design record §10.2 both parameters stay in `Type`; no universe
polymorphism until a consumer forces it.
-/

namespace Lax13Proofs.Refine

/-- A nondeterministic computation returning `α` and paying in `γ`.
`fail` is the source's `FAILi`, the top element that a violated
assertion produces; `rest M` is the source's `REST M`, offering each
result `x` at cost `M x`, with `M x = ⊥` meaning "not a possible
result". -/
inductive NRest (α γ : Type) where
  /-- The failing computation; the top of the order. -/
  | fail
  /-- The computation whose results are described by the map `M`. -/
  | rest (M : α → WithBot γ)

namespace NRest

variable {α β γ : Type}

theorem rest_ne_fail (M : α → WithBot γ) : rest M ≠ fail := by simp

theorem fail_ne_rest (M : α → WithBot γ) : fail ≠ rest M := by simp

@[simp] theorem rest_inj_iff {M N : α → WithBot γ} : rest M = rest N ↔ M = N :=
  ⟨fun h => by cases h; rfl, fun h => by rw [h]⟩

/-! ### Single-result maps

The idiom `λe. if e = x then _ else None` occurs in `RETURNT`, in
`consume_RETURNT` and in the definition of `inresT`; it is named once
here. The `if` is classical, as HOL's is — the price is that the
operations built from it are `noncomputable`, and the sanity layer
bridges to a `DecidableEq`-based twin. -/

open Classical in
/-- `single x u`: the result map admitting exactly the result `x`, at
cost `u`. HOL writes it `[x ↦ t]`. -/
noncomputable def single (x : α) (u : WithBot γ) : α → WithBot γ :=
  fun v => if v = x then u else ⊥

@[simp] theorem single_self (x : α) (u : WithBot γ) : single x u x = u := by
  simp [single]

@[simp] theorem single_of_ne {x v : α} (h : v ≠ x) (u : WithBot γ) : single x u v = ⊥ := by
  simp [single, h]

/-- The `DecidableEq` reading of `single`; the sanity layer's executable
twin agrees with it through this. -/
theorem single_eq_ite [DecidableEq α] (x : α) (u : WithBot γ) (v : α) :
    single x u v = if v = x then u else ⊥ := by
  by_cases h : v = x
  · subst h; simp
  · simp [h]

@[simp] theorem single_bot (x : α) : single x (⊥ : WithBot γ) = ⊥ := by
  funext v; by_cases h : v = x
  · subst h; simp
  · simp [h]

/-- The defining property of `single`: it is the least result map
admitting `x` at cost `u`. -/
theorem single_le_iff [Preorder γ] {x : α} {u : WithBot γ} {X : α → WithBot γ} :
    single x u ≤ X ↔ u ≤ X x := by
  constructor
  · intro h; simpa using h x
  · intro h v
    by_cases hv : v = x
    · subst hv; simpa using h
    · simp [hv]

/-! ### The order

The source's `less_eq_nrest`, clause for clause. The three `simp`
lemmas below *are* its equation lemmas. -/

/-- The source's `less_eq_nrest`. The second argument is examined first
so that `m ≤ fail` reduces for a variable `m`. -/
instance instLE [LE γ] : LE (NRest α γ) where
  le m n :=
    match n with
    | .fail => True
    | .rest b =>
      match m with
      | .fail => False
      | .rest a => a ≤ b

@[simp] theorem le_fail [LE γ] (m : NRest α γ) : m ≤ fail := trivial

@[simp] theorem not_fail_le_rest [LE γ] (b : α → WithBot γ) : ¬ (fail ≤ rest b) := id

@[simp] theorem rest_le_rest_iff [LE γ] {a b : α → WithBot γ} : rest a ≤ rest b ↔ a ≤ b := Iff.rfl

theorem fail_le_iff [LE γ] {m : NRest α γ} : fail ≤ m ↔ m = fail := by
  cases m <;> simp

/-- `≤` is a partial order as soon as the resource order is one; `<` is
the `Preorder` default, which is what `completeLatticeOfSup` will
inherit. -/
instance instPartialOrder [PartialOrder γ] : PartialOrder (NRest α γ) where
  le_refl m := by cases m <;> simp
  le_trans a b c hab hbc := by
    cases c with
    | fail => simp
    | rest c =>
      cases b with
      | fail => simp at hbc
      | rest b =>
        cases a with
        | fail => simp at hab
        | rest a =>
          exact rest_le_rest_iff.mpr
            (le_trans (rest_le_rest_iff.mp hab) (rest_le_rest_iff.mp hbc))
  le_antisymm a b hab hba := by
    cases a with
    | fail => cases b with
      | fail => rfl
      | rest b => simp at hab
    | rest a => cases b with
      | fail => simp at hba
      | rest b => simpa using le_antisymm hab hba

/-! ### The binary lattice operations

Given explicitly (rather than left to `completeLatticeOfSup`'s
`sSup`-of-a-pair default) so that they compute. -/

/-- `⊔` on `NRest`: `fail` is the top, so it absorbs. -/
def join [CompleteLattice γ] (m n : NRest α γ) : NRest α γ :=
  match m, n with
  | .fail, _ => .fail
  | _, .fail => .fail
  | .rest a, .rest b => .rest (a ⊔ b)

@[simp] theorem join_fail_left [CompleteLattice γ] (n : NRest α γ) : join fail n = fail := rfl

@[simp] theorem join_fail_right [CompleteLattice γ] (a : α → WithBot γ) :
    join (rest a) fail = fail := rfl

@[simp] theorem join_rest [CompleteLattice γ] (a b : α → WithBot γ) :
    join (rest a) (rest b) = rest (a ⊔ b) := rfl

/-- `⊓` on `NRest`: `fail` is the top, so it is neutral. -/
def meet [CompleteLattice γ] (m n : NRest α γ) : NRest α γ :=
  match m, n with
  | .fail, n => n
  | m, .fail => m
  | .rest a, .rest b => .rest (a ⊓ b)

@[simp] theorem meet_fail_left [CompleteLattice γ] (n : NRest α γ) : meet fail n = n := rfl

@[simp] theorem meet_fail_right [CompleteLattice γ] (a : α → WithBot γ) :
    meet (rest a) fail = rest a := rfl

@[simp] theorem meet_rest [CompleteLattice γ] (a b : α → WithBot γ) :
    meet (rest a) (rest b) = rest (a ⊓ b) := rfl

/-! ### Suprema

The source's `Sup`: `FAILi` if it occurs, otherwise `REST` of the
pointwise supremum of the result maps occurring in the set. -/

/-- The result maps occurring in a set of computations. -/
def restsOf (S : Set (NRest α γ)) : Set (α → WithBot γ) := {M | rest M ∈ S}

@[simp] theorem mem_restsOf {S : Set (NRest α γ)} {M : α → WithBot γ} :
    M ∈ restsOf S ↔ rest M ∈ S := Iff.rfl

open Classical in
/-- The source's `Sup` on `nrest`, before it is packaged as an
instance. -/
noncomputable def supSet' [CompleteLattice γ] (S : Set (NRest α γ)) : NRest α γ :=
  if fail ∈ S then fail else rest (sSup (restsOf S))

/-- The source's `Sup`, as the instance the lattice is built from. -/
noncomputable instance instSupSet [CompleteLattice γ] : SupSet (NRest α γ) := ⟨supSet'⟩

theorem sSup_def [CompleteLattice γ] (S : Set (NRest α γ)) : sSup S = supSet' S := rfl

theorem sSup_of_mem_fail [CompleteLattice γ] {S : Set (NRest α γ)} (h : fail ∈ S) :
    sSup S = fail := by
  simp only [sSup_def, supSet', if_pos h]

theorem sSup_of_notMem_fail [CompleteLattice γ] {S : Set (NRest α γ)} (h : fail ∉ S) :
    sSup S = rest (sSup (restsOf S)) := by
  simp only [sSup_def, supSet', if_neg h]

theorem isLUB_sSup' [CompleteLattice γ] (S : Set (NRest α γ)) : IsLUB S (sSup S) := by
  by_cases h : fail ∈ S
  · rw [sSup_of_mem_fail h]
    exact ⟨fun m _ => le_fail m, fun _ hu => hu h⟩
  · rw [sSup_of_notMem_fail h]
    refine ⟨fun m hm => ?_, fun u hu => ?_⟩
    · cases m with
      | fail => exact absurd hm h
      | rest M => exact rest_le_rest_iff.mpr (le_sSup (mem_restsOf.mpr hm))
    · cases u with
      | fail => exact le_fail _
      | rest U =>
        exact rest_le_rest_iff.mpr (sSup_le fun M hM => rest_le_rest_iff.mp (hu hM))

theorem rest_bot_le [CompleteLattice γ] (m : NRest α γ) : rest (⊥ : α → WithBot γ) ≤ m := by
  cases m <;> simp

/-- The complete lattice, from the `IsLUB` proof above. `⊤`, `⊥`, `⊔`
and `⊓` are given explicitly so that they are the plain matches of this
file rather than `completeLatticeOfSup`'s set-comprehension defaults;
only `sInf` is left derived, and nothing below uses it. -/
noncomputable instance instCompleteLattice [CompleteLattice γ] :
    CompleteLattice (NRest α γ) where
  __ := completeLatticeOfSup (NRest α γ) isLUB_sSup'
  top := fail
  le_top := le_fail
  bot := rest ⊥
  bot_le := rest_bot_le
  sup := join
  le_sup_left m n := by
    cases m with
    | fail => simp
    | rest a => cases n with
      | fail => simp
      | rest b => simp
  le_sup_right m n := by
    cases m with
    | fail => simp
    | rest a => cases n with
      | fail => simp
      | rest b => simp
  sup_le m n k hm hk := by
    cases k with
    | fail => simp
    | rest c =>
      cases m with
      | fail => simp at hm
      | rest a => cases n with
        | fail => simp at hk
        | rest b => simpa using sup_le hm hk
  inf := meet
  inf_le_left m n := by
    cases m with
    | fail => simp
    | rest a => cases n with
      | fail => simp
      | rest b => simp
  inf_le_right m n := by
    cases m with
    | fail => simp
    | rest a => cases n with
      | fail => simp
      | rest b => simp
  le_inf m n k hn hk := by
    cases m with
    | fail =>
      cases n with
      | fail => simpa using hk
      | rest b => simp at hn
    | rest a => cases n with
      | fail => simpa using hk
      | rest b => cases k with
        | fail => simpa using hn
        | rest c => simpa using le_inf hn hk

@[simp] theorem top_eq_fail [CompleteLattice γ] : (⊤ : NRest α γ) = fail := rfl

@[simp] theorem bot_eq_rest_bot [CompleteLattice γ] : (⊥ : NRest α γ) = rest ⊥ := rfl

@[simp] theorem sup_eq_join [CompleteLattice γ] (m n : NRest α γ) : m ⊔ n = join m n := rfl

@[simp] theorem inf_eq_meet [CompleteLattice γ] (m n : NRest α γ) : m ⊓ n = meet m n := rfl

@[simp] theorem sSup_eq_fail_iff [CompleteLattice γ] {S : Set (NRest α γ)} :
    sSup S = fail ↔ fail ∈ S := by
  by_cases h : fail ∈ S
  · simp [sSup_of_mem_fail h, h]
  · simp [sSup_of_notMem_fail h, h]

@[simp] theorem iSup_eq_fail_iff [CompleteLattice γ] {ι : Sort*} {F : ι → NRest α γ} :
    (⨆ i, F i) = fail ↔ ∃ i, F i = fail := by
  simp [iSup]

/-- Suprema of sets of `rest`s are computed inside `rest`. -/
theorem sSup_image_rest [CompleteLattice γ] (T : Set (α → WithBot γ)) :
    sSup (rest '' T) = rest (sSup T) := by
  have h : fail ∉ rest '' T := by rintro ⟨M, -, hM⟩; exact rest_ne_fail M hM
  rw [sSup_of_notMem_fail h]
  congr 1
  ext M
  simp [restsOf]

/-- Suprema of families of `rest`s are computed inside `rest`. -/
theorem iSup_rest [CompleteLattice γ] {ι : Sort*} (F : ι → α → WithBot γ) :
    (⨆ i, rest (F i)) = rest (⨆ i, F i) := by
  have h : (Set.range fun i => rest (F i)) = rest '' Set.range F := by ext m; simp
  rw [iSup, h, sSup_image_rest, iSup]

/-! ### The operations

Source names and argument orders throughout, casing adapted to Lean. -/

/-- The source's `RETURNT`: the computation with the single result `x`,
free. Note `(0 : WithBot γ)` is the coercion of `(0 : γ)` — the cost
zero — and is strictly above `⊥`, which is "no such result". -/
noncomputable def returnT [Zero γ] (x : α) : NRest α γ := rest (single x (0 : WithBot γ))

theorem returnT_eq [Zero γ] (x : α) :
    (returnT x : NRest α γ) = rest (fun e => single x (0 : WithBot γ) e) := rfl

@[simp] theorem returnT_ne_fail [Zero γ] (x : α) : (returnT x : NRest α γ) ≠ fail :=
  rest_ne_fail _

open Classical in
/-- The source's `SPEC P t`: any result satisfying `P`, at the cost `t`
names for it. The `if` is classical, as in HOL. -/
noncomputable def spec (P : α → Prop) (t : α → γ) : NRest α γ :=
  rest (fun v => if P v then ((t v : γ) : WithBot γ) else ⊥)

@[simp] theorem spec_ne_fail (P : α → Prop) (t : α → γ) : spec P t ≠ fail := rest_ne_fail _

/-- The source's `consume`: charge `t` on top of everything `m` already
charges. The added cost sits on the *left*, `map_option ((+) t)`, which
matters as soon as `γ` is not commutative. -/
def consume [Add γ] (m : NRest α γ) (t : γ) : NRest α γ :=
  match m with
  | .fail => .fail
  | .rest X => .rest (fun x => WithBot.map (t + ·) (X x))

@[simp] theorem consume_fail [Add γ] (t : γ) : consume (fail : NRest α γ) t = fail := rfl

@[simp] theorem consume_rest [Add γ] (X : α → WithBot γ) (t : γ) :
    consume (rest X) t = rest (fun x => WithBot.map (t + ·) (X x)) := rfl

/-- The source's `bindT`, a supremum over the results of `m` of the
continuation charged with the cost that reaching that result took. -/
noncomputable def bindT [CompleteLattice γ] [Add γ] (m : NRest α γ) (f : α → NRest β γ) :
    NRest β γ :=
  match m with
  | .fail => ⊤
  | .rest X => sSup { n | ∃ (x : α) (t : γ), X x = (t : WithBot γ) ∧ n = consume (f x) t }

@[simp] theorem bindT_fail [CompleteLattice γ] [Add γ] (f : α → NRest β γ) :
    bindT (fail : NRest α γ) f = fail := rfl

@[simp] theorem bindT_rest [CompleteLattice γ] [Add γ] (X : α → WithBot γ)
    (f : α → NRest β γ) :
    bindT (rest X) f =
      sSup { n | ∃ (x : α) (t : γ), X x = (t : WithBot γ) ∧ n = consume (f x) t } := rfl

/-! ### `consumea`

The source's one-result "pay this and continue" computation, and the
rewriting of `consume` as a bind against it. `consumea` sits in
`NREST.thy` next to `consume`, which is why it sits here; P1 defined it
in `Combinators.lean` because this file was frozen for that slice
(`Combinators.lean`'s decision C6), and P2 wave A moved it up.

The two *statements* are P1's, unchanged. `consume_alt2`'s **proof** had
to change: P1 proved it through `Pw.lean`'s `bindT_rest_eq_iSup`, which
sits above this file, so the same fact is read off `bindT_rest`'s own
set comprehension instead — at `Unit` that comprehension is a singleton,
which is what P1's `iSup_unique` step was also using. -/

open Classical in
/-- The source's `consumea T = SPECT [() ↦ T]`. -/
noncomputable def consumea [CompleteLattice γ] (T : γ) : NRest Unit γ :=
  rest (single () (T : WithBot γ))

@[simp] theorem consumea_ne_fail [CompleteLattice γ] (T : γ) :
    consumea T ≠ (fail : NRest Unit γ) := rest_ne_fail _

/-- The source's `consume_alt2`: charging a cost is binding against
`consumea`. -/
theorem consume_alt2 [CompleteLattice γ] [AddMonoid γ] (M : NRest α γ) (T : γ) :
    consume M T = bindT (consumea T) fun _ => M := by
  rw [consumea, bindT_rest]
  have hset : {n : NRest α γ | ∃ (x : Unit) (t : γ),
      single () (T : WithBot γ) x = (t : WithBot γ) ∧ n = consume M t} = {consume M T} := by
    ext n
    constructor
    · rintro ⟨⟨⟩, t, ht, rfl⟩
      rw [single_self, WithBot.coe_inj] at ht
      rw [ht]
      exact rfl
    · rintro rfl
      exact ⟨(), T, by simp, rfl⟩
  rw [hset, sSup_singleton]

open Classical in
/-- The source's `iASSERT`: run `ret ()` if `Φ` holds, fail otherwise. -/
noncomputable def iAssert [CompleteLattice γ] (ret : Unit → NRest α γ) (Φ : Prop) : NRest α γ :=
  if Φ then ret () else ⊤

/-- The source's `ASSERT = iASSERT RETURNT`. -/
noncomputable def assert [CompleteLattice γ] [Zero γ] (Φ : Prop) : NRest Unit γ :=
  iAssert returnT Φ

@[simp] theorem iAssert_pos [CompleteLattice γ] {Φ : Prop} (h : Φ) (ret : Unit → NRest α γ) :
    iAssert ret Φ = ret () := by simp [iAssert, h]

@[simp] theorem iAssert_neg [CompleteLattice γ] {Φ : Prop} (h : ¬ Φ) (ret : Unit → NRest α γ) :
    iAssert ret Φ = fail := by simp [iAssert, h]

@[simp] theorem assert_pos [CompleteLattice γ] [Zero γ] {Φ : Prop} (h : Φ) :
    (assert Φ : NRest Unit γ) = returnT () := by simp [assert, h]

@[simp] theorem assert_neg [CompleteLattice γ] [Zero γ] {Φ : Prop} (h : ¬ Φ) :
    (assert Φ : NRest Unit γ) = fail := by simp [assert, h]

end NRest

/-- The source's `FAILT`. -/
noncomputable abbrev failT {α γ : Type} [CompleteLattice γ] : NRest α γ := ⊤

/-- The source's `SUCCEEDT`: the computation with no results at all. -/
noncomputable abbrev succeedT {α γ : Type} [CompleteLattice γ] : NRest α γ := ⊥

end Lax13Proofs.Refine
