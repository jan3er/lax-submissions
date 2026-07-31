import Lax13Proofs.Refine.Sepref.IntfUtil

/-!
# P6 conventions — how a collection is written in this tower

This is the *conventions* module of the IICF port, not a framework: three
patterns and the four lemmas they need. Everything below is consumed by
`Iicf/IicfArray.lean` and `Iicf/IicfTrailArray.lean` (wave A) and is meant
to be consumed unchanged by wave B's stack/queue/CSR/bitmask.

The source (`isabelle_llvm_time` @ `42dd7f5`, `IICF/`) splits every
collection into `Intf/` (abstract type + `sepref_decl_op` interface ops,
cost-silent) and `Impl/` (one concrete representation + a raw `hn_refine`
rule per op, `FCOMP`-composed with the interface's parametricity fact and
registered in `sepref_fr_rules`). The design record's D6-P6-1…4 map that
onto our substrate. What follows is the *shape* of the map.

## 1. The composite-assertion pattern (design D6-P6-2)

A structure is **one `def`** from its abstract value and a tuple of cell
names to an `Assn`, plus **one unfold lemma** into `hnCtxt`/cell
conjuncts. The unfold lemma is what lets the P4 frame matcher pair the
structure's cells with the goal's by concrete cell name
(`Sepref/Frame.lean`'s `conjuncts`/`conjunctsSplit` pair syntactically,
and they do not look inside a `def`).

```
def fooAssn : FooAbs → String × String → Assn :=
  fun s c => ∃ᵃ ghost, ⌜FooWf s ghost⌝ ∗ (arrayAssn … c.1 ∗ natAssn … c.2)

theorem fooAssn_unfold … : fooAssn s c = ∃ᵃ g, ⌜FooWf s g⌝ ∗ (…) := rfl
```

The *ghost* part — a representation detail the abstract value does not
determine, such as a trail array's stale suffix — is existentially owned,
and the well-formedness relating it to the abstract value is a `⌜⌝`
conjunct. `Sepref/Basic.lean`'s `hnr_pre_ex_conv` and `hnr_pre_pure_conv`
strip both in one step, so a structure rule is proved at the *unfolded*
assertion and stated at the composite one.

**P6/D-h — a structure's ops are proved at the raw cells and stated at
the composite assertion; the synthesis pipeline never sees the composite
one.** This is the exact analogue of the source's
`raw_array_assn`-versus-`array_assn` split (`p6-iicf-extracts.md` §3.1,
§3.3: every Impl rule is proved against the raw assertion and lifted by
`FCOMP`), and it is forced here for the same reason plus one of our own:
the P4 matcher is syntactic, so the pipeline can only synthesize a
program whose ownership is spelled in `arrayAssn`/`natAssn` conjuncts. Our
`FCOMP` is `hnr_pre_ex_conv` + `hnr_pre_pure_conv` on the way in and
`hnRefine_cons_post`/`hnRefine_res_cast` on the way out.

## 2. Init from junk, release to junk (design D6-P6-2)

The substrate does not allocate (ledger D2): a structure lives at
caller-chosen cell names whose capacity is fixed before it exists. So the
source's `*_new`/`*_free` ops have no counterpart, and are replaced by

* **init**: an hnr theorem whose *precondition* is junk — `junkCell`s and
  `junkArrayOfLen`s — and whose result assertion is the structure. Its
  program is the fill/zero loop that establishes the invariant.
* **release**: a plain entailment `structAssn s c ⊢ (the junk it was
  built from)`, registered nowhere and applied by
  `hnRefine_cons_res`. Nothing is freed; the cells go back to being
  scratch.

**P6/D-i — junk for an array is `junkArrayOfLen`, not `junkArray`.**
`Sepref/Frame.lean`'s `junkArray a = ∃ᵃ xs, a ↦ₐ xs` forgets the length,
and a no-alloc init loop cannot recover it: the loop's bound is the
array's length, so an init rule stated from `junkArray` is unprovable.
`junkArrayOfLen n a` — *some* contents, of a known length — is the
capacity-fixed junk the substrate actually offers, and it is what an
`arrayAssn` releases to. Fallback if a structure genuinely does not care
about capacity: `junkArrayOfLen_entails_junkArray` weakens.

## 3. Registration (design D6-P6-3)

* An op that produces a value into cells is an `hnRefine` theorem tagged
  `@[sepref_fr_rules]`, stated at the interface `mop_…`, with cell names
  universally quantified and the destination in the judgment's result
  slot. One op, one rule; consumers never see the compound program.
* An op that is a *guard* — `isEmpty`, `mem`, `i < size` — is **not** an
  hnr rule. P4/D-af made guards structural: they are `CondRefine` facts
  about the precondition, tagged `@[sepref_cond_rules]` (design D6-P6-5).
  A structure therefore exports its emptiness test as, e.g.,
  `CondRefine (fooAssn s c ∗ Γ) (.lt (.lit 0) (.cell c.2)) (decide (0 < s.2))`.
* The compound program itself is **synthesized**, not written: the op's
  raw rule is produced by `sepref_synth` from the primitive mops
  (D6-P6-3), its `Com` pinned by `#guard`, and only then lifted and
  registered. That is how the cost stays honest — nobody writes a cost
  down, the pipeline reports what it spent.

**P6/D-j — the interface op is `consume (returnT …) C` in closed form,
with `C` a concrete `ECost` multiset.** D6-P6-1 already says the cost *is*
the interface (our `hnRefine` has no hidden cost notation). The extra
commitment here is that a structure op's abstract program is a
*closed-form* `consume (returnT …) C` rather than the loop it is
implemented by: a consumer of `mop_array_fill` must not have to reason
about an `irWhileIT`. The bridge is one value lemma per looping op
(`fillLoop_value`, `resetLoop_value`), proved by induction, plus
`hnRefine_res_cast` below.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

namespace Iicf

/-! ## 1. Capacity-fixed array junk (P6/D-i) -/

/-- The no-alloc substrate's array junk: the cell `a` holds *some* list of
the fixed length `n`. This is what a structure is initialized from and
what it is released back to. -/
def junkArrayOfLen (n : ℕ) (a : String) : Assn := ∃ᵃ xs, ⌜xs.length = n⌝ ∗ arrayAssn xs a

theorem junkArrayOfLen_def (n : ℕ) (a : String) :
    junkArrayOfLen n a = ∃ᵃ xs, ⌜xs.length = n⌝ ∗ arrayAssn xs a := rfl

/-- The release direction for a plain array: a known array is junk of its
own length. -/
theorem arrayAssn_entails_junkArrayOfLen (xs : List ℕ) (a : String) :
    arrayAssn xs a ⊢ junkArrayOfLen xs.length a :=
  fun _ h => ⟨xs, predLift_sepConj_iff.2 ⟨rfl, h⟩⟩

/-- …and, at a length the caller states. -/
theorem arrayAssn_entails_junkArrayOfLen' {n : ℕ} (xs : List ℕ) (a : String)
    (h : xs.length = n) : arrayAssn xs a ⊢ junkArrayOfLen n a :=
  fun _ hh => ⟨xs, predLift_sepConj_iff.2 ⟨h, hh⟩⟩

/-- Capacity-fixed junk is junk (P6/D-i's fallback). -/
theorem junkArrayOfLen_entails_junkArray (n : ℕ) (a : String) :
    junkArrayOfLen n a ⊢ junkArray a := by
  intro h hh
  obtain ⟨xs, hxs⟩ := hh
  exact ⟨xs, (predLift_sepConj_iff.1 hxs).2⟩

/-- An hnr judgment whose precondition is capacity-fixed junk is a
judgment at every concrete filling of that junk — the *init* half of
P6/D-i, in the form `hnr_pre_ex_conv` wants. -/
theorem hnRefine_junkArrayOfLen {α κ : Type} {Γ' : Assn} {c : Com} {d : κ}
    {R : α → κ → Assn} {m : NRest α ECost} {n : ℕ} {a : String} {Γ : Assn}
    (h : ∀ xs : List ℕ, xs.length = n → hnRefine (arrayAssn xs a ∗ Γ) c Γ' d R m) :
    hnRefine (junkArrayOfLen n a ∗ Γ) c Γ' d R m := by
  rw [junkArrayOfLen_def, sepEx_sepConj]
  refine hnr_pre_ex_conv.2 fun xs => ?_
  rw [sepConj_assoc]
  exact hnr_pre_pure_conv.2 fun hlen => h xs hlen

/-! ## 2. Permutation of ownership, inside a structure's own proofs

The exercises must contain no hand frame work — that is the phase's
acceptance criterion. A *structure's* own lifting proofs are the other
side of that coin: they are where the permutations live, once per op, so
that no consumer ever writes one. Two one-liners make them uniform. -/

/-- A permutation of `∗`-conjuncts is an entailment. -/
theorem entails_of_eq {P Q : Assn} (h : P = Q) : P ⊢ Q := h ▸ entails_refl P

/-- `prodAssn` applied, as a rewrite: the tuple assertion *is* its
components starred (`Sepref/Frame.lean`'s `hnCtxt_prodAssn`, without the
`hnCtxt` tag, so that a normalizing `simp only` reaches it). -/
@[simp] theorem prodAssn_apply {α₁ α₂ κ₁ κ₂ : Type} (A : α₁ → κ₁ → Assn) (B : α₂ → κ₂ → Assn)
    (a : α₁ × α₂) (c : κ₁ × κ₂) : (A ×ₐ B) a c = A a.1 c.1 ∗ B a.2 c.2 := rfl

/-- Close an entailment between two `∗`-trees over the same cells, after
normalizing away the `hnCtxt` tags and the tuple assertions. The
structure-side counterpart of `Sepref/Frame.lean`'s `sepref_ac`. -/
macro "iicf_perm" : tactic =>
  `(tactic| (refine entails_of_eq ?_
             simp only [hnCtxt_def, prodAssn_apply, sepConj_emp, emp_sepConj]
             ac_rfl))

/-! ## 3. The result cast (P6/D-k)

The one lemma the whole synthesized-impl route turns on. -/

/-- Binding a one-op program is charging its cost and going on — the one
normalization step every body-value lemma runs on. (The same lemma as
`Sepref/Examples/Acceptance.lean`'s; restated here because a library file
may not import an examples file, and its home is P1's `NREST/Pw.lean`.) -/
theorem bindT_unit {α β : Type} (x : α) (c : ECost) (f : α → NRest β ECost) :
    NRest.bindT (NRest.consume (NRest.returnT x) c) f = NRest.consume (f x) c := by
  rw [NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.returnT_bindT]

/-- **P6/D-k, general form** — re-read a closed-form judgment's *whole*
postcondition. The synthesized judgment's post is `Q ∗ R x d`; the
interface op's is `Q' ∗ R' y d'`. Any entailment between the two is a
legal re-reading, which is what lets a structure op move the scratch
cells its implementation used out of the result slot and into the
postcondition (a plain `hnRefine_cons_res` cannot: dropping ownership
from the result slot is not an entailment, moving it is). -/
theorem hnRefine_res_cast' {α β κ κ' : Type} {Γ Q Q' : Assn} {c : Com} {d : κ} {d' : κ'}
    {R : α → κ → Assn} {R' : β → κ' → Assn} {x : α} {y : β} {C : ECost}
    (h : hnRefine Γ c Q d R (NRest.consume (NRest.returnT x) C))
    (hent : Q ∗ R x d ⊢ Q' ∗ R' y d') :
    hnRefine Γ c Q' d' R' (NRest.consume (NRest.returnT y) C) := by
  refine hnRefineI fun M F s cr hm hs => ?_
  rw [NRest.consume_returnT, NRest.rest_inj_iff] at hm
  obtain ⟨ra, Ca, hCa, w⟩ := hnRefineD h (NRest.consume_returnT x C) hs
  have hra : ra = x := by
    by_contra hne
    rw [NRest.single_of_ne hne] at hCa
    exact WithBot.coe_ne_bot (le_bot_iff.1 hCa)
  subst hra
  refine ⟨y, Ca, ?_, ?_⟩
  · rw [← hm, NRest.single_self]
    rwa [NRest.single_self] at hCa
  · refine wp_mono_ir (fun _ p hp => ?_) w
    have e : (Q ∗ R ra d ∗ F ∗ GC) = ((Q ∗ R ra d) ∗ (F ∗ GC)) := by ac_rfl
    have e' : (Q' ∗ R' y d' ∗ F ∗ GC) = ((Q' ∗ R' y d') ∗ (F ∗ GC)) := by ac_rfl
    show (Q' ∗ R' y d' ∗ F ∗ GC) _
    rw [e']
    rw [e] at hp
    exact conj_entails_mono hent (entails_refl _) _ hp

/-- **P6/D-k — re-index a closed-form judgment's result.** A synthesized
loop's judgment is stated at the loop *state* — a tuple of cells, holding
a tuple value. An interface op's judgment is stated at what the op
*returns* — usually one component of that tuple, at one cell, under the
structure's own assertion. When the abstract program is already in the
closed form `consume (returnT x) C` (P6/D-j), the two are the same
judgment: the program, the precondition, the postcondition and the price
are untouched, and only the *reading* of the final state changes, which
is one entailment.

This is the projection P4/D-ec's fallback asked for ("a projection
operation would let the top-level program end at the array alone; it is
one rule and one `Com.skip`"), obtained without a rule and without a
`skip`, because the closed form makes the result a known value. -/
theorem hnRefine_res_cast {α β κ κ' : Type} {Γ Q : Assn} {c : Com} {d : κ} {d' : κ'}
    {R : α → κ → Assn} {R' : β → κ' → Assn} {x : α} {y : β} {C : ECost}
    (h : hnRefine Γ c Q d R (NRest.consume (NRest.returnT x) C))
    (hent : R x d ⊢ R' y d') :
    hnRefine Γ c Q d' R' (NRest.consume (NRest.returnT y) C) :=
  hnRefine_res_cast' h (conj_entails_mono (entails_refl Q) hent)

/-! ## 4. Release, as a named pattern

The `Releasable` half of §2's init/release pair: one `def` so that a
structure's release obligation has a name a consumer can look up, and one
corollary so that discharging it on an hnr judgment is a single term. -/

/-- The structure `R` can be handed back as the junk `J`. -/
def Releasable {α κ : Type} (R : α → κ → Assn) (J : κ → Assn) : Prop :=
  ∀ (a : α) (c : κ), R a c ⊢ J c

/-- Releasing a judgment's result: the program is done with the
structure, and what is left is the cells. -/
theorem Releasable.res {α κ : Type} {R : α → κ → Assn} {J : κ → Assn}
    (hR : Releasable R J) {Γ Q : Assn} {c : Com} {d : κ} {m : NRest α ECost}
    (h : hnRefine Γ c Q d R m) : hnRefine Γ c Q d (fun _ e => J e) m :=
  hnRefine_cons_res h fun a e => hR a e

/-- Plain arrays release to capacity-fixed junk, at a statically known
length (the static-length discipline, D6-P6-4). -/
theorem releasable_arrayAssn (n : ℕ) :
    Releasable (fun (xs : { l : List ℕ // l.length = n }) (a : String) => arrayAssn xs.1 a)
      (junkArrayOfLen n) :=
  fun xs a => arrayAssn_entails_junkArrayOfLen' xs.1 a xs.2

end Iicf

end Lax13Proofs.Refine.Sepref
