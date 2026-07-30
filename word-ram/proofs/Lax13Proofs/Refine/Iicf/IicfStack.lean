import Lax13Proofs.Refine.Sepref.Definition

/-!
# IICF: bounded stack over two fixed cells

The first of P6-B's four composite structures
(`plans/word-ram/refinement-tower/p6-iicf-design.md`, structure 3):
an abstract `List ℕ` — top = head — living in the two caller-named cells
`(S, top)` with a *static* capacity, no allocation and no dealloc.

This file also carries the **shared idiom** of the P6-B wave (§1): the
`hnRefine`-level bridges every composite structure is built with. They
belong in P6-A's `Iicf/Basic.lean`; they are here because the two waves
run in parallel and P6-B may not create or import that file (flag
`P6/D-ba`). `IicfQueue`, `IicfCsr` and `IicfBitmask` import *this* file
for them.

## Judgment calls (P6/D-ba …)

**P6/D-ba — the wave's shared bridges live in this file.** Three lemmas
(`hnRefine_reinterp`, `hnr_pre_ex_pure`, `hnr_pre_pure_star`) plus
`bindT_unit` are what turn a *synthesized raw* judgment into a
*composite* one. They are structure-agnostic and used by all four files,
so duplicating them four times would be worse than the one import edge
`IicfQueue/IicfCsr/IicfBitmask → IicfStack`. Fallback at merge: move them
verbatim into `Iicf/Basic.lean` and delete this section; no statement
changes.

**P6/D-bb — a composite assertion is `hr_comp`, spelled out.** The source
builds every IICF assertion as `hr_comp raw_assn rel` (extracts §3.1,
§4.1). Ours is the same shape written directly:
`stackAssn cap s d = ∃ᵃ xs, ⌜StackWf cap s xs⌝ ∗ (arrayAssn ×ₐ natAssn) (xs, cap - |s|) d`.
The existential is what makes the *unused* array slots abstract, which is
the point: `pop` leaves the popped value in place and no operation has to
zero anything. The alternative considered and rejected was a canonical
padding (`arrayAssn (… ++ replicate … 0)`), which needs no existential but
makes `pop` pay an extra `ir.aset` to re-canonicalize. The existential is
stripped once per rule by `hnr_pre_ex_pure` and reintroduced once by
`stackAssn_intro`.

**P6/D-bc — the frame matcher never looks inside a composite assertion,
so composite rules are hand-derived from synthesized *raw* rules.** P4's
`frameMatch` pairs conjuncts by `isDefEq` and its one retry splits
`prodAssn` (`conjunctsSplit`); it cannot split
`hnCtxt (stackAssn cap) s d` into an array conjunct and a scalar
conjunct, because that split sits under a `⌜⌝` and an `∃ᵃ`. So
`sepref_synth` is run on the **raw** goal — components spelled out,
abstract program the bind-chain of primitive mops — and the composite
`hnr` rule is derived from the synthesized theorem in four steps, none of
them a frame clause: the raw chain's *value* lemma, `hnRefine_reinterp`,
`hnRefine_pre_perm` for the association, and `fri` for the leftover post.
The *program* is synthesized for every operation in this file; only the
wrapper is written, and it is the same four lines each time. This is
design D6-P6-3's "hand-derived where the pipeline does not handle it",
read honestly. **No P4 file was edited.**

**P6/D-bd — cell names are binders, so no `_impl` definition is
emitted.** `sepref_synth` defines `<name>_impl` only when the synthesized
program is closed (`Sepref/Definition.lean`, `prog.hasFVar`). A structure
lives at *caller-chosen* cells (design D6-P6-2), so its rules quantify
over the cell names and the synthesized program has free variables. The
program is pinned instead by *stating* the composite rule at a
hand-written `Com`-valued definition (`pushCom`, `popCom`): the
derivation typechecks only if the synthesized program is that definition
unfolded, and a `#guard` pins each one at concrete names.

**P6/D-be — the stack grows *downward*, and this is forced by the P4
translator, not by taste.** With `top` = the number of elements (the
obvious choice) `pop` is `top := top - 1; r := S[top]`, and that program
**cannot be synthesized**: `transOp` commits to the first
`sepref_fr_rules` entry whose own side conditions close, `hnr_mop_binop`
(destination-taking) precedes `hnr_mop_binop_self` (in-place) in the
database, and the decrement therefore *takes* the scratch cell `r` that
the `aget` needs one step later. There is no backtracking into that
choice — the failure only surfaces in the next sub-goal, by which time
the rule has been committed. Turning the stack around fixes it with no
machinery at all: `top` is the *index of the top element*, the stack
occupies `[top, cap)`, empty is `top = cap`, and both operations then put
their `aget`/`aset` **before** the in-place index update, so the scratch
cell is already spent when the `binop` is translated and only
`hnr_mop_binop_self` can apply. Reported as a P4 finding
(greedy, non-backtracking scratch allocation); no P4 file was changed,
because the fix here is free and reordering the database would break
P4's own pinned `chain_impl`.

**P6/D-bf — emptiness is a fused guard on the `top` cell, never a boolean
operation** (design D6-P6-5). Two `sepref_cond_rules` entries,
`condRefine_stack_empty` (`top = cap`) and `condRefine_stack_nonempty`
(`top < cap`), read the length off the composite assertion. There is no
`isEmpty` op and no boolean cell, exactly as P4/D-af prescribes.

**P6/D-bg — `push` takes its value from a cell that survives it.** The
value operand stays owned (`hnCtxt natAssn v vc` is in both the pre- and
the postcondition), which is what lets the fill exercise push the loop
counter and then increment it in place.
-/

namespace Lax13Proofs.Refine.Iicf

open Sepref Ir NRest

/-! ## 1. The wave's shared bridges (P6/D-ba)

Four lemmas. `bindT_unit` normalizes a one-op prefix of a bind chain;
`hnr_pre_ex_pure` and `hnr_pre_pure_star` open a composite precondition;
`hnRefine_reinterp` closes a composite postcondition, and is the only one
with content — it is where the *abstract type* of a judgment changes,
from the raw components a synthesized rule delivers to the structure the
interface speaks of. -/

/-- Binding a one-op program is charging its cost and going on. -/
theorem bindT_unit {α β : Type} (x : α) (c : ECost) (f : α → NRest β ECost) :
    NRest.bindT (NRest.consume (NRest.returnT x) c) f = NRest.consume (f x) c := by
  rw [NRest.bindT_consume NRest.addSupContinuousB_acost, NRest.returnT_bindT]

/-- **The reinterpretation bridge.** A judgment whose abstract program is
a *deterministic* one-result program `consume (returnT r) t` at the raw
assertion `A` becomes a judgment at any assertion `R` and result `x` the
raw result entails. This is the source's `hr_comp` composition
specialized to the deterministic programs every structure operation is,
and it is the only place in P6-B where a judgment's abstract type
changes. -/
theorem hnRefine_reinterp {α β κ : Type} {Γ Γ' : Assn} {c : Com} {d : κ}
    {A : α → κ → Assn} {R : β → κ → Assn} {r : α} {x : β} {t : ECost}
    (h : hnRefine Γ c Γ' d A ((NRest.returnT r).consume t))
    (hent : A r d ⊢ R x d) :
    hnRefine Γ c Γ' d R ((NRest.returnT x).consume t) := by
  intro _ M F s cr hm hs
  rw [NRest.consume_returnT] at hm
  have hM : M = NRest.single x ((t : ECost) : WithBot ECost) := (NRest.rest_inj_iff.1 hm).symm
  obtain ⟨ra, Ca, hCa, w⟩ := hnRefineD h (NRest.consume_returnT r t) hs
  have hra : ra = r := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff] at hCa
    exact WithBot.coe_ne_bot hCa
  subst hra
  rw [NRest.single_self] at hCa
  refine ⟨x, Ca, ?_, ?_⟩
  · rw [hM, NRest.single_self]; exact hCa
  · refine wp_mono_ir (fun _ p hp => ?_) w
    exact start_entailsE hp
      (conj_entails_mono (entails_refl Γ') (conj_entails_mono hent (entails_refl (F ∗ GC))))

/-- Open a composite precondition of the `hr_comp` shape: an existential
over the representation, guarded by a pure well-formedness conjunct. -/
theorem hnr_pre_ex_pure {β α κ : Type} {P : β → Prop} {Δ : β → Assn} {Γ Γ' : Assn} {c : Com}
    {d : κ} {R : α → κ → Assn} {m : NRest α ECost}
    (h : ∀ y, P y → hnRefine (Δ y ∗ Γ) c Γ' d R m) :
    hnRefine ((∃ᵃ y, ⌜P y⌝ ∗ Δ y) ∗ Γ) c Γ' d R m := by
  rw [sepEx_sepConj]
  refine hnr_pre_ex_conv.2 fun y => ?_
  rw [sepConj_assoc]
  exact hnr_pre_pure_conv.2 (h y)

/-- …and the existential-free case (`IicfCsr`'s shape). -/
theorem hnr_pre_pure_star {α κ : Type} {P : Prop} {Δ Γ Γ' : Assn} {c : Com} {d : κ}
    {R : α → κ → Assn} {m : NRest α ECost} (h : P → hnRefine (Δ ∗ Γ) c Γ' d R m) :
    hnRefine ((⌜P⌝ ∗ Δ) ∗ Γ) c Γ' d R m := by
  rw [sepConj_assoc]
  exact hnr_pre_pure_conv.2 h

/-! ## 2. The stack assertion (P6/D-bb, P6/D-be) -/

/-- The backing array of a stack: `cap` slots, of which the *last* `|s|`
hold `s` top-to-bottom. Everything below index `cap - |s|` is
unconstrained — that is what the existential in `stackAssn` hides. -/
def StackWf (cap : ℕ) (s xs : List ℕ) : Prop :=
  xs.length = cap ∧ xs.drop (cap - s.length) = s

theorem StackWf.len_le {cap : ℕ} {s xs : List ℕ} (h : StackWf cap s xs) : s.length ≤ cap := by
  have hl := congrArg List.length h.2
  rw [List.length_drop, h.1] at hl
  omega

/-- The composite assertion (P6/D-bb): a stack of `s` at the cell pair
`d = (S, top)`, capacity `cap`, `top` the index of the top element. -/
def stackAssn (cap : ℕ) : List ℕ → String × String → Assn := fun s d =>
  ∃ᵃ xs, ⌜StackWf cap s xs⌝ ∗ ((arrayAssn ×ₐ natAssn) (xs, cap - s.length) d)

/-- The unfold lemma the P4 frame matcher never applies and every rule
below does: the composite is the two cell conjuncts under the
representation existential. Definitional. -/
theorem stackAssn_unfold (cap : ℕ) (s : List ℕ) (d : String × String) :
    hnCtxt (stackAssn cap) s d
      = ∃ᵃ xs, ⌜StackWf cap s xs⌝ ∗
          (hnCtxt arrayAssn xs d.1 ∗ hnCtxt natAssn (cap - s.length) d.2) := rfl

/-- Closing the composite: a well-formed representation *is* a stack. -/
theorem stackAssn_intro (cap : ℕ) (s xs : List ℕ) (d : String × String)
    (hwf : StackWf cap s xs) :
    (hnCtxt arrayAssn xs d.1 ∗ hnCtxt natAssn (cap - s.length) d.2)
      ⊢ hnCtxt (stackAssn cap) s d :=
  fun _ hh => ⟨xs, predLift_sepConj_iff.2 ⟨hwf, hh⟩⟩

/-- …in the `prodAssn` spelling `hnRefine_reinterp` hands it. -/
theorem stackAssn_intro' (cap : ℕ) (s xs : List ℕ) (n : ℕ) (d : String × String)
    (hwf : StackWf cap s xs) (hn : n = cap - s.length) :
    (arrayAssn ×ₐ natAssn) (xs, n) d ⊢ stackAssn cap s d := by
  subst hn
  exact stackAssn_intro cap s xs d hwf

/-- Opening the composite in a precondition (P6/D-bc, step 1). -/
theorem stack_pre {cap : ℕ} {s : List ℕ} {dS : String × String} {Γ Γ' : Assn} {c : Com}
    {α κ : Type} {d : κ} {R : α → κ → Assn} {m : NRest α ECost}
    (h : ∀ xs : List ℕ, StackWf cap s xs →
      hnRefine ((hnCtxt arrayAssn xs dS.1 ∗ hnCtxt natAssn (cap - s.length) dS.2) ∗ Γ)
        c Γ' d R m) :
    hnRefine (hnCtxt (stackAssn cap) s dS ∗ Γ) c Γ' d R m :=
  hnr_pre_ex_pure h

/-- **Establishment from junk.** A caller who owns an array of `cap`
slots holding anything and a cell holding `cap` owns an empty stack. This
replaces the source's `*_new` (design D6-P6-2): nothing is allocated. -/
theorem stackAssn_init (cap : ℕ) (xs : List ℕ) (d : String × String) (hlen : xs.length = cap) :
    (hnCtxt arrayAssn xs d.1 ∗ hnCtxt natAssn cap d.2) ⊢ hnCtxt (stackAssn cap) [] d := by
  have h : cap - ([] : List ℕ).length = cap := by simp
  rw [← h]
  exact stackAssn_intro cap [] xs d ⟨hlen, by simp [hlen]⟩

/-- **Release to junk.** The structure's cells are owned but dead — the
entailment that replaces the source's `*_free`. -/
theorem stackAssn_release (cap : ℕ) (s : List ℕ) (d : String × String) :
    hnCtxt (stackAssn cap) s d ⊢ junkArray d.1 ∗ junkCell d.2 := by
  rintro h ⟨xs, hh⟩
  obtain ⟨-, hh⟩ := predLift_sepConj_iff.1 hh
  exact conj_entails_mono (arrayAssn_entails_junkArray xs d.1)
    (natAssn_entails_junkCell (cap - s.length) d.2) h hh

/-! ## 3. Refute before prove

The two operations, as computable twins on lists, executed before
anything is proved about them. `pushTwin`/`popTwin` are the *values* the
interface operations of §4 return, `repPush`/`repPop` are the values the
*raw* chains of §5 return, and `wfTwin` decides `StackWf`, so the three
together check the representation invariant the whole file rests on. -/

/-- The abstract push: `v` on top. -/
def pushTwin (s : List ℕ) (v : ℕ) : List ℕ := v :: s

/-- The abstract pop: the top and the rest. -/
def popTwin (s : List ℕ) : ℕ × List ℕ := (s.head!, s.tail)

/-- The representation after a push: the slot *below* the old top. -/
def repPush (xs : List ℕ) (n v : ℕ) : List ℕ × ℕ := (xs.set (n - 1) v, n - 1)

/-- …and after a pop: the array is *untouched* (P6/D-bb). -/
def repPop (xs : List ℕ) (n : ℕ) : ℕ × (List ℕ × ℕ) := (xs[n]!, (xs, n + 1))

/-- `StackWf`, decided. -/
def wfTwin (cap : ℕ) (s xs : List ℕ) : Bool :=
  decide (xs.length = cap) && decide (xs.drop (cap - s.length) = s)

-- Push then pop is the identity on the abstract stack.
#guard popTwin (pushTwin [3, 1] 7) = (7, [3, 1])
#guard pushTwin [] 5 = [5]
#guard popTwin [4, 2, 9] = (4, [2, 9])

-- The representation invariant is established by `init` …
#guard wfTwin 4 [] [0, 0, 0, 0] = true
-- … maintained by push (`top` starts at `cap = 4`) …
#guard repPush [0, 0, 0, 0] 4 7 = ([0, 0, 0, 7], 3)
#guard wfTwin 4 [7] [0, 0, 0, 7] = true
#guard repPush [0, 0, 0, 7] 3 1 = ([0, 0, 1, 7], 2)
#guard wfTwin 4 [1, 7] [0, 0, 1, 7] = true
-- … and by pop, which leaves the array alone.
#guard repPop ([0, 0, 1, 7] : List ℕ) 2 = (1, ([0, 0, 1, 7], 3))
#guard popTwin [1, 7] = (1, [7])
#guard wfTwin 4 [7] ([0, 0, 1, 7] : List ℕ) = true

-- **Negative control 1.** A capacity that does not match the array is
-- not well-formed.
/--
error: Expression
  decide (wfTwin 3 [] [0, 0, 0, 0] = true)
did not evaluate to `true`
-/
#guard_msgs in
#guard wfTwin 3 [] [0, 0, 0, 0] = true

-- **Negative control 2.** The stack grows downward (P6/D-be): the
-- upward spelling is refutable.
/--
error: Expression
  decide (wfTwin 4 [1, 7] [1, 7, 0, 0] = true)
did not evaluate to `true`
-/
#guard_msgs in
#guard wfTwin 4 [1, 7] ([1, 7, 0, 0] : List ℕ) = true

/-! ## 4. The interface operations (design D6-P6-1: the cost *is* the
interface)

Two operations, each an `NRest` program on the abstract `List ℕ` with an
explicit `ECost` multiset of ir currencies — the multiset the synthesized
program of §5 actually spends. -/

/-- `push`: one decrement, one array write, one tuple step. -/
noncomputable def pushCost : ECost :=
  irUnit Currency.sub + irUnit Currency.aset + irUnit Currency.skip

/-- `pop`: one array read, one increment, two tuple steps (the
representation pair, then the result pair). -/
noncomputable def popCost : ECost :=
  irUnit Currency.aget + irUnit Currency.add + irUnit Currency.skip + irUnit Currency.skip

/-- The interface operation `push` (design D6-P6-5's `assert len < cap`). -/
noncomputable def mopPush (cap : ℕ) (s : List ℕ) (v : ℕ) : NRest (List ℕ) ECost :=
  NRest.bindT (NRest.assert (s.length < cap)) fun _ =>
    NRest.consume (NRest.returnT (v :: s)) pushCost

/-- The interface operation `pop`: the top *and* the shortened stack, the
first destined for a scratch cell, the second for the structure's own. -/
noncomputable def mopPop (s : List ℕ) : NRest (ℕ × List ℕ) ECost :=
  NRest.bindT (NRest.assert (s ≠ [])) fun _ =>
    NRest.consume (NRest.returnT (s.head!, s.tail)) popCost

theorem mopPush_def (cap : ℕ) (s : List ℕ) (v : ℕ) :
    mopPush cap s v = NRest.bindT (NRest.assert (s.length < cap)) fun _ =>
      NRest.consume (NRest.returnT (v :: s)) pushCost := rfl

theorem mopPop_def (s : List ℕ) :
    mopPop s = NRest.bindT (NRest.assert (s ≠ [])) fun _ =>
      NRest.consume (NRest.returnT (s.head!, s.tail)) popCost := rfl

/-! ## 5. The raw chains and their synthesis (P6/D-bc, P6/D-bd, P6/D-be) -/

/-- The raw chain `push` expands to: unbump, write, tuple. -/
noncomputable def pushRaw (xs : List ℕ) (n v : ℕ) : NRest (List ℕ × ℕ) ECost :=
  NRest.bindT (mopBinop .sub n 1) fun n' =>
    NRest.bindT (mopAset xs n' v) fun xs' => mopPair xs' n'

/-- The raw chain `pop` expands to: read, bump, tuple, tuple. -/
noncomputable def popRaw (xs : List ℕ) (n : ℕ) : NRest (ℕ × (List ℕ × ℕ)) ECost :=
  NRest.bindT (mopAget xs n) fun w =>
    NRest.bindT (mopBinop .add n 1) fun n' =>
      NRest.bindT (mopPair xs n') fun p => mopPair w p

theorem pushRaw_eq (xs : List ℕ) (n v : ℕ) (h : n - 1 < xs.length) :
    pushRaw xs n v = NRest.consume (NRest.returnT (xs.set (n - 1) v, n - 1)) pushCost := by
  show NRest.bindT (mopBinop .sub n 1) _ = _
  rw [mopBinop_def, bindT_unit]
  simp only [Imp.Bop.apply_sub, binopCurrency_sub]
  rw [mopAset_def, NRest.assert_pos h, NRest.returnT_bindT, bindT_unit, mopPair_def,
    NRest.consume_consume, NRest.consume_consume]
  simp only [pushCost]

theorem popRaw_eq (xs : List ℕ) (n : ℕ) (h : n < xs.length) :
    popRaw xs n = NRest.consume (NRest.returnT (xs[n]!, (xs, n + 1))) popCost := by
  show NRest.bindT (mopAget xs n) _ = _
  rw [mopAget_def, NRest.assert_pos h, NRest.returnT_bindT, bindT_unit, mopBinop_def,
    bindT_unit]
  simp only [Imp.Bop.apply_add, binopCurrency_add]
  rw [mopPair_def, bindT_unit, mopPair_def, NRest.consume_consume, NRest.consume_consume,
    NRest.consume_consume]
  simp only [popCost]

/-- The program `push` compiles to (P6/D-bd: the pin). -/
def pushCom (S top vc one : String) : Com :=
  .seq (.binop .sub top top one) (.seq (.aset S top vc) .skip)

/-- The program `pop` compiles to. -/
def popCom (S top r one : String) : Com :=
  .seq (.aget r S top) (.seq (.binop .add top top one) (.seq .skip .skip))

#guard pushCom "S" "top" "v" "one" =
  Com.seq (Com.binop Imp.Bop.sub "top" "top" "one")
    (Com.seq (Com.aset "S" "top" "v") Com.skip)

#guard popCom "S" "top" "r" "one" =
  Com.seq (Com.aget "r" "S" "top")
    (Com.seq (Com.binop Imp.Bop.add "top" "top" "one") (Com.seq Com.skip Com.skip))

sepref_synth pushSynth (S top vc one : String) (xs : List ℕ) (n v : ℕ) :
  hnRefine (hnCtxt arrayAssn xs S ∗ hnCtxt natAssn n top ∗ hnCtxt natAssn v vc ∗
      hnCtxt natAssn 1 one)
    _ _ (S, top) (arrayAssn ×ₐ natAssn) (pushRaw xs n v)

sepref_synth popSynth (S top r one : String) (xs : List ℕ) (n : ℕ) :
  hnRefine (hnCtxt arrayAssn xs S ∗ hnCtxt natAssn n top ∗ junkCell r ∗
      hnCtxt natAssn 1 one)
    _ _ (r, (S, top)) (natAssn ×ₐ (arrayAssn ×ₐ natAssn)) (popRaw xs n)

/-! ## 6. The composite rules (P6/D-bc)

One `sepref_fr_rules` entry per interface operation, each derived from
the synthesized raw theorem above in the same four steps: open the
composite precondition, restate the raw chain at its value, reinterpret
the raw result as the structure, and let `fri` reconcile the leftover
post. -/

/-- The one list fact the push rule needs: writing at `k` and dropping to
`k` exposes the written value. -/
theorem drop_set_self {xs : List ℕ} {k v : ℕ} (h : k < xs.length) :
    (xs.set k v).drop k = v :: xs.drop (k + 1) := by
  have h' : k < (xs.set k v).length := by simpa using h
  rw [List.drop_eq_getElem_cons h', List.getElem_set_self, List.drop_set]
  simp

@[sepref_fr_rules]
theorem hnr_mop_push (cap : ℕ) (s : List ℕ) (v : ℕ) (S top vc one : String) :
    hnRefine (hnCtxt (stackAssn cap) s (S, top) ∗ hnCtxt natAssn v vc ∗ hnCtxt natAssn 1 one)
      (pushCom S top vc one) (hnCtxt natAssn v vc ∗ hnCtxt natAssn 1 one) (S, top)
      (stackAssn cap) (mopPush cap s v) := by
  rw [mopPush_def]
  refine hnr_assert fun hlt => ?_
  refine stack_pre fun xs hwf => ?_
  have hle := hwf.len_le
  have hidx : cap - s.length - 1 < xs.length := by rw [hwf.1]; omega
  have hsyn := hnRefine_abs_cong (pushRaw_eq xs (cap - s.length) v hidx).symm
    (pushSynth S top vc one xs (cap - s.length) v)
  have hwf' : StackWf cap (v :: s) (xs.set (cap - s.length - 1) v) := by
    refine ⟨by simpa using hwf.1, ?_⟩
    have hk : cap - (v :: s).length = cap - s.length - 1 := by simp; omega
    have hk1 : cap - s.length - 1 + 1 = cap - s.length := by omega
    rw [hk, drop_set_self hidx, hk1, hwf.2]
  have hent : (arrayAssn ×ₐ natAssn) (xs.set (cap - s.length - 1) v, cap - s.length - 1) (S, top)
      ⊢ stackAssn cap (v :: s) (S, top) :=
    stackAssn_intro' cap (v :: s) _ _ (S, top) hwf' (by simp; omega)
  exact hnRefine_pre_perm (by ac_rfl)
    (hnRefine_cons_post (hnRefine_reinterp hsyn hent) (by fri))

@[sepref_fr_rules]
theorem hnr_mop_pop (cap : ℕ) (s : List ℕ) (S top r one : String) :
    hnRefine (hnCtxt (stackAssn cap) s (S, top) ∗ junkCell r ∗ hnCtxt natAssn 1 one)
      (popCom S top r one) (hnCtxt natAssn 1 one) (r, (S, top))
      (natAssn ×ₐ stackAssn cap) (mopPop s) := by
  rw [mopPop_def]
  refine hnr_assert fun hne => ?_
  obtain ⟨a, t, rfl⟩ : ∃ a t, s = a :: t := by
    cases s with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, t, rfl⟩
  refine stack_pre fun xs hwf => ?_
  have hle := hwf.len_le
  have hidx : cap - (a :: t).length < xs.length := by
    rw [hwf.1]; simp only [List.length_cons] at hle ⊢; omega
  have hd := List.drop_eq_getElem_cons (l := xs) hidx
  rw [hwf.2] at hd
  injection hd with hA hT
  have hval : xs[cap - (a :: t).length]! = a := by
    rw [getElem!_pos xs _ hidx, ← hA]
  have hkey : cap - (a :: t).length + 1 = cap - t.length := by
    simp only [List.length_cons] at hle ⊢; omega
  have hwft : StackWf cap t xs := ⟨hwf.1, by rw [← hkey, ← hT]⟩
  have hsyn := hnRefine_abs_cong (popRaw_eq xs (cap - (a :: t).length) hidx).symm
    (popSynth S top r one xs (cap - (a :: t).length))
  have hent : (natAssn ×ₐ (arrayAssn ×ₐ natAssn))
      (xs[cap - (a :: t).length]!, (xs, cap - (a :: t).length + 1)) (r, (S, top))
      ⊢ (natAssn ×ₐ stackAssn cap) (a, t) (r, (S, top)) := by
    refine conj_entails_mono ?_ (stackAssn_intro' cap t xs _ (S, top) hwft hkey)
    rw [hval]
  have hgoal : ((NRest.returnT ((a :: t).head!, (a :: t).tail)).consume popCost)
      = (NRest.returnT (a, t)).consume popCost := by simp
  rw [hgoal]
  exact hnRefine_pre_perm (by ac_rfl)
    (hnRefine_cons_post (hnRefine_reinterp hsyn hent) (by fri))

/-! ## 7. Emptiness as a fused guard (P6/D-bf, design D6-P6-5)

Two `CondRefine` rules on the `top` cell. There is no `isEmpty`
operation and no boolean cell: the IR evaluates the condition inside the
`ite`/`while` charge (P4/D-af), so emptiness is a *fact about the
ownership*, not a program. -/

/-- The `top` cell's contents, read out of the composite assertion. -/
theorem stackAssn_top_vars {cap : ℕ} {s : List ℕ} {S top : String} {F : Assn} {st : State}
    {cr : ECost} (hs : irSTATE (hnCtxt (stackAssn cap) s (S, top) ∗ F) (st, cr)) :
    st.vars top = some (cap - s.length) ∧ s.length ≤ cap := by
  rw [stackAssn_unfold, sepEx_sepConj] at hs
  obtain ⟨xs, hxs⟩ := hs
  rw [sepConj_assoc] at hxs
  obtain ⟨hwf, hxs⟩ := predLift_sepConj_iff.1 hxs
  refine ⟨?_, hwf.len_le⟩
  simp only [hnCtxt_def, natAssn_def, arrayAssn_def] at hxs
  rw [sepConj_assoc] at hxs
  exact ptoVar_vars (irSTATE_rot hxs)

@[sepref_cond_rules]
theorem condRefine_stack_nonempty (cap : ℕ) (s : List ℕ) (S top : String) :
    CondRefine (hnCtxt (stackAssn cap) s (S, top)) (.lt (.cell top) (.lit cap))
      (decide (s ≠ [])) := by
  intro F st cr hs
  obtain ⟨hv, hle⟩ := stackAssn_top_vars hs
  have h : (cap - s.length < cap) = (s ≠ []) := by
    cases s with
    | nil => simp
    | cons a t =>
      simp only [List.length_cons, ne_eq, reduceCtorEq, not_false_eq_true, eq_iff_iff,
        iff_true]
      simp only [List.length_cons] at hle
      omega
  simp [hv, h]

@[sepref_cond_rules]
theorem condRefine_stack_empty (cap : ℕ) (s : List ℕ) (S top : String) :
    CondRefine (hnCtxt (stackAssn cap) s (S, top)) (.eq (.cell top) (.lit cap))
      (decide (s = [])) := by
  intro F st cr hs
  obtain ⟨hv, hle⟩ := stackAssn_top_vars hs
  have h : (s = []) ↔ (cap - s.length = cap) := by
    cases s with
    | nil => simp
    | cons a t =>
      simp only [List.length_cons] at hle
      simp only [reduceCtorEq, List.length_cons, false_iff]
      omega
  simp [hv, h]
  rfl

/-! ## 8. Exercise: push–drain sum (the phase's acceptance criterion)

Two abstract loops, both pushed through `sepref_synth` consuming **only**
the registered rules of §6 and §7 — no bespoke tactic, no hand-written
frame clause, no `∗`-rearrangement. The first fills a stack with
`0, 1, …, n-1`; the second drains it, accumulating the sum. Each loop's
`LOOP_VARIANT` hypothesis is discharged by a separate variant lemma
(P4/D-cv). -/

namespace Exercise

/-! ### Refute before prove: the two loops, executed -/

/-- The fill loop's twin. -/
def fillRun (n : ℕ) : ℕ → ℕ × List ℕ → ℕ × List ℕ
  | 0, st => st
  | k + 1, st => if st.1 < n then fillRun n k (st.1 + 1, st.1 :: st.2) else st

/-- The drain loop's twin. -/
def drainRun : ℕ → ℕ × List ℕ → ℕ × List ℕ
  | 0, st => st
  | k + 1, st => if st.2 ≠ [] then drainRun k (st.1 + st.2.head!, st.2.tail) else st

/-- Fill with `0 … n-1`, then drain, summing. -/
def pushDrainSum (n : ℕ) : ℕ := (drainRun n (0, (fillRun n n (0, [])).2)).1

#guard (fillRun 4 4 (0, [])).2 = [3, 2, 1, 0]
#guard pushDrainSum 4 = 6
#guard pushDrainSum 5 = 10
#guard pushDrainSum 0 = 0
#guard pushDrainSum 1 = 0
-- …against an independent decider of the same quantity.
#guard pushDrainSum 5 = (List.range 5).sum
#guard pushDrainSum 7 = (List.range 7).sum

-- **Negative control.** A wrong expected sum fails, and says so.
/--
error: Expression
  decide (pushDrainSum 5 = 11)
did not evaluate to `true`
-/
#guard_msgs in
#guard pushDrainSum 5 = 11

/-! ### The fill loop -/

/-- The invariant: the stack holds exactly as many elements as the
counter counts. It is what makes `push`'s capacity assertion pass. -/
def fillI : ℕ × List ℕ → Prop := fun st => st.2.length = st.1

/-- The guard: `i < n`. -/
def fillBf (n : ℕ) : ℕ × List ℕ → Bool := fun st => decide (st.1 < n)

/-- The body: push the counter, bump it, retuple. -/
noncomputable def fillF (cap : ℕ) : ℕ × List ℕ → NRest (ℕ × List ℕ) ECost := fun st =>
  NRest.bindT (mopPush cap st.2 st.1) fun s' =>
    NRest.bindT (mopBinop .add st.1 1) fun i' => mopPair i' s'

/-- One iteration's price: a push, an increment and the tuple. -/
noncomputable def fillCost : ECost := pushCost + irUnit Currency.add + irUnit Currency.skip

theorem fillF_eq (cap : ℕ) (st : ℕ × List ℕ) (h : st.2.length < cap) :
    fillF cap st = NRest.consume (NRest.returnT (st.1 + 1, st.1 :: st.2)) fillCost := by
  show NRest.bindT (mopPush cap st.2 st.1) _ = _
  rw [mopPush_def, NRest.assert_pos h, NRest.returnT_bindT, bindT_unit, mopBinop_def,
    bindT_unit, mopPair_def, NRest.consume_consume, NRest.consume_consume]
  simp only [fillCost, Imp.Bop.apply_add, binopCurrency_add]

theorem fill_variant (cap n : ℕ) (hn : n ≤ cap) :
    LOOP_VARIANT fillI (fillBf n) (fillF cap) (fun st => n - st.1) := by
  intro st st' hI hb hle
  have hI' : st.2.length = st.1 := hI
  have hb' : st.1 < n := by simpa [fillBf] using hb
  have hlt : st.2.length < cap := by omega
  rw [fillF_eq cap st hlt, NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hst : st' = (st.1 + 1, st.1 :: st.2) := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  subst hst
  show n - (st.1 + 1) < n - st.1
  omega

-- The variant annotation below is inert since R0/D-b: no rule in
-- `sepref_comb_rules` reads a `LOOP_VARIANT` any more. The signature
-- is kept because this synthesis theorem is landed capital.
set_option linter.unusedVariables false in
sepref_synth stackFill (cap n : ℕ)
    (hv : LOOP_VARIANT fillI (fillBf n) (fillF cap) (fun st => n - st.1)) :
  hnRefine (hnCtxt (natAssn ×ₐ stackAssn cap) (0, []) ("i", ("S", "top")) ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn n "n")
    _ _ ("i", ("S", "top")) (natAssn ×ₐ stackAssn cap)
    (irWhileIT fillI (fillBf n) (fillF cap) (0, []))

/-! ### The drain loop

The capacity is concrete here (`8`) for one reason only: the emptiness
guard is `top < cap`, so a symbolic capacity would put a free variable in
the *program* and `sepref_synth` would emit no `_impl` definition to pin
(P6/D-bd). Nothing else in the derivation depends on it. -/

/-- No invariant is needed: the guard already gives `pop`'s
nonemptiness. -/
def drainI : ℕ × List ℕ → Prop := fun _ => True

/-- The guard: the stack is nonempty — the fused `top < cap` of §7. -/
def drainBf : ℕ × List ℕ → Bool := fun st => decide (st.2 ≠ [])

/-- The body: pop into the scratch cell, accumulate, retuple. -/
noncomputable def drainF : ℕ × List ℕ → NRest (ℕ × List ℕ) ECost := fun st =>
  NRest.bindT (mopPop st.2) fun p =>
    NRest.bindT (mopBinop .add st.1 p.1) fun acc' => mopPair acc' p.2

/-- One iteration's price: a pop, an addition and the tuple. -/
noncomputable def drainCost : ECost := popCost + irUnit Currency.add + irUnit Currency.skip

theorem drainF_eq (st : ℕ × List ℕ) (h : st.2 ≠ []) :
    drainF st
      = NRest.consume (NRest.returnT (st.1 + st.2.head!, st.2.tail)) drainCost := by
  show NRest.bindT (mopPop st.2) _ = _
  rw [mopPop_def, NRest.assert_pos h, NRest.returnT_bindT, bindT_unit, mopBinop_def,
    bindT_unit, mopPair_def, NRest.consume_consume, NRest.consume_consume]
  simp only [drainCost, Imp.Bop.apply_add, binopCurrency_add]

theorem drain_variant : LOOP_VARIANT drainI drainBf drainF (fun st => st.2.length) := by
  intro st st' _ hb hle
  have hb' : st.2 ≠ [] := by simpa [drainBf] using hb
  rw [drainF_eq st hb', NRest.consume_returnT, returnT_le_rest_iff] at hle
  have hst : st' = (st.1 + st.2.head!, st.2.tail) := by
    by_contra hne
    rw [NRest.single_of_ne hne, le_bot_iff, ← WithBot.coe_zero] at hle
    exact WithBot.coe_ne_bot hle
  subst hst
  show st.2.tail.length < st.2.length
  cases hs : st.2 with
  | nil => exact absurd hs hb'
  | cons a t => simp

-- The variant annotation below is inert since R0/D-b: no rule in
-- `sepref_comb_rules` reads a `LOOP_VARIANT` any more. The signature
-- is kept because this synthesis theorem is landed capital.
set_option linter.unusedVariables false in
sepref_synth stackDrain (s₀ : List ℕ)
    (hv : LOOP_VARIANT drainI drainBf drainF (fun st => st.2.length)) :
  hnRefine (hnCtxt (natAssn ×ₐ stackAssn 8) (0, s₀) ("acc", ("S", "top")) ∗
      junkCell "r" ∗ hnCtxt natAssn 1 "one")
    _ _ ("acc", ("S", "top")) (natAssn ×ₐ stackAssn 8)
    (irWhileIT drainI drainBf drainF (0, s₀))

-- The synthesized fill loop, pinned: the composite `push` inlined, the
-- counter bumped in place, the tuple a `skip`.
#guard stackFill_impl =
  Com.while (Cond.lt (Operand.cell "i") (Operand.cell "n"))
    (Com.seq (Com.seq (Com.binop Imp.Bop.sub "top" "top" "one")
        (Com.seq (Com.aset "S" "top" "i") Com.skip))
      (Com.seq (Com.binop Imp.Bop.add "i" "i" "one") Com.skip))

-- …and the drain loop: the fused emptiness guard `top < 8` is the
-- condition the tool *synthesized* from `decide (s ≠ [])`.
#guard stackDrain_impl =
  Com.while (Cond.lt (Operand.cell "top") (Operand.lit 8))
    (Com.seq (Com.seq (Com.aget "r" "S" "top")
        (Com.seq (Com.binop Imp.Bop.add "top" "top" "one") (Com.seq Com.skip Com.skip)))
      (Com.seq (Com.binop Imp.Bop.add "acc" "acc" "r") Com.skip))

/-- The fill loop with its variant discharged. -/
theorem stackFill' (cap n : ℕ) (hn : n ≤ cap) :
    hnRefine (hnCtxt (natAssn ×ₐ stackAssn cap) (0, []) ("i", ("S", "top")) ∗
        hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn n "n")
      stackFill_impl (hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn n "n") ("i", ("S", "top"))
      (natAssn ×ₐ stackAssn cap) (irWhileIT fillI (fillBf n) (fillF cap) (0, [])) :=
  stackFill cap n (fill_variant cap n hn)

/-- The drain loop with its variant discharged. -/
theorem stackDrain' (s₀ : List ℕ) :
    hnRefine (hnCtxt (natAssn ×ₐ stackAssn 8) (0, s₀) ("acc", ("S", "top")) ∗
        junkCell "r" ∗ hnCtxt natAssn 1 "one")
      stackDrain_impl (junkCell "r" ∗ hnCtxt natAssn 1 "one") ("acc", ("S", "top"))
      (natAssn ×ₐ stackAssn 8) (irWhileIT drainI drainBf drainF (0, s₀)) :=
  stackDrain s₀ drain_variant

/-- info: 'Lax13Proofs.Refine.Iicf.hnr_mop_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_push

/-- info: 'Lax13Proofs.Refine.Iicf.hnr_mop_pop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_pop

/-- info: 'Lax13Proofs.Refine.Iicf.Exercise.stackFill'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stackFill'

/-- info: 'Lax13Proofs.Refine.Iicf.Exercise.stackDrain'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stackDrain'

end Exercise

/-! ## 9. Telemetry for the whole P6-B wave

Recorded here because `IicfStack.lean` is the wave's lead file.

* **Files and size.** `IicfStack` 701 lines (374 of Lean), `IicfQueue`
  590 (360), `IicfCsr` 424 (228), `IicfBitmask` 567 (296) — 2282 lines,
  1258 of them Lean, by a nesting-aware blank/comment scan.

* **Operations, and how each impl was produced.** Every operation's
  `Ir.Com` was produced by `sepref_synth` on the raw component-level
  goal — `push`, `pop`, `enq`, `deq`, `rowStart`/`slotTarget` (one
  synthesis, two uses), `rowEnd`, `bmEmpty`, `bmInsert`, `bmMem`: nine
  syntheses, nine programs, none written by hand. What *is* written by
  hand is the four-line composite wrapper of P6/D-bc, once per
  operation.

* **Exercises: nine `sepref_synth` invocations, zero frame clauses.**
  `stackFill`, `stackDrain`, `queueFill`, `queueDrain`, `csrDegree`,
  `csrRowWalk`, `bmFill`, `bmCount`, `bmBranch`. Each is an abstract
  program plus a precondition; none of them contains a single
  `sepConj_assoc`, `sepConj_comm`, `ac_rfl`-on-assertions, `fri`,
  `hnRefine_pre_perm` or `hnRefine_frame` step, and none needs a tactic
  the pipeline does not already run. Six of the nine are loops, each
  with its `LOOP_VARIANT` discharged by a separate variant lemma
  (P4/D-cv); all nine synthesized programs are `#guard`-pinned.

  The wave's `∗`-shaped hand steps are counted honestly and are all in
  the *rule wrappers*, never in an exercise: seven `ac_rfl`s inside
  `hnRefine_pre_perm`/`hnRefine_frame_perm` (each a pure permutation of
  the caller's own conjunct list) and nine `fri` calls reconciling a
  synthesized postcondition with the composite one.

* **Refute before prove.** Each file opens with computable twins of its
  operations and of its representation invariant, `#guard`ed on concrete
  data before any `hnr` proof, with two negative controls per file (one
  per file for the bitmask's two, one for the exercises). One of them
  fired for real: the CSR row-sum cross-check in `IicfCsr.lean` §2 was
  wrong on first writing and the `#guard` refuted it.

* **Axioms.** `#print axioms` is pinned for every composite rule and
  every exercise theorem: all are `[propext, Classical.choice,
  Quot.sound]` and nothing else. No `sorry`, no new axiom.

* **P4 edits: none.** The three pipeline limits this wave hit
  (P6/D-be's greedy scratch allocation, P6/D-bc's opaque composite
  conjuncts, P6/D-br's universally quantified bind result) were all
  worked around in P6-B's own files. -/

end Lax13Proofs.Refine.Iicf
