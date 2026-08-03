import Lax13Proofs.Refine.Sepref.HeapAlloc
import Lax13Proofs.Compile

/-!
# The compiled space-budget probe (ledger E29, leaf P4.5.D)

P4.5 repealed "peak memory equals total allocation": with a real
allocator only the **live set plus whatever LIFO cannot reclaim** has to
fit.  That repeal is safe for time and *not* automatically safe for
space, and on the consumer's path space is the scarcer resource.  This
file compiles the space side of the repeal, in both directions, over a
driver-shaped skeleton built from the landed allocator primitives
(`allocProg` / `freeProg` of `Refine/Sepref/HeapAlloc.lean`).

## The hazard this file exists to prevent

A LIFO `free` **decreases** the bump pointer.  So the *final* value of
`hp` is not the *peak*, and a theorem bounding only the final `hp` is
vacuous as a space statement: it is satisfied by a program that
allocates `n ^ (1 + ε)` cells and frees them all.  §7's
`final_hp_is_not_peak` compiles exactly that counterexample — for
`wastefulCom K` the final bump pointer is back where it started while an
intermediate state sits `K` above it — so the difference between the two
statement forms is a theorem here and not a comment.

Everything positive below is therefore stated as `PeakLe`: a bound on
`hpOf s'` for **every** state `s'` the run passes through
(`Mid`, §1), proved by induction over the loop structure (§3's
`peak_while`), never by evaluating the end state.

The gap is not hypothetical, and not confined to a contrived program.
`run_reuseSkel` and `reuse_peak_attained` (§8) give it at the *positive*
skeleton itself: the final bump pointer is `setup` above entry, an
intermediate one is `setup + aw`.  And `no_word_size_for_wasteful` (§9)
closes the circle — `wastefulCom K` satisfies the final-`hp` condition at
every `K` while its peak is refuted at every admissible word length, so
the two statement forms disagree on a concrete program.

## What is compiled

* **§1–§3, the peak calculus.**  `Mid c s s'` is the intermediate-state
  relation of the IR's own big-step semantics: `s'` is `s`, or the end
  of a completed run of `c`, or an intermediate state of a component.
  `NetLe c g` bounds the *net* growth of `hp` across a completed run,
  `PeakLe c p` bounds it at every intermediate state.  The one rule that
  carries the whole argument is `peak_while`: a loop whose body has
  **zero net growth** has the body's peak, *whatever the iteration
  count* — that is LIFO reuse, in the currency the consumer cares about.

* **§4, the skeleton.**  A setup phase sized in `|x|`, then
  `turns × levels` arena passes, in three flavours: `reuseSkel` (each
  pass carves an arena and gives it back — LIFO), `ownedSkel` (the arena
  is allocated once in setup and threaded — caller-owned), `freshSkel`
  (each pass carves a fresh arena and never gives it back).  All
  parameters are symbolic; C0-shaped numbers appear only in `#guard`s.

* **§9b, the shape a real driver has — and the answer to "which of the
  three".**  A recursive per-arena ND-MC-style driver is **none of the
  three above**: it is `nestedSkel`, which within a turn descends
  `levels` deep holding one arena live per level and then unwinds LIFO.
  Its peak is `setup + levels * aw` — `peak_nestedSkel` — so arenas
  compose with **depth** but not with **turns**, strictly between
  `reuseSkel`'s `setup + aw` and `freshSkel`'s
  `setup + turns * levels * aw`.  **What such a driver must maintain to
  stay inside the budget is therefore not "free everything" but
  `levels * aw = O(|x|)`: bounded recursion depth times per-level
  arena.**  That is not assumed here — `nested_fits_iff` is an `↔`, and
  `no_word_size_for_nested` is the compiled statement that it can fail:
  once the depth grows with `n`, no admissible word length rescues the
  descending driver either.

* **§5–§6, the positive result.**  `peak_reuseSkel` and
  `peak_ownedSkel`: the peak growth is `setup + aw`, **independent of
  `turns` and `levels`**.  `reuse_fits_linear` cashes that into
  `Layout.FitsWords` at a word length `w` with `2 ^ w` linear in `|x|`,
  and `reuse_fits_at_admissible_word` (§9) does it at a `w` the C0-shaped
  domain itself admits — which is the comparison the negative result
  demands, since that result kills *every* admissible `w`.

* **§8, the runs.**  A `PeakLe` bound over an unrunnable program says
  nothing, so `run_skel` constructs a symbolic run of all three
  skeletons, `run_countedLoop` doing the counting.
  `reuse_peak_attained` then shows the positive bound is *attained*: it
  is the peak, not a loose over-estimate.

* **§9, the negative control.**  `run_freshSkel` gives the fresh
  variant's bump pointer as
  `hp₀ + setup + turns * levels * aw`.  `no_word_size_for_fresh` is then
  `Lax3Proofs.Refine.BridgeSeamProbe.no_word_size_for_sparse`'s shape:
  for every constant `c` and every instance past that constant's
  crossover, the C0-shaped domain admits a word length `w` at which
  `Layout.FitsWords` and the space budget are **jointly unsatisfiable** —
  no word size rescues the fresh discipline.  The crossover is inhabited
  at `Σ|X_c| = n ^ (3/2)`, i.e. already at *sub-quadratic* fresh
  allocation.

* **§10, registration discipline (E29's other half).**  `mentions
  hpName` is `decide`-checkable, so "synthesis may not pick an
  allocating form inside a loop" is a compiled check: the loop interior
  of `ownedSkel` does not mention `hpName`, its setup does, and the
  check bites (the reusing interior and `allocProg` both mention it).

## Two things deliberately *not* done

**No import of the consumer.**  The tower cannot depend on ND-MC, so
C0's domain is reproduced in *shape* over `probeWord` — a word of length
`n + 3` whose entries are bounded by `n` — rather than imported.  What is
reproduced is the quantifier order (`c` before the instance, `∀ w` over
the domain), which is the whole of the argument; `EncodesGraph` is not,
and no claim here is about graphs.

**No re-zeroing.**  E27/E28: space freed by LIFO `free` comes back
**raw**, not zeroed (`availRaw`, and `availRaw_not_entails_avail` says
there is no way back).  A skeleton that reuses freed space and then
re-zeroes it would fix the space budget and silently break the time
budget — the same defect in the other currency.  §4's passes are
touched-only, and §10's gate is the compiled check: `hasAset` and
`hasWhile` are `false` of every pass, so no pass can sweep the arena,
and `opCount` is therefore the same at width `0` and width `10 ^ 6`.
§11 pins which availability flavour each skeleton consumes, against the
landed triples.

## Nothing is `sorry`

There is no `sorry` and no named unproved `Prop` in this file.
-/

namespace Lax13Proofs.Refine.Sepref.SpaceBudget

open Ir

/-! ## 1. The bump pointer, and the states a run passes through -/

/-- The bump pointer's value at a state (`0` if the cell is absent —
which never happens under `Good`, §4). -/
def hpOf (s : State) : ℕ := (s.vars hpName).getD 0

theorem hpOf_setVar_ne {s : State} {y : String} (hy : y ≠ hpName) (v : Val) :
    hpOf (s.setVar y v) = hpOf s := by
  simp only [hpOf, State.vars_setVar, if_neg (Ne.symm hy)]

theorem hpOf_setVar_self (s : State) (v : Val) : hpOf (s.setVar hpName v) = v := by
  simp [hpOf, State.vars_setVar]

theorem hpOf_of_vars {s : State} {v : ℕ} (h : s.vars hpName = some v) : hpOf s = v := by
  simp [hpOf, h]

/-- **The states a run passes through.**  `Mid c s s'` holds of `s`
itself, of the end state of a completed run, and of every intermediate
state of a component — a sequence's first half, a taken branch, a loop
body, a later turn of a loop.

This is the object the positive bounds below are stated over.  A bound
on the *end* state of `BigStep` would be a bound on the final bump
pointer, which is not a space bound at all (§7). -/
inductive Mid : Com → State → State → Prop
  /-- Before any step. -/
  | start (c : Com) (s : State) : Mid c s s
  /-- After a completed run. -/
  | done {c : Com} {s s' : State} {κ : Cost} (h : BigStep c s s' κ) : Mid c s s'
  /-- Partway through the first half of a sequence. -/
  | seqL {c d : Com} {s s' : State} (h : Mid c s s') : Mid (c.seq d) s s'
  /-- Partway through the second half of a sequence. -/
  | seqR {c d : Com} {s s₁ s' : State} {κ : Cost}
      (h₁ : BigStep c s s₁ κ) (h₂ : Mid d s₁ s') : Mid (c.seq d) s s'
  /-- Partway through the branch the condition selects. -/
  | ite {b : Cond} {c d : Com} {t : Bool} {s s' : State}
      (hb : b.eval s = some t) (h : Mid (if t then c else d) s s') :
      Mid (Com.ite b c d) s s'
  /-- Partway through the loop's body, on the current turn. -/
  | whileBody {b : Cond} {c : Com} {s s' : State}
      (hb : b.eval s = some true) (h : Mid c s s') : Mid (Com.while b c) s s'
  /-- Partway through a later turn of the loop. -/
  | whileNext {b : Cond} {c : Com} {s s₁ s' : State} {κ : Cost}
      (hb : b.eval s = some true) (h₁ : BigStep c s s₁ κ)
      (h₂ : Mid (Com.while b c) s₁ s') : Mid (Com.while b c) s s'

/-! ## 2. Which commands can move the bump pointer

`mentions` is `ArrayListButlastAppend.lean` §6's decidable occurrence
check, replicated here because it is `private` there.  It is used twice:
to see that a command cannot move `hp` at all (§2), and as §10's
compiled registration discipline. -/

/-- Does the operand name the cell `x`? -/
def opMentions (x : String) : Operand → Bool
  | .cell y => y == x
  | .lit _ => false

/-- Does the condition name the cell `x`? -/
def condMentions (x : String) : Cond → Bool
  | .eq u v => opMentions x u || opMentions x v
  | .lt u v => opMentions x u || opMentions x v

/-- Does the command name the cell `x` anywhere? -/
def mentions (x : String) : Com → Bool
  | .skip => false
  | .const y _ => y == x
  | .copy y z => y == x || z == x
  | .binop _ y z w => y == x || z == x || w == x
  | .aget y a i => y == x || a == x || i == x
  | .aset a i v => a == x || i == x || v == x
  | .seq c d => mentions x c || mentions x d
  | .ite b c d => condMentions x b || mentions x c || mentions x d
  | .while b c => condMentions x b || mentions x c

theorem ne_of_beq_false {y x : String} (h : (y == x) = false) : y ≠ x := by
  simpa using h

/-- **A command that does not name the bump-pointer cell cannot move
it.** -/
theorem hp_eq_of_not_mentions {c : Com} {s s' : State} {κ : Cost}
    (hs : BigStep c s s' κ) : mentions hpName c = false → hpOf s' = hpOf s := by
  induction hs with
  | skip => intro _; rfl
  | @const s x n hx =>
      intro h
      simp only [mentions, beq_eq_false_iff_ne] at h
      exact hpOf_setVar_ne h n
  | @copy s x y v hx hy =>
      intro h
      simp only [mentions, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      exact hpOf_setVar_ne h.1 v
  | @binop s op x y z m n hx hy hz =>
      intro h
      simp only [mentions, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      exact hpOf_setVar_ne h.1.1 _
  | @aget s x a i k v xs hx hi ha hv =>
      intro h
      simp only [mentions, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      exact hpOf_setVar_ne h.1.1 v
  | aset hi hv ha hk => intro _; rfl
  | seq h₁ h₂ ih₁ ih₂ =>
      intro h
      simp only [mentions, Bool.or_eq_false_iff] at h
      rw [ih₂ h.2, ih₁ h.1]
  | @ite_true b c d s s' κ hb hc ih =>
      intro h
      simp only [mentions, Bool.or_eq_false_iff] at h
      exact ih h.1.2
  | @ite_false b c d s s' κ hb hd ih =>
      intro h
      simp only [mentions, Bool.or_eq_false_iff] at h
      exact ih h.2
  | @while_true b c s s' s'' κ κ' hb hc hw ihc ihw =>
      intro h
      have h' := h
      simp only [mentions, Bool.or_eq_false_iff] at h'
      rw [ihw h, ihc h'.2]
  | while_false hb => intro _; rfl

/-- …and neither can any state it passes through. -/
theorem mid_hp_eq_of_not_mentions {c : Com} {s s' : State}
    (hm : Mid c s s') : mentions hpName c = false → hpOf s' = hpOf s := by
  induction hm with
  | start c s => intro _; rfl
  | done h => intro hc; exact hp_eq_of_not_mentions h hc
  | seqL h ih =>
      intro hc
      simp only [mentions, Bool.or_eq_false_iff] at hc
      exact ih hc.1
  | seqR h₁ h₂ ih =>
      intro hc
      simp only [mentions, Bool.or_eq_false_iff] at hc
      rw [ih hc.2, hp_eq_of_not_mentions h₁ hc.1]
  | @ite b c d t s s' hb h ih =>
      intro hc
      simp only [mentions, Bool.or_eq_false_iff] at hc
      refine ih ?_
      cases t <;> simp [hc.1.2, hc.2]
  | whileBody hb h ih =>
      intro hc
      have hc' := hc
      simp only [mentions, Bool.or_eq_false_iff] at hc'
      exact ih hc'.2
  | whileNext hb h₁ h₂ ih =>
      intro hc
      have hc' := hc
      simp only [mentions, Bool.or_eq_false_iff] at hc'
      rw [ih hc, hp_eq_of_not_mentions h₁ hc'.2]

/-! ## 3. The peak calculus

`NetLe c g` — a completed run of `c` leaves the bump pointer at most `g`
above where it found it.  `PeakLe c p` — **every** state the run passes
through has the bump pointer at most `p` above.  Only the second is a
space statement (§7). -/

/-- The net growth of the bump pointer across a completed run. -/
def NetLe (c : Com) (g : ℕ) : Prop := ∀ ⦃s s' : State⦄ ⦃κ : Cost⦄, BigStep c s s' κ →
  hpOf s' ≤ hpOf s + g

/-- **The peak growth of the bump pointer over the whole run** — the
bound this file's positive results are stated in. -/
def PeakLe (c : Com) (p : ℕ) : Prop := ∀ ⦃s s' : State⦄, Mid c s s' → hpOf s' ≤ hpOf s + p

theorem net_mono {c : Com} {g g' : ℕ} (h : NetLe c g) (hg : g ≤ g') : NetLe c g' :=
  fun _ _ _ hb => le_trans (h hb) (by omega)

theorem peak_mono {c : Com} {p p' : ℕ} (h : PeakLe c p) (hp : p ≤ p') : PeakLe c p' :=
  fun _ _ hm => le_trans (h hm) (by omega)

/-- A completed run is one of the states the run passes through, so a
peak bound is always also a net bound.  The converse is false, and §7 is
the counterexample. -/
theorem net_of_peak {c : Com} {p : ℕ} (h : PeakLe c p) : NetLe c p :=
  fun _ _ _ hb => h (Mid.done hb)

theorem net_of_not_mentions {c : Com} (h : mentions hpName c = false) : NetLe c 0 :=
  fun _ _ _ hb => by rw [hp_eq_of_not_mentions hb h]; omega

theorem peak_of_not_mentions {c : Com} (h : mentions hpName c = false) : PeakLe c 0 :=
  fun _ _ hm => by rw [mid_hp_eq_of_not_mentions hm h]; omega

theorem net_seq {c d : Com} {g g' : ℕ} (hc : NetLe c g) (hd : NetLe d g') :
    NetLe (c.seq d) (g + g') := by
  intro s s'' κ h
  obtain ⟨s', κ₁, κ₂, h₁, h₂, -⟩ := bigStep_seq_iff.1 h
  have := hc h₁
  have := hd h₂
  omega

/-- **The peak of a sequence.**  Either the peak of the first half, or
the second half's peak measured from wherever the first half left the
bump pointer. -/
theorem peak_seq {c d : Com} {g p q : ℕ} (hg : NetLe c g) (hp : PeakLe c p) (hq : PeakLe d q) :
    PeakLe (c.seq d) (max p (g + q)) := by
  intro s s' h
  cases h with
  | start => omega
  | done hb =>
      obtain ⟨s₁, κ₁, κ₂, h₁, h₂, -⟩ := bigStep_seq_iff.1 hb
      have := hg h₁
      have := hq (Mid.done h₂)
      omega
  | seqL h => have := hp h; omega
  | seqR h₁ h₂ =>
      have := hg h₁
      have := hq h₂
      omega

/-- **A loop whose body has zero net growth has the body's peak** — no
`turns` and no `levels` anywhere in the bound.  This is LIFO reuse as a
theorem: the arena is carved and given back each pass, so the number of
passes cannot raise the high-water mark. -/
theorem net_while {b : Cond} {c : Com} (hc : NetLe c 0) : NetLe (Com.while b c) 0 := by
  intro s s' κ h
  simp only [Nat.add_zero]
  generalize hw : Com.while b c = w at h
  induction h with
  | skip => exact absurd hw (by simp)
  | const hx => exact absurd hw (by simp)
  | copy hx hy => exact absurd hw (by simp)
  | binop hx hy hz => exact absurd hw (by simp)
  | aget hx hi ha hv => exact absurd hw (by simp)
  | aset hi hv ha hk => exact absurd hw (by simp)
  | seq h₁ h₂ ih₁ ih₂ => exact absurd hw (by simp)
  | ite_true hb h ih => exact absurd hw (by simp)
  | ite_false hb h ih => exact absurd hw (by simp)
  | @while_true b' c' s₀ s₁ s₂ κ₁ κ₂ hb hbody hloop ihbody ihloop =>
      obtain ⟨rfl, rfl⟩ := Com.while.inj hw
      have h1 := hc hbody
      have h2 := ihloop hw
      omega
  | @while_false b' c' s₀ hb => exact le_refl _

theorem peak_while {b : Cond} {c : Com} {p : ℕ} (hnet : NetLe c 0) (hpk : PeakLe c p) :
    PeakLe (Com.while b c) p := by
  intro s s' h
  generalize hw : Com.while b c = w at h
  induction h with
  | start c₀ s₀ => omega
  | done hb =>
      subst hw
      have := net_while hnet hb
      omega
  | seqL h ih => exact absurd hw (by simp)
  | seqR h₁ h₂ ih => exact absurd hw (by simp)
  | ite hb h ih => exact absurd hw (by simp)
  | @whileBody b' c' s₀ s₁ hb h ih =>
      obtain ⟨rfl, rfl⟩ := Com.while.inj hw
      exact hpk h
  | @whileNext b' c' s₀ s₁ s₂ κ hb h₁ h₂ ih =>
      obtain ⟨rfl, rfl⟩ := Com.while.inj hw
      have h1 := hnet h₁
      have h2 := ih hw
      omega

/-! ## 4. The skeleton

**Driver-shaped, not an arithmetic model.**  Every allocation is the
landed `allocProg` and every deallocation the landed `freeProg`; the
loops are the IR's own `while`; the parameters `setup`, `aw`, `turns`,
`levels` are symbolic and enter the emitted `Com` as literals, so the
theorems below quantify over the whole domain rather than holding at one
instance.

The literal staging (`Com.const "aw" k` immediately before each
`allocProg` / `freeProg`, `Com.const "one" 1` immediately before each
increment) is what makes the steps *unconditional*: no caller has to
have arranged for a cell to hold the right number, so `NetLe` and
`PeakLe` — which quantify over **all** states — are the right shape. -/

/-- The scalar cells the skeleton uses. -/
def probeScalars : List String := [hpName, "t", "l", "aw", "one", "arena", "base", "scr"]

/-- The skeleton's cells all exist.  Nothing stronger is ever needed:
the IR is stuck on an absent name, so this is exactly the domain
condition. -/
structure Good (s : State) : Prop where
  hp : s.vars hpName ≠ none
  t : s.vars "t" ≠ none
  l : s.vars "l" ≠ none
  aw : s.vars "aw" ≠ none
  one : s.vars "one" ≠ none
  arena : s.vars "arena" ≠ none
  base : s.vars "base" ≠ none
  scr : s.vars "scr" ≠ none

theorem vars_setVar_ne_none {s : State} {z : String} (h : s.vars z ≠ none) (y : String) (v : Val) :
    (s.setVar y v).vars z ≠ none := by
  simp only [State.vars_setVar]
  split
  · exact Option.some_ne_none v
  · exact h

theorem Good.setVar {s : State} (h : Good s) (y : String) (v : Val) : Good (s.setVar y v) :=
  ⟨vars_setVar_ne_none h.hp y v, vars_setVar_ne_none h.t y v, vars_setVar_ne_none h.l y v,
    vars_setVar_ne_none h.aw y v, vars_setVar_ne_none h.one y v,
    vars_setVar_ne_none h.arena y v, vars_setVar_ne_none h.base y v,
    vars_setVar_ne_none h.scr y v⟩

/-- **An entry state.**  Every cell reads `0`, no arrays — exactly
`Imp.initEnv`'s shape at the scalar layer, and what `avail_of_entry`
consumes.  Its existence is what keeps every hypothesis of the form
`Good s ∧ hpOf s = 0 ∧ s.vars "t" = some 0` from being vacuous. -/
def entryState : State := ⟨fun _ => some 0, fun _ => none⟩

theorem good_entryState : Good entryState :=
  ⟨by simp [entryState], by simp [entryState], by simp [entryState], by simp [entryState],
    by simp [entryState], by simp [entryState], by simp [entryState], by simp [entryState]⟩

theorem hpOf_entryState : hpOf entryState = 0 := rfl

theorem t_entryState : entryState.vars "t" = some 0 := rfl

/-- `x := x + 1`, with the `1` staged through a cell. -/
def incrCom (x : String) : Com := (Com.const "one" 1).seq (Com.binop .add x x "one")

/-- **Carve `k` cells** into `dst` — the landed `allocProg`, with its
size argument staged as a literal. -/
def allocLit (dst : String) (k : ℕ) : Com := (Com.const "aw" k).seq (allocProg dst "aw")

/-- **Give the topmost `k` cells back** — the landed `freeProg`, same
staging. -/
def freeLit (k : ℕ) : Com := (Com.const "aw" k).seq (freeProg "aw")

/-- The per-pass work: read the arena's base pointer.  O(1), no array
write, no loop — the touched-only discipline (E27/E28), never a
re-zeroing sweep.  `noRezero_reusePass` in §10 is the compiled check. -/
def workCom : Com := Com.copy "scr" "arena"

/-- **A LIFO-reused pass**: carve an arena, work, give it back.  What
comes back is `availRaw`, never `avail` (§11). -/
def reusePass (k : ℕ) : Com := (allocLit "arena" k).seq (workCom.seq (freeLit k))

/-- **A caller-owned pass**: the arena was carved once, in setup, and is
threaded.  No allocation at all. -/
def ownedPass : Com := workCom

/-- **A fresh pass**: carve an arena and never give it back.  This is
the discipline `no_word_size_for_fresh` refutes. -/
def freshPass (k : ℕ) : Com := allocLit "arena" k

/-- `levels` passes per turn. -/
def levelLoop (pass : Com) (levels : ℕ) : Com :=
  Com.while (.lt (.cell "l") (.lit levels)) (pass.seq (incrCom "l"))

/-- One turn: reset the level counter, run the levels, advance. -/
def turnBody (pass : Com) (levels : ℕ) : Com :=
  ((Com.const "l" 0).seq (levelLoop pass levels)).seq (incrCom "t")

/-- `turns` turns. -/
def turnLoop (pass : Com) (turns levels : ℕ) : Com :=
  Com.while (.lt (.cell "t") (.lit turns)) (turnBody pass levels)

/-- The setup a driver builds once, sized in `|x|`. -/
def setupOnly (setup : ℕ) : Com := allocLit "base" setup

/-- The same, plus the one arena every pass will share. -/
def setupWithArena (setup aw : ℕ) : Com := (allocLit "base" setup).seq (allocLit "arena" aw)

/-- **The reusing skeleton** — the passes carve and give back. -/
def reuseSkel (setup aw turns levels : ℕ) : Com :=
  (setupOnly setup).seq (turnLoop (reusePass aw) turns levels)

/-- **The caller-owned skeleton** — the arena is set up once and
threaded; the loop interior never touches the allocator. -/
def ownedSkel (setup aw turns levels : ℕ) : Com :=
  (setupWithArena setup aw).seq (turnLoop ownedPass turns levels)

/-- **The fresh skeleton** — one fresh arena per pass, none given back.
Even at `Σ|X_c| = n ^ (1 + ε)` this is refuted (§9). -/
def freshSkel (setup aw turns levels : ℕ) : Com :=
  (setupOnly setup).seq (turnLoop (freshPass aw) turns levels)

/-- **The skeleton a final-`hp` bound cannot tell from a good one**:
carve `K` cells, give them all back.  §7. -/
def wastefulCom (K : ℕ) : Com := (allocLit "arena" K).seq (freeLit K)

/-! ### The exact effect of the staged primitives -/

theorem hp_ne_aw : hpName ≠ "aw" := by decide
theorem hp_ne_one : hpName ≠ "one" := by decide
theorem hp_ne_l : hpName ≠ "l" := by decide
theorem hp_ne_t : hpName ≠ "t" := by decide
theorem hp_ne_scr : hpName ≠ "scr" := by decide

theorem const_aw_no_hp (k : ℕ) : mentions hpName (Com.const "aw" k) = false := rfl

theorem vars_setVar_self (s : State) (x : String) (v : Val) :
    (s.setVar x v).vars x = some v := by rw [State.vars_setVar, if_pos rfl]

/-- The landed `allocProg` moves the bump pointer up by exactly the size
its size cell holds. -/
theorem hp_allocProg {dst : String} (h1 : dst ≠ hpName) (h2 : dst ≠ "aw") {k : ℕ}
    {s s' : State} {κ : Cost} (haw : s.vars "aw" = some k)
    (h : BigStep (allocProg dst "aw") s s' κ) : hpOf s' = hpOf s + k := by
  rw [allocProg] at h
  obtain ⟨s₂, κ₃, κ₄, hcp, hbo, -⟩ := bigStep_seq_iff.1 h
  obtain ⟨-, v, hv, rfl, -⟩ := bigStep_copy_iff.1 hcp
  obtain ⟨-, m, n, hm, hn, rfl, -⟩ := bigStep_binop_iff.1 hbo
  rw [State.vars_setVar, if_neg (Ne.symm h1)] at hm
  rw [State.vars_setVar, if_neg (Ne.symm h2)] at hn
  have hm' : m = v := by rw [hv] at hm; exact (Option.some.inj hm).symm
  have hn' : n = k := by rw [haw] at hn; exact (Option.some.inj hn).symm
  have hv' : hpOf s = v := hpOf_of_vars hv
  rw [hpOf_setVar_self, Imp.Bop.apply_add, hm', hn', hv']

/-- Every state the landed `allocProg` passes through has the bump
pointer at most the block size above where it started. -/
theorem peak_allocProg {dst : String} (h1 : dst ≠ hpName) (h2 : dst ≠ "aw") {k : ℕ}
    {s s' : State} (haw : s.vars "aw" = some k) (h : Mid (allocProg dst "aw") s s') :
    hpOf s' ≤ hpOf s + k := by
  rw [allocProg] at h
  cases h with
  | start => omega
  | done hb => rw [hp_allocProg h1 h2 haw (by rw [allocProg]; exact hb)]
  | seqL hm =>
      cases hm with
      | start => omega
      | done hb =>
          obtain ⟨-, v, hv, rfl, -⟩ := bigStep_copy_iff.1 hb
          rw [hpOf_setVar_ne h1 v]; omega
  | seqR h₁ h₂ =>
      obtain ⟨-, v, hv, rfl, -⟩ := bigStep_copy_iff.1 h₁
      have hs₁ : hpOf (s.setVar dst v) = hpOf s := hpOf_setVar_ne h1 v
      cases h₂ with
      | start => omega
      | done hb =>
          obtain ⟨-, m, n, hm, hn, rfl, -⟩ := bigStep_binop_iff.1 hb
          rw [State.vars_setVar, if_neg (Ne.symm h1)] at hm
          rw [State.vars_setVar, if_neg (Ne.symm h2)] at hn
          have hm' : m = v := by rw [hv] at hm; exact (Option.some.inj hm).symm
          have hn' : n = k := by rw [haw] at hn; exact (Option.some.inj hn).symm
          have hv' : hpOf s = v := hpOf_of_vars hv
          rw [hpOf_setVar_self, Imp.Bop.apply_add, hm', hn', hv']

/-- The landed `freeProg` moves it down by exactly that size. -/
theorem hp_freeProg {k : ℕ} {s s' : State} {κ : Cost} (haw : s.vars "aw" = some k)
    (h : BigStep (freeProg "aw") s s' κ) : hpOf s' = hpOf s - k := by
  rw [freeProg] at h
  obtain ⟨-, m, n, hm, hn, rfl, -⟩ := bigStep_binop_iff.1 h
  have hn' : n = k := by rw [haw] at hn; exact (Option.some.inj hn).symm
  have hm' : hpOf s = m := hpOf_of_vars hm
  rw [hpOf_setVar_self, Imp.Bop.apply_sub, hn', hm']

/-- `alloc` moves the bump pointer up by exactly the staged literal. -/
theorem hp_allocLit {dst : String} (h1 : dst ≠ hpName) (h2 : dst ≠ "aw") {k : ℕ}
    {s s' : State} {κ : Cost} (h : BigStep (allocLit dst k) s s' κ) :
    hpOf s' = hpOf s + k := by
  rw [allocLit] at h
  obtain ⟨s₁, κ₁, κ₂, hc, ha, -⟩ := bigStep_seq_iff.1 h
  obtain ⟨-, rfl, -⟩ := bigStep_const_iff.1 hc
  rw [hp_allocProg h1 h2 (vars_setVar_self s "aw" k) ha,
    hpOf_setVar_ne (Ne.symm hp_ne_aw)]

/-- `free` moves it down by exactly the staged literal. -/
theorem hp_freeLit {k : ℕ} {s s' : State} {κ : Cost} (h : BigStep (freeLit k) s s' κ) :
    hpOf s' = hpOf s - k := by
  rw [freeLit] at h
  obtain ⟨s₁, κ₁, κ₂, hc, hf, -⟩ := bigStep_seq_iff.1 h
  obtain ⟨-, rfl, -⟩ := bigStep_const_iff.1 hc
  rw [hp_freeProg (vars_setVar_self s "aw" k) hf, hpOf_setVar_ne (Ne.symm hp_ne_aw)]

theorem net_allocLit {dst : String} (h1 : dst ≠ hpName) (h2 : dst ≠ "aw") (k : ℕ) :
    NetLe (allocLit dst k) k := fun _ _ _ h => le_of_eq (hp_allocLit h1 h2 h)

theorem net_freeLit (k : ℕ) : NetLe (freeLit k) 0 := fun _ _ _ h => by
  rw [hp_freeLit h]; omega

/-- **The peak of an allocation is the allocation.**  Its intermediate
states are exactly: before, after the staging `const`, after the base
pointer is read, and after the bump pointer moves. -/
theorem peak_allocLit {dst : String} (h1 : dst ≠ hpName) (h2 : dst ≠ "aw") (k : ℕ) :
    PeakLe (allocLit dst k) k := by
  intro s s' h
  rw [allocLit] at h
  cases h with
  | start => omega
  | done hb => rw [hp_allocLit h1 h2 (by rw [allocLit]; exact hb)]
  | seqL hm => rw [mid_hp_eq_of_not_mentions hm (const_aw_no_hp k)]; omega
  | seqR h₁ h₂ =>
      obtain ⟨-, rfl, -⟩ := bigStep_const_iff.1 h₁
      have hpk := peak_allocProg h1 h2 (vars_setVar_self s "aw" k) h₂
      rw [hpOf_setVar_ne (Ne.symm hp_ne_aw)] at hpk
      omega

theorem peak_freeLit (k : ℕ) : PeakLe (freeLit k) 0 := by
  intro s s' h
  rw [freeLit] at h
  cases h with
  | start => omega
  | done hb => rw [hp_freeLit (by rw [freeLit]; exact hb)]; omega
  | seqL hm => rw [mid_hp_eq_of_not_mentions hm (const_aw_no_hp k)]; omega
  | seqR h₁ h₂ =>
      obtain ⟨-, rfl, -⟩ := bigStep_const_iff.1 h₁
      have hs₁ : hpOf (s.setVar "aw" k) = hpOf s := hpOf_setVar_ne (Ne.symm hp_ne_aw) k
      rw [freeProg] at h₂
      cases h₂ with
      | start => omega
      | done hb =>
          have h3 := hp_freeProg (vars_setVar_self s "aw" k) (by rw [freeProg]; exact hb)
          omega

/-- **A block really is carved.**  The allocation step runs from every
state whose cells exist, so nothing below is vacuous. -/
theorem run_allocLit {dst : String} (h1 : dst ≠ hpName) (h2 : dst ≠ "aw")
    (hd : ∀ {s : State}, Good s → s.vars dst ≠ none) {k : ℕ} {s : State} (hs : Good s) :
    ∃ (s' : State) (κ : Cost), BigStep (allocLit dst k) s s' κ ∧ Good s' ∧
      hpOf s' = hpOf s + k ∧
      ∀ y, y ≠ dst → y ≠ "aw" → y ≠ hpName → s'.vars y = s.vars y := by
  obtain ⟨v, hv⟩ := State.exists_of_vars_ne_none hs.hp
  have hv₁ : (s.setVar "aw" k).vars hpName = some v := by
    rw [State.vars_setVar, if_neg hp_ne_aw]; exact hv
  have hv₂ : ((s.setVar "aw" k).setVar dst v).vars hpName = some v := by
    rw [State.vars_setVar, if_neg (Ne.symm h1)]; exact hv₁
  have haw₂ : ((s.setVar "aw" k).setVar dst v).vars "aw" = some k := by
    rw [State.vars_setVar, if_neg (Ne.symm h2)]; exact vars_setVar_self s "aw" k
  have hstep : BigStep (allocLit dst k) s
      (((s.setVar "aw" k).setVar dst v).setVar hpName (v + k))
      (ACost.cost Currency.const 1 +
        (ACost.cost Currency.copy 1 + ACost.cost (binopCurrency Imp.Bop.add) 1)) := by
    rw [allocLit, allocProg]
    refine BigStep.seq (BigStep.const hs.aw) (BigStep.seq (BigStep.copy ?_ hv₁) ?_)
    · exact vars_setVar_ne_none (hd hs) _ _
    · have hadd : Imp.Bop.add.apply v k = v + k := Imp.Bop.apply_add v k
      rw [← hadd]
      exact BigStep.binop (by rw [hv₂]; exact Option.some_ne_none v) hv₂ haw₂
  refine ⟨_, _, hstep, ?_, ?_, ?_⟩
  · exact ((hs.setVar "aw" k).setVar dst v).setVar hpName _
  · rw [hpOf_setVar_self, hpOf_of_vars hv]
  · intro y hy1 hy2 hy3
    rw [State.vars_setVar, if_neg hy3, State.vars_setVar, if_neg hy1,
      State.vars_setVar, if_neg hy2]

/-! ## 5. The positive bound: peak, not final

The reusing pass has **zero** net growth — the free cancels the alloc
exactly — and peak growth `aw`.  `peak_while` then carries that through
both loops without the iteration counts appearing anywhere. -/

/-- The reusing pass gives back exactly what it took. -/
theorem hp_reusePass {k : ℕ} {s s' : State} {κ : Cost} (h : BigStep (reusePass k) s s' κ) :
    hpOf s' = hpOf s := by
  rw [reusePass] at h
  obtain ⟨s₁, κ₁, κ₂, ha, hrest, -⟩ := bigStep_seq_iff.1 h
  obtain ⟨s₂, κ₃, κ₄, hw, hf, -⟩ := bigStep_seq_iff.1 hrest
  have h1 := hp_allocLit (by decide) (by decide) ha
  have h2 := hp_eq_of_not_mentions hw (by decide)
  have h3 := hp_freeLit hf
  omega

theorem net_reusePass (k : ℕ) : NetLe (reusePass k) 0 := fun _ _ _ h => by
  rw [hp_reusePass h]; omega

theorem peak_reusePass (k : ℕ) : PeakLe (reusePass k) k := by
  have h := peak_seq (c := allocLit "arena" k) (d := workCom.seq (freeLit k))
    (net_allocLit (by decide) (by decide) k) (peak_allocLit (by decide) (by decide) k)
    (peak_seq (net_of_not_mentions (c := workCom) (by decide))
      (peak_of_not_mentions (c := workCom) (by decide)) (peak_freeLit k))
  exact peak_mono h (by simp)

/-- **The peak of a `turns × levels` engine over a pass with zero net
growth is the pass's own peak.**  Neither `turns` nor `levels` occurs in
the bound: this is what LIFO reuse buys, stated over every intermediate
state rather than the end of the run. -/
theorem peak_turnLoop {pass : Com} {p turns levels : ℕ}
    (hnet : NetLe pass 0) (hpk : PeakLe pass p) : PeakLe (turnLoop pass turns levels) p := by
  have hlvlBody : NetLe (pass.seq (incrCom "l")) 0 :=
    net_mono (net_seq hnet (net_of_not_mentions (c := incrCom "l") (by decide))) (by omega)
  have hlvlPeak : PeakLe (pass.seq (incrCom "l")) p :=
    peak_mono (peak_seq hnet hpk (peak_of_not_mentions (c := incrCom "l") (by decide))) (by simp)
  have hlvl : PeakLe (levelLoop pass levels) p := peak_while hlvlBody hlvlPeak
  have hlvlNet : NetLe (levelLoop pass levels) 0 := net_while hlvlBody
  have hinner : PeakLe ((Com.const "l" 0).seq (levelLoop pass levels)) p :=
    peak_mono (peak_seq (net_of_not_mentions (c := Com.const "l" 0) (by decide))
      (peak_of_not_mentions (c := Com.const "l" 0) (by decide)) hlvl) (by simp)
  have hinnerNet : NetLe ((Com.const "l" 0).seq (levelLoop pass levels)) 0 :=
    net_mono (net_seq (net_of_not_mentions (c := Com.const "l" 0) (by decide)) hlvlNet) (by omega)
  have hbodyPeak : PeakLe (turnBody pass levels) p :=
    peak_mono (peak_seq hinnerNet hinner
      (peak_of_not_mentions (c := incrCom "t") (by decide))) (by simp)
  have hbodyNet : NetLe (turnBody pass levels) 0 :=
    net_mono (net_seq hinnerNet (net_of_not_mentions (c := incrCom "t") (by decide))) (by omega)
  exact peak_while hbodyNet hbodyPeak

theorem net_turnLoop {pass : Com} (hnet : NetLe pass 0) (turns levels : ℕ) :
    NetLe (turnLoop pass turns levels) 0 := by
  have hlvlBody : NetLe (pass.seq (incrCom "l")) 0 :=
    net_mono (net_seq hnet (net_of_not_mentions (c := incrCom "l") (by decide))) (by omega)
  have hinnerNet : NetLe ((Com.const "l" 0).seq (levelLoop pass levels)) 0 :=
    net_mono (net_seq (net_of_not_mentions (c := Com.const "l" 0) (by decide))
      (net_while hlvlBody)) (by omega)
  exact net_while (net_mono (net_seq hinnerNet
    (net_of_not_mentions (c := incrCom "t") (by decide))) (by omega))

/-- **The reusing skeleton's peak: `setup + aw`.**  A bound on the space
*high-water mark* over the entire run — every intermediate state, by
induction over the loop structure — and it does not mention `turns` or
`levels`. -/
theorem peak_reuseSkel (setup aw turns levels : ℕ) :
    PeakLe (reuseSkel setup aw turns levels) (setup + aw) := by
  have h := peak_seq (c := setupOnly setup) (d := turnLoop (reusePass aw) turns levels)
    (net_allocLit (by decide) (by decide) setup)
    (peak_allocLit (by decide) (by decide) setup)
    (peak_turnLoop (net_reusePass aw) (peak_reusePass aw))
  exact peak_mono h (by simp)

/-- **The caller-owned skeleton's peak: the same.**  The arena is carved
once in setup and threaded; the loop interior does not touch the
allocator at all (§10). -/
theorem peak_ownedSkel (setup aw turns levels : ℕ) :
    PeakLe (ownedSkel setup aw turns levels) (setup + aw) := by
  have hsetup : PeakLe (setupWithArena setup aw) (setup + aw) :=
    peak_mono (peak_seq (net_allocLit (by decide) (by decide) setup)
      (peak_allocLit (by decide) (by decide) setup)
      (peak_allocLit (by decide) (by decide) aw)) (by simp)
  have hsetupNet : NetLe (setupWithArena setup aw) (setup + aw) :=
    net_seq (net_allocLit (by decide) (by decide) setup)
      (net_allocLit (by decide) (by decide) aw)
  have hloop : PeakLe (turnLoop ownedPass turns levels) 0 :=
    peak_turnLoop (net_of_not_mentions (by decide)) (peak_of_not_mentions (by decide))
  exact peak_mono (peak_seq hsetupNet hsetup hloop) (by simp)

/-! ## 6. Cashing the peak into a word length

`Layout.FitsWords B w` (`Compile.lean:85`) has three clauses: `1 < B`,
`B ≤ 2 ^ w`, and `L.span B ≤ 2 ^ w` with
`L.span B = L.temps + L.scalars.length + L.arrays.length * B`.  A peak
bound linear in `|x|` therefore fits at a word length whose `2 ^ w` is
linear in `|x|` — which is exactly the resource C0's domain admits, and
exactly what §9 shows the fresh discipline cannot have. -/

open Lax13Proofs.Compile in
/-- Every positive number is between a power of two and its double.
(`BridgeSeamProbe.exists_pow_between`, re-derived: the tower may not
import the consumer.) -/
theorem exists_pow_between {m : ℕ} (hm : 0 < m) : ∃ w : ℕ, m ≤ 2 ^ w ∧ 2 ^ w ≤ 2 * m := by
  refine ⟨Nat.log 2 m + 1, le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) m), ?_⟩
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))

open Lax13Proofs.Compile in
/-- **A peak bound linear in `|x|` fits into words linear in `|x|`.**
The conclusion is over `Mid`, so what fits is the high-water mark and
not the end state. -/
theorem fits_of_peak_linear {c : Com} {p len a : ℕ} (hpk : PeakLe c p) (hlin : p ≤ a * len) :
    ∃ (w B : ℕ) (L : Layout),
      2 ^ w ≤ 2 * (a * len + 10) ∧ L.FitsWords B w ∧
        L.scalars = probeScalars ∧ L.arrays = [heapName] ∧ L.temps = 0 ∧
        ∀ s s' : State, Mid c s s' → hpOf s = 0 → hpOf s' < B := by
  obtain ⟨w, hw1, hw2⟩ := exists_pow_between (m := p + 10) (by omega)
  refine ⟨w, p + 2, ⟨probeScalars, [heapName], 0⟩, ?_, ⟨by omega, by omega, ?_⟩,
    rfl, rfl, rfl, ?_⟩
  · omega
  · show Layout.span _ (p + 2) ≤ 2 ^ w
    simp only [Layout.span, probeScalars, List.length_cons, List.length_nil]
    omega
  · intro s s' hm hs
    have := hpk hm
    omega

open Lax13Proofs.Compile in
/-- **The positive headline.**  Whenever the setup and the arena are
linear in `|x|`, the reusing engine's *peak* fits at a word length whose
`2 ^ w` is linear in `|x|` — for every `turns` and every `levels`. -/
theorem reuse_fits_linear (setup aw turns levels len a : ℕ) (hlin : setup + aw ≤ a * len) :
    ∃ (w B : ℕ) (L : Layout),
      2 ^ w ≤ 2 * (a * len + 10) ∧ L.FitsWords B w ∧
        L.scalars = probeScalars ∧ L.arrays = [heapName] ∧ L.temps = 0 ∧
        ∀ s s' : State, Mid (reuseSkel setup aw turns levels) s s' → hpOf s = 0 →
          hpOf s' < B :=
  fits_of_peak_linear (peak_reuseSkel setup aw turns levels) hlin

/-! ## 7. Why the bound had to be a peak

`wastefulCom K` allocates `K` cells and gives them all back.  Its
**final** bump pointer is exactly where it started — so any "space
bound" phrased on the end state of `BigStep` is satisfied by it, at
every `K`, including `K = n ^ (1 + ε)`.  Its **peak** is `K`.

This is the compiled form of the hazard: the two statement forms are not
equivalent, and only one of them is about space. -/

/-- **A final-`hp` bound is not a space bound.**  Both halves at once:
every completed run of `wastefulCom K` returns the bump pointer to where
it started, and the run passes through a state `K` above it. -/
theorem final_hp_is_not_peak (K : ℕ) {s : State} (hs : Good s) :
    (∀ (s' : State) (κ : Cost), BigStep (wastefulCom K) s s' κ → hpOf s' = hpOf s) ∧
      (∃ s' : State, Mid (wastefulCom K) s s' ∧ hpOf s' = hpOf s + K) := by
  constructor
  · intro s' κ h
    rw [wastefulCom] at h
    obtain ⟨s₁, κ₁, κ₂, ha, hf, -⟩ := bigStep_seq_iff.1 h
    have h1 := hp_allocLit (dst := "arena") (by decide) (by decide) ha
    have h2 := hp_freeLit hf
    omega
  · obtain ⟨s₁, κ₁, hb, -, hh, -⟩ :=
      run_allocLit (dst := "arena") (by decide) (by decide) (fun h => h.arena) (k := K) hs
    exact ⟨s₁, Mid.seqL (Mid.done hb), hh⟩

/-! The same gap holds at the *reusing* skeleton, which is a program
anyone would want to call correct: `run_reuseSkel` gives its final bump
pointer as `setup` above entry, `reuse_peak_attained` gives an
intermediate state at `setup + aw`.  Both are in §8, after the run
machinery that a *lower* bound on the peak needs. -/

/-! ## 8. The runs, and the fresh variant's climb

The negative direction needs a *lower* bound on the peak, so it needs a
run, not an invariant.  `run_countedLoop` builds one: a loop whose guard
is a literal and whose body ends in `incrCom` runs exactly as many times
as the literal says, and its bump-pointer growth is the body's, times
the count. -/

theorem hpOf_incr {x : String} (hx : x ≠ hpName) (s : State) (j : ℕ) :
    hpOf ((s.setVar "one" 1).setVar x (Imp.Bop.add.apply j 1)) = hpOf s := by
  rw [hpOf_setVar_ne hx, hpOf_setVar_ne (Ne.symm hp_ne_one)]

/-- **A counted loop runs exactly as often as its literal bound says.**
`keep` is the frame: cells the body leaves alone and that the loop
therefore also leaves alone, which is how the level loop can be nested
inside the turn loop. -/
theorem run_countedLoop {x : String} {keep : List String} {c : Com} {d N : ℕ}
    (hx1 : x ≠ "one") (hxh : x ≠ hpName) (hxk : x ∉ keep) (hok : "one" ∉ keep)
    (hbody : ∀ s : State, Good s → ∃ (s' : State) (κ : Cost), BigStep c s s' κ ∧ Good s' ∧
      hpOf s' = hpOf s + d ∧ s'.vars x = s.vars x ∧ ∀ y ∈ keep, s'.vars y = s.vars y) :
    ∀ (m j : ℕ), N - j = m → j ≤ N → ∀ s : State, Good s → s.vars x = some j →
      ∃ (s' : State) (κ : Cost),
        BigStep (Com.while (Cond.lt (.cell x) (.lit N)) (c.seq (incrCom x))) s s' κ ∧
          Good s' ∧ hpOf s' = hpOf s + (N - j) * d ∧ s'.vars x = some N ∧
          ∀ y ∈ keep, s'.vars y = s.vars y := by
  intro m
  induction m with
  | zero =>
      intro j hm hj s hs hx
      have hjN : j = N := by omega
      subst hjN
      refine ⟨s, _, BigStep.while_false ?_, hs, by simp, hx, fun y _ => rfl⟩
      simp [hx]
  | succ m ih =>
      intro j hm hj s hs hx
      have hjN : j < N := by omega
      obtain ⟨s₁, κ₁, hb, hs₁, hhp₁, hxeq, hkeep₁⟩ := hbody s hs
      have hx₁ : s₁.vars x = some j := by rw [hxeq, hx]
      have hone : s₁.vars "one" ≠ none := hs₁.one
      have hx₂ : (s₁.setVar "one" 1).vars x = some j := by
        rw [State.vars_setVar, if_neg hx1]; exact hx₁
      have hstep : BigStep (incrCom x) s₁
          ((s₁.setVar "one" 1).setVar x (Imp.Bop.add.apply j 1)) _ :=
        BigStep.seq (BigStep.const hone)
          (BigStep.binop (by rw [hx₂]; exact Option.some_ne_none j) hx₂
            (by rw [State.vars_setVar, if_pos rfl]))
      set s₃ := (s₁.setVar "one" 1).setVar x (Imp.Bop.add.apply j 1) with hs₃
      have hgood₃ : Good s₃ := (hs₁.setVar "one" 1).setVar x _
      have hhp₃ : hpOf s₃ = hpOf s + d := by rw [hs₃, hpOf_incr hxh, hhp₁]
      have hx₃ : s₃.vars x = some (j + 1) := by
        rw [hs₃, State.vars_setVar, if_pos rfl, Imp.Bop.apply_add]
      have hkeep₃ : ∀ y ∈ keep, s₃.vars y = s.vars y := by
        intro y hy
        have hyx : y ≠ x := by rintro rfl; exact hxk hy
        have hyo : y ≠ "one" := by rintro rfl; exact hok hy
        rw [hs₃, State.vars_setVar, if_neg hyx, State.vars_setVar, if_neg hyo]
        exact hkeep₁ y hy
      obtain ⟨s', κ', hloop, hgood', hhp', hx', hkeep'⟩ :=
        ih (j + 1) (by omega) (by omega) s₃ hgood₃ hx₃
      refine ⟨s', _, BigStep.while_true ?_ (BigStep.seq hb hstep) hloop, hgood', ?_, hx', ?_⟩
      · simp [hx, hjN]
      · rw [hhp', hhp₃]
        have hsub : N - (j + 1) = m := by omega
        rw [hsub, hm]
        ring
      · intro y hy; rw [hkeep' y hy, hkeep₃ y hy]

/-! ### The passes run, and so do the skeletons

Both directions need this.  The negative one needs a *lower* bound on the
peak, which only a constructed run gives; the positive one needs
non-vacuity, since a `PeakLe` bound over an unrunnable program would say
nothing. -/

/-- A pass specification: from any state whose cells exist the pass runs,
grows the bump pointer by exactly `d`, and leaves both counters alone.
This is exactly `run_countedLoop`'s body hypothesis. -/
def PassRuns (pass : Com) (d : ℕ) : Prop :=
  ∀ s : State, Good s → ∃ (s' : State) (κ : Cost), BigStep pass s s' κ ∧ Good s' ∧
    hpOf s' = hpOf s + d ∧ s'.vars "l" = s.vars "l" ∧ ∀ y ∈ ["t"], s'.vars y = s.vars y

/-- The `free` step runs from every state whose cells exist. -/
theorem run_freeLit (k : ℕ) {s : State} (hs : Good s) :
    ∃ (s' : State) (κ : Cost), BigStep (freeLit k) s s' κ ∧ Good s' ∧
      hpOf s' = hpOf s - k ∧ ∀ y, y ≠ "aw" → y ≠ hpName → s'.vars y = s.vars y := by
  obtain ⟨v, hv⟩ := State.exists_of_vars_ne_none hs.hp
  have hv₁ : (s.setVar "aw" k).vars hpName = some v := by
    rw [State.vars_setVar, if_neg hp_ne_aw]; exact hv
  have haw₁ : (s.setVar "aw" k).vars "aw" = some k := vars_setVar_self s "aw" k
  have hstep : BigStep (freeLit k) s ((s.setVar "aw" k).setVar hpName (v - k))
      (ACost.cost Currency.const 1 + ACost.cost (binopCurrency Imp.Bop.sub) 1) := by
    rw [freeLit, freeProg]
    refine BigStep.seq (BigStep.const hs.aw) ?_
    have hsub : Imp.Bop.sub.apply v k = v - k := Imp.Bop.apply_sub v k
    rw [← hsub]
    exact BigStep.binop (by rw [hv₁]; exact Option.some_ne_none v) hv₁ haw₁
  refine ⟨_, _, hstep, (hs.setVar "aw" k).setVar hpName _, ?_, ?_⟩
  · rw [hpOf_setVar_self, hpOf_of_vars hv]
  · intro y hy1 hy2
    rw [State.vars_setVar, if_neg hy2, State.vars_setVar, if_neg hy1]

/-- The per-pass work runs; it moves nothing but the scratch cell. -/
theorem run_workCom {s : State} (hs : Good s) :
    ∃ (s' : State) (κ : Cost), BigStep workCom s s' κ ∧ Good s' ∧ hpOf s' = hpOf s ∧
      ∀ y, y ≠ "scr" → s'.vars y = s.vars y := by
  obtain ⟨v, hv⟩ := State.exists_of_vars_ne_none hs.arena
  refine ⟨s.setVar "scr" v, ACost.cost Currency.copy 1, BigStep.copy hs.scr hv,
    hs.setVar _ _, hpOf_setVar_ne (by decide) v, fun y hy => ?_⟩
  rw [State.vars_setVar, if_neg hy]

/-- One fresh pass grows the bump pointer by exactly the arena width and
touches neither counter. -/
theorem run_freshPass (k : ℕ) : PassRuns (freshPass k) k := by
  intro s hs
  obtain ⟨s', κ, hb, hg, hh, hfr⟩ :=
    run_allocLit (dst := "arena") (by decide) (by decide) (fun h => h.arena) (k := k) hs
  refine ⟨s', κ, hb, hg, hh, hfr "l" (by decide) (by decide) (by decide), ?_⟩
  intro y hy
  simp only [List.mem_singleton] at hy
  subst hy
  exact hfr "t" (by decide) (by decide) (by decide)

/-- **One reusing pass gives back exactly what it took** — net zero, and
it runs.  This is the compiled content of "LIFO reuse". -/
theorem run_reusePass (k : ℕ) : PassRuns (reusePass k) 0 := by
  intro s hs
  obtain ⟨s₁, κ₁, ha, hg₁, hh₁, hfr₁⟩ :=
    run_allocLit (dst := "arena") (by decide) (by decide) (fun h => h.arena) (k := k) hs
  obtain ⟨s₂, κ₂, hw, hg₂, hh₂, hfr₂⟩ := run_workCom hg₁
  obtain ⟨s₃, κ₃, hf, hg₃, hh₃, hfr₃⟩ := run_freeLit k hg₂
  have hframe : ∀ y, y ≠ "arena" → y ≠ "aw" → y ≠ hpName → y ≠ "scr" →
      s₃.vars y = s.vars y := by
    intro y h1 h2 h3 h4
    rw [hfr₃ y h2 h3, hfr₂ y h4, hfr₁ y h1 h2 h3]
  refine ⟨s₃, _, BigStep.seq ha (BigStep.seq hw hf), hg₃, ?_, ?_, ?_⟩
  · rw [hh₃, hh₂, hh₁]; omega
  · exact hframe "l" (by decide) (by decide) (by decide) (by decide)
  · intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact hframe "t" (by decide) (by decide) (by decide) (by decide)

/-- **The skeleton runs, and its bump pointer ends `setup + turns * levels * d`
above entry.**  One theorem for all three flavours; `d` is the pass's own
growth, `0` for both positive skeletons and `aw` for the fresh one. -/
theorem run_skel {pass : Com} {d : ℕ} (hpass : PassRuns pass d)
    (setup turns levels : ℕ) {s : State} (hs : Good s) (ht : s.vars "t" = some 0) :
    ∃ (s' : State) (κ : Cost),
      BigStep ((setupOnly setup).seq (turnLoop pass turns levels)) s s' κ ∧
        Good s' ∧ hpOf s' = hpOf s + setup + turns * (levels * d) := by
  have hlevel : ∀ s₀ : State, Good s₀ → ∃ (s' : State) (κ : Cost),
      BigStep ((Com.const "l" 0).seq (levelLoop pass levels)) s₀ s' κ ∧ Good s' ∧
        hpOf s' = hpOf s₀ + levels * d ∧ s'.vars "t" = s₀.vars "t" ∧
        ∀ y ∈ ([] : List String), s'.vars y = s₀.vars y := by
    intro s₀ hs₀
    have hconst : BigStep (Com.const "l" 0) s₀ (s₀.setVar "l" 0)
        (ACost.cost Currency.const 1) := BigStep.const hs₀.l
    have hg₁ : Good (s₀.setVar "l" 0) := hs₀.setVar "l" 0
    have hl₁ : (s₀.setVar "l" 0).vars "l" = some 0 := vars_setVar_self _ _ _
    obtain ⟨s', κ', hloop, hg', hh', -, hkeep'⟩ :=
      run_countedLoop (x := "l") (keep := ["t"]) (c := pass) (d := d) (N := levels)
        (by decide) (by decide) (by decide) (by decide)
        hpass levels 0 (by omega) (by omega) (s₀.setVar "l" 0) hg₁ hl₁
    refine ⟨s', _, BigStep.seq hconst hloop, hg', ?_, ?_, fun y hy => absurd hy (by simp)⟩
    · rw [hh', hpOf_setVar_ne (by decide : "l" ≠ hpName), Nat.sub_zero]
    · rw [hkeep' "t" (by simp), State.vars_setVar, if_neg (by decide : "t" ≠ "l")]
  obtain ⟨s₁, κ₁, hsetup, hg₁, hh₁, hfr₁⟩ :=
    run_allocLit (dst := "base") (by decide) (by decide) (fun h => h.base) (k := setup) hs
  have ht₁ : s₁.vars "t" = some 0 := by
    rw [hfr₁ "t" (by decide) (by decide) (by decide)]; exact ht
  obtain ⟨s', κ', hloop, hg', hh', -, -⟩ :=
    run_countedLoop (x := "t") (keep := ([] : List String))
      (c := (Com.const "l" 0).seq (levelLoop pass levels))
      (d := levels * d) (N := turns) (by decide) (by decide) (by simp) (by simp)
      hlevel turns 0 (by omega) (by omega) s₁ hg₁ ht₁
  exact ⟨s', _, BigStep.seq hsetup hloop, hg', by rw [hh', hh₁, Nat.sub_zero]⟩

/-- **The fresh skeleton climbs to `setup + turns * levels * aw`.**  A
constructed run — so the negative result below is about a state the
machine actually reaches, not about an unreachable worst case. -/
theorem run_freshSkel (setup aw turns levels : ℕ) {s : State} (hs : Good s)
    (ht : s.vars "t" = some 0) :
    ∃ (s' : State) (κ : Cost), BigStep (freshSkel setup aw turns levels) s s' κ ∧
      Good s' ∧ hpOf s' = hpOf s + setup + turns * levels * aw := by
  obtain ⟨s', κ, hb, hg, hh⟩ := run_skel (run_freshPass aw) setup turns levels hs ht
  exact ⟨s', κ, hb, hg, by rw [hh]; ring⟩

/-- **The reusing skeleton runs too, and its bump pointer comes back to
`setup` above entry** — the whole `turns * levels` of arena traffic
leaves no trace in the *final* value.  Together with
`reuse_peak_attained` this is the hazard at the skeleton the positive
theorem is actually about: final `setup`, peak `setup + aw`. -/
theorem run_reuseSkel (setup aw turns levels : ℕ) {s : State} (hs : Good s)
    (ht : s.vars "t" = some 0) :
    ∃ (s' : State) (κ : Cost), BigStep (reuseSkel setup aw turns levels) s s' κ ∧
      Good s' ∧ hpOf s' = hpOf s + setup := by
  obtain ⟨s', κ, hb, hg, hh⟩ := run_skel (run_reusePass aw) setup turns levels hs ht
  exact ⟨s', κ, hb, hg, by rw [hh]; ring⟩

/-- **The peak bound is attained, so it is not a vacuous over-estimate.**
At the first pass of the first turn the reusing skeleton's bump pointer
really is `setup + aw` above entry — a state `Mid` records and
`BigStep`'s end state does not. -/
theorem reuse_peak_attained (setup aw turns levels : ℕ) (hturns : 0 < turns)
    (hlevels : 0 < levels) {s : State} (hs : Good s) (ht : s.vars "t" = some 0) :
    ∃ s' : State, Mid (reuseSkel setup aw turns levels) s s' ∧
      hpOf s' = hpOf s + setup + aw := by
  obtain ⟨s₁, κ₁, hsetup, hg₁, hh₁, hfr₁⟩ :=
    run_allocLit (dst := "base") (by decide) (by decide) (fun h => h.base) (k := setup) hs
  have ht₁ : s₁.vars "t" = some 0 := by
    rw [hfr₁ "t" (by decide) (by decide) (by decide)]; exact ht
  have hguardT : (Cond.lt (Operand.cell "t") (Operand.lit turns)).eval s₁ = some true := by
    simp [ht₁, hturns]
  have hconstL : BigStep (Com.const "l" 0) s₁ (s₁.setVar "l" 0)
      (ACost.cost Currency.const 1) := BigStep.const hg₁.l
  have hg₂ : Good (s₁.setVar "l" 0) := hg₁.setVar "l" 0
  have hl₂ : (s₁.setVar "l" 0).vars "l" = some 0 := vars_setVar_self _ _ _
  have hguardL : (Cond.lt (Operand.cell "l") (Operand.lit levels)).eval (s₁.setVar "l" 0)
      = some true := by simp [hlevels]
  obtain ⟨s₃, κ₃, halloc, -, hh₃, -⟩ :=
    run_allocLit (dst := "arena") (by decide) (by decide) (fun h => h.arena) (k := aw) hg₂
  refine ⟨s₃, Mid.seqR hsetup (Mid.whileBody hguardT (Mid.seqL
    (Mid.seqR hconstL (Mid.whileBody hguardL (Mid.seqL (Mid.seqL (Mid.done halloc))))))), ?_⟩
  rw [hh₃, hpOf_setVar_ne (by decide : "l" ≠ hpName), hh₁]

/-! ## 9. The negative control: no word size rescues fresh allocation

`no_word_size_for_sparse`'s shape, reproduced over the bump pointer.
C0's domain is `{x | … ∧ ∀ v ∈ x, c * (|x| + v + 1) ≤ 2 ^ w}` and the
root theorem quantifies over **all** `w`, so the *smallest admissible*
word length is in scope, where `2 ^ w` is only linear in `|x|`.  Against
that, `turns * levels * aw` — the fresh discipline's total allocation,
`Σ|X_c|` — is superlinear, and the bump pointer is a value of the run,
so it must be below `B ≤ 2 ^ w`.

The word `probeWord n` plays the role C0's sparse instance plays: length
`n + 3`, every entry at most `n`.  It is *not* a graph encoding — the
tower may not import the consumer — and nothing here is a claim about
graphs.  What is reproduced is the quantifier order, which is the whole
of the argument. -/

/-- A C0-shaped word: `n + 3` cells, every entry `n` or `0`. -/
def probeWord (n : ℕ) : List ℕ := n :: List.replicate (n + 2) 0

theorem length_probeWord (n : ℕ) : (probeWord n).length = n + 3 := by
  simp [probeWord]

theorem mem_probeWord {n v : ℕ} (h : v ∈ probeWord n) : v = n ∨ v = 0 := by
  simp only [probeWord, List.mem_cons] at h
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (List.eq_of_mem_replicate h)

open Lax13Proofs.Compile in
/-- **The smallest admissible word length, and how small it is.**  C0's
domain admits every `w` above `c * (|x| + max x + 1)`, and the statement
quantifies over all of them — so the smallest is in scope, and there
`2 ^ w` is only *linear* in `|x|`.  This is the whole engine of the
refutation; the constant `c` is fixed before the instance. -/
theorem admissible_word_small (c n : ℕ) (hc : 0 < c) :
    ∃ w : ℕ, (∀ v ∈ probeWord n, c * ((probeWord n).length + v + 1) ≤ 2 ^ w) ∧
      2 ^ w ≤ 4 * c * (n + 2) := by
  obtain ⟨w, hw1, hw2⟩ := exists_pow_between (m := c * (2 * n + 4)) (by positivity)
  refine ⟨w, ?_, ?_⟩
  · intro v hv
    refine le_trans ?_ hw1
    rw [length_probeWord]
    rcases mem_probeWord hv with rfl | rfl <;> exact Nat.mul_le_mul_left c (by omega)
  · calc 2 ^ w ≤ 2 * (c * (2 * n + 4)) := hw2
      _ = 4 * c * (n + 2) := by ring

open Lax13Proofs.Compile in
/-- The refutation, once, over any program that reaches a bump pointer
past the crossover. -/
theorem no_word_size_of_reaches {com : Com} {c n T : ℕ}
    (hcross : 4 * c * (n + 2) ≤ T) {w : ℕ} (hw : 2 ^ w ≤ 4 * c * (n + 2))
    {s : State} (hreach : ∃ s' : State, Mid com s s' ∧ T ≤ hpOf s')
    {L : Layout} {B : ℕ} (hfit : L.FitsWords B w) :
    ¬ (∀ s' : State, Mid com s s' → hpOf s' < B) := by
  intro hall
  obtain ⟨s', hmid, hge⟩ := hreach
  have hbad : 4 * c * (n + 2) < 4 * c * (n + 2) :=
    calc 4 * c * (n + 2) ≤ T := hcross
      _ ≤ hpOf s' := hge
      _ < B := hall s' hmid
      _ ≤ 2 ^ w := hfit.bound
      _ ≤ 4 * c * (n + 2) := hw
  exact absurd hbad (lt_irrefl _)

open Lax13Proofs.Compile in
/-- **The refutation.**  For every constant `c` and every instance past
that constant's crossover, C0's own domain admits a word length `w` at
which the compile layout's fits-words condition and the space budget —
"the bump pointer is a value of the run, hence below `B`" — are
**jointly unsatisfiable** for the fresh skeleton.  No word size reaches
it: the quantities are `turns * levels * aw` (the fresh total) against
`2 ^ w` (the machine's addressable range), and no cost repair occurs.

Note the shape of the conclusion: what fails is a bound over `Mid`, i.e.
over the states the run passes through.  Since the offending state is
reached by `run_freshSkel`, the refutation is of a peak bound and *a
fortiori* of anything stronger. -/
theorem no_word_size_for_fresh (c n setup aw turns levels : ℕ) (hc : 0 < c)
    (hcross : 4 * c * (n + 2) ≤ turns * levels * aw) :
    ∃ w : ℕ,
      (∀ v ∈ probeWord n, c * ((probeWord n).length + v + 1) ≤ 2 ^ w) ∧
      ∀ (L : Layout) (B : ℕ) (s : State), Good s → hpOf s = 0 → s.vars "t" = some 0 →
        L.FitsWords B w →
        ¬ (∀ s' : State, Mid (freshSkel setup aw turns levels) s s' → hpOf s' < B) := by
  obtain ⟨w, hadm, hw⟩ := admissible_word_small c n hc
  refine ⟨w, hadm, fun L B s hs hhp ht hfit => ?_⟩
  refine no_word_size_of_reaches hcross hw ?_ hfit
  obtain ⟨s', κ, hrun, -, hh⟩ := run_freshSkel setup aw turns levels hs ht
  exact ⟨s', Mid.done hrun, by rw [hh, hhp]; exact Nat.le_add_left _ _⟩

open Lax13Proofs.Compile in
/-- **The same refutation, aimed at the program a final-`hp` bound
cannot see.**  `wastefulCom K` allocates `K` and frees it all, so by
`final_hp_is_not_peak` its *final* bump pointer is exactly where it
started — a final-`hp` "space bound" holds of it at **every** `K`,
including `K = n ^ (1 + ε)`.  Its peak is refuted at every admissible
word length.  The two statement forms therefore disagree on a concrete
program, which is why §5–§6 are stated over `Mid`. -/
theorem no_word_size_for_wasteful (c n K : ℕ) (hc : 0 < c)
    (hcross : 4 * c * (n + 2) ≤ K) :
    ∃ w : ℕ,
      (∀ v ∈ probeWord n, c * ((probeWord n).length + v + 1) ≤ 2 ^ w) ∧
      ∀ (L : Layout) (B : ℕ) (s : State), Good s →
        L.FitsWords B w →
        (∀ (s' : State) (κ : Cost), BigStep (wastefulCom K) s s' κ → hpOf s' = hpOf s) ∧
        ¬ (∀ s' : State, Mid (wastefulCom K) s s' → hpOf s' < B) := by
  obtain ⟨w, hadm, hw⟩ := admissible_word_small c n hc
  refine ⟨w, hadm, fun L B s hs hfit => ⟨(final_hp_is_not_peak K hs).1, ?_⟩⟩
  refine no_word_size_of_reaches hcross hw ?_ hfit
  obtain ⟨s', hmid, hh⟩ := (final_hp_is_not_peak K hs).2
  exact ⟨s', hmid, by rw [hh]; omega⟩

/-! ### Controls on the control

Finding 3 of the ND-MC seam probe carries three; so does this. -/

-- **The crossover is inhabited**, and already at *sub-quadratic* fresh
-- allocation: `c` is fixed before the instance, and at a constant as
-- generous as `10 ^ 9`, `n = 10 ^ 20` with `turns = n`, `levels = 1`,
-- `aw = n ^ (1/2) = 10 ^ 10` — i.e. `Σ|X_c| = n ^ (3/2)`, the touched-only
-- `n ^ (1 + ε)` the phase actually predicts — is past it.
#guard 4 * 10 ^ 9 * (10 ^ 20 + 2) ≤ 10 ^ 20 * 1 * 10 ^ 10

-- **First negative control**: below the crossover the hypothesis fails,
-- so the theorem is not a statement about every instance — it is the
-- quantifier order.
#guard ¬ (4 * 10 ^ 9 * (5 + 2) ≤ 5 * 1 * 5)

-- …and it fails for a *linear* total at the very same large instance,
-- which is the point: linear fresh allocation is not refuted.
#guard ¬ (4 * 10 ^ 9 * (10 ^ 20 + 2) ≤ 10 ^ 20 * 1 * 1)

open Lax13Proofs.Compile in
/-- **Second negative control**: the fits-words condition is satisfiable
at *whatever* bound the fresh discipline needs — including
`T = turns * levels * aw` — as soon as the word length is free.  So what
§9 refutes is not the condition on its own; it is the conjunction with
the word lengths C0's domain admits, and nothing else. -/
theorem fits_at_a_free_word_length (T : ℕ) :
    ∃ (w B : ℕ) (L : Layout), T < B ∧ L.FitsWords B w ∧
      L.scalars = probeScalars ∧ L.arrays = [heapName] := by
  obtain ⟨w, hw1, -⟩ := exists_pow_between (m := T + 10) (by omega)
  refine ⟨w, T + 2, ⟨probeScalars, [heapName], 0⟩, by omega, ⟨by omega, by omega, ?_⟩, rfl, rfl⟩
  show Layout.span _ (T + 2) ≤ 2 ^ w
  simp only [Layout.span, probeScalars, List.length_cons, List.length_nil]
  omega

open Lax13Proofs.Compile in
/-- **Fourth control: the refutation's own hypotheses are inhabited.**
At the entry state, past the crossover, the fresh skeleton is refuted at
every admissible word length — no `Good`/`hpOf`/counter hypothesis is
carrying the theorem. -/
theorem no_word_size_for_fresh_at_entry (c n setup aw turns levels : ℕ) (hc : 0 < c)
    (hcross : 4 * c * (n + 2) ≤ turns * levels * aw) :
    ∃ w : ℕ,
      (∀ v ∈ probeWord n, c * ((probeWord n).length + v + 1) ≤ 2 ^ w) ∧
      ∀ (L : Layout) (B : ℕ), L.FitsWords B w →
        ¬ (∀ s' : State, Mid (freshSkel setup aw turns levels) entryState s' →
            hpOf s' < B) := by
  obtain ⟨w, hadm, hkill⟩ := no_word_size_for_fresh c n setup aw turns levels hc hcross
  exact ⟨w, hadm, fun L B hfit =>
    hkill L B entryState good_entryState hpOf_entryState t_entryState hfit⟩

open Lax13Proofs.Compile in
/-- **The reusing skeleton fits at a word length that is itself
admissible for the domain**, and that word length is linear in `|x|` as
long as `c` and the setup are.  This is the fair comparison: the fresh
refutation kills *every* admissible `w`, so the positive side has to
exhibit one, not merely some `w` of its own choosing. -/
theorem reuse_fits_at_admissible_word (c n setup aw turns levels : ℕ) :
    ∃ (w B : ℕ) (L : Layout),
      2 ^ w ≤ 2 * max (c * (2 * n + 4)) (setup + aw + 10) ∧
      (∀ v ∈ probeWord n, c * ((probeWord n).length + v + 1) ≤ 2 ^ w) ∧
      L.FitsWords B w ∧ L.scalars = probeScalars ∧ L.arrays = [heapName] ∧
      ∀ s s' : State, Mid (reuseSkel setup aw turns levels) s s' → hpOf s = 0 →
        hpOf s' < B := by
  obtain ⟨w, hw1, hw2⟩ :=
    exists_pow_between (m := max (c * (2 * n + 4)) (setup + aw + 10)) (by omega)
  have hspan : setup + aw + 10 ≤ 2 ^ w := le_trans (le_max_right _ _) hw1
  have hdom : c * (2 * n + 4) ≤ 2 ^ w := le_trans (le_max_left _ _) hw1
  refine ⟨w, setup + aw + 2, ⟨probeScalars, [heapName], 0⟩, hw2, ?_,
    ⟨by omega, by omega, ?_⟩, rfl, rfl, ?_⟩
  · intro v hv
    refine le_trans ?_ hdom
    rw [length_probeWord]
    rcases mem_probeWord hv with rfl | rfl <;> exact Nat.mul_le_mul_left c (by omega)
  · show Layout.span _ (setup + aw + 2) ≤ 2 ^ w
    simp only [Layout.span, probeScalars, List.length_cons, List.length_nil]
    omega
  · intro s s' hm hs
    have := peak_reuseSkel setup aw turns levels hm
    omega

open Lax13Proofs.Compile in
/-- **Third control, and the one that makes the probe bite.**  At the
*very* parameters where the fresh discipline is refuted, the reusing
discipline fits — at a word length the domain admits.  The two skeletons
differ only in whether the pass gives its arena back; the space verdicts
are opposite. -/
theorem reuse_fits_where_fresh_cannot (c n setup aw turns levels : ℕ) (hc : 0 < c)
    (hcross : 4 * c * (n + 2) ≤ turns * levels * aw) :
    (∃ (w B : ℕ) (L : Layout),
        2 ^ w ≤ 2 * max (c * (2 * n + 4)) (setup + aw + 10) ∧
        (∀ v ∈ probeWord n, c * ((probeWord n).length + v + 1) ≤ 2 ^ w) ∧
        L.FitsWords B w ∧
        ∀ s s' : State, Mid (reuseSkel setup aw turns levels) s s' → hpOf s = 0 →
          hpOf s' < B) ∧
    (∃ w : ℕ, (∀ v ∈ probeWord n, c * ((probeWord n).length + v + 1) ≤ 2 ^ w) ∧
      ∀ (L : Layout) (B : ℕ) (s : State), Good s → hpOf s = 0 → s.vars "t" = some 0 →
        L.FitsWords B w →
        ¬ (∀ s' : State, Mid (freshSkel setup aw turns levels) s s' → hpOf s' < B)) := by
  refine ⟨?_, no_word_size_for_fresh c n setup aw turns levels hc hcross⟩
  obtain ⟨w, B, L, h1, h2, h3, -, -, h4⟩ :=
    reuse_fits_at_admissible_word c n setup aw turns levels
  exact ⟨w, B, L, h1, h2, h3, h4⟩

/-! ## 9b. The descending skeleton — the shape a real driver actually has

`reuseSkel` and `ownedSkel` say arenas never accumulate at all;
`freshSkel` says they accumulate as `turns * levels * aw`.  A recursive
per-arena driver is **neither**: within one turn it descends `levels`
deep, holding one arena live at each level while it recurses, and then
unwinds, freeing LIFO.  Its arenas accumulate *within* a turn and not
*across* turns, so its peak is `setup + levels * aw` — independent of
`turns`, linear in `levels`.

The IR has no recursion (ledger D6) and does not need it: a descent loop
that allocates without freeing followed by an ascent loop that frees LIFO
has exactly the recursion's allocation trace, which is the only thing
under test.  The ascent counts the depth cell back down, so the two loops
share one counter and no new cell is reserved.

The peak calculus of §3 does not reach this on its own: the descent's
body has **non-zero** net growth, so `peak_while` does not apply.
`peak_while_pot` below is `peak_while` with a potential — the allocation
still to come — and it is what turns "the body grows, but only `levels`
times" into a bound. -/

section Descending

/-! ### A loop rule for a body with net growth -/

/-- The depth cell's value. -/
def lOf (s : State) : ℕ := (s.vars "l").getD 0

/-- **The descent's potential**: the arenas not yet carved.  The descent
body converts exactly one unit of it into bump pointer, which is why
`hpOf + Φ` is invariant and the peak is the potential at entry. -/
def descPot (levels aw : ℕ) (s : State) : ℕ := (levels - lOf s) * aw

/-- `peak_while`'s net half, with a potential: if each guarded body step
leaves `hpOf + Φ` where it found it or lower, so does the whole loop. -/
theorem net_while_pot {b : Cond} {c : Com} {Φ : State → ℕ}
    (hnet : ∀ ⦃s s' : State⦄ ⦃κ : Cost⦄, b.eval s = some true → BigStep c s s' κ →
      hpOf s' + Φ s' ≤ hpOf s + Φ s) :
    ∀ ⦃s s' : State⦄ ⦃κ : Cost⦄, BigStep (Com.while b c) s s' κ →
      hpOf s' + Φ s' ≤ hpOf s + Φ s := by
  intro s s' κ h
  generalize hw : Com.while b c = w at h
  induction h with
  | skip => exact absurd hw (by simp)
  | const hx => exact absurd hw (by simp)
  | copy hx hy => exact absurd hw (by simp)
  | binop hx hy hz => exact absurd hw (by simp)
  | aget hx hi ha hv => exact absurd hw (by simp)
  | aset hi hv ha hk => exact absurd hw (by simp)
  | seq h₁ h₂ ih₁ ih₂ => exact absurd hw (by simp)
  | ite_true hb h ih => exact absurd hw (by simp)
  | ite_false hb h ih => exact absurd hw (by simp)
  | @while_true b' c' s₀ s₁ s₂ κ₁ κ₂ hb hbody hloop ihbody ihloop =>
      obtain ⟨rfl, rfl⟩ := Com.while.inj hw
      exact le_trans (ihloop hw) (hnet hb hbody)
  | @while_false b' c' s₀ hb => exact le_refl _

/-- **`peak_while` with a potential.**  A loop whose guarded body neither
raises `hpOf + Φ` nor leaves `hpOf + Φ` at any intermediate state has, at
every state it passes through, `hpOf` at most `Φ` above where it started.
With `Φ = 0` this is `peak_while`; with `Φ` the arenas still to carve it
is the descent's bound, and the *iteration count never appears* — it is
the potential that is finite, not the loop. -/
theorem peak_while_pot {b : Cond} {c : Com} {Φ : State → ℕ}
    (hnet : ∀ ⦃s s' : State⦄ ⦃κ : Cost⦄, b.eval s = some true → BigStep c s s' κ →
      hpOf s' + Φ s' ≤ hpOf s + Φ s)
    (hpk : ∀ ⦃s s' : State⦄, b.eval s = some true → Mid c s s' → hpOf s' ≤ hpOf s + Φ s) :
    ∀ ⦃s s' : State⦄, Mid (Com.while b c) s s' → hpOf s' ≤ hpOf s + Φ s := by
  intro s s' h
  generalize hw : Com.while b c = w at h
  induction h with
  | start c₀ s₀ => omega
  | done hb =>
      subst hw
      have := net_while_pot hnet hb
      omega
  | seqL h ih => exact absurd hw (by simp)
  | seqR h₁ h₂ ih => exact absurd hw (by simp)
  | ite hb h ih => exact absurd hw (by simp)
  | @whileBody b' c' s₀ s₁ hb h ih =>
      obtain ⟨rfl, rfl⟩ := Com.while.inj hw
      exact hpk hb h
  | @whileNext b' c' s₀ s₁ s₂ κ hb h₁ h₂ ih =>
      obtain ⟨rfl, rfl⟩ := Com.while.inj hw
      have h3 := hnet hb h₁
      have h4 := ih hw
      omega

/-! ### Reading the guards, and the frames -/

theorem lt_lit_guard {x : String} {N : ℕ} {s : State}
    (hb : (Cond.lt (Operand.cell x) (Operand.lit N)).eval s = some true) :
    ∃ j, s.vars x = some j ∧ j < N := by
  cases hj : s.vars x with
  | none => rw [Cond.eval_lt, Operand.eval_cell, hj] at hb; simp at hb
  | some j =>
      refine ⟨j, rfl, ?_⟩
      rw [Cond.eval_lt, Operand.eval_cell, hj] at hb
      simpa using hb

theorem lt_lit_guard_of {x : String} {N j : ℕ} {s : State} (hj : s.vars x = some j)
    (hb : (Cond.lt (Operand.cell x) (Operand.lit N)).eval s = some true) : j < N := by
  rw [Cond.eval_lt, Operand.eval_cell, hj] at hb
  simpa using hb

theorem lt_lit_guard_false {x : String} {N j : ℕ} {s : State} (hj : s.vars x = some j)
    (hb : (Cond.lt (Operand.cell x) (Operand.lit N)).eval s = some false) : N ≤ j := by
  rw [Cond.eval_lt, Operand.eval_cell, hj] at hb
  simpa using hb

theorem lit_lt_guard {x : String} {s : State}
    (hb : (Cond.lt (Operand.lit 0) (Operand.cell x)).eval s = some true) :
    ∃ j, s.vars x = some j ∧ 0 < j := by
  cases hj : s.vars x with
  | none => rw [Cond.eval_lt, Operand.eval_lit, Operand.eval_cell, hj] at hb; simp at hb
  | some j =>
      refine ⟨j, rfl, ?_⟩
      rw [Cond.eval_lt, Operand.eval_lit, Operand.eval_cell, hj] at hb
      simpa using hb

theorem lit_lt_guard_of {x : String} {j : ℕ} {s : State} (hj : s.vars x = some j)
    (hb : (Cond.lt (Operand.lit 0) (Operand.cell x)).eval s = some true) : 0 < j := by
  rw [Cond.eval_lt, Operand.eval_lit, Operand.eval_cell, hj] at hb
  simpa using hb

theorem lit_lt_guard_false {x : String} {j : ℕ} {s : State} (hj : s.vars x = some j)
    (hb : (Cond.lt (Operand.lit 0) (Operand.cell x)).eval s = some false) : j = 0 := by
  rw [Cond.eval_lt, Operand.eval_lit, Operand.eval_cell, hj] at hb
  simpa using hb

/-- The allocation step leaves every cell but its three alone. -/
theorem vars_allocLit {dst : String} {k : ℕ} {s s' : State} {κ : Cost}
    (h : BigStep (allocLit dst k) s s' κ) {y : String}
    (h1 : y ≠ dst) (h2 : y ≠ "aw") (h3 : y ≠ hpName) : s'.vars y = s.vars y := by
  rw [allocLit, allocProg] at h
  obtain ⟨s₁, κ₁, κ₂, hc, hrest, -⟩ := bigStep_seq_iff.1 h
  obtain ⟨s₂, κ₃, κ₄, hcp, hbo, -⟩ := bigStep_seq_iff.1 hrest
  obtain ⟨-, rfl, -⟩ := bigStep_const_iff.1 hc
  obtain ⟨-, v, hv, rfl, -⟩ := bigStep_copy_iff.1 hcp
  obtain ⟨-, m, n, hm, hn, rfl, -⟩ := bigStep_binop_iff.1 hbo
  rw [State.vars_setVar, if_neg h3, State.vars_setVar, if_neg h1, State.vars_setVar, if_neg h2]

/-- …and so does the deallocation step. -/
theorem vars_freeLit {k : ℕ} {s s' : State} {κ : Cost}
    (h : BigStep (freeLit k) s s' κ) {y : String}
    (h2 : y ≠ "aw") (h3 : y ≠ hpName) : s'.vars y = s.vars y := by
  rw [freeLit, freeProg] at h
  obtain ⟨s₁, κ₁, κ₂, hc, hbo, -⟩ := bigStep_seq_iff.1 h
  obtain ⟨-, rfl, -⟩ := bigStep_const_iff.1 hc
  obtain ⟨-, m, n, hm, hn, rfl, -⟩ := bigStep_binop_iff.1 hbo
  rw [State.vars_setVar, if_neg h3, State.vars_setVar, if_neg h2]

theorem vars_incrCom {x : String} (hx : x ≠ "one") {j : ℕ} {s s' : State} {κ : Cost}
    (hj : s.vars x = some j) (h : BigStep (incrCom x) s s' κ) :
    s'.vars x = some (j + 1) := by
  rw [incrCom] at h
  obtain ⟨s₁, κ₁, κ₂, hc, hb, -⟩ := bigStep_seq_iff.1 h
  obtain ⟨-, rfl, -⟩ := bigStep_const_iff.1 hc
  obtain ⟨-, m, n, hm, hn, rfl, -⟩ := bigStep_binop_iff.1 hb
  rw [State.vars_setVar, if_neg hx, hj] at hm
  rw [State.vars_setVar, if_pos rfl] at hn
  have hm' : m = j := (Option.some.inj hm).symm
  have hn' : n = 1 := (Option.some.inj hn).symm
  rw [State.vars_setVar, if_pos rfl, Imp.Bop.apply_add, hm', hn']

/-- `x := x - 1`, staged exactly as `incrCom` stages its `1`. -/
def decrCom (x : String) : Com := (Com.const "one" 1).seq (Com.binop .sub x x "one")

theorem vars_decrCom {x : String} (hx : x ≠ "one") {j : ℕ} {s s' : State} {κ : Cost}
    (hj : s.vars x = some j) (h : BigStep (decrCom x) s s' κ) :
    s'.vars x = some (j - 1) := by
  rw [decrCom] at h
  obtain ⟨s₁, κ₁, κ₂, hc, hb, -⟩ := bigStep_seq_iff.1 h
  obtain ⟨-, rfl, -⟩ := bigStep_const_iff.1 hc
  obtain ⟨-, m, n, hm, hn, rfl, -⟩ := bigStep_binop_iff.1 hb
  rw [State.vars_setVar, if_neg hx, hj] at hm
  rw [State.vars_setVar, if_pos rfl] at hn
  have hm' : m = j := (Option.some.inj hm).symm
  have hn' : n = 1 := (Option.some.inj hn).symm
  rw [State.vars_setVar, if_pos rfl, Imp.Bop.apply_sub, hm', hn']

/-! ### The skeleton -/

/-- **The descent**: carve one arena per level, give none back, and step
one level deeper each time.  It is `levelLoop` over the *fresh* pass —
the same command the refuted skeleton uses per turn, which is the point:
what makes the two differ is the unwind, not the descent. -/
def descendLoop (aw levels : ℕ) : Com := levelLoop (freshPass aw) levels

/-- **The unwind**: while the depth cell is positive, give the topmost
arena back and step out one level.  LIFO by construction, and exactly
the allocation trace a recursion's return path has. -/
def ascendLoop (aw : ℕ) : Com :=
  Com.while (.lt (.lit 0) (.cell "l")) ((freeLit aw).seq (decrCom "l"))

/-- One turn of the descending driver: enter at depth `0`, descend,
unwind, advance the turn counter. -/
def nestedInner (aw levels : ℕ) : Com :=
  ((Com.const "l" 0).seq (descendLoop aw levels)).seq (ascendLoop aw)

def nestedTurnBody (aw levels : ℕ) : Com := (nestedInner aw levels).seq (incrCom "t")

def nestedTurnLoop (aw turns levels : ℕ) : Com :=
  Com.while (.lt (.cell "t") (.lit turns)) (nestedTurnBody aw levels)

/-- **The descending skeleton.**  The third shape, and the consumer's. -/
def nestedSkel (setup aw turns levels : ℕ) : Com :=
  (setupOnly setup).seq (nestedTurnLoop aw turns levels)

/-! ### What the two loops do, exactly -/

/-- **The descent, exactly.**  From depth `j` it carves `levels - j`
arenas and comes out at depth `levels`.  Proved by induction on the
loop's own derivation — no `Good` and no constructed run, so it holds of
*every* run, which is what `NetLe` needs. -/
theorem hp_descendLoop (aw levels : ℕ) : ∀ {s s' : State} {κ : Cost},
    BigStep (descendLoop aw levels) s s' κ → ∀ j : ℕ, s.vars "l" = some j → j ≤ levels →
      hpOf s' = hpOf s + (levels - j) * aw ∧ s'.vars "l" = some levels := by
  intro s s' κ h
  rw [descendLoop, levelLoop] at h
  generalize hw : Com.while (Cond.lt (Operand.cell "l") (Operand.lit levels))
    ((freshPass aw).seq (incrCom "l")) = w at h
  induction h with
  | skip => exact absurd hw (by simp)
  | const hx => exact absurd hw (by simp)
  | copy hx hy => exact absurd hw (by simp)
  | binop hx hy hz => exact absurd hw (by simp)
  | aget hx hi ha hv => exact absurd hw (by simp)
  | aset hi hv ha hk => exact absurd hw (by simp)
  | seq h₁ h₂ ih₁ ih₂ => exact absurd hw (by simp)
  | ite_true hb h ih => exact absurd hw (by simp)
  | ite_false hb h ih => exact absurd hw (by simp)
  | @while_true b' c' s₀ s₁ s₂ κ₁ κ₂ hb hbody hloop ihbody ihloop =>
      obtain ⟨rfl, rfl⟩ := Com.while.inj hw
      intro j hj hjle
      have hlt : j < levels := lt_lit_guard_of hj hb
      obtain ⟨sm, κ₃, κ₄, ha, hi, -⟩ := bigStep_seq_iff.1 hbody
      have hha : hpOf sm = hpOf s₀ + aw := hp_allocLit (by decide) (by decide) ha
      have hla : sm.vars "l" = some j := by
        rw [vars_allocLit ha (by decide) (by decide) (by decide)]; exact hj
      have hhi : hpOf s₁ = hpOf sm := hp_eq_of_not_mentions hi (by decide)
      have hli : s₁.vars "l" = some (j + 1) := vars_incrCom (by decide) hla hi
      obtain ⟨hh, hl⟩ := ihloop hw (j + 1) hli (by omega)
      refine ⟨?_, hl⟩
      have hstep : levels - j = (levels - (j + 1)) + 1 := by omega
      have hmul : (levels - j) * aw = (levels - (j + 1)) * aw + aw := by
        rw [hstep, add_mul, one_mul]
      omega
  | @while_false b' c' s₀ hb =>
      obtain ⟨rfl, rfl⟩ := Com.while.inj hw
      intro j hj hjle
      have hge : levels ≤ j := lt_lit_guard_false hj hb
      obtain rfl : j = levels := by omega
      exact ⟨by simp, hj⟩

/-- **The unwind, exactly.**  From depth `j` it gives back `j` arenas and
comes out at depth `0`.  The bump pointer's arithmetic is `ℕ` monus, and
that is sound here precisely because the unwind is LIFO: it never frees
what it did not carve. -/
theorem hp_ascendLoop (aw : ℕ) : ∀ {s s' : State} {κ : Cost},
    BigStep (ascendLoop aw) s s' κ → ∀ j : ℕ, s.vars "l" = some j →
      hpOf s' = hpOf s - j * aw := by
  intro s s' κ h
  rw [ascendLoop] at h
  generalize hw : Com.while (Cond.lt (Operand.lit 0) (Operand.cell "l"))
    ((freeLit aw).seq (decrCom "l")) = w at h
  induction h with
  | skip => exact absurd hw (by simp)
  | const hx => exact absurd hw (by simp)
  | copy hx hy => exact absurd hw (by simp)
  | binop hx hy hz => exact absurd hw (by simp)
  | aget hx hi ha hv => exact absurd hw (by simp)
  | aset hi hv ha hk => exact absurd hw (by simp)
  | seq h₁ h₂ ih₁ ih₂ => exact absurd hw (by simp)
  | ite_true hb h ih => exact absurd hw (by simp)
  | ite_false hb h ih => exact absurd hw (by simp)
  | @while_true b' c' s₀ s₁ s₂ κ₁ κ₂ hb hbody hloop ihbody ihloop =>
      obtain ⟨rfl, rfl⟩ := Com.while.inj hw
      intro j hj
      have hpos : 0 < j := lit_lt_guard_of hj hb
      obtain ⟨sm, κ₃, κ₄, hf, hd, -⟩ := bigStep_seq_iff.1 hbody
      have hhf : hpOf sm = hpOf s₀ - aw := hp_freeLit hf
      have hlf : sm.vars "l" = some j := by
        rw [vars_freeLit hf (by decide) (by decide)]; exact hj
      have hhd : hpOf s₁ = hpOf sm := hp_eq_of_not_mentions hd (by decide)
      have hld : s₁.vars "l" = some (j - 1) := vars_decrCom (by decide) hlf hd
      have hh := ihloop hw (j - 1) hld
      have hstep : j = (j - 1) + 1 := by omega
      have hmul : j * aw = (j - 1) * aw + aw := by
        conv_lhs => rw [hstep]
        rw [add_mul, one_mul]
      omega
  | @while_false b' c' s₀ hb =>
      obtain ⟨rfl, rfl⟩ := Com.while.inj hw
      intro j hj
      obtain rfl : j = 0 := lit_lt_guard_false hj hb
      simp

/-- **A turn of the descending driver returns the bump pointer.**  The
descent carves `levels` arenas, the unwind gives back exactly those — so
arenas accumulate *within* a turn and not *across* turns.  This is the
`NetLe … 0` the turn loop needs, and it is why `turns` is absent from the
peak. -/
theorem hp_nestedInner (aw levels : ℕ) {s s' : State} {κ : Cost}
    (h : BigStep (nestedInner aw levels) s s' κ) : hpOf s' = hpOf s := by
  rw [nestedInner] at h
  obtain ⟨s₂, κ₁, κ₂, hdesc, hasc, -⟩ := bigStep_seq_iff.1 h
  obtain ⟨s₁, κ₃, κ₄, hc, hd, -⟩ := bigStep_seq_iff.1 hdesc
  obtain ⟨-, rfl, -⟩ := bigStep_const_iff.1 hc
  obtain ⟨hh₂, hl₂⟩ := hp_descendLoop aw levels hd 0 (vars_setVar_self _ _ _) (by omega)
  have hh₃ := hp_ascendLoop aw hasc levels hl₂
  rw [hpOf_setVar_ne (by decide : "l" ≠ hpName)] at hh₂
  simp only [Nat.sub_zero] at hh₂
  omega

theorem net_nestedInner (aw levels : ℕ) : NetLe (nestedInner aw levels) 0 :=
  fun _ _ _ h => by rw [hp_nestedInner aw levels h]; omega

/-! ### The peak of the descent -/

theorem descPot_setVar_zero (levels aw : ℕ) (s : State) :
    descPot levels aw (s.setVar "l" 0) = levels * aw := by
  simp [descPot, lOf, State.vars_setVar]

/-- The descent body converts one unit of potential into bump pointer —
so `hpOf + Φ` is exactly preserved.  The guard is what makes this true:
below the depth bound there really is potential left to convert. -/
theorem descend_body_net (aw levels : ℕ) ⦃s s' : State⦄ ⦃κ : Cost⦄
    (hb : (Cond.lt (Operand.cell "l") (Operand.lit levels)).eval s = some true)
    (h : BigStep ((freshPass aw).seq (incrCom "l")) s s' κ) :
    hpOf s' + descPot levels aw s' ≤ hpOf s + descPot levels aw s := by
  obtain ⟨j, hj, hlt⟩ := lt_lit_guard hb
  have hpos : 0 < levels - j := Nat.sub_pos_of_lt hlt
  have hmul : (levels - j) * aw = (levels - (j + 1)) * aw + aw := by
    rw [← Nat.sub_sub]
    conv_lhs => rw [← Nat.sub_add_cancel hpos]
    rw [add_mul]
    simp
  obtain ⟨sm, κ₃, κ₄, ha, hi, -⟩ := bigStep_seq_iff.1 h
  have hha : hpOf sm = hpOf s + aw := hp_allocLit (by decide) (by decide) ha
  have hla : sm.vars "l" = some j := by
    rw [vars_allocLit ha (by decide) (by decide) (by decide)]; exact hj
  have hhi : hpOf s' = hpOf sm := hp_eq_of_not_mentions hi (by decide)
  have hli : s'.vars "l" = some (j + 1) := vars_incrCom (by decide) hla hi
  have hΦ : descPot levels aw s = (levels - j) * aw := by simp [descPot, lOf, hj]
  have hΦ' : descPot levels aw s' = (levels - (j + 1)) * aw := by simp [descPot, lOf, hli]
  omega

/-- …and every intermediate state of the body stays inside that
potential, because one arena is at most the arenas still to carve. -/
theorem descend_body_peak (aw levels : ℕ) ⦃s s' : State⦄
    (hb : (Cond.lt (Operand.cell "l") (Operand.lit levels)).eval s = some true)
    (h : Mid ((freshPass aw).seq (incrCom "l")) s s') :
    hpOf s' ≤ hpOf s + descPot levels aw s := by
  obtain ⟨j, hj, hlt⟩ := lt_lit_guard hb
  have hbody : PeakLe ((freshPass aw).seq (incrCom "l")) aw :=
    peak_mono (peak_seq (net_allocLit (by decide) (by decide) aw)
      (peak_allocLit (by decide) (by decide) aw)
      (peak_of_not_mentions (c := incrCom "l") (by decide))) (by simp)
  have haw : aw ≤ (levels - j) * aw := Nat.le_mul_of_pos_left aw (Nat.sub_pos_of_lt hlt)
  have hΦ : descPot levels aw s = (levels - j) * aw := by simp [descPot, lOf, hj]
  have := hbody h
  omega

/-- **The descent phase's peak is `levels * aw`** — the iteration count of
the descent is `levels`, and that is the only place it appears. -/
theorem peak_descendPhase (aw levels : ℕ) :
    PeakLe ((Com.const "l" 0).seq (descendLoop aw levels)) (levels * aw) := by
  intro s s' h
  cases h with
  | start => omega
  | done hb =>
      obtain ⟨s₁, κ₃, κ₄, hc, hd, -⟩ := bigStep_seq_iff.1 hb
      obtain ⟨-, rfl, -⟩ := bigStep_const_iff.1 hc
      obtain ⟨hh, -⟩ := hp_descendLoop aw levels hd 0 (vars_setVar_self _ _ _) (by omega)
      rw [hpOf_setVar_ne (by decide : "l" ≠ hpName)] at hh
      simp only [Nat.sub_zero] at hh
      omega
  | seqL hm => rw [mid_hp_eq_of_not_mentions hm (by decide)]; omega
  | seqR h₁ h₂ =>
      obtain ⟨-, rfl, -⟩ := bigStep_const_iff.1 h₁
      have hpk := peak_while_pot (descend_body_net aw levels) (descend_body_peak aw levels) h₂
      rw [descPot_setVar_zero, hpOf_setVar_ne (by decide : "l" ≠ hpName)] at hpk
      omega

theorem net_descendPhase (aw levels : ℕ) :
    NetLe ((Com.const "l" 0).seq (descendLoop aw levels)) (levels * aw) := by
  intro s s' κ h
  obtain ⟨s₁, κ₃, κ₄, hc, hd, -⟩ := bigStep_seq_iff.1 h
  obtain ⟨-, rfl, -⟩ := bigStep_const_iff.1 hc
  obtain ⟨hh, -⟩ := hp_descendLoop aw levels hd 0 (vars_setVar_self _ _ _) (by omega)
  rw [hpOf_setVar_ne (by decide : "l" ≠ hpName)] at hh
  simp only [Nat.sub_zero] at hh
  omega

/-! ### The unwind, and the whole skeleton -/

theorem net_ascendLoop (aw : ℕ) : NetLe (ascendLoop aw) 0 :=
  net_while (net_mono (net_seq (net_freeLit aw)
    (net_of_not_mentions (c := decrCom "l") (by decide))) (by omega))

theorem peak_ascendLoop (aw : ℕ) : PeakLe (ascendLoop aw) 0 :=
  peak_while (net_mono (net_seq (net_freeLit aw)
      (net_of_not_mentions (c := decrCom "l") (by decide))) (by omega))
    (peak_mono (peak_seq (net_freeLit aw) (peak_freeLit aw)
      (peak_of_not_mentions (c := decrCom "l") (by decide))) (by simp))

theorem peak_nestedInner (aw levels : ℕ) : PeakLe (nestedInner aw levels) (levels * aw) :=
  peak_mono (peak_seq (net_descendPhase aw levels) (peak_descendPhase aw levels)
    (peak_ascendLoop aw)) (by simp)

/-- **The descending skeleton's peak: `setup + levels * aw`.**

`turns` does not occur, and that absence is the theorem's content: the
unwind returns each turn's arenas, so turns do not compose.  `levels`
*does* occur, and that too is the content: the descent holds one arena
live per level, so depth composes.  This skeleton sits exactly between
`reuseSkel` (`setup + aw`, nothing accumulates) and `freshSkel`
(`setup + turns * levels * aw`, everything does). -/
theorem peak_nestedSkel (setup aw turns levels : ℕ) :
    PeakLe (nestedSkel setup aw turns levels) (setup + levels * aw) := by
  have hbodyNet : NetLe (nestedTurnBody aw levels) 0 :=
    net_mono (net_seq (net_nestedInner aw levels)
      (net_of_not_mentions (c := incrCom "t") (by decide))) (by omega)
  have hbodyPeak : PeakLe (nestedTurnBody aw levels) (levels * aw) :=
    peak_mono (peak_seq (net_nestedInner aw levels) (peak_nestedInner aw levels)
      (peak_of_not_mentions (c := incrCom "t") (by decide))) (by simp)
  have hloop : PeakLe (nestedTurnLoop aw turns levels) (levels * aw) :=
    peak_while hbodyNet hbodyPeak
  exact peak_mono (peak_seq (net_allocLit (by decide) (by decide) setup)
    (peak_allocLit (by decide) (by decide) setup) hloop) (by simp)

/-- **…and it is attained**, at the bottom of the first turn's descent.
So the bound is the peak, not an over-estimate — which is what makes the
`←` direction of `nested_fits_iff` and the refutation below possible. -/
theorem nested_peak_attained (setup aw turns levels : ℕ) (hturns : 0 < turns)
    {s : State} (hs : Good s) (ht : s.vars "t" = some 0) :
    ∃ s' : State, Mid (nestedSkel setup aw turns levels) s s' ∧
      hpOf s' = hpOf s + setup + levels * aw := by
  obtain ⟨s₁, κ₁, hsetup, hg₁, hh₁, hfr₁⟩ :=
    run_allocLit (dst := "base") (by decide) (by decide) (fun h => h.base) (k := setup) hs
  have ht₁ : s₁.vars "t" = some 0 := by
    rw [hfr₁ "t" (by decide) (by decide) (by decide)]; exact ht
  have hguardT : (Cond.lt (Operand.cell "t") (Operand.lit turns)).eval s₁ = some true := by
    simp [ht₁, hturns]
  have hconstL : BigStep (Com.const "l" 0) s₁ (s₁.setVar "l" 0)
      (ACost.cost Currency.const 1) := BigStep.const hg₁.l
  have hg₂ : Good (s₁.setVar "l" 0) := hg₁.setVar "l" 0
  have hl₂ : (s₁.setVar "l" 0).vars "l" = some 0 := vars_setVar_self _ _ _
  obtain ⟨s₃, κ₃, hdesc, -, hh₃, -, -⟩ :=
    run_countedLoop (x := "l") (keep := ["t"]) (c := freshPass aw) (d := aw) (N := levels)
      (by decide) (by decide) (by decide) (by decide) (run_freshPass aw)
      levels 0 (by omega) (by omega) (s₁.setVar "l" 0) hg₂ hl₂
  refine ⟨s₃, Mid.seqR hsetup (Mid.whileBody hguardT (Mid.seqL (Mid.seqL
    (Mid.seqR hconstL (Mid.done hdesc))))), ?_⟩
  rw [hh₃, hpOf_setVar_ne (by decide : "l" ≠ hpName), hh₁, Nat.sub_zero]

/-! ### The fits statement, as an `↔`

The question the consumer actually has to answer is not "does it fit"
— for a big enough word length everything fits — but **how large a word
length the shape demands**.  Both directions are available here, because
the peak is both bounded (`peak_nestedSkel`) and attained
(`nested_peak_attained`), so the following is an `↔` and not an
implication. -/

open Lax13Proofs.Compile in
/-- **The descending skeleton fits the probe's layout at word length `w`
iff `2 ^ w` covers `setup + levels * aw` plus the layout's own
constant.**  `→` is the attainment, `←` is the peak bound; `turns`
occurs on neither side.

Read asymptotically, this is the statement the leaf exists to make: the
descending driver fits a word length **linear in `|x|` exactly when
`levels * aw` is linear in `|x|`** — bounded recursion depth times
per-level arena.  It is not assumed; it is the two directions above. -/
theorem nested_fits_iff (setup aw turns levels w : ℕ) (hturns : 0 < turns) :
    (∃ (B : ℕ) (L : Layout), L.scalars = probeScalars ∧ L.arrays = [heapName] ∧
        L.temps = 0 ∧ L.FitsWords B w ∧
        ∀ s' : State, Mid (nestedSkel setup aw turns levels) entryState s' → hpOf s' < B)
      ↔ max (setup + levels * aw + 9) 10 ≤ 2 ^ w := by
  constructor
  · rintro ⟨B, L, hsc, har, htm, hfit, hall⟩
    obtain ⟨s', hmid, hh⟩ :=
      nested_peak_attained setup aw turns levels hturns good_entryState t_entryState
    have hlt : hpOf s' < B := hall s' hmid
    rw [hh, hpOf_entryState] at hlt
    have hspan := hfit.span
    have hone := hfit.one_lt
    rw [Layout.span, hsc, har, htm] at hspan
    simp only [probeScalars, List.length_cons, List.length_nil] at hspan
    omega
  · intro hM
    refine ⟨max (setup + levels * aw + 1) 2, ⟨probeScalars, [heapName], 0⟩, rfl, rfl, rfl,
      ⟨by omega, by omega, ?_⟩, ?_⟩
    · show Layout.span _ (max (setup + levels * aw + 1) 2) ≤ 2 ^ w
      simp only [Layout.span, probeScalars, List.length_cons, List.length_nil]
      omega
    · intro s' hmid
      have := peak_nestedSkel setup aw turns levels hmid
      rw [hpOf_entryState] at this
      omega

/-! ### The two controls

The `↔` cuts both ways, so the leaf can fail — and does, on one side. -/

open Lax13Proofs.Compile in
/-- **Control A — bounded depth fits, at a word length the domain
admits.**  A fixed sentence and a fixed `ε` fix `levels`, and then the
descending driver is inside the budget: the same fair comparison
`reuse_fits_at_admissible_word` makes. -/
theorem nested_fits_at_admissible_word (c n setup aw turns levels : ℕ) :
    ∃ (w B : ℕ) (L : Layout),
      2 ^ w ≤ 2 * max (c * (2 * n + 4)) (setup + levels * aw + 10) ∧
      (∀ v ∈ probeWord n, c * ((probeWord n).length + v + 1) ≤ 2 ^ w) ∧
      L.FitsWords B w ∧ L.scalars = probeScalars ∧ L.arrays = [heapName] ∧
      ∀ s s' : State, Mid (nestedSkel setup aw turns levels) s s' → hpOf s = 0 →
        hpOf s' < B := by
  obtain ⟨w, hw1, hw2⟩ :=
    exists_pow_between (m := max (c * (2 * n + 4)) (setup + levels * aw + 10)) (by omega)
  have hspan : setup + levels * aw + 10 ≤ 2 ^ w := le_trans (le_max_right _ _) hw1
  have hdom : c * (2 * n + 4) ≤ 2 ^ w := le_trans (le_max_left _ _) hw1
  refine ⟨w, setup + levels * aw + 2, ⟨probeScalars, [heapName], 0⟩, hw2, ?_,
    ⟨by omega, by omega, ?_⟩, rfl, rfl, ?_⟩
  · intro v hv
    refine le_trans ?_ hdom
    rw [length_probeWord]
    rcases mem_probeWord hv with rfl | rfl <;> exact Nat.mul_le_mul_left c (by omega)
  · show Layout.span _ (setup + levels * aw + 2) ≤ 2 ^ w
    simp only [Layout.span, probeScalars, List.length_cons, List.length_nil]
    omega
  · intro s s' hm hs
    have := peak_nestedSkel setup aw turns levels hm
    omega

-- **Control A, concretely**: at `c = 10 ^ 9`, `n = 10 ^ 20`, a setup and
-- an arena both linear in `n` and a *constant* depth `3`, the peak is
-- below what C0's domain already grants — so bounded depth costs no word
-- length at all beyond the domain's own.
#guard 10 ^ 20 + 3 * 10 ^ 20 + 10 ≤ 10 ^ 9 * (2 * 10 ^ 20 + 4)

open Lax13Proofs.Compile in
/-- **Control B — depth growing with `n` is refuted, at every admissible
word length.**  This is the one that earns the leaf: the descending
driver is *not* automatically safe.  What it must maintain is exactly
`levels * aw` linear in `|x|`; past the crossover no word size rescues
it, in the same shape as `no_word_size_for_fresh` — and note that
`turns` does not appear in the hypothesis, so this is a statement about
depth alone. -/
theorem no_word_size_for_nested (c n setup aw turns levels : ℕ) (hc : 0 < c)
    (hturns : 0 < turns) (hcross : 4 * c * (n + 2) ≤ levels * aw) :
    ∃ w : ℕ,
      (∀ v ∈ probeWord n, c * ((probeWord n).length + v + 1) ≤ 2 ^ w) ∧
      ∀ (L : Layout) (B : ℕ) (s : State), Good s → hpOf s = 0 → s.vars "t" = some 0 →
        L.FitsWords B w →
        ¬ (∀ s' : State, Mid (nestedSkel setup aw turns levels) s s' → hpOf s' < B) := by
  obtain ⟨w, hadm, hw⟩ := admissible_word_small c n hc
  refine ⟨w, hadm, fun L B s hs hhp ht hfit => ?_⟩
  refine no_word_size_of_reaches hcross hw ?_ hfit
  obtain ⟨s', hmid, hh⟩ := nested_peak_attained setup aw turns levels hturns hs ht
  exact ⟨s', hmid, by rw [hh, hhp]; omega⟩

-- **Control B is inhabited**: depth and arena both growing as
-- `n ^ (3/4)` gives `levels * aw = n ^ (3/2)`, past the crossover — the
-- descending driver is refuted at `Σ` exactly the sub-quadratic total
-- that refutes `freshSkel`, but now with `turns = 1`.
#guard 4 * 10 ^ 9 * (10 ^ 20 + 2) ≤ 10 ^ 15 * 10 ^ 15

-- …and **it does not fire at bounded depth**, which is what makes it a
-- control rather than a blanket refutation: at `levels = 3` and an arena
-- of `10 ^ 10` the crossover hypothesis fails at the same instance.
#guard ¬ (4 * 10 ^ 9 * (10 ^ 20 + 2) ≤ 3 * 10 ^ 10)

-- The three shapes really are three: at `turns = 10 ^ 20`, `levels = 3`,
-- `aw = 10 ^ 10`, the reusing peak is `aw`, the descending peak
-- `levels * aw`, and the fresh total `turns * levels * aw`.
#guard 10 ^ 10 < 3 * 10 ^ 10
#guard 3 * 10 ^ 10 < 10 ^ 20 * 3 * 10 ^ 10

-- The unwind really is the only difference from the refuted skeleton:
-- both have the same descent.  (The `hasAset` / `opCount` checks for the
-- descending skeleton are in §10, with those definitions.)
#guard descendLoop 7 3 == levelLoop (freshPass 7) 3

#print axioms peak_while_pot
#print axioms hp_descendLoop
#print axioms hp_ascendLoop
#print axioms hp_nestedInner
#print axioms peak_nestedSkel
#print axioms nested_peak_attained
#print axioms nested_fits_iff
#print axioms nested_fits_at_admissible_word
#print axioms no_word_size_for_nested

end Descending

/-! ## 10. Registration discipline, and the no-re-zeroing check

E29's other half: synthesis must not silently pick an **allocating**
form inside a loop and fail only at the bridge, sessions later.
`mentions hpName` is `decide`-checkable, so that is a compiled check —
`ArrayListGrowSynth`'s `growBlock_no_hp` / `allocProg_uses_hp` idiom. -/

/-- Does the command write an array anywhere?  A re-zeroing sweep must;
a touched-only pass must not. -/
def hasAset : Com → Bool
  | .aset _ _ _ => true
  | .seq c d => hasAset c || hasAset d
  | .ite _ c d => hasAset c || hasAset d
  | .while _ c => hasAset c
  | _ => false

/-- Does the command contain a loop? -/
def hasWhile : Com → Bool
  | .while _ _ => true
  | .seq c d => hasWhile c || hasWhile d
  | .ite _ c d => hasWhile c || hasWhile d
  | _ => false

/-- The command's instruction count — the *static* one, so a pass whose
count does not depend on the arena width cannot be `O(aw)`. -/
def opCount : Com → ℕ
  | .skip | .const _ _ | .copy _ _ | .binop _ _ _ _ | .aget _ _ _ | .aset _ _ _ => 1
  | .seq c d => opCount c + opCount d
  | .ite _ c d => 1 + opCount c + opCount d
  | .while _ c => 1 + opCount c

section Gate

-- **The registration check.**  The caller-owned skeleton's loop interior
-- does not mention the bump-pointer cell…
#guard mentions hpName (turnBody ownedPass 7) = false
#guard mentions hpName (levelLoop ownedPass 7) = false

-- …while its setup does, which is where the allocations belong.
#guard mentions hpName (setupWithArena 5 7) = true

-- **The check bites** — it is not true of everything.  The reusing
-- skeleton's interior allocates, and so do the landed primitives.
#guard mentions hpName (turnBody (reusePass 7) 3) = true
#guard mentions hpName (turnBody (freshPass 7) 3) = true
#guard mentions hpName (allocProg "p" "n") = true
#guard mentions hpName (freeProg "n") = true

-- **The no-re-zeroing check (E27/E28).**  A pass that reused freed space
-- and then wanted clean state would need an `O(aw)` sweep; the passes
-- here contain no array write and no loop at all, so they cannot.
#guard hasAset (reusePass 7) = false
#guard hasWhile (reusePass 7) = false
#guard hasAset ownedPass = false
#guard hasWhile ownedPass = false

-- …and that check bites too: a sweep is exactly what it rejects.
#guard hasAset (Com.while (.lt (.cell "i") (.lit 7)) (Com.aset heapName "i" "z")) = true
#guard hasWhile (Com.while (.lt (.cell "i") (.lit 7)) (Com.aset heapName "i" "z")) = true

-- **The time budget, in compiled form.**  The pass's instruction count
-- is independent of the arena width: a linear term would break these,
-- exactly as `allocCost_const` guards `alloc`'s price.
#guard opCount (reusePass 0) == opCount (reusePass 1000000)
#guard opCount (reusePass 3) == 6
#guard opCount (turnBody (reusePass 3) 5) == opCount (turnBody (reusePass 1000000) 5)

-- **The descending skeleton, same two checks.**  Its turn interior *does*
-- mention the bump-pointer cell — the honest reading of a driver that
-- holds arenas live across a recursive call — while neither phase
-- sweeps, so no re-zeroing can hide in it and its instruction count is
-- independent of the arena width.
#guard mentions hpName (nestedTurnBody 7 3) = true
#guard hasAset (nestedTurnBody 7 3) = false
#guard hasAset (ascendLoop 7) = false
#guard opCount (nestedTurnBody 0 3) == opCount (nestedTurnBody 1000000 3)

-- The skeletons really are the same program modulo the pass, and the
-- reusing one really does contain both primitives.
#guard reuseSkel 5 7 3 2 == (allocLit "base" 5).seq (turnLoop (reusePass 7) 3 2)
#guard freshSkel 5 7 3 2 == (allocLit "base" 5).seq (turnLoop (freshPass 7) 3 2)

end Gate

/-! ## 11. Which availability flavour each skeleton consumes

E27/E28, made explicit rather than left to the prose.  Both statements
are instantiations of the landed triples of `HeapAlloc.lean`, at the
skeleton's own cell names — so if the flavour ever changed, these would
stop typechecking. -/

/-- **The first reusing pass degrades `avail` to `availRaw`.**  What the
arena gives back is raw, not zeroed: `availRaw_not_entails_avail` says
there is no way back, and re-zeroing would cost `O(aw)`. -/
example (aw k old hp : ℕ) :
    irTriple (¤(allocCost aw + freeCost aw) ∗ ("arena" ↦ᵥ old) ∗ avail hp (aw + k) ∗
        ("aw" ↦ᵥ aw))
      ((allocProg "arena" "aw").seq (freeProg "aw"))
      (("arena" ↦ᵥ hp) ∗ availRaw hp (aw + k) ∗ ("aw" ↦ᵥ aw)) :=
  alloc_free_roundtrip "arena" "aw" old hp aw k

/-- **Every later reusing pass consumes `availRaw` and returns it**, in
O(1) — which is why the peak does not grow with `turns`. -/
example (k old p : ℕ) (xs : List Val) :
    irTriple (¤(freeCost xs.length + allocCost xs.length) ∗ ("arena" ↦ᵥ old) ∗ (p ↦ₕ xs) ∗
        availRaw (p + xs.length) k ∗ ("aw" ↦ᵥ xs.length))
      ((freeProg "aw").seq (allocProg "arena" "aw"))
      (("arena" ↦ᵥ p) ∗ rawSpace p xs.length ∗ availRaw (p + xs.length) k ∗
        ("aw" ↦ᵥ xs.length)) :=
  free_allocRaw_reuse "arena" "aw" old p k xs

/-- **The caller-owned skeleton's arena is carved once, zeroed**, out of
the entry availability, and then threaded — no per-pass allocation at
all, so no flavour question arises inside the loop. -/
example (aw k old hp : ℕ) :
    irTriple (¤(allocCost aw) ∗ ("arena" ↦ᵥ old) ∗ avail hp (aw + k) ∗ ("aw" ↦ᵥ aw))
      (allocProg "arena" "aw")
      (("arena" ↦ᵥ hp) ∗ (hp ↦ₕ List.replicate aw 0) ∗ avail (hp + aw) k ∗ ("aw" ↦ᵥ aw)) :=
  alloc_triple "arena" "aw" old hp aw k

/-! ## 12. The axiom gate -/

#print axioms peak_reuseSkel
#print axioms peak_ownedSkel
#print axioms peak_while
#print axioms net_while
#print axioms fits_of_peak_linear
#print axioms reuse_fits_linear
#print axioms final_hp_is_not_peak
#print axioms run_countedLoop
#print axioms run_freshSkel
#print axioms run_reuseSkel
#print axioms reuse_peak_attained
#print axioms admissible_word_small
#print axioms no_word_size_for_fresh
#print axioms no_word_size_for_wasteful
#print axioms fits_at_a_free_word_length
#print axioms no_word_size_for_fresh_at_entry
#print axioms reuse_fits_at_admissible_word
#print axioms reuse_fits_where_fresh_cannot

end Lax13Proofs.Refine.Sepref.SpaceBudget
