import Lax13Proofs.Refine.Codegen.BigStepB

/-!
The bounds pass: a verification-condition generator for
`∃ s' κ, Ir.BigStepB B c s s' κ`.

**This file is ours** (ledger **D3**); its specification is the last
paragraph of `plans/word-ram/refinement-tower/p5-codegen-design.md` §5,
"the bound is a genuine per-program obligation".

## Why there is a second derivation at all

`hnRefine` (P4) delivers a *plain* run: its `natAssn` is deliberately
unbounded, matching the NREST layer above it, and the Isabelle source
owes no bound only because its concrete values are machine words,
bounded by their type. Ours are `ℕ`. The codegen boundary
(`Sim.lean`) consumes a `BigStepB`, so somebody has to prove that the
run's values stay below `B`, and that somebody is this file: a VCG over
the *deep* syntax tree, whose output is exactly the arithmetic the
abstract invariants already prove (`i + 1 ≤ n + 1 < B`).

Design record P5/D-a records the deliberate choice of the two-derivation
route over the source-faithful `wordAssn B` retrofit inside synthesis;
the telemetry that decides whether to revisit it is the *annotation
line count* per program, measured in `Examples/EndToEnd.lean`.

## The shape

`Runs B c s Q` is the goal — "`c` runs from `s` under the bound, and the
state it stops in satisfies `Q`". Everything is stated at it:

* `bwp B c Q` is a genuine weakest precondition for the *loop-free*
  fragment, computed by structural recursion on the syntax tree, with
  `bwp_sound` its one soundness theorem. Applying `bwp_sound` and
  unfolding is the whole of `ir_bound_vcg`: what is left is one
  definedness fact per cell touched and one `< B` fact per value
  created.
* `runs_while` is the loop rule, an invariant and a variant, proved by
  strong induction on the variant. A loop is the one place a VCG over a
  deep syntax tree cannot be a computation, so it is the one place a
  program pays an annotation.

The obligations are honest about which ops create values. `copy`,
`aget` and `aset` create none — they need no `< B` goal at all — and the
five *non-growing* arithmetic operators discharge theirs from the state
invariant alone (`apply_sub_lt` and friends below). What is left over is
`const`, `add`, `mul`, `shiftl`, the two bit-spreading operators at a
power-of-two bound, and the literals of guards: precisely the design
record's list.

## Judgment calls

**P5/D-aa — the VCG is a weakest precondition over the loop-free
fragment plus a rule at the loop, not an inductive `BSpec` calculus.**
The design record asks for "per-op lemmas … seq/ite composition … a
while rule … then a seed tactic". A Hoare-style calculus needs the
intermediate assertion of every `seq` to be guessed by the tactic; a
`wp` computes it. Since `Ir.Com` is a deep, *concrete* tree at every
call site, `bwp` reduces by `simp only [bwp]` to a single conjunction
with no metavariable anywhere, which is what makes `ir_bound_vcg` a
three-line macro rather than a search. The per-op lemmas of the record
are still there — they are the equations of `bwp`, and each is stated
and proved as a standalone `simp` lemma below.

**P5/D-ab — `bwp` at a `while` is the goal itself, not `False`.** A
weakest precondition for a loop is not computable, and the honest
options are to make the VCG fail there or to let it stop there. It
stops: `bwp B (.while b c) Q s` is *defined* as `Runs B (.while b c) s
Q`, so a loop nested inside straight-line code is left as a residual
goal in exactly the form `runs_while` closes, and `bwp_sound` stays a
theorem about the whole language rather than about a fragment.

**P5/D-ac — the bit operators are bounded at a power-of-two bound
only.** `Nat.land m n ≤ m` holds outright, so `and` is free; `lor` and
`xor` can exceed both arguments (`1 ||| 2 = 3`), and the standard bound
for them is `< 2 ^ k` when both arguments are. The design record's
"power-of-two convention" is therefore recorded as the *hypothesis* of
`apply_or_lt` / `apply_xor_lt` rather than as a global assumption on
`B`: a program that uses neither operator — both toys, and P7's BFS —
never sees it, and `B = 2 ^ w` is what the machine boundary supplies
anyway.
-/

namespace Lax13Proofs.Refine.Ir

/-! ### The goal -/

/-- `Runs B c s Q`: from `s`, the command `c` has a *bounded* run, and
the state it stops in satisfies `Q`. This is the bounds pass's goal
shape; `Sim.lean` consumes the derivation, and the final state is
pinned only as far as the invariants of the pass need it. -/
def Runs (B : ℕ) (c : Com) (s : State) (Q : State → Prop) : Prop :=
  ∃ s' κ, BigStepB B c s s' κ ∧ Q s'

/-- The bounds witness the cashing theorem asks for, forgetting the
postcondition. -/
theorem Runs.exists {B : ℕ} {c : Com} {s : State} {Q : State → Prop} (h : Runs B c s Q) :
    ∃ s' κ, BigStepB B c s s' κ := by
  obtain ⟨s', κ, hr, -⟩ := h
  exact ⟨s', κ, hr⟩

/-- Weakening the postcondition. -/
theorem Runs.mono {B : ℕ} {c : Com} {s : State} {Q Q' : State → Prop} (h : Runs B c s Q)
    (hQ : ∀ s', Q s' → Q' s') : Runs B c s Q' := by
  obtain ⟨s', κ, hr, hq⟩ := h
  exact ⟨s', κ, hr, hQ s' hq⟩

/-- Sequencing two runs. -/
theorem Runs.seq {B : ℕ} {c d : Com} {s : State} {M Q : State → Prop} (h : Runs B c s M)
    (h' : ∀ s₁, M s₁ → Runs B d s₁ Q) : Runs B (.seq c d) s Q := by
  obtain ⟨s₁, κ₁, hr, hm⟩ := h
  obtain ⟨s₂, κ₂, hr', hq⟩ := h' s₁ hm
  exact ⟨s₂, κ₁ + κ₂, .seq hr hr', hq⟩

/-! ### Reading an operand and a guard under the bound

The four lemmas a guard obligation is discharged by: a cell is below the
bound because the state invariant says so, a literal because it is a
numeral, and a condition because both its operands are. -/

/-- A defined cell, under the state invariant. -/
theorem Operand.evalB_cell_of_stateBound {B : ℕ} {s : State} (hs : StateBound B s)
    {x : String} {v : Val} (hx : s.vars x = some v) :
    (Operand.cell x).evalB B s = some v :=
  Operand.evalB_of_eval (by simpa using hx) (hs.var hx)

/-- A literal below the bound. -/
theorem Operand.evalB_lit_of_lt {B : ℕ} {n : Val} {s : State} (h : n < B) :
    (Operand.lit n).evalB B s = some n :=
  Operand.evalB_of_eval rfl h

/-- An equality guard whose two operands read. -/
theorem Cond.evalB_eq_of {B : ℕ} {u v : Operand} {s : State} {m n : Val}
    (hu : u.evalB B s = some m) (hv : v.evalB B s = some n) :
    (Cond.eq u v).evalB B s = some (m == n) := by
  rw [Cond.evalB_eq, hu, hv]; rfl

/-- A comparison guard whose two operands read. -/
theorem Cond.evalB_lt_of {B : ℕ} {u v : Operand} {s : State} {m n : Val}
    (hu : u.evalB B s = some m) (hv : v.evalB B s = some n) :
    (Cond.lt u v).evalB B s = some (decide (m < n)) := by
  rw [Cond.evalB_lt, hu, hv]; rfl

/-! ### The non-growing operators

Five of the nine arithmetic operators cannot leave the range their
arguments came from, so their `< B` obligation is discharged from
`StateBound` alone and never reaches the user. The remaining four —
`add`, `mul`, `shiftl`, and `or`/`xor` off a power-of-two bound — are
the genuine per-program goals (judgment call P5/D-ac). -/

theorem apply_sub_lt {B m n : ℕ} (h : m < B) : Imp.Bop.sub.apply m n < B :=
  lt_of_le_of_lt (Nat.sub_le m n) h

theorem apply_div_lt {B m n : ℕ} (h : m < B) : Imp.Bop.div.apply m n < B :=
  lt_of_le_of_lt (Nat.div_le_self m n) h

theorem apply_shiftr_lt {B m n : ℕ} (h : m < B) : Imp.Bop.shiftr.apply m n < B :=
  lt_of_le_of_lt (Nat.div_le_self m _) h

theorem apply_and_lt {B m n : ℕ} (h : m < B) : Imp.Bop.and.apply m n < B :=
  lt_of_le_of_lt (Nat.and_le_left) h

theorem apply_or_lt {B k m n : ℕ} (hB : 2 ^ k ≤ B) (hm : m < 2 ^ k) (hn : n < 2 ^ k) :
    Imp.Bop.or.apply m n < B :=
  lt_of_lt_of_le (Nat.or_lt_two_pow hm hn) hB

theorem apply_xor_lt {B k m n : ℕ} (hB : 2 ^ k ≤ B) (hm : m < 2 ^ k) (hn : n < 2 ^ k) :
    Imp.Bop.xor.apply m n < B :=
  lt_of_lt_of_le (Nat.xor_lt_two_pow hm hn) hB

/-! ### The weakest precondition of the loop-free fragment -/

/-- `bwp B c Q` — what a state must satisfy for `c` to have a bounded
run into `Q`. One clause per op, each of them the op's rule of
`BigStepB` read backwards: the cells it touches must exist, the values
it creates must fit, and the state it leaves must satisfy `Q`. At a
loop the recursion stops and the goal is reproduced (judgment call
P5/D-ab). -/
def bwp (B : ℕ) : Com → (State → Prop) → State → Prop
  | .skip, Q => Q
  | .const x n, Q => fun s => s.vars x ≠ none ∧ n < B ∧ Q (s.setVar x n)
  | .copy x y, Q => fun s => s.vars x ≠ none ∧ ∃ v, s.vars y = some v ∧ Q (s.setVar x v)
  | .binop op x y z, Q => fun s => s.vars x ≠ none ∧ ∃ m n, s.vars y = some m ∧
      s.vars z = some n ∧ op.apply m n < B ∧ Q (s.setVar x (op.apply m n))
  | .aget x a i, Q => fun s => s.vars x ≠ none ∧ ∃ k xs v, s.vars i = some k ∧
      s.arrs a = some xs ∧ xs[k]? = some v ∧ Q (s.setVar x v)
  | .aset a i v, Q => fun s => ∃ k n xs, s.vars i = some k ∧ s.vars v = some n ∧
      s.arrs a = some xs ∧ k < xs.length ∧ Q (s.setArr a (xs.set k n))
  | .seq c d, Q => bwp B c (bwp B d Q)
  | .ite b c d, Q => fun s => (b.evalB B s = some true ∧ bwp B c Q s) ∨
      (b.evalB B s = some false ∧ bwp B d Q s)
  | .while b c, Q => fun s => Runs B (.while b c) s Q

@[simp] theorem bwp_skip (B : ℕ) (Q : State → Prop) : bwp B .skip Q = Q := rfl

@[simp] theorem bwp_const (B : ℕ) (x : String) (n : Val) (Q : State → Prop) (s : State) :
    bwp B (.const x n) Q s ↔ s.vars x ≠ none ∧ n < B ∧ Q (s.setVar x n) := Iff.rfl

@[simp] theorem bwp_copy (B : ℕ) (x y : String) (Q : State → Prop) (s : State) :
    bwp B (.copy x y) Q s ↔ s.vars x ≠ none ∧ ∃ v, s.vars y = some v ∧ Q (s.setVar x v) :=
  Iff.rfl

@[simp] theorem bwp_binop (B : ℕ) (op : Imp.Bop) (x y z : String) (Q : State → Prop)
    (s : State) :
    bwp B (.binop op x y z) Q s ↔ s.vars x ≠ none ∧ ∃ m n, s.vars y = some m ∧
      s.vars z = some n ∧ op.apply m n < B ∧ Q (s.setVar x (op.apply m n)) := Iff.rfl

@[simp] theorem bwp_aget (B : ℕ) (x a i : String) (Q : State → Prop) (s : State) :
    bwp B (.aget x a i) Q s ↔ s.vars x ≠ none ∧ ∃ k xs v, s.vars i = some k ∧
      s.arrs a = some xs ∧ xs[k]? = some v ∧ Q (s.setVar x v) := Iff.rfl

@[simp] theorem bwp_aset (B : ℕ) (a i v : String) (Q : State → Prop) (s : State) :
    bwp B (.aset a i v) Q s ↔ ∃ k n xs, s.vars i = some k ∧ s.vars v = some n ∧
      s.arrs a = some xs ∧ k < xs.length ∧ Q (s.setArr a (xs.set k n)) := Iff.rfl

@[simp] theorem bwp_seq (B : ℕ) (c d : Com) (Q : State → Prop) :
    bwp B (.seq c d) Q = bwp B c (bwp B d Q) := rfl

@[simp] theorem bwp_ite (B : ℕ) (b : Cond) (c d : Com) (Q : State → Prop) (s : State) :
    bwp B (.ite b c d) Q s ↔ (b.evalB B s = some true ∧ bwp B c Q s) ∨
      (b.evalB B s = some false ∧ bwp B d Q s) := Iff.rfl

@[simp] theorem bwp_while (B : ℕ) (b : Cond) (c : Com) (Q : State → Prop) (s : State) :
    bwp B (.while b c) Q s ↔ Runs B (.while b c) s Q := Iff.rfl

/-- **Soundness.** The weakest precondition is a precondition: one
induction over the syntax tree, one constructor of `BigStepB` per
clause. -/
theorem bwp_sound {B : ℕ} {c : Com} {Q : State → Prop} {s : State} (h : bwp B c Q s) :
    Runs B c s Q := by
  induction c generalizing Q s with
  | skip => exact ⟨s, _, .skip, h⟩
  | const x n => exact ⟨_, _, .const h.1 h.2.1, h.2.2⟩
  | copy x y =>
      obtain ⟨hx, v, hy, hq⟩ := h
      exact ⟨_, _, .copy hx hy, hq⟩
  | binop op x y z =>
      obtain ⟨hx, m, n, hy, hz, hb, hq⟩ := h
      exact ⟨_, _, .binop hx hy hz hb, hq⟩
  | aget x a i =>
      obtain ⟨hx, k, xs, v, hi, ha, hv, hq⟩ := h
      exact ⟨_, _, .aget hx hi ha hv, hq⟩
  | aset a i v =>
      obtain ⟨k, n, xs, hi, hv, ha, hk, hq⟩ := h
      exact ⟨_, _, .aset hi hv ha hk, hq⟩
  | seq c d ihc ihd =>
      exact (ihc h).seq fun s₁ hm => ihd hm
  | ite b c d ihc ihd =>
      rcases h with ⟨hb, hc⟩ | ⟨hb, hd⟩
      · obtain ⟨s', κ, hr, hq⟩ := ihc hc
        exact ⟨s', _, .ite_true hb hr, hq⟩
      · obtain ⟨s', κ, hr, hq⟩ := ihd hd
        exact ⟨s', _, .ite_false hb hr, hq⟩
  | «while» b c _ => exact h

/-! ### The loop rule -/

/-- **The loop rule.** An invariant that determines the guard and a
variant the body decreases. This is the one annotation a program pays
to the bounds pass; everything else `ir_bound_vcg` computes.

The invariant is *not* forced to be `StateBound B` — that is a
consequence of `BigStepB.stateBound`, not a hypothesis — but in practice
a caller conjoins it, because that is where the guard's cell bounds and
the body's non-growing operators come from. -/
theorem runs_while {B : ℕ} {b : Cond} {body : Com} (I : State → Prop) (V : State → ℕ)
    (hg : ∀ s, I s → ∃ r, b.evalB B s = some r)
    (hbody : ∀ s, I s → b.evalB B s = some true →
      Runs B body s (fun s' => I s' ∧ V s' < V s))
    {s : State} (hs : I s) :
    Runs B (.while b body) s (fun s' => I s' ∧ b.evalB B s' = some false) := by
  suffices key : ∀ n s, I s → V s ≤ n →
      Runs B (.while b body) s (fun s' => I s' ∧ b.evalB B s' = some false) from
    key (V s) s hs le_rfl
  intro n
  induction n with
  | zero =>
      intro s hI hle
      obtain ⟨r, hr⟩ := hg s hI
      cases r with
      | false => exact ⟨s, _, .while_false hr, hI, hr⟩
      | true =>
          obtain ⟨s₁, -, -, -, hlt⟩ := hbody s hI hr
          omega
  | succ n ih =>
      intro s hI hle
      obtain ⟨r, hr⟩ := hg s hI
      cases r with
      | false => exact ⟨s, _, .while_false hr, hI, hr⟩
      | true =>
          obtain ⟨s₁, κ₁, hr₁, hI₁, hlt⟩ := hbody s hI hr
          obtain ⟨s₂, κ₂, hr₂, hq⟩ := ih s₁ hI₁ (by omega)
          exact ⟨s₂, _, .while_true hr hr₁ hr₂, hq⟩

/-! ### The seed tactic

`ir_bound_vcg` is the design record's seed: apply soundness, unfold the
weakest precondition on the concrete tree, and normalise the state
updates the clauses left behind. What survives is the arithmetic. -/

/-- Unfold the bounds VCG on a concrete `Ir.Com` and normalise. Leaves
one goal, a conjunction of definedness and `< B` facts; a loop is left
as a `Runs` goal for `runs_while`. -/
syntax (name := irBoundVcg) "ir_bound_vcg"
  (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ir_bound_vcg) =>
      `(tactic| refine bwp_sound ?_ <;>
          simp only [bwp_skip, bwp_const, bwp_copy, bwp_binop, bwp_aget, bwp_aset,
            bwp_seq, bwp_ite, bwp_while, State.vars_setVar, State.arrs_setVar,
            State.vars_setArr, State.arrs_setArr, Imp.Bop.apply_add, Imp.Bop.apply_sub,
            Imp.Bop.apply_mul, ne_eq, reduceIte, if_true, if_false])
  | `(tactic| ir_bound_vcg [$ts,*]) =>
      `(tactic| (simp only [$ts,*]; ir_bound_vcg))

/-! ### The gate

Two straight-line programs and one loop, run through the VCG on
`Ir/Semantics.lean`'s own gate states, plus the negative control the
whole pass exists for: the *same* program at a bound its values do not
fit under has no bounded run, and the VCG's obligation is exactly the
one that fails. -/

namespace VcgGate

/-- `a := 6; b := 7; c := a * b; d := c - b`, from wave A's state: the
VCG leaves five definedness facts, two literal bounds, two arithmetic
bounds and the value, and every one of them is a numeral. -/
theorem arith_runs : Runs 128 Gate.arith Gate.arithState (fun s => s.vars "d" = some 35) := by
  ir_bound_vcg [Gate.arith, Gate.arithState]
  exact ⟨by decide, by decide, by decide, by decide, by decide, 6, 7, by decide, by decide,
    by decide, by decide, 42, 7, by decide, by decide, by decide, by decide⟩

/-- The array roundtrip. No value is created, so the only obligations
are definedness and the index being in range. -/
theorem roundtrip_runs :
    Runs 128 Gate.roundtrip Gate.roundtripState (fun s => s.arrs "A" = some [3, 1, 3]) := by
  ir_bound_vcg [Gate.roundtrip, Gate.roundtripState]
  exact ⟨by decide, 0, [3, 1, 4], 3, by decide, by decide, by decide, 2, 3, [3, 1, 4],
    by decide, by decide, by decide, by decide, by decide⟩

/-! #### The loop

`one := 1; while 0 < n do n := n - one`, from `n = 2`. Two lines of
annotation — the invariant and the variant — and the body is the
tactic's. Note that the *subtraction* costs no bound obligation
(`apply_sub_lt`); what the invariant is for is the guard, whose literal
`0` and cell `n` both have to be readable below the bound. -/

/-- The invariant. -/
def cdInv (s : State) : Prop :=
  (∃ k : ℕ, s.vars "n" = some k ∧ k ≤ 2) ∧ s.vars "one" = some 1

/-- The variant. -/
def cdVar (s : State) : ℕ := (s.vars "n").getD 0

/-- The guard, read off the invariant. -/
theorem cd_guard {t : State} {k : ℕ} (hk : t.vars "n" = some k) (hkle : k ≤ 2) :
    (Cond.lt (.lit 0) (.cell "n")).evalB 128 t = some (decide (0 < k)) := by
  have h1 : (Operand.lit 0).evalB 128 t = some 0 := Operand.evalB_lit_of_lt (by decide)
  have hkB : k < 128 := by omega
  have h2 : (Operand.cell "n").evalB 128 t = some k :=
    Operand.evalB_of_eval (by simpa using hk) hkB
  exact Cond.evalB_lt_of h1 h2

theorem countdown_runs :
    Runs 128 Gate.countdown (Gate.countdownState 2) (fun s => s.vars "n" = some 0) := by
  rw [show Gate.countdown = Com.seq (.const "one" 1)
    (.while (.lt (.lit 0) (.cell "n")) (.binop .sub "n" "n" "one")) from rfl]
  refine Runs.seq (M := cdInv) (bwp_sound ?_) fun s hs => (runs_while cdInv cdVar ?_ ?_ hs).mono ?_
  · exact ⟨by decide, by decide, ⟨2, by decide, by decide⟩, by decide⟩
  · rintro t ⟨⟨k, hk, hkle⟩, -⟩
    exact ⟨_, cd_guard hk hkle⟩
  · rintro t ⟨⟨k, hk, hkle⟩, hone⟩ hb
    rw [cd_guard hk hkle] at hb
    have hk0 : 0 < k := by simpa using hb
    have hlt : Imp.Bop.sub.apply k 1 < 128 := apply_sub_lt (show k < 128 by omega)
    have hne : t.vars "n" ≠ none := by rw [hk]; simp
    have hval : (t.setVar "n" (Imp.Bop.sub.apply k 1)).vars "n" = some (k - 1) := by simp
    have hone' : (t.setVar "n" (Imp.Bop.sub.apply k 1)).vars "one" = some 1 := by
      simpa using hone
    have hle : k - 1 ≤ 2 := by omega
    have hvar : cdVar (t.setVar "n" (Imp.Bop.sub.apply k 1)) < cdVar t := by
      simp [cdVar, hk]
      omega
    exact bwp_sound (c := .binop .sub "n" "n" "one")
      ⟨hne, k, 1, hk, hone, hlt, ⟨⟨k - 1, hval, hle⟩, hone'⟩, hvar⟩
  · rintro t ⟨⟨⟨k, hk, hkle⟩, -⟩, hfalse⟩
    rw [cd_guard hk hkle] at hfalse
    have hk0 : k = 0 := by
      have : ¬ (0 < k) := by simpa using hfalse
      omega
    rw [hk, hk0]

/-! #### The negative control

The obligation the VCG produces is the one that decides the matter: at a
bound the literal does not fit under, `200 < 128` is false, and there is
indeed no bounded run (`BigStepB.lean`'s `no_bigStepB_bigConst`). -/

example : ¬ (200 < 128) := by decide

theorem no_runs_bigConst :
    ¬ Runs 128 (.const "x" 200) Ir.BoundGate.bigConstState (fun _ => True) := by
  rintro ⟨s', κ, h, -⟩
  exact Ir.BoundGate.no_bigStepB_bigConst ⟨s', κ, h⟩

#print axioms bwp_sound
#print axioms runs_while
#print axioms countdown_runs

end VcgGate

end Lax13Proofs.Refine.Ir
