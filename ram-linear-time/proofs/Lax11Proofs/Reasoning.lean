import Lax11.RamComputes
import Lax11Proofs.Simulation

/-!
The reasoning kit: how an algorithm is actually proved in this stack.

A big-step derivation is the wrong object to hand a user. It fixes the
cost *on the nose* — the constructors produce sums like
`1 + b.size + k + k'`, which no bound is definitionally equal to — and
it forces every loop to be re-proved by hand from the two `while`
constructors. This layer fixes both, and nothing else:

`Run c σ σ' K` says that `c`, started in `σ`, terminates in `σ'` at a
cost of **at most** `K`. Every construct gets a rule, the rules compose
by adding bounds, and slack can be introduced at any point (`Run.mono`)
instead of being pushed to the end.

The loop rule is the only one with content. It takes an invariant `I`
and a **potential** `Φ : Env → ℕ`, and asks that one iteration —
condition test included — pay for itself out of the potential:
`1 + b.size + K + Φ σ' ≤ Φ σ`. Termination and the cost bound then come
out together, because a potential that pays for a nonzero cost is also
a variant; the loop costs at most `Φ σ + 1 + b.size`, the extra term
being the test that fails. Amortized arguments are the reason for the
potential form: a BFS scan cannot bound the cost of one outer iteration
by a constant, but it can pay for it out of "queue entries left plus
adjacency slots left". `Run.while_count` is the uniform-cost special
case, an invariant and a variant, for the loops where that suffices.

*Why there is no separate DSL and no fuel interpreter here.* The plan
for this layer was a second syntax `Prog` with an executable fuel
denotation, a compiler to IMP+ and an adequacy theorem. Written out,
`Prog` is `Com`, its compiler is the identity, and adequacy is a
restatement — the syntax distance is zero, because IMP+ was already
designed to be written by hand. The fuel interpreter would earn its
keep only if per-algorithm proofs evaluated it, and they cannot: the
environments in an invariant are symbolic, so `run` never reduces where
it would be needed. Executable testing, the interpreter's other
purpose, is already available one level down and is *better* there,
since `#eval`-ing the compiled machine program tests the compiler too.
What was actually needed from the plan's P3 is this file: the bounded
judgment and the loop rule (D19).
-/

namespace Lax11Proofs.Reasoning

open Lax11.Ram Lax11.RamComputes Lax11Proofs.Imp Lax11Proofs.Compile
open Lax11Proofs.Simulation

/-! ### Reading an updated environment

Every rule below produces an environment written as a chain of updates,
and every use reads a variable back out of such a chain. These are the
lemmas that collapse the chain; they are `simp` lemmas, so the reader
of an algorithm proof sees `simp` where the P1-level proof had explicit
`Env.setVar` unfolding at every step. -/

@[simp] theorem vars_setVar (σ : Env) (x : String) (v : ℕ) (y : String) :
    (σ.setVar x v).vars y = if y = x then v else σ.vars y := rfl

@[simp] theorem arrs_setVar (σ : Env) (x : String) (v : ℕ) :
    (σ.setVar x v).arrs = σ.arrs := rfl

@[simp] theorem inp_setVar (σ : Env) (x : String) (v : ℕ) :
    (σ.setVar x v).inp = σ.inp := rfl

@[simp] theorem out_setVar (σ : Env) (x : String) (v : ℕ) :
    (σ.setVar x v).out = σ.out := rfl

@[simp] theorem vars_setArr (σ : Env) (a : String) (i v : ℕ) :
    (σ.setArr a i v).vars = σ.vars := rfl

@[simp] theorem arrs_setArr (σ : Env) (a : String) (i v : ℕ) (b : String) :
    (σ.setArr a i v).arrs b = if b = a then (σ.arrs a).set i v else σ.arrs b := rfl

@[simp] theorem inp_setArr (σ : Env) (a : String) (i v : ℕ) :
    (σ.setArr a i v).inp = σ.inp := rfl

@[simp] theorem out_setArr (σ : Env) (a : String) (i v : ℕ) :
    (σ.setArr a i v).out = σ.out := rfl

/-- A store never changes the length of any array, which is what the
range condition of the next store is about. -/
@[simp] theorem length_arrs_setArr (σ : Env) (a : String) (i v : ℕ) (b : String) :
    ((σ.setArr a i v).arrs b).length = (σ.arrs b).length := by
  rw [arrs_setArr]; split
  · subst_vars; exact List.length_set ..
  · rfl

/-! ### Arrays as functions

An IMP+ array is a list, but an invariant wants to say what is *at*
each position, not what the list is. `arrOf n f` is the array of length
`n` whose entry `i` is `f i`; an invariant then names the function, a
store updates the function at a point, and a read is a function
application. -/

/-- The array of length `n` whose `i`-th entry is `f i`. -/
def arrOf (n : ℕ) (f : ℕ → ℕ) : List ℕ := (List.range n).map f

@[simp] theorem length_arrOf (n : ℕ) (f : ℕ → ℕ) : (arrOf n f).length = n := by
  simp [arrOf]

@[simp] theorem getElem?_arrOf {n i : ℕ} (f : ℕ → ℕ) (h : i < n) :
    (arrOf n f)[i]? = some (f i) := by
  simp [arrOf, List.getElem?_map, List.getElem?_range, h]

/-- Storing into an array updates the function it comes from. -/
theorem set_arrOf {n i : ℕ} (f : ℕ → ℕ) (v : ℕ) :
    (arrOf n f).set i v = arrOf n (fun k => if k = i then v else f k) := by
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  simp only [arrOf, List.length_map, List.length_range] at h₁ h₂
  rw [List.getElem_set]
  by_cases hk : k = i
  · subst hk; simp [arrOf]
  · simp [arrOf, hk, Ne.symm hk]

/-! ### Evaluating expressions and counting their size

Both are structural recursions on syntax, and both are wanted as `simp`
rules: an algorithm proof should never see an `Expr.eval` and should
never be told what a concrete expression costs. With these, a side
condition of the form `e.eval σ = some v` on a concrete `e` in a
concrete update chain is closed by `simp`, and a cost bound over
concrete syntax becomes arithmetic on numerals. -/

@[simp] theorem eval_lit (n : ℕ) (σ : Env) : (Expr.lit n).eval σ = some n := rfl

@[simp] theorem eval_var (x : String) (σ : Env) : (Expr.var x).eval σ = some (σ.vars x) := rfl

@[simp] theorem eval_get (a : String) (i : Expr) (σ : Env) :
    (Expr.get a i).eval σ = (i.eval σ).bind fun k => (σ.arrs a)[k]? := rfl

@[simp] theorem eval_add (e f : Expr) (σ : Env) :
    (Expr.add e f).eval σ = (e.eval σ).bind fun m => (f.eval σ).map fun n => m + n := rfl

@[simp] theorem eval_sub (e f : Expr) (σ : Env) :
    (Expr.sub e f).eval σ = (e.eval σ).bind fun m => (f.eval σ).map fun n => m - n := rfl

@[simp] theorem eval_condEq (e f : Expr) (σ : Env) :
    (Cond.eq e f).eval σ = (e.eval σ).bind fun m => (f.eval σ).map fun n => m == n := rfl

@[simp] theorem eval_condLt (e f : Expr) (σ : Env) :
    (Cond.lt e f).eval σ = (e.eval σ).bind fun m => (f.eval σ).map fun n => decide (m < n) := rfl

@[simp] theorem size_lit (n : ℕ) : (Expr.lit n).size = 1 := rfl
@[simp] theorem size_var (x : String) : (Expr.var x).size = 1 := rfl
@[simp] theorem size_get (a : String) (i : Expr) : (Expr.get a i).size = i.size + 1 := rfl
@[simp] theorem size_add (e f : Expr) : (Expr.add e f).size = e.size + f.size + 1 := rfl
@[simp] theorem size_sub (e f : Expr) : (Expr.sub e f).size = e.size + f.size + 1 := rfl
@[simp] theorem size_condEq (e f : Expr) : (Cond.eq e f).size = e.size + f.size + 1 := rfl
@[simp] theorem size_condLt (e f : Expr) : (Cond.lt e f).size = e.size + f.size + 1 := rfl

/-! ### The bounded judgment -/

/-- `Run c σ σ' K`: started in `σ`, the command `c` terminates in `σ'`
at a cost of at most `K`. This is the judgment every algorithm proof is
written in; the cost is a bound rather than a value, so the arithmetic
of the cost model never has to be matched syntactically. -/
def Run (c : Com) (σ σ' : Env) (K : ℕ) : Prop := ∃ k ≤ K, BigStep c σ σ' k

theorem Run.of_bigStep {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStep c σ σ' k) :
    Run c σ σ' k := ⟨k, le_rfl, h⟩

/-- Slack may be taken at any point in a proof, not only at the end. -/
theorem Run.mono {c : Com} {σ σ' : Env} {K K' : ℕ} (h : Run c σ σ' K) (hK : K ≤ K') :
    Run c σ σ' K' := by
  obtain ⟨k, hk, hbs⟩ := h; exact ⟨k, hk.trans hK, hbs⟩

/-- The final environment matters only up to equality, and rules
produce it in whatever shape the update chain has. -/
theorem Run.congr {c : Com} {σ σ' σ'' : Env} {K : ℕ} (h : Run c σ σ' K) (hσ : σ' = σ'') :
    Run c σ σ'' K := hσ ▸ h

theorem Run.skip {σ : Env} : Run .skip σ σ 1 := .of_bigStep .skip

theorem Run.assign {σ : Env} {x : String} {e : Expr} {v : ℕ} (h : e.eval σ = some v) :
    Run (.assign x e) σ (σ.setVar x v) (1 + e.size) := .of_bigStep (.assign h)

theorem Run.store {σ : Env} {a : String} {i e : Expr} {idx v : ℕ}
    (hi : i.eval σ = some idx) (he : e.eval σ = some v) (hidx : idx < (σ.arrs a).length) :
    Run (.store a i e) σ (σ.setArr a idx v) (1 + i.size + e.size) :=
  .of_bigStep (.store hi he hidx)

theorem Run.read {σ : Env} {x : String} {v : ℕ} {rest : List ℕ} (h : σ.inp = v :: rest) :
    Run (.read x) σ { σ.setVar x v with inp := rest } 1 := .of_bigStep (.read h)

theorem Run.write {σ : Env} {e : Expr} {v : ℕ} (h : e.eval σ = some v) :
    Run (.write e) σ { σ with out := σ.out ++ [v] } (1 + e.size) := .of_bigStep (.write h)

theorem Run.seq {c d : Com} {σ σ' σ'' : Env} {K K' : ℕ}
    (h : Run c σ σ' K) (h' : Run d σ' σ'' K') : Run (.seq c d) σ σ'' (K + K') := by
  obtain ⟨k, hk, hbs⟩ := h
  obtain ⟨k', hk', hbs'⟩ := h'
  exact ⟨k + k', by omega, .seq hbs hbs'⟩

theorem Run.ite_true {b : Cond} {c d : Com} {σ σ' : Env} {K : ℕ}
    (hb : b.eval σ = some true) (h : Run c σ σ' K) :
    Run (.ite b c d) σ σ' (1 + b.size + K) := by
  obtain ⟨k, hk, hbs⟩ := h
  exact ⟨1 + b.size + k, by omega, .ite_true hb hbs⟩

theorem Run.ite_false {b : Cond} {c d : Com} {σ σ' : Env} {K : ℕ}
    (hb : b.eval σ = some false) (h : Run d σ σ' K) :
    Run (.ite b c d) σ σ' (1 + b.size + K) := by
  obtain ⟨k, hk, hbs⟩ := h
  exact ⟨1 + b.size + k, by omega, .ite_false hb hbs⟩

theorem Run.while_false {b : Cond} {c : Com} {σ : Env} (hb : b.eval σ = some false) :
    Run (.while b c) σ σ (1 + b.size) := .of_bigStep (.while_false hb)

/-! ### The loop rule -/

/-- **The while rule.** Given an invariant `I` whose condition always
evaluates, and a potential `Φ` out of which one iteration — the
condition test included — pays for itself, the loop terminates in a
state that still satisfies `I` and fails the condition, at a cost of at
most `Φ σ + 1 + b.size`.

Termination is not a separate obligation: an iteration costs at least
one unit, so a potential that pays for it strictly decreases. The
potential form is what makes amortized bounds direct — the cost of a
single iteration need not be bounded at all, only the total.

The conclusion bounds the cost by the potential *drop*, not by the
potential at entry. That is what lets one loop's leftover potential pay
for what happens after it: a nested search whose outer sweep and inner
searches draw on the same budget could not be assembled from the weaker
form, since the outer proof would have to count the inner potential
twice. -/
theorem Run.while_pot {b : Cond} {c : Com} (I : Env → Prop) (Φ : Env → ℕ)
    (hdef : ∀ σ, I σ → ∃ v, b.eval σ = some v)
    (hstep : ∀ σ, I σ → b.eval σ = some true →
      ∃ σ' K, Run c σ σ' K ∧ I σ' ∧ 1 + b.size + K + Φ σ' ≤ Φ σ)
    {σ : Env} (hI : I σ) :
    ∃ σ' K, Run (.while b c) σ σ' K ∧ I σ' ∧ b.eval σ' = some false ∧
      K + Φ σ' ≤ Φ σ + 1 + b.size := by
  suffices H : ∀ n σ, I σ → Φ σ ≤ n →
      ∃ σ' K, Run (.while b c) σ σ' K ∧ I σ' ∧ b.eval σ' = some false ∧
        K + Φ σ' ≤ Φ σ + 1 + b.size from H (Φ σ) σ hI le_rfl
  clear hI σ
  intro n
  induction n with
  | zero =>
      intro σ hI hΦ
      obtain ⟨v, hv⟩ := hdef σ hI
      cases v with
      | false => exact ⟨σ, _, Run.while_false hv, hI, hv, by omega⟩
      | true =>
          obtain ⟨σ₁, K, hrun, _, hpay⟩ := hstep σ hI hv
          omega
  | succ n ih =>
      intro σ hI hΦ
      obtain ⟨v, hv⟩ := hdef σ hI
      cases v with
      | false => exact ⟨σ, _, Run.while_false hv, hI, hv, by omega⟩
      | true =>
          obtain ⟨σ₁, K, hrun, hI₁, hpay⟩ := hstep σ hI hv
          obtain ⟨σ', K', hrun', hI', hfalse, hpay'⟩ := ih σ₁ hI₁ (by omega)
          obtain ⟨k, hk, hbs⟩ := hrun
          obtain ⟨k', hk', hbs'⟩ := hrun'
          exact ⟨σ', 1 + b.size + k + k', ⟨1 + b.size + k + k', le_rfl,
            .while_true hv hbs hbs'⟩, hI', hfalse, by omega⟩

/-- **The counted while rule**, the common case: an invariant, a
variant that strictly decreases, and one bound `P` on the cost of an
iteration. -/
theorem Run.while_count {b : Cond} {c : Com} (I : Env → Prop) (V : Env → ℕ) (P : ℕ)
    (hdef : ∀ σ, I σ → ∃ v, b.eval σ = some v)
    (hstep : ∀ σ, I σ → b.eval σ = some true → ∃ σ', Run c σ σ' P ∧ I σ' ∧ V σ' < V σ)
    {σ : Env} (hI : I σ) :
    ∃ σ', Run (.while b c) σ σ' ((1 + b.size + P) * V σ + 1 + b.size) ∧ I σ' ∧
      b.eval σ' = some false := by
  have key : ∀ τ, I τ → b.eval τ = some true →
      ∃ τ' K, Run c τ τ' K ∧ I τ' ∧
        1 + b.size + K + (1 + b.size + P) * V τ' ≤ (1 + b.size + P) * V τ := by
    intro τ hIτ hv
    obtain ⟨τ', hrun, hI', hV⟩ := hstep τ hIτ hv
    refine ⟨τ', P, hrun, hI', ?_⟩
    calc 1 + b.size + P + (1 + b.size + P) * V τ'
        = (1 + b.size + P) * (V τ' + 1) := by ring
      _ ≤ (1 + b.size + P) * V τ := Nat.mul_le_mul_left _ hV
  obtain ⟨σ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_pot I (fun σ => (1 + b.size + P) * V σ) hdef key hI
  exact ⟨σ', hrun.mono (by omega), hI', hfalse⟩

/-! ### Cashing a `Run` in at the concept surface

The one lemma that ends an algorithm proof. Everything below it — the
compiler, the layout invariant, the machine — is discharged by the
simulation theorem; the caller supplies a `Run`, the output it computes
and the arithmetic of the constant. -/

/-- A well-formed IMP+ program whose `Run` on every valid input
produces the right output within `K` compiles to a machine program that
computes the same function within `L.const * K` steps.

The declared array lengths `ext` are chosen *per input*. They have to
be: an algorithm sizes its arrays by what it reads, and the compiled
program does not represent them at all — the machine's memory is
unbounded and starts zeroed, so arrays of any lengths are there for
free, and the lengths exist only to say which accesses are in range
(D17). -/
theorem computesInTime_of_run {L : Layout} {c : Com}
    {D : Set (List ℕ)} {f : List ℕ → List ℕ} {T : List ℕ → ℕ} (hok : Com.Ok L c)
    (h : ∀ x ∈ D, ∃ (ext : String → ℕ) (σ' : Env) (K : ℕ),
      Run c (initEnv ext x) σ' K ∧ σ'.out = f x ∧ L.const * K ≤ T x) :
    ComputesInTime (compileProgram L c) D f T := by
  intro x hx
  obtain ⟨ext, σ', K, ⟨k, hk, hbs⟩, hout, hT⟩ := h x hx
  obtain ⟨t, ht, hrun⟩ := compileProgram_runsTo hok hbs
  refine ⟨t, ?_, ?_⟩
  · exact ht.trans ((Nat.mul_le_mul_left _ hk).trans hT)
  · rwa [hout] at hrun

end Lax11Proofs.Reasoning
