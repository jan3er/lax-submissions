import Lax13.Ram
import Mathlib.Tactic

/-!
Reasoning kit for the word machine: the equations of the concept's
definitions, composition of runs, and the placement predicate `Fits`.

Every equation here is proved by `rfl`. The concept's `step`,
`Instr.effect` and `Op.value` are defined by pattern matching, and
`simp`-unfolding such a definition creates an auxiliary declaration
named after it — in the concept's namespace, which this package is not
allowed to declare into. So the equations are restated here, in this
package's namespace, and only these are ever used.

The word length appears in two places: every value the machine produces
carries a `% 2 ^ w`, and every address it uses carries one. The lemmas
below come in two flavours accordingly — the raw equation, and the
version whose hypothesis is that the value or the address is a word, in
which case `Nat.mod_eq_of_lt` removes the reduction. Everything above
this file uses only the second flavour, which is what makes the
simulation an equality with the unbounded reference semantics rather
than a congruence modulo `2 ^ w`.
-/

namespace Lax13Proofs.Machine

open Lax13.Ram

/-- There is at least one word. -/
theorem two_pow_pos (w : ℕ) : 0 < 2 ^ w := by positivity

/-! ### Memory -/

theorem setCell_eq (w : ℕ) (m : ℕ → ℕ) (a v b : ℕ) :
    setCell w m a v b = if b = a % 2 ^ w then v % 2 ^ w else m b := rfl

/-- Writing a word to a cell whose address is a word is an ordinary
update. -/
theorem setCell_self {w a v : ℕ} (m : ℕ → ℕ) (ha : a < 2 ^ w) (hv : v < 2 ^ w) :
    setCell w m a v a = v := by
  rw [setCell_eq, Nat.mod_eq_of_lt ha, if_pos rfl, Nat.mod_eq_of_lt hv]

/-- A write to a word address leaves every other cell alone. -/
theorem setCell_of_ne {w a b : ℕ} (m : ℕ → ℕ) (v : ℕ) (ha : a < 2 ^ w) (hb : b ≠ a) :
    setCell w m a v b = m b := by
  rw [setCell_eq, Nat.mod_eq_of_lt ha, if_neg hb]

/-! ### Operands -/

@[simp] theorem value_lit (w n : ℕ) (m : ℕ → ℕ) : (Op.lit n).value w m = n := rfl

theorem value_mem_eq (w a : ℕ) (m : ℕ → ℕ) : (Op.mem a).value w m = m (a % 2 ^ w) := rfl

theorem value_ind_eq (w a : ℕ) (m : ℕ → ℕ) :
    (Op.ind a).value w m = m (m (a % 2 ^ w) % 2 ^ w) := rfl

theorem value_mem {w a : ℕ} (m : ℕ → ℕ) (ha : a < 2 ^ w) : (Op.mem a).value w m = m a := by
  rw [value_mem_eq, Nat.mod_eq_of_lt ha]

theorem value_ind {w a : ℕ} (m : ℕ → ℕ) (ha : a < 2 ^ w) (hm : m a < 2 ^ w) :
    (Op.ind a).value w m = m (m a) := by
  rw [value_ind_eq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hm]

/-! ### Instructions -/

@[simp] theorem effect_load (w : ℕ) (o : Op) (s : State) :
    (Instr.load o).effect w s =
      some { s with pc := s.pc + 1, acc := o.value w s.mem % 2 ^ w } := rfl

@[simp] theorem effect_store (w a : ℕ) (s : State) :
    (Instr.store a).effect w s =
      some { s with pc := s.pc + 1, mem := setCell w s.mem a s.acc } := rfl

@[simp] theorem effect_storeInd (w a : ℕ) (s : State) :
    (Instr.storeInd a).effect w s =
      some { s with pc := s.pc + 1, mem := setCell w s.mem (s.mem (a % 2 ^ w)) s.acc } := rfl

@[simp] theorem effect_add (w : ℕ) (o : Op) (s : State) :
    (Instr.add o).effect w s =
      some { s with pc := s.pc + 1, acc := (s.acc + o.value w s.mem) % 2 ^ w } := rfl

@[simp] theorem effect_sub (w : ℕ) (o : Op) (s : State) :
    (Instr.sub o).effect w s =
      some { s with pc := s.pc + 1, acc := (s.acc - o.value w s.mem) % 2 ^ w } := rfl

@[simp] theorem effect_mul (w : ℕ) (o : Op) (s : State) :
    (Instr.mul o).effect w s =
      some { s with pc := s.pc + 1, acc := (s.acc * o.value w s.mem) % 2 ^ w } := rfl

@[simp] theorem effect_div (w : ℕ) (o : Op) (s : State) :
    (Instr.div o).effect w s =
      some { s with pc := s.pc + 1, acc := (s.acc / o.value w s.mem) % 2 ^ w } := rfl

@[simp] theorem effect_and (w : ℕ) (o : Op) (s : State) :
    (Instr.and o).effect w s =
      some { s with pc := s.pc + 1, acc := Nat.land s.acc (o.value w s.mem) % 2 ^ w } := rfl

@[simp] theorem effect_or (w : ℕ) (o : Op) (s : State) :
    (Instr.or o).effect w s =
      some { s with pc := s.pc + 1, acc := Nat.lor s.acc (o.value w s.mem) % 2 ^ w } := rfl

@[simp] theorem effect_xor (w : ℕ) (o : Op) (s : State) :
    (Instr.xor o).effect w s =
      some { s with pc := s.pc + 1, acc := Nat.xor s.acc (o.value w s.mem) % 2 ^ w } := rfl

@[simp] theorem effect_shiftl (w : ℕ) (o : Op) (s : State) :
    (Instr.shiftl o).effect w s =
      some { s with pc := s.pc + 1, acc := s.acc * 2 ^ o.value w s.mem % 2 ^ w } := rfl

@[simp] theorem effect_shiftr (w : ℕ) (o : Op) (s : State) :
    (Instr.shiftr o).effect w s =
      some { s with pc := s.pc + 1, acc := s.acc / 2 ^ o.value w s.mem % 2 ^ w } := rfl

@[simp] theorem effect_jump (w l : ℕ) (s : State) :
    (Instr.jump l).effect w s = some { s with pc := l } := rfl

@[simp] theorem effect_jzero (w l : ℕ) (s : State) :
    (Instr.jzero l).effect w s =
      some { s with pc := if s.acc = 0 then l else s.pc + 1 } := rfl

@[simp] theorem effect_jgtz (w l : ℕ) (s : State) :
    (Instr.jgtz l).effect w s =
      some { s with pc := if 0 < s.acc then l else s.pc + 1 } := rfl

@[simp] theorem effect_halt (w : ℕ) (s : State) : Instr.halt.effect w s = none := rfl

@[simp] theorem effect_write (w : ℕ) (o : Op) (s : State) :
    (Instr.write o).effect w s =
      some { s with pc := s.pc + 1, out := s.out ++ [o.value w s.mem % 2 ^ w] } := rfl

theorem effect_read_eq (w a : ℕ) (s : State) :
    (Instr.read a).effect w s =
      s.inp.head?.map fun v =>
        { s with pc := s.pc + 1, mem := setCell w s.mem a v, inp := s.inp.tail } := rfl

theorem effect_read {w : ℕ} {s : State} {v : ℕ} {rest : List ℕ} (a : ℕ)
    (h : s.inp = v :: rest) :
    (Instr.read a).effect w s =
      some { s with pc := s.pc + 1, mem := setCell w s.mem a v, inp := rest } := by
  rw [effect_read_eq, h]; rfl

/-! ### Running -/

theorem step_eq (w : ℕ) (p : Program) (s : State) :
    step w p s = p[s.pc]?.bind fun i => i.effect w s := rfl

@[simp] theorem run_zero (w : ℕ) (p : Program) (s : State) : run w p 0 s = some s := rfl

theorem run_succ (w : ℕ) (p : Program) (t : ℕ) (s : State) :
    run w p (t + 1) s = (step w p s).bind (run w p t) := rfl

theorem run_add (w : ℕ) (p : Program) (t t' : ℕ) (s : State) :
    run w p (t + t') s = (run w p t s).bind (run w p t') := by
  induction t generalizing s with
  | zero => simp
  | succ t ih =>
      rw [Nat.succ_add, run_succ, run_succ]
      cases h : step w p s with
      | none => simp
      | some s₁ => simpa using ih s₁

/-- Runs compose: `t₁` steps to `s₁` and then `t₂` steps to `s₂`. -/
theorem run_trans {w : ℕ} {p : Program} {t₁ t₂ : ℕ} {s s₁ s₂ : State}
    (h₁ : run w p t₁ s = some s₁) (h₂ : run w p t₂ s₁ = some s₂) :
    run w p (t₁ + t₂) s = some s₂ := by
  rw [run_add, h₁]; exact h₂

/-- One step, when the instruction at the program counter is known. -/
theorem run_one {w : ℕ} {p : Program} {s : State} {ins : Instr} (h : p[s.pc]? = some ins) :
    run w p 1 s = ins.effect w s := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_eq, h]
  show (ins.effect w s).bind (run w p 0) = ins.effect w s
  cases ins.effect w s <;> rfl

/-! ### Placement -/

/-- The program `p` contains the block `q` at address `a`. -/
def Fits (p : Program) (a : ℕ) (q : Program) : Prop :=
  ∀ i, i < q.length → p[a + i]? = q[i]?

theorem Fits.head {p : Program} {a : ℕ} {ins : Instr} {q : Program}
    (h : Fits p a (ins :: q)) : p[a]? = some ins := by
  simpa using h 0 (by simp)

theorem fits_append {p : Program} {a : ℕ} {q r : Program} :
    Fits p a (q ++ r) ↔ Fits p a q ∧ Fits p (a + q.length) r := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i (by simp; omega)
      rwa [List.getElem?_append_left hi] at this
    · have := h (q.length + i) (by simp; omega)
      rw [List.getElem?_append_right (by omega)] at this
      simpa [Nat.add_assoc] using this
  · rintro ⟨h₁, h₂⟩ i hi
    rcases lt_or_ge i q.length with hlt | hge
    · rw [List.getElem?_append_left hlt]; exact h₁ i hlt
    · rw [List.getElem?_append_right hge]
      have := h₂ (i - q.length) (by simp at hi; omega)
      rwa [Nat.add_assoc, Nat.add_sub_cancel' hge] at this

theorem Fits.congr {p : Program} {a a' : ℕ} {q : Program} (h : Fits p a q) (ha : a = a') :
    Fits p a' q := ha ▸ h

theorem fits_singleton {p : Program} {a : ℕ} {ins : Instr} :
    Fits p a [ins] ↔ p[a]? = some ins := by
  constructor
  · exact fun h => h.head
  · intro h i hi
    have : i = 0 := by simp at hi; omega
    subst this
    simpa using h

theorem fits_self (q r : Program) : Fits (q ++ r) 0 q := by
  intro i hi
  simpa using List.getElem?_append_left (l₂ := r) hi

end Lax13Proofs.Machine
