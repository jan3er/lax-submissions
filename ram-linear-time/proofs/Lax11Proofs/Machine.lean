import Lax11.Ram
import Mathlib.Tactic

/-!
Reasoning kit for the machine: the equations of the concept's
definitions, composition of runs, and the placement predicate `Fits`.

Every equation here is proved by `rfl`. The concept's `step`,
`Instr.effect` and `Op.value` are defined by pattern matching, and
`simp`-unfolding such a definition creates an auxiliary declaration
named after it — in the concept's namespace, which this package is not
allowed to declare into. So the equations are restated here, in this
package's namespace, and only these are ever used.
-/

namespace Lax11Proofs.Machine

open Lax11.Ram

/-! ### Memory -/

theorem setCell_eq (m : ℕ → ℕ) (a v b : ℕ) :
    setCell m a v b = if b = a then v else m b := rfl

@[simp] theorem setCell_self (m : ℕ → ℕ) (a v : ℕ) : setCell m a v a = v := by
  simp [setCell_eq]

theorem setCell_of_ne {b a : ℕ} (m : ℕ → ℕ) (v : ℕ) (h : b ≠ a) :
    setCell m a v b = m b := by simp [setCell_eq, h]

/-! ### Operands -/

@[simp] theorem value_lit (n : ℕ) (m : ℕ → ℕ) : (Op.lit n).value m = n := rfl

@[simp] theorem value_mem (a : ℕ) (m : ℕ → ℕ) : (Op.mem a).value m = m a := rfl

@[simp] theorem value_ind (a : ℕ) (m : ℕ → ℕ) : (Op.ind a).value m = m (m a) := rfl

/-! ### Instructions -/

@[simp] theorem effect_load (o : Op) (s : State) :
    (Instr.load o).effect s = some { s with pc := s.pc + 1, acc := o.value s.mem } := rfl

@[simp] theorem effect_store (a : ℕ) (s : State) :
    (Instr.store a).effect s =
      some { s with pc := s.pc + 1, mem := setCell s.mem a s.acc } := rfl

@[simp] theorem effect_storeInd (a : ℕ) (s : State) :
    (Instr.storeInd a).effect s =
      some { s with pc := s.pc + 1, mem := setCell s.mem (s.mem a) s.acc } := rfl

@[simp] theorem effect_add (o : Op) (s : State) :
    (Instr.add o).effect s =
      some { s with pc := s.pc + 1, acc := s.acc + o.value s.mem } := rfl

@[simp] theorem effect_sub (o : Op) (s : State) :
    (Instr.sub o).effect s =
      some { s with pc := s.pc + 1, acc := s.acc - o.value s.mem } := rfl

@[simp] theorem effect_jump (l : ℕ) (s : State) :
    (Instr.jump l).effect s = some { s with pc := l } := rfl

@[simp] theorem effect_jzero (l : ℕ) (s : State) :
    (Instr.jzero l).effect s =
      some { s with pc := if s.acc = 0 then l else s.pc + 1 } := rfl

@[simp] theorem effect_jgtz (l : ℕ) (s : State) :
    (Instr.jgtz l).effect s =
      some { s with pc := if 0 < s.acc then l else s.pc + 1 } := rfl

@[simp] theorem effect_halt (s : State) : Instr.halt.effect s = none := rfl

@[simp] theorem effect_write (o : Op) (s : State) :
    (Instr.write o).effect s =
      some { s with pc := s.pc + 1, out := s.out ++ [o.value s.mem] } := rfl

theorem effect_read_eq (a : ℕ) (s : State) :
    (Instr.read a).effect s =
      s.inp.head?.map fun v =>
        { s with pc := s.pc + 1, mem := setCell s.mem a v, inp := s.inp.tail } := rfl

theorem effect_read {s : State} {v : ℕ} {rest : List ℕ} (a : ℕ) (h : s.inp = v :: rest) :
    (Instr.read a).effect s =
      some { s with pc := s.pc + 1, mem := setCell s.mem a v, inp := rest } := by
  rw [effect_read_eq, h]; rfl

/-! ### Running -/

theorem step_eq (p : Program) (s : State) :
    step p s = p[s.pc]?.bind fun i => i.effect s := rfl

@[simp] theorem run_zero (p : Program) (s : State) : run p 0 s = some s := rfl

theorem run_succ (p : Program) (t : ℕ) (s : State) :
    run p (t + 1) s = (step p s).bind (run p t) := rfl

theorem run_add (p : Program) (t t' : ℕ) (s : State) :
    run p (t + t') s = (run p t s).bind (run p t') := by
  induction t generalizing s with
  | zero => simp
  | succ t ih =>
      rw [Nat.succ_add, run_succ, run_succ]
      cases h : step p s with
      | none => simp
      | some s₁ => simpa using ih s₁

/-- Runs compose: `t₁` steps to `s₁` and then `t₂` steps to `s₂`. -/
theorem run_trans {p : Program} {t₁ t₂ : ℕ} {s s₁ s₂ : State}
    (h₁ : run p t₁ s = some s₁) (h₂ : run p t₂ s₁ = some s₂) :
    run p (t₁ + t₂) s = some s₂ := by
  rw [run_add, h₁]; exact h₂

/-- One step, when the instruction at the program counter is known. -/
theorem run_one {p : Program} {s : State} {ins : Instr} (h : p[s.pc]? = some ins) :
    run p 1 s = ins.effect s := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, step_eq, h]
  show (ins.effect s).bind (run p 0) = ins.effect s
  cases ins.effect s <;> rfl

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
    simp only [List.length_singleton] at hi
    interval_cases i
    simpa using h

end Lax11Proofs.Machine
