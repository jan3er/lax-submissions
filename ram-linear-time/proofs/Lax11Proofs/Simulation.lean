import Lax11Proofs.Compile
import Lax11Proofs.Machine

/-!
The simulation theorem: a terminating IMP+ run is matched by a run of
the compiled machine program, in a number of steps bounded by a
constant of the program times the cost of the IMP+ run.

The invariant is `Represents`: each scalar sits in its cell, each array
entry *within its declared length* sits in its cell, and the tapes
agree. Array lengths never reach the machine — they only decide which
IMP+ programs have a derivation — so the all-zero memory of a starting
machine represents an environment whose arrays are zero-filled, of
whatever lengths.

Straight-line code is described by `Reaches`, which bundles what every
such block guarantees: it gets to the instruction just past itself, in
at most as many steps as it has instructions, with a known accumulator,
with the tapes untouched, and touching only the temporaries from `d`
upwards. That last clause is the frame condition, and it is why the
compiler can compile the operands of a binary operator at consecutive
depths and rely on the first result surviving the second computation.
-/

namespace Lax11Proofs.Simulation

open Lax11.Ram Lax11Proofs.Imp Lax11Proofs.Compile Lax11Proofs.Machine

/-- The machine state `s` represents the environment `σ`. -/
structure Represents (L : Layout) (σ : Env) (s : State) : Prop where
  /-- Every scalar of the layout is in its cell. -/
  vars : ∀ x ∈ L.scalars, s.mem (L.varAddr x) = σ.vars x
  /-- Every array entry within the array's length is in its cell. -/
  arrs : ∀ a ∈ L.arrays, ∀ i, i < (σ.arrs a).length →
    s.mem (L.arrAddr a i) = (σ.arrs a).getD i 0
  /-- The input tapes agree. -/
  inp : s.inp = σ.inp
  /-- The output tapes agree. -/
  out : s.out = σ.out

/-- The straight-line block laid out at `s.pc` gets from `s` to `s'`.
`len` is its length, `v` the accumulator it leaves, and `d` the first
temporary it is allowed to touch. -/
structure Reaches (p : Program) (L : Layout) (d len v : ℕ) (s s' : State) : Prop where
  /-- It takes at most as many steps as the block has instructions. -/
  steps : ∃ t ≤ len, run p t s = some s'
  /-- It falls through to the instruction just past the block. -/
  pc : s'.pc = s.pc + len
  /-- It leaves `v` in the accumulator. -/
  acc : s'.acc = v
  /-- It does not touch the input tape. -/
  inp : s'.inp = s.inp
  /-- It does not touch the output tape. -/
  out : s'.out = s.out
  /-- It writes only to the temporaries from `d` upwards. -/
  frame : ∀ i, i < d ∨ L.temps ≤ i → s'.mem i = s.mem i

theorem Reaches.trans {p L d d' l₁ l₂ v₁ v₂ s s₁ s₂}
    (h₁ : Reaches p L d l₁ v₁ s s₁) (h₂ : Reaches p L d' l₂ v₂ s₁ s₂) (hd : d ≤ d') :
    Reaches p L d (l₁ + l₂) v₂ s s₂ where
  steps := by
    obtain ⟨t₁, ht₁, hr₁⟩ := h₁.steps
    obtain ⟨t₂, ht₂, hr₂⟩ := h₂.steps
    exact ⟨t₁ + t₂, by omega, run_trans hr₁ hr₂⟩
  pc := by rw [h₂.pc, h₁.pc]; omega
  acc := h₂.acc
  inp := by rw [h₂.inp, h₁.inp]
  out := by rw [h₂.out, h₁.out]
  frame i hi := by
    rw [h₂.frame i (by omega), h₁.frame i hi]

/-- The length of a block is only ever needed up to arithmetic. -/
theorem Reaches.congr {p L d l l' v s s'} (h : Reaches p L d l v s s') (hl : l = l') :
    Reaches p L d l' v s s' := hl ▸ h

/-- A one-instruction block. -/
theorem reaches_one {p : Program} {L : Layout} {d v : ℕ} {s s' : State} {ins : Instr}
    (hf : p[s.pc]? = some ins) (he : ins.effect s = some s')
    (hpc : s'.pc = s.pc + 1) (hacc : s'.acc = v)
    (hinp : s'.inp = s.inp) (hout : s'.out = s.out)
    (hframe : ∀ i, i < d ∨ L.temps ≤ i → s'.mem i = s.mem i) :
    Reaches p L d 1 v s s' where
  steps := ⟨1, le_refl 1, by rw [run_one hf, he]⟩
  pc := hpc
  acc := hacc
  inp := hinp
  out := hout
  frame := hframe

/-- The invariant survives a straight-line block, which touches only
temporaries and neither tape. -/
theorem Represents.reaches {L σ s p d len v s'} (h : Represents L σ s)
    (hr : Reaches p L d len v s s') : Represents L σ s' where
  vars x hx := by rw [hr.frame _ (Or.inr (temps_le_varAddr L x))]; exact h.vars x hx
  arrs a ha i hi := by
    rw [hr.frame _ (Or.inr (le_trans (Nat.le_add_right _ _) (le_arrAddr L a i)))]
    exact h.arrs a ha i hi
  inp := by rw [hr.inp]; exact h.inp
  out := by rw [hr.out]; exact h.out

/-- The invariant does not see the program counter. -/
theorem Represents.setPc {L σ s} (h : Represents L σ s) (n : ℕ) :
    Represents L σ { s with pc := n } :=
  ⟨h.vars, h.arrs, h.inp, h.out⟩

/-- The block of repeated additions in `Layout.idxCode`, which turns
the index `s.acc` into `q` times the index. -/
theorem reaches_adds (n : ℕ) {p : Program} {L : Layout} {d : ℕ} {s : State}
    (hfits : Fits p s.pc (List.replicate n (Instr.add (.mem d)))) :
    ∃ s' : State, Reaches p L d n (s.acc + n * s.mem d) s s' ∧ s'.mem = s.mem := by
  induction n generalizing s with
  | zero =>
      refine ⟨s, ⟨⟨0, le_refl 0, rfl⟩, rfl, by simp, rfl, rfl, fun i _ => rfl⟩, rfl⟩
  | succ n ih =>
      rw [List.replicate_succ, show Instr.add (Op.mem d) :: List.replicate n (Instr.add (.mem d))
            = [Instr.add (.mem d)] ++ List.replicate n (Instr.add (.mem d)) from rfl,
          fits_append] at hfits
      obtain ⟨hf₁, hf₂⟩ := hfits
      set s₁ : State := { s with pc := s.pc + 1, acc := s.acc + s.mem d } with hs₁
      have hstep : Reaches p L d 1 (s.acc + s.mem d) s s₁ :=
        reaches_one (fits_singleton.mp hf₁) rfl rfl rfl rfl rfl (fun i _ => rfl)
      have hpc : s₁.pc = s.pc + 1 := rfl
      obtain ⟨s', hr, hmem⟩ := ih (s := s₁) (by simpa [hpc] using hf₂)
      refine ⟨s', ?_, by rw [hmem]⟩
      have : s₁.acc + n * s₁.mem d = s.acc + (n + 1) * s.mem d := by
        simp [hs₁]; ring
      rw [this] at hr
      exact (hstep.trans hr (le_refl d)).congr (by omega)

/-- `Layout.idxCode` turns the index in the accumulator into the
address of that entry of `a`, in the accumulator and in temporary
`d`. -/
theorem reaches_idxCode {p : Program} {L : Layout} {a : String} {d : ℕ} {s : State}
    (ha : a ∈ L.arrays) (hd : d < L.temps) (hfits : Fits p s.pc (L.idxCode a d)) :
    ∃ s', Reaches p L d L.idxLen (L.arrAddr a s.acc) s s' ∧
      s'.mem d = L.arrAddr a s.acc := by
  have hq : 1 ≤ L.arrays.length := by
    have := List.idxOf_lt_length_of_mem ha; omega
  rw [show L.idxCode a d = [Instr.store d] ++
        (List.replicate (L.arrays.length - 1) (Instr.add (.mem d)) ++
          ([Instr.add (.lit (L.arrBase a))] ++ [Instr.store d])) from rfl,
      fits_append, fits_append, fits_append] at hfits
  obtain ⟨hf₁, hf₂, hf₃, hf₄⟩ := hfits
  -- store the index into the temporary
  set s₁ : State := { s with pc := s.pc + 1, mem := setCell s.mem d s.acc } with hs₁
  have h₁ : Reaches p L d 1 s.acc s s₁ :=
    reaches_one (fits_singleton.mp hf₁) rfl rfl rfl rfl rfl
      (fun i hi => setCell_of_ne _ _ (by omega))
  -- add it to itself `q - 1` times
  obtain ⟨s₂, h₂, hmem₂⟩ := reaches_adds (L := L) (L.arrays.length - 1) (s := s₁)
    (by simpa [hs₁] using hf₂)
  have hacc₂ : s₁.acc + (L.arrays.length - 1) * s₁.mem d = L.arrays.length * s.acc := by
    have : s₁.mem d = s.acc := setCell_self _ _ _
    have h2 : s₁.acc = s.acc := rfl
    obtain ⟨n, hn⟩ : ∃ n, L.arrays.length = n + 1 := ⟨L.arrays.length - 1, by omega⟩
    rw [this, h2, hn, Nat.add_sub_cancel]
    ring
  rw [hacc₂] at h₂
  -- add the base address
  have hf₃' : p[s₂.pc]? = some (Instr.add (.lit (L.arrBase a))) := by
    rw [h₂.pc, h₁.pc]; exact fits_singleton.mp (by simpa [hs₁] using hf₃)
  set s₃ : State := { s₂ with pc := s₂.pc + 1, acc := s₂.acc + L.arrBase a } with hs₃
  have h₃ : Reaches p L d 1 (L.arrAddr a s.acc) s₂ s₃ :=
    reaches_one hf₃' rfl rfl (by simp [hs₃, h₂.acc, Layout.arrAddr]; omega) rfl rfl
      (fun i _ => rfl)
  -- store the address into the temporary
  have hf₄' : p[s₃.pc]? = some (Instr.store d) := by
    rw [show s₃.pc = s.pc + 1 + (L.arrays.length - 1) + 1 by
          rw [hs₃, h₂.pc, h₁.pc]]
    exact fits_singleton.mp (by simpa [hs₁, Nat.add_assoc] using hf₄)
  set s₄ : State := { s₃ with pc := s₃.pc + 1, mem := setCell s₃.mem d s₃.acc } with hs₄
  have h₄ : Reaches p L d 1 (L.arrAddr a s.acc) s₃ s₄ :=
    reaches_one hf₄' rfl rfl h₃.acc rfl rfl (fun i hi => setCell_of_ne _ _ (by omega))
  refine ⟨s₄, ((h₁.trans h₂ (le_refl d)).trans (h₃.trans h₄ (le_refl d)) (le_refl d)).congr ?_,
    ?_⟩
  · simp [Layout.idxLen]; omega
  · rw [hs₄]; simpa using h₃.acc

/-- Compiled expressions: the code evaluates `e` into the accumulator,
falls through, leaves the tapes alone, and writes only to temporaries
from `d` upwards. -/
theorem compileExpr_correct {L : Layout} {σ : Env} {p : Program} (e : Expr) :
    ∀ (d v : ℕ) (s : State), Expr.Ok L e d → e.eval σ = some v →
      Represents L σ s → Fits p s.pc (compileExpr L e d) →
      ∃ s', Reaches p L d (esize L e) v s s' := by
  induction e with
  | lit n =>
      intro d v s _ hv _ hfits
      simp only [Expr.eval, Option.some.injEq] at hv
      subst hv
      exact ⟨_, reaches_one (fits_singleton.mp hfits) rfl rfl rfl rfl rfl (fun i _ => rfl)⟩
  | var x =>
      intro d v s hok hv hrep hfits
      simp only [Expr.eval, Option.some.injEq] at hv
      refine ⟨_, reaches_one (fits_singleton.mp hfits) rfl rfl ?_ rfl rfl (fun i _ => rfl)⟩
      show s.mem (L.varAddr x) = v
      rw [hrep.vars x hok]; exact hv
  | get a i ih =>
      intro d v s hok hv hrep hfits
      obtain ⟨ha, hoki, hd⟩ := hok
      simp only [Expr.eval, Option.bind_eq_some_iff] at hv
      obtain ⟨k, hk, hget⟩ := hv
      rw [List.getElem?_eq_some_iff] at hget
      obtain ⟨hklt, hkv⟩ := hget
      rw [show compileExpr L (.get a i) d
            = compileExpr L i d ++ (L.idxCode a d ++ [Instr.load (.ind d)]) from by
          simp [compileExpr, List.append_assoc],
          fits_append, fits_append] at hfits
      obtain ⟨hf₁, hf₂, hf₃⟩ := hfits
      obtain ⟨s₁, h₁⟩ := ih d k s hoki hk hrep hf₁
      obtain ⟨s₂, h₂, hmem₂⟩ := reaches_idxCode ha hd (by rw [h₁.pc]; simpa using hf₂)
      rw [h₁.acc] at h₂ hmem₂
      have hf₃' : p[s₂.pc]? = some (Instr.load (.ind d)) := by
        rw [h₂.pc, h₁.pc]
        exact fits_singleton.mp (by simpa [Nat.add_assoc] using hf₃)
      refine ⟨_, ((h₁.trans h₂ (le_refl d)).trans
        (reaches_one (L := L) (d := d) hf₃' rfl rfl ?_ rfl rfl (fun i _ => rfl))
        (le_refl d)).congr (by simp [esize])⟩
      show s₂.mem (s₂.mem d) = v
      rw [hmem₂, h₂.frame _ (Or.inr (le_trans (Nat.le_add_right _ _) (le_arrAddr L a k))),
        h₁.frame _ (Or.inr (le_trans (Nat.le_add_right _ _) (le_arrAddr L a k))),
        hrep.arrs a ha k hklt]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hklt, hkv]
  | add e f ihe ihf =>
      intro d v s hok hv hrep hfits
      obtain ⟨hokf, hoke, hd⟩ := hok
      simp only [Expr.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hv
      obtain ⟨m, hm, n, hn, rfl⟩ := hv
      rw [show compileExpr L (.add e f) d
            = compileExpr L f d ++ ([Instr.store d] ++
                (compileExpr L e (d + 1) ++ [Instr.add (.mem d)])) from by
          simp [compileExpr, List.append_assoc],
          fits_append, fits_append, fits_append] at hfits
      obtain ⟨hf₁, hf₂, hf₃, hf₄⟩ := hfits
      obtain ⟨s₁, h₁⟩ := ihf d n s hokf hn hrep hf₁
      set s₂ : State := { s₁ with pc := s₁.pc + 1, mem := setCell s₁.mem d s₁.acc } with hs₂
      have h₂ : Reaches p L d 1 n s₁ s₂ :=
        reaches_one (fits_singleton.mp (by rw [h₁.pc]; simpa using hf₂)) rfl rfl h₁.acc rfl rfl
          (fun i hi => setCell_of_ne _ _ (by omega))
      have hmemd : s₂.mem d = n := by rw [hs₂]; simpa using h₁.acc
      obtain ⟨s₃, h₃⟩ := ihe (d + 1) m s₂ hoke hm ((hrep.reaches h₁).reaches h₂)
        (by rw [h₂.pc, h₁.pc]; simpa [Nat.add_assoc] using hf₃)
      have hf₄' : p[s₃.pc]? = some (Instr.add (.mem d)) := by
        rw [h₃.pc, h₂.pc, h₁.pc]
        exact fits_singleton.mp (by simpa [Nat.add_assoc] using hf₄)
      refine ⟨_, (((h₁.trans h₂ (le_refl d)).trans h₃ (by omega)).trans
        (reaches_one (L := L) (d := d) hf₄' rfl rfl ?_ rfl rfl (fun i _ => rfl))
        (le_refl d)).congr (by simp [esize])⟩
      show s₃.acc + s₃.mem d = m + n
      rw [h₃.acc, h₃.frame d (Or.inl (by omega)), hmemd]
  | sub e f ihe ihf =>
      intro d v s hok hv hrep hfits
      obtain ⟨hokf, hoke, hd⟩ := hok
      simp only [Expr.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hv
      obtain ⟨m, hm, n, hn, rfl⟩ := hv
      rw [show compileExpr L (.sub e f) d
            = compileExpr L f d ++ ([Instr.store d] ++
                (compileExpr L e (d + 1) ++ [Instr.sub (.mem d)])) from by
          simp [compileExpr, List.append_assoc],
          fits_append, fits_append, fits_append] at hfits
      obtain ⟨hf₁, hf₂, hf₃, hf₄⟩ := hfits
      obtain ⟨s₁, h₁⟩ := ihf d n s hokf hn hrep hf₁
      set s₂ : State := { s₁ with pc := s₁.pc + 1, mem := setCell s₁.mem d s₁.acc } with hs₂
      have h₂ : Reaches p L d 1 n s₁ s₂ :=
        reaches_one (fits_singleton.mp (by rw [h₁.pc]; simpa using hf₂)) rfl rfl h₁.acc rfl rfl
          (fun i hi => setCell_of_ne _ _ (by omega))
      have hmemd : s₂.mem d = n := by rw [hs₂]; simpa using h₁.acc
      obtain ⟨s₃, h₃⟩ := ihe (d + 1) m s₂ hoke hm ((hrep.reaches h₁).reaches h₂)
        (by rw [h₂.pc, h₁.pc]; simpa [Nat.add_assoc] using hf₃)
      have hf₄' : p[s₃.pc]? = some (Instr.sub (.mem d)) := by
        rw [h₃.pc, h₂.pc, h₁.pc]
        exact fits_singleton.mp (by simpa [Nat.add_assoc] using hf₄)
      refine ⟨_, (((h₁.trans h₂ (le_refl d)).trans h₃ (by omega)).trans
        (reaches_one (L := L) (d := d) hf₄' rfl rfl ?_ rfl rfl (fun i _ => rfl))
        (le_refl d)).congr (by simp [esize])⟩
      show s₃.acc - s₃.mem d = m - n
      rw [h₃.acc, h₃.frame d (Or.inl (by omega)), hmemd]

/-- A condition evaluates to zero exactly when it holds, because that
is what `condExpr` computes. -/
theorem condExpr_eval {b : Cond} {σ : Env} {r : Bool} (h : b.eval σ = some r) :
    ∃ v, (condExpr b).eval σ = some v ∧ (v = 0 ↔ r = true) := by
  cases b with
  | eq e f =>
      simp only [Cond.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨m, hm, n, hn, rfl⟩ := h
      refine ⟨(m - n) + (n - m), by simp [condExpr, Expr.eval, hm, hn], ?_⟩
      simp only [beq_iff_eq]
      omega
  | lt e f =>
      simp only [Cond.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨m, hm, n, hn, rfl⟩ := h
      refine ⟨1 - (n - m), by simp [condExpr, Expr.eval, hm, hn], ?_⟩
      simp only [decide_eq_true_eq]
      omega

/-- Compiled conditions: the code leaves the accumulator zero exactly
when the condition holds. -/
theorem compileCond_correct {L : Layout} {σ : Env} {p : Program} {b : Cond} {d : ℕ}
    {r : Bool} {s : State} (hok : Cond.Ok L b d) (hv : b.eval σ = some r)
    (hrep : Represents L σ s) (hfits : Fits p s.pc (compileCond L b d)) :
    ∃ (s' : State) (v : ℕ), Reaches p L d (bsize L b) v s s' ∧ (v = 0 ↔ r = true) := by
  obtain ⟨v, hev, hiff⟩ := condExpr_eval hv
  obtain ⟨s', hr⟩ := compileExpr_correct (condExpr b) d v s hok hev hrep hfits
  exact ⟨s', v, hr, hiff⟩

/-! ### The constant

Every construct of IMP+ costs at least one, and compiles to at most a
fixed number of instructions per unit of that cost. The fixed number
depends on the layout only through the cost of one array access, which
is where the number of arrays enters; it does not depend on the program
and it does not depend on the input. Nothing here is tight. -/

theorem esize_le_size (L : Layout) (e : Expr) : esize L e ≤ (L.idxLen + 2) * e.size := by
  induction e with
  | lit n => simp [esize, Expr.size]
  | var x => simp [esize, Expr.size]
  | get a i ih =>
      simp only [esize, Expr.size, Nat.mul_add, Nat.mul_one]
      omega
  | add e f ihe ihf =>
      simp only [esize, Expr.size, Nat.mul_add, Nat.mul_one]
      omega
  | sub e f ihe ihf =>
      simp only [esize, Expr.size, Nat.mul_add, Nat.mul_one]
      omega

theorem esize_le (L : Layout) (e : Expr) : esize L e ≤ L.const * e.size :=
  le_trans (esize_le_size L e)
    (Nat.mul_le_mul_right _ (by simp only [Layout.const]; omega))

theorem bsize_le (L : Layout) (b : Cond) : bsize L b ≤ L.const * b.size := by
  have hd : 2 * (L.idxLen + 2) + 6 ≤ L.const := by simp only [Layout.const]; omega
  cases b with
  | eq e f =>
      have he := esize_le_size L e
      have hf := esize_le_size L f
      have h1 : 2 * ((L.idxLen + 2) * e.size) ≤ L.const * e.size := by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
      have h2 : 2 * ((L.idxLen + 2) * f.size) ≤ L.const * f.size := by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
      simp only [bsize, condExpr, esize, Cond.size, Nat.mul_add, Nat.mul_one]
      omega
  | lt e f =>
      have he := esize_le_size L e
      have hf := esize_le_size L f
      have h1 : (L.idxLen + 2) * e.size ≤ L.const * e.size :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : (L.idxLen + 2) * f.size ≤ L.const * f.size :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [bsize, condExpr, esize, Cond.size, Nat.mul_add, Nat.mul_one]
      omega

theorem idxLen_le_const (L : Layout) : L.idxLen + 1 ≤ L.const := by
  simp only [Layout.const, Layout.idxLen]; omega

theorem one_le_const (L : Layout) : 1 ≤ L.const := by simp only [Layout.const]; omega

theorem two_le_const (L : Layout) : 2 ≤ L.const := by simp only [Layout.const]; omega

/-! ### Jumps -/

theorem run_jump {p : Program} {s : State} {l : ℕ} (h : p[s.pc]? = some (Instr.jump l)) :
    run p 1 s = some { s with pc := l } := by rw [run_one h]; rfl

theorem run_jzero {p : Program} {s : State} {l : ℕ} (h : p[s.pc]? = some (Instr.jzero l)) :
    run p 1 s = some { s with pc := if s.acc = 0 then l else s.pc + 1 } := by
  rw [run_one h]; rfl

/-! ### The simulation theorem -/

/-- A terminating IMP+ run is matched by a run of the compiled code:
from any machine state representing the initial environment, with the
code laid out at the program counter, the machine reaches the
instruction just past the code in at most `L.const` steps per unit of
IMP+ cost, in a state representing the final environment. -/
theorem compile_correct {L : Layout} {p : Program} {c : Com} {σ σ' : Env} {k : ℕ}
    (hbs : BigStep c σ σ' k) :
    Com.Ok L c → ∀ (a : ℕ) (s : State), s.pc = a → Represents L σ s →
      Fits p a (compile L c a) →
      ∃ (t : ℕ) (s' : State), t ≤ L.const * k ∧ run p t s = some s' ∧
        s'.pc = a + size L c ∧ Represents L σ' s' := by
  induction hbs with
  | @skip σ =>
      intro _ a s hpc hrep _
      exact ⟨0, s, by simp, rfl, by simp [size, hpc], hrep⟩
  | @assign σ x e v hev =>
      intro hok a s hpc hrep hfits
      obtain ⟨hx, hoke⟩ := hok
      rw [show compile L (.assign x e) a = compileExpr L e 0 ++ [Instr.store (L.varAddr x)]
            from rfl, fits_append] at hfits
      obtain ⟨hf₁, hf₂⟩ := hfits
      obtain ⟨s₁, h₁⟩ := compileExpr_correct e 0 v s hoke hev hrep (hf₁.congr hpc.symm)
      obtain ⟨t₁, ht₁, hr₁⟩ := h₁.steps
      have hf₂' : p[s₁.pc]? = some (Instr.store (L.varAddr x)) := by
        rw [h₁.pc, hpc]; exact fits_singleton.mp (by simpa using hf₂)
      refine ⟨t₁ + 1, _, ?_, run_trans hr₁ (run_one hf₂'), ?_, ?_⟩
      · simp only [Nat.mul_add, Nat.mul_one]
        have := esize_le L e
        have := one_le_const L
        omega
      · show s₁.pc + 1 = a + size L (.assign x e)
        rw [h₁.pc, hpc]; simp [size]; omega
      · refine ⟨fun y hy => ?_, fun b hb i hi => ?_, ?_, ?_⟩
        · show setCell s₁.mem (L.varAddr x) s₁.acc (L.varAddr y) = _
          by_cases hxy : y = x
          · subst hxy
            rw [setCell_self, h₁.acc]
            simp [Env.setVar]
          · rw [setCell_of_ne _ _ (fun hc => hxy (varAddr_inj L hy hx hc)),
              h₁.frame _ (Or.inr (temps_le_varAddr L y)), hrep.vars y hy]
            simp [Env.setVar, hxy]
        · show setCell s₁.mem (L.varAddr x) s₁.acc (L.arrAddr b i) = _
          rw [setCell_of_ne _ _ (fun hc => varAddr_ne_arrAddr L hx i hc.symm),
            h₁.frame _ (Or.inr (le_trans (Nat.le_add_right _ _) (le_arrAddr L b i)))]
          exact hrep.arrs b hb i hi
        · show s₁.inp = _; rw [h₁.inp]; exact hrep.inp
        · show s₁.out = _; rw [h₁.out]; exact hrep.out
  | @seq c d σ σ₁ σ₂ k k' _ _ ih ih' =>
      intro hok a s hpc hrep hfits
      obtain ⟨hokc, hokd⟩ := hok
      rw [show compile L (.seq c d) a = compile L c a ++ compile L d (a + size L c) from rfl,
        fits_append] at hfits
      obtain ⟨hf₁, hf₂⟩ := hfits
      obtain ⟨t₁, s₁, ht₁, hr₁, hpc₁, hrep₁⟩ := ih hokc a s hpc hrep hf₁
      obtain ⟨t₂, s₂, ht₂, hr₂, hpc₂, hrep₂⟩ :=
        ih' hokd (a + size L c) s₁ hpc₁ hrep₁ (by simpa using hf₂)
      refine ⟨t₁ + t₂, s₂, ?_, run_trans hr₁ hr₂, ?_, hrep₂⟩
      · simp only [Nat.mul_add]; omega
      · rw [hpc₂]; simp [size]; omega
  | @read σ x v rest hinp =>
      intro hok a s hpc hrep hfits
      have hs : s.inp = v :: rest := by rw [hrep.inp]; exact hinp
      have hf : p[s.pc]? = some (Instr.read (L.varAddr x)) :=
        fits_singleton.mp (by rw [hpc]; simpa using hfits)
      refine ⟨1, _, ?_, by rw [run_one hf, effect_read _ hs], ?_, ?_⟩
      · simp only [Nat.mul_one]; exact one_le_const L
      · show s.pc + 1 = a + size L (.read x); rw [hpc]; simp [size]
      · refine ⟨fun y hy => ?_, fun b hb i hi => ?_, rfl, ?_⟩
        · show setCell s.mem (L.varAddr x) v (L.varAddr y) = _
          by_cases hxy : y = x
          · subst hxy; rw [setCell_self]; simp [Env.setVar]
          · rw [setCell_of_ne _ _ (fun hc => hxy (varAddr_inj L hy hok hc)), hrep.vars y hy]
            simp [Env.setVar, hxy]
        · show setCell s.mem (L.varAddr x) v (L.arrAddr b i) = _
          rw [setCell_of_ne _ _ (fun hc => varAddr_ne_arrAddr L hok i hc.symm)]
          exact hrep.arrs b hb i hi
        · show s.out = _; exact hrep.out
  | @write σ e v hev =>
      intro hok a s hpc hrep hfits
      obtain ⟨hoke, htemps⟩ := hok
      rw [show compile L (.write e) a
            = compileExpr L e 0 ++ ([Instr.store 0] ++ [Instr.write (.mem 0)]) from by
          simp [compile], fits_append, fits_append] at hfits
      obtain ⟨hf₁, hf₂, hf₃⟩ := hfits
      obtain ⟨s₁, h₁⟩ := compileExpr_correct e 0 v s hoke hev hrep (hf₁.congr hpc.symm)
      obtain ⟨t₁, ht₁, hr₁⟩ := h₁.steps
      have hf₂' : p[s₁.pc]? = some (Instr.store 0) := by
        rw [h₁.pc, hpc]; exact fits_singleton.mp (by simpa using hf₂)
      set s₂ : State := { s₁ with pc := s₁.pc + 1, mem := setCell s₁.mem 0 s₁.acc } with hs₂
      have hf₃' : p[s₂.pc]? = some (Instr.write (.mem 0)) := by
        show p[s₁.pc + 1]? = _
        rw [h₁.pc, hpc]; exact fits_singleton.mp (by simpa [Nat.add_assoc] using hf₃)
      refine ⟨t₁ + 1 + 1, _, ?_, run_trans (run_trans hr₁ (run_one hf₂')) (run_one hf₃'), ?_, ?_⟩
      · simp only [Nat.mul_add, Nat.mul_one]
        have := esize_le L e
        have := two_le_const L
        omega
      · show s₁.pc + 1 + 1 = a + size L (.write e)
        rw [h₁.pc, hpc]; simp [size]; omega
      · refine ⟨fun y hy => ?_, fun b hb i hi => ?_, ?_, ?_⟩
        · show setCell s₁.mem 0 s₁.acc (L.varAddr y) = _
          rw [setCell_of_ne _ _ (by have := temps_le_varAddr L y; omega),
            h₁.frame _ (Or.inr (temps_le_varAddr L y))]
          exact hrep.vars y hy
        · show setCell s₁.mem 0 s₁.acc (L.arrAddr b i) = _
          have hle := le_trans (Nat.le_add_right L.temps L.scalars.length) (le_arrAddr L b i)
          rw [setCell_of_ne _ _ (by omega), h₁.frame _ (Or.inr hle)]
          exact hrep.arrs b hb i hi
        · show s₁.inp = _; rw [h₁.inp]; exact hrep.inp
        · show s₁.out ++ [setCell s₁.mem 0 s₁.acc 0] = _
          rw [setCell_self, h₁.acc, h₁.out, hrep.out]
  | @store σ arr i e kk v hi hev hk =>
      intro hok a s hpc hrep hfits
      obtain ⟨ha, hoki, hoke, htemps⟩ := hok
      rw [show compile L (.store arr i e) a
            = compileExpr L i 0 ++ (L.idxCode arr 0 ++
                (compileExpr L e 1 ++ [Instr.storeInd 0])) from by
          simp [compile, List.append_assoc], fits_append, fits_append, fits_append] at hfits
      obtain ⟨hf₁, hf₂, hf₃, hf₄⟩ := hfits
      obtain ⟨s₁, h₁⟩ := compileExpr_correct i 0 kk s hoki hi hrep (hf₁.congr hpc.symm)
      obtain ⟨s₂, h₂, hmem₂⟩ := reaches_idxCode ha htemps
        (by rw [h₁.pc, hpc]; simpa using hf₂)
      rw [h₁.acc] at h₂ hmem₂
      obtain ⟨s₃, h₃⟩ := compileExpr_correct e 1 v s₂ hoke hev
        ((hrep.reaches h₁).reaches h₂) (by rw [h₂.pc, h₁.pc, hpc]; simpa [Nat.add_assoc] using hf₃)
      have hmem₃ : s₃.mem 0 = L.arrAddr arr kk := by
        rw [h₃.frame 0 (Or.inl (by omega))]; exact hmem₂
      have hf₄' : p[s₃.pc]? = some (Instr.storeInd 0) := by
        rw [h₃.pc, h₂.pc, h₁.pc, hpc]
        exact fits_singleton.mp (by simpa [Nat.add_assoc] using hf₄)
      obtain ⟨t₁, ht₁, hr₁⟩ := (h₁.trans h₂ (le_refl 0)).trans h₃ (by omega) |>.steps
      refine ⟨t₁ + 1, _, ?_, run_trans hr₁ (run_one hf₄'), ?_, ?_⟩
      · simp only [Nat.mul_add, Nat.mul_one]
        have := esize_le L i
        have := esize_le L e
        have := idxLen_le_const L
        omega
      · show s₃.pc + 1 = a + size L (.store arr i e)
        rw [h₃.pc, h₂.pc, h₁.pc, hpc]; simp [size]; omega
      · have hlen : ((σ.arrs arr).set kk v).length = (σ.arrs arr).length := by simp
        refine ⟨fun y hy => ?_, fun b hb j hj => ?_, ?_, ?_⟩
        · show setCell s₃.mem (s₃.mem 0) s₃.acc (L.varAddr y) = _
          rw [hmem₃, setCell_of_ne _ _ (fun hc => varAddr_ne_arrAddr L hy kk hc),
            h₃.frame _ (Or.inr (temps_le_varAddr L y)),
            h₂.frame _ (Or.inr (temps_le_varAddr L y)),
            h₁.frame _ (Or.inr (temps_le_varAddr L y))]
          exact hrep.vars y hy
        · show setCell s₃.mem (s₃.mem 0) s₃.acc (L.arrAddr b j) = _
          have hle := le_trans (Nat.le_add_right L.temps L.scalars.length) (le_arrAddr L b j)
          have hjlen : j < (σ.arrs b).length := by
            by_cases hb' : b = arr
            · subst hb'; simpa [Env.setArr] using hj
            · simpa [Env.setArr, hb'] using hj
          rw [hmem₃]
          by_cases hcase : b = arr ∧ j = kk
          · obtain ⟨rfl, rfl⟩ := hcase
            rw [setCell_self, h₃.acc]
            simp [Env.setArr, List.getD_eq_getElem?_getD, hk]
          · have hne : L.arrAddr b j ≠ L.arrAddr arr kk := fun hc => by
              obtain ⟨rfl, rfl⟩ := arrAddr_inj L hb ha hc
              exact hcase ⟨rfl, rfl⟩
            rw [setCell_of_ne _ _ hne, h₃.frame _ (Or.inr hle), h₂.frame _ (Or.inr hle),
              h₁.frame _ (Or.inr hle)]
            rw [hrep.arrs b hb j hjlen]
            by_cases hb' : b = arr
            · subst hb'
              have hjk : j ≠ kk := fun hc => hcase ⟨rfl, hc⟩
              simp [Env.setArr, List.getD_eq_getElem?_getD, Ne.symm hjk]
            · simp [Env.setArr, hb']
        · show s₃.inp = _
          rw [h₃.inp, h₂.inp, h₁.inp]; exact hrep.inp
        · show s₃.out = _
          rw [h₃.out, h₂.out, h₁.out]; exact hrep.out
  | @ite_true b c d σ σ' k hb _ ih =>
      intro hok a s hpc hrep hfits
      obtain ⟨hokb, hokc, hokd⟩ := hok
      rw [show compile L (.ite b c d) a
            = compileCond L b 0 ++ ([Instr.jzero (a + bsize L b + 1 + size L d + 1)] ++
                (compile L d (a + bsize L b + 1) ++
                  ([Instr.jump (a + bsize L b + 1 + size L d + 1 + size L c)] ++
                    compile L c (a + bsize L b + 1 + size L d + 1)))) from by
          simp [compile, List.append_assoc],
        fits_append, fits_append, fits_append, fits_append] at hfits
      obtain ⟨hf₁, hf₂, hf₃, hf₄, hf₅⟩ := hfits
      obtain ⟨s₁, v, h₁, hv⟩ := compileCond_correct hokb hb hrep (hf₁.congr hpc.symm)
      obtain ⟨t₁, ht₁, hr₁⟩ := h₁.steps
      have hzero : s₁.acc = 0 := by rw [h₁.acc]; exact hv.mpr rfl
      have hf₂' : p[s₁.pc]? = some (Instr.jzero (a + bsize L b + 1 + size L d + 1)) := by
        rw [h₁.pc, hpc]; exact fits_singleton.mp (by simpa using hf₂)
      have hjz : run p 1 s₁ = some { s₁ with pc := a + bsize L b + 1 + size L d + 1 } := by
        rw [run_jzero hf₂', hzero]; simp
      obtain ⟨t₂, s₂, ht₂, hr₂, hpc₂, hrep₂⟩ :=
        ih hokc (a + bsize L b + 1 + size L d + 1)
          { s₁ with pc := a + bsize L b + 1 + size L d + 1 } rfl ((hrep.reaches h₁).setPc _)
          (by simpa [Nat.add_assoc] using hf₅)
      refine ⟨t₁ + 1 + t₂, s₂, ?_, run_trans (run_trans hr₁ hjz) hr₂, ?_, hrep₂⟩
      · simp only [Nat.mul_add, Nat.mul_one]
        have := bsize_le L b
        have := one_le_const L
        omega
      · rw [hpc₂]; simp [size]; omega
  | @ite_false b c d σ σ' k hb _ ih =>
      intro hok a s hpc hrep hfits
      obtain ⟨hokb, hokc, hokd⟩ := hok
      rw [show compile L (.ite b c d) a
            = compileCond L b 0 ++ ([Instr.jzero (a + bsize L b + 1 + size L d + 1)] ++
                (compile L d (a + bsize L b + 1) ++
                  ([Instr.jump (a + bsize L b + 1 + size L d + 1 + size L c)] ++
                    compile L c (a + bsize L b + 1 + size L d + 1)))) from by
          simp [compile, List.append_assoc],
        fits_append, fits_append, fits_append, fits_append] at hfits
      obtain ⟨hf₁, hf₂, hf₃, hf₄, hf₅⟩ := hfits
      obtain ⟨s₁, v, h₁, hv⟩ := compileCond_correct hokb hb hrep (hf₁.congr hpc.symm)
      obtain ⟨t₁, ht₁, hr₁⟩ := h₁.steps
      have hne : s₁.acc ≠ 0 := by
        rw [h₁.acc]; intro hc; exact absurd (hv.mp hc) (by simp)
      have hf₂' : p[s₁.pc]? = some (Instr.jzero (a + bsize L b + 1 + size L d + 1)) := by
        rw [h₁.pc, hpc]; exact fits_singleton.mp (by simpa using hf₂)
      have hjz : run p 1 s₁ = some { s₁ with pc := a + bsize L b + 1 } := by
        rw [run_jzero hf₂']
        have : s₁.pc + 1 = a + bsize L b + 1 := by rw [h₁.pc, hpc]
        simp [hne, this]
      obtain ⟨t₂, s₂, ht₂, hr₂, hpc₂, hrep₂⟩ :=
        ih hokd (a + bsize L b + 1) { s₁ with pc := a + bsize L b + 1 } rfl ((hrep.reaches h₁).setPc _)
          (by simpa [Nat.add_assoc] using hf₃)
      have hf₄' : p[s₂.pc]? =
          some (Instr.jump (a + bsize L b + 1 + size L d + 1 + size L c)) := by
        rw [hpc₂]; exact fits_singleton.mp (by simpa [Nat.add_assoc] using hf₄)
      refine ⟨t₁ + 1 + t₂ + 1, _, ?_,
        run_trans (run_trans (run_trans hr₁ hjz) hr₂) (run_jump hf₄'), ?_, ?_⟩
      · simp only [Nat.mul_add, Nat.mul_one]
        have := bsize_le L b
        have := two_le_const L
        omega
      · show a + bsize L b + 1 + size L d + 1 + size L c = a + size L (.ite b c d)
        simp [size]; omega
      · exact hrep₂.setPc _
  | @while_true b c σ σ₁ σ₂ k k' hb _ _ ih ih' =>
      intro hok a s hpc hrep hfits
      obtain ⟨hokb, hokc⟩ := hok
      have hcode : compile L (.while b c) a
          = compileCond L b 0 ++ ([Instr.jzero (a + bsize L b + 2)] ++
              ([Instr.jump (a + bsize L b + 2 + size L c + 1)] ++
                (compile L c (a + bsize L b + 2) ++ [Instr.jump a]))) := by
        simp [compile, List.append_assoc]
      rw [hcode, fits_append, fits_append, fits_append, fits_append] at hfits
      obtain ⟨hf₁, hf₂, hf₃, hf₄, hf₅⟩ := hfits
      obtain ⟨s₁, v, h₁, hv⟩ := compileCond_correct hokb hb hrep (hf₁.congr hpc.symm)
      obtain ⟨t₁, ht₁, hr₁⟩ := h₁.steps
      have hzero : s₁.acc = 0 := by rw [h₁.acc]; exact hv.mpr rfl
      have hf₂' : p[s₁.pc]? = some (Instr.jzero (a + bsize L b + 2)) := by
        rw [h₁.pc, hpc]; exact fits_singleton.mp (by simpa using hf₂)
      have hjz : run p 1 s₁ = some { s₁ with pc := a + bsize L b + 2 } := by
        rw [run_jzero hf₂', hzero]; simp
      obtain ⟨t₂, s₂, ht₂, hr₂, hpc₂, hrep₂⟩ :=
        ih hokc (a + bsize L b + 2) { s₁ with pc := a + bsize L b + 2 } rfl ((hrep.reaches h₁).setPc _)
          (by simpa [Nat.add_assoc] using hf₄)
      have hf₅' : p[s₂.pc]? = some (Instr.jump a) := by
        rw [hpc₂]; exact fits_singleton.mp (by simpa [Nat.add_assoc] using hf₅)
      obtain ⟨t₃, s₃, ht₃, hr₃, hpc₃, hrep₃⟩ :=
        ih' (⟨hokb, hokc⟩ : Com.Ok L (.while b c)) a { s₂ with pc := a } rfl
          (hrep₂.setPc _) (by rw [hcode]; exact
          (fits_append.mpr ⟨hf₁, fits_append.mpr ⟨hf₂, fits_append.mpr ⟨hf₃,
            fits_append.mpr ⟨hf₄, hf₅⟩⟩⟩⟩))
      refine ⟨t₁ + 1 + t₂ + 1 + t₃, s₃, ?_,
        run_trans (run_trans (run_trans (run_trans hr₁ hjz) hr₂)
          (run_jump hf₅')) hr₃, hpc₃, hrep₃⟩
      simp only [Nat.mul_add, Nat.mul_one]
      have := bsize_le L b
      have := two_le_const L
      omega
  | @while_false b c σ hb =>
      intro hok a s hpc hrep hfits
      obtain ⟨hokb, hokc⟩ := hok
      rw [show compile L (.while b c) a
            = compileCond L b 0 ++ ([Instr.jzero (a + bsize L b + 2)] ++
                ([Instr.jump (a + bsize L b + 2 + size L c + 1)] ++
                  (compile L c (a + bsize L b + 2) ++ [Instr.jump a]))) from by
          simp [compile, List.append_assoc],
        fits_append, fits_append, fits_append, fits_append] at hfits
      obtain ⟨hf₁, hf₂, hf₃, hf₄, hf₅⟩ := hfits
      obtain ⟨s₁, v, h₁, hv⟩ := compileCond_correct hokb hb hrep (hf₁.congr hpc.symm)
      obtain ⟨t₁, ht₁, hr₁⟩ := h₁.steps
      have hne : s₁.acc ≠ 0 := by
        rw [h₁.acc]; intro hc; exact absurd (hv.mp hc) (by simp)
      have hf₂' : p[s₁.pc]? = some (Instr.jzero (a + bsize L b + 2)) := by
        rw [h₁.pc, hpc]; exact fits_singleton.mp (by simpa using hf₂)
      have hf₃' : p[s₁.pc + 1]? = some (Instr.jump (a + bsize L b + 2 + size L c + 1)) := by
        rw [h₁.pc, hpc]; exact fits_singleton.mp (by simpa [Nat.add_assoc] using hf₃)
      have hjz : run p 1 s₁ = some { s₁ with pc := s₁.pc + 1 } := by
        rw [run_jzero hf₂']; simp [hne]
      have hf₃'' : p[({ s₁ with pc := s₁.pc + 1 } : State).pc]? =
          some (Instr.jump (a + bsize L b + 2 + size L c + 1)) := hf₃'
      refine ⟨t₁ + 1 + 1, _, ?_,
        run_trans (run_trans hr₁ hjz) (run_jump hf₃''), ?_, ?_⟩
      · simp only [Nat.mul_add, Nat.mul_one]
        have := bsize_le L b
        have := two_le_const L
        omega
      · show a + bsize L b + 2 + size L c + 1 = a + size L (.while b c)
        simp [size]; omega
      · exact (hrep.reaches h₁).setPc _

/-! ### From an IMP+ derivation to a machine run

The two ends are joined here: the all-zero memory of a starting machine
represents the initial environment for *any* declared array lengths,
and the halt instruction after the code is what stops the machine. -/

/-- The starting machine state represents the starting environment, no
matter what lengths its arrays are declared with: unbounded zeroed
memory holds a zero-filled array of every length at once. -/
theorem represents_initState (L : Layout) (ext : String → ℕ) (x : List ℕ) :
    Represents L (initEnv ext x) (initState x) where
  vars _ _ := rfl
  arrs a _ i _ := by
    show (0 : ℕ) = (List.replicate (ext a) 0).getD i 0
    rw [List.getD_eq_getElem?_getD]
    rcases h : (List.replicate (ext a) 0)[i]? with _ | w
    · rfl
    · have := List.mem_of_getElem? h
      simp only [List.mem_replicate] at this
      rw [this.2]; rfl
  inp := rfl
  out := rfl

theorem fits_self (q r : Program) : Fits (q ++ r) 0 q := by
  intro i hi
  simpa using List.getElem?_append_left (l₂ := r) hi

/-- **The simulation theorem.** A terminating IMP+ run of `c` on the
input `x` is matched by a run of the compiled machine program on the
same input, halting with the same output, in at most `L.const` machine
steps per unit of the IMP+ cost. The constant depends on the layout
alone; the array lengths `ext` are the user's free choice and cost
nothing. -/
theorem compileProgram_runsTo {L : Layout} {c : Com} {ext : String → ℕ} {x : List ℕ}
    {σ' : Env} {k : ℕ} (hok : Com.Ok L c) (hbs : BigStep c (initEnv ext x) σ' k) :
    ∃ t ≤ L.const * k, RunsTo (compileProgram L c) x σ'.out t := by
  obtain ⟨t, s', ht, hr, hpc, hrep⟩ :=
    compile_correct hbs hok 0 (initState x) rfl (represents_initState L ext x)
      (fits_self _ _)
  refine ⟨t, ht, s', hr, ?_, by rw [← hrep.out]⟩
  have hhalt : (compileProgram L c)[s'.pc]? = some Instr.halt := by
    rw [hpc, compileProgram]
    rw [List.getElem?_append_right (by simp)]
    simp
  rw [step_eq, hhalt]
  rfl

end Lax11Proofs.Simulation
