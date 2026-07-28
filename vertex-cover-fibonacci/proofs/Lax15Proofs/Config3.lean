import Lax15Proofs.Config

/-!
The configuration side of the second rung: the same search stack, a
sharper branching rule, and the potential that pays for it.

Nothing about the configuration itself changes. Frames, the trail, the
marking, frame health, the stored alternatives and the invariant `J`
are `Config.lean`'s, imported and reused verbatim: a branch that takes
a vertex of residual degree at least *three* also has residual degree
at least two, so rung A's health clause is satisfied on the nose. What
changes is the arithmetic. The first rung branched at degree two, so a
push split a budget `b` into `b − 1` and `b − 2` and the recursion was
Fibonacci's. This rung branches at degree three, so a push splits `b`
into `b − 1` and `b − 3`, and the leaf count obeys

    branchCount (b + 3) = branchCount (b + 2) + branchCount b,

the recurrence of the real root `β ≈ 1.4656` of `x³ = x² + 1`. The
potential is `fPot3 b = 4·branchCount b − 3`, so `fPot3 = 1, 5, 9, 13,
21, 33, …`; the `−3` and the two units of slack carried by a stored
phase-zero frame are load-bearing exactly as on the first rung, and for
the same reason: they make the push drop *exact*, including at the two
budgets where truncated subtraction bends the recurrence (`b = 1` and
`b = 2`, where the stored child is measured at budget `0`).

The one genuinely new piece is the extra invariant clause. The flip
gives back `b_i − d` where `d` is the residual degree branched on, and
the drop needs `d ≥ 3` — which is a fact about the push that created
the frame, not about the flip. So the invariant remembers it: `Sharp`
says every phase-zero frame on the stack branched at residual degree at
least three, and `J3` is `J` together with `Sharp`. Its preservation is
mechanical — the push creates the clause out of its own guard, the flip
turns phase zero into phase one and thereby discharges it, the pop
drops a frame, and the leaves do not touch the stack.

`branchCount` here is the proofs-side copy of the concept's definition,
written with the same equations so that the two are definitionally
interchangeable when the endgame's identity check runs.
-/

namespace Lax15Proofs.VC3

open Lax11Proofs.VC (Ok)
open Lax15Proofs.VC

variable {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}

/-! ### The branching recurrence -/

/-- Leaf count of the search tree that branches, at budget `b ≥ 3`,
into budgets `b − 1` and `b − 3`: the take-the-vertex child and the
take-its-three-plus-neighbours child. Grows as `β^k` for the real root
`β ≈ 1.4656` of `x³ = x² + 1`. The equations are the concept's,
verbatim. -/
def branchCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | (b + 3) => branchCount (b + 2) + branchCount b

@[simp] theorem branchCount_zero : branchCount 0 = 1 := by simp [branchCount]

@[simp] theorem branchCount_one : branchCount 1 = 2 := by simp [branchCount]

@[simp] theorem branchCount_two : branchCount 2 = 3 := by simp [branchCount]

/-- **The branching recurrence**: a budget of `b + 3` branches into
`b + 2` and `b`. -/
@[simp] theorem branchCount_add_three (b : ℕ) :
    branchCount (b + 3) = branchCount (b + 2) + branchCount b := by
  simp [branchCount]

theorem branchCount_pos : ∀ b, 0 < branchCount b
  | 0 => by simp
  | 1 => by simp
  | 2 => by simp
  | (b + 3) => by
    have := branchCount_pos (b + 2)
    rw [branchCount_add_three]
    omega

theorem branchCount_le_succ (b : ℕ) : branchCount b ≤ branchCount (b + 1) := by
  match b with
  | 0 => simp
  | 1 => simp
  | 2 =>
    rw [show (2 : ℕ) + 1 = 0 + 3 from by norm_num, branchCount_add_three]
    simp
  | (c + 3) =>
    rw [show c + 3 + 1 = (c + 1) + 3 from by omega, branchCount_add_three,
      branchCount_add_three]
    have := branchCount_pos (c + 1)
    have : branchCount (c + 1 + 2) = branchCount (c + 2) + branchCount c := by
      rw [show c + 1 + 2 = c + 3 from by omega, branchCount_add_three]
    omega

theorem branchCount_mono : Monotone branchCount :=
  monotone_nat_of_le_succ branchCount_le_succ

/-! ### The potential -/

/-- The pending work of one level of the search tree: `4·branchCount b
− 3`, so that `fPot3 0 = 1`, `fPot3 1 = 5`, `fPot3 2 = 9` and
`fPot3 (b+3) = fPot3 (b+2) + fPot3 b + 3` exactly. The `−3` is
load-bearing — it is what a push pays out of. -/
def fPot3 (b : ℕ) : ℕ := 4 * branchCount b - 3

theorem fPot3_zero : fPot3 0 = 1 := by norm_num [fPot3]

theorem fPot3_one : fPot3 1 = 5 := by norm_num [fPot3]

theorem fPot3_two : fPot3 2 = 9 := by norm_num [fPot3]

/-- **The rung-B recurrence**, exactly: a level splits into its two
children — one step down and three steps down — and three units of
slack. -/
theorem fPot3_add_three (b : ℕ) : fPot3 (b + 3) = fPot3 (b + 2) + fPot3 b + 3 := by
  have h1 := branchCount_pos (b + 2)
  have h2 := branchCount_pos b
  simp only [fPot3, branchCount_add_three]
  omega

theorem one_le_fPot3 (b : ℕ) : 1 ≤ fPot3 b := by
  have h := branchCount_pos b
  simp only [fPot3]
  omega

theorem fPot3_mono : Monotone fPot3 := by
  intro a b hab
  have h := branchCount_mono hab
  simp only [fPot3]
  omega

theorem fPot3_le_of_le {a b : ℕ} (h : a ≤ b) : fPot3 a ≤ fPot3 b := fPot3_mono h

/-- What a push pays: the level it splits covers the active child, the
stored child at three steps down, the frame's two units of slack and
the push itself. Exact at every budget — at `b = 1` the truncated
subtraction turns the recurrence into `5 = 1 + (1 + 2) + 1` and at
`b = 2` into `9 = 5 + (1 + 2) + 1`, which is why the `−3` cannot be
simplified away. -/
theorem fPot3_push {b : ℕ} (hb : 1 ≤ b) : fPot3 (b - 1) + fPot3 (b - 3) + 3 ≤ fPot3 b := by
  match b, hb with
  | 1, _ => simp [fPot3_zero, fPot3_one]
  | 2, _ => simp [fPot3_zero, fPot3_one, fPot3_two]
  | (c + 3), _ =>
    have h := fPot3_add_three c
    simp only [show c + 3 - 1 = c + 2 from by omega, show c + 3 - 3 = c from by omega]
    omega

/-- The push identity at the first truncation point: a budget of one
splits into an active child at budget zero and a stored child measured
at budget zero as well, plus the frame's slack and the push. -/
theorem fPot3_push_one : fPot3 0 + (fPot3 0 + 2) + 1 = fPot3 1 := by
  rw [fPot3_zero, fPot3_one]

/-- The push identity at the second truncation point. -/
theorem fPot3_push_two : fPot3 1 + (fPot3 0 + 2) + 1 = fPot3 2 := by
  rw [fPot3_zero, fPot3_one, fPot3_two]

/-- The pending work of the stack: a phase-zero frame holds a whole
child plus two units of slack, a phase-one frame one unit. The child is
measured at the budget the frame will have after paying for the second
branch, which is at least three — hence `b − 3`. -/
def stackPot3 : List (Frame n) → ℕ
  | [] => 0
  | f :: fs => (if f.phase then 1 else fPot3 (f.b - 3) + 2) + stackPot3 fs

@[simp] theorem stackPot3_nil : stackPot3 ([] : List (Frame n)) = 0 := rfl

theorem stackPot3_cons (f : Frame n) (fs : List (Frame n)) :
    stackPot3 (f :: fs) = (if f.phase then 1 else fPot3 (f.b - 3) + 2) + stackPot3 fs := rfl

/-- The pending work of a configuration: the active subtree while
descending, the stack, and one unit for not being done. -/
def pot3 (C : Config n) : ℕ :=
  (if C.mode = 0 then fPot3 C.bud else 0) + stackPot3 C.frames +
    (if C.mode = 2 then 0 else 1)

theorem pot3_init (k a : ℕ) : pot3 (⟨[], 0, k, a⟩ : Config n) = fPot3 k + 1 := by
  simp [pot3]

theorem pot3_init_le (k a : ℕ) :
    pot3 (⟨[], 0, k, a⟩ : Config n) ≤ 4 * branchCount k := by
  rw [pot3_init]
  have h := branchCount_pos k
  simp only [fPot3]
  omega

/-! ### The potential as the machine holds it -/

/-- The stack potential read off the stored budgets and phases alone —
the two stack arrays, and nothing else. -/
def stackPotN3 : List (ℕ × Bool) → ℕ
  | [] => 0
  | p :: ps => (if p.2 then 1 else fPot3 (p.1 - 3) + 2) + stackPotN3 ps

@[simp] theorem stackPotN3_nil : stackPotN3 [] = 0 := rfl

theorem stackPotN3_cons (p : ℕ × Bool) (ps : List (ℕ × Bool)) :
    stackPotN3 (p :: ps) = (if p.2 then 1 else fPot3 (p.1 - 3) + 2) + stackPotN3 ps := rfl

theorem stackPot3_eq_stackPotN3 (fs : List (Frame n)) :
    stackPot3 fs = stackPotN3 (fs.map (fun f => (f.b, f.phase))) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [stackPot3_cons, stackPotN3_cons, ih]

/-- The potential as a function of what the environment holds: the mode,
the budget, and the stack's budget–phase pairs. -/
def potN3 (mode bud : ℕ) (frs : List (ℕ × Bool)) : ℕ :=
  (if mode = 0 then fPot3 bud else 0) + stackPotN3 frs + (if mode = 2 then 0 else 1)

theorem pot3_eq_potN3 (C : Config n) :
    pot3 C = potN3 C.mode C.bud (C.frames.map (fun f => (f.b, f.phase))) := by
  simp [pot3, potN3, stackPot3_eq_stackPotN3]

/-! ### The invariant -/

/-- Stack sharpness: every phase-zero frame branched on a vertex of
residual degree at least three below it. This is what a push at the
sharper branching rule establishes and what the feasible flip consumes:
the flip gives back `b_i − d`, and the drop needs `d ≥ 3`, a fact about
the push that is no longer visible when the flip happens. -/
def Sharp (G : SimpleGraph (Fin n)) : List (Frame n) → Prop
  | [] => True
  | f :: fs => (f.phase = false → 3 ≤ resDeg G (marked fs) f.v) ∧ Sharp G fs

@[simp] theorem sharp_nil : Sharp G ([] : List (Frame n)) := trivial

theorem sharp_cons {f : Frame n} {fs : List (Frame n)} :
    Sharp G (f :: fs) ↔
      ((f.phase = false → 3 ≤ resDeg G (marked fs) f.v) ∧ Sharp G fs) := Iff.rfl

theorem Sharp.tail {f : Frame n} {fs : List (Frame n)} (h : Sharp G (f :: fs)) :
    Sharp G fs := h.2

theorem Sharp.head {f : Frame n} {fs : List (Frame n)} (h : Sharp G (f :: fs))
    (hph : f.phase = false) : 3 ≤ resDeg G (marked fs) f.v := h.1 hph

/-- The invariant of the second rung's outer loop: the first rung's
invariant, together with the record that every stored branch was taken
at residual degree at least three. -/
def J3 (G : SimpleGraph (Fin n)) (k : ℕ) (C : Config n) : Prop :=
  J G k C ∧ Sharp G C.frames

theorem J3.j {C : Config n} (hJ : J3 G k C) : J G k C := hJ.1

theorem J3.sharp {C : Config n} (hJ : J3 G k C) : Sharp G C.frames := hJ.2

/-- The search starts in descend mode with an empty stack and the full
budget; there is nothing on the stack to be sharp about. -/
theorem j3_init (G : SimpleGraph (Fin n)) (k : ℕ) : J3 G k ⟨[], 0, k, 0⟩ :=
  ⟨j_init G k, sharp_nil⟩

/-- At done, the answer is the concept's `if` — rung A's reading of the
answer, unchanged. -/
theorem ans3_eq {C : Config n} (hJ : J3 G k C) (hm : C.mode = 2) :
    C.ans = if G.vertexCoverNum ≤ (k : ℕ∞) then 1 else 0 := ans_eq hJ.j hm

/-! ### The eight transitions

Each takes the semantic fact the scan or the solver will have
certified — never a condition on slots — establishes the invariant for
the new configuration, and pays the loop rule one unit of potential.
The `J`-halves are rung A's, projected; the drops are fresh, and five
of them are exact (`T3` stuck, `T4` push, `T6` flip at `d = 3`, `T5`
exhausted, `T8` pop). -/

/-- **T1, the solver yes**: the solver has certified that the active
marking admits a cover within budget, so the answer is yes. -/
theorem step3_yes {C : Config n} (hJ : J3 G k C) (hm : C.mode = 0)
    (hok : Ok G (marked C.frames) C.bud) :
    J3 G k ⟨C.frames, 2, C.bud, 1⟩ ∧
      pot3 (⟨C.frames, 2, C.bud, 1⟩ : Config n) + 1 ≤ pot3 C := by
  refine ⟨⟨(step_yes hJ.j hm hok).1, hJ.sharp⟩, ?_⟩
  simp only [pot3, hm]
  norm_num

/-- **T2, the solver no**: the solver has certified that the active
marking is dead, so only the stored alternatives remain. -/
theorem step3_no {C : Config n} (hJ : J3 G k C) (hm : C.mode = 0)
    (hdead : ¬ Ok G (marked C.frames) C.bud) :
    J3 G k ⟨C.frames, 1, C.bud, C.ans⟩ ∧
      pot3 (⟨C.frames, 1, C.bud, C.ans⟩ : Config n) + 1 ≤ pot3 C := by
  obtain ⟨-, hh, -, hdesc, -, -⟩ := hJ.j
  refine ⟨⟨⟨by norm_num, hh, by simp, by simp, fun _ => ?_, by simp⟩, hJ.sharp⟩, ?_⟩
  · rw [hdesc hm]
    tauto
  · have := one_le_fPot3 C.bud
    simp only [pot3, hm]
    norm_num
    omega

/-- **T3, the budget no**: a residual edge is on the table and the
budget is spent, so the active marking is dead. -/
theorem step3_stuck {C : Config n} {u v : Fin n} (hJ : J3 G k C) (hm : C.mode = 0)
    (hb : C.bud = 0) (huv : G.Adj u v) (hu : u ∉ marked C.frames)
    (hv : v ∉ marked C.frames) :
    J3 G k ⟨C.frames, 1, C.bud, C.ans⟩ ∧
      pot3 (⟨C.frames, 1, C.bud, C.ans⟩ : Config n) + 1 ≤ pot3 C := by
  refine ⟨⟨(step_stuck hJ.j hm hb huv hu hv).1, hJ.sharp⟩, ?_⟩
  simp only [pot3, hm, hb, fPot3_zero]
  norm_num

/-- **T4, the push**: a vertex with *three* residual neighbours and
budget left. Rung A's branch lemma splits the active claim into the
branch that takes `v` and the branch that takes its residual
neighbourhood; the new frame records that the split was sharp. The drop
is the one unit the level's `−3` was holding — exact at every budget,
including the two where the stored child is measured at zero. -/
theorem step3_push {C : Config n} {v : Fin n} (hJ : J3 G k C) (hm : C.mode = 0)
    (hb : 1 ≤ C.bud) (hv : v ∉ marked C.frames)
    (hd : 3 ≤ resDeg G (marked C.frames) v) :
    J3 G k ⟨⟨v, C.bud, false, [v]⟩ :: C.frames, 0, C.bud - 1, C.ans⟩ ∧
      pot3 (⟨⟨v, C.bud, false, [v]⟩ :: C.frames, 0, C.bud - 1, C.ans⟩ : Config n) + 1 ≤
        pot3 C := by
  refine ⟨⟨(step_push hJ.j hm hb hv (by omega)).1, ⟨fun _ => hd, hJ.sharp⟩⟩, ?_⟩
  have hpush := fPot3_push hb
  simp only [pot3, hm, stackPot3_cons]
  norm_num
  omega

/-- **T5, the exhaustion**: backtracking with an empty stack. No
alternatives are left, so `Ok ∅ k` fails and the answer is no. The drop
is the not-done unit. -/
theorem step3_exhausted {C : Config n} (hJ : J3 G k C) (hm : C.mode = 1)
    (hfr : C.frames = []) :
    J3 G k ⟨C.frames, 2, C.bud, 0⟩ ∧
      pot3 (⟨C.frames, 2, C.bud, 0⟩ : Config n) + 1 ≤ pot3 C := by
  refine ⟨⟨(step_exhausted hJ.j hm hfr).1, hJ.sharp⟩, ?_⟩
  simp only [pot3, hm]
  norm_num

/-- **T6, the feasible flip**: the top frame's stored alternative fits
in its budget, so it becomes the active branch. The budget becomes the
frame's minus the residual degree, on the nose — and the residual
degree is at least three, which is exactly what `Sharp` remembers about
the push that created the frame. The drop is exact when the residual
degree is three. -/
theorem step3_flip {C : Config n} {f : Frame n} {fs : List (Frame n)} {l : List (Fin n)}
    (hJ : J3 G k C) (hm : C.mode = 1) (hfr : C.frames = f :: fs) (hph : f.phase = false)
    (hnd : l.Nodup) (hl : l.toFinset = ResNbhd G (marked fs) f.v)
    (hd : resDeg G (marked fs) f.v ≤ f.b) :
    J3 G k ⟨⟨f.v, f.b, true, l⟩ :: fs, 0, f.b - resDeg G (marked fs) f.v, C.ans⟩ ∧
      pot3 (⟨⟨f.v, f.b, true, l⟩ :: fs, 0, f.b - resDeg G (marked fs) f.v, C.ans⟩ :
          Config n) + 1 ≤ pot3 C := by
  have hs : Sharp G (f :: fs) := hfr ▸ hJ.sharp
  have hd3 : 3 ≤ resDeg G (marked fs) f.v := hs.head hph
  refine ⟨⟨(step_flip hJ.j hm hfr hph hnd hl hd).1, ⟨by simp, hs.tail⟩⟩, ?_⟩
  have hmono : fPot3 (f.b - resDeg G (marked fs) f.v) ≤ fPot3 (f.b - 3) :=
    fPot3_le_of_le (by omega)
  simp only [pot3, hm, hfr, stackPot3_cons, hph]
  norm_num
  omega

/-- **T7, the infeasible flip**: the top frame's stored alternative does
not fit in its budget, so it was never an alternative at all; the frame
flips to phase one and backtracking continues. The drop is at least two
units, one more than needed. -/
theorem step3_flip_infeasible {C : Config n} {f : Frame n} {fs : List (Frame n)}
    {l : List (Fin n)} (bud' : ℕ)
    (hJ : J3 G k C) (hm : C.mode = 1) (hfr : C.frames = f :: fs) (hph : f.phase = false)
    (hnd : l.Nodup) (hl : l.toFinset = ResNbhd G (marked fs) f.v)
    (hd : f.b < resDeg G (marked fs) f.v) :
    J3 G k ⟨⟨f.v, f.b, true, l⟩ :: fs, 1, bud', C.ans⟩ ∧
      pot3 (⟨⟨f.v, f.b, true, l⟩ :: fs, 1, bud', C.ans⟩ : Config n) + 1 ≤ pot3 C := by
  have hs : Sharp G (f :: fs) := hfr ▸ hJ.sharp
  refine ⟨⟨(step_flip_infeasible bud' hJ.j hm hfr hph hnd hl hd).1, ⟨by simp, hs.tail⟩⟩, ?_⟩
  have := one_le_fPot3 (f.b - 3)
  simp only [pot3, hm, hfr, stackPot3_cons, hph]
  norm_num

/-- **T8, the pop**: the top frame has spent both branches; it
contributes nothing to the alternatives, its marks come off the trail
and its budget comes back. The drop is the frame's last unit. -/
theorem step3_pop {C : Config n} {f : Frame n} {fs : List (Frame n)} (bud' : ℕ)
    (hJ : J3 G k C) (hm : C.mode = 1) (hfr : C.frames = f :: fs) (hph : f.phase = true) :
    J3 G k ⟨fs, 1, bud', C.ans⟩ ∧
      pot3 (⟨fs, 1, bud', C.ans⟩ : Config n) + 1 ≤ pot3 C := by
  have hs : Sharp G (f :: fs) := hfr ▸ hJ.sharp
  refine ⟨⟨(step_pop bud' hJ.j hm hfr hph).1, hs.tail⟩, ?_⟩
  simp only [pot3, hm, hfr, stackPot3_cons, hph]
  norm_num

end Lax15Proofs.VC3
