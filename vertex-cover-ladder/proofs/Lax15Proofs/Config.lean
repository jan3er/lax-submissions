import Lax15Proofs.Residual

/-!
The configuration side of the pure model: the search stack, what it
claims, and what it still has to do.

A configuration is a stack of frames, a mode (descend, backtrack,
done), a budget and an answer. A frame records the vertex `v` it
branched on, the budget `b` that was available when it was pushed, its
phase — `false` while the branch that takes `v` into the cover is
active, `true` once the branch that takes the whole residual
neighbourhood of `v` is — and the list `S` of vertices it marked. The
list is what makes this rung different from the `2^k` one: a phase-one
frame marks a whole neighbourhood, not a single vertex, so the depth of
the stack is no longer the budget spent, and each frame has to carry
its own budget. Everything below a frame is its marking `P_i`, the
union of the `S_j` under it; the marking of the whole stack is `M`, and
the trail is the concatenation of the `S_i` — the order the machine
unmarks in.

Frame health says the `S_i` are disjoint, nodup and nonempty, that a
phase-zero frame marked exactly `[v_i]` and a phase-one frame marked
exactly the residual neighbourhood of `v_i` below it, that the branch
vertex was a legitimate one (unmarked, residual degree at least two),
and that the stored budget is the initial one minus everything marked
below. Its consequences are the two bounds the machine needs for its
array writes: at most `n` frames and at most `n` trail entries, because
the `S_i` are disjoint nonempty subsets of `Fin n`.

The invariant `J` splits the answer the way the search does: while
descending, `Ok ∅ k` holds iff the active marking still admits a cover
within the remaining budget *or* one of the stored alternatives does;
while backtracking only the alternatives remain; at done the answer has
been written. The pending work `P` — `pot` here — is `fPot b =
4·fib (b+2) − 3` for the active subtree, `fPot (b_i − 2) + 2` for a
stored phase-zero frame, one unit for a phase-one frame and one for not
being done. The `−3` and the `+2` are load-bearing: `fPot` satisfies
`fPot (b+2) = fPot (b+1) + fPot b + 3` exactly, and a push splits its
level into the active child, the stored child, the frame's two units of
slack and the one unit that pays for the push. Every one of the eight
transitions drops `pot` by at least one, four of them by exactly one.

Nothing here mentions an environment; the machine meets this file only
through `Rep`-style representation lemmas later. The mirror `potN`
computes the same number from what the machine actually holds — the
mode, the budget and the list of `(b_i, phase_i)` read off the stack
arrays.
-/

namespace Lax15Proofs.VC

open Lax11Proofs.VC (Ok ok_empty_iff not_ok_zero)

variable {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}

/-! ### Frames, configurations, the marking -/

/-- One frame of the search stack: the vertex branched on, the budget
available when the frame was pushed, the phase — `false` while the
branch that takes `v` is active, `true` once the branch that takes the
residual neighbourhood of `v` is — and the vertices this frame marked,
in trail order. -/
structure Frame (n : ℕ) where
  /-- The vertex branched on. -/
  v : Fin n
  /-- The budget at the moment of the push. -/
  b : ℕ
  /-- Whether the second branch is the active one. -/
  phase : Bool
  /-- The vertices this frame marked, in trail order. -/
  S : List (Fin n)

/-- A configuration of the search: the stack of frames with the top at
the head, the mode (`0` descend, `1` backtrack, `2` done), the remaining
budget, and the answer. -/
structure Config (n : ℕ) where
  /-- The stack of frames, top first. -/
  frames : List (Frame n)
  /-- `0` descend, `1` backtrack, `2` done. -/
  mode : ℕ
  /-- The budget still available to the active branch. -/
  bud : ℕ
  /-- The answer, meaningful once the mode is `2`. -/
  ans : ℕ

/-- The trail: everything the stack has marked, in the order the frames
marked it — the top frame's marks first, which is the order the machine
unmarks in. -/
def trail (fs : List (Frame n)) : List (Fin n) := fs.flatMap Frame.S

@[simp] theorem trail_nil : trail ([] : List (Frame n)) = [] := rfl

@[simp] theorem trail_cons (f : Frame n) (fs : List (Frame n)) :
    trail (f :: fs) = f.S ++ trail fs := by
  simp [trail]

/-- The marking: the set of vertices the stack currently commits. The
marking *below* a frame — the `P_i` of the plan — is `marked` of the
frames under it. -/
def marked (fs : List (Frame n)) : Finset (Fin n) := (trail fs).toFinset

@[simp] theorem marked_nil : marked ([] : List (Frame n)) = ∅ := rfl

@[simp] theorem marked_cons (f : Frame n) (fs : List (Frame n)) :
    marked (f :: fs) = f.S.toFinset ∪ marked fs := by
  simp [marked]

theorem mem_marked_iff {w : Fin n} {fs : List (Frame n)} :
    w ∈ marked fs ↔ w ∈ trail fs := List.mem_toFinset

/-- The one-element case of `marked_cons`, the shape a push produces. -/
theorem toFinset_singleton_union (a : Fin n) (s : Finset (Fin n)) :
    ([a] : List (Fin n)).toFinset ∪ s = insert a s := by simp

/-! ### Frame health -/

/-- Frame health. Each frame branched on a vertex that was unmarked and
had two residual neighbours below it; it marked a nodup list, which is
`[v]` in phase zero and exactly the residual neighbourhood of `v` in
phase one; and its stored budget is the initial budget minus everything
marked below it. -/
def Healthy (G : SimpleGraph (Fin n)) (k : ℕ) : List (Frame n) → Prop
  | [] => True
  | f :: fs =>
      f.v ∉ marked fs ∧ 2 ≤ resDeg G (marked fs) f.v ∧ f.S.Nodup ∧
      f.b + (trail fs).length = k ∧
      (f.phase = false → f.S = [f.v]) ∧
      (f.phase = true → f.S.toFinset = ResNbhd G (marked fs) f.v) ∧
      Healthy G k fs

@[simp] theorem healthy_nil : Healthy G k ([] : List (Frame n)) := trivial

theorem healthy_cons {f : Frame n} {fs : List (Frame n)} :
    Healthy G k (f :: fs) ↔
      (f.v ∉ marked fs ∧ 2 ≤ resDeg G (marked fs) f.v ∧ f.S.Nodup ∧
        f.b + (trail fs).length = k ∧
        (f.phase = false → f.S = [f.v]) ∧
        (f.phase = true → f.S.toFinset = ResNbhd G (marked fs) f.v) ∧
        Healthy G k fs) := Iff.rfl

theorem Healthy.tail {f : Frame n} {fs : List (Frame n)}
    (h : Healthy G k (f :: fs)) : Healthy G k fs := h.2.2.2.2.2.2

/-- What a frame marked is disjoint from what is marked below it: in
phase zero because the branch vertex was unmarked, in phase one because
a residual neighbourhood is unmarked by definition. -/
theorem Healthy.head_disjoint {f : Frame n} {fs : List (Frame n)}
    (h : Healthy G k (f :: fs)) : Disjoint f.S.toFinset (marked fs) := by
  obtain ⟨hv, -, -, -, h0, h1, -⟩ := h
  cases hph : f.phase
  · rw [h0 hph]
    simpa using Finset.disjoint_singleton_left.2 hv
  · rw [h1 hph]
    exact resNbhd_disjoint _

/-- Every frame marked something: one vertex in phase zero, a
neighbourhood of size at least two in phase one. This is what keeps the
stack no deeper than the trail is long. -/
theorem Healthy.head_ne_nil {f : Frame n} {fs : List (Frame n)}
    (h : Healthy G k (f :: fs)) : f.S ≠ [] := by
  obtain ⟨-, hd, -, -, h0, h1, -⟩ := h
  cases hph : f.phase
  · rw [h0 hph]; simp
  · intro hnil
    have hS := h1 hph
    rw [hnil] at hS
    have : resDeg G (marked fs) f.v = 0 := by
      rw [resDeg_eq_card, ← hS]; simp
    omega

theorem Healthy.head_length_pos {f : Frame n} {fs : List (Frame n)}
    (h : Healthy G k (f :: fs)) : 0 < f.S.length := by
  cases hS : f.S with
  | nil => exact absurd hS h.head_ne_nil
  | cons a t => simp

/-- The size of a phase-one frame's marks is the residual degree it
branched on. -/
theorem Healthy.head_length_phase {f : Frame n} {fs : List (Frame n)}
    (h : Healthy G k (f :: fs)) (hph : f.phase = true) :
    f.S.length = resDeg G (marked fs) f.v := by
  rw [resDeg_eq_card, ← h.2.2.2.2.2.1 hph, List.toFinset_card_of_nodup h.2.2.1]

/-- The trail has no repetitions: the frames mark disjoint sets and each
marks a nodup list. -/
theorem Healthy.trail_nodup {fs : List (Frame n)} (h : Healthy G k fs) :
    (trail fs).Nodup := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    have hdisj : ∀ x ∈ f.S, ∀ y ∈ trail fs, x ≠ y := fun x hx y hy hxy =>
      Finset.disjoint_left.1 h.head_disjoint (List.mem_toFinset.2 hx)
        (mem_marked_iff.2 (hxy ▸ hy))
    rw [trail_cons, List.nodup_append]
    exact ⟨h.2.2.1, ih h.tail, hdisj⟩

theorem Healthy.card_marked {fs : List (Frame n)} (h : Healthy G k fs) :
    (marked fs).card = (trail fs).length :=
  List.toFinset_card_of_nodup h.trail_nodup

/-- **The trail bound**: the trail lists distinct vertices of `Fin n`,
so it is never longer than `n`. Every write to the trail array, at
extent `n + 1`, is in bounds. -/
theorem Healthy.trail_length_le {fs : List (Frame n)} (h : Healthy G k fs) :
    (trail fs).length ≤ n := by
  rw [← h.card_marked]
  simpa using Finset.card_le_univ (marked fs)

theorem Healthy.length_le_trail {fs : List (Frame n)} (h : Healthy G k fs) :
    fs.length ≤ (trail fs).length := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    have h1 := h.head_length_pos
    have h2 := ih h.tail
    rw [trail_cons, List.length_append]
    simp only [List.length_cons]
    omega

/-- **The stack bound**: each frame marks at least one vertex and the
frames mark disjoint sets, so there are never more than `n` of them.
Every write to a stack array, at extent `n + 1`, is in bounds. -/
theorem Healthy.length_le {fs : List (Frame n)} (h : Healthy G k fs) :
    fs.length ≤ n := h.length_le_trail.trans h.trail_length_le

/-- What a flip does to membership in the marking, pointwise: the
branch vertex comes off, the replacement list goes on. This is the shape
of the mark-array writes the flip performs. -/
theorem mem_marked_flip {f : Frame n} {fs : List (Frame n)} {l : List (Fin n)}
    (h : Healthy G k (f :: fs)) (hph : f.phase = false) (w : Fin n) :
    w ∈ marked (Frame.mk f.v f.b true l :: fs) ↔
      w ∈ l ∨ (w ≠ f.v ∧ w ∈ marked (f :: fs)) := by
  obtain ⟨hv, -, -, -, h0, -, -⟩ := h
  rw [marked_cons, marked_cons, h0 hph, toFinset_singleton_union]
  simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_insert]
  constructor
  · rintro (hw | hw)
    · exact Or.inl hw
    · exact Or.inr ⟨fun hc => hv (hc ▸ hw), Or.inr hw⟩
  · rintro (hw | ⟨hne, rfl | hw⟩)
    · exact Or.inl hw
    · exact absurd rfl hne
    · exact Or.inr hw

/-- What a pop does to membership in the marking, pointwise: exactly the
frame's own marks come off. -/
theorem mem_marked_pop {f : Frame n} {fs : List (Frame n)}
    (h : Healthy G k (f :: fs)) (w : Fin n) :
    w ∈ marked fs ↔ w ∉ f.S ∧ w ∈ marked (f :: fs) := by
  rw [marked_cons]
  simp only [Finset.mem_union, List.mem_toFinset]
  constructor
  · intro hw
    exact ⟨fun hc => Finset.disjoint_left.1 h.head_disjoint (List.mem_toFinset.2 hc) hw,
      Or.inr hw⟩
  · rintro ⟨hne, hw | hw⟩
    · exact absurd hw hne
    · exact hw

/-! ### The stored alternatives -/

/-- The stored alternatives: some phase-zero frame's second branch —
the one that takes the whole residual neighbourhood of its vertex — is
within its budget and succeeds. Each frame carries the budget it was
pushed at, so nothing has to be threaded through the recursion. -/
def Alt (G : SimpleGraph (Fin n)) : List (Frame n) → Prop
  | [] => False
  | f :: fs =>
      (f.phase = false ∧ resDeg G (marked fs) f.v ≤ f.b ∧
        Ok G (marked fs ∪ ResNbhd G (marked fs) f.v)
          (f.b - resDeg G (marked fs) f.v)) ∨ Alt G fs

@[simp] theorem alt_nil : Alt G ([] : List (Frame n)) ↔ False := Iff.rfl

theorem alt_cons (f : Frame n) (fs : List (Frame n)) :
    Alt G (f :: fs) ↔
      (f.phase = false ∧ resDeg G (marked fs) f.v ≤ f.b ∧
        Ok G (marked fs ∪ ResNbhd G (marked fs) f.v)
          (f.b - resDeg G (marked fs) f.v)) ∨ Alt G fs := Iff.rfl

/-! ### The invariant -/

/-- The invariant of the outer loop, on the pure configuration. While
descending, the answer is split between the active marking and the
stored alternatives, and the budget accounts for the whole trail; while
backtracking only the alternatives are left; at done the answer has been
written. Frame health rides along, and with it the two array bounds. -/
def J (G : SimpleGraph (Fin n)) (k : ℕ) (C : Config n) : Prop :=
  C.mode ≤ 2 ∧ Healthy G k C.frames ∧
  (C.mode = 0 → C.bud + (trail C.frames).length = k) ∧
  (C.mode = 0 → (Ok G ∅ k ↔ Ok G (marked C.frames) C.bud ∨ Alt G C.frames)) ∧
  (C.mode = 1 → (Ok G ∅ k ↔ Alt G C.frames)) ∧
  (C.mode = 2 → (C.ans = 1 ↔ Ok G ∅ k) ∧ C.ans ≤ 1)

theorem J.healthy {C : Config n} (hJ : J G k C) : Healthy G k C.frames := hJ.2.1

/-- The stack never outgrows the vertex set. -/
theorem J.frames_length_le {C : Config n} (hJ : J G k C) : C.frames.length ≤ n :=
  hJ.healthy.length_le

/-- The trail never outgrows the vertex set. -/
theorem J.trail_length_le {C : Config n} (hJ : J G k C) : (trail C.frames).length ≤ n :=
  hJ.healthy.trail_length_le

/-- The search starts in descend mode with an empty stack and the full
budget. -/
theorem j_init (G : SimpleGraph (Fin n)) (k : ℕ) : J G k ⟨[], 0, k, 0⟩ := by
  refine ⟨by norm_num, healthy_nil, by simp, fun _ => ?_, by simp, by simp⟩
  simp

/-- At done, the answer is the concept's `if`. -/
theorem ans_eq {C : Config n} (hJ : J G k C) (hm : C.mode = 2) :
    C.ans = if G.vertexCoverNum ≤ (k : ℕ∞) then 1 else 0 := by
  obtain ⟨-, -, -, -, -, hdone⟩ := hJ
  obtain ⟨hans, hle⟩ := hdone hm
  by_cases h : Ok G ∅ k
  · rw [if_pos ((ok_empty_iff G k).1 h)]
    exact hans.2 h
  · rw [if_neg (fun hv => h ((ok_empty_iff G k).2 hv))]
    have : C.ans ≠ 1 := fun h1 => h (hans.1 h1)
    omega

/-! ### The potential -/

theorem one_le_fib_add_two (b : ℕ) : 1 ≤ Nat.fib (b + 2) := by
  simpa using Nat.fib_mono (show 1 ≤ b + 2 by omega)

/-- The pending work of one level of the search tree: `4·fib (b+2) − 3`,
so that `fPot 0 = 1`, `fPot 1 = 5` and `fPot (b+2) = fPot (b+1) +
fPot b + 3` exactly. The `−3` is load-bearing — it is what a push pays
out of — and the recurrence is the Fibonacci one, which is where the
base `φ` comes from. -/
def fPot (b : ℕ) : ℕ := 4 * Nat.fib (b + 2) - 3

theorem fPot_zero : fPot 0 = 1 := by norm_num [fPot]

theorem fPot_one : fPot 1 = 5 := by
  have h : Nat.fib 3 = 2 := by norm_num [Nat.fib_add_two]
  norm_num [fPot, h]

/-- **The Fibonacci recurrence**, exactly: a level splits into its two
children and three units of slack. -/
theorem fPot_succ_succ (b : ℕ) : fPot (b + 2) = fPot (b + 1) + fPot b + 3 := by
  have hb2 : b + 2 + 2 = b + 4 := by omega
  have hb1 : b + 1 + 2 = b + 3 := by omega
  have hfib : Nat.fib (b + 4) = Nat.fib (b + 2) + Nat.fib (b + 3) := by
    have h := Nat.fib_add_two (n := b + 2)
    rwa [show b + 2 + 2 = b + 4 from by omega, show b + 2 + 1 = b + 3 from by omega] at h
  have h1 : 1 ≤ Nat.fib (b + 2) := one_le_fib_add_two b
  have h2 : 1 ≤ Nat.fib (b + 3) := by
    have := one_le_fib_add_two (b + 1)
    rwa [hb1] at this
  simp only [fPot, hb2, hb1]
  omega

theorem one_le_fPot (b : ℕ) : 1 ≤ fPot b := by
  have h := one_le_fib_add_two b
  simp only [fPot]
  omega

theorem fPot_mono : Monotone fPot := by
  intro a b hab
  have h := Nat.fib_mono (show a + 2 ≤ b + 2 by omega)
  simp only [fPot]
  omega

theorem fPot_le_of_le {a b : ℕ} (h : a ≤ b) : fPot a ≤ fPot b := fPot_mono h

/-- What a push pays: the level it splits covers both children, the
frame's two units of slack and the push itself. Exact at every budget —
at `b = 1` the truncated subtraction turns the recurrence into
`5 = 1 + 1 + 3`, which is why the `−3` cannot be simplified away. -/
theorem fPot_push {b : ℕ} (hb : 1 ≤ b) : fPot (b - 1) + fPot (b - 2) + 3 ≤ fPot b := by
  match b, hb with
  | 1, _ => simp [fPot_zero, fPot_one]
  | (b + 2), _ =>
    have h := fPot_succ_succ b
    simp only [Nat.add_sub_cancel, show b + 2 - 1 = b + 1 from by omega]
    omega

/-- The pending work of the stack: a phase-zero frame holds a whole
child plus two units of slack, a phase-one frame one unit. The child is
measured at the budget the frame will have after paying for the second
branch, which is at least two — hence `b − 2`. -/
def stackPot : List (Frame n) → ℕ
  | [] => 0
  | f :: fs => (if f.phase then 1 else fPot (f.b - 2) + 2) + stackPot fs

@[simp] theorem stackPot_nil : stackPot ([] : List (Frame n)) = 0 := rfl

theorem stackPot_cons (f : Frame n) (fs : List (Frame n)) :
    stackPot (f :: fs) = (if f.phase then 1 else fPot (f.b - 2) + 2) + stackPot fs := rfl

/-- The pending work of a configuration: the active subtree while
descending, the stack, and one unit for not being done. -/
def pot (C : Config n) : ℕ :=
  (if C.mode = 0 then fPot C.bud else 0) + stackPot C.frames +
    (if C.mode = 2 then 0 else 1)

theorem pot_init (k a : ℕ) : pot (⟨[], 0, k, a⟩ : Config n) = fPot k + 1 := by
  simp [pot]

theorem pot_init_le (k a : ℕ) : pot (⟨[], 0, k, a⟩ : Config n) ≤ 4 * Nat.fib (k + 2) := by
  rw [pot_init]
  have h := one_le_fib_add_two k
  simp only [fPot]
  omega

/-! ### The potential as the machine holds it -/

/-- The stack potential read off the stored budgets and phases alone —
the two stack arrays, and nothing else. -/
def stackPotN : List (ℕ × Bool) → ℕ
  | [] => 0
  | p :: ps => (if p.2 then 1 else fPot (p.1 - 2) + 2) + stackPotN ps

@[simp] theorem stackPotN_nil : stackPotN [] = 0 := rfl

theorem stackPotN_cons (p : ℕ × Bool) (ps : List (ℕ × Bool)) :
    stackPotN (p :: ps) = (if p.2 then 1 else fPot (p.1 - 2) + 2) + stackPotN ps := rfl

theorem stackPot_eq_stackPotN (fs : List (Frame n)) :
    stackPot fs = stackPotN (fs.map (fun f => (f.b, f.phase))) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [stackPot_cons, stackPotN_cons, ih]

/-- The potential as a function of what the environment holds: the mode,
the budget, and the stack's budget–phase pairs. -/
def potN (mode bud : ℕ) (frs : List (ℕ × Bool)) : ℕ :=
  (if mode = 0 then fPot bud else 0) + stackPotN frs + (if mode = 2 then 0 else 1)

theorem pot_eq_potN (C : Config n) :
    pot C = potN C.mode C.bud (C.frames.map (fun f => (f.b, f.phase))) := by
  simp [pot, potN, stackPot_eq_stackPotN]

/-! ### The eight transitions

Each takes the semantic fact the scan will have certified — never a
condition on slots — establishes the invariant for the new
configuration, and pays the loop rule one unit of potential. Four of
the drops are exact (`T4` push, `T5` exhausted, `T6` flip at
`d = 2`, `T8` pop); the rest have slack. -/

/-- **T1, the matching yes**: the active marking admits a cover within
budget, so the answer is yes. The scan certifies this by counting the
residual edges; `ok_of_card_resEdges_le` turns the count into `Ok`. -/
theorem step_yes {C : Config n} (hJ : J G k C) (hm : C.mode = 0)
    (hok : Ok G (marked C.frames) C.bud) :
    J G k ⟨C.frames, 2, C.bud, 1⟩ ∧
      pot (⟨C.frames, 2, C.bud, 1⟩ : Config n) + 1 ≤ pot C := by
  obtain ⟨-, hh, -, hdesc, -, -⟩ := hJ
  have hok0 : Ok G ∅ k := (hdesc hm).2 (Or.inl hok)
  refine ⟨⟨by norm_num, hh, by simp, by simp, by simp, fun _ => ⟨by simp [hok0], le_rfl⟩⟩, ?_⟩
  simp only [pot, hm]
  norm_num

/-- **T2, the matching no**: no unmarked vertex has two residual
neighbours and the residual edges outnumber the budget, so the active
marking is dead and only the stored alternatives remain. -/
theorem step_no {C : Config n} (hJ : J G k C) (hm : C.mode = 0)
    (hdeg : ∀ v : Fin n, v ∉ marked C.frames → resDeg G (marked C.frames) v ≤ 1)
    (hlt : C.bud < (ResEdges G (marked C.frames)).card) :
    J G k ⟨C.frames, 1, C.bud, C.ans⟩ ∧
      pot (⟨C.frames, 1, C.bud, C.ans⟩ : Config n) + 1 ≤ pot C := by
  obtain ⟨-, hh, -, hdesc, -, -⟩ := hJ
  have hdead : ¬ Ok G (marked C.frames) C.bud := not_ok_of_lt_card_resEdges hdeg hlt
  refine ⟨⟨by norm_num, hh, by simp, by simp, fun _ => ?_, by simp⟩, ?_⟩
  · rw [hdesc hm]
    tauto
  · have := one_le_fPot C.bud
    simp only [pot, hm]
    norm_num
    omega

/-- **T3, the budget no**: a residual edge is on the table and the
budget is spent, so the active marking is dead. -/
theorem step_stuck {C : Config n} {u v : Fin n} (hJ : J G k C) (hm : C.mode = 0)
    (hb : C.bud = 0) (huv : G.Adj u v) (hu : u ∉ marked C.frames)
    (hv : v ∉ marked C.frames) :
    J G k ⟨C.frames, 1, C.bud, C.ans⟩ ∧
      pot (⟨C.frames, 1, C.bud, C.ans⟩ : Config n) + 1 ≤ pot C := by
  obtain ⟨-, hh, -, hdesc, -, -⟩ := hJ
  have hdead : ¬ Ok G (marked C.frames) C.bud := hb ▸ not_ok_zero huv hu hv
  refine ⟨⟨by norm_num, hh, by simp, by simp, fun _ => ?_, by simp⟩, ?_⟩
  · rw [hdesc hm]
    tauto
  · simp only [pot, hm, hb, fPot_zero]
    norm_num

/-- **T4, the push**: a vertex with two residual neighbours and budget
left. The branch lemma rewrites the active claim into the branch that
takes `v` — the new active marking — and the branch that takes its
residual neighbourhood, which is exactly the new frame's stored
alternative. The drop is the one unit the level's `−3` was holding. -/
theorem step_push {C : Config n} {v : Fin n} (hJ : J G k C) (hm : C.mode = 0)
    (hb : 1 ≤ C.bud) (hv : v ∉ marked C.frames)
    (hd : 2 ≤ resDeg G (marked C.frames) v) :
    J G k ⟨⟨v, C.bud, false, [v]⟩ :: C.frames, 0, C.bud - 1, C.ans⟩ ∧
      pot (⟨⟨v, C.bud, false, [v]⟩ :: C.frames, 0, C.bud - 1, C.ans⟩ : Config n) + 1 ≤
        pot C := by
  obtain ⟨-, hh, hbud, hdesc, -, -⟩ := hJ
  have hbudk := hbud hm
  refine ⟨⟨by norm_num, ⟨hv, hd, by simp, hbudk, fun _ => rfl, by simp, hh⟩, ?_, ?_,
    by simp, by simp⟩, ?_⟩
  · intro _
    show C.bud - 1 + (trail (Frame.mk v C.bud false [v] :: C.frames)).length = k
    simp only [trail_cons, List.length_append, List.length_cons, List.length_nil]
    omega
  · intro _
    show Ok G ∅ k ↔ Ok G (marked (Frame.mk v C.bud false [v] :: C.frames)) (C.bud - 1) ∨
      Alt G (Frame.mk v C.bud false [v] :: C.frames)
    rw [hdesc hm, ok_branch_resNbhd hv hb, alt_cons, marked_cons,
      toFinset_singleton_union]
    tauto
  · have hpush := fPot_push hb
    simp only [pot, hm, stackPot_cons]
    norm_num
    omega

/-- **T5, the exhaustion**: backtracking with an empty stack. No
alternatives are left, so `Ok ∅ k` fails and the answer is no. The drop
is the not-done unit. -/
theorem step_exhausted {C : Config n} (hJ : J G k C) (hm : C.mode = 1)
    (hfr : C.frames = []) :
    J G k ⟨C.frames, 2, C.bud, 0⟩ ∧
      pot (⟨C.frames, 2, C.bud, 0⟩ : Config n) + 1 ≤ pot C := by
  obtain ⟨-, hh, -, -, hback, -⟩ := hJ
  have hnot : ¬ Ok G ∅ k := by
    rw [hback hm, hfr]
    simp
  refine ⟨⟨by norm_num, hh, by simp, by simp, by simp,
    fun _ => ⟨by simp [hnot], by norm_num⟩⟩, ?_⟩
  simp only [pot, hm]
  norm_num

/-- **T6, the feasible flip**: the top frame's stored alternative fits
in its budget, so it becomes the active branch — the marking becomes
what is below the frame together with the residual neighbourhood, and
the budget becomes the frame's minus the residual degree, on the nose.
The replacement list is arbitrary up to order and repetition: the
machine produces it in the encoding's order, and the pure side must not
care. The drop is exact when the residual degree is two. -/
theorem step_flip {C : Config n} {f : Frame n} {fs : List (Frame n)} {l : List (Fin n)}
    (hJ : J G k C) (hm : C.mode = 1) (hfr : C.frames = f :: fs) (hph : f.phase = false)
    (hnd : l.Nodup) (hl : l.toFinset = ResNbhd G (marked fs) f.v)
    (hd : resDeg G (marked fs) f.v ≤ f.b) :
    J G k ⟨⟨f.v, f.b, true, l⟩ :: fs, 0, f.b - resDeg G (marked fs) f.v, C.ans⟩ ∧
      pot (⟨⟨f.v, f.b, true, l⟩ :: fs, 0, f.b - resDeg G (marked fs) f.v, C.ans⟩ :
          Config n) + 1 ≤ pot C := by
  obtain ⟨-, hh, -, -, hback, -⟩ := hJ
  rw [hfr] at hh hback
  obtain ⟨hv, hdeg, -, hbk, -, -, hhfs⟩ := hh
  have hlen : l.length = resDeg G (marked fs) f.v := by
    rw [resDeg_eq_card, ← hl, List.toFinset_card_of_nodup hnd]
  refine ⟨⟨by norm_num, ⟨hv, hdeg, hnd, hbk, by simp, fun _ => hl, hhfs⟩, ?_, ?_,
    by simp, by simp⟩, ?_⟩
  · intro _
    show f.b - resDeg G (marked fs) f.v +
      (trail (Frame.mk f.v f.b true l :: fs)).length = k
    simp only [trail_cons, List.length_append, hlen]
    omega
  · intro _
    show Ok G ∅ k ↔ Ok G (marked (Frame.mk f.v f.b true l :: fs))
        (f.b - resDeg G (marked fs) f.v) ∨ Alt G (Frame.mk f.v f.b true l :: fs)
    rw [hback hm, alt_cons, alt_cons, marked_cons, hl,
      Finset.union_comm (ResNbhd G (marked fs) f.v) (marked fs)]
    exact ⟨fun h => h.elim (fun hc => Or.inl hc.2.2) (fun hr => Or.inr (Or.inr hr)),
      fun h => h.elim (fun hok => Or.inl ⟨hph, hd, hok⟩)
        (fun h2 => h2.elim (fun hc => absurd hc.1 (by simp)) Or.inr)⟩
  · have hmono : fPot (f.b - resDeg G (marked fs) f.v) ≤ fPot (f.b - 2) :=
      fPot_le_of_le (by omega)
    simp only [pot, hm, hfr, stackPot_cons, hph]
    norm_num
    omega

/-- **T7, the infeasible flip**: the top frame's stored alternative does
not fit in its budget, so it was never an alternative at all; the frame
flips to phase one — its marks are on the trail, and the pop will take
them off — and backtracking continues. The drop is two units, one more
than needed. -/
theorem step_flip_infeasible {C : Config n} {f : Frame n} {fs : List (Frame n)}
    {l : List (Fin n)} (bud' : ℕ)
    (hJ : J G k C) (hm : C.mode = 1) (hfr : C.frames = f :: fs) (hph : f.phase = false)
    (hnd : l.Nodup) (hl : l.toFinset = ResNbhd G (marked fs) f.v)
    (hd : f.b < resDeg G (marked fs) f.v) :
    J G k ⟨⟨f.v, f.b, true, l⟩ :: fs, 1, bud', C.ans⟩ ∧
      pot (⟨⟨f.v, f.b, true, l⟩ :: fs, 1, bud', C.ans⟩ : Config n) + 1 ≤ pot C := by
  obtain ⟨-, hh, -, -, hback, -⟩ := hJ
  rw [hfr] at hh hback
  obtain ⟨hv, hdeg, -, hbk, -, -, hhfs⟩ := hh
  refine ⟨⟨by norm_num, ⟨hv, hdeg, hnd, hbk, by simp, fun _ => hl, hhfs⟩, by simp, by simp,
    fun _ => ?_, by simp⟩, ?_⟩
  · show Ok G ∅ k ↔ Alt G (Frame.mk f.v f.b true l :: fs)
    rw [hback hm, alt_cons, alt_cons]
    exact ⟨fun h => h.elim (fun hc => absurd hc.2.1 (by omega)) Or.inr,
      fun h => h.elim (fun hc => absurd hc.1 (by simp)) Or.inr⟩
  · have := one_le_fPot (f.b - 2)
    simp only [pot, hm, hfr, stackPot_cons, hph]
    norm_num

/-- **T8, the pop**: the top frame has spent both branches; it
contributes nothing to the alternatives, its marks come off the trail
and its budget comes back. The drop is the frame's last unit. -/
theorem step_pop {C : Config n} {f : Frame n} {fs : List (Frame n)} (bud' : ℕ)
    (hJ : J G k C) (hm : C.mode = 1) (hfr : C.frames = f :: fs) (hph : f.phase = true) :
    J G k ⟨fs, 1, bud', C.ans⟩ ∧
      pot (⟨fs, 1, bud', C.ans⟩ : Config n) + 1 ≤ pot C := by
  obtain ⟨-, hh, -, -, hback, -⟩ := hJ
  rw [hfr] at hh hback
  refine ⟨⟨by norm_num, hh.tail, by simp, by simp, fun _ => ?_, by simp⟩, ?_⟩
  · rw [hback hm, alt_cons]
    simp [hph]
  · simp only [pot, hm, hfr, stackPot_cons, hph]
    norm_num

end Lax15Proofs.VC
