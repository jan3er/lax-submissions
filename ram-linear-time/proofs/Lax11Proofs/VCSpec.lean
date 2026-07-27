import Lax11.VertexCover
import Lax11Proofs.CCGraph

/-!
The pure side of the bounded search tree, with no environment anywhere.

Three layers. First the search predicate `Ok M b` — some vertex cover
extends `M` by at most `b` vertices — with the three facts the search
lives on: the bridge to the concept's `vertexCoverNum`, the branch
lemma (an uncovered edge forces one of its endpoints, at one unit of
budget), and cover-on-exhaustion (a marking no CSR slot escapes is a
cover). Second the configuration of the search: a stack of frames, a
mode, a budget and an answer, with the invariant `Inv` tying the
machine's state to `Ok ∅ k` and one preservation lemma per transition.
Third the potential: the pending work `pot` of a configuration, which
every transition strictly decreases; this is the amortized budget the
loop rule spends.

The stack is a list with the *top at the head*, and both the stored
alternative `Alt` and the potential `stackPot` recurse on it carrying
the current budget: the frame below the top was pushed at one budget
more, so the recursion adds one as it descends. This is what makes
push, flip and pop line up definitionally — no index arithmetic over
frame positions ever appears.

The budget of a level is `fPot b = 4·2^b − 3`, so that
`fPot (b+1) = 2·fPot b + 3` exactly: a push splits its level's budget
into the active child, the stored child and three units of slack, one
of which pays for the push itself. The naive `4·2^b` fails — a push
would gain a unit — so the `−3` is load-bearing; do not simplify it
away.
-/

namespace Lax11Proofs.VC

open Lax11.GraphEncoding Lax11Proofs.CC

variable {n : ℕ} {G : SimpleGraph (Fin n)}

/-! ### The search predicate -/

/-- `Ok G M b`: some vertex cover of `G` extends `M` by at most `b`
vertices. The search maintains what `Ok ∅ k` is equivalent to; the
bridge below turns it into the concept's answer. -/
def Ok (G : SimpleGraph (Fin n)) (M : Finset (Fin n)) (b : ℕ) : Prop :=
  ∃ S : Finset (Fin n), G.IsVertexCover ↑S ∧ M ⊆ S ∧ (S \ M).card ≤ b

theorem Ok.mono {M : Finset (Fin n)} {b b' : ℕ} (h : Ok G M b) (hb : b ≤ b') :
    Ok G M b' := by
  obtain ⟨S, hS, hMS, hcard⟩ := h
  exact ⟨S, hS, hMS, hcard.trans hb⟩

/-- A marking that is itself a cover satisfies its own budget, whatever
it is. -/
theorem Ok.of_isVertexCover {M : Finset (Fin n)} {b : ℕ}
    (h : G.IsVertexCover ↑M) : Ok G M b :=
  ⟨M, h, Finset.Subset.refl M, by simp⟩

/-- **The bridge**: the search predicate at the empty marking is the
concept's answer. This is the only contact with `ℕ∞` in the whole
development; it is quarantined here. -/
theorem ok_empty_iff (G : SimpleGraph (Fin n)) (k : ℕ) :
    Ok G ∅ k ↔ G.vertexCoverNum ≤ (k : ℕ∞) := by
  constructor
  · rintro ⟨S, hS, -, hcard⟩
    calc G.vertexCoverNum ≤ (↑S : Set (Fin n)).encard := hS.vertexCoverNum_le
      _ = (S.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard S
      _ ≤ (k : ℕ∞) := by
          simp only [Finset.sdiff_empty] at hcard
          exact_mod_cast hcard
  · intro h
    obtain ⟨s, henc, hcov⟩ := SimpleGraph.vertexCoverNum_exists G
    have hfin : s.Finite := Set.toFinite s
    refine ⟨hfin.toFinset, by rwa [Set.Finite.coe_toFinset], Finset.empty_subset _, ?_⟩
    have hcard : (hfin.toFinset.card : ℕ∞) ≤ (k : ℕ∞) := by
      rw [← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset, henc]
      exact h
    simpa [Finset.sdiff_empty] using (Nat.cast_le.1 hcard)

/-- With an uncovered edge on the table and no budget, the search is
stuck: no cover extends the marking for free. -/
theorem not_ok_zero {M : Finset (Fin n)} {u v : Fin n} (huv : G.Adj u v)
    (hu : u ∉ M) (hv : v ∉ M) : ¬ Ok G M 0 := by
  rintro ⟨S, hS, hMS, hcard⟩
  have hSM : S = M := Finset.Subset.antisymm
    (fun x hx => by
      by_contra hxM
      exact absurd (Finset.card_pos.2 ⟨x, Finset.mem_sdiff.2 ⟨hx, hxM⟩⟩) (by omega))
    hMS
  rcases hS huv with h | h
  · exact hu (hSM ▸ h)
  · exact hv (hSM ▸ h)

/-- Dropping a vertex from the marking costs one unit of budget. -/
theorem Ok.insert_out {M : Finset (Fin n)} {u : Fin n} {b : ℕ}
    (h : Ok G (insert u M) b) : Ok G M (b + 1) := by
  obtain ⟨S, hS, hMS, hcard⟩ := h
  refine ⟨S, hS, (Finset.subset_insert u M).trans hMS, ?_⟩
  have hsub : S \ M ⊆ insert u (S \ insert u M) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rcases eq_or_ne x u with rfl | hxu
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_sdiff.2 ⟨hx.1, by simp [Finset.mem_insert, hxu, hx.2]⟩)
  calc (S \ M).card ≤ (insert u (S \ insert u M)).card := Finset.card_le_card hsub
    _ ≤ (S \ insert u M).card + 1 := Finset.card_insert_le _ _
    _ ≤ b + 1 := by omega

/-- **The branch lemma**: an edge neither endpoint of which is marked
forces one of its endpoints into any extending cover, at one unit of
budget. -/
theorem ok_branch {M : Finset (Fin n)} {u v : Fin n} {b : ℕ} (huv : G.Adj u v)
    (hu : u ∉ M) (hv : v ∉ M) :
    Ok G M b ↔ 0 < b ∧ (Ok G (insert u M) (b - 1) ∨ Ok G (insert v M) (b - 1)) := by
  constructor
  · rintro ⟨S, hS, hMS, hcard⟩
    have key : ∀ w : Fin n, w ∈ S → w ∉ M →
        0 < b ∧ Ok G (insert w M) (b - 1) := by
      intro w hwS hwM
      have hwmem : w ∈ S \ M := Finset.mem_sdiff.2 ⟨hwS, hwM⟩
      have hpos : 0 < (S \ M).card := Finset.card_pos.2 ⟨w, hwmem⟩
      refine ⟨by omega, S, hS, Finset.insert_subset hwS hMS, ?_⟩
      have hdiff : S \ insert w M = (S \ M).erase w := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        tauto
      rw [hdiff, Finset.card_erase_of_mem hwmem]
      omega
    rcases hS huv with h | h
    · obtain ⟨hb, hok⟩ := key u h hu
      exact ⟨hb, Or.inl hok⟩
    · obtain ⟨hb, hok⟩ := key v h hv
      exact ⟨hb, Or.inr hok⟩
  · rintro ⟨hb, h | h⟩
    · exact h.insert_out.mono (by omega)
    · exact h.insert_out.mono (by omega)

/-- **Cover-on-exhaustion**: a marking that touches every CSR slot —
for every vertex's block, either the vertex or the slot's target is
marked — is a vertex cover. Adjacency transports through the encoding
once, here. -/
theorem isVertexCover_of_slots {g : List ℕ} (hg : EncodesGraph g n G)
    (M : Finset (Fin n))
    (h : ∀ o p, (ho : o < n) → (hp : target g p < n) →
      offset g o ≤ p → p < offset g (o + 1) →
      (⟨o, ho⟩ : Fin n) ∈ M ∨ (⟨target g p, hp⟩ : Fin n) ∈ M) :
    G.IsVertexCover ↑M := by
  intro a b hab
  obtain ⟨j, hj₁, hj₂, hj₃⟩ := (hg.adj_iff a b).1 hab
  have hpt : target g j < n := by rw [hj₃]; exact b.2
  rcases h a j a.2 hpt hj₁ hj₂ with hm | hm
  · exact Or.inl (by simpa using hm)
  · refine Or.inr ?_
    have : (⟨target g j, hpt⟩ : Fin n) = b := Fin.ext hj₃
    rw [this] at hm
    simpa using hm

/-! ### The configuration of the search -/

/-- One frame of the search stack: the two endpoints of the branching
edge, and the phase — `false` while the branch through `u` is active,
`true` once the branch through `v` is. -/
structure Frame (n : ℕ) where
  /-- The first endpoint of the branching edge. -/
  u : Fin n
  /-- The second endpoint of the branching edge. -/
  v : Fin n
  /-- Whether the second branch is the active one. -/
  ph : Bool

/-- The vertex a frame currently commits to the cover. -/
def Frame.chosen (f : Frame n) : Fin n := if f.ph then f.v else f.u

@[simp] theorem chosen_false (u v : Fin n) : (Frame.mk u v false).chosen = u := rfl

@[simp] theorem chosen_true (u v : Fin n) : (Frame.mk u v true).chosen = v := rfl

/-- A configuration of the search: the stack of frames with the top at
the head, the mode (`0` descend, `1` backtrack, `2` done), the budget,
and the answer. -/
structure Config (n : ℕ) where
  /-- The stack of frames, top first. -/
  frames : List (Frame n)
  /-- `0` descend, `1` backtrack, `2` done. -/
  mode : ℕ
  /-- The remaining budget: `k` minus the depth of the stack. -/
  bud : ℕ
  /-- The answer, meaningful once the mode is `2`. -/
  ans : ℕ

/-- The marked set: the vertices the stack currently commits. -/
def marked (fs : List (Frame n)) : Finset (Fin n) :=
  (fs.map Frame.chosen).toFinset

@[simp] theorem marked_nil : marked ([] : List (Frame n)) = ∅ := rfl

@[simp] theorem marked_cons (f : Frame n) (fs : List (Frame n)) :
    marked (f :: fs) = insert f.chosen (marked fs) := by
  simp [marked]

/-- The stored alternatives: some phase-`false` frame's branch through
`v` succeeds. The argument `b` is the budget at the top of the stack;
one level down it is one more. -/
def Alt (G : SimpleGraph (Fin n)) : List (Frame n) → ℕ → Prop
  | [], _ => False
  | f :: fs, b => (f.ph = false ∧ Ok G (insert f.v (marked fs)) b) ∨ Alt G fs (b + 1)

@[simp] theorem alt_nil (b : ℕ) : Alt G [] b ↔ False := Iff.rfl

theorem alt_cons (f : Frame n) (fs : List (Frame n)) (b : ℕ) :
    Alt G (f :: fs) b ↔
      (f.ph = false ∧ Ok G (insert f.v (marked fs)) b) ∨ Alt G fs (b + 1) := by
  simp [Alt]

/-- Frame health: each frame's committed vertex is fresh, and a
phase-`false` frame's stored endpoint avoids both its partner and
everything below — which is what makes the unmark on flip and on pop
undo exactly one mark. -/
def Healthy : List (Frame n) → Prop
  | [] => True
  | f :: fs => f.chosen ∉ marked fs ∧
      (f.ph = false → f.v ∉ insert f.u (marked fs)) ∧ Healthy fs

/-- What a flip does to membership in the marked set, pointwise: the
shape of the two mark-array writes (`u` off, `v` on). -/
theorem mem_marked_flip {u v : Fin n} {fs : List (Frame n)}
    (hh : Healthy (Frame.mk u v false :: fs)) (w : Fin n) :
    w ∈ marked (Frame.mk u v true :: fs) ↔
      w = v ∨ (w ≠ u ∧ w ∈ marked (Frame.mk u v false :: fs)) := by
  obtain ⟨hu, hv, -⟩ := hh
  have hv' := hv rfl
  simp only [chosen_false] at hu
  simp only [Finset.mem_insert, not_or] at hv'
  simp only [marked_cons, chosen_true, chosen_false, Finset.mem_insert]
  constructor
  · rintro (rfl | hw)
    · exact Or.inl rfl
    · rcases eq_or_ne w u with rfl | hwu
      · exact absurd hw hu
      · exact Or.inr ⟨hwu, Or.inr hw⟩
  · rintro (rfl | ⟨hwu, rfl | hw⟩)
    · exact Or.inl rfl
    · exact absurd rfl hwu
    · exact Or.inr hw

/-- What a pop does to membership in the marked set, pointwise: the
shape of the one mark-array write (`v` off). -/
theorem mem_marked_pop {u v : Fin n} {fs : List (Frame n)}
    (hh : Healthy (Frame.mk u v true :: fs)) (w : Fin n) :
    w ∈ marked fs ↔ w ≠ v ∧ w ∈ marked (Frame.mk u v true :: fs) := by
  obtain ⟨hv, -, -⟩ := hh
  simp only [chosen_true] at hv
  simp only [marked_cons, chosen_true, Finset.mem_insert]
  constructor
  · intro hw
    exact ⟨fun h => hv (h ▸ hw), Or.inr hw⟩
  · rintro ⟨hwv, rfl | hw⟩
    · exact absurd rfl hwv
    · exact hw

/-! ### The invariant -/

/-- The invariant of the outer loop, on the pure configuration. In
descend mode the answer is split between the active marking and the
stored alternatives; in backtrack mode only the alternatives remain; at
done the answer has been written. Health and the budget–depth tie ride
along. -/
def Inv (G : SimpleGraph (Fin n)) (k : ℕ) (C : Config n) : Prop :=
  C.mode ≤ 2 ∧ C.bud + C.frames.length = k ∧ Healthy C.frames ∧
  (C.mode = 0 → (Ok G ∅ k ↔ Ok G (marked C.frames) C.bud ∨ Alt G C.frames C.bud)) ∧
  (C.mode = 1 → (Ok G ∅ k ↔ Alt G C.frames C.bud)) ∧
  (C.mode = 2 → (C.ans = 1 ↔ Ok G ∅ k) ∧ C.ans ≤ 1)

/-- The search starts in descend mode with an empty stack and the full
budget. -/
theorem inv_init (G : SimpleGraph (Fin n)) (k : ℕ) :
    Inv G k ⟨[], 0, k, 0⟩ := by
  refine ⟨by norm_num, by simp, trivial, fun _ => ?_, by simp, by simp⟩
  simp

/-- At done, the answer is the concept's `if`. -/
theorem ans_eq {k : ℕ} {C : Config n} (hI : Inv G k C) (hm : C.mode = 2) :
    C.ans = if G.vertexCoverNum ≤ (k : ℕ∞) then 1 else 0 := by
  obtain ⟨-, -, -, -, -, hdone⟩ := hI
  obtain ⟨hans, hle⟩ := hdone hm
  by_cases h : Ok G ∅ k
  · rw [if_pos ((ok_empty_iff G k).1 h)]
    exact hans.2 h
  · rw [if_neg (fun hv => h ((ok_empty_iff G k).2 hv))]
    have : C.ans ≠ 1 := fun h1 => h (hans.1 h1)
    omega

/-! ### The six transitions -/

/-- **Push**: an uncovered edge with budget left. The new frame commits
`u`; the branch through `v` joins the alternatives, definitionally. -/
theorem inv_push {k : ℕ} {C : Config n} {u v : Fin n} (hI : Inv G k C)
    (hm : C.mode = 0) (hb : 0 < C.bud) (huv : G.Adj u v)
    (hu : u ∉ marked C.frames) (hv : v ∉ marked C.frames) :
    Inv G k ⟨Frame.mk u v false :: C.frames, 0, C.bud - 1, C.ans⟩ := by
  obtain ⟨-, hlen, hh, hdesc, -, -⟩ := hI
  refine ⟨by norm_num, by simp; omega, ?_, fun _ => ?_, by simp, by simp⟩
  · exact ⟨by simpa using hu, fun _ => by
      simp only [Finset.mem_insert, not_or]
      exact ⟨huv.ne', hv⟩, hh⟩
  · rw [hdesc hm, ok_branch huv hu hv]
    simp only [marked_cons, chosen_false, alt_cons, true_and]
    have hb1 : C.bud - 1 + 1 = C.bud := by omega
    rw [hb1]
    have := hb
    tauto

/-- **Descend to backtrack**: an uncovered edge and no budget. The
active marking is dead, so only the alternatives remain. -/
theorem inv_stuck {k : ℕ} {C : Config n} {u v : Fin n} (hI : Inv G k C)
    (hm : C.mode = 0) (hb : C.bud = 0) (huv : G.Adj u v)
    (hu : u ∉ marked C.frames) (hv : v ∉ marked C.frames) :
    Inv G k ⟨C.frames, 1, C.bud, C.ans⟩ := by
  obtain ⟨-, hlen, hh, hdesc, -, -⟩ := hI
  refine ⟨by norm_num, hlen, hh, by simp, fun _ => ?_, by simp⟩
  rw [hdesc hm]
  have hdead : ¬ Ok G (marked C.frames) C.bud := hb ▸ not_ok_zero huv hu hv
  tauto

/-- **Success exit**: the marking is a cover, so `Ok ∅ k` holds and the
answer is `1`. -/
theorem inv_found_cover {k : ℕ} {C : Config n} (hI : Inv G k C)
    (hm : C.mode = 0) (hcov : G.IsVertexCover ↑(marked C.frames)) :
    Inv G k ⟨C.frames, 2, C.bud, 1⟩ := by
  obtain ⟨-, hlen, hh, hdesc, -, -⟩ := hI
  have hok : Ok G ∅ k := (hdesc hm).2 (Or.inl (Ok.of_isVertexCover hcov))
  exact ⟨le_rfl, hlen, hh, by simp, by simp, fun _ => ⟨by simp [hok], le_rfl⟩⟩

/-- **Failure exit**: backtrack with an empty stack. No alternatives
are left, so `Ok ∅ k` fails and the answer is `0`. -/
theorem inv_fail {k : ℕ} {C : Config n} (hI : Inv G k C)
    (hm : C.mode = 1) (hfr : C.frames = []) :
    Inv G k ⟨C.frames, 2, C.bud, 0⟩ := by
  obtain ⟨-, hlen, hh, -, hback, -⟩ := hI
  have hnot : ¬ Ok G ∅ k := by
    rw [hback hm, hfr]
    simp
  exact ⟨le_rfl, hlen, hh, by simp, by simp, fun _ => ⟨by simp [hnot], by norm_num⟩⟩

/-- **Flip**: the top frame's stored branch becomes the active one. The
marking becomes `insert v` of what is below, and the budget is already
right — the bookkeeping makes this definitional. -/
theorem inv_flip {k : ℕ} {C : Config n} {u v : Fin n} {fs : List (Frame n)}
    (hI : Inv G k C) (hm : C.mode = 1) (hfr : C.frames = Frame.mk u v false :: fs) :
    Inv G k ⟨Frame.mk u v true :: fs, 0, C.bud, C.ans⟩ := by
  obtain ⟨-, hlen, hh, -, hback, -⟩ := hI
  rw [hfr] at hlen hh hback
  obtain ⟨hcu, hcv, hhfs⟩ := hh
  refine ⟨by norm_num, by simpa using hlen, ?_, fun _ => ?_, by simp, by simp⟩
  · refine ⟨?_, by simp, hhfs⟩
    simp only [chosen_true]
    exact fun h => (hcv rfl) (Finset.mem_insert_of_mem h)
  · rw [hback hm, alt_cons]
    simp [alt_cons]

/-- **Pop**: the top frame is exhausted; its mark comes off and its
budget unit comes back. -/
theorem inv_pop {k : ℕ} {C : Config n} {u v : Fin n} {fs : List (Frame n)}
    (hI : Inv G k C) (hm : C.mode = 1) (hfr : C.frames = Frame.mk u v true :: fs) :
    Inv G k ⟨fs, 1, C.bud + 1, C.ans⟩ := by
  obtain ⟨-, hlen, hh, -, hback, -⟩ := hI
  rw [hfr] at hlen hh hback
  refine ⟨by norm_num, by simp at hlen ⊢; omega, hh.2.2, by simp, fun _ => ?_, by simp⟩
  rw [hback hm, alt_cons]
  simp

/-! ### The potential -/

/-- The budget of one level of the tree: `4·2^b − 3`, so that
`fPot 0 = 1` and `fPot (b+1) = 2·fPot b + 3` exactly. The `−3` is
load-bearing: it is what a push pays out of. -/
def fPot (b : ℕ) : ℕ := 4 * 2 ^ b - 3

@[simp] theorem fPot_zero : fPot 0 = 1 := rfl

theorem fPot_succ (b : ℕ) : fPot (b + 1) = 2 * fPot b + 3 := by
  have h : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  simp only [fPot, pow_succ]
  omega

theorem one_le_fPot (b : ℕ) : 1 ≤ fPot b := by
  have h : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  simp only [fPot]
  omega

theorem fPot_le (b : ℕ) : fPot b ≤ 4 * 2 ^ b := Nat.sub_le _ _

/-- The pending work of the stack: a phase-`false` frame holds a whole
child plus two units of slack, a phase-`true` frame one unit. The
argument `b` is the budget at the top, as in `Alt`. -/
def stackPot : List (Frame n) → ℕ → ℕ
  | [], _ => 0
  | f :: fs, b => (if f.ph then 1 else fPot b + 2) + stackPot fs (b + 1)

@[simp] theorem stackPot_nil (b : ℕ) : stackPot ([] : List (Frame n)) b = 0 := rfl

theorem stackPot_cons (f : Frame n) (fs : List (Frame n)) (b : ℕ) :
    stackPot (f :: fs) b = (if f.ph then 1 else fPot b + 2) + stackPot fs (b + 1) := rfl

/-- The pending work of a configuration: the active subtree while
descending, the stack, and one unit for not being done. -/
def pot (C : Config n) : ℕ :=
  (if C.mode = 0 then fPot C.bud else 0) + stackPot C.frames C.bud +
    (if C.mode = 2 then 0 else 1)

theorem pot_init (k a : ℕ) : pot (⟨[], 0, k, a⟩ : Config n) = fPot k + 1 := by
  simp [pot]

theorem pot_init_le (k a : ℕ) : pot (⟨[], 0, k, a⟩ : Config n) ≤ 4 * 2 ^ k := by
  rw [pot_init]
  have h : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  simp only [fPot]
  omega

/-- A push pays one unit: `fPot b` splits into the two children and the
frame's slack, with one unit left over. -/
theorem pot_push {fs : List (Frame n)} {b : ℕ} (hb : 0 < b) (u v : Fin n) (a a' : ℕ) :
    pot (⟨Frame.mk u v false :: fs, 0, b - 1, a⟩ : Config n) + 1 ≤
      pot (⟨fs, 0, b, a'⟩ : Config n) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  simp only [pot, stackPot_cons, if_pos, Nat.add_sub_cancel]
  rw [fPot_succ]
  simp
  omega

/-- Running out of budget pays the `fPot 0 = 1` of the dead subtree. -/
theorem pot_stuck {fs : List (Frame n)} (a a' : ℕ) :
    pot (⟨fs, 1, 0, a⟩ : Config n) + 1 ≤ pot (⟨fs, 0, 0, a'⟩ : Config n) := by
  simp [pot]

/-- The success exit pays the not-done unit. -/
theorem pot_found {fs : List (Frame n)} (b : ℕ) (a a' : ℕ) :
    pot (⟨fs, 2, b, a⟩ : Config n) + 1 ≤ pot (⟨fs, 0, b, a'⟩ : Config n) := by
  have := one_le_fPot b
  simp [pot]

/-- The failure exit pays the not-done unit. -/
theorem pot_fail {fs : List (Frame n)} (b : ℕ) (a a' : ℕ) :
    pot (⟨fs, 2, b, a⟩ : Config n) + 1 ≤ pot (⟨fs, 1, b, a'⟩ : Config n) := by
  simp [pot]

/-- A flip pays one of the frame's two units of slack: `fPot b + 2`
becomes the active `fPot b` plus the frame's remaining unit. -/
theorem pot_flip {fs : List (Frame n)} {u v : Fin n} (b : ℕ) (a a' : ℕ) :
    pot (⟨Frame.mk u v true :: fs, 0, b, a⟩ : Config n) + 1 ≤
      pot (⟨Frame.mk u v false :: fs, 1, b, a'⟩ : Config n) := by
  simp [pot, stackPot_cons]
  omega

/-- A pop pays the frame's last unit. -/
theorem pot_pop {fs : List (Frame n)} {u v : Fin n} (b : ℕ) (a a' : ℕ) :
    pot (⟨fs, 1, b + 1, a⟩ : Config n) + 1 ≤
      pot (⟨Frame.mk u v true :: fs, 1, b, a'⟩ : Config n) := by
  simp [pot, stackPot_cons]

end Lax11Proofs.VC
