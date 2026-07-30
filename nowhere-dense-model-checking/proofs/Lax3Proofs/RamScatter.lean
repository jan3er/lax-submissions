import Lax3.ScatterSentences
import Lax3Proofs.RamBfs

/-!
The **greedy scatter pass**, as a word-RAM program with its correctness
and its running time.

A scatter sentence asks whether a distinguished `r`-scattered subset of
the set defined by a one-variable formula has at least `t` elements, and
the distinguished subset this submission's evaluator uses is
`Lax3.ScatterSentences.greedyChoice` — the set the greedy process
produces running through the vertices in the canonical order of `Fin n`
and taking every vertex it can. So the pass is handed a masked arena, a
radius `r`, a threshold `t`, and one bit per vertex saying whether the
formula holds there, and it has to decide

    t ≤ (greedySet (masked G M) r X).ncard.

### The program *is* the recursion

`GreedyMem` says that `v` is selected exactly when it lies in `X` and no
*earlier selected* vertex is within `r` of it. That is a recursion in
`Fin`-order, and a single left-to-right scan runs it: keep a counter of
what has been selected and one bit per vertex saying "some already
selected vertex is within `r` of you". At `v`, the two tests the
recursion asks for are two array reads — the table bit, and the
exclusion bit — and a vertex that passes them is selected, whereupon one
depth-capped breadth-first search from `v` finds everything within `r`
of it and a flat sweep sets their exclusion bits.

The one place the program is not literally the recursion is the early
exit. The answer only needs `t` members, so once the counter reaches `t`
the pass stops selecting: it keeps scanning — a while-language with one
loop condition has no `break` — but does nothing per turn. That is the
whole reason the invariant is a *disjunction*: either the counter has
reached `t`, and then the answer is already settled and nothing more is
claimed about the arrays, or it has not, and then the selected set is
exactly the greedy set restricted to the prefix already scanned. The
negative answer is the second branch read at the end of the scan, where
the prefix is everything.

### The exclusion bit and its arithmetic

The marking sweep writes, for each `w`,

    exc[w] := 1 - (1 - exc[w]) * (1 - ((r + 1) - dist[w])),

which is `0` exactly when `exc[w]` was `0` and `dist[w] > r`. Truncated
subtraction does the work of two comparisons and a conjunction, so the
sweep is one store per cell and no branch; and because every
intermediate value is at most `r + 1`, the whole expression asks for no
more room than the search itself already does.

The array `dist` the sweep reads is whatever the search left, and the
specification of the search says only what its thresholds decide, not
how large its entries are — so the sweep's own bound obligation is
answered not from the search's postcondition but from the machine:
`Words` below says that an array has `n` cells and every one of them is
a word, and a run of the bounded semantics preserves that, since every
value it stores came out of a bounded evaluation.

### The cost

`t` searches and one flat scan, which is what the potential

    Φ = (cost of a pick) · (t − cnt) + 25 · (n − v)

pays out: a turn that picks draws on the first term, a turn that does
not draws on the second, and the loop rule of the kit asks for nothing
else. The exported bound is `(74n + 44ns + 60) · t + 36n + 20`.
-/

namespace Lax3Proofs.RamScatter

open Lax3.ColoredGraphs Lax3.ScatterSentences
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs

variable {n ns nt r t : ℕ} {G : SimpleGraph (Fin n)} {M Tab O T : ℕ → ℕ} {X : Set (Fin n)}

/-! ### The recursion the pass implements -/

/-- **The clause lemma of the greedy process.** `GreedyMem` is a
well-founded recursion, so it does not reduce by `rfl`; its equation is
the one fact about it this file uses, and the concept file has already
forced it. -/
theorem greedyMem_iff {v : Fin n} :
    GreedyMem G r X v ↔
      v ∈ X ∧ ∀ u : Fin n, u < v → GreedyMem G r X u → ¬ WithinDist G r u v := by
  rw [Lax3.ScatterSentences.GreedyMem]

/-- The greedy set is the members of the process, which is what its
set-builder says. -/
theorem mem_greedySet {v : Fin n} : v ∈ greedySet G r X ↔ GreedyMem G r X v := Iff.rfl

/-- The vertex *numbered* `a` is one the greedy process selects, in the
arena the mask cuts out. This is `RamBfs`'s `MAdj`/`WD` pattern for the
notion the pass decides. -/
def GSel (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (r : ℕ) (X : Set (Fin n)) (a : ℕ) : Prop :=
  ∃ h : a < n, (⟨a, h⟩ : Fin n) ∈ greedySet (masked G M) r X

theorem GSel.lt {a : ℕ} (h : GSel G M r X a) : a < n := h.1

theorem gsel_of_mem {v : Fin n} (h : v ∈ greedySet (masked G M) r X) :
    GSel G M r X (v : ℕ) := ⟨v.isLt, h⟩

theorem mem_of_gsel {a : ℕ} (h : GSel G M r X a) (ha : a < n) :
    (⟨a, ha⟩ : Fin n) ∈ greedySet (masked G M) r X := h.2

/-- **The recursion, on vertex numbers.** A vertex is selected exactly
when it lies in the table's set and no *earlier selected* vertex is
within `r` of it in the arena — which is, one step at a time, what the
outer scan of the pass tests. -/
theorem gsel_iff {a : ℕ} (ha : a < n) :
    GSel G M r X a ↔
      (⟨a, ha⟩ : Fin n) ∈ X ∧ ∀ u < a, GSel G M r X u → ¬ WD G M r u a := by
  rw [GSel]
  constructor
  · rintro ⟨h', hmem⟩
    obtain ⟨hX, hfar⟩ := greedyMem_iff.1 hmem
    refine ⟨hX, fun u hu hgu hwd => ?_⟩
    exact hfar ⟨u, hgu.lt⟩ (by simpa using hu) (mem_of_gsel hgu hgu.lt)
      ((wd_iff_withinDist hgu.lt ha).1 hwd)
  · rintro ⟨hX, hfar⟩
    refine ⟨ha, greedyMem_iff.2 ⟨hX, fun u hu hgu hwd => ?_⟩⟩
    exact hfar (u : ℕ) (by simpa using hu) ⟨u.isLt, hgu⟩
      ((wd_iff_withinDist u.isLt ha).2 hwd)

/-! ### The prefix of the greedy set

What the scan has selected after `p` turns is the greedy set cut down to
the first `p` vertices, and the three lemmas below are the three ways the
loop invariant moves: it starts empty, it grows by one exactly at a
selected vertex, and at the end it is everything. -/

/-- The vertices the greedy process selects among the first `p`. -/
def selBelow (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (r : ℕ) (X : Set (Fin n)) (p : ℕ) :
    Set (Fin n) :=
  {u | u ∈ greedySet (masked G M) r X ∧ (u : ℕ) < p}

theorem selBelow_subset {p : ℕ} : selBelow G M r X p ⊆ greedySet (masked G M) r X :=
  fun _ h => h.1

theorem selBelow_zero : selBelow G M r X 0 = ∅ := by
  ext u; simp [selBelow]

/-- Scanned to the end, the prefix is the whole greedy set. -/
theorem selBelow_all : selBelow G M r X n = greedySet (masked G M) r X := by
  ext u; exact ⟨fun h => h.1, fun h => ⟨h, u.isLt⟩⟩

/-- A vertex the process passes over does not extend the prefix. -/
theorem selBelow_succ_of_not {p : ℕ} (h : ¬ GSel G M r X p) :
    selBelow G M r X (p + 1) = selBelow G M r X p := by
  ext u
  constructor
  · rintro ⟨hu, hlt⟩
    refine ⟨hu, ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt' | heq
    · exact hlt'
    · exact absurd (heq ▸ gsel_of_mem hu) h
  · rintro ⟨hu, hlt⟩
    exact ⟨hu, by omega⟩

/-- And one it selects extends it by exactly that vertex. -/
theorem selBelow_succ_of_gsel {p : ℕ} (hp : p < n) (h : GSel G M r X p) :
    selBelow G M r X (p + 1) = insert (⟨p, hp⟩ : Fin n) (selBelow G M r X p) := by
  ext u
  simp only [selBelow, Set.mem_setOf_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨hu, hlt⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt' | heq
    · exact Or.inr ⟨hu, hlt'⟩
    · exact Or.inl (Fin.ext heq)
  · rintro (rfl | ⟨hu, hlt⟩)
    · exact ⟨mem_of_gsel h hp, by simp⟩
    · exact ⟨hu, by omega⟩

theorem notMem_selBelow_self {p : ℕ} (hp : p < n) :
    (⟨p, hp⟩ : Fin n) ∉ selBelow G M r X p := fun h => absurd h.2 (by simp)

/-- The prefix grows by one when the process selects. -/
theorem ncard_selBelow_succ_of_gsel {p : ℕ} (hp : p < n) (h : GSel G M r X p) :
    (selBelow G M r X (p + 1)).ncard = (selBelow G M r X p).ncard + 1 := by
  rw [selBelow_succ_of_gsel hp h, Set.ncard_insert_of_notMem (notMem_selBelow_self hp)]

/-- Every prefix count is a lower bound on the answer, which is what
makes the early exit sound. -/
theorem ncard_selBelow_le {p : ℕ} :
    (selBelow G M r X p).ncard ≤ (greedySet (masked G M) r X).ncard :=
  Set.ncard_le_ncard selBelow_subset (Set.toFinite _)

/-! ### Arrays across a phase

The search of `RamBfs` says what its `dist` array decides, not how large
its entries are, and the marking sweep has to *read* them. The missing
fact is not the search's: it is the machine's. A run of the bounded
semantics only ever writes into a cell a value that came out of a
bounded evaluation, so an array of `n` words stays an array of `n`
words, whatever the phase in between did. -/

/-- `Words B n a σ`: the array named `a` is a length-`n` array all of
whose cells are words. -/
def Words (B n : ℕ) (a : String) (σ : Env) : Prop :=
  ∃ g, σ.arrs a = arrOf n g ∧ ∀ i < n, g i < B

theorem Words.arr {B : ℕ} {a : String} {σ : Env} (h : Words B n a σ) :
    ∃ g, σ.arrs a = arrOf n g := by
  obtain ⟨g, hg, -⟩ := h; exact ⟨g, hg⟩

/-- The relation is about one array, so any environment agreeing on it
satisfies it — which is how it crosses a phase that writes elsewhere. -/
theorem Words.of_eq {B : ℕ} {a : String} {σ σ' : Env} (h : Words B n a σ)
    (harr : σ'.arrs a = σ.arrs a) : Words B n a σ' := by
  obtain ⟨g, hg, hgB⟩ := h; exact ⟨g, by rw [harr, hg], hgB⟩

/-- Reading a cell off a named cell function: two names for the same
array agree below its length. -/
theorem Words.cell {B : ℕ} {a : String} {g : ℕ → ℕ} {σ : Env} (h : Words B n a σ)
    (hg : σ.arrs a = arrOf n g) {i : ℕ} (hi : i < n) : g i < B := by
  obtain ⟨g', hg', hgB⟩ := h
  rw [show g i = (arrOf n g).getD i 0 from (getD_arrOf g hi).symm, ← hg, hg',
    getD_arrOf g' hi]
  exact hgB i hi

/-- **An array of words survives any phase.** A run of the bounded
semantics only ever stores a value that came out of a bounded
evaluation, so the induction is the frame rule's with the value bound in
place of the syntax. -/
theorem Words.run {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} {a : String}
    (hrun : Run B c σ σ' K) (h : Words B n a σ) : Words B n a σ' := by
  obtain ⟨k, -, hbs⟩ := hrun
  clear K
  induction hbs with
  | skip => exact h
  | assign _ => exact h
  | @store σ₀ arr i e p v hi he hp =>
      obtain ⟨g, hg, hgB⟩ := h
      by_cases hnm : a = arr
      · subst hnm
        refine ⟨upd g p v, by rw [arrs_setArr, if_pos rfl, hg, set_arrOf_eq_upd],
          fun z hz => ?_⟩
        rw [upd_apply]
        split
        · exact Expr.lt_of_evalB he
        · exact hgB z hz
      · exact ⟨g, by rw [arrs_setArr, if_neg hnm]; exact hg, hgB⟩
  | seq _ _ ih ih' => exact ih' (ih h)
  | ite_true _ _ ih => exact ih h
  | ite_false _ _ ih => exact ih h
  | while_true _ _ _ ih ih' => exact ih' (ih h)
  | while_false _ => exact h
  | read _ => exact h
  | write _ => exact h

/-! ### The marking arithmetic

One store per cell and no branch: truncated subtraction decides
`dist[w] ≤ r`, and a product decides the conjunction with "not already
excluded". -/

/-- The new exclusion bit of a vertex the search put at distance `d`,
given the old bit `e`. -/
def markVal (r e d : ℕ) : ℕ := 1 - (1 - e) * (1 - (r + 1 - d))

/-- It is a bit. -/
theorem markVal_le_one (r e d : ℕ) : markVal r e d ≤ 1 := Nat.sub_le _ _

/-- **What the sweep decides**: the bit stays clear exactly when it was
clear and the search put the vertex out of range. -/
theorem markVal_eq_zero_iff (r e d : ℕ) : markVal r e d = 0 ↔ e = 0 ∧ r < d := by
  have h₁ : 1 - e = 0 ∨ (1 - e = 1 ∧ e = 0) := by omega
  have h₂ : 1 - (r + 1 - d) = 0 ∨ (1 - (r + 1 - d) = 1 ∧ r < d) := by omega
  rw [markVal]
  rcases h₁ with h₁ | ⟨h₁, -⟩ <;> rcases h₂ with h₂ | ⟨h₂, -⟩ <;> rw [h₁, h₂] <;> omega

/-! ### The program

Seven arrays — the five of the search, the table `tab` and the exclusion
bits `exc` — and four scalars of its own: the scan counter `sv`, the
sweep counter `sw`, the count `cnt` of what has been selected, and the
answer `flag`. The radius and the threshold occur in the program text as
literals, for the same reason the search's cap does: both come from the
formula, which the quantifier rank fixes, and not from the input. -/

/-- The new exclusion bit, as an expression: `1 - (1 - exc[sw]) *
(1 - ((r+1) - dist[sw]))`. Every value it produces is at most `r + 1`. -/
def markExpr (r : ℕ) : Expr :=
  .sub (.lit 1)
    (.mul (.sub (.lit 1) (.get "exc" (.var "sw")))
      (.sub (.lit 1) (.sub (.lit (r + 1)) (.get "dist" (.var "sw")))))

/-- Clear every exclusion bit: the kit's array fill. -/
def clearExc : Com :=
  .seq (.assign "sw" (.lit 0))
    (.while (.lt (.var "sw") (.var "n")) (Fill.put "exc" "sw" (.lit 0)))

/-- Mark everything the search just reached: a flat sweep over the
distance array. -/
def markCom (r : ℕ) : Com :=
  .seq (.assign "sw" (.lit 0))
    (.while (.lt (.var "sw") (.var "n")) (Fill.put "exc" "sw" (markExpr r)))

/-- Take the vertex the scan is at: count it, search from it, mark its
ball. -/
def pickCom (r : ℕ) : Com :=
  .seq (.assign "cnt" (.add (.var "cnt") (.lit 1)))
    (.seq (.assign "src" (.var "sv")) (.seq (bfsCom r) (markCom r)))

/-- One turn of the scan, before the counter moves: the two tests of the
recursion, under the guard that stops the pass once it has enough. -/
def scatterBody (r t : ℕ) : Com :=
  .ite (.lt (.var "cnt") (.lit t))
    (.ite (.lt (.lit 0) (.get "tab" (.var "sv")))
      (.ite (.eq (.get "exc" (.var "sv")) (.lit 0)) (pickCom r) .skip)
      .skip)
    .skip

/-- One turn of the scan. -/
def scatterStep (r t : ℕ) : Com :=
  .seq (scatterBody r t) (.assign "sv" (.add (.var "sv") (.lit 1)))

/-- The scan itself. -/
def scatterLoop (r t : ℕ) : Com :=
  .seq (.assign "sv" (.lit 0)) (.while (.lt (.var "sv") (.var "n")) (scatterStep r t))

/-- **The whole pass**: clear, scan, report. The flag is `1` exactly
when the count reached the threshold. -/
def scatterCom (r t : ℕ) : Com :=
  .seq (.assign "cnt" (.lit 0))
    (.seq clearExc
      (.seq (scatterLoop r t)
        (.ite (.lt (.var "cnt") (.lit t)) (.assign "flag" (.lit 0)) (.assign "flag" (.lit 1)))))

/-! ### The marking sweep -/

/-- The invariant of the sweep: the distances are the search's, and the
exclusion array holds the marked values below the counter and the old
ones at and above it. Nothing else in the machine is mentioned, because
the sweep touches nothing else. -/
def MarkInv (n r : ℕ) (E D : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "sw" ≤ n ∧ σ.arrs "dist" = arrOf n D ∧
    ∃ E', σ.arrs "exc" = arrOf n E' ∧
      (∀ j < σ.vars "sw", E' j = markVal r (E j) (D j)) ∧
      (∀ j, σ.vars "sw" ≤ j → j < n → E' j = E j)

/-- One cell of the sweep. The store's value is the marking arithmetic
and its bound obligation is the whole of what the expression asks: no
subexpression exceeds `r + 1`. -/
theorem markPut_spec {B : ℕ} {E D : ℕ → ℕ} (hnB : n < B) (hrB : r + 1 < B)
    (hE : ∀ i < n, E i ≤ 1) (hD : ∀ i < n, D i < B) :
    Spec B (fun σ => MarkInv n r E D σ ∧ σ.vars "sw" < n)
      (Fill.put "exc" "sw" (markExpr r))
      (fun σ σ' => MarkInv n r E D σ' ∧ σ'.vars "sw" = σ.vars "sw" + 1) 19 := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hn, -, hdist, E', hexc, hbelow, habove⟩, hlt⟩ := hσ
  have h1B : 1 < B := by omega
  have hswB : σ.vars "sw" < B := by omega
  have hEsw : E' (σ.vars "sw") = E (σ.vars "sw") := habove _ le_rfl hlt
  have hElt : E (σ.vars "sw") ≤ 1 := hE _ hlt
  have hDlt : D (σ.vars "sw") < B := hD _ hlt
  -- the two reads of the expression
  have hread : (Expr.get "exc" (.var "sw")).evalB B σ = some (E (σ.vars "sw")) :=
    evalB_get (evalB_var hswB) (by rw [hexc, getElem?_arrOf E' hlt, hEsw]) (by omega)
  have hreadD : (Expr.get "dist" (.var "sw")).evalB B σ = some (D (σ.vars "sw")) :=
    evalB_get (evalB_var hswB) (by rw [hdist, getElem?_arrOf D hlt]) hDlt
  -- the arithmetic, from the inside out
  have e₁ : (Expr.sub (.lit 1) (.get "exc" (.var "sw"))).evalB B σ
      = some (1 - E (σ.vars "sw")) :=
    evalB_bin (evalB_lit h1B) hread (by simp; omega)
  have e₂ : (Expr.sub (.lit (r + 1)) (.get "dist" (.var "sw"))).evalB B σ
      = some (r + 1 - D (σ.vars "sw")) :=
    evalB_bin (evalB_lit hrB) hreadD (by simp; omega)
  have e₃ : (Expr.sub (.lit 1) (.sub (.lit (r + 1)) (.get "dist" (.var "sw")))).evalB B σ
      = some (1 - (r + 1 - D (σ.vars "sw"))) :=
    evalB_bin (evalB_lit h1B) e₂ (by simp; omega)
  have hprod : (1 - E (σ.vars "sw")) * (1 - (r + 1 - D (σ.vars "sw"))) ≤ 1 := by
    simpa using Nat.mul_le_mul (Nat.sub_le 1 (E (σ.vars "sw")))
      (Nat.sub_le 1 (r + 1 - D (σ.vars "sw")))
  have e₄ : (Expr.mul (.sub (.lit 1) (.get "exc" (.var "sw")))
        (.sub (.lit 1) (.sub (.lit (r + 1)) (.get "dist" (.var "sw"))))).evalB B σ
      = some ((1 - E (σ.vars "sw")) * (1 - (r + 1 - D (σ.vars "sw")))) :=
    evalB_bin e₁ e₃ (by simp; omega)
  have hval : (markExpr r).evalB B σ = some (markVal r (E (σ.vars "sw")) (D (σ.vars "sw"))) :=
    evalB_bin (evalB_lit h1B) e₄ (by simp; omega)
  refine ⟨_, _, Run.seq
      (Run.store (idx := σ.vars "sw") (evalB_var hswB) hval
        (by rw [hexc, length_arrOf]; exact hlt))
      (Run.assign (v := σ.vars "sw" + 1)
        (evalB_bin (evalB_var (by simpa using hswB)) (evalB_lit h1B) (by simp; omega))),
    by simp [markExpr], ⟨by simpa using hn, by simp; omega, by simpa using hdist, ?_⟩, by simp⟩
  refine ⟨upd E' (σ.vars "sw") (markVal r (E (σ.vars "sw")) (D (σ.vars "sw"))), ?_, ?_, ?_⟩
  · simp [hexc, set_arrOf_eq_upd]
  · intro j hj
    rw [show ((σ.setArr "exc" (σ.vars "sw")
        (markVal r (E (σ.vars "sw")) (D (σ.vars "sw")))).setVar "sw"
        (σ.vars "sw" + 1)).vars "sw" = σ.vars "sw" + 1 by simp] at hj
    by_cases hje : j = σ.vars "sw"
    · rw [hje, upd_self]
    · rw [upd_of_ne _ hje]; exact hbelow j (by omega)
  · intro j hj₁ hj₂
    rw [show ((σ.setArr "exc" (σ.vars "sw")
        (markVal r (E (σ.vars "sw")) (D (σ.vars "sw")))).setVar "sw"
        (σ.vars "sw" + 1)).vars "sw" = σ.vars "sw" + 1 by simp] at hj₁
    rw [upd_of_ne _ (by omega)]
    exact habove j (by omega) hj₂

/-- **The whole sweep.** The counter loop is the kit's; what is left is
the cell function it produces, which is the marking arithmetic applied
pointwise. -/
theorem mark_spec {B : ℕ} {E D : ℕ → ℕ} (hnB : n < B) (hrB : r + 1 < B)
    (hE : ∀ i < n, E i ≤ 1) (hD : ∀ i < n, D i < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.arrs "dist" = arrOf n D ∧ σ.arrs "exc" = arrOf n E)
      (markCom r)
      (fun _ σ' => σ'.arrs "exc" = arrOf n (fun j => markVal r (E j) (D j)) ∧
        σ'.vars "sw" = n)
      (23 * n + 6) := by
  refine ((Spec.forRangeZero "sw" "n" (MarkInv n r E D) n 19 hnB (fun _ hσ => hσ.2.1)
    (fun _ hσ => hσ.1) (markPut_spec hnB hrB hE hD)).pre ?_).post ?_ |>.mono (by omega)
  · rintro σ ⟨hn, hdist, hexc⟩
    exact ⟨by simpa using hn, by simp, by simpa using hdist,
      E, by simpa using hexc, by simp, fun _ _ _ => rfl⟩
  · rintro σ σ' - ⟨⟨-, -, -, E', hexc, hbelow, -⟩, hsw⟩
    refine ⟨?_, hsw⟩
    rw [hexc]
    exact arrOf_congr fun i hi => hbelow i (by omega)

/-! ### The state the scan walks

`Arena` is what the pass never writes to — the block structure, the mask
and the table — together with the two arrays the search owns, which it
does write to but always leaves as arrays of words. `Progress` is the
disjunction the early exit forces. -/

/-- The part of the machine's state the scan carries unchanged. The
target array is at the caller's width `nt` (rebase B5-cont-2), the
block structure's slot count entering only through
`CsrGraph G ns O T` and the cost — this relation never coupled the
two, and the walk below carries `ns ≤ nt` next to the structure. -/
def Arena (B n nt : ℕ) (O T M Tab : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
    σ.arrs "alv" = arrOf n M ∧ σ.arrs "tab" = arrOf n Tab ∧
    Words B n "dist" σ ∧ Words B n "q" σ

/-- **What the scan has established after the vertices before `p`.**
Either the count has reached the threshold, and the answer is settled;
or it has not, and then the count is the size of the greedy set's prefix
and the exclusion bit of a vertex is set exactly when some selected
vertex of the prefix is within `r` of it. -/
def Progress (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (r t : ℕ) (X : Set (Fin n))
    (p : ℕ) (σ : Env) : Prop :=
  (σ.vars "cnt" = t ∧ t ≤ (greedySet (masked G M) r X).ncard) ∨
    (σ.vars "cnt" < t ∧ σ.vars "cnt" = (selBelow G M r X p).ncard ∧
      ∃ E, σ.arrs "exc" = arrOf n E ∧ (∀ w < n, E w ≤ 1) ∧
        ∀ w < n, (E w = 0 ↔ ∀ u < p, GSel G M r X u → ¬ WD G M r u w))

theorem Progress.cnt_le {p : ℕ} {σ : Env} (h : Progress G M r t X p σ) : σ.vars "cnt" ≤ t := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- Both are statements about a handful of names, so both transport. -/
theorem Arena.of_eq {B : ℕ} {σ σ' : Env} (h : Arena B n nt O T M Tab σ)
    (hv : σ'.vars "n" = σ.vars "n") (h₁ : σ'.arrs "off" = σ.arrs "off")
    (h₂ : σ'.arrs "tgt" = σ.arrs "tgt") (h₃ : σ'.arrs "alv" = σ.arrs "alv")
    (h₄ : σ'.arrs "tab" = σ.arrs "tab") (h₅ : σ'.arrs "dist" = σ.arrs "dist")
    (h₆ : σ'.arrs "q" = σ.arrs "q") : Arena B n nt O T M Tab σ' := by
  obtain ⟨e₀, e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  exact ⟨by rw [hv, e₀], by rw [h₁, e₁], by rw [h₂, e₂], by rw [h₃, e₃], by rw [h₄, e₄],
    e₅.of_eq h₅, e₆.of_eq h₆⟩

theorem Arena.setVar {B : ℕ} {σ : Env} {x : String} {v : ℕ} (h : Arena B n nt O T M Tab σ)
    (hx : x ≠ "n") : Arena B n nt O T M Tab (σ.setVar x v) :=
  h.of_eq (by simp [Ne.symm hx]) rfl rfl rfl rfl rfl rfl

theorem Progress.of_eq {p : ℕ} {σ σ' : Env} (h : Progress G M r t X p σ)
    (hc : σ'.vars "cnt" = σ.vars "cnt") (he : σ'.arrs "exc" = σ.arrs "exc") :
    Progress G M r t X p σ' := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂, E, hexc, hE1, hEiff⟩
  · exact Or.inl ⟨by rw [hc, h₁], h₂⟩
  · exact Or.inr ⟨by rw [hc]; exact h₁, by rw [hc]; exact h₂, E, by rw [he, hexc], hE1, hEiff⟩

/-- **A vertex the scan passes over changes nothing.** The prefix does
not grow and no exclusion bit is owed, which is the whole content of a
turn that does not pick. -/
theorem progress_succ_of_not {p : ℕ} {σ : Env} (hg : ¬ GSel G M r X p)
    (h : Progress G M r t X p σ) : Progress G M r t X (p + 1) σ := by
  rcases h with hB | ⟨h₁, h₂, E, hexc, hE1, hEiff⟩
  · exact Or.inl hB
  · refine Or.inr ⟨h₁, by rw [h₂, selBelow_succ_of_not hg], E, hexc, hE1, fun w hw => ?_⟩
    rw [hEiff w hw]
    refine ⟨fun hall u hu hgu => ?_, fun hall u hu hgu => hall u (by omega) hgu⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu' | rfl
    · exact hall u hu' hgu
    · exact absurd hgu hg

/-! ### One turn of the scan -/

/-- What a pick costs: the search, the sweep, and the twenty-four units
of the three tests and the two assignments around them. -/
def pickCost (n ns : ℕ) : ℕ := 74 * n + 44 * ns + 60

/-! The frame of the pass, read off the syntax of the two phases a turn
invokes: neither the search nor the sweep can touch the scan's own
scalars, the block structure, the mask or the table. Each is one `simp`
against concrete program text, and every use of one is a `by simp`
against a concrete name. -/

theorem notMem_bfs_wvars (d : ℕ) (y : String)
    (hy : y ∈ ["n", "src", "sv", "sw", "cnt", "flag"]) : y ∉ (bfsCom d).wvars := by
  fin_cases hy <;>
    simp [bfsCom, initDist, seedSrc, bfsDrain, expandRow, scanSlot, Fill.put, Csr.loadRow,
      Csr.scan, Queue.drain, Com.wvars]

theorem notMem_bfs_warrs (d : ℕ) (a : String)
    (ha : a ∈ ["off", "tgt", "alv", "tab", "exc"]) : a ∉ (bfsCom d).warrs := by
  fin_cases ha <;>
    simp [bfsCom, initDist, seedSrc, bfsDrain, expandRow, scanSlot, Fill.put, Csr.loadRow,
      Csr.scan, Queue.drain, Com.warrs]

theorem notMem_mark_wvars (d : ℕ) (y : String)
    (hy : y ∈ ["n", "src", "sv", "cnt", "flag"]) : y ∉ (markCom d).wvars := by
  fin_cases hy <;> simp [markCom, Com.wvars]

theorem notMem_mark_warrs (d : ℕ) (a : String)
    (ha : a ∈ ["off", "tgt", "alv", "tab", "dist", "q"]) : a ∉ (markCom d).warrs := by
  fin_cases ha <;> simp [markCom, Com.warrs]

/-- **One turn of the scan**, and everything it is worth. The four
control-flow paths are the four the recursion has: the count is already
enough; the table says no; an earlier pick already excluded this vertex;
or the vertex is selected, and then one search and one sweep pay for it.

Nothing is claimed about the cost beyond the two cases the potential
needs — a turn that does not pick is constant, a turn that picks costs a
search and a sweep — because that is all the loop rule asks. -/
theorem step_run {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt)
    (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B) (hTabB : ∀ z < n, Tab z < B)
    (hTab : ∀ v : Fin n, Tab (v : ℕ) ≠ 0 ↔ v ∈ X) {σ : Env}
    (hA : Arena B n nt O T M Tab σ) (hsv : σ.vars "sv" < n)
    (hP : Progress G M r t X (σ.vars "sv") σ) :
    ∃ σ' K, Run B (scatterStep r t) σ σ' K ∧ Arena B n nt O T M Tab σ' ∧
      σ'.vars "sv" = σ.vars "sv" + 1 ∧ Progress G M r t X (σ'.vars "sv") σ' ∧
      ((σ'.vars "cnt" = σ.vars "cnt" ∧ K ≤ 21) ∨
        (σ'.vars "cnt" = σ.vars "cnt" + 1 ∧ σ.vars "cnt" < t ∧ K ≤ pickCost n ns)) := by
  obtain ⟨hn, hoff, htgt, halv, htabA, hdistW, hqW⟩ := id hA
  have hsvB : σ.vars "sv" < B := by omega
  have hcntt : σ.vars "cnt" ≤ t := hP.cnt_le
  have hcntB : σ.vars "cnt" < B := by omega
  -- the assignment that ends every turn
  have hbump : ∀ τ : Env, τ.vars "sv" = σ.vars "sv" →
      Run B (.assign "sv" (.add (.var "sv") (.lit 1))) τ
        (τ.setVar "sv" (σ.vars "sv" + 1)) 4 := by
    intro τ hτ
    refine (Run.assign (v := σ.vars "sv" + 1) ?_).mono (by norm_num)
    rw [← hτ]
    exact evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega)
  -- and what a turn that leaves the machine alone is worth
  have hnopick : ∀ K₁, Run B (scatterBody r t) σ σ K₁ → K₁ ≤ 17 →
      ¬ GSel G M r X (σ.vars "sv") →
      ∃ σ' K, Run B (scatterStep r t) σ σ' K ∧ Arena B n nt O T M Tab σ' ∧
        σ'.vars "sv" = σ.vars "sv" + 1 ∧ Progress G M r t X (σ'.vars "sv") σ' ∧
        ((σ'.vars "cnt" = σ.vars "cnt" ∧ K ≤ 21) ∨
          (σ'.vars "cnt" = σ.vars "cnt" + 1 ∧ σ.vars "cnt" < t ∧ K ≤ pickCost n ns)) := by
    intro K₁ hrun hK hg
    refine ⟨σ.setVar "sv" (σ.vars "sv" + 1), K₁ + 4, hrun.seq (hbump σ rfl),
      hA.setVar (by decide), by simp, ?_, Or.inl ⟨by simp, by omega⟩⟩
    rw [show (σ.setVar "sv" (σ.vars "sv" + 1)).vars "sv" = σ.vars "sv" + 1 by simp]
    exact (progress_succ_of_not hg hP).of_eq (by simp) rfl
  by_cases hlt : σ.vars "cnt" < t
  · -- there is still room, so the two tests of the recursion are asked
    have hc₀ : (Cond.lt (Expr.var "cnt") (.lit t)).evalB B σ = some true := by
      rw [evalB_condLt (evalB_var hcntB) (evalB_lit htB)]; simp [hlt]
    obtain ⟨-, hcnteq, E, hexc, hE1, hEiff⟩ :
        σ.vars "cnt" < t ∧ σ.vars "cnt" = (selBelow G M r X (σ.vars "sv")).ncard ∧
          ∃ E, σ.arrs "exc" = arrOf n E ∧ (∀ w < n, E w ≤ 1) ∧
            ∀ w < n, (E w = 0 ↔ ∀ u < σ.vars "sv", GSel G M r X u → ¬ WD G M r u w) := by
      rcases hP with ⟨h, -⟩ | h
      · omega
      · exact h
    have htabv : (Expr.get "tab" (.var "sv")).evalB B σ = some (Tab (σ.vars "sv")) :=
      evalB_get (evalB_var hsvB) (by rw [htabA, getElem?_arrOf Tab hsv]) (hTabB _ hsv)
    by_cases htab0 : Tab (σ.vars "sv") = 0
    · -- the table says no
      have hc₁ : (Cond.lt (Expr.lit 0) (.get "tab" (.var "sv"))).evalB B σ = some false := by
        rw [evalB_condLt (evalB_lit (by omega)) htabv]; simp [htab0]
      refine hnopick _ (Run.ite_true hc₀ (Run.ite_false hc₁ Run.skip)) (by simp) fun hg => ?_
      exact (hTab ⟨σ.vars "sv", hsv⟩).2 ((gsel_iff hsv).1 hg).1 htab0
    · have hc₁ : (Cond.lt (Expr.lit 0) (.get "tab" (.var "sv"))).evalB B σ = some true := by
        rw [evalB_condLt (evalB_lit (by omega)) htabv]; simp; omega
      have hexcv : (Expr.get "exc" (.var "sv")).evalB B σ = some (E (σ.vars "sv")) :=
        evalB_get (evalB_var hsvB) (by rw [hexc, getElem?_arrOf E hsv])
          (by have := hE1 _ hsv; omega)
      by_cases hE0 : E (σ.vars "sv") = 0
      · -- **the vertex is selected**
        have hgsel : GSel G M r X (σ.vars "sv") :=
          (gsel_iff hsv).2 ⟨(hTab ⟨σ.vars "sv", hsv⟩).1 (by simpa using htab0),
            (hEiff _ hsv).1 hE0⟩
        have hc₂ : (Cond.eq (.get "exc" (.var "sv")) (.lit 0)).evalB B σ = some true := by
          rw [evalB_condEq hexcv (evalB_lit (by omega))]; simp [hE0]
        -- count it
        obtain ⟨τ₁, hτ₁⟩ : ∃ τ, τ = σ.setVar "cnt" (σ.vars "cnt" + 1) := ⟨_, rfl⟩
        have run₁ : Run B (.assign "cnt" (.add (.var "cnt") (.lit 1))) σ τ₁ 4 := by
          rw [hτ₁]
          exact (Run.assign (v := σ.vars "cnt" + 1)
            (evalB_bin (evalB_var hcntB) (evalB_lit (by omega))
              (by simp; omega))).mono (by norm_num)
        have hv₁ : ∀ y, y ≠ "cnt" → τ₁.vars y = σ.vars y := by
          intro y hy; rw [hτ₁]; simp [hy]
        have hcnt₁ : τ₁.vars "cnt" = σ.vars "cnt" + 1 := by rw [hτ₁]; simp
        have ha₁ : τ₁.arrs = σ.arrs := by rw [hτ₁]; simp
        -- name the source
        obtain ⟨τ₂, hτ₂⟩ : ∃ τ, τ = τ₁.setVar "src" (σ.vars "sv") := ⟨_, rfl⟩
        have run₂ : Run B (.assign "src" (.var "sv")) τ₁ τ₂ 2 := by
          rw [hτ₂]
          refine (Run.assign (v := σ.vars "sv") ?_).mono (by norm_num)
          rw [← hv₁ "sv" (by decide)]
          exact evalB_var (by rw [hv₁ "sv" (by decide)]; omega)
        have hv₂ : ∀ y, y ≠ "src" → τ₂.vars y = τ₁.vars y := by
          intro y hy; rw [hτ₂]; simp [hy]
        have ha₂ : τ₂.arrs = τ₁.arrs := by rw [hτ₂]; simp
        have hsrc₂ : τ₂.vars "src" = σ.vars "sv" := by rw [hτ₂]; simp
        -- search from it
        obtain ⟨τ₃, run₃, ⟨D, hDarr, hDspec⟩, hfv₃, hfa₃, -, -⟩ :=
          ((bfs_specW (G := G) (M := M) (O := O) (T := T) (ns := ns) (nt := nt) (d := r)
            (s := σ.vars "sv") hcsr hsv hnB hnsB hnt hrB hMB).frame).run (σ := τ₂)
            ⟨by rw [hv₂ "n" (by decide), hv₁ "n" (by decide), hn], hsrc₂,
              by rw [ha₂, ha₁]; exact hoff, by rw [ha₂, ha₁]; exact htgt,
              by rw [ha₂, ha₁]; exact halv,
              (hdistW.of_eq (by rw [ha₂, ha₁])).arr, (hqW.of_eq (by rw [ha₂, ha₁])).arr⟩
        have hdistW₃ : Words B n "dist" τ₃ := Words.run run₃ (hdistW.of_eq (by rw [ha₂, ha₁]))
        have hqW₃ : Words B n "q" τ₃ := Words.run run₃ (hqW.of_eq (by rw [ha₂, ha₁]))
        -- and mark its ball
        obtain ⟨τ₄, run₄, ⟨hexc₄, -⟩, hfv₄, hfa₄, -, -⟩ :=
          ((mark_spec (n := n) (r := r) (E := E) (D := D) hnB hrB hE1
            (fun i hi => hdistW₃.cell hDarr hi)).frame).run (σ := τ₃)
            ⟨by rw [hfv₃ "n" (notMem_bfs_wvars r "n" (by simp)), hv₂ "n" (by decide),
                hv₁ "n" (by decide), hn], hDarr,
              by rw [hfa₃ "exc" (notMem_bfs_warrs r "exc" (by simp)), ha₂, ha₁]; exact hexc⟩
        -- what the two phases left
        have hsv₄ : τ₄.vars "sv" = σ.vars "sv" := by
          rw [hfv₄ "sv" (notMem_mark_wvars r "sv" (by simp)),
            hfv₃ "sv" (notMem_bfs_wvars r "sv" (by simp)), hv₂ "sv" (by decide),
            hv₁ "sv" (by decide)]
        have hcnt₄ : τ₄.vars "cnt" = σ.vars "cnt" + 1 := by
          rw [hfv₄ "cnt" (notMem_mark_wvars r "cnt" (by simp)),
            hfv₃ "cnt" (notMem_bfs_wvars r "cnt" (by simp)), hv₂ "cnt" (by decide), hcnt₁]
        have harr₄ : ∀ a, a ∈ ["off", "tgt", "alv", "tab"] → τ₄.arrs a = σ.arrs a := by
          intro a ha
          rw [hfa₄ a (notMem_mark_warrs r a (by fin_cases ha <;> simp)),
            hfa₃ a (notMem_bfs_warrs r a (by fin_cases ha <;> simp)), ha₂, ha₁]
        have hA₄ : Arena B n nt O T M Tab τ₄ :=
          ⟨by rw [hfv₄ "n" (notMem_mark_wvars r "n" (by simp)),
              hfv₃ "n" (notMem_bfs_wvars r "n" (by simp)), hv₂ "n" (by decide),
              hv₁ "n" (by decide), hn],
            by rw [harr₄ "off" (by simp)]; exact hoff,
            by rw [harr₄ "tgt" (by simp)]; exact htgt,
            by rw [harr₄ "alv" (by simp)]; exact halv,
            by rw [harr₄ "tab" (by simp)]; exact htabA,
            hdistW₃.of_eq (hfa₄ "dist" (notMem_mark_warrs r "dist" (by simp))),
            hqW₃.of_eq (hfa₄ "q" (notMem_mark_warrs r "q" (by simp)))⟩
        -- **the mathematics of the turn**: the search decides the radius,
        -- so the new bits are exactly the recursion's next clause
        have hDwd : ∀ w, ∀ hw : w < n, (D w ≤ r ↔ WD G M r (σ.vars "sv") w) := by
          intro w hw
          rw [wd_iff_withinDist hsv hw]
          simpa using hDspec ⟨w, hw⟩ r le_rfl
        have hE'iff : ∀ w < n, (markVal r (E w) (D w) = 0 ↔
            ∀ u < σ.vars "sv" + 1, GSel G M r X u → ¬ WD G M r u w) := by
          intro w hw
          rw [markVal_eq_zero_iff, hEiff w hw]
          constructor
          · rintro ⟨hall, hgt⟩ u hu hgu
            rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu' | rfl
            · exact hall u hu' hgu
            · exact fun hwd => absurd ((hDwd w hw).2 hwd) (by omega)
          · intro hall
            refine ⟨fun u hu hgu => hall u (by omega) hgu, ?_⟩
            by_contra hcon
            exact hall (σ.vars "sv") (by omega) hgsel ((hDwd w hw).1 (by omega))
        have hncard : σ.vars "cnt" + 1 = (selBelow G M r X (σ.vars "sv" + 1)).ncard := by
          rw [ncard_selBelow_succ_of_gsel hsv hgsel, hcnteq]
        have hlei : σ.vars "cnt" + 1 ≤ (greedySet (masked G M) r X).ncard := by
          rw [hncard]; exact ncard_selBelow_le
        have hrunPick : Run B (pickCom r) σ τ₄
            (4 + (2 + ((51 * n + 44 * ns + 30) + (23 * n + 6)))) :=
          run₁.seq (run₂.seq (run₃.seq run₄))
        refine ⟨τ₄.setVar "sv" (σ.vars "sv" + 1), _,
          (Run.ite_true hc₀ (Run.ite_true hc₁ (Run.ite_true hc₂ hrunPick))).seq
            (hbump τ₄ hsv₄), hA₄.setVar (by decide), by simp, ?_,
          Or.inr ⟨by simp [hcnt₄], hlt, by simp [pickCost]; omega⟩⟩
        rw [show (τ₄.setVar "sv" (σ.vars "sv" + 1)).vars "sv" = σ.vars "sv" + 1 by simp]
        rcases Nat.lt_or_ge (σ.vars "cnt" + 1) t with hlt' | hge'
        · exact Or.inr ⟨by simp [hcnt₄]; omega, by simp [hcnt₄, ← hncard],
            (fun j => markVal r (E j) (D j)), by simp [hexc₄],
            fun w _ => markVal_le_one .., hE'iff⟩
        · exact Or.inl ⟨by simp [hcnt₄]; omega, by omega⟩
      · -- an earlier pick already excluded it
        have hc₂ : (Cond.eq (.get "exc" (.var "sv")) (.lit 0)).evalB B σ = some false := by
          rw [evalB_condEq hexcv (evalB_lit (by omega))]; simp [hE0]
        refine hnopick _ (Run.ite_true hc₀ (Run.ite_true hc₁ (Run.ite_false hc₂ Run.skip)))
          (by simp) fun hg => hE0 ((hEiff _ hsv).2 ((gsel_iff hsv).1 hg).2)
  · -- the count has reached the threshold: the pass is done selecting
    have hc₀ : (Cond.lt (Expr.var "cnt") (.lit t)).evalB B σ = some false := by
      rw [evalB_condLt (evalB_var hcntB) (evalB_lit htB)]; simp [hlt]
    have hB : σ.vars "cnt" = t ∧ t ≤ (greedySet (masked G M) r X).ncard := by
      rcases hP with h | ⟨h, -⟩
      · exact h
      · omega
    exact ⟨σ.setVar "sv" (σ.vars "sv" + 1), _,
      (Run.ite_false hc₀ Run.skip).seq (hbump σ rfl), hA.setVar (by decide), by simp,
      Or.inl ⟨by simp [hB.1], hB.2⟩, Or.inl ⟨by simp, by simp⟩⟩

/-! ### The scan

The loop rule is the kit's `Spec.while_potential`: a turn that picks
draws on the first term of the potential and a turn that does not draws
on the second, so the whole scan costs one search per pick and a
constant per vertex. -/

/-- The invariant of the scan. -/
def ScatterInv (B n nt : ℕ) (G : SimpleGraph (Fin n)) (M Tab O T : ℕ → ℕ) (r t : ℕ)
    (X : Set (Fin n)) (σ : Env) : Prop :=
  Arena B n nt O T M Tab σ ∧ σ.vars "sv" ≤ n ∧ Progress G M r t X (σ.vars "sv") σ

/-- The potential the scan is paid out of: one pick's worth per pick
still allowed, and a constant per vertex not yet reached. -/
def ScatterPot (n ns t : ℕ) (σ : Env) : ℕ :=
  pickCost n ns * (t - σ.vars "cnt") + 25 * (n - σ.vars "sv")

/-- **The scan.** At the exit the counter is at the end of the carrier,
so the prefix the invariant speaks of is the whole greedy set. -/
theorem loop_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt)
    (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B) (hTabB : ∀ z < n, Tab z < B)
    (hTab : ∀ v : Fin n, Tab (v : ℕ) ≠ 0 ↔ v ∈ X) :
    Spec B (fun σ => ScatterInv B n nt G M Tab O T r t X (σ.setVar "sv" 0))
      (scatterLoop r t)
      (fun _ σ' => Arena B n nt O T M Tab σ' ∧ Progress G M r t X n σ' ∧ σ'.vars "sv" = n)
      (pickCost n ns * t + 25 * n + 6) := by
  have hwhile : Spec B (ScatterInv B n nt G M Tab O T r t X)
      (.while (.lt (.var "sv") (.var "n")) (scatterStep r t))
      (fun _ σ' => ScatterInv B n nt G M Tab O T r t X σ' ∧
        (Cond.lt (Expr.var "sv") (.var "n")).evalB B σ' = some false)
      (pickCost n ns * t + 25 * n + 4) := by
    refine Spec.while_potential _ (ScatterPot n ns t) (fun τ hτ => ?_) (fun τ hτ hb => ?_)
      (fun _ h => h) (fun τ hτ => ?_)
    · exact evalB_condLt_vars (by have := hτ.2.1; omega) (by rw [hτ.1.1]; exact hnB)
    · have hlt : τ.vars "sv" < n := by
        have := lt_of_condLt_true hb; rw [hτ.1.1] at this; exact this
      obtain ⟨τ', K, hrun, hA', hsv', hP', hcase⟩ :=
        step_run hcsr hnB hnsB hnt hrB htB hMB hTabB hTab hτ.1 hlt hτ.2.2
      refine ⟨τ', K, hrun, ⟨hA', by omega, hP'⟩, ?_⟩
      have hn1 : n - τ.vars "sv" = (n - (τ.vars "sv" + 1)) + 1 := by omega
      simp only [ScatterPot, hsv', hn1]
      rcases hcase with ⟨hc, hK⟩ | ⟨hc, hct, hK⟩
      · rw [hc]; simp only [Cond.size, Expr.size]; omega
      · have hn2 : t - τ.vars "cnt" = (t - (τ.vars "cnt" + 1)) + 1 := by omega
        rw [hc, hn2, Nat.mul_succ]
        simp only [Cond.size, Expr.size]
        omega
    · have h₁ : pickCost n ns * (t - τ.vars "cnt") ≤ pickCost n ns * t :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have h₂ : 25 * (n - τ.vars "sv") ≤ 25 * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      simp only [ScatterPot, Cond.size, Expr.size]
      omega
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨σ', hrun, hI', hfalse⟩ := hwhile.run (σ := σ.setVar "sv" 0) hσ
  have hsvn : σ'.vars "sv" = n := by
    have := le_of_condLt_false hfalse
    have h₁ := hI'.1.1
    have h₂ := hI'.2.1
    omega
  exact ⟨σ', _, Run.seq (Run.assign (v := 0) (evalB_lit (by omega))) hrun,
    by simp; omega, hI'.1, hsvn ▸ hI'.2.2, hsvn⟩

/-! ### The pass -/

/-- What the whole pass costs: `t` searches, a sweep apiece, and two
flat passes over the carrier. -/
def scatterCost (n ns t : ℕ) : ℕ := pickCost n ns * t + 36 * n + 20

/-! The clearing pass has the same frame as the marking one: one
counter and one array. -/

theorem notMem_clear_wvars (y : String) (hy : y ∈ ["n", "src", "sv", "cnt", "flag"]) :
    y ∉ clearExc.wvars := by
  fin_cases hy <;> simp [clearExc, Fill.put, Com.wvars]

theorem notMem_clear_warrs (a : String)
    (ha : a ∈ ["off", "tgt", "alv", "tab", "dist", "q"]) : a ∉ clearExc.warrs := by
  fin_cases ha <;> simp [clearExc, Fill.put, Com.warrs]

/-- **The greedy scatter pass.** Handed a block structure for `G`, a
mask, a table of the set `X`, a radius and a threshold, `scatterCom r t`
leaves in `flag` the truth value of the scatter sentence: `1` exactly
when the greedy `r`-scattered subset of `X` in the masked arena has at
least `t` elements. -/
theorem scatter_specW {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt)
    (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B) (hTabB : ∀ z < n, Tab z < B)
    (hTab : ∀ v : Fin n, Tab (v : ℕ) ≠ 0 ↔ v ∈ X) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧
        σ.arrs "tgt" = arrOf nt T ∧ σ.arrs "alv" = arrOf n M ∧ σ.arrs "tab" = arrOf n Tab ∧
        Words B n "dist" σ ∧ Words B n "q" σ ∧ (∃ g, σ.arrs "exc" = arrOf n g))
      (scatterCom r t)
      (fun _ σ' => (σ'.vars "flag" = 1 ↔ t ≤ (greedySet (masked G M) r X).ncard) ∧
        σ'.vars "flag" ≤ 1)
      (scatterCost n ns t) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hn, hoff, htgt, halv, htabA, hdistW, hqW, hexc⟩ := hσ
  -- the counter
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ, τ = σ.setVar "cnt" 0 := ⟨_, rfl⟩
  have run₁ : Run B (.assign "cnt" (.lit 0)) σ τ₁ 2 := by
    rw [hτ₁]; exact (Run.assign (v := 0) (evalB_lit (by omega))).mono (by norm_num)
  have hv₁ : ∀ y, y ≠ "cnt" → τ₁.vars y = σ.vars y := by
    intro y hy; rw [hτ₁]; simp [hy]
  have ha₁ : τ₁.arrs = σ.arrs := by rw [hτ₁]; simp
  have hcnt₁ : τ₁.vars "cnt" = 0 := by rw [hτ₁]; simp
  -- the exclusion bits
  obtain ⟨τ₂, run₂, ⟨⟨g, hg, hg0⟩, -⟩, hfv₂, hfa₂, -, -⟩ :=
    ((Fill.loop_spec B n "exc" "sw" "n" (.lit 0) (fun _ => 0) (by decide) hnB
      (fun _ _ _ _ => evalB_lit (by omega))).frame).run (σ := τ₁)
      ⟨by rw [ha₁]; exact hexc, by rw [hv₁ "n" (by decide)]; exact hn⟩
  have hcnt₂ : τ₂.vars "cnt" = 0 := by
    rw [hfv₂ "cnt" (notMem_clear_wvars "cnt" (by simp)), hcnt₁]
  have hn₂ : τ₂.vars "n" = n := by
    rw [hfv₂ "n" (notMem_clear_wvars "n" (by simp)), hv₁ "n" (by decide), hn]
  have harr₂ : ∀ a, a ∈ ["off", "tgt", "alv", "tab", "dist", "q"] → τ₂.arrs a = σ.arrs a := by
    intro a ha
    rw [hfa₂ a (notMem_clear_warrs a ha), ha₁]
  have hA₂ : Arena B n nt O T M Tab τ₂ :=
    ⟨hn₂, by rw [harr₂ "off" (by simp)]; exact hoff,
      by rw [harr₂ "tgt" (by simp)]; exact htgt, by rw [harr₂ "alv" (by simp)]; exact halv,
      by rw [harr₂ "tab" (by simp)]; exact htabA,
      hdistW.of_eq (harr₂ "dist" (by simp)), hqW.of_eq (harr₂ "q" (by simp))⟩
  -- the scan starts with nothing selected and nothing excluded
  have hI₂ : ScatterInv B n nt G M Tab O T r t X (τ₂.setVar "sv" 0) := by
    refine ⟨hA₂.setVar (by decide), by simp, ?_⟩
    rw [show (τ₂.setVar "sv" 0).vars "sv" = 0 by simp]
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact Or.inl ⟨by simp [hcnt₂], by omega⟩
    · exact Or.inr ⟨by simp [hcnt₂]; omega, by simp [hcnt₂, selBelow_zero],
        g, by simp [hg], fun w hw => by rw [hg0 w hw]; omega,
        fun w hw => by rw [hg0 w hw]; simp⟩
  obtain ⟨τ₃, run₃, hA₃, hP₃, hsv₃⟩ :=
    (loop_spec hcsr hnB hnsB hnt hrB htB hMB hTabB hTab).run (σ := τ₂) hI₂
  -- the answer
  have hcntt : τ₃.vars "cnt" ≤ t := hP₃.cnt_le
  have hcntB : τ₃.vars "cnt" < B := by omega
  have hcv : (Cond.lt (Expr.var "cnt") (.lit t)).evalB B τ₃
      = some (decide (τ₃.vars "cnt" < t)) := evalB_condLt (evalB_var hcntB) (evalB_lit htB)
  by_cases hlt : τ₃.vars "cnt" < t
  · have hns : ¬ t ≤ (greedySet (masked G M) r X).ncard := by
      rcases hP₃ with ⟨h, -⟩ | ⟨-, h, -⟩
      · omega
      · rw [selBelow_all] at h; omega
    exact ⟨τ₃.setVar "flag" 0, _,
      run₁.seq (run₂.seq (run₃.seq (Run.ite_true (by rw [hcv]; simp [hlt])
        (Run.assign (v := 0) (evalB_lit (by omega)))))),
      by simp [scatterCost]; omega, by simp [hns], by simp⟩
  · have hyes : t ≤ (greedySet (masked G M) r X).ncard := by
      rcases hP₃ with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · omega
    exact ⟨τ₃.setVar "flag" 1, _,
      run₁.seq (run₂.seq (run₃.seq (Run.ite_false (by rw [hcv]; simp [hlt])
        (Run.assign (v := 1) (evalB_lit (by omega)))))),
      by simp [scatterCost]; omega, by simp [hyes], by simp⟩

/-- **The greedy scatter pass at the pinned target array** — the frozen
export, which is the widened walk at `nt = ns`. Nothing is re-walked:
the two preconditions are the same proposition there, and neither the
answer nor `scatterCost` ever mentioned the width. -/
theorem scatter_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hrB : r + 1 < B) (htB : t < B) (hMB : ∀ z < n, M z < B) (hTabB : ∀ z < n, Tab z < B)
    (hTab : ∀ v : Fin n, Tab (v : ℕ) ≠ 0 ↔ v ∈ X) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.arrs "off" = arrOf (n + 1) O ∧
        σ.arrs "tgt" = arrOf ns T ∧ σ.arrs "alv" = arrOf n M ∧ σ.arrs "tab" = arrOf n Tab ∧
        Words B n "dist" σ ∧ Words B n "q" σ ∧ (∃ g, σ.arrs "exc" = arrOf n g))
      (scatterCom r t)
      (fun _ σ' => (σ'.vars "flag" = 1 ↔ t ≤ (greedySet (masked G M) r X).ncard) ∧
        σ'.vars "flag" ≤ 1)
      (scatterCost n ns t) :=
  scatter_specW hcsr hnB hnsB le_rfl hrB htB hMB hTabB hTab

section Falsification

/-! The widening's one authored delta in this file is `Arena`'s `tgt`
clause, and its refutable reading is that it is no delta — that the
pass's arena at a width above the slot count is the arena at the slot
count. It is not: an empty arena in a length-one target array already
separates them. -/

/-- No vertices, no slots, and one cell in `tgt`. -/
private def wideArenaEnv : Env where
  vars := fun _ => 0
  arrs := fun a => if a = "off" ∨ a = "tgt" then [0] else []
  inp := []
  out := []

-- the arena holds of it at width `1` …
example : Arena 1 0 1 (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) wideArenaEnv :=
  ⟨rfl, by simp [wideArenaEnv, arrOf], by simp [wideArenaEnv, arrOf],
    by simp [wideArenaEnv, arrOf], by simp [wideArenaEnv, arrOf],
    ⟨fun _ => 0, by simp [wideArenaEnv, arrOf], by simp⟩,
    ⟨fun _ => 0, by simp [wideArenaEnv, arrOf], by simp⟩⟩

-- … and is **refuted** at the slot count `0`, at every target function.
example : ¬ ∃ T, Arena 1 0 0 (fun _ => 0) T (fun _ => 0) (fun _ => 0) wideArenaEnv := by
  rintro ⟨T, -, -, htgt, -⟩
  simp [wideArenaEnv, arrOf] at htgt

end Falsification

/-! ### The worked example

House discipline: what the specification says is also *seen*. The arena
is the path `0—1—2—3—4`, every vertex alive, and the radius is `1`, so
the greedy process takes every other vertex. The table bit of vertex `2`
is the parameter, and it moves the answer: with `2` in the set the
process takes `0`, `2`, `4` and the value is three, and with `2` out of
it the process takes `0` and then — vertex `1` being excluded by `0`,
and vertex `3` being two steps away from it — takes `3`, and the value
is two. Each is read at the threshold it meets and at the one above it. -/

namespace Demo

/-- The offsets of the path `0—1—2—3—4`. -/
def demoOff : Com :=
  .seq (.store "off" (.lit 0) (.lit 0))
    (.seq (.store "off" (.lit 1) (.lit 1))
      (.seq (.store "off" (.lit 2) (.lit 3))
        (.seq (.store "off" (.lit 3) (.lit 5))
          (.seq (.store "off" (.lit 4) (.lit 7)) (.store "off" (.lit 5) (.lit 8))))))

/-- Its targets: `1 | 0 2 | 1 3 | 2 4 | 3`. -/
def demoTgt : Com :=
  .seq (.store "tgt" (.lit 0) (.lit 1))
    (.seq (.store "tgt" (.lit 1) (.lit 0))
      (.seq (.store "tgt" (.lit 2) (.lit 2))
        (.seq (.store "tgt" (.lit 3) (.lit 1))
          (.seq (.store "tgt" (.lit 4) (.lit 3))
            (.seq (.store "tgt" (.lit 5) (.lit 2))
              (.seq (.store "tgt" (.lit 6) (.lit 4)) (.store "tgt" (.lit 7) (.lit 3))))))))

/-- Nothing is killed. -/
def demoAlv : Com :=
  .seq (.store "alv" (.lit 0) (.lit 1))
    (.seq (.store "alv" (.lit 1) (.lit 1))
      (.seq (.store "alv" (.lit 2) (.lit 1))
        (.seq (.store "alv" (.lit 3) (.lit 1)) (.store "alv" (.lit 4) (.lit 1)))))

/-- The table, with the bit of vertex `2` left open. -/
def demoTab (b2 : ℕ) : Com :=
  .seq (.store "tab" (.lit 0) (.lit 1))
    (.seq (.store "tab" (.lit 1) (.lit 1))
      (.seq (.store "tab" (.lit 2) (.lit b2))
        (.seq (.store "tab" (.lit 3) (.lit 1)) (.store "tab" (.lit 4) (.lit 1)))))

/-- Five vertices, eight slots. -/
def demoSetup (b2 : ℕ) : Com :=
  .seq (.assign "n" (.lit 5)) (.seq demoOff (.seq demoTgt (.seq demoAlv (demoTab b2))))

/-- Build the arena, run the pass, report the flag. -/
def demoWatched (b2 r t : ℕ) : Com :=
  .seq (demoSetup b2) (.seq (scatterCom r t) (.write (.var "flag")))

/-- Sixteen scalars, the seven arrays, four temporaries. -/
def demoLayout : Lax13Proofs.Compile.Layout :=
  ⟨["n", "src", "i", "head", "tail", "sc", "v", "w", "dv", "dn", "j", "jend",
    "sv", "sw", "cnt", "flag"],
   ["off", "tgt", "alv", "dist", "q", "tab", "exc"], 4⟩

/-- The machine program. -/
def demoProg (b2 r t : ℕ) : Lax13.Ram.Program :=
  Lax13Proofs.Compile.compileProgram demoLayout (demoWatched b2 r t)

/-- The layout covers the block, so the compilation is the one the
simulation theorem is about and not an accident. -/
theorem demoWatched_ok (b2 r t : ℕ) :
    Lax13Proofs.Compile.Com.Ok demoLayout (demoWatched b2 r t) := by
  simp [demoWatched, demoSetup, demoOff, demoTgt, demoAlv, demoTab, scatterCom, clearExc,
    scatterLoop, scatterStep, scatterBody, pickCom, markCom, markExpr, bfsCom, initDist,
    seedSrc, bfsDrain, expandRow, scanSlot, Fill.put, Csr.loadRow, Csr.scan, Queue.drain,
    demoLayout, Lax13Proofs.Compile.Com.Ok, Lax13Proofs.Compile.Cond.Ok,
    Lax13Proofs.Compile.condExpr, Lax13Proofs.Compile.Expr.Ok]

/-- Run it at a word length that holds every number this arena
produces. -/
def demoRun (b2 r t : ℕ) : Option (List ℕ × ℕ) :=
  runOut 16 20000 (demoProg b2 r t) (Lax13.Ram.initState []) 0

-- the whole table, radius `1`: the process takes `0`, `2`, `4`, so the
-- value is three — met at the threshold three and missed at four
#guard demoRun 1 1 3 = some ([1], 3859)
#guard demoRun 1 1 4 = some ([0], 3858)
-- and a threshold of zero is met by the empty set, before any search
#guard demoRun 1 1 0 = some ([1], 573)
-- vertex `2` out of the table: the process takes `0` and then `3`, so
-- the value is two
#guard demoRun 0 1 2 = some ([1], 2801)
#guard demoRun 0 1 3 = some ([0], 2849)

/-! And the arithmetic on the other side of the abstraction: at radius
one, a vertex is newly excluded at distance `0` or `1`, stays clear at
distance `2`, and an excluded vertex stays excluded. -/

#guard [markVal 1 0 0, markVal 1 0 1, markVal 1 0 2, markVal 1 1 2] = [1, 1, 0, 1]

end Demo

end Lax3Proofs.RamScatter
