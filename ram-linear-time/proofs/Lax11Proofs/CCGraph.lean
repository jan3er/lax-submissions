import Lax11Proofs.CC
import Lax11Proofs.Labels

/-!
The graph-theoretic facts the search proof consumes, and nothing else.

Two groups. The first is about the labelling: it is the least vertex of
the component, so it is at most the vertex itself, it is *attained* —
the least vertex is reachable, which is why an unlabelled vertex in the
sweep is the root of its own component — and it is constant on
components. The second is about the encoding read as arrays of numbers:
the offsets are nondecreasing all the way up, so every block lies
inside the target array, and adjacency is membership in a block.

Everything here is stated for numbers rather than for `Fin n`, because
that is what an array index is. `lbl G w` is the label of the vertex
numbered `w`, and `n` — not a vertex — where `w` is out of range, which
is the same marker the program uses for "unvisited".
-/

namespace Lax11Proofs.CC

open Lax11.GraphEncoding Lax11.ConnectedComponents Lax11Proofs.Labels

variable {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}

/-! ### The labelling -/

/-- The label of the vertex numbered `w`. -/
noncomputable def lbl (G : SimpleGraph (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then label G ⟨w, h⟩ else n

theorem lbl_eq {w : ℕ} (h : w < n) : lbl G w = label G ⟨w, h⟩ := dif_pos h

/-- The set of numbers of vertices reaching `v` is nonempty: `v`
reaches itself. -/
theorem label_mem (v : Fin n) : ∃ u : Fin n, G.Reachable u v ∧ (u : ℕ) = label G v :=
  Nat.sInf_mem (⟨v, v, SimpleGraph.Reachable.refl v, rfl⟩ :
    (Fin.val '' {u : Fin n | G.Reachable u v}).Nonempty)

/-- A vertex is at most its own label's witness: the label is at most
the vertex. -/
theorem label_le (v : Fin n) : label G v ≤ (v : ℕ) :=
  Nat.sInf_le ⟨v, SimpleGraph.Reachable.refl v, rfl⟩

theorem lbl_le {w : ℕ} (h : w < n) : lbl G w ≤ w := by
  rw [lbl_eq h]; exact label_le _

theorem lbl_lt {w : ℕ} (h : w < n) : lbl G w < n := lt_of_le_of_lt (lbl_le h) h

/-- The label is attained: the least vertex of the component of `w` is
reachable from `w`. -/
theorem reachable_lbl {w : ℕ} (h : w < n) :
    G.Reachable ⟨lbl G w, lbl_lt h⟩ ⟨w, h⟩ := by
  obtain ⟨u, hu, huv⟩ := label_mem (G := G) ⟨w, h⟩
  have hval : (⟨lbl G w, lbl_lt h⟩ : Fin n) = u := by
    apply Fin.ext
    show lbl G w = (u : ℕ)
    rw [lbl_eq h, huv]
  rw [hval]; exact hu

/-- The label is constant on a component. -/
theorem label_eq_of_reachable {a b : Fin n} (hab : G.Reachable a b) :
    label G a = label G b := by
  have : {u : Fin n | G.Reachable u a} = {u : Fin n | G.Reachable u b} := by
    ext u
    exact ⟨fun h => h.trans hab, fun h => h.trans hab.symm⟩
  simp only [label, this]

theorem lbl_eq_of_reachable {a b : ℕ} (ha : a < n) (hb : b < n)
    (hab : G.Reachable ⟨a, ha⟩ ⟨b, hb⟩) : lbl G a = lbl G b := by
  rw [lbl_eq ha, lbl_eq hb]; exact label_eq_of_reachable hab

/-- A property that passes along edges passes along reachability. -/
theorem reachable_closed {P : Fin n → Prop} (hcl : ∀ a b : Fin n, G.Adj a b → P a → P b)
    {a b : Fin n} (h : G.Reachable a b) : P a → P b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact id
  | cons hadj _ ih => exact fun ha => ih (hcl _ _ hadj ha)

/-! ### Adjacency and reachability between vertex *numbers*

The search works with array indices, so it wants adjacency and
reachability as relations on `ℕ` that carry the range condition
themselves. -/

/-- The vertices numbered `a` and `b` are adjacent. -/
def Adjn (G : SimpleGraph (Fin n)) (a b : ℕ) : Prop :=
  ∃ (ha : a < n) (hb : b < n), G.Adj ⟨a, ha⟩ ⟨b, hb⟩

/-- The vertex numbered `b` is reachable from the one numbered `a`. -/
def Rch (G : SimpleGraph (Fin n)) (a b : ℕ) : Prop :=
  ∃ (ha : a < n) (hb : b < n), G.Reachable ⟨a, ha⟩ ⟨b, hb⟩

theorem Rch.lt_left {a b : ℕ} (h : Rch G a b) : a < n := h.1

theorem Rch.lt_right {a b : ℕ} (h : Rch G a b) : b < n := h.2.1

theorem Rch.refl {a : ℕ} (h : a < n) : Rch G a a := ⟨h, h, .refl _⟩

theorem Rch.of_adjn {a b : ℕ} (h : Adjn G a b) : Rch G a b :=
  ⟨h.1, h.2.1, h.2.2.reachable⟩

theorem Rch.trans_adjn {a b c : ℕ} (h : Rch G a b) (hbc : Adjn G b c) : Rch G a c := by
  obtain ⟨ha, hb, hab⟩ := h
  obtain ⟨hb', hc, hbc'⟩ := hbc
  exact ⟨ha, hc, hab.trans hbc'.reachable⟩

/-- The label is constant on a component. -/
theorem lbl_eq_of_rch {a b : ℕ} (h : Rch G a b) : lbl G a = lbl G b := by
  obtain ⟨ha, hb, hab⟩ := h
  rw [lbl_eq ha, lbl_eq hb]; exact label_eq_of_reachable hab

/-- The least vertex of the component of `w` reaches `w`. -/
theorem rch_lbl {w : ℕ} (h : w < n) : Rch G (lbl G w) w :=
  ⟨lbl_lt h, h, reachable_lbl h⟩

/-- A property that passes along edges passes along reachability. -/
theorem rch_closed {P : ℕ → Prop} (hcl : ∀ a b, Adjn G a b → P a → P b)
    {a b : ℕ} (h : Rch G a b) : P a → P b := by
  obtain ⟨ha, hb, hab⟩ := h
  exact reachable_closed (P := fun z : Fin n => P z)
    (fun c d hcd hc => hcl c d ⟨c.2, d.2, by simpa using hcd⟩ hc) hab

/-! ### The encoding, as arrays of numbers -/

/-- The offsets are nondecreasing all the way up, not just by one
step. -/
theorem offset_mono' (hx : EncodesGraph x n G) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    offset x i ≤ offset x j := by
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst this; exact le_rfl
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact le_trans (ih (by omega) (by omega)) (hx.offset_mono j (by omega))
      · have : i = j + 1 := by omega
        subst this; exact le_rfl

/-- Every offset is inside the target array. -/
theorem offset_le (hx : EncodesGraph x n G) {i : ℕ} (hi : i ≤ n) :
    offset x i ≤ 2 * edgeCount x := by
  rw [← hx.offset_last]; exact offset_mono' hx hi le_rfl

/-- The block of `a` lists exactly the neighbours of `a`. -/
theorem adj_iff' (hx : EncodesGraph x n G) {a b : ℕ} (ha : a < n) (hb : b < n) :
    G.Adj ⟨a, ha⟩ ⟨b, hb⟩ ↔
      ∃ j, offset x a ≤ j ∧ j < offset x (a + 1) ∧ target x j = b :=
  hx.adj_iff ⟨a, ha⟩ ⟨b, hb⟩

/-- Everything a block names is a vertex. -/
theorem target_lt' (hx : EncodesGraph x n G) {a j : ℕ} (ha : a < n)
    (h₂ : j < offset x (a + 1)) : target x j < n :=
  hx.target_lt j (lt_of_lt_of_le h₂ (offset_le hx (by omega)))

/-- A slot of a block names a neighbour. -/
theorem adjn_of_slot (hx : EncodesGraph x n G) {a j : ℕ} (ha : a < n)
    (h₁ : offset x a ≤ j) (h₂ : j < offset x (a + 1)) : Adjn G a (target x j) :=
  ⟨ha, target_lt' hx ha h₂, (adj_iff' hx ha (target_lt' hx ha h₂)).2 ⟨j, h₁, h₂, rfl⟩⟩

/-- Conversely, every neighbour is named by a slot of the block. -/
theorem slot_of_adjn (hx : EncodesGraph x n G) {a b : ℕ} (h : Adjn G a b) :
    ∃ j, offset x a ≤ j ∧ j < offset x (a + 1) ∧ target x j = b := by
  obtain ⟨ha, hb, hab⟩ := h
  exact (adj_iff' hx ha hb).1 hab

/-! ### How much of the target array a set of blocks takes up

The cost of the search is paid out of the length of the target array,
so the proof needs to know that the blocks of distinct vertices do not
overlap. They do not, because the offsets are nondecreasing: the blocks
tile the array. -/

/-- The size of the block of the vertex `v`. -/
def deg (x : List ℕ) (v : ℕ) : ℕ := offset x (v + 1) - offset x v

/-- The blocks of the first `k` vertices tile the target array up to
the `k`-th offset. -/
theorem sum_deg (hx : EncodesGraph x n G) {k : ℕ} (hk : k ≤ n) :
    ∑ i ∈ Finset.range k, deg x i = offset x k - offset x 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h₁ : offset x 0 ≤ offset x k := offset_mono' hx (Nat.zero_le _) (by omega)
      have h₂ : offset x k ≤ offset x (k + 1) := hx.offset_mono k (by omega)
      rw [Finset.sum_range_succ, ih (by omega)]
      simp only [deg]; omega

/-- The blocks of a set of distinct vertices fit inside the target
array. -/
theorem sum_deg_le (hx : EncodesGraph x n G) {s : Finset ℕ} (hs : ∀ v ∈ s, v < n) :
    ∑ v ∈ s, deg x v ≤ 2 * edgeCount x := by
  have hsub : s ⊆ Finset.range n := fun v hv => Finset.mem_range.2 (hs v hv)
  calc ∑ v ∈ s, deg x v ≤ ∑ v ∈ Finset.range n, deg x v :=
        Finset.sum_le_sum_of_subset hsub
    _ = offset x n - offset x 0 := sum_deg hx le_rfl
    _ ≤ 2 * edgeCount x := by rw [hx.offset_last]; omega

/-- The blocks of the vertices the queue holds fit inside the target
array — the form in which the search uses it, with the queue's
injectivity standing in for distinctness. -/
theorem sum_deg_queue (hx : EncodesGraph x n G) {Q : ℕ → ℕ} {k : ℕ}
    (hQ : ∀ i < k, Q i < n) (hinj : ∀ i < k, ∀ j < k, Q i = Q j → i = j) :
    ∑ i ∈ Finset.range k, deg x (Q i) ≤ 2 * edgeCount x := by
  have himg : ∑ v ∈ (Finset.range k).image Q, deg x v = ∑ i ∈ Finset.range k, deg x (Q i) :=
    Finset.sum_image
      (fun i hi j hj h => hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) h)
  rw [← himg]
  refine sum_deg_le hx fun v hv => ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
  exact hQ i (Finset.mem_range.1 hi)

end Lax11Proofs.CC
