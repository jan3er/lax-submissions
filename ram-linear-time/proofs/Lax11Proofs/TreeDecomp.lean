import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
Tree decompositions, and the set theory the fold consumes.

This is the pure graph theory of Courcelle's theorem: no programs, no
logic, no types — only bags, subtrees, and the four facts that make a
bottom-up fold over a decomposition well founded. Everything is stated
in the shape the rest of the development needs, which is the *machine's*
shape (plan decision C6): the nodes are the numbers `0, …, N-1`, the
parent map is a function `ℕ → ℕ` with `i < par i` below the root, the
root is `N - 1` and is its own parent, and the bags are a function
`ℕ → Finset (Fin n)`. So the same `par` that the tree-fold schema folds
over is the one the decomposition lemmas talk about, and no translation
layer stands between the math and the program.

Validity is four conditions: the bags cover the vertices, every edge sits
inside some bag, and — the only one with content — the *occurrence set*
of a vertex is connected in the tree. Connectivity is stated in its
rooted form, which is one clause rather than a path predicate: if `v`
occurs at `i` and again at some higher node, then `v` occurs at `i`'s
parent. Climbing that clause is what every lemma below does.

The objects:

* `Desc par s t` — `s` is a descendant of `t` (or `t` itself), i.e.
  iterating the parent map from `s` reaches `t`. Being an ancestor is
  therefore *not* a separate definition, and the tree structure enters
  through one lemma, `Valid.desc_of_desc_of_le`: two ancestors of the
  same node are comparable.
* `top N bags v` — the highest node whose bag contains `v`, by
  `Nat.findGreatest`, so it computes. Coherence makes it the root of
  `v`'s occurrence set (`Valid.desc_top`), which is the uniqueness that
  the driver's first label phase needs (plan C7a(a)).
* `subtree N par bags t` — the union of the bags in `t`'s subtree, as a
  `Set (Fin n)`, because that is what the type algebra takes as a
  region.

The four facts, in the order they are used downstream:

1. `Valid.mem_subtree_iff` — a subtree is its bag together with the
   subtrees of its children. This is the induction step of the fold.
2. `Valid.mem_bags_of_out` (the exit lemma) and its corollary
   `Valid.separation` — a vertex of `subtree c` that is also seen from
   outside lies in `B_c` *and* in `B_{par c}`. Hence no edge leaves a
   subtree except through its bag, and the gluing hypothesis of the
   composition lemma holds in the form that file wants it
   (`Valid.sep_glue`).
3. `Valid.sibling` — the subtrees of two incomparable nodes meet only
   in both bags, so sibling *interiors* are disjoint.
4. `Valid.mem_bags_min_top` and `Valid.mem_bags_par_of_edge` — the two
   coherence lemmas plan C7a owes the label pass: an edge is present at
   the lower of its endpoints' top nodes, and an edge inside a bag whose
   top node is elsewhere is also inside the parent's bag. Together they
   are why bag adjacency can be computed in linear total time instead of
   `Σ_t Σ_{u ∈ B_t} deg u`.
-/

namespace Lax11Proofs.TreeDecomp

variable {n N : ℕ} {par : ℕ → ℕ} {bags : ℕ → Finset (Fin n)}
  {G : SimpleGraph (Fin n)} {c c₁ c₂ i s t w : ℕ} {u v : Fin n}

/-! ### Descendants

The tree order, as the reflexive-transitive closure of the parent map —
spelled as iteration, which is the only form the proofs below use. -/

/-- `s` is a descendant of `t`, or `t` itself: iterating the parent map
from `s` reaches `t`. -/
def Desc (par : ℕ → ℕ) (s t : ℕ) : Prop := ∃ k, par^[k] s = t

theorem Desc.refl (par : ℕ → ℕ) (s : ℕ) : Desc par s s := ⟨0, rfl⟩

theorem Desc.trans (h₁ : Desc par s t) (h₂ : Desc par t w) : Desc par s w := by
  obtain ⟨k, rfl⟩ := h₁
  obtain ⟨l, rfl⟩ := h₂
  exact ⟨l + k, by rw [Function.iterate_add_apply]⟩

/-- One step up. -/
theorem Desc.step (par : ℕ → ℕ) (s : ℕ) : Desc par s (par s) := ⟨1, rfl⟩

theorem Desc.of_par (h : Desc par (par s) t) : Desc par s t := (Desc.step par s).trans h

/-- A descendant that is not the node itself is a descendant of one of
its parent's descendants — the first step of the climb. -/
theorem Desc.par_of_ne (h : Desc par s t) (hne : s ≠ t) : Desc par (par s) t := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero => exact absurd hk hne
  | succ k => exact ⟨k, by rwa [Function.iterate_succ_apply] at hk⟩

/-! ### Valid decompositions

The definition, in the numbering the encoding uses (plan C6): children
before parents, root `N - 1`, and — the one convention that is a choice
rather than a fact — the root is its own parent, so that `par` is total
on the nodes and `Desc` never escapes the tree. It costs no generality
(the fold reads `children par i = {c < i | par c = i}`, and the root is
not below itself, so a self-parenting root has no extra child), and it
is what the encoded parent array will hold at position `N - 1`. -/

/-- A valid tree decomposition of `G` with `N` nodes: `par` is a rooted
tree in the C6 numbering, the bags cover the vertices and the edges, and
the occurrences of each vertex are connected. -/
structure Valid (G : SimpleGraph (Fin n)) (N : ℕ) (par : ℕ → ℕ)
    (bags : ℕ → Finset (Fin n)) : Prop where
  /-- There is at least one node. -/
  pos : 0 < N
  /-- Children come before their parents. -/
  par_gt : ∀ i, i + 1 < N → i < par i
  /-- Parents are nodes. -/
  par_mem : ∀ i, i + 1 < N → par i < N
  /-- The root `N - 1` is its own parent. -/
  par_root : par (N - 1) = N - 1
  /-- Vertex coverage: every vertex is in some bag. -/
  vertex_cover : ∀ v : Fin n, ∃ t, t < N ∧ v ∈ bags t
  /-- Edge coverage: every edge is inside some bag. -/
  edge_cover : ∀ u v : Fin n, G.Adj u v → ∃ t, t < N ∧ u ∈ bags t ∧ v ∈ bags t
  /-- Coherence: if `v` occurs at `i` and again higher up, it occurs at
  `i`'s parent. Equivalently — and this is the usual phrasing — the set
  of nodes whose bag contains `v` is connected in the tree. -/
  coherent : ∀ (v : Fin n) (i j : ℕ), i < j → j < N → v ∈ bags i → v ∈ bags j →
    v ∈ bags (par i)

/-- The decomposition has width at most `k`. -/
def Width (N : ℕ) (bags : ℕ → Finset (Fin n)) (k : ℕ) : Prop :=
  ∀ t < N, (bags t).card ≤ k + 1

namespace Valid

/-! ### The parent map on nodes -/

theorem le_par (hV : Valid G N par bags) (h : i < N) : i ≤ par i := by
  rcases Nat.lt_or_ge (i + 1) N with h' | h'
  · exact (hV.par_gt i h').le
  · have hi : i = N - 1 := by omega
    rw [hi, hV.par_root]

theorem par_lt (hV : Valid G N par bags) (h : i < N) : par i < N := by
  rcases Nat.lt_or_ge (i + 1) N with h' | h'
  · exact hV.par_mem i h'
  · have hi : i = N - 1 := by omega
    rw [hi, hV.par_root]; omega

theorem iterate_lt (hV : Valid G N par bags) (h : i < N) (k : ℕ) : par^[k] i < N := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply']; exact hV.par_lt ih

theorem le_iterate (hV : Valid G N par bags) (h : i < N) (k : ℕ) : i ≤ par^[k] i := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (hV.le_par (hV.iterate_lt h k))

theorem iterate_mono (hV : Valid G N par bags) (h : i < N) {k l : ℕ} (hkl : k ≤ l) :
    par^[k] i ≤ par^[l] i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact hV.le_iterate (hV.iterate_lt h k) d

/-! ### The tree order -/

theorem desc_le (hV : Valid G N par bags) (h : s < N) (hd : Desc par s t) : s ≤ t := by
  obtain ⟨k, rfl⟩ := hd; exact hV.le_iterate h k

theorem desc_lt (hV : Valid G N par bags) (h : s < N) (hd : Desc par s t) : t < N := by
  obtain ⟨k, rfl⟩ := hd; exact hV.iterate_lt h k

theorem desc_antisymm (hV : Valid G N par bags) (h : s < N)
    (h₁ : Desc par s t) (h₂ : Desc par t s) : s = t :=
  le_antisymm (hV.desc_le h h₁) (hV.desc_le (hV.desc_lt h h₁) h₂)

/-- **Two ancestors of the same node are comparable.** This is the only
place the tree shape of `par` is used, and every case analysis below
goes through it. -/
theorem desc_of_desc_of_le (hV : Valid G N par bags) (hc : c < N)
    (h₁ : Desc par c s) (h₂ : Desc par c t) (hst : s ≤ t) : Desc par s t := by
  obtain ⟨k, rfl⟩ := h₁
  obtain ⟨l, rfl⟩ := h₂
  rcases Nat.le_total k l with hkl | hlk
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
    exact ⟨d, by rw [Nat.add_comm, Function.iterate_add_apply]⟩
  · have hle := hV.iterate_mono hc hlk
    have : par^[k] c = par^[l] c := le_antisymm hst hle
    rw [this]
    exact Desc.refl _ _

/-- Comparability in the form the case analyses want: two ancestors of a
node are related one way or the other. -/
theorem desc_total (hV : Valid G N par bags) (hc : c < N)
    (h₁ : Desc par c s) (h₂ : Desc par c t) : Desc par s t ∨ Desc par t s := by
  rcases Nat.le_total s t with h | h
  · exact Or.inl (hV.desc_of_desc_of_le hc h₁ h₂ h)
  · exact Or.inr (hV.desc_of_desc_of_le hc h₂ h₁ h)

private theorem desc_root_aux (hV : Valid G N par bags) :
    ∀ (d i : ℕ), N - 1 - i ≤ d → i < N → Desc par i (N - 1) := by
  intro d
  induction d with
  | zero =>
      intro i hle hi
      have : i = N - 1 := by omega
      rw [this]
      exact Desc.refl _ _
  | succ d ih =>
      intro i hle hi
      rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt hi) with he | hlt
      · rw [he]; exact Desc.refl _ _
      · have h1 : i + 1 < N := by omega
        have h2 : i < par i := hV.par_gt i h1
        exact Desc.of_par (ih (par i) (by omega) (hV.par_mem i h1))

/-- Every node is a descendant of the root. -/
theorem desc_root (hV : Valid G N par bags) (hi : i < N) : Desc par i (N - 1) :=
  desc_root_aux hV (N - 1 - i) i le_rfl hi

/-- The child of `t` through which a strict descendant reaches it. -/
theorem exists_child (hV : Valid G N par bags) (hs : s < N) (hd : Desc par s t)
    (hne : s ≠ t) : ∃ c, c < t ∧ par c = t ∧ Desc par s c := by
  obtain ⟨k, hk⟩ := hd
  induction k generalizing s with
  | zero => exact absurd hk hne
  | succ k ih =>
      rw [Function.iterate_succ_apply] at hk
      by_cases hpt : par s = t
      · refine ⟨s, ?_, hpt, Desc.refl _ _⟩
        have := hV.le_par hs
        omega
      · obtain ⟨c, hc, hpc, hdc⟩ := ih (hV.par_lt hs) hpt hk
        exact ⟨c, hc, hpc, Desc.of_par hdc⟩

/-! ### The top node of a vertex

The occurrence set of a vertex is connected, so it has a highest node,
and every occurrence is a descendant of it. That node is what the label
pass computes first (plan C7a(a)); here it is also the handle by which
every set lemma below climbs. -/

end Valid

/-- The highest node whose bag contains `v`. Computable — the driver
computes it — and, under `Valid`, the root of `v`'s occurrence set. -/
def top (N : ℕ) (bags : ℕ → Finset (Fin n)) (v : Fin n) : ℕ :=
  Nat.findGreatest (fun t => v ∈ bags t) (N - 1)

namespace Valid

theorem top_lt (hV : Valid G N par bags) (v : Fin n) : top N bags v < N :=
  lt_of_le_of_lt (Nat.findGreatest_le _) (by have := hV.pos; omega)

/-- No validity needed: the top node is at least every occurrence. -/
theorem _root_.Lax11Proofs.TreeDecomp.le_top (h : t < N) (hv : v ∈ bags t) :
    t ≤ top N bags v :=
  Nat.le_findGreatest (by omega) hv

theorem mem_top (hV : Valid G N par bags) (v : Fin n) : v ∈ bags (top N bags v) := by
  obtain ⟨t, ht, hvt⟩ := hV.vertex_cover v
  exact Nat.findGreatest_spec (P := fun t => v ∈ bags t) (by omega) hvt

/-- The unique characterization: the top node is the greatest node whose
bag contains `v`. -/
theorem top_eq (hV : Valid G N par bags) (ht : t < N) (hv : v ∈ bags t)
    (hmax : ∀ s < N, v ∈ bags s → s ≤ t) : top N bags v = t :=
  le_antisymm (hmax _ (hV.top_lt v) (hV.mem_top v)) (le_top ht hv)

/-- **The climb.** Below its top node, an occurrence of `v` has an
occurrence of `v` above it. -/
theorem mem_par_of_lt_top (hV : Valid G N par bags) (hv : v ∈ bags i)
    (h : i < top N bags v) : v ∈ bags (par i) :=
  hV.coherent v i (top N bags v) h (hV.top_lt v) hv (hV.mem_top v)

private theorem desc_top_aux (hV : Valid G N par bags) :
    ∀ (d i : ℕ), top N bags v - i ≤ d → i < N → v ∈ bags i → Desc par i (top N bags v) := by
  intro d
  induction d with
  | zero =>
      intro i hle hi hv
      have := le_top hi hv
      have : i = top N bags v := by omega
      rw [this]
      exact Desc.refl _ _
  | succ d ih =>
      intro i hle hi hv
      rcases eq_or_lt_of_le (le_top hi hv) with he | hlt
      · rw [he]; exact Desc.refl _ _
      · have h1 : i + 1 < N := by have := hV.top_lt (bags := bags) v; omega
        have h2 : i < par i := hV.par_gt i h1
        exact Desc.of_par
          (ih (par i) (by omega) (hV.par_mem i h1) (hV.mem_par_of_lt_top hv hlt))

/-- **The occurrence set is rooted at the top node**: every occurrence of
`v` is a descendant of `top v`. This is the connectivity of the
occurrence set, in the form the lemmas use. -/
theorem desc_top (hV : Valid G N par bags) (hi : i < N) (hv : v ∈ bags i) :
    Desc par i (top N bags v) :=
  desc_top_aux hV (top N bags v - i) i le_rfl hi hv

private theorem mem_of_iterate (hV : Valid G N par bags) :
    ∀ (k s : ℕ), s < N → v ∈ bags s → par^[k] s ≤ top N bags v → v ∈ bags (par^[k] s) := by
  intro k
  induction k with
  | zero => intro s _ hv _; exact hv
  | succ k ih =>
      intro s hs hv hle
      rcases eq_or_lt_of_le (le_top hs hv) with he | hlt
      · have h1 : s ≤ par^[k + 1] s := hV.le_iterate hs _
        have h2 : par^[k + 1] s = top N bags v := by omega
        rw [h2]
        exact hV.mem_top v
      · rw [Function.iterate_succ_apply] at hle ⊢
        exact ih (par s) (hV.par_lt hs) (hV.mem_par_of_lt_top hv hlt) hle

/-- **The occurrence set is upward closed to the top**: an occurrence of
`v` occurs again at every ancestor of it up to `top v`. -/
theorem mem_of_desc (hV : Valid G N par bags) (hs : s < N) (hv : v ∈ bags s)
    (hd : Desc par s t) (hle : t ≤ top N bags v) : v ∈ bags t := by
  obtain ⟨k, rfl⟩ := hd
  exact mem_of_iterate hV k s hs hv hle

/-! ### Subtrees -/

end Valid

/-- The set of vertices in the bags of `t`'s subtree — the region whose
type the fold computes at node `t`. -/
def subtree (N : ℕ) (par : ℕ → ℕ) (bags : ℕ → Finset (Fin n)) (t : ℕ) : Set (Fin n) :=
  {v | ∃ s, s < N ∧ Desc par s t ∧ v ∈ bags s}

theorem mem_subtree {t : ℕ} : v ∈ subtree N par bags t ↔ ∃ s, s < N ∧ Desc par s t ∧ v ∈ bags s :=
  Iff.rfl

theorem bags_subset_subtree (ht : t < N) : (bags t : Set (Fin n)) ⊆ subtree N par bags t :=
  fun _ hv => ⟨t, ht, Desc.refl _ _, hv⟩

theorem subtree_mono (hd : Desc par c t) : subtree N par bags c ⊆ subtree N par bags t :=
  fun _ ⟨s, hs, hsc, hv⟩ => ⟨s, hs, hsc.trans hd, hv⟩

namespace Valid

/-- **A subtree is its bag together with its children's subtrees.** The
induction step of the fold: the children are exactly the nodes `c < t`
with `par c = t`, which is what the schema folds over. -/
theorem mem_subtree_iff (hV : Valid G N par bags) (ht : t < N) :
    v ∈ subtree N par bags t ↔
      v ∈ bags t ∨ ∃ c, c < t ∧ par c = t ∧ v ∈ subtree N par bags c := by
  constructor
  · rintro ⟨s, hs, hd, hv⟩
    by_cases hst : s = t
    · exact Or.inl (hst ▸ hv)
    · obtain ⟨c, hc, hpc, hdc⟩ := hV.exists_child hs hd hst
      exact Or.inr ⟨c, hc, hpc, ⟨s, hs, hdc, hv⟩⟩
  · rintro (h | ⟨c, hct, hpc, s, hs, hd, hv⟩)
    · exact ⟨t, ht, Desc.refl _ _, h⟩
    · exact ⟨s, hs, hd.trans ⟨1, hpc⟩, hv⟩

/-- The root's subtree is everything — vertex coverage, plus the fact
that every node descends from the root. -/
theorem subtree_root (hV : Valid G N par bags) :
    subtree N par bags (N - 1) = Set.univ := by
  ext v
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  obtain ⟨t, ht, hvt⟩ := hV.vertex_cover v
  exact ⟨t, ht, hV.desc_root ht, hvt⟩

/-! ### Separation

The exit lemma and its consequences. Everything here is one shape: a
vertex seen both inside `subtree c` and at a node outside it must sit in
`B_c`, because its occurrence set is connected and its top node is
therefore strictly above `c`. -/

/-- **The exit lemma.** A vertex of `subtree c` that also occurs at a
node outside `c`'s subtree lies in `B_c` — and, since its top node is
then strictly above `c`, also in `B_{par c}`. -/
theorem mem_bags_of_out (hV : Valid G N par bags)
    (hv : v ∈ subtree N par bags c) (hw : w < N) (hvw : v ∈ bags w)
    (hnd : ¬ Desc par w c) : v ∈ bags c ∧ v ∈ bags (par c) := by
  obtain ⟨s, hs, hd, hvs⟩ := hv
  have hdw : Desc par w (top N bags v) := hV.desc_top hw hvw
  have hds : Desc par s (top N bags v) := hV.desc_top hs hvs
  have hlt : c < top N bags v := by
    rcases hV.desc_total hs hd hds with h | h
    · rcases eq_or_lt_of_le (hV.desc_le (hV.desc_lt hs hd) h) with he | hlt
      · exact absurd (he ▸ hdw) hnd
      · exact hlt
    · exact absurd (hdw.trans h) hnd
  have hmem : v ∈ bags c := hV.mem_of_desc hs hvs hd hlt.le
  exact ⟨hmem, hV.mem_par_of_lt_top hmem hlt⟩

/-- **The separation lemma.** No edge leaves a subtree except through
its bag: an edge from `subtree c` to the outside has its inner endpoint
in `B_c`, and in `B_{par c}`. -/
theorem separation (hV : Valid G N par bags)
    (hu : u ∈ subtree N par bags c) (hv : v ∉ subtree N par bags c) (hadj : G.Adj u v) :
    u ∈ bags c ∧ u ∈ bags (par c) := by
  obtain ⟨w, hw, hwu, hwv⟩ := hV.edge_cover u v hadj
  refine hV.mem_bags_of_out hu hw hwu (fun hd => hv ⟨w, hw, hd, hwv⟩)

/-- The separation lemma in its usual phrasing: no edge of `G` joins the
*interior* of a subtree — what is left of it after its bag is removed —
to the exterior. -/
theorem no_edge_interior (hV : Valid G N par bags) (hu : u ∈ subtree N par bags c)
    (hnb : u ∉ bags c) (hv : v ∉ subtree N par bags c) : ¬ G.Adj u v :=
  fun h => hnb (hV.separation hu hv h).1

/-- Separation in the shape the composition lemma's gluing hypothesis
wants (`Glue.sep`): for any region `X` containing the parent's bag, an
edge between `X` and `subtree c` has an endpoint in the overlap. -/
theorem sep_glue (hV : Valid G N par bags) {X : Set (Fin n)}
    (hX : (bags (par c) : Set (Fin n)) ⊆ X) :
    ∀ u ∈ X, ∀ v ∈ subtree N par bags c, G.Adj u v →
      u ∈ subtree N par bags c ∨ v ∈ X := by
  intro u _ v hv hadj
  by_cases hu : u ∈ subtree N par bags c
  · exact Or.inl hu
  · exact Or.inr (hX (hV.separation hv hu hadj.symm).2)

/-- The overlap of a bag with a child's subtree is inside the child's
bag: the two regions the fold glues meet only in `B_c ∩ B_t`. -/
theorem bags_inter_subtree (hV : Valid G N par bags) (ht : t < N) (hct : c < t)
    (hpc : par c = t) (hvt : v ∈ bags t) (hv : v ∈ subtree N par bags c) :
    v ∈ bags c := by
  refine (hV.mem_bags_of_out hv ht hvt (fun hd => ?_)).1
  exact absurd (hV.desc_le ht hd) (by omega)

/-- **Sibling interiors are disjoint.** Two incomparable nodes — in
particular two distinct children of the same node — have subtrees that
meet only inside both bags (and hence, by the climb, inside both
parents' bags). -/
theorem sibling (hV : Valid G N par bags)
    (h₁₂ : ¬ Desc par c₁ c₂) (h₂₁ : ¬ Desc par c₂ c₁)
    (hv₁ : v ∈ subtree N par bags c₁) (hv₂ : v ∈ subtree N par bags c₂) :
    v ∈ bags c₁ ∧ v ∈ bags (par c₁) ∧ v ∈ bags c₂ ∧ v ∈ bags (par c₂) := by
  obtain ⟨s₁, hs₁, hd₁, hvs₁⟩ := hv₁
  obtain ⟨s₂, hs₂, hd₂, hvs₂⟩ := hv₂
  have hn₁ : ¬ Desc par s₁ c₂ := fun h =>
    (hV.desc_total hs₁ h hd₁).elim (fun h' => h₂₁ h') (fun h' => h₁₂ h')
  have hn₂ : ¬ Desc par s₂ c₁ := fun h =>
    (hV.desc_total hs₂ h hd₂).elim (fun h' => h₁₂ h') (fun h' => h₂₁ h')
  obtain ⟨m₁, p₁⟩ := hV.mem_bags_of_out ⟨s₁, hs₁, hd₁, hvs₁⟩ hs₂ hvs₂ hn₂
  obtain ⟨m₂, p₂⟩ := hV.mem_bags_of_out ⟨s₂, hs₂, hd₂, hvs₂⟩ hs₁ hvs₁ hn₁
  exact ⟨m₁, p₁, m₂, p₂⟩

/-- Sibling interiors are disjoint, in that phrasing: outside its own
bag, a subtree meets no incomparable subtree. -/
theorem sibling_interior_disjoint (hV : Valid G N par bags)
    (h₁₂ : ¬ Desc par c₁ c₂) (h₂₁ : ¬ Desc par c₂ c₁) :
    (subtree N par bags c₁ \ (bags c₁ : Set (Fin n))) ∩ subtree N par bags c₂ = ∅ := by
  ext v
  simp only [Set.mem_inter_iff, Set.mem_diff, Finset.mem_coe, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro ⟨hv₁, hnb⟩ hv₂
  exact hnb (hV.sibling h₁₂ h₂₁ hv₁ hv₂).1

/-- Distinct children of the same node are incomparable — a child of `t`
is not a descendant of anything below `t`. -/
theorem child_not_desc (hV : Valid G N par bags) (ht : t < N)
    (hp₁ : par c₁ = t) (h₂ : c₂ < t) (hne : c₁ ≠ c₂) : ¬ Desc par c₁ c₂ := by
  intro hd
  have hdt : Desc par t c₂ := hp₁ ▸ hd.par_of_ne hne
  have := hV.desc_le ht hdt
  omega

/-! ### The two coherence lemmas of C7a

What the label pass needs to compute bag adjacency in linear total time:
each edge is *discovered* once, at the lower of its endpoints' top
nodes, and is then *propagated* downward from parent to child. -/

/-- Every node whose bag contains both endpoints of an edge is a
descendant of the lower of the two top nodes. -/
theorem desc_min_top (hV : Valid G N par bags) (hw : w < N)
    (hu : u ∈ bags w) (hv : v ∈ bags w) :
    Desc par w (min (top N bags u) (top N bags v)) := by
  rcases min_cases (top N bags u) (top N bags v) with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he]; exact hV.desc_top hw hu
  · rw [he]; exact hV.desc_top hw hv

/-- **Every edge is present at the lower of its endpoints' top nodes.**
Together with `desc_min_top` — which says no node above it sees the edge
— this is the lemma that lets the driver find each edge exactly once, by
scanning `v`'s adjacency block only at `top v`. -/
theorem mem_bags_min_top (hV : Valid G N par bags) (hadj : G.Adj u v) :
    u ∈ bags (min (top N bags u) (top N bags v)) ∧
      v ∈ bags (min (top N bags u) (top N bags v)) := by
  obtain ⟨w, hw, hwu, hwv⟩ := hV.edge_cover u v hadj
  rcases min_cases (top N bags u) (top N bags v) with ⟨he, hle⟩ | ⟨he, hle⟩
  · rw [he]
    exact ⟨hV.mem_top u, hV.mem_of_desc hw hwv (hV.desc_top hw hwu) hle⟩
  · rw [he]
    exact ⟨hV.mem_of_desc hw hwu (hV.desc_top hw hwv) hle.le, hV.mem_top v⟩

/-- **An edge inside a bag whose top node is elsewhere is inside the
parent's bag too.** This is the soundness of the top-down propagation
`edges(B_c) = discovered at c ∪ edges(B_{par c}) ∩ B_c`: read
contrapositively, an edge of `B_c` that is not in `B_{par c}` was
discovered at `c`. -/
theorem mem_bags_par_of_edge (hV : Valid G N par bags) (hc : c < N)
    (hu : u ∈ bags c) (hv : v ∈ bags c)
    (hne : c ≠ min (top N bags u) (top N bags v)) :
    u ∈ bags (par c) ∧ v ∈ bags (par c) := by
  have hd := hV.desc_min_top hc hu hv
  have hle := hV.desc_le hc hd
  have hlt : c < min (top N bags u) (top N bags v) := lt_of_le_of_ne hle hne
  exact ⟨hV.mem_par_of_lt_top hu (lt_of_lt_of_le hlt (min_le_left _ _)),
    hV.mem_par_of_lt_top hv (lt_of_lt_of_le hlt (min_le_right _ _))⟩

end Valid

/-! ### A decomposition, checked by hand

Non-vacuity, in the house style: the path `0 — 1 — 2` (the same graph the
composition lemma is checked against) with the two-node decomposition
`{0,1} — {1,2}`, of width `1`. Without a witness, seven hypotheses can
hold vacuously. -/

/-- The path `0 — 1 — 2`. -/
private abbrev pathG : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun u v : Fin 3 => u.val + 1 = v.val

/-- Two bags: the child `{0,1}` and the root `{1,2}`. -/
private def pathBags : ℕ → Finset (Fin 3) := fun t => if t = 0 then {0, 1} else {1, 2}

/-- Node `0`'s parent is the root `1`, which is its own parent. -/
private def pathPar : ℕ → ℕ := fun _ => 1

/-- The path's four (directed) edges, by cases. -/
private theorem path_adj (u v : Fin 3) (h : pathG.Adj u v) :
    (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) := by
  revert h; fin_cases u <;> fin_cases v <;> decide

private theorem path_valid : Valid pathG 2 pathPar pathBags where
  pos := by omega
  par_gt i h := by
    have hi : i = 0 := by omega
    subst hi; simp [pathPar]
  par_mem i _ := by simp [pathPar]
  par_root := rfl
  vertex_cover v := by
    fin_cases v
    · exact ⟨0, by omega, by decide⟩
    · exact ⟨0, by omega, by decide⟩
    · exact ⟨1, by omega, by decide⟩
  edge_cover u v h := by
    rcases path_adj u v h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, by omega, by decide⟩
    · exact ⟨0, by omega, by decide⟩
    · exact ⟨1, by omega, by decide⟩
    · exact ⟨1, by omega, by decide⟩
  coherent v i j hij hj _ hvj := by
    have hi : i = 0 := by omega
    have hj' : j = 1 := by omega
    subst hi; subst hj'
    simpa [pathPar] using hvj

private theorem path_width : Width 2 pathBags 1 := by
  intro t _
  by_cases h : t = 0 <;> simp [pathBags, h]

-- the top nodes: vertex `0` lives only in the child's bag, `1` in both,
-- `2` only in the root's — and `top` computes.
#guard top 2 pathBags 0 = 0
#guard top 2 pathBags 1 = 1
#guard top 2 pathBags 2 = 1

/-- The root's subtree is the whole vertex set. -/
private example : subtree 2 pathPar pathBags 1 = Set.univ := path_valid.subtree_root

end Lax11Proofs.TreeDecomp
