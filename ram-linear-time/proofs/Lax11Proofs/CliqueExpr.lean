import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

/-!
`k`-expressions: the object the theorem takes as input.

Cliquewidth replaces treewidth as the width parameter of this
development (plan decision C11), so the decomposition the program folds
over is a *`k`-expression*: a term built from labelled single vertices
by disjoint union, edge addition between two label classes, and
relabelling. This file is the object itself — the syntax, the evaluator,
validity, and the handful of structural facts the congruences and the
main induction consume. No logic, no types, no programs.

Three decisions shape it, all inherited from the ambient-subset style of
`MsoTypes.lean` and all aimed at keeping the eventual concept surface
auditable in one sitting (plan C12):

*Vertices are named globally by the leaves.* A leaf carries a vertex
name `v : Fin n`, and the vertex set of a subexpression is the finite
set of names of its leaves. So no node of the expression builds a fresh
structure that would have to be glued along an isomorphism: every
subexpression is a *subset* of the same ambient `Fin n`, disjoint union
is literally `∪`, and the disjointness that `⊕` needs is a consequence
of the leaf names being distinct (`Valid`). What does vary along the
tree is the graph — `addEdges` creates edges — which is why the
downstream statements are cross-graph; that is already the house style
(`typ_union_congr` is cross-ambient).

*Labels are sets, not a colouring.* `cls e i` is the `i`-th label class
of `e`, a `Finset (Fin n)`. A `k`-labelled graph is therefore an ambient
subset together with a `k`-tuple of sets, i.e. exactly the data
`typ q` already takes at `r = 0`, `s = k`: no marks anywhere in the
outer statements. The classes are pairwise disjoint and cover the
vertex set (`cls_disjoint`, `verts_eq_biUnion_cls`), but that is a
theorem about valid expressions, not part of the definition.

*Everything computes.* `verts`, `cls` and `opsOk` are `Finset`- and
`Bool`-valued, and `graph e` gets a `DecidableRel` instance by the same
structural recursion, so a hand-written expression can be `#eval`ed and
its edges `decide`d. The smoke test at the end of the file does exactly
that on the path `0—1—2` at `k = 2` — the house discipline, run before
anything was proved.

Validity has two clauses: the leaf names are distinct (`Nodup`), which
is what makes the two sides of every `⊕` disjoint, and the operations
are well formed (`addEdges i j` with `i ≠ j`, the standard restriction
on `η`). `ValidFor e G` adds the two root conditions, that the vertex
set is everything and the evaluated graph is `G`.
-/

namespace Lax11Proofs.CliqueExpr

variable {n k : ℕ}

/-- A `k`-expression over the vertex names `Fin n`: a single labelled
vertex, disjoint union, edge addition between two label classes, or
relabelling one class into another. -/
inductive Expr (n k : ℕ) : Type
  /-- The vertex `v`, carrying label `l`. -/
  | leaf (v : Fin n) (l : Fin k)
  /-- Disjoint union `⊕`. -/
  | union (e₁ e₂ : Expr n k)
  /-- `η i j`: join every vertex of class `i` to every vertex of class `j`. -/
  | addEdges (i j : Fin k) (e : Expr n k)
  /-- `ρ i j`: move class `i` into class `j`. -/
  | relabel (i j : Fin k) (e : Expr n k)

/-- The vertex names created by the leaves, in order. -/
def leafIds : Expr n k → List (Fin n)
  | .leaf v _ => [v]
  | .union e₁ e₂ => leafIds e₁ ++ leafIds e₂
  | .addEdges _ _ e => leafIds e
  | .relabel _ _ e => leafIds e

/-- The vertex set of an expression. -/
def verts : Expr n k → Finset (Fin n)
  | .leaf v _ => {v}
  | .union e₁ e₂ => verts e₁ ∪ verts e₂
  | .addEdges _ _ e => verts e
  | .relabel _ _ e => verts e

/-- The label classes of an expression: `cls e i` is the set of vertices
of `e` currently carrying label `i`. -/
def cls : Expr n k → Fin k → Finset (Fin n)
  | .leaf v l, i => if i = l then {v} else ∅
  | .union e₁ e₂, i => cls e₁ i ∪ cls e₂ i
  | .addEdges _ _ e, i => cls e i
  | .relabel i j e, t => if t = j then cls e i ∪ cls e j else if t = i then ∅ else cls e t

/-- The graph an expression evaluates to. -/
def graph : Expr n k → SimpleGraph (Fin n)
  | .leaf _ _ => ⊥
  | .union e₁ e₂ => graph e₁ ⊔ graph e₂
  | .addEdges i j e => graph e ⊔ SimpleGraph.fromRel fun u v => u ∈ cls e i ∧ v ∈ cls e j
  | .relabel _ _ e => graph e

/-- The evaluated graph has a decidable adjacency relation, by the same
structural recursion — this is what makes the smoke tests `decide`. -/
instance decidableAdj : ∀ e : Expr n k, DecidableRel (graph e).Adj
  | .leaf _ _ => fun u v => show Decidable ((⊥ : SimpleGraph (Fin n)).Adj u v) from
      inferInstance
  | .union e₁ e₂ => fun u v => by
      letI := decidableAdj e₁
      letI := decidableAdj e₂
      exact show Decidable ((graph e₁ ⊔ graph e₂).Adj u v) from inferInstance
  | .addEdges i j e => fun u v => by
      letI := decidableAdj e
      exact show Decidable
        ((graph e ⊔ SimpleGraph.fromRel fun u v => u ∈ cls e i ∧ v ∈ cls e j).Adj u v) from
        inferInstance
  | .relabel _ _ e => fun u v => by
      letI := decidableAdj e
      exact show Decidable ((graph e).Adj u v) from inferInstance

/-- Well-formedness of the operations: `addEdges` joins two *different*
classes, the standard restriction on `η`. -/
def opsOk : Expr n k → Bool
  | .leaf _ _ => true
  | .union e₁ e₂ => opsOk e₁ && opsOk e₂
  | .addEdges i j e => (i != j) && opsOk e
  | .relabel _ _ e => opsOk e

/-- A valid expression: the leaves create pairwise distinct vertices —
which is what makes the two sides of every `⊕` disjoint — and the
operations are well formed. -/
structure Valid (e : Expr n k) : Prop where
  /-- No vertex name is created twice. -/
  nodup : (leafIds e).Nodup
  /-- Every `addEdges` joins two different classes. -/
  ops : opsOk e = true

/-- A `k`-expression *for* `G`: valid, and at the root it has created
every vertex and exactly the edges of `G`. -/
structure ValidFor (e : Expr n k) (G : SimpleGraph (Fin n)) : Prop extends Valid e where
  /-- The root creates every vertex. -/
  verts_eq : verts e = Finset.univ
  /-- The root evaluates to `G`. -/
  graph_eq : graph e = G

/-! ### The equations

Named `rfl` lemmas for the four recursions, so that no proof below has
to `simp` with a definition written by pattern matching. -/

@[simp] theorem leafIds_leaf (v : Fin n) (l : Fin k) :
    leafIds (Expr.leaf v l) = [v] := rfl
@[simp] theorem leafIds_union (e₁ e₂ : Expr n k) :
    leafIds (.union e₁ e₂) = leafIds e₁ ++ leafIds e₂ := rfl
@[simp] theorem leafIds_addEdges (i j : Fin k) (e : Expr n k) :
    leafIds (.addEdges i j e) = leafIds e := rfl
@[simp] theorem leafIds_relabel (i j : Fin k) (e : Expr n k) :
    leafIds (.relabel i j e) = leafIds e := rfl

@[simp] theorem verts_leaf (v : Fin n) (l : Fin k) :
    verts (Expr.leaf v l) = {v} := rfl
@[simp] theorem verts_union (e₁ e₂ : Expr n k) :
    verts (.union e₁ e₂) = verts e₁ ∪ verts e₂ := rfl
@[simp] theorem verts_addEdges (i j : Fin k) (e : Expr n k) :
    verts (.addEdges i j e) = verts e := rfl
@[simp] theorem verts_relabel (i j : Fin k) (e : Expr n k) :
    verts (.relabel i j e) = verts e := rfl

@[simp] theorem cls_leaf (v : Fin n) (l i : Fin k) :
    cls (Expr.leaf v l) i = if i = l then {v} else ∅ := rfl
@[simp] theorem cls_union (e₁ e₂ : Expr n k) (i : Fin k) :
    cls (.union e₁ e₂) i = cls e₁ i ∪ cls e₂ i := rfl
@[simp] theorem cls_addEdges (i j : Fin k) (e : Expr n k) (t : Fin k) :
    cls (.addEdges i j e) t = cls e t := rfl
@[simp] theorem cls_relabel (i j : Fin k) (e : Expr n k) (t : Fin k) :
    cls (.relabel i j e) t =
      if t = j then cls e i ∪ cls e j else if t = i then ∅ else cls e t := rfl

@[simp] theorem graph_leaf (v : Fin n) (l : Fin k) :
    graph (Expr.leaf v l) = ⊥ := rfl
@[simp] theorem graph_union (e₁ e₂ : Expr n k) :
    graph (.union e₁ e₂) = graph e₁ ⊔ graph e₂ := rfl
@[simp] theorem graph_addEdges (i j : Fin k) (e : Expr n k) :
    graph (.addEdges i j e) =
      graph e ⊔ SimpleGraph.fromRel fun u v => u ∈ cls e i ∧ v ∈ cls e j := rfl
@[simp] theorem graph_relabel (i j : Fin k) (e : Expr n k) :
    graph (.relabel i j e) = graph e := rfl

@[simp] theorem opsOk_leaf (v : Fin n) (l : Fin k) :
    opsOk (Expr.leaf v l) = true := rfl
@[simp] theorem opsOk_union (e₁ e₂ : Expr n k) :
    opsOk (.union e₁ e₂) = (opsOk e₁ && opsOk e₂) := rfl
@[simp] theorem opsOk_addEdges (i j : Fin k) (e : Expr n k) :
    opsOk (.addEdges i j e) = ((i != j) && opsOk e) := rfl
@[simp] theorem opsOk_relabel (i j : Fin k) (e : Expr n k) :
    opsOk (.relabel i j e) = opsOk e := rfl

/-! ### The structural facts

Four facts, in the order the congruences and the main induction use
them: the vertex set is the set of leaf names; the label classes are
contained in it, cover it, and — for a valid expression — are pairwise
disjoint; the evaluated edges stay inside it; and the two sides of a
`⊕` are disjoint, which is the hypothesis the empty-pool composition
lemma needs. -/

/-- The vertex set of an expression is the set of its leaf names. -/
theorem mem_verts_iff {v : Fin n} : ∀ e : Expr n k, v ∈ verts e ↔ v ∈ leafIds e
  | .leaf w _ => by simp
  | .union e₁ e₂ => by simp [mem_verts_iff e₁, mem_verts_iff e₂]
  | .addEdges _ _ e => by simpa using mem_verts_iff e
  | .relabel _ _ e => by simpa using mem_verts_iff e

theorem verts_eq_toFinset (e : Expr n k) : verts e = (leafIds e).toFinset := by
  ext v; simp [mem_verts_iff]

/-- Every label class is a set of vertices. -/
theorem cls_subset_verts : ∀ (e : Expr n k) (i : Fin k), cls e i ⊆ verts e
  | .leaf v l, i => by
      by_cases h : i = l <;> simp [h]
  | .union e₁ e₂, i => by
      simpa using Finset.union_subset_union (cls_subset_verts e₁ i) (cls_subset_verts e₂ i)
  | .addEdges _ _ e, i => by simpa using cls_subset_verts e i
  | .relabel i j e, t => by
      simp only [cls_relabel, verts_relabel]
      split
      · exact Finset.union_subset (cls_subset_verts e i) (cls_subset_verts e j)
      · split
        · exact Finset.empty_subset _
        · exact cls_subset_verts e t

/-- Every vertex carries a label. -/
theorem exists_mem_cls : ∀ (e : Expr n k) {v : Fin n}, v ∈ verts e → ∃ i, v ∈ cls e i
  | .leaf w l, v, hv => ⟨l, by simp at hv ⊢; simp [hv]⟩
  | .union e₁ e₂, v, hv => by
      simp only [verts_union, Finset.mem_union] at hv
      rcases hv with hv | hv
      · obtain ⟨i, hi⟩ := exists_mem_cls e₁ hv
        exact ⟨i, by simp [hi]⟩
      · obtain ⟨i, hi⟩ := exists_mem_cls e₂ hv
        exact ⟨i, by simp [hi]⟩
  | .addEdges _ _ e, v, hv => by
      obtain ⟨i, hi⟩ := exists_mem_cls e (by simpa using hv)
      exact ⟨i, by simpa using hi⟩
  | .relabel i j e, v, hv => by
      obtain ⟨t, ht⟩ := exists_mem_cls e (by simpa using hv)
      by_cases htj : t = j
      · exact ⟨j, by simp [htj] at ht ⊢; simp [ht]⟩
      by_cases hti : t = i
      · exact ⟨j, by simp [hti] at ht ⊢; simp [ht]⟩
      · exact ⟨t, by simp [htj, hti, ht]⟩

/-- The label classes cover the vertex set. -/
theorem verts_eq_biUnion_cls (e : Expr n k) :
    verts e = Finset.univ.biUnion fun i => cls e i := by
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨exists_mem_cls e, fun ⟨i, hi⟩ => cls_subset_verts e i hi⟩

/-- Distinct leaves means disjoint sides at a `⊕`. -/
theorem verts_disjoint {e₁ e₂ : Expr n k} (h : (leafIds (.union e₁ e₂)).Nodup) :
    Disjoint (verts e₁) (verts e₂) := by
  rw [leafIds_union, List.nodup_append] at h
  rw [Finset.disjoint_left]
  intro v hv hv'
  exact h.2.2 v ((mem_verts_iff e₁).1 hv) v ((mem_verts_iff e₂).1 hv') rfl

/-- A vertex has only one label. -/
theorem cls_unique : ∀ (e : Expr n k), (leafIds e).Nodup →
    ∀ {v : Fin n} {i j : Fin k}, v ∈ cls e i → v ∈ cls e j → i = j
  | .leaf w l, _, v, i, j, hi, hj => by
      by_cases h : i = l <;> by_cases h' : j = l <;> simp_all
  | .union e₁ e₂, h, v, i, j, hi, hj => by
      have hd := verts_disjoint h
      rw [leafIds_union, List.nodup_append] at h
      simp only [cls_union, Finset.mem_union] at hi hj
      have h₁ : v ∈ cls e₁ i → v ∈ cls e₂ j → False := fun p q =>
        (Finset.disjoint_left.1 hd) (cls_subset_verts e₁ i p) (cls_subset_verts e₂ j q)
      have h₂ : v ∈ cls e₂ i → v ∈ cls e₁ j → False := fun p q =>
        (Finset.disjoint_left.1 hd) (cls_subset_verts e₁ j q) (cls_subset_verts e₂ i p)
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact cls_unique e₁ h.1 hi hj
      · exact absurd hj (fun hj => h₁ hi hj)
      · exact absurd hi (fun hi => h₂ hi hj)
      · exact cls_unique e₂ h.2.1 hi hj
  | .addEdges _ _ e, h, v, i, j, hi, hj => cls_unique e (by simpa using h)
      (by simpa using hi) (by simpa using hj)
  | .relabel i j e, h, v, t, u, ht, hu => by
      -- the label of `v` in `ρ i j e` is its label in `e`, except that `i` reads as `j`
      have key : ∀ {s : Fin k}, v ∈ cls (.relabel i j e) s →
          (s = j ∧ (v ∈ cls e i ∨ v ∈ cls e j)) ∨ (s ≠ j ∧ s ≠ i ∧ v ∈ cls e s) := by
        intro s hs
        simp only [cls_relabel] at hs
        split at hs
        · exact Or.inl ⟨by assumption, by simpa using hs⟩
        · split at hs
          · exact absurd hs (by simp)
          · exact Or.inr ⟨by assumption, by assumption, hs⟩
      have hn : (leafIds e).Nodup := by simpa using h
      rcases key ht with ⟨rfl, ht'⟩ | ⟨htj, hti, ht'⟩
      · rcases key hu with ⟨rfl, hu'⟩ | ⟨huj, hui, hu'⟩
        · rfl
        · rcases ht' with ht'' | ht''
          · exact absurd (cls_unique e hn hu' ht'') hui
          · exact absurd (cls_unique e hn hu' ht'') huj
      · rcases key hu with ⟨rfl, hu'⟩ | ⟨huj, hui, hu'⟩
        · rcases hu' with hu'' | hu''
          · exact absurd (cls_unique e hn ht' hu'') hti
          · exact absurd (cls_unique e hn ht' hu'') htj
        · exact cls_unique e hn ht' hu'

/-- The label classes of a valid expression are pairwise disjoint. -/
theorem cls_disjoint {e : Expr n k} (h : (leafIds e).Nodup) {i j : Fin k} (hij : i ≠ j) :
    Disjoint (cls e i) (cls e j) :=
  Finset.disjoint_left.2 fun _ hi hj => hij (cls_unique e h hi hj)

/-- The evaluated edges stay inside the vertex set. -/
theorem mem_verts_of_adj : ∀ (e : Expr n k) {u v : Fin n}, (graph e).Adj u v →
    u ∈ verts e ∧ v ∈ verts e
  | .leaf w l, u, v, huv => by simp at huv
  | .union e₁ e₂, u, v, huv => by
      simp only [graph_union, SimpleGraph.sup_adj] at huv
      rcases huv with huv | huv
      · exact ⟨by simp [(mem_verts_of_adj e₁ huv).1], by simp [(mem_verts_of_adj e₁ huv).2]⟩
      · exact ⟨by simp [(mem_verts_of_adj e₂ huv).1], by simp [(mem_verts_of_adj e₂ huv).2]⟩
  | .addEdges i j e, u, v, huv => by
      simp only [graph_addEdges, SimpleGraph.sup_adj, SimpleGraph.fromRel_adj] at huv
      rcases huv with huv | ⟨-, huv | huv⟩
      · simpa using mem_verts_of_adj e huv
      · exact ⟨by simpa using cls_subset_verts e i huv.1,
          by simpa using cls_subset_verts e j huv.2⟩
      · exact ⟨by simpa using cls_subset_verts e j huv.2,
          by simpa using cls_subset_verts e i huv.1⟩
  | .relabel _ _ e, u, v, huv => by simpa using mem_verts_of_adj e (by simpa using huv)

/-! ### Validity

The two clauses pass to subexpressions, and at a `⊕` the leaf clause
becomes the two hypotheses of the empty-pool composition lemma:
the sides are disjoint (`Valid.disjoint`) and there is no edge between
them (`Valid.sep`, stated in the `Glue.sep` shape, over `Set`s, so that
the congruence can consume it verbatim). -/

theorem Valid.left {e₁ e₂ : Expr n k} (h : Valid (.union e₁ e₂)) : Valid e₁ := by
  have hn := h.nodup
  have ho := h.ops
  rw [leafIds_union, List.nodup_append] at hn
  rw [opsOk_union, Bool.and_eq_true] at ho
  exact ⟨hn.1, ho.1⟩

theorem Valid.right {e₁ e₂ : Expr n k} (h : Valid (.union e₁ e₂)) : Valid e₂ := by
  have hn := h.nodup
  have ho := h.ops
  rw [leafIds_union, List.nodup_append] at hn
  rw [opsOk_union, Bool.and_eq_true] at ho
  exact ⟨hn.2.1, ho.2⟩

theorem Valid.of_addEdges {i j : Fin k} {e : Expr n k} (h : Valid (.addEdges i j e)) :
    Valid e := by
  have ho := h.ops
  rw [opsOk_addEdges, Bool.and_eq_true] at ho
  exact ⟨by simpa using h.nodup, ho.2⟩

theorem Valid.ne {i j : Fin k} {e : Expr n k} (h : Valid (.addEdges i j e)) : i ≠ j := by
  have := h.ops; simp at this; exact this.1

theorem Valid.of_relabel {i j : Fin k} {e : Expr n k} (h : Valid (.relabel i j e)) :
    Valid e :=
  ⟨by simpa using h.nodup, by simpa using h.ops⟩

/-- The two sides of a `⊕` are disjoint — this is what leaf-distinctness
is for. -/
theorem Valid.disjoint {e₁ e₂ : Expr n k} (h : Valid (.union e₁ e₂)) :
    Disjoint (verts e₁) (verts e₂) :=
  verts_disjoint h.nodup

/-- No edge of a `⊕` node joins the two sides: the separation hypothesis
of the composition lemma, at the empty mark pool. Validity is not needed
— a `⊕` adds no edge at all, so an edge between the sides would have to
be an edge of one side with an endpoint in the other. -/
theorem sep_union {e₁ e₂ : Expr n k} :
    ∀ u ∈ (verts e₁ : Set (Fin n)), ∀ v ∈ (verts e₂ : Set (Fin n)),
      (graph (.union e₁ e₂)).Adj u v →
        u ∈ (verts e₂ : Set (Fin n)) ∨ v ∈ (verts e₁ : Set (Fin n)) := by
  intro u hu v hv huv
  simp only [Finset.mem_coe] at hu hv ⊢
  simp only [graph_union, SimpleGraph.sup_adj] at huv
  rcases huv with huv | huv
  · exact Or.inr (mem_verts_of_adj e₁ huv).2
  · exact Or.inl (mem_verts_of_adj e₂ huv).1

/-! ### Smoke test

The path `0—1—2` at `k = 2`, hand-written: create `0` with label `0` and
`1` with label `1` and join the classes; then add `2` with label `0` and
join the classes again — the second join adds `2—1` and re-adds `0—1`.
Run before anything below was proved. -/

/-- The path `0—1—2` as a `2`-expression. -/
def pathExpr : Expr 3 2 :=
  .addEdges 0 1 (.union (.addEdges 0 1 (.union (.leaf 0 0) (.leaf 1 1))) (.leaf 2 0))

#guard leafIds pathExpr = [0, 1, 2]
#guard verts pathExpr = Finset.univ
#guard cls pathExpr 0 = {0, 2}
#guard cls pathExpr 1 = {1}
#guard opsOk pathExpr
-- the edge set: exactly `0—1` and `1—2`, in both orders
#guard (Finset.univ.filter fun p : Fin 3 × Fin 3 => (graph pathExpr).Adj p.1 p.2)
    = {(0, 1), (1, 0), (1, 2), (2, 1)}
-- relabelling merges the classes and empties the source
#guard cls (.relabel 1 0 pathExpr) 0 = {0, 1, 2}
#guard cls (.relabel 1 0 pathExpr) 1 = ∅
-- …and changes no edge
#guard (Finset.univ.filter fun p : Fin 3 × Fin 3 => (graph (.relabel 1 0 pathExpr)).Adj p.1 p.2)
    = (Finset.univ.filter fun p : Fin 3 × Fin 3 => (graph pathExpr).Adj p.1 p.2)

end Lax11Proofs.CliqueExpr
