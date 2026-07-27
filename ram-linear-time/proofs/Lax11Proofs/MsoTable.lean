import Lax11Proofs.MsoCliqueOps
import Lax11Proofs.TreeFold

/-!
The type table, and the main induction (plan decision C14).

This is where the two workstreams meet. `TreeFold.lean` built a
table-driven bottom-up fold over a parent-pointer tree and proved a
program computes it; `MsoTypes.lean`–`MsoCliqueOps.lean` built the
MSO type algebra and the four congruences of the clique-width
operations. Here the types become the fold's value alphabet, the
operations become its label alphabet, and the congruences become the
table — after which the fold's value at a node *is* the type of the
subexpression rooted there.

Four decisions shape the file.

*The table is extracted by choice, never computed* (plan C5). A
congruence says "equal types have equal images"; the corresponding
function on types is obtained from it by `Classical.choice` over the
set of realizations, and its only property is the one correctness
equation `f (typeOf I) = typeOf (op I)`. Nothing below ever looks
inside a type, and nothing is decidable.

*The value alphabet carries op-tagged partial states.* The schema
folds a node's children one at a time into an accumulator seeded from
the node's own label, so a binary `⊕` needs an intermediate value
("left child absorbed, waiting for the right"), and the unary ops need
a seed that remembers which op it is. That is the "label inside the
value" device `TreeFold.lean`'s header advertises, and it is what
makes the schema's two tables enough. The partial states are ordinary
inhabitants of the value type, so they are counted by `Table.V` and
`Table.Wf` holds by construction.

*The label alphabet is explicit arithmetic, not an enumeration.* The
op codes are the `lab` array of the instance word — a reader of the
statement must be able to say which number means `η 0 1` — so `Op.code`
is a computable formula and `Op.decode` is its computable inverse,
proved so by `Op.decode_code`. Both live on the endorsement surface,
with the expression type they number. The *value* numbering, which
nobody writes down, is `Fintype.equivFin` and is noncomputable.

*The fold is joined to the expression by a relation, not by an array.*
`EncExpr par lab i e` says "node `i` of the tree `(par, lab)` is the
expression `e`": the op code matches and the children, in the schema's
increasing-index order, encode the subexpressions. The main induction
is structural on `Expr` against that relation. Turning an instance
word into an `EncExpr` is the encoding work, and it belongs to the
driver milestone; this file proves the mathematics against the
relation, which is exactly the interface `EncodesTree` already speaks.
-/

namespace Lax11Proofs.MsoTable

open Lax11Proofs.MsoTypes Lax11Proofs.CliqueExpr Lax11Proofs.TreeFold

variable {k : ℕ}

/-! ### The operation alphabet

One symbol per operation of a `k`-expression, with the leaf's *label*
inside the symbol and the leaf's vertex name outside it: the type of a
one-vertex region does not depend on which vertex it is
(`typ_singleton`), which is why the driver never reads the vertex-id
array. `Op`, `Op.code`, `Op.decode` and `opCard` are the surface
definitions of `Lax11.CliqueExpr` (re-exported by
`Lax11Proofs/CliqueExpr.lean`, so that there is one op-code layout and
the instance encoding on the surface reads the same numbers the fold
does); what is proved here is that the codes are a bijection onto an
initial segment, which is what makes them the fold's labels. -/

/-- A pair of labels read in base `k` is below `k²`. -/
private theorem pair_lt (i j : Fin k) : (i : ℕ) * k + (j : ℕ) < k * k := by
  have hi : (i : ℕ) + 1 ≤ k := i.isLt
  have hj : (j : ℕ) < k := j.isLt
  calc (i : ℕ) * k + (j : ℕ) < (i : ℕ) * k + k := by omega
    _ = ((i : ℕ) + 1) * k := by ring
    _ ≤ k * k := Nat.mul_le_mul_right k hi

private theorem div_pair (i j : Fin k) : ((i : ℕ) * k + (j : ℕ)) / k = (i : ℕ) := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  rw [Nat.mul_comm, Nat.mul_add_div hk, Nat.div_eq_of_lt j.isLt, Nat.add_zero]

/-- The codes are what `decode` decodes. -/
theorem Op.decode_code (o : Op k) : Op.decode k o.code = o := by
  cases o with
  | union => rfl
  | leaf l =>
      have hl : (l : ℕ) < k := l.isLt
      simp only [Op.code_leaf, Op.decode, if_neg (show ¬ 1 + (l : ℕ) = 0 by omega),
        dif_pos (show 1 + (l : ℕ) - 1 < k by omega)]
      simp
  | eta i j =>
      have hp := pair_lt i j
      have h0 : ¬ 1 + k + ((i : ℕ) * k + (j : ℕ)) = 0 := by omega
      have h1 : ¬ 1 + k + ((i : ℕ) * k + (j : ℕ)) - 1 < k := by omega
      have h2 : 1 + k + ((i : ℕ) * k + (j : ℕ)) - 1 - k = (i : ℕ) * k + (j : ℕ) := by omega
      simp only [Op.code_eta, Op.decode, if_neg h0, dif_neg h1, h2, dif_pos hp]
      simp [div_pair, Nat.mod_eq_of_lt j.isLt]
  | rho i j =>
      have hp := pair_lt i j
      have h0 : ¬ 1 + k + k * k + ((i : ℕ) * k + (j : ℕ)) = 0 := by omega
      have h1 : ¬ 1 + k + k * k + ((i : ℕ) * k + (j : ℕ)) - 1 < k := by omega
      have h2 : ¬ 1 + k + k * k + ((i : ℕ) * k + (j : ℕ)) - 1 - k < k * k := by omega
      have h3 : 1 + k + k * k + ((i : ℕ) * k + (j : ℕ)) - 1 - k - k * k
          = (i : ℕ) * k + (j : ℕ) := by omega
      simp only [Op.code_rho, Op.decode, if_neg h0, dif_neg h1, dif_neg h2, h3, dif_pos hp]
      simp [div_pair, Nat.mod_eq_of_lt j.isLt]

/-- Every code is a label of the table. -/
theorem Op.code_lt (o : Op k) : o.code < opCard k := by
  cases o with
  | union => simp [Op.code_union, opCard_eq]
  | leaf l => have := l.isLt; simp only [Op.code_leaf, opCard_eq]; omega
  | eta i j => have := pair_lt i j; simp only [Op.code_eta, opCard_eq]; omega
  | rho i j => have := pair_lt i j; simp only [Op.code_rho, opCard_eq]; omega

/-! ### The value alphabet

`q`-types of `k`-labelled regions, together with the partial states the
sequential fold needs: a `⊕` node's accumulator before any child has
arrived (`unionEmpty`) and after the left one has (`unionLeft`), and the
seeds of the two unary ops, which carry their parameters. The partial
states are inhabitants of the same type, so the schema's bound `V`
counts them and `Table.Wf` is immediate. -/

/-- The fold's value at a node: a finished type, or an op-tagged partial
state waiting for children. -/
inductive Val (q k : ℕ) where
  /-- A finished `q`-type. -/
  | done (t : T q 0 k)
  /-- A `⊕` node with no child absorbed yet. -/
  | unionEmpty
  /-- A `⊕` node with its left child absorbed. -/
  | unionLeft (t : T q 0 k)
  /-- An `η i j` node before its child arrives. -/
  | etaWait (i j : Fin k)
  /-- A `ρ i j` node before its child arrives. -/
  | rhoWait (i j : Fin k)
  deriving DecidableEq, Fintype

instance {q k : ℕ} : Inhabited (Val q k) := ⟨.unionEmpty⟩

/-- The number of a value. Noncomputable (`Fintype.equivFin`), which is
all C5 ever asked for: the *values* are internal to the fold, only the
op codes appear in the input. -/
noncomputable def enc {q : ℕ} (v : Val q k) : ℕ := (Fintype.equivFin (Val q k) v : ℕ)

/-- The value with a given number, junk outside the range. -/
noncomputable def dec (q k : ℕ) (a : ℕ) : Val q k :=
  if h : a < Fintype.card (Val q k) then (Fintype.equivFin (Val q k)).symm ⟨a, h⟩
  else .unionEmpty

theorem enc_lt {q : ℕ} (v : Val q k) : enc v < Fintype.card (Val q k) :=
  (Fintype.equivFin (Val q k) v).isLt

@[simp] theorem dec_enc {q : ℕ} (v : Val q k) : dec q k (enc v) = v := by
  rw [dec, dif_pos (enc_lt v)]
  exact (Fintype.equivFin (Val q k)).symm_apply_apply v

/-! ### The realizations, and the table by choice

A congruence of `MsoCliqueOps.lean` says: two regions with the same type
have images with the same type. To turn that into a function on types,
package a region as data (`Inst`, and `UInst` for the two disjoint
regions a `⊕` glues), take a realization of the given type by
`Classical.choice`, and apply the operation to it. The congruence is
exactly what makes the answer independent of the realization, which is
the one lemma each definition is followed by. No type is ever
inspected. -/

/-- A region of an ambient graph with the label classes as set
parameters: the data whose `q`-type the fold carries. -/
structure Inst (k : ℕ) where
  /-- The size of the ambient vertex set. -/
  n : ℕ
  /-- The ambient graph. -/
  G : SimpleGraph (Fin n)
  /-- The region. -/
  X : Set (Fin n)
  /-- The label classes, as set parameters. -/
  A : Fin k → Set (Fin n)

/-- The `q`-type of a region. Marks never appear: `r = 0` throughout. -/
noncomputable def Inst.ty (I : Inst k) (q : ℕ) : T q 0 k :=
  typ I.G I.X q Fin.elim0 I.A

/-- The `η i j` image of a region: the same region in the joined graph. -/
def Inst.eta (I : Inst k) (i j : Fin k) : Inst k :=
  ⟨I.n, addEdgesG I.G I.A i j, I.X, I.A⟩

/-- The `ρ i j` image of a region: the same region with merged classes. -/
def Inst.rho (I : Inst k) (i j : Fin k) : Inst k :=
  ⟨I.n, I.G, I.X, relabelSets I.A i j⟩

/-- Two disjoint, mutually non-adjacent regions of one ambient graph:
the data a `⊕` node glues. The two fields are exactly the hypotheses of
`typ_disjUnion`. -/
structure UInst (k : ℕ) where
  /-- The size of the ambient vertex set. -/
  n : ℕ
  /-- The ambient graph. -/
  G : SimpleGraph (Fin n)
  /-- The left region. -/
  X : Set (Fin n)
  /-- The right region. -/
  Y : Set (Fin n)
  /-- The label classes, as set parameters. -/
  A : Fin k → Set (Fin n)
  /-- The regions are disjoint. -/
  disj : Disjoint X Y
  /-- No edge joins them. -/
  sep : ∀ u ∈ X, ∀ v ∈ Y, G.Adj u v → u ∈ Y ∨ v ∈ X

/-- The type of the left region. -/
noncomputable def UInst.tyL (I : UInst k) (q : ℕ) : T q 0 k := typ I.G I.X q Fin.elim0 I.A
/-- The type of the right region. -/
noncomputable def UInst.tyR (I : UInst k) (q : ℕ) : T q 0 k := typ I.G I.Y q Fin.elim0 I.A
/-- The type of the union. -/
noncomputable def UInst.tyU (I : UInst k) (q : ℕ) : T q 0 k :=
  typ I.G (I.X ∪ I.Y) q Fin.elim0 I.A

open Classical in
/-- The type of an `η i j` node, as a function of its child's type. -/
noncomputable def etaVal (q : ℕ) (i j : Fin k) (t : T q 0 k) : Val q k :=
  if h : ∃ I : Inst k, I.ty q = t then .done ((h.choose.eta i j).ty q) else .unionEmpty

open Classical in
/-- The type of a `ρ i j` node, as a function of its child's type. -/
noncomputable def rhoVal (q : ℕ) (i j : Fin k) (t : T q 0 k) : Val q k :=
  if h : ∃ I : Inst k, I.ty q = t then .done ((h.choose.rho i j).ty q) else .unionEmpty

open Classical in
/-- The type of a `⊕` node, as a function of its two children's types. -/
noncomputable def unionVal (q : ℕ) (t₁ t₂ : T q 0 k) : Val q k :=
  if h : ∃ I : UInst k, I.tyL q = t₁ ∧ I.tyR q = t₂ then .done (h.choose.tyU q)
  else .unionEmpty

/-- The `η` entry is correct: `typ_addEdges` is what makes the choice
irrelevant. -/
theorem etaVal_ty (q : ℕ) (i j : Fin k) (I : Inst k) :
    etaVal q i j (I.ty q) = .done ((I.eta i j).ty q) := by
  have hex : ∃ J : Inst k, J.ty q = I.ty q := ⟨I, rfl⟩
  rw [etaVal, dif_pos hex]
  exact congrArg Val.done (typ_addEdges q i j hex.choose_spec)

/-- The `ρ` entry is correct: `typ_relabel` is what makes the choice
irrelevant. -/
theorem rhoVal_ty (q : ℕ) (i j : Fin k) (I : Inst k) :
    rhoVal q i j (I.ty q) = .done ((I.rho i j).ty q) := by
  have hex : ∃ J : Inst k, J.ty q = I.ty q := ⟨I, rfl⟩
  rw [rhoVal, dif_pos hex]
  exact congrArg Val.done (typ_relabel q i j hex.choose_spec)

/-- The `⊕` entry is correct: `typ_disjUnion` — the empty-pool instance
of the composition lemma — is what makes the choice irrelevant. -/
theorem unionVal_ty (q : ℕ) (I : UInst k) :
    unionVal q (I.tyL q) (I.tyR q) = .done (I.tyU q) := by
  have hex : ∃ J : UInst k, J.tyL q = I.tyL q ∧ J.tyR q = I.tyR q := ⟨I, rfl, rfl⟩
  rw [unionVal, dif_pos hex]
  exact congrArg Val.done
    (typ_disjUnion q hex.choose.disj I.disj hex.choose.sep I.sep
      hex.choose_spec.1 hex.choose_spec.2)

/-- The type of a leaf. No choice is needed: `typ_singleton` says a
one-vertex region's type depends only on its label, so a canonical
one-vertex graph computes it. -/
noncomputable def leafType (q k : ℕ) (l : Fin k) : T q 0 k :=
  typ (⊥ : SimpleGraph (Fin 1)) ({0} : Set (Fin 1)) q Fin.elim0
    (fun t => if t = l then ({0} : Set (Fin 1)) else ∅)

/-! ### The table -/

/-- The value a node starts from: its op, with no child absorbed. -/
noncomputable def initV (q k : ℕ) (c : ℕ) : Val q k :=
  match Op.decode k c with
  | .union => .unionEmpty
  | .leaf l => .done (leafType q k l)
  | .eta i j => .etaWait i j
  | .rho i j => .rhoWait i j

/-- Absorbing one child into an accumulator. The four meaningful cases
are the two halves of a `⊕` and the single child of each unary op;
everything else is unreachable and answers junk. -/
noncomputable def stepV (q : ℕ) : Val q k → Val q k → Val q k
  | .unionEmpty, .done t => .unionLeft t
  | .unionLeft t₁, .done t₂ => unionVal q t₁ t₂
  | .etaWait i j, .done t => etaVal q i j t
  | .rhoWait i j, .done t => rhoVal q i j t
  | _, _ => .unionEmpty

@[simp] theorem stepV_unionEmpty (q : ℕ) (t : T q 0 k) :
    stepV q (.unionEmpty) (.done t) = .unionLeft t := rfl
@[simp] theorem stepV_unionLeft (q : ℕ) (t₁ t₂ : T q 0 k) :
    stepV q (.unionLeft t₁) (.done t₂) = unionVal q t₁ t₂ := rfl
@[simp] theorem stepV_etaWait (q : ℕ) (i j : Fin k) (t : T q 0 k) :
    stepV q (.etaWait i j) (.done t) = etaVal q i j t := rfl
@[simp] theorem stepV_rhoWait (q : ℕ) (i j : Fin k) (t : T q 0 k) :
    stepV q (.rhoWait i j) (.done t) = rhoVal q i j t := rfl

/-- **The type table**: the fold schema's `Table`, with the `q`-types of
`k`-labelled regions (and the partial states) as values and the
operation codes as labels. -/
noncomputable def table (q k : ℕ) : Table where
  V := Fintype.card (Val q k)
  L := opCard k
  init := fun c => enc (initV q k c)
  step := fun a b => enc (stepV q (dec q k a) (dec q k b))

@[simp] theorem table_V (q k : ℕ) : (table q k).V = Fintype.card (Val q k) := rfl
@[simp] theorem table_L (q k : ℕ) : (table q k).L = opCard k := rfl
@[simp] theorem table_init (q k c : ℕ) : (table q k).init c = enc (initV q k c) := rfl
@[simp] theorem table_step (q k a b : ℕ) :
    (table q k).step a b = enc (stepV q (dec q k a) (dec q k b)) := rfl

/-- The table is well formed, because every value the table produces is
a value: the numbering is into an initial segment of `ℕ` by
construction. -/
theorem table_wf (q k : ℕ) : (table q k).Wf :=
  ⟨fun _ _ => enc_lt _, fun _ _ _ _ => enc_lt _⟩

/-! ### The type of a subexpression

The semantic object the fold computes: the `q`-type of the region a
subexpression has built, in the graph that subexpression evaluates to,
with its label classes as the set parameters. Noncomputable, and never
computed. -/

/-- The `q`-type of the subexpression `e`. -/
noncomputable def typeOf (q : ℕ) {n : ℕ} (e : Expr n k) : T q 0 k :=
  typ (graph e) ((verts e : Finset (Fin n)) : Set (Fin n)) q Fin.elim0
    (fun i => ((cls e i : Finset (Fin n)) : Set (Fin n)))

variable {n : ℕ}

/-- **The leaf case.** A one-vertex region's type is a function of its
label alone — which is why the vertex-id array of the instance is never
read by the program. -/
theorem typeOf_leaf (q : ℕ) (v : Fin n) (l : Fin k) :
    typeOf q (Expr.leaf v l) = leafType q k l := by
  have hX : ((verts (Expr.leaf v l) : Finset (Fin n)) : Set (Fin n)) = ({v} : Set (Fin n)) := by
    simp
  rw [typeOf, hX, leafType]
  refine typ_singleton q (fun a => a.elim0) (fun a => a.elim0) (fun t => ?_)
  by_cases h : t = l <;> simp [h]

/-- **The `η` case.** One application of `typ_addEdges`, with no
plumbing at all: the evaluated graph of an `η` node is literally
`addEdgesG` of its child's. -/
theorem typeOf_addEdges (q : ℕ) (i j : Fin k) (e : Expr n k) :
    etaVal q i j (typeOf q e) = .done (typeOf q (.addEdges i j e)) := by
  have hI : (Inst.mk n (graph e) ((verts e : Finset (Fin n)) : Set (Fin n))
      (fun t => ((cls e t : Finset (Fin n)) : Set (Fin n)))).ty q = typeOf q e := rfl
  rw [← hI, etaVal_ty]
  rfl

/-- **The `ρ` case.** One application of `typ_relabel`; the classes of a
`ρ` node are `relabelSets` of its child's, by `cls_relabel_eq`. -/
theorem typeOf_relabel (q : ℕ) (i j : Fin k) (e : Expr n k) :
    rhoVal q i j (typeOf q e) = .done (typeOf q (.relabel i j e)) := by
  have hI : (Inst.mk n (graph e) ((verts e : Finset (Fin n)) : Set (Fin n))
      (fun t => ((cls e t : Finset (Fin n)) : Set (Fin n)))).ty q = typeOf q e := rfl
  rw [← hI, rhoVal_ty]
  show Val.done _ = Val.done _
  rw [typeOf, cls_relabel_eq]
  rfl

/-- The label classes of a `⊕` agree with a side's own classes inside
that side — the one plumbing step the C13 list does not mention, and an
instance of `typ_congr_inter` (M4). -/
private theorem cls_union_inter_left {e₁ e₂ : Expr n k} (h : Valid (.union e₁ e₂)) (j : Fin k) :
    ((cls (.union e₁ e₂) j : Finset (Fin n)) : Set (Fin n))
        ∩ ((verts e₁ : Finset (Fin n)) : Set (Fin n))
      = ((cls e₁ j : Finset (Fin n)) : Set (Fin n))
        ∩ ((verts e₁ : Finset (Fin n)) : Set (Fin n)) := by
  ext x
  simp only [cls_union, Finset.coe_union, Set.mem_inter_iff, Set.mem_union, Finset.mem_coe]
  constructor
  · rintro ⟨hx | hx, hv⟩
    · exact ⟨hx, hv⟩
    · exact absurd hv (Finset.disjoint_right.mp (Valid.disjoint h) (cls_subset_verts e₂ j hx))
  · rintro ⟨hx, hv⟩
    exact ⟨Or.inl hx, hv⟩

/-- The mirror image. -/
private theorem cls_union_inter_right {e₁ e₂ : Expr n k} (h : Valid (.union e₁ e₂)) (j : Fin k) :
    ((cls (.union e₁ e₂) j : Finset (Fin n)) : Set (Fin n))
        ∩ ((verts e₂ : Finset (Fin n)) : Set (Fin n))
      = ((cls e₂ j : Finset (Fin n)) : Set (Fin n))
        ∩ ((verts e₂ : Finset (Fin n)) : Set (Fin n)) := by
  ext x
  simp only [cls_union, Finset.coe_union, Set.mem_inter_iff, Set.mem_union, Finset.mem_coe]
  constructor
  · rintro ⟨hx | hx, hv⟩
    · exact absurd hv (Finset.disjoint_left.mp (Valid.disjoint h) (cls_subset_verts e₁ j hx))
    · exact ⟨hx, hv⟩
  · rintro ⟨hx, hv⟩
    exact ⟨Or.inr hx, hv⟩

/-- **The `⊕` case.** `typ_disjUnion` fed the disjointness and the
separation of the two sides, after two rewrites that move a child's type
from its own graph and classes into the parent's — `typ_graph_union_*`
(the other side contributes no edge here) and `typ_congr_inter` (the
parent's classes agree with the child's inside the child). -/
theorem typeOf_union (q : ℕ) {e₁ e₂ : Expr n k} (h : Valid (.union e₁ e₂)) :
    unionVal q (typeOf q e₁) (typeOf q e₂) = .done (typeOf q (.union e₁ e₂)) := by
  set A : Fin k → Set (Fin n) :=
    fun i => ((cls (.union e₁ e₂) i : Finset (Fin n)) : Set (Fin n)) with hA
  let I : UInst k :=
    { n := n, G := graph (.union e₁ e₂)
      X := ((verts e₁ : Finset (Fin n)) : Set (Fin n))
      Y := ((verts e₂ : Finset (Fin n)) : Set (Fin n))
      A := A
      disj := Valid.disjoint_coe h
      sep := sep_union }
  have hL : I.tyL q = typeOf q e₁ := by
    show typ (graph (.union e₁ e₂)) ((verts e₁ : Finset (Fin n)) : Set (Fin n)) q Fin.elim0 A = _
    rw [typ_congr_inter (graph (.union e₁ e₂)) _ q Fin.elim0 A
      (fun i => ((cls e₁ i : Finset (Fin n)) : Set (Fin n))) (fun i => i.elim0)
      (cls_union_inter_left h)]
    exact typ_graph_union_left h (fun i => i.elim0)
  have hR : I.tyR q = typeOf q e₂ := by
    show typ (graph (.union e₁ e₂)) ((verts e₂ : Finset (Fin n)) : Set (Fin n)) q Fin.elim0 A = _
    rw [typ_congr_inter (graph (.union e₁ e₂)) _ q Fin.elim0 A
      (fun i => ((cls e₂ i : Finset (Fin n)) : Set (Fin n))) (fun i => i.elim0)
      (cls_union_inter_right h)]
    exact typ_graph_union_right h (fun i => i.elim0)
  have hU : I.tyU q = typeOf q (.union e₁ e₂) := by
    show typ (graph (.union e₁ e₂))
      (((verts e₁ : Finset (Fin n)) : Set (Fin n)) ∪ ((verts e₂ : Finset (Fin n)) : Set (Fin n)))
        q Fin.elim0 A = _
    rw [typeOf, verts_union, Finset.coe_union]
  rw [← hL, ← hR, unionVal_ty, hU]

/-! ### The expression, as a tree the fold can walk

`EncExpr par lab i e` says that node `i` of the parent-pointer tree
`(par, lab)` carries the expression `e`: the op code at `i` is `e`'s,
and `i`'s children — which the schema visits in increasing index order
— carry `e`'s subexpressions, left before right. This is the whole
correspondence between the structural induction and the fold; producing
it from an instance word is the driver's job. -/

/-- Node `i` of the tree `(par, lab)` is the expression `e`. -/
def EncExpr (par lab : ℕ → ℕ) : ℕ → Expr n k → Prop
  | i, .leaf _ l => children par i = [] ∧ lab i = (Op.leaf l).code
  | i, .union e₁ e₂ => ∃ c₁ c₂, children par i = [c₁, c₂] ∧
      lab i = (Op.union : Op k).code ∧ EncExpr par lab c₁ e₁ ∧ EncExpr par lab c₂ e₂
  | i, .addEdges a b e => ∃ c, children par i = [c] ∧
      lab i = (Op.eta a b).code ∧ EncExpr par lab c e
  | i, .relabel a b e => ∃ c, children par i = [c] ∧
      lab i = (Op.rho a b).code ∧ EncExpr par lab c e

/-- **The main theorem.** On a valid expression encoded as a
parent-pointer tree, the fold's value at every node is the number of
that node's type. Structural induction on the expression, one case per
constructor, each case one congruence of `MsoCliqueOps.lean`. -/
theorem val_eq_typeOf (q : ℕ) {par lab : ℕ → ℕ} :
    ∀ e : Expr n k, Valid e → ∀ i : ℕ, EncExpr par lab i e →
      val (table q k) par lab i = enc (Val.done (typeOf q e)) := by
  intro e
  induction e with
  | leaf v l =>
      intro _ i he
      obtain ⟨hc, hl⟩ := he
      rw [val_eq_foldl, hc, List.foldl_nil, table_init, hl, initV, Op.decode_code,
        typeOf_leaf]
  | union e₁ e₂ ih₁ ih₂ =>
      intro hv i he
      obtain ⟨c₁, c₂, hc, hl, h₁, h₂⟩ := he
      rw [val_eq_foldl, hc]
      simp only [List.foldl_cons, List.foldl_nil, table_init, table_step, hl,
        ih₁ (Valid.left hv) c₁ h₁, ih₂ (Valid.right hv) c₂ h₂, initV, Op.decode_code, dec_enc,
        stepV_unionEmpty, stepV_unionLeft, typeOf_union q hv]
  | addEdges a b e ih =>
      intro hv i he
      obtain ⟨c, hc, hl, h⟩ := he
      rw [val_eq_foldl, hc]
      simp only [List.foldl_cons, List.foldl_nil, table_init, table_step, hl,
        ih (Valid.of_addEdges hv) c h, initV, Op.decode_code, dec_enc, stepV_etaWait,
        typeOf_addEdges]
  | relabel a b e ih =>
      intro hv i he
      obtain ⟨c, hc, hl, h⟩ := he
      rw [val_eq_foldl, hc]
      simp only [List.foldl_cons, List.foldl_nil, table_init, table_step, hl,
        ih (Valid.of_relabel hv) c h, initV, Op.decode_code, dec_enc, stepV_rhoWait,
        typeOf_relabel]

/-! ### The root

At the root a valid expression has built the whole of `G`, so its type
is the `q`-type of `G` itself — after the label classes are forgotten
(`typ_forgetAll`), which is what lets adequacy read a sentence off it. -/

/-- **The root type decides every sentence of rank at most `q`.** -/
theorem sat_congr_typeOf {q : ℕ} (φ : MSO 0 0) (hq : rank φ ≤ q) {n₁ n₂ : ℕ}
    {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    {e₁ : Expr n₁ k} {e₂ : Expr n₂ k}
    (h₁ : ValidFor e₁ G₁) (h₂ : ValidFor e₂ G₂) (h : typeOf q e₁ = typeOf q e₂) :
    (Sat G₁ Fin.elim0 Fin.elim0 φ ↔ Sat G₂ Fin.elim0 Fin.elim0 φ) := by
  have hu₁ : ((verts e₁ : Finset (Fin n₁)) : Set (Fin n₁)) = Set.univ := by
    rw [h₁.verts_eq]; simp
  have hu₂ : ((verts e₂ : Finset (Fin n₂)) : Set (Fin n₂)) = Set.univ := by
    rw [h₂.verts_eq]; simp
  have hf := typ_forgetAll q (Fin.elim0 : Fin 0 → Set (Fin n₁))
    (Fin.elim0 : Fin 0 → Set (Fin n₂)) h
  refine sat_congr_sentence φ hq ?_
  have g₁ : typ G₁ Set.univ q Fin.elim0 Fin.elim0
      = typ (graph e₁) ((verts e₁ : Finset (Fin n₁)) : Set (Fin n₁)) q Fin.elim0 Fin.elim0 := by
    rw [h₁.graph_eq, hu₁]
  have g₂ : typ G₂ Set.univ q Fin.elim0 Fin.elim0
      = typ (graph e₂) ((verts e₂ : Finset (Fin n₂)) : Set (Fin n₂)) q Fin.elim0 Fin.elim0 := by
    rw [h₂.graph_eq, hu₂]
  rw [g₁, g₂]
  exact hf

/-- The accepting set of C9: the types realized by a graph satisfying
`φ`. Defined by an existential, so no choice is needed to state it and
the driver's accept table is a membership test. -/
def Accepts (q : ℕ) (φ : MSO 0 0) (t : T q 0 k) : Prop :=
  ∃ (m : ℕ) (G : SimpleGraph (Fin m)) (e : Expr m k),
    ValidFor e G ∧ typeOf q e = t ∧ Sat G Fin.elim0 Fin.elim0 φ

/-- Membership in the accepting set is satisfaction. -/
theorem accepts_typeOf {q : ℕ} (φ : MSO 0 0) (hq : rank φ ≤ q)
    {G : SimpleGraph (Fin n)} {e : Expr n k} (h : ValidFor e G) :
    Accepts q φ (typeOf q e) ↔ Sat G Fin.elim0 Fin.elim0 φ := by
  constructor
  · rintro ⟨m, G', e', h', ht, hs⟩
    exact (sat_congr_typeOf φ hq h' h ht).mp hs
  · intro hs
    exact ⟨n, G, e, h, rfl, hs⟩

open Classical in
/-- The accept table the driver reads: a number is accepting when it is
the number of a finished type in the accepting set. -/
noncomputable def acceptVal (q k : ℕ) (φ : MSO 0 0) (a : ℕ) : Bool :=
  match dec q k a with
  | .done t => decide (Accepts q φ t)
  | _ => false

/-- **The corollary the driver cashes in.** For a `k`-expression *for*
`G`, the fold's value at the root decides `φ`. -/
theorem acceptVal_val (q : ℕ) (φ : MSO 0 0) (hq : rank φ ≤ q)
    {G : SimpleGraph (Fin n)} {e : Expr n k} (hv : ValidFor e G)
    {par lab : ℕ → ℕ} {i : ℕ} (he : EncExpr par lab i e) :
    acceptVal q k φ (val (table q k) par lab i) = true ↔ Sat G Fin.elim0 Fin.elim0 φ := by
  rw [val_eq_typeOf q e hv.toValid i he, acceptVal, dec_enc]
  simpa using accepts_typeOf φ hq hv

/-! ### Smoke test

The path expression of `CliqueExpr.lean`, laid out as a parent-pointer
tree: seven nodes, children before parents, root last. Nothing here can
be `#eval`ed — the values are noncomputable — so what is checked is the
*encoding*: that the arrays a driver would produce really satisfy
`EncExpr`, computed by `decide` from the definitions of `children` and
`Op.code`. A correspondence relation no array satisfies would be
worthless. -/

/-- The parent array of `pathExpr`'s tree; the root (node 6) is its own
parent. -/
def pathPar : ℕ → ℕ := fun i => [2, 2, 3, 5, 5, 6, 6].getD i 0

/-- The op-code array of `pathExpr`'s tree, at `k = 2`: leaf 0, leaf 1,
`⊕`, `η 0 1`, leaf 0, `⊕`, `η 0 1`. -/
def pathLab : ℕ → ℕ := fun i => [1, 2, 0, 4, 1, 0, 4].getD i 0

example : EncExpr pathPar pathLab 6 pathExpr :=
  ⟨5, by decide, by decide,
    ⟨3, 4, by decide, by decide,
      ⟨2, by decide, by decide,
        ⟨0, 1, by decide, by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩⟩,
      ⟨by decide, by decide⟩⟩⟩

end Lax11Proofs.MsoTable
