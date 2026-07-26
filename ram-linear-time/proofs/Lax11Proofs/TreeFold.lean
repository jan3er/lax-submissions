import Lax11Proofs.CCPhases

/-!
The tree-fold schema: a bottom-up fold over a parent-pointer tree,
driven by a table that the schema knows nothing about.

This is the shape every dynamic program on a tree decomposition has,
and it is built here once, generically, so that the algorithm and its
cost are settled before the mathematics that supplies the table exists.
The table is data — a finite function on a bounded alphabet — and the
program is generated from it: a prologue of stores materializes it into
arrays, and every use is then an array read. Nothing in the schema
requires the table to be *computed*; it may come from classical choice,
which is what lets the eventual type table be noncomputable.

Three decisions shape the file.

*The fold is sequential, not associative.* A node's value is a **left**
fold of its children's values, seeded by a value read off the node's own
label. Gluing a bag to its subtrees one child at a time is exactly this
shape, and it is not a fold of the children with each other: the seed
carries the node's own data, so the children are combined *into the
node*, never into one another. No commutativity, associativity or unit
is assumed anywhere.

*The children arrive in index order, and the sweep is one pass.* A node
is pushed into its parent as soon as it is finished, which is possible
because the encoding numbers children before parents. So the program
never searches for the children of a node — the quadratic trap — and
the order in which a node's children are folded is the increasing order
of their indices, which is what the pure model says too.

*There is no separate "adjust before passing up" table.* A unary map
applied to a value on its way to its parent is expressible by carrying
the node's label inside the value alphabet, and the table generation is
Lean-side and free. So the schema has two tables, not three, and the
per-node work is two array reads.
-/

namespace Lax11Proofs.TreeFold

open Lax11.Ram Lax11Proofs.Imp Lax11Proofs.Compile Lax11Proofs.Reasoning
open Lax11Proofs.CC (readLoop)

/-! ### The table

A table is a bounded alphabet of values, a bounded alphabet of labels,
a seed for each label, and a binary combination. It is `ℕ`-valued
throughout: the values of an eventual instantiation are numbered by an
enumeration of a `Fintype`, and the schema only ever needs the bound. -/

/-- The data driving a fold: values below `V`, labels below `L`, a seed
`init` for each label and a combination `step` of an accumulator with a
child's value. -/
structure Table where
  /-- Values are the naturals below this bound. -/
  V : ℕ
  /-- Labels are the naturals below this bound. -/
  L : ℕ
  /-- The value a node starts from, before any child is folded in. -/
  init : ℕ → ℕ
  /-- The accumulator after folding in one more child's value. -/
  step : ℕ → ℕ → ℕ

/-- A table is well-formed when its alphabet is closed under both
operations. This is all the program needs: every table lookup it makes
is then in range. -/
structure Table.Wf (T : Table) : Prop where
  /-- Seeds are values. -/
  init_lt : ∀ l < T.L, T.init l < T.V
  /-- Combinations of values are values. -/
  step_lt : ∀ a < T.V, ∀ b < T.V, T.step a b < T.V

/-! ### The pure model

The value of a node, by recursion on the tree, with no environment and
no program in sight. The recursion is bounded by an explicit fuel
rather than by well-founded recursion on the node index: the recursive
calls sit under a `foldl`, where the termination checker cannot see
that they are on smaller indices, and a fuel that is discharged once —
`valAux_eq_val` — costs less than fighting for it. -/

/-- The children of `i`: the nodes below `i` whose parent is `i`. The
encoding numbers children before parents, so this is the whole list. -/
def children (par : ℕ → ℕ) (i : ℕ) : List ℕ :=
  (List.range i).filter (fun c => par c == i)

/-- The children of `i` among the first `j` nodes. -/
def childrenUpTo (par : ℕ → ℕ) (i j : ℕ) : List ℕ :=
  (List.range (min i j)).filter (fun c => par c == i)

theorem childrenUpTo_self {par : ℕ → ℕ} {i j : ℕ} (h : i ≤ j) :
    childrenUpTo par i j = children par i := by
  simp [childrenUpTo, children, Nat.min_eq_left h]

/-- The value of node `i`, unfolding the tree at most `k` levels. -/
def valAux (T : Table) (par lab : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, i =>
      (children par i).foldl (fun a c => T.step a (valAux T par lab k c)) (T.init (lab i))

/-- The value of node `i`: the left fold of its children's values, in
increasing order of index, seeded by its label's entry in the table. -/
def val (T : Table) (par lab : ℕ → ℕ) (i : ℕ) : ℕ := valAux T par lab (i + 1) i

private theorem foldl_val_congr {T : Table} {par lab : ℕ → ℕ} {k : ℕ} {cs : List ℕ}
    (hcs : ∀ c ∈ cs, c < k) (ih : ∀ c < k, valAux T par lab k c = val T par lab c) :
    ∀ a, cs.foldl (fun a c => T.step a (valAux T par lab k c)) a =
      cs.foldl (fun a c => T.step a (val T par lab c)) a := by
  induction cs with
  | nil => intro a; rfl
  | cons c cs ihcs =>
      intro a
      simp only [List.foldl_cons, ih c (hcs c (by simp))]
      exact ihcs (fun d hd => hcs d (by simp [hd])) _

theorem mem_children {par : ℕ → ℕ} {i c : ℕ} (h : c ∈ children par i) : c < i ∧ par c = i := by
  simp [children, List.mem_filter, List.mem_range] at h
  exact ⟨h.1, h.2⟩

/-- Enough fuel computes the value. -/
theorem valAux_eq_val (T : Table) (par lab : ℕ → ℕ) :
    ∀ k i, i < k → valAux T par lab k i = val T par lab i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      match k with
      | 0 => intro i hi; omega
      | k + 1 =>
          intro i hi
          have hk : ∀ c < k, valAux T par lab k c = val T par lab c :=
            fun c hc => ih k (by omega) c hc
          have hi' : ∀ c < i, valAux T par lab i c = val T par lab c :=
            fun c hc => ih i (by omega) c hc
          show (children par i).foldl _ _ = valAux T par lab (i + 1) i
          rw [show valAux T par lab (i + 1) i =
            (children par i).foldl (fun a c => T.step a (valAux T par lab i c))
              (T.init (lab i)) from rfl]
          rw [foldl_val_congr (fun c hc => lt_of_lt_of_le (mem_children hc).1 (by omega)) hk,
            foldl_val_congr (fun c hc => (mem_children hc).1) hi']

/-- The equation the model is used through. -/
theorem val_eq_foldl (T : Table) (par lab : ℕ → ℕ) (i : ℕ) :
    val T par lab i =
      (children par i).foldl (fun a c => T.step a (val T par lab c)) (T.init (lab i)) := by
  show valAux T par lab (i + 1) i = _
  exact foldl_val_congr (fun c hc => (mem_children hc).1)
    (fun c hc => valAux_eq_val T par lab i c hc) _

/-- Values stay in the alphabet. -/
theorem val_lt {T : Table} (hT : T.Wf) {par lab : ℕ → ℕ}
    (hlab : ∀ i, lab i < T.L) : ∀ i, val T par lab i < T.V := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      rw [val_eq_foldl]
      have key : ∀ (cs : List ℕ), (∀ c ∈ cs, c < i) → ∀ a < T.V,
          cs.foldl (fun a c => T.step a (val T par lab c)) a < T.V := by
        intro cs
        induction cs with
        | nil => intro _ a ha; exact ha
        | cons c cs ihcs =>
            intro hcs a ha
            exact ihcs (fun d hd => hcs d (by simp [hd])) _
              (hT.step_lt a ha _ (ih c (hcs c (by simp))))
      exact key _ (fun c hc => (mem_children hc).1) _ (hT.init_lt _ (hlab i))

/-! ### The sweep, still pure

The program does not recurse: it runs an accumulator array over the
nodes in increasing order, pushing each finished node into its parent.
That sweep is a Lean recursion too, and the theorem that it computes
the tree fold is proved here, away from any environment — so that the
`Run` lemma has only representation left to do. -/

/-- The accumulator array after the nodes `0, …, j-1` have been pushed
into their parents. -/
def sweep (T : Table) (par lab : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => fun i => T.init (lab i)
  | j + 1 => fun i =>
      if i = par j then T.step (sweep T par lab j (par j)) (sweep T par lab j j)
      else sweep T par lab j i

/-- After `j` pushes, every node holds the fold of the children it has
seen so far. Only the parent pointers actually used are constrained. -/
theorem sweep_eq_foldl (T : Table) (par lab : ℕ → ℕ) :
    ∀ j, (∀ c < j, c < par c) → ∀ i, sweep T par lab j i =
      (childrenUpTo par i j).foldl (fun a c => T.step a (val T par lab c)) (T.init (lab i)) := by
  intro j
  induction j with
  | zero => intro _ i; simp [sweep, childrenUpTo]
  | succ j ih =>
      intro hpar i
      have ihj := ih (fun c hc => hpar c (by omega))
      have hjp : j < par j := hpar j (by omega)
      -- the children of `i` among the first `j+1` nodes
      have hsplit : childrenUpTo par i (j + 1) =
          if par j = i ∧ j < i then childrenUpTo par i j ++ [j] else childrenUpTo par i j := by
        simp only [childrenUpTo]
        rcases lt_or_ge j i with hji | hji
        · rw [Nat.min_eq_right (by omega : j + 1 ≤ i), Nat.min_eq_right (by omega : j ≤ i),
            List.range_succ, List.filter_append]
          by_cases hp : par j = i
          · simp [hp, hji]
          · simp [hp]
        · rw [Nat.min_eq_left (by omega : i ≤ j + 1), Nat.min_eq_left (by omega : i ≤ j)]
          simp [Nat.not_lt.mpr hji]
      by_cases hp : i = par j
      · subst hp
        have hsw : sweep T par lab (j + 1) (par j) =
            T.step (sweep T par lab j (par j)) (sweep T par lab j j) := by simp [sweep]
        rw [hsw, hsplit, if_pos ⟨rfl, hjp⟩, List.foldl_append, List.foldl_cons, List.foldl_nil,
          ihj (par j), ihj j, childrenUpTo_self (le_refl j), ← val_eq_foldl]
      · have hsw : sweep T par lab (j + 1) i = sweep T par lab j i := by simp [sweep, hp]
        rw [hsw, hsplit, if_neg (by tauto)]
        exact ihj i

/-- Once the sweep has passed a node, that node holds its value. -/
theorem sweep_eq_val (T : Table) (par lab : ℕ → ℕ) {i j : ℕ}
    (hpar : ∀ c < j, c < par c) (hij : i ≤ j) :
    sweep T par lab j i = val T par lab i := by
  rw [sweep_eq_foldl T par lab j hpar i, childrenUpTo_self hij, ← val_eq_foldl]

/-! ### The encoding

The instance word is the number of nodes, then the parent of each node,
then the label of each node. Children are numbered before parents and
the root is the last node — a rooted tree always admits such a
numbering, so the hypothesis costs no generality, and it is what makes
the sweep a single forward pass. The root's own parent entry is present
(the block has one number per node) and never read. -/

/-- `x` encodes the tree on `N` nodes with parent function `par` and
labels `lab`, for a table with `L` labels. -/
def EncodesTree (x : List ℕ) (N : ℕ) (par lab : ℕ → ℕ) (L : ℕ) : Prop :=
  1 ≤ N ∧ x = N :: (arrOf N par ++ arrOf N lab) ∧
    (∀ i, i + 1 < N → i < par i ∧ par i < N) ∧ (∀ i < N, lab i < L)

/-! ### The table, materialized

Three arrays hold the table. `ini` is the seed for each label. The
combination is a square array `tab` read at `a * V + b`, and since the
machine language has no multiplication, the row bases `a * V` are
themselves a table, `row`. So a combination costs two array reads and
one addition, and the program contains no arithmetic that depends on
the alphabet size. -/

/-- The seeds, one per label. -/
def initList (T : Table) : List ℕ := arrOf T.L T.init

/-- The row bases of the combination table. -/
def rowList (T : Table) : List ℕ := arrOf T.V (fun a => a * T.V)

/-- The combination table, row by row. -/
def stepList (T : Table) : List ℕ := arrOf (T.V * T.V) (fun k => T.step (k / T.V) (k % T.V))

/-- Store the list `vs` into the array `a` from position `i` on: the
prologue that puts a table into memory, one store per entry. -/
def storesFrom (a : String) : ℕ → List ℕ → Com
  | _, [] => .skip
  | i, v :: vs => .seq (.store a (.lit i) (.lit v)) (storesFrom a (i + 1) vs)

/-- Store the list `vs` into the array `a`. -/
def stores (a : String) (vs : List ℕ) : Com := storesFrom a 0 vs

/-! ### The program -/

/-- Seed every node with its label's entry. This pass exists because a
node must be seeded before any of its children pushes into it, and its
children come earlier in the sweep. -/
def seedLoop : Com :=
  .seq (.assign "i" (.lit 0))
    (.while (.lt (.var "i") (.var "N"))
      (.seq (.store "acc" (.var "i") (.get "ini" (.get "lab" (.var "i"))))
        (.assign "i" (.add (.var "i") (.lit 1)))))

/-- The sweep: push each node but the root into its parent. The parent
is a later node, so its accumulator is still open; the node's own
accumulator is complete, because all of its children are earlier. -/
def pushLoop : Com :=
  .seq (.assign "i" (.lit 0))
    (.while (.lt (.var "i") (.sub (.var "N") (.lit 1)))
      (.seq (.assign "p" (.get "par" (.var "i")))
        (.seq (.store "acc" (.var "p")
                (.get "tab" (.add (.get "row" (.get "acc" (.var "p")))
                  (.get "acc" (.var "i")))))
          (.assign "i" (.add (.var "i") (.lit 1))))))

/-- The whole schema: read the tree, materialize the table, seed,
sweep, write the root's value. -/
def foldCom (T : Table) : Com :=
  .seq (.read "N") <|
  .seq (readLoop "par" "N") <|
  .seq (readLoop "lab" "N") <|
  .seq (stores "ini" (initList T)) <|
  .seq (stores "row" (rowList T)) <|
  .seq (stores "tab" (stepList T)) <|
  .seq seedLoop <|
  .seq pushLoop <|
  .write (.get "acc" (.sub (.var "N") (.lit 1)))

/-- Four scalars, six arrays, four temporaries (the deepest expression
is the combination lookup, which nests three array reads). -/
def layout : Layout :=
  ⟨["N", "i", "t", "p"], ["par", "lab", "acc", "ini", "row", "tab"], 4⟩

/-- The machine program for a given table. -/
def foldProgram (T : Table) : Program := compileProgram layout (foldCom T)

/-! ### The program, run

The house discipline: the machine program is checked against the pure
model by evaluation before anything is proved. `runOut` runs to a halt
and reports the output tape and the number of steps; it is the same
three lines as in `CC.lean`, kept here so that this file depends on
nothing of the connected-components driver but its read loop. -/

/-- Run a machine program to a halt within `f` steps, reporting the
output tape and the number of steps taken. -/
def runOut : ℕ → Program → State → ℕ → Option (List ℕ × ℕ)
  | 0, _, _, _ => none
  | f + 1, p, s, k =>
      match step p s with
      | none => some (s.out, k)
      | some s' => runOut f p s' (k + 1)

/-- The instance word of a tree given by two lists. -/
def encTree (parL labL : List ℕ) : List ℕ := parL.length :: (parL ++ labL)

/-- What the model says the output is. -/
def modelOut (T : Table) (parL labL : List ℕ) : List ℕ :=
  [val T (fun i => parL.getD i 0) (fun i => labL.getD i 0) (parL.length - 1)]

/-- What the machine says the output is. -/
def machineOut (T : Table) (parL labL : List ℕ) : Option (List ℕ) :=
  (runOut 300000 (foldProgram T) (initState (encTree parL labL)) 0).map Prod.fst

/-- Subtree label sums, modulo three: commutative, so it checks the
arithmetic and the tree walk but not the order of the children. -/
def sumTable : Table where
  V := 3
  L := 3
  init l := l % 3
  step a b := (a + b) % 3

/-- A deliberately non-commutative, non-associative table: the value
depends on the order in which the children are folded in, so a schema
that visited them in the wrong order would be caught. -/
def skewTable : Table where
  V := 5
  L := 5
  init l := l % 5
  step a b := (2 * a + b + 1) % 5

-- one node, the root alone
#guard machineOut sumTable [0] [2] = some (modelOut sumTable [0] [2])
-- a path 0 → 1 → 2 → 3
#guard machineOut sumTable [1, 2, 3, 0] [1, 1, 1, 1] = some (modelOut sumTable [1, 2, 3, 0] [1, 1, 1, 1])
-- a star with three leaves
#guard machineOut sumTable [3, 3, 3, 0] [0, 1, 2, 1] = some (modelOut sumTable [3, 3, 3, 0] [0, 1, 2, 1])
-- a tree of depth two: 0,1 under 4; 2,3,4 under the root 5. The labels
-- stay below `L`, which is not a formality: the first run of this test
-- used labels `3` and `4` against a three-label table, and the machine
-- read past the seed array into the interleaved cells of another one
-- while the model went on computing — the mismatch is exactly the
-- `lab i < L` clause of `EncodesTree`.
#guard machineOut sumTable [4, 4, 5, 5, 5, 0] [1, 2, 0, 1, 0, 1] =
  some (modelOut sumTable [4, 4, 5, 5, 5, 0] [1, 2, 0, 1, 0, 1])
-- the same trees against the order-sensitive table
#guard machineOut skewTable [0] [3] = some (modelOut skewTable [0] [3])
#guard machineOut skewTable [1, 2, 3, 0] [1, 4, 2, 3] = some (modelOut skewTable [1, 2, 3, 0] [1, 4, 2, 3])
#guard machineOut skewTable [3, 3, 3, 0] [0, 1, 2, 1] = some (modelOut skewTable [3, 3, 3, 0] [0, 1, 2, 1])
#guard machineOut skewTable [4, 4, 5, 5, 5, 0] [1, 2, 4, 3, 0, 2] =
  some (modelOut skewTable [4, 4, 5, 5, 5, 0] [1, 2, 4, 3, 0, 2])
-- the order-sensitive table really is order-sensitive: swapping two
-- children of the root changes the answer
#guard modelOut skewTable [4, 4, 5, 5, 5, 0] [1, 2, 3, 4, 0, 2] ≠
  modelOut skewTable [4, 4, 5, 5, 5, 0] [1, 2, 4, 3, 0, 2]

end Lax11Proofs.TreeFold
