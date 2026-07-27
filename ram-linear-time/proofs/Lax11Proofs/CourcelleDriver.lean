import Lax11Proofs.MsoTable
import Lax11Proofs.TreeFoldRun
import Lax11Proofs.CourcelleSmoke

/-!
The driver of Courcelle's theorem: the program, and the two bridges
from the instance word to the fold.

Everything the program does has been proved somewhere else. The fold
schema of `TreeFold.lean` reads a parent-pointer tree and computes a
table's fold over it; `MsoTable.lean` supplies the table, and its
`acceptVal_val` says the root value decides the sentence. What is left,
and what this file is, is the *instance word*: the surface encoding of
`Lax11.InstanceEncoding` presents a compressed sparse row block followed by an
expression block of three arrays, and the schema's own encoding is
neither of those. So the program here is the schema's program with a
different front end and a one-instruction epilogue.

Three things are worth saying about it.

*The program never looks at the graph.* It reads the compressed sparse
row block only to get past it — two header entries, then `n + 1 + 2m`
numbers dropped into an array that is never read again — and the
expression block's vertex-name array likewise. That is not an
optimization, it is the content of the theorem: the graph is determined
by the expression, so the certificate is all the program needs, and the
first block is there for the *statement*, to say which graph the
sentence is about. The two junk arrays are the honest way to write "read
and discard" in a language whose only input construct is a read.

*The accept bit is a table lookup, not a decision.* The root's value is
a number naming a type, and whether that type is accepting is a fact
about the mathematics, not something the program could compute. So the
accepting set is materialized as one more array — `arrOf T.V` of a
noncomputable function, exactly like the three tables of the schema —
and the epilogue is a single `write` of `acp[acc[N-1]]`. Plan decision
C9, at three lines of program text.

*The program is generic in the table.* `driverCom` takes the table and
the accepting-set array as data, so it can be instantiated with a
computable stand-in and run. It is: the smoke test at the end runs the
compiled machine on the literal instance word of `CourcelleSmoke.lean`
against a hand table that decides whether the graph has an edge. The
real table is noncomputable and can never be run, which is exactly why
the plumbing has to be tested against one that can.
-/

namespace Lax11Proofs.Courcelle

open Lax13.Ram Lax13.RamComputes Lax11.GraphEncoding Lax11.Mso Lax11.CliqueExpr
open Lax13Proofs.Imp Lax13Proofs.Compile Lax13Proofs.Reasoning
open Lax11Proofs.CliqueExpr Lax11Proofs.TreeFold Lax11Proofs.MsoTable
open Lax11Proofs.CC (readLoop)
open Lax11.InstanceEncoding (nodeCount parent opCode vertexName EncodesExprTree EncodesExpr
  EncodesModelCheckingInstance)

/-! ### The program

The schema's phases, with the two blocks of the instance word in front
and the accept lookup behind. -/

/-- The driver, for a given table and a given accepting-set array.
The first four phases consume the compressed sparse row block: its two
header entries give its length, and the rest goes into `csr`, which
nothing ever reads. The expression block is then read as the schema
wants it — one number for the node count, then the parents and the op
codes — followed by the vertex names, which go into `ids` and are, for
the same reason, never read again. -/
def driverCom (T : Table) (acp : ℕ → ℕ) : Com :=
  .seq (.read "n") <|
  .seq (.read "m") <|
  .seq (.assign "len" (.add (.add (.var "n") (.lit 1)) (.add (.var "m") (.var "m")))) <|
  .seq (readLoop "csr" "len") <|
  .seq (.read "N") <|
  .seq (readLoop "par" "N") <|
  .seq (readLoop "lab" "N") <|
  .seq (readLoop "ids" "N") <|
  .seq (stores "ini" (initList T)) <|
  .seq (stores "row" (rowList T)) <|
  .seq (stores "tab" (stepList T)) <|
  .seq (stores "acp" (arrOf T.V acp)) <|
  .seq seedLoop <|
  .seq pushLoop <|
  .write (.get "acp" (.get "acc" (.sub (.var "N") (.lit 1))))

/-- Seven scalars, nine arrays, four temporaries. Three of the arrays
(`csr`, `ids`, and the accepting set `acp`) are what this layout has
beyond the schema's own. -/
def layout : Layout :=
  ⟨["N", "n", "m", "len", "i", "t", "p"],
   ["csr", "par", "lab", "ids", "acc", "ini", "row", "tab", "acp"], 4⟩

/-- The machine program of the driver. -/
def driverProgram (T : Table) (acp : ℕ → ℕ) : Program :=
  compileProgram layout (driverCom T acp)

/-- The driver fits its layout, whatever the table and the accepting
set are: only the lengths of the four store prologues depend on them. -/
theorem driverCom_ok (T : Table) (acp : ℕ → ℕ) : Com.Ok layout (driverCom T acp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    storesFrom_ok ?_ ?_ 0 _, storesFrom_ok ?_ ?_ 0 _, storesFrom_ok ?_ ?_ 0 _,
    storesFrom_ok ?_ ?_ 0 _, ?_, ?_, ?_⟩ <;>
    simp [readLoop, seedLoop, pushLoop, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-- The array extents the driver runs with, chosen per input (D17): the
junk array for the graph block is as long as that block, the four arrays
of the expression block have one entry per node, and the four tables
have the sizes the table fixes. -/
def driverExt (T : Table) (n m N : ℕ) (a : String) : ℕ :=
  if a = "csr" then n + 1 + (m + m)
  else if a = "ini" then T.L
  else if a = "row" then T.V
  else if a = "tab" then T.V * T.V
  else if a = "acp" then T.V
  else N

/-! ### The first bridge: the surface relation forgets to the fold's

`Lax11.InstanceEncoding.EncodesExpr` and `MsoTable.EncExpr` are the same
recursion, except that the surface one also pins the vertex name at
every leaf — the certificate clause the program has no use for. The
forgetful direction is a structural induction with nothing in it; the
two `children` are syntactically the same definition, so they need not
even be rewritten. -/

/-- The schema's children and the surface's are the same list. -/
theorem children_eq (par : ℕ → ℕ) (i : ℕ) :
    Lax11.InstanceEncoding.children par i = TreeFold.children par i := rfl

/-- **The surface encoding relation implies the fold's.** -/
theorem encExpr_of_encodesExpr {n k : ℕ} {par lab ids : ℕ → ℕ} :
    ∀ (e : Expr n k) (i : ℕ), EncodesExpr par lab ids i e → EncExpr par lab i e := by
  intro e
  induction e with
  | leaf v l => rintro i ⟨hc, hl, _⟩; exact ⟨hc, hl⟩
  | union e₁ e₂ ih₁ ih₂ =>
      rintro i ⟨c₁, c₂, hc, hl, h₁, h₂⟩
      exact ⟨c₁, c₂, hc, hl, ih₁ c₁ h₁, ih₂ c₂ h₂⟩
  | addEdges a b e ih => rintro i ⟨c, hc, hl, h⟩; exact ⟨c, hc, hl, ih c h⟩
  | relabel a b e ih => rintro i ⟨c, hc, hl, h⟩; exact ⟨c, hc, hl, ih c h⟩

/-! ### The second bridge: the instance word, as the program reads it

The program's view of the word is a list of segments: two header
numbers, the rest of the graph block, the node count, and then three
arrays of `N` numbers each. `EncodesModelCheckingInstance` states its clauses through
the accessors `parent`, `opCode`, `vertexName`, which are `List.getD` at
computed offsets; this lemma turns the whole package into the segments
and the two functions the fold speaks about. -/

/-- Reading a segment of a list back out of it. -/
theorem getD_take {l : List ℕ} {b i : ℕ} (h : i < b) : (l.take b).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos h]

/-- Reading past a dropped prefix. -/
theorem getD_drop (l : List ℕ) (a i : ℕ) : (l.drop a).getD i 0 = l.getD (a + i) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **The instance word, decomposed.** Everything the driver's run needs
about an admissible input: the four segments the reads consume, their
lengths, the two functions the fold folds over, and the expression that
the second block encodes. -/
theorem instance_tape {x : List ℕ} {n k : ℕ} {G : SimpleGraph (Fin n)}
    (hx : EncodesModelCheckingInstance x n G k) :
    ∃ (m N : ℕ) (gr tr : List ℕ) (e : Expr n k),
      x = n :: m :: (gr ++ N :: tr) ∧ gr.length = n + 1 + (m + m) ∧
        tr.length = 3 * N ∧ 1 ≤ N ∧ N ≤ x.length ∧
        n + 1 + (m + m) ≤ x.length ∧
        (∀ i, i + 1 < N → i < tr.getD i 0 ∧ tr.getD i 0 < N) ∧
        (∀ i < N, tr.getD (N + i) 0 < opCard k) ∧
        ValidFor e G ∧
        EncExpr (fun i => tr.getD i 0) (fun i => tr.getD (N + i) 0) (N - 1) e := by
  obtain ⟨g, t, e, rfl, hg, ht, he, hvf⟩ := hx
  -- the graph block: two header entries, then the offsets and the targets
  obtain ⟨b, gr, rfl⟩ : ∃ b gr, g = n :: b :: gr := by
    cases g with
    | nil => have := hg.length_eq; simp at this; omega
    | cons a g₁ =>
        cases g₁ with
        | nil => have := hg.length_eq; simp at this; omega
        | cons b gr =>
            refine ⟨b, gr, ?_⟩
            rw [show a = n from hg.vertexCount_eq]
  have hgrlen : gr.length = n + 1 + (b + b) := by
    have hlen := hg.length_eq
    rw [show edgeCount (n :: b :: gr) = b from rfl] at hlen
    simp at hlen
    omega
  -- the expression block: the node count, then three arrays
  obtain ⟨N, tr, rfl⟩ : ∃ N tr, t = N :: tr := by
    cases t with
    | nil =>
        have h0 : nodeCount ([] : List ℕ) = 0 := rfl
        have := ht.length_eq; rw [h0] at this; simp at this
    | cons c tr => exact ⟨c, tr, rfl⟩
  -- the node count is the block's first entry, so it is `N` by definition
  have hN : nodeCount (N :: tr) = N := rfl
  have htrlen : tr.length = 3 * N := by
    have := ht.length_eq; rw [hN] at this; simp at this; omega
  -- the two accessors, as functions of the segment
  have hpar : parent (N :: tr) = fun i => tr.getD i 0 := by
    funext i
    show (N :: tr).getD (1 + i) 0 = _
    rw [Nat.add_comm]
    rfl
  have hlab : opCode (N :: tr) = fun i => tr.getD (N + i) 0 := by
    funext i
    show (N :: tr).getD (1 + nodeCount (N :: tr) + i) 0 = _
    rw [hN, show 1 + N + i = (N + i) + 1 from by omega]
    rfl
  refine ⟨b, N, gr, tr, e, rfl, hgrlen, htrlen, ht.pos, ?_, ?_, ?_, ?_, hvf, ?_⟩
  · simp; omega
  · simp; omega
  · intro i hi
    have := ht.parent_gt i hi
    rwa [hpar] at this
  · intro i hi
    have := ht.opCode_lt i hi
    rwa [hlab] at this
  · have := encExpr_of_encodesExpr e (N - 1) he
    rwa [hpar, hlab] at this

/-! ### The program, run on a table that can be run

The house discipline is to `#eval` the compiled machine against the
model before proving anything about it. The table of the theorem is
noncomputable — it is extracted by choice from the congruences of
`MsoCliqueOps.lean` — so what is run here is a stand-in of exactly the
same shape: a table over the *same* operation alphabet, decoded with the
*same* `Op.decode`, whose values are the three bits "class `0` is
nonempty", "class `1` is nonempty", "the graph has an edge", together
with the partial states the schema's sequential fold needs. That is a
genuine clique-width dynamic program: `η i j` with `i ≠ j` creates an
edge exactly when both classes are nonempty, and `⊕` and `ρ` are the
obvious things.

So the two sentences the run decides are "some two vertices are
adjacent" and its negation, and the instance is the literal word of
`CourcelleSmoke.lean` — the path `0—1—2` in compressed sparse row form
followed by the `2`-expression `pathExpr`. The path has an edge, so the
machine must write `1` for the first and `0` for the second, and it must
get there having skipped a graph block and a vertex-name array it never
reads. -/

private def b0 (v : ℕ) : ℕ := v % 2
private def b1 (v : ℕ) : ℕ := v / 2 % 2
private def b2 (v : ℕ) : ℕ := v / 4 % 2
private def mkD (a b e : ℕ) : ℕ := a + 2 * b + 4 * e

/-- The stand-in table at `k = 2`: values `0 … 7` are the finished
states (the three bits), `8` is a `⊕` with nothing absorbed, `9 … 16` a
`⊕` with its left child absorbed, and `17 … 21` the five unary waits
(`η` with distinct classes, `η` with equal classes, `ρ 0 1`, `ρ 1 0`,
`ρ i i`). -/
def edgeTable : Table where
  V := 22
  L := opCard 2
  init c :=
    match Op.decode 2 c with
    | .union => 8
    | .leaf l => if (l : ℕ) = 0 then mkD 1 0 0 else mkD 0 1 0
    | .eta i j => if i = j then 18 else 17
    | .rho i j =>
        if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then 19
        else if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then 20 else 21
  step a b :=
    if 8 ≤ b then 8
    else if a = 8 then 9 + b
    else if 9 ≤ a ∧ a ≤ 16 then
      mkD (max (b0 (a - 9)) (b0 b)) (max (b1 (a - 9)) (b1 b)) (max (b2 (a - 9)) (b2 b))
    else if a = 17 then mkD (b0 b) (b1 b) (max (b2 b) (min (b0 b) (b1 b)))
    else if a = 18 then b
    else if a = 19 then mkD 0 (max (b0 b) (b1 b)) (b2 b)
    else if a = 20 then mkD (max (b0 b) (b1 b)) 0 (b2 b)
    else if a = 21 then b
    else 8

/-- The accepting set of "some two vertices are adjacent". -/
def acpEdge (v : ℕ) : ℕ := if v < 8 ∧ b2 v = 1 then 1 else 0

/-- The accepting set of its negation. -/
def acpNoEdge (v : ℕ) : ℕ := if v < 8 ∧ b2 v = 0 then 1 else 0

/-- Run the driver on a word, at a word length that holds every number
the stand-in table and this instance produce. -/
def runDriver (T : Table) (acp : ℕ → ℕ) (x : List ℕ) : Option (List ℕ) :=
  (runOut 16 2000000 (driverProgram T acp) (initState x) 0).map Prod.fst

-- the model is the model *of that word*: the parent and op-code arrays
-- the driver reads out of the expression block are the ones `MsoTable`'s
-- smoke test proved to encode `pathExpr`. Without this the machine run
-- and the model run would be joined by nothing but the reader's eye.
#guard (List.range 7).all fun i =>
  parent CourcelleSmoke.exprBlock i == pathPar i &&
    opCode CourcelleSmoke.exprBlock i == pathLab i

-- the model, by hand: the root of `pathExpr` has both classes nonempty
-- and an edge, so its value is `mkD 1 1 1 = 7`
#guard val edgeTable pathPar pathLab 6 = 7

-- the machine agrees with the model, on the word the surface smoke test
-- proved to be an encoding of the path together with a `2`-expression
-- for it, and the two accepting sets pick out the two answers
#guard runDriver edgeTable acpEdge CourcelleSmoke.instanceWord =
  some [acpEdge (val edgeTable pathPar pathLab 6)]
#guard runDriver edgeTable acpNoEdge CourcelleSmoke.instanceWord =
  some [acpNoEdge (val edgeTable pathPar pathLab 6)]
#guard runDriver edgeTable acpEdge CourcelleSmoke.instanceWord = some [1]
#guard runDriver edgeTable acpNoEdge CourcelleSmoke.instanceWord = some [0]

/-! ### No multiplication anywhere in the compiled program

The fold indexes a square table, which is where a multiplication would
naturally appear, and a linear-time claim on a unit-cost machine that
leans on unit-cost multiplication is at risk of being an artifact of the
model. The row bases are materialized instead, so the program is
addition, subtraction and control only. That is a property of the
program text, and the program text is the same for every table — only
the lengths of the four store prologues depend on it — so it is checked
here by evaluation rather than asserted in an annotation. -/

/-- The instructions whose unit cost a strict reading of the model would
object to. -/
def isWideInstr : Instr → Bool
  | .mul _ => true
  | .div _ => true
  | .shiftl _ => true
  | .shiftr _ => true
  | _ => false

#guard ((driverProgram edgeTable acpEdge).filter isWideInstr).isEmpty

end Lax11Proofs.Courcelle
