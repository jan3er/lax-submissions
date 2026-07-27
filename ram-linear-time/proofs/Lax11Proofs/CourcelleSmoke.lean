import Lax11.Courcelle
import Lax11Proofs.CliqueExpr
import Mathlib.Tactic

/-!
Sanity check for the Courcelle surface: the two definitions the axiom of
`concepts/Lax11/Courcelle.lean` is stated over are exercised on concrete
objects, so that neither is vacuous and the index arithmetic of the
instance word is known to line up.

Two things are checked. First, satisfaction: the sentence "there are two
adjacent vertices" holds in the two-vertex complete graph and fails in
the two-vertex empty graph, computed from the surface `Sat` alone.
Second, the instance encoding: a literal word is exhibited as an
encoding of the path `0—1—2` together with the `2`-expression for it
from `CliqueExpr.lean`. The word is the compressed sparse row block of
the path followed by the expression block — the number of nodes, the
seven parents, the seven operation codes, the seven vertex names — and
`EncodesInstance` is proved for it, expression and all.

Nothing here is a proof of a submitted statement; this is a smoke test
of the concept surface, in the style of `EncodingSanity.lean`.
-/

namespace Lax11Proofs.CourcelleSmoke

open Lax11.Mso Lax11.CliqueExpr Lax11.Courcelle Lax11Proofs.CliqueExpr

/-! ### Satisfaction

The sentence `∃x ∃y (x adjacent y)`, at the surface's `Sat`. -/

/-- Some two vertices are adjacent. -/
def hasEdge : MSO 0 0 := .exV (.exV (.adj 0 1))

/-- The two-vertex complete graph has an edge. -/
example : Sat (⊤ : SimpleGraph (Fin 2)) Fin.elim0 Fin.elim0 hasEdge := by
  refine ⟨0, 1, ?_⟩
  show (⊤ : SimpleGraph (Fin 2)).Adj _ _
  simp only [SimpleGraph.top_adj]
  decide

/-- The two-vertex empty graph has none. -/
example : ¬ Sat (⊥ : SimpleGraph (Fin 2)) Fin.elim0 Fin.elim0 hasEdge := by
  rintro ⟨u, v, h⟩
  exact h

/-! ### The instance word

The path `0—1—2`, given both ways: as a compressed sparse row block and
as the `2`-expression `pathExpr`. -/

/-- The graph the instance is about: what `pathExpr` evaluates to, which
the smoke test of `CliqueExpr.lean` has already checked by computation
to be the path `0—1—2`. -/
def pathG : SimpleGraph (Fin 3) := graph pathExpr

instance : DecidableRel pathG.Adj := decidableAdj pathExpr

/-- The compressed sparse row block: three vertices, two edges, the
offsets `0, 1, 3, 4`, and the neighbours of `0`, then of `1`, then of
`2`. -/
def csrBlock : List ℕ := [3, 2, 0, 1, 3, 4, 1, 0, 2, 1]

/-- The expression block of `pathExpr`: seven nodes, then the parents
(the root, node `6`, is its own parent), then the operation codes at
`k = 2` — leaf 0, leaf 1, `⊕`, `η 0 1`, leaf 0, `⊕`, `η 0 1` — then the
vertex names, which matter at the three leaves and nowhere else. -/
def exprBlock : List ℕ :=
  [7] ++ [2, 2, 3, 5, 5, 6, 6] ++ [1, 2, 0, 4, 1, 0, 4] ++ [0, 1, 0, 0, 2, 0, 0]

/-- The instance word. -/
def instanceWord : List ℕ := csrBlock ++ exprBlock

private theorem pathG_adj_iff (u v : Fin 3) :
    pathG.Adj u v ↔ ((u : ℕ) = 0 ∧ (v : ℕ) = 1) ∨ ((u : ℕ) = 1 ∧ (v : ℕ) = 0)
      ∨ ((u : ℕ) = 1 ∧ (v : ℕ) = 2) ∨ ((u : ℕ) = 2 ∧ (v : ℕ) = 1) := by
  revert u v; decide

theorem encodesGraph_csrBlock : Lax11.GraphEncoding.EncodesGraph csrBlock 3 pathG where
  vertexCount_eq := rfl
  length_eq := rfl
  offset_zero := rfl
  offset_last := rfl
  offset_mono := by intro i hi; interval_cases i <;> decide
  target_lt := by
    intro j hj
    have hj : j < 4 := hj
    interval_cases j <;> decide
  adj_iff := by
    intro u v
    rw [pathG_adj_iff]
    fin_cases u <;> fin_cases v <;>
      simp only [csrBlock, Lax11.GraphEncoding.target, Lax11.GraphEncoding.offset,
        Lax11.GraphEncoding.vertexCount, List.getD_cons_zero, List.getD_cons_succ] <;>
      constructor <;>
      first
        | (rintro ⟨j, h1, h2, h3⟩; interval_cases j <;> simp_all)
        | (intro _; first
            | exact ⟨0, by decide⟩ | exact ⟨1, by decide⟩
            | exact ⟨2, by decide⟩ | exact ⟨3, by decide⟩
            | simp_all)

theorem encodesExprTree_exprBlock : EncodesExprTree exprBlock 7 2 where
  nodeCount_eq := rfl
  pos := by decide
  length_eq := by decide
  parent_gt := by
    intro i hi
    have hi' : i < 6 := by omega
    interval_cases i <;> decide
  opCode_lt := by intro i hi; interval_cases i <;> decide

theorem encodesExpr_exprBlock :
    EncodesExpr (parent exprBlock) (opCode exprBlock) (vertexName exprBlock) 6 pathExpr :=
  ⟨5, by decide, by decide,
    ⟨3, 4, by decide, by decide,
      ⟨2, by decide, by decide,
        ⟨0, 1, by decide, by decide,
          ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩⟩,
      ⟨by decide, by decide, by decide⟩⟩⟩

theorem validFor_pathExpr : ValidFor pathExpr pathG where
  nodup := by decide
  ops := by decide
  verts_eq := by decide
  graph_eq := rfl

/-- **The instance encoding is satisfiable**: one word presents the path
`0—1—2` in compressed sparse row form together with a `2`-expression for
it. -/
theorem encodesInstance_instanceWord : EncodesInstance instanceWord 3 pathG 2 :=
  ⟨csrBlock, exprBlock, 7, pathExpr, rfl, encodesGraph_csrBlock,
    encodesExprTree_exprBlock, encodesExpr_exprBlock, validFor_pathExpr⟩

end Lax11Proofs.CourcelleSmoke
