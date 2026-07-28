import Lax3.FirstOrder
import Lax12.NowhereDenseClasses
import Lax13.RamComputes
import Lax11.GraphEncoding
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: First-order model checking on nowhere dense classes in almost linear time
type: theorem
---
Deciding a first-order sentence is fixed-parameter tractable on every
nowhere dense class of graphs, in almost linear time on a word random
access machine: for every nowhere dense class, every sentence φ and
every ε > 0 there are one program, one constant *c* and one time bound
*T* with *T*(x) ≤ *c* · (|x| + 1)^(1+ε), such that at every word
length *w*, on every member of the class given in compressed sparse
row form as a word *x* each of whose entries *v* satisfies
*c*(|x| + *v* + 1) ≤ 2^*w*, the program halts within *T*(x) steps and
writes `1` if φ holds in the graph and `0` if it does not.

This is the theorem of Grohe, Kreutzer and Siebertz (JACM 2017), with
the algorithm realized on the word RAM of Lax13. Nowhere denseness is
the exact limit of this kind of tractability on monotone classes, and
the input is the graph *alone*: unlike the Courcelle theorem of Lax11,
which is handed a k-expression alongside the graph, every auxiliary
object the algorithm consumes — orderings, neighborhood covers,
splitter moves, distance profiles — is computed from the input. That
computation is the main algorithmic weight of the theorem.

# Formalization notes

The statement follows the house pattern of Lax11's Courcelle axiom:
program and constant after the class data, the sentence and ε; before
the graph and the word length; inputs restricted to encodings whose
entries fit the word length under the same `c * (x.length + v + 1) ≤
2 ^ w` side condition; output by a classical `if` on satisfaction.
The differences are the ones the theorem is about. The hypothesis is
`Lax12.NowhereDense` verbatim — the endorsed shallow-minor form, not a
restatement. The input predicate is `Lax11.EncodesGraph` alone: no
expression, no ordering, no promise beyond membership in the class.
The time bound cannot be the Courcelle form `c * (x.length + 1)`,
since `n^(1+ε)` has no elementary spelling over ℕ: the bound function
`T : List ℕ → ℕ` is existentially quantified and pinned by the
real-valued side condition `(T x : ℝ) ≤ c * ((x.length : ℝ) + 1) ^
(1 + ε)` — the same real-exponent idiom as Lax12's subpolynomial
bounds, whose `^` is `Real.rpow`.

The sentence ranges over plain first-order logic on graphs, `FO 0` of
this submission — adjacency and equality, no colors: colors and
distance atoms are working machinery of the proof, and surfacing them
in the headline would weaken it (a statement over colored graphs
follows by the standard encoding of colors as input, and the distance
logic's headline role is played by the locality theorem concept). The
parameter dependence f(φ, ε, C) of the fixed-parameter claim lives in
the existential `c` and `T`, as in the source; the class enters
through the choice of `c` and `T` only, the program depending on
finitely many of its excluded-minor thresholds.
-/

namespace Lax3.ModelChecking

open Lax3.FirstOrder
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax13.Ram Lax13.RamComputes
open Lax11.GraphEncoding

open Classical in
/-- **First-order model checking on nowhere dense classes** (Grohe–
Kreutzer–Siebertz): for every nowhere dense class, sentence and
ε > 0, there are a program, a constant `c` and a time bound `T` with
`T x ≤ c * (|x| + 1) ^ (1 + ε)`, such that at every word length `w`,
on every member of the class in compressed sparse row form as a word
`x` each of whose entries `v` satisfies `c * (x.length + v + 1) ≤
2 ^ w`, the program halts within `T x` steps, having written `1` if
the sentence holds in the graph and `0` otherwise. -/
axiom exists_almostLinearTime_program_modelChecking :
    ∀ (C : GraphClass), NowhereDense C →
    ∀ (φ : FO 0) (ε : ℝ), 0 < ε →
      ∃ (p : Program) (c : ℕ) (T : List ℕ → ℕ),
        (∀ x : List ℕ, (T x : ℝ) ≤ c * ((x.length : ℝ) + 1) ^ (1 + ε)) ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
          ComputesInTime w p
            {x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w}
            (fun _ => if Sat G Fin.elim0 φ then [1] else [0])
            T

end Lax3.ModelChecking
