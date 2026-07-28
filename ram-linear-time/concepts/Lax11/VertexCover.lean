import Lax13.RamComputes
import Lax11.GraphEncoding
import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-!
---
title: A graph with a parameter appended
type: definition
---
A parameterized graph problem is handed to the machine as one word: the
compressed sparse row block encoding the graph, followed by the single
entry *k*. This file defines that instance format and nothing else.

# Formalization notes

The instance word is the graph block with one entry appended. The
compressed sparse row block is self-delimiting — its own header
determines its length — so nothing needs to separate it from the
parameter, and the split of the word into the two parts is determined
by the word itself, not chosen. The parameter comes last so that the
graph block sits at the same offsets as in every other statement built
on this encoding.

The format is defined here, next to the encoding it extends, and the
statements made on it live elsewhere: the vertex cover ladder — the
2^*k* bounded search tree and the two statements that lower its
base — is the submission *Vertex Cover Below Two to the k*, which
imports this format rather than restating it, so that all of its bounds
are claims about literally the same inputs. The proof of its base rung
is in this submission's proof package, where the format's first
consumer was built.
-/

namespace Lax11.VertexCover

open Lax13.Ram Lax13.RamComputes Lax11.GraphEncoding

/-- The word `x` presents the graph `G` on `n` vertices together with
the parameter `k`: a compressed sparse row block encoding `G`, followed
by the single entry `k`. -/
def EncodesParamInstance (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ g, x = g ++ [k] ∧ EncodesGraph g n G

end Lax11.VertexCover
