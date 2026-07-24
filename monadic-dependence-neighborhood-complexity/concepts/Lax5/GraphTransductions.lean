import Lax5.GraphClasses
import Lax5.Transductions
import Mathlib.ModelTheory.Graph

/-!
---
title: Graph transductions
type: definition
---
A finite simple graph is a structure of the language of graphs, with the
single binary relation interpreted as adjacency. A graph class
transduces another if the corresponding classes of graph structures are
related by a first-order transduction.

# Formalization notes

Graphs enter as structures via mathlib's `SimpleGraph.structure`. The
target structures of a graph transduction are therefore honest graph
structures — symmetric and irreflexive — so the interpreting formula
must define the output adjacency exactly. This matches the common
convention of interpreting by an arbitrary formula `φ` and keeping the
pairs `u ≠ v` with `φ(u,v) ∧ φ(v,u)`: that symmetrized condition is
itself a formula, so both conventions define the same transduces
relation on graph classes.
-/

namespace Lax5.GraphTransductions

open FirstOrder Lax5.GraphClasses

/-- The members of a graph class, as structures of the language of
graphs: adjacency interprets the binary relation. -/
def structureClass (C : GraphClass) :
    Transductions.StructureClass Language.graph :=
  fun n S => ∃ G : SimpleGraph (Fin n), C n G ∧ S = G.structure

/-- `C` transduces `D` as graph classes: the corresponding classes of
graph structures are related by a first-order transduction. -/
def Transduces (C D : GraphClass) : Prop :=
  Transductions.Transduces (structureClass C) (structureClass D)

end Lax5.GraphTransductions
