import Lax11.RamComputes
import Lax11.Mso
import Lax11.InstanceEncoding

/-!
---
title: Courcelle's theorem on a random access machine
type: theorem
---
Every property of graphs expressible in monadic second-order logic can
be decided in linear time on graphs of bounded cliquewidth, given a
*k*-expression for the graph. Fix a sentence and a width bound *k*;
then there is one random access machine program and one constant *c*
such that, given any graph in compressed sparse row form followed by a
*k*-expression that evaluates to it, the program halts within
*c*(|x|+1) steps and writes `1` if the sentence holds in the graph and
`0` if it does not.

This is the Courcelle–Makowsky–Rotics form of Courcelle's theorem: the
width measure is cliquewidth and the logic is monadic second-order
logic with quantification over vertices and vertex sets, which is the
pairing the two notions are matched to.

# Formalization notes

The expression is *input*, not something the program computes. Deciding
cliquewidth, or approximating it, is a different theorem with a
different proof, and folding it in here would silently claim it; the
statement is the honest one, "given a graph together with a
*k*-expression for it". This is the same choice a treewidth-based
statement makes when it takes a tree decomposition as input.

The order of the quantifiers is the content of the theorem: the
sentence and the width bound come first, then the program and the
constant, then the graph. So one program serves all graphs of
cliquewidth at most *k*, with one constant, but both may depend — and
in every known proof do depend, in a way that grows faster than any
tower of exponentials in the sentence — on the sentence and the width.
Nothing here estimates the constant.

Only encodings of `G` are admitted as inputs; the program may behave
arbitrarily on words that encode nothing.
-/

namespace Lax11.Courcelle

open Lax11.Ram Lax11.RamComputes Lax11.Mso Lax11.InstanceEncoding

open Classical in
/-- **Courcelle's theorem** (Courcelle–Makowsky–Rotics form): model
checking monadic second-order logic is linear time on a random access
machine, for graphs presented together with a `k`-expression. For every
sentence and every width bound there are one program and one constant
such that, on every graph given in compressed sparse row form followed
by a `k`-expression for it, the program halts within a constant
multiple of the length of the input, having written `1` if the sentence
holds in the graph and `0` otherwise. -/
axiom exists_linearTime_program_modelChecking :
    ∀ (φ : MSO 0 0) (k : ℕ),
      ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        ComputesInTime p {x | EncodesModelCheckingInstance x n G k}
          (fun _ => if Sat G Fin.elim0 Fin.elim0 φ then [1] else [0])
          (fun x => c * (x.length + 1))

end Lax11.Courcelle
