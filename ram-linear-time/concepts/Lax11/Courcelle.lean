import Lax13.RamComputes
import Lax11.Mso
import Lax11.InstanceEncoding

/-!
---
title: Courcelle's theorem on a word RAM
type: theorem
---
Every property of graphs expressible in monadic second-order logic can
be decided in linear time on graphs of bounded cliquewidth, given a
*k*-expression for the graph. Fix a sentence and a width bound *k*; then
there are one word RAM program and one constant *c* such that, at every
word length, given any graph in compressed sparse row form followed by a
*k*-expression that evaluates to it, as a word *x* each of whose entries
*v* satisfies *c*(|x|+*v*+1) ≤ `2 ^ w`, the program halts within
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
constant, then the graph and the word length. So one program serves all
graphs of cliquewidth at most *k* at every word length, with one
constant, but both may depend — and in every known proof do depend, in a
way that grows faster than any tower of exponentials in the sentence —
on the sentence and the width. Nothing here estimates the constant. This
is the opposite ordering from the vertex cover statement of this
submission, and it has to be: there the parameter is an entry of the
input word, so one program can read it and serve every parameter, while
here the sentence is not part of the input at all and a program that has
never seen it cannot decide it. Quantifying the program before the word
length says the same thing about `w` as everywhere else in this
submission — one program that works at every word length that admits its
input, rather than a family of programs, one of which could hide an
arbitrary amount of information in its literals.

One constant does both jobs, and the condition it appears in says two
things at once. The first is that the running time fits: taking *v* to
be any entry of the word — an instance word is never empty — the
condition gives *c*(|x|+1) ≤ `2 ^ w`, so `2 ^ w` is at least the number
of steps the claim allows, and with it every quantity the program forms
out of the length of the word, the number of nodes of the expression and
the addresses of the arrays included. The four tables of the dynamic
program are also covered, since their sizes depend on the sentence and
the width bound alone and are therefore absorbed into *c*, which is
chosen after both.

The second is that the entries themselves fit, and this is why the
condition quantifies over them. A machine at word length `w` sees its
input reduced modulo `2 ^ w`, so an entry that is not a word is not the
entry it was handed. Most entries of an instance are small: vertex
numbers, offsets and node numbers are below the length of the word, and
an operation code is below the number of operations at width *k*, which
`c` covers. But not all of them are, because the format has slots the
encoding deliberately leaves free — the parent entry of the root,
through which nothing points, and the vertex name at a node whose
operation creates no vertex. Those may hold any number whatever, and
saying of every entry that it fits is what makes the claim about them
honest instead of silently assuming they are small. It is the same
bookkeeping the vertex cover statement of this submission does with
`c * (|x| + k + 1)`, where the one entry not bounded by the length is
the parameter.

The fitting condition is a condition on the admissible inputs and not a
hypothesis of the claim, because as a hypothesis it would be empty. A
graph with an edge has encodings of every length, since a block may list
a neighbour repeatedly, so no word length accommodates all encodings of
a fixed graph at once and "if every instance for `G` and `k` fits into a
word" would never be satisfied. Restricting the inputs instead says what
is meant: at every word length, every instance that fits is decided
within the bound.

Only encodings of `G` are admitted as inputs; the program may behave
arbitrarily on words that encode nothing, and on words too long for its
word length.
-/

namespace Lax11.Courcelle

open Lax13.Ram Lax13.RamComputes Lax11.Mso Lax11.InstanceEncoding

open Classical in
/-- **Courcelle's theorem** (Courcelle–Makowsky–Rotics form): model
checking monadic second-order logic is linear time on a word random
access machine, for graphs presented together with a `k`-expression. For
every sentence and every width bound there are one program and one
constant such that, at every word length `w`, on every graph given in
compressed sparse row form followed by a `k`-expression for it as a word
`x` each of whose entries `v` satisfies `c * (x.length + v + 1) ≤ 2 ^ w`,
the program halts within a constant multiple of the length of the input,
having written `1` if the sentence holds in the graph and `0`
otherwise. -/
axiom exists_linearTime_program_modelChecking :
    ∀ (φ : MSO 0 0) (k : ℕ),
      ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ),
        ComputesInTime w p
          {x | EncodesModelCheckingInstance x n G k ∧
            ∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w}
          (fun _ => if Sat G Fin.elim0 Fin.elim0 φ then [1] else [0])
          (fun x => c * (x.length + 1))

end Lax11.Courcelle
