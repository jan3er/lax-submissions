# Courcelle plan (rev 1 — decisions taken under Jan's delegation 2026-07-27)

Status (2026-07-27, night): written by the Fable orchestrator under
Jan's explicit "no approval needed" delegation; the C-decisions below
are therefore *settled* the way D9–D12 were, revisable only the way
D16 was — by contact with the material, argued in a rev bump. The
Opus relay executes against this plan; `courcelle-night-brief.md` maps
it to overnight milestones.

Goal: **Courcelle's theorem on the Lax11 RAM** — for every MSO
sentence and every width bound, model checking on graphs given with a
tree decomposition of that width is linear time. This is the endgame
the RAM stack was built for; Lax11 (complete, submit-ready) supplies
the machine, the compiler, the reasoning kit, and the CC driver's
proof patterns.

Honest scale estimate up front: this is 5–10× Lax11. Unlike Lax11,
one component (the composition lemma, step Q1) carries genuine
research-*engineering* risk — not "is it true" but "how much quotient
and normal-form pain". The plan is shaped so that component is built
and measured first at small rank before anything depends on it.

## The statement (C0 target)

```lean
/-- Courcelle's theorem: MSO model checking is linear-time on the RAM,
for graphs presented with a tree decomposition of bounded width. -/
axiom courcelle :
    ∀ (φ : MSO) (hφ : φ.Closed) (k : ℕ),
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ComputesInTime p {x | EncodesInstance x n G k}
        (fun _ => if Sat G φ then [1] else [0])
        (fun x => c * (x.length + 1))
```

- Quantifier order is the theorem: `p` and `c` come after `φ` and `k`,
  before the graph — **non-uniform in the sentence and the width**,
  which is the textbook Courcelle (the constant is allowed to be a
  tower in `|φ|` and `k`; we never estimate it).
- `EncodesInstance x n G k`: `x` encodes `G` (CSR, Lax11's
  `EncodesGraph` reused) **followed by a rooted tree decomposition of
  `G` of width ≤ k** (C6). The decomposition is *input*: Bodlaender's
  linear-time algorithm is a separate future submission, and the
  formalization notes must say so plainly — the theorem as stated is
  the standard "given a decomposition" form, and it is what every
  textbook proves first.
- Output `[1]`/`[0]` on the output tape (C9).

## Decision record

- **C1 (scope)** MSO₁ — adjacency signature, quantification over
  vertices and vertex *sets*. MSO₂ (edge-set quantification /
  incidence encoding) is a later concept with its own submission;
  everything below is built so the change is confined to the atomic
  layer of the type algebra. Rationale: halves the surface and the
  atomic case work, and MSO₁ on the incidence graph *is* MSO₂ when we
  want it.
- **C2 (logic representation)** Deep embedding, **de Bruijn indices,
  environment semantics**. Two sorts of variables (vertex, set), one
  `inductive MSO`: atoms `adj i j`, `eq i j`, `mem i X`; connectives
  `not`, `and`; quantifiers `exV`, `exS`; nothing else (∨, →, ∀ are
  abbreviations in proofs, not constructors — smaller trusted
  recursion). `Sat` is a ~15-line recursion over two environment
  functions `Fin r → Fin n` and `Fin s → Set (Fin n)` — **no
  substitution machinery anywhere**, which is the entire point: the
  semantics is the new trust object (the analogue of `Instr.effect`)
  and must be auditable in one sitting. `rank φ` counts both
  quantifier kinds. Honesty note: de Bruijn is the one non-textbook
  device on the surface; the ledger argues it (named syntax needs
  capture-avoiding substitution *in the trusted surface*, which is a
  far worse audit object than indices).
- **C3 (proof route)** **No tree automata, no Hintikka/normal-form
  syntax.** The engine is the *abstract type algebra*: define, by
  recursion on rank, the finite set of q-types of boundaried
  structures and the type function —

  ```
  T 0 r s       := atomic diagrams on r marked vertices, s sets   (finite)
  T (q+1) r s   := T 0 r s × Set (T q (r+1) s) × Set (T q r (s+1))
  typ (q+1) A   := (typ 0 A, {typ q (A, +v) | v}, {typ q (A, +S) | S})
  ```

  with `Fintype` by induction. Three theorems make it an engine:
  1. *Adequacy*: a rank-≤q formula's truth depends only on
     `typ q` (induction on the formula).
  2. *Forget*: the type of a reduct (dropping a mark) is a function
     of the type of the expansion (induction on q).
  3. *Composition* (the make-or-break): for structures `X`, `Y`
     overlapping exactly in a shared set of marked vertices, with no
     edges between `X∖Y` and `Y∖X`,
     `typ q (X ∪ Y) = F q (typ q X) (typ q Y) (overlap pattern)`,
     with `F` defined by the same recursion (a vertex/set move in the
     union splits into a move in `X` and a move in `Y`; for sets,
     `S ↦ (S ∩ X, S ∩ Y)`).
  Rationale: this is game-free (no strategy plumbing), syntax-free
  (finiteness needs no formula normal forms), and it is the same
  proof culture as Lax5's `LocalTypes`/`EFAgreement` — that code is
  FO and not literally reusable, but the team has built exactly this
  shape before. Automata would add a translation layer and buy
  nothing; Hintikka formulas would put syntax back into the induction.
- **C4 (decomposition math)** Bags `Fin N → Finset (Fin n)`, rooted
  by a parent function. Children are folded **sequentially**: the
  accumulated structure at node `t` after `j` children is
  glue-of-bag-and-first-`j`-subtrees, and each step is one binary
  composition (C3.3) followed by forgets (C3.2) of the child's
  non-shared bag vertices. No "nice decompositions", no
  introduce/forget/join normalization — the sequential fold does the
  same job with zero preprocessing to verify. The decomposition facts
  needed: edge coverage, coherence (connectivity of occurrence sets),
  and the separation lemma (no edges between a subtree's interior and
  its exterior; subtree interiors of siblings are disjoint). Mathlib
  status per first survey: nothing usable — we define tree
  decompositions on the surface (they are part of the *statement*).
- **C5 (the table is allowed to be noncomputable)** The theorem is
  `∃ p : Program`. The transition table — composition `F` and the
  accepting set of root types, restricted to the finitely many types
  realizable at width k — is finite *data*, and Lean may produce it
  by classical choice; the *program* is generated from that data
  (types numbered by an enumeration of the Fintype, table
  materialized into an array by a generated prologue of stores, then
  lookups are arithmetic indexing). Nothing requires deciding MSO
  truth by computation at the meta level. This kills the single most
  expensive part of every executable-flavored Courcelle: we never
  prove the table *computable*, only that it *exists and is correct*.
- **C6 (instance encoding)** After the CSR graph block: `N`, then for
  each decomposition node its parent index, then bag sizes/offsets,
  then bag contents (CSR-style two-array layout, reusing the offset
  pattern). Validity predicate `EncodesInstance` includes
  **children-before-parent numbering** (`parent i > i`, root `N−1`).
  Honesty: a rooted decomposition always admits such a numbering, so
  the hypothesis costs no generality — argued in the ledger next to
  the CSR dumbness argument. (Computing the order in-program via the
  CC BFS pattern is a possible later hardening, noted, not planned.)
- **C7 (phase-2 program shape)** One pass over nodes `0..N−1`
  (children first by C6). Per node: compute its bag's atomic data and
  overlap patterns with already-folded children by scanning the bag
  arrays (`O(k²)` per comparison, `k` fixed — constants may depend on
  k per C1's non-uniformity), then repeated table lookups. Cost by
  the CC-style global potential ("nodes left + bag-slots left +
  child-slots left"). This is the **P4 tree-fold schema**,
  generic over any table — built and verified *before* the type
  algebra exists, against an abstract table, in Lax11's proof package.
- **C8 (staging and homes)** Three work packages, two eventual
  submissions:
  - **Q3 = P4 tree-fold schema**: lives in `Lax11Proofs` as helper
    files now (mirrors D8: split infrastructure when the second
    consumer exists).
  - **Q1 = type algebra** and **Q2 = decomposition math**: pure
    mathematics, no RAM anywhere. Developed now in the Lax11 proofs
    package under a `Lax11Proofs.MsoTypes` / `.TreeDecomp` namespace
    (it has mathlib and a warm build), migrated verbatim when Jan
    provisions the ids.
  - Submission A (needs `lax init`, Jan): MSO + tree decompositions +
    the `courcelle` axiom — the concept surface above.
  - Submission B (optional split, later): the type-algebra
    infrastructure as its own endorsement surface, if the
    composition lemma turns out to deserve independent citation.
- **C9** Output `[1]`/`[0]`, decided by membership of the root type
  in the accepting set.
- **C10 (cross-submission reuse, open tooling question for Jan)**
  Submission A's concepts should *import* Lax11's (`Program`,
  `ComputesInTime`, `EncodesGraph`) rather than restate them. Whether
  lax supports concept-package dependencies is the one provisioning
  question Jan must answer; if not, we restate verbatim with a
  ledger note. **This is the only decision genuinely blocked on Jan.**

## Steps

1. **Q3 — the tree-fold schema** (overnight, running): encoding of a
   parent-pointer tree with per-node data, generic table-driven
   bottom-up fold as an IMP+ program, `#eval`-checked, then the `Run`
   lemma with a linear bound. Checkpoint: the schema's statement is
   clean enough that "instantiate table := type table" is plausibly a
   plug-in, and per-node cost is visibly `O(k)`-shaped.
2. **Q1a — type algebra, small rank** (the make-or-break, measured
   early): `T`/`typ`/`Fintype`, adequacy, forget, and the
   composition lemma **at q ≤ 1 fully worked**, on boundaried graph
   structures. Checkpoint: lines-per-obligation at q ≤ 1 decides
   whether the general induction is a grind or a redesign; report in
   the style of the step-3/step-5 checkpoints of the RAM plan.
3. **Q1b — general composition** by induction on q, plus the
   realizable-at-width-k finite restriction of the table.
4. **Q2 — decomposition math**: separation lemma, the abstract
   bottom-up fold as a pure Lean recursion, its correctness
   (root type determines `Sat G φ` via adequacy).
5. **C0 freeze**: write the surface (MSO, TreeDecomposition,
   EncodesInstance, the axiom), smoke tests in proofs (Sat on
   two-vertex graphs, a hand-checked width-1 decomposition of a
   path). Requires Jan's `lax init` and the C10 answer; everything
   before this point is deliberately surface-independent.
6. **Driver**: instantiate Q3's schema with Q1's table, the per-node
   bag/overlap scanning program, assemble phases CC-style, discharge
   the axiom, audit.
7. **Wrap-up**: notes/honesty ledger (C1 MSO₁, C2 de Bruijn, C5
   noncomputable table, C6 ordering hypothesis, Bodlaender out of
   scope), abstracts, split per C8.

Order rationale: Q3 first because it is riskless and warm (CC
patterns fresh); Q1a immediately after because it is the *only*
component that could force a redesign and must be measured before
Q2/Q6 build on it; the surface freezes *last among the math* (step 5)
because — unlike Lax11, where the machine was the trust object and
could freeze first — here the trust object (MSO semantics) is also
the induction target of Q1, and freezing it before the q ≤ 1
checkpoint would repeat the D3 mistake (frozen convention, compiler
later proves it unworkable) at 10× the cost.

## Feasibility judgment

Q3: no risk, CC-shaped. Q2: standard graph theory, volume ≈ CCGraph.
Q1 adequacy/forget: textbook inductions. **Q1 composition: the one
hard object** — the induction is standard on paper (Feferman–Vaught
for gluing over a shared boundary), but the Lean cost of "structure =
graph + marks + set assignment, glued along an overlap pattern" is
unmeasured; that is exactly what step 2's checkpoint measures at
q ≤ 1 before anything is committed to it. Driver: bigger than CC's
but pattern-identical. Prior art to survey when convenient (not
blocking): no complete mechanization of Courcelle is known to this
plan; Traytel's MSO-on-words work (Isabelle) is the nearest relative
and took the automaton route we rejected — cite both facts in the
notes when confirmed.
