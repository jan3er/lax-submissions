# Plan: extract the Ramsey material into its own submission

Rev 1, 2026-07-27. Design only — nothing is created, initialized or committed
by this document. Written for an implementation agent: the concept drafts
below are final and compile as given (see "Verification log"); an
implementation agent needs no further design decisions.

Goal: the Ramsey-theoretic material that currently sits inside the Lax5 proof
package (`Lax5Proofs/Ramsey.lean`, the Ramsey core of `Lax5Proofs/TupleRamsey.lean`)
becomes its own small, dependency-free submission **`finite-ramsey/`** (id
allocated by `lax init`; called **LaxR** below), whose statements the sparsity
submission (LaxS = `Lax12`, `sparsity-lectures/`) and Lax5 then *assume*
instead of reproving. Ramsey's theorem is the archetypal thing many
submissions want to cite; today it is buried twice over in a proof package
where nobody can cite it.

This supersedes the Ramsey handling of `sparsity-lectures-plan.md` — Design
sections (b) (the "two `Lax5Proofs` files are copied wholesale" line) and (c)
(the "Ramsey copy list"). The exact replacement text is in §5A; that plan's
own sections are **not** edited by this document.

---

## 1. Context: what exists today

| file | lines | public content | consumers |
| --- | --- | --- | --- |
| `Lax5Proofs/Ramsey.lean` | 239 | `compl_induce_eq`, `ramsey` (two-colour, graph form), `multicolor_ramsey` (list of sizes, `Sym2` colouring) | `NowhereDenseBridge.lean` (`multicolor_ramsey`), `Source/…/NDImpliesUQW/Full.lean` (`ramsey`) |
| `Lax5Proofs/BipartiteRamsey.lean` | 737 | `bipartite_ramsey` (notes Lemma 3.9), `iterated_bipartite_ramsey` (Lemma 3.10), 12 private colouring helpers, `R_star`, `iterStep` | `Source/…/NDImpliesUQW/Full.lean` only |
| `Lax5Proofs/TupleRamsey.lean` | 646 | `orderType`, `tuple_ramsey` (ℓ-tuple Ramsey up to order type), `glueLT`, `orderType_append_of_lt`, `bipartite_tuple_ramsey` (Mählmann Lemma 4.15) | `SubdividedBicliqueRamsey.lean` only |
| `Lax5Proofs/SubdividedBicliqueRamsey.lean` | 2451 | `subdividedBiclique_ramsey` | `Corollary6a.lean` |

Import-graph facts established by grep (they drive §5B):

- The only frontmattered Lax5 proof whose axiom closure touches any of this is
  `Corollary6a.lean` (it imports `NowhereDenseBridge` and
  `SubdividedBicliqueRamsey`). `AdlerAdler`, `NowhereDenseWcol`, `Corollary6b`,
  `Theorem2` do not.
- `BipartiteRamsey.lean`'s sole consumer is the vendored `NDImpliesUQW`, which
  leaves Lax5 with the sparsity extraction — so that file leaves Lax5 anyway.
- `TupleRamsey.lean`'s sole consumer is `SubdividedBicliqueRamsey.lean`.

**Mathlib check.** At the pinned revision `c5ea0035…` mathlib contains *no*
finite Ramsey theorem: `grep -ril ramsey Mathlib/` hits only
`Combinatorics/HalesJewett.lean` and `Combinatorics/Hindman.lean` (both merely
say "Ramsey theory" in prose) and an author name in `RingTheory/Coalgebra`.
There is no `SimpleGraph` Ramsey-number API, no `IsNClique`-or-`IsNIndepSet`
existence lemma, no hypergraph Ramsey. So every statement of this submission
is genuinely new archive content and every proof is a real proof, not a
one-line `exact` into mathlib. (Mathlib *does* supply the vocabulary the
statements use: `SimpleGraph.IsClique`, `SimpleGraph.IsIndepSet` — an `abbrev`
for `s.Pairwise fun v w => ¬G.Adj v w` — `Sym2`, `Set.ncard`.)

---

## 2. Decisions

### D1 — Scope: Ramsey only, not a "fundamentals" grab-bag

A submission is a citable unit and a concept is an endorsement unit; a
grab-bag called "fundamentals" would be a bag with no reviewable identity and
would grow forever, dragging every future addition through a re-draft that
moves the record triple and breaks every downstream pin. The archive's
convention is already content-named submissions (`twin-width-treewidth-separation`,
`ram-linear-time`, `sparsity-lectures`, and the planned `word-ram/` of
`word-ram-plan.md`, which likewise says "RAM fundamentals" in prose but names
the *directory* after its content). Other fundamentals get their own
content-named directories.

**Directory `finite-ramsey/`.** "Finite" is doing work: it fences off the
infinite/ultrafilter side of Ramsey theory, which is a genuinely different
development and would be its own submission. Proposed
`title: Finite Ramsey Theorems for Pairs and Tuples`.

### D2 — Concept surface: three theorem-concepts and one definition-concept

```
concepts/LaxR/Ramsey.lean             theorem     Ramsey's theorem (graph form, two colours)
concepts/LaxR/MulticolorRamsey.lean   theorem     k-colourings of pairs, monochromatic subset
concepts/LaxR/OrderTypes.lean         definition  order type of a tuple
concepts/LaxR/TupleRamsey.lean        theorem     ℓ-tuples, homogeneity up to order type
```

Why each earns its place:

- **`MulticolorRamsey`** is the workhorse. `NowhereDenseBridge` uses Ramsey
  with an arbitrary fintype of colours (`ramseyFor C Q`), and Lemma 3.9 uses
  it with `⌊(d−1) choose 2⌋ + 1` colours. Two-colour Ramsey does not serve
  them; the multicolour statement does.
- **`Ramsey`** (graph form: clique or independent set) is what people *cite*
  as "Ramsey's theorem", and it is what `NDImpliesUQW` consumes. It is the
  two-colour case of `MulticolorRamsey`, so it is discharged inside LaxR by a
  **glue proof** with `assumptions: [LaxR.MulticolorRamsey.exists_monochromatic_set]`
  — the Lax2 `Main.lean` pattern. That makes the derivation visible on the
  archive instead of pretending the two statements are unrelated, and it is
  honest about which one carries the induction.
- **`TupleRamsey`** (Erdős–Rado hypergraph Ramsey, in the order-type form used
  in model theory) is the second genuinely fundamental, graph-theory-agnostic,
  infinite-variant-free theorem in the Lax5 proof package. It is already
  stated over `Fin n` with plain colourings, it is 350 lines of real
  mathematics, and it is exactly the kind of statement a future
  monadic-stability/indiscernibles submission will assume. Including it is the
  difference between "we moved one theorem" and "the archive has a Ramsey
  entry".
- **`OrderTypes`** exists because `TupleRamsey` cannot be stated without the
  notion, and the notion will plausibly appear in a second statement
  (bipartite/two-sided versions, indiscernible sequences). "Definitions cannot
  move later, so place them now — when in doubt, hoist" applies; the
  alternative (inlining `fun i j => a i < a j` in the axiom) saves three lines
  now and costs a nominal duplication forever.

**Rejected for concept-hood** (deliberately, and each is defensible on its
own):

- *Bipartite Ramsey, notes Lemma 3.9* (`bipartite_ramsey`). Not a Ramsey
  theorem in the fundamental sense: its conclusion is a trichotomy about a
  bipartite graph whose middle branch is a `ShallowTopologicalMinorModel` of
  `K_t` — i.e. it mentions the very machinery `sparsity-lectures-plan.md`
  decision (1) deliberately keeps off the endorsement surface. It is sparsity
  lecture-notes material, it is graph-theoretic, and its statement would drag
  an eight-field `Sym2`-plumbing structure into a fundamentals submission.
  Stays proof-internal in LaxS, now proved *from* the LaxR multicolour
  statement.
- *Iterated bipartite Ramsey, Lemma 3.10* (`iterated_bipartite_ramsey`). Same,
  more so: a bespoke induction (`R_star`, `iterStep`) whose conclusion is
  tailored to the even-step reduction of the nd ⇒ UQW proof. Stays in LaxS.
- *`bipartite_tuple_ramsey`* (Mählmann Lemma 4.15). A short (≈ 80-line)
  corollary of `tuple_ramsey` obtained by concatenating tuples and splitting
  the homogeneous set in half. Derived, thesis-local, and consumed by exactly
  one Lax5 file. Stays in the Lax5 proof package, now derived from the
  assumed LaxR statement — which is the more meaningful network anyway.
- *The classical bipartite Ramsey theorem* (monochromatic `K_{t,t}` in a
  coloured `K_{N,N}`) is a genuine fundamental — but nothing in the repository
  proves it, so it is not in scope. A later revision of LaxR can add it as a
  fourth theorem-concept without moving anything.
- *A `ramseyNumber` parameter* (`sInf {N | …}`). The archive's `HasXAtMost` +
  `sInf` convention applies to *parameters that statements consume*; no
  statement here consumes a numeric Ramsey bound, so a `ramseyNumber` def
  would be review surface nothing uses. Same reasoning as
  `sparsity-lectures-plan.md` decision (3) on grad. Noted in the formalization
  notes.
- *A `Colouring` definition-concept.* A colouring is a function; `Sym2 (Fin n) → Fin k`
  and `(Fin ℓ → Fin n) → Fin k` say everything. No def.

### D3 — Statement forms

Every statement has the shape `∃ N : ℕ, ∀ n, N ≤ n → …` over canonical `Fin n`
carriers, with `Set` + `Set.ncard` for sizes (the Lax12 convention) and
`Set.Pairwise` for monochromaticity. Three uniform choices, argued once:

1. **`≥ N` rather than "on exactly `N` vertices".** Consumers apply Ramsey to
   whatever large carrier they have; the `N ≤ n` form is directly usable and
   is what all three local statements already say.
2. **"at least `s`" rather than "exactly `s`" for the monochromatic set.**
   Shrinking is free, and the `≤ ncard` form avoids a subset-extraction step
   in every consumer.
3. **No positivity hypothesis on the number of colours.** With `k = 0` there
   is no function into `Fin 0` from the (nonempty) set of pairs/tuples of a
   nonempty carrier, so `N := 1` discharges the statement vacuously. The local
   `multicolor_ramsey` and `tuple_ramsey` carry `sizes ≠ []` / `0 < k`
   hypotheses; dropping them removes a technical side condition from the
   endorsement surface at the cost of two lines in the bridge. (Verified: the
   bridge in §4 closes the `k = 0` case with `(c s(⟨0, hn⟩, ⟨0, hn⟩)).elim0`.)

Quantifier maps from the local statements are in §4.

### D4 — Lax5 is rewired too (not zero-churn)

Recommended: **Lax5-proofs takes a second git-pinned require on LaxR-concepts**,
deletes the proof of `Ramsey.lean` and the core of `TupleRamsey.lean`, and
`Corollary6a` grows an `assumptions:` block naming the two LaxR statements it
uses. Rationale:

- The extraction only pays off if somebody actually cites it. If Lax5 keeps
  local copies, the archive shows a Ramsey submission that nothing depends on,
  and the same theorem is proved twice in the database.
- The churn is small and *mechanical* because of the trick in §5B: the
  replacement `Lax5Proofs/Ramsey.lean` and the slimmed `Lax5Proofs/TupleRamsey.lean`
  keep their namespaces and lemma signatures, so `NowhereDenseBridge.lean`
  (1442 lines) and `SubdividedBicliqueRamsey.lean` (2451 lines) are **not
  edited at all**. Net: −840 lines in Lax5.
- The extra pin is the real cost. It is mitigated by the fact that LaxR has
  **no dependencies of its own** — nothing can force it to re-draft — and by
  freezing it (optionally registering it) before the dependents pin (§5C).
  Lax5 will already carry the Lax12 pin; the marginal maintenance is one more
  line in one lakefile.
- Archive value: `Lax5.WeaklySparseDependent.nowhereDense_of_weaklySparse_of_monadicallyDependent`
  visibly assuming Ramsey's theorem is exactly the network the archive exists
  to show.

### D5 — LaxR is strictly upstream of everything

LaxR imports nothing but mathlib. Dependency direction after the dust settles:

    LaxR-concepts ◀──requires── Lax12-proofs   (sparsity-lectures)
    LaxR-concepts ◀──requires── Lax5-proofs
    Lax12-concepts ◀─requires── Lax5-proofs

No cycles, no proof-package requires, three pins total in the archive.

---

## 3. Concept modules, in full

`concepts/LaxR.lean` has exactly four import lines, in this order:
`LaxR.OrderTypes`, `LaxR.MulticolorRamsey`, `LaxR.Ramsey`, `LaxR.TupleRamsey`.

### `concepts/LaxR/MulticolorRamsey.lean`

```lean
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Set.Card

/-!
---
title: Ramsey's theorem for colourings of pairs
type: theorem
---
For every number of colours *k* and every size *s* there is an *N* such
that for every colouring of the unordered pairs of an *N*-element set with
*k* colours there is a monochromatic subset of size *s*: a set of *s*
elements all of whose pairs receive one and the same colour. This is
Ramsey's theorem for pairs in its multicolour form; the number of colours
and the requested size are arbitrary and the bound *N* depends only on
them.

# Formalization notes

The colouring is a plain function on `Sym2 (Fin n)`, mathlib's type of
unordered pairs; no notion of colouring is introduced. Colourings assign a
colour to the degenerate pairs `s(u, u)` as well, and the conclusion
ignores them — `Set.Pairwise` constrains distinct elements only — so
colourings of the edges of the complete graph are exactly the functions
considered here, restricted along an inclusion that changes nothing.

Sizes are stated as "at least": a monochromatic set of size at least *s*
contains one of size exactly *s*, and the stated form is what every
application uses. All statements of this submission range over the
canonical carriers `Fin n` and over all `n` beyond the bound, so the
theorem applies to a set of any size by transport along a bijection.

The Ramsey number itself is deliberately not defined. The archive's
convention for a numeric parameter would be `sInf {N | …}`, but no
statement of this submission consumes a numeric bound, so such a
definition would be endorsement surface that nothing uses; the existential
carries the whole content.

No hypothesis is placed on the number of colours: for `k = 0` there is no
colouring of the pairs of a nonempty set at all, so the statement holds
vacuously with `N = 1`.
-/

namespace LaxR.MulticolorRamsey

/-- Ramsey's theorem for pairs: every `k`-colouring of the unordered pairs
of a large enough finite set has a monochromatic subset of size `s`. -/
axiom exists_monochromatic_set (k s : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (c : Sym2 (Fin n) → Fin k), N ≤ n →
      ∃ (i : Fin k) (S : Set (Fin n)), s ≤ S.ncard ∧
        S.Pairwise fun u v => c s(u, v) = i

end LaxR.MulticolorRamsey
```

### `concepts/LaxR/Ramsey.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card

/-!
---
title: Ramsey's theorem
type: theorem
---
For all *a* and *b* there is an *N* such that every graph on at least *N*
vertices contains a clique on *a* vertices or an independent set on *b*
vertices. Equivalently: colouring the edges of a large enough complete
graph with two colours always leaves a monochromatic clique.

# Formalization notes

A clique is a set of pairwise adjacent vertices and an independent set a
set of pairwise non-adjacent vertices, both in mathlib's `Set`-valued,
`Prop`-valued form (`IsIndepSet` is by definition pairwise
non-adjacency, so no complement graph and no decidability appear in the
statement). Sizes are counted with `Set.ncard` and stated as "at least",
as everywhere in this submission.

Graphs range over the canonical carriers `Fin n` for all `n` beyond the
bound, so the statement applies to a graph on any finite vertex set by
transport along a bijection.

This is the two-colour case of the multicolour concept of this
submission — colour a pair by whether it is an edge — and it is proved
that way, by a glue proof assuming that statement. It gets its own
statement because it is the form the literature cites and the form
graph-theoretic applications consume, and because a submission's headline
should not be reachable only through a strengthening.
-/

namespace LaxR.Ramsey

/-- Ramsey's theorem: a large enough graph contains a clique on `a`
vertices or an independent set on `b` vertices. -/
axiom exists_clique_or_indepSet (a b : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n →
      (∃ S : Set (Fin n), G.IsClique S ∧ a ≤ S.ncard) ∨
      (∃ S : Set (Fin n), G.IsIndepSet S ∧ b ≤ S.ncard)

end LaxR.Ramsey
```

### `concepts/LaxR/OrderTypes.lean`

```lean
import Mathlib.Order.Basic
import Mathlib.Data.Fin.Basic

/-!
---
title: Order type of a tuple
type: definition
---
Fix a linearly ordered set and a tuple *a* = (*a*₁, …, *a*_ℓ) of its
elements. The order type of *a* records which coordinates carry strictly
smaller entries than which: it is the relation that holds of *i* and *j*
when *a*ᵢ < *a*ⱼ. Two tuples have the same order type when they are
arranged in the same way — in particular they then agree on which
coordinates carry equal entries, since a linear order is total.

# Formalization notes

The order type is a `Prop`-valued relation on coordinates rather than a
three-valued code: in a linear order the strict-order pattern determines
the equality pattern (`a i = a j` exactly when neither `a i < a j` nor
`a j < a i`), so recording `<` alone loses nothing and keeps
decidability, `compare` and `Ordering` off the endorsement surface.

The definition is stated for an arbitrary linearly ordered vertex type,
not only for `Fin n`: it is a pointwise notion, and proofs that consume it
work over intermediate carriers. Statements of this submission still
instantiate it at the canonical carriers.
-/

namespace LaxR.OrderTypes

/-- The order type of a tuple: the relation holding of coordinates `i` and
`j` when the `i`-th entry is strictly smaller than the `j`-th. Two tuples
have the same order type when this relation is the same. -/
def orderType {V : Type*} [LinearOrder V] {ℓ : ℕ} (a : Fin ℓ → V) :
    Fin ℓ → Fin ℓ → Prop :=
  fun i j => a i < a j

end LaxR.OrderTypes
```

### `concepts/LaxR/TupleRamsey.lean`

```lean
import LaxR.OrderTypes
import Mathlib.Data.Set.Card

/-!
---
title: Ramsey's theorem for tuples
type: theorem
---
For every number of colours *k*, every arity ℓ and every size *s* there is
an *N* such that for every colouring of the ℓ-tuples over a linearly
ordered *N*-element set with *k* colours there is a subset *I* of size *s*
on which the colour of a tuple depends only on its order type: any two
tuples with entries in *I* that are arranged in the same way receive the
same colour. This is the finite Ramsey theorem for hypergraphs of
Erdős and Rado, in the order-type form used in model theory.

# Formalization notes

Tuples are arbitrary functions `Fin ℓ → Fin n`, so repeated entries and
every ordering of the entries are allowed. This is stronger than colouring
the ℓ-element *subsets* of the ground set — that classical form is the
special case where the colouring only depends on the increasing
enumeration — and it is the form that applications consume, since the
tuples they colour arise from arbitrary indexed families.

Homogeneity is stated as "tuples with entries in *I* and equal order types
receive equal colours", rather than as the existence of a function from
order types to colours through which the colouring factors. The two are
equivalent — such a function is obtained by choice — and the stated form
carries no choice and needs no default colour for the order types that no
tuple over *I* realizes.

The ground set is `Fin n` with its standard linear order, the canonical
carrier of this submission; sizes are `Set.ncard`, stated as "at least".
As in the other statements, no hypothesis is placed on the number of
colours: with `k = 0` there is no colouring at all.
-/

namespace LaxR.TupleRamsey

open LaxR.OrderTypes

/-- Ramsey's theorem for tuples: every `k`-colouring of the `ℓ`-tuples
over a large enough linearly ordered finite set has a subset of size `s`
on which the colour of a tuple depends only on its order type. -/
axiom exists_orderType_homogeneous (k ℓ s : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (c : (Fin ℓ → Fin n) → Fin k), N ≤ n →
      ∃ I : Set (Fin n), s ≤ I.ncard ∧
        ∀ a b : Fin ℓ → Fin n, (∀ i, a i ∈ I) → (∀ i, b i ∈ I) →
          orderType a = orderType b → c a = c b

end LaxR.TupleRamsey
```

---

## 4. Proof package: file map, quantifier maps, bridges

    proofs/LaxRProofs.lean                      -- five import lines
    proofs/LaxRProofs/PairRamsey.lean           -- ported, helpers only
    proofs/LaxRProofs/MulticolorRamsey.lean     -- proof of the multicolour statement
    proofs/LaxRProofs/Ramsey.lean               -- glue proof (assumptions:)
    proofs/LaxRProofs/TupleCore.lean            -- ported, helpers only
    proofs/LaxRProofs/TupleRamsey.lean          -- proof of the tuple statement

### 4.1 `PairRamsey.lean` — verbatim port

`Lax5Proofs/Ramsey.lean` (239 lines) moves in unchanged apart from
`namespace Lax5Proofs.Ramsey` → `namespace LaxRProofs.PairRamsey`. Imports are
mathlib-only already. All three declarations (`compl_induce_eq`, `ramsey`,
`multicolor_ramsey`) are needed: `multicolor_ramsey` inducts on the colour list
using `ramsey`, which uses `compl_induce_eq`. They carry no frontmatter — the
archive ignores helpers.

Local statement, verbatim (`Lax5Proofs/Ramsey.lean:147`):

```lean
theorem multicolor_ramsey (sizes : List ℕ) (hk : sizes ≠ []) :
    ∃ N : ℕ, ∀ {V : Type} [DecidableEq V] [Fintype V],
      N ≤ Fintype.card V →
      ∀ (c : Sym2 V → Fin sizes.length),
        ∃ (i : Fin sizes.length) (S : Finset V),
          sizes.get i ≤ S.card ∧
          (↑S : Set V).Pairwise (fun u v => c s(u, v) = i)
```

### 4.2 `MulticolorRamsey.lean` — proof of `LaxR.MulticolorRamsey.exists_monochromatic_set`

Quantifier map, local ⟶ concept:

| local | concept |
| --- | --- |
| `sizes : List ℕ` with `sizes ≠ []` | `k s : ℕ`, no hypothesis; instantiate `sizes := List.replicate k s` |
| `{V : Type} [DecidableEq V] [Fintype V]`, `N ≤ Fintype.card V` | `V := Fin n`, `Fintype.card (Fin n) = n`, `N ≤ n` |
| `c : Sym2 V → Fin sizes.length` | `c : Sym2 (Fin n) → Fin k`, precomposed with `Fin.cast (List.length_replicate).symm` |
| `i : Fin sizes.length` | `Fin.cast (List.length_replicate) i : Fin k` |
| `S : Finset V`, `sizes.get i ≤ S.card` | `(↑S : Set (Fin n))`, `s ≤ S.ncard` via `Set.ncard_coe_finset` and `List.get_replicate` |
| `k = 0` | no local instance; the colouring itself is absurd (`(c s(⟨0, hn⟩, ⟨0, hn⟩)).elim0`) |

Body (**compiled green**, see verification log; frontmatter to be added):

```lean
/--
---
conclusion: LaxR.MulticolorRamsey.exists_monochromatic_set
---
…
-/
theorem exists_monochromatic_set (k s : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (c : Sym2 (Fin n) → Fin k), N ≤ n →
      ∃ (i : Fin k) (S : Set (Fin n)), s ≤ S.ncard ∧
        S.Pairwise fun u v => c s(u, v) = i := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, fun n c hn => ?_⟩
    exact ((c s(⟨0, hn⟩, ⟨0, hn⟩)).elim0)
  · obtain ⟨N, hN⟩ := PairRamsey.multicolor_ramsey (List.replicate k s) (by
      simp [List.replicate_eq_nil_iff, hk.ne'])
    have hlen : (List.replicate k s).length = k := List.length_replicate
    refine ⟨N, fun n c hn => ?_⟩
    have hcard : N ≤ Fintype.card (Fin n) := by simpa using hn
    obtain ⟨i, S, hsize, hpair⟩ :=
      hN (V := Fin n) hcard (fun e => Fin.cast hlen.symm (c e))
    refine ⟨Fin.cast hlen i, (↑S : Set (Fin n)), ?_, ?_⟩
    · rw [Set.ncard_coe_finset]
      calc s = (List.replicate k s).get i := by simp
        _ ≤ S.card := hsize
    · intro u hu v hv huv
      have h := hpair hu hv huv
      simp only at h
      exact congrArg (Fin.cast hlen) h
```

### 4.3 `Ramsey.lean` — glue proof of `LaxR.Ramsey.exists_clique_or_indepSet`

Frontmatter:

```yaml
conclusion: LaxR.Ramsey.exists_clique_or_indepSet
assumptions:
  - LaxR.MulticolorRamsey.exists_monochromatic_set
```

The proof imports the two concept modules and nothing else — no ported source
at all. Body (**compiled green**):

```lean
theorem exists_clique_or_indepSet (a b : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n →
      (∃ S : Set (Fin n), G.IsClique S ∧ a ≤ S.ncard) ∨
      (∃ S : Set (Fin n), G.IsIndepSet S ∧ b ≤ S.ncard) := by
  classical
  obtain ⟨N, hN⟩ := exists_monochromatic_set 2 (max a b)
  refine ⟨N, fun n G hn => ?_⟩
  set c : Sym2 (Fin n) → Fin 2 :=
    Sym2.lift ⟨fun u v => if G.Adj u v then 0 else 1, by
      intro u v
      simp [SimpleGraph.adj_comm]⟩ with hc
  obtain ⟨i, S, hcard, hpair⟩ := hN n c hn
  have hcval : ∀ u v : Fin n, c s(u, v) = if G.Adj u v then 0 else 1 := by
    intro u v; rw [hc]; rfl
  fin_cases i
  · refine Or.inl ⟨S, ?_, le_trans (le_max_left a b) hcard⟩
    intro u hu v hv huv
    have := hpair hu hv huv
    simp only [hcval] at this
    by_cases h : G.Adj u v
    · exact h
    · simp [h] at this
  · refine Or.inr ⟨S, ?_, le_trans (le_max_right a b) hcard⟩
    intro u hu v hv huv
    have := hpair hu hv huv
    simp only [hcval] at this
    by_cases h : G.Adj u v
    · simp [h] at this
    · exact h
```

(`fin_cases` needs `import Mathlib.Tactic.FinCases`.)

### 4.4 `TupleCore.lean` — ported Ramsey core of `Lax5Proofs/TupleRamsey.lean`

Copy lines 15–22 and 85–439 of `Lax5Proofs/TupleRamsey.lean`, i.e.

- `orderType` (the `Ordering`-valued local one) — **rename to `otp`** to avoid
  clashing with the concept's `orderType`;
- `chainBound`, `buildChain`, `strictMonoRamseyFinset`;
- `Shape`, `Shape.arity`, `Shape.pattern`, `Shape.pattern_surjective`,
  `orderType_comp_strictMono`, `factorThroughShape`, `decomposeTuple`,
  `shapeRamseyFamily`, `tupleRamseyAtSize`.

Drop `private` from `tupleRamseyAtSize` (the frontmattered proof lives in
another module; helpers are ignored by the archive either way). **Do not**
copy `existsMonotoneUnbounded` (lines 33–84), `tuple_ramsey` (441), `glueLT`
(483), `orderType_append_of_lt` (501) or `bipartite_tuple_ramsey` (521): the
concept statement is `∃ N : ℕ`, not `∃ N : ℕ → ℕ`, so the monotone-unbounded
packaging is not needed here — it stays in Lax5 (§5B). Imports are
mathlib-only. Also fix the stale "**Proof strategy (not yet formalized).**"
line in the `tupleRamseyAtSize` docstring, which is a leftover — the lemma is
fully proved.

Local statement, verbatim (`Lax5Proofs/TupleRamsey.lean:410`):

```lean
private lemma tupleRamseyAtSize (k ℓ M : ℕ) (hk : 0 < k) :
    ∃ Nfin : ℕ, ∀ {n : ℕ} (S : Finset (Fin n)),
      Nfin ≤ S.card → ∀ c : (Fin ℓ → Fin n) → Fin k,
        ∃ I : Finset (Fin n), I ⊆ S ∧ M ≤ I.card ∧
          ∃ f : (Fin ℓ × Fin ℓ → Ordering) → Fin k,
            ∀ a : Fin ℓ → Fin n, (∀ i, a i ∈ I) → c a = f (orderType a)
```

### 4.5 `TupleRamsey.lean` — proof of `LaxR.TupleRamsey.exists_orderType_homogeneous`

Quantifier map:

| local | concept |
| --- | --- |
| `hk : 0 < k` | none; `k = 0` closed by `(c (fun _ => ⟨0, _⟩)).elim0` (`ℓ = 0`: apply `c` to `Fin.elim0`) |
| `M` (requested size) | `s` |
| `S : Finset (Fin n)`, `Nfin ≤ S.card` | `S := Finset.univ`, `Finset.card_univ`, `N ≤ n` |
| `I : Finset (Fin n)`, `I ⊆ S`, `M ≤ I.card` | `(↑I : Set (Fin n))`, `s ≤ I.ncard` (`Set.ncard_coe_finset`); the `I ⊆ S` clause is discarded |
| `∃ f, c a = f (otp a)` | `orderType a = orderType b → c a = c b`: rewrite both sides through `f` and use the bridge below |

One bridge lemma is needed, in the ⇐ direction only:

```lean
/-- Equal `Prop`-valued order types force equal `Ordering`-valued ones. -/
theorem otp_eq_of_orderType_eq {n ℓ : ℕ} {a b : Fin ℓ → Fin n}
    (h : LaxR.OrderTypes.orderType a = LaxR.OrderTypes.orderType b) :
    TupleCore.otp a = TupleCore.otp b
```

Proof sketch: `funext ⟨i, j⟩`; `otp a (i, j) = compare (a i) (a j)`; by
`lt_trichotomy` on `a i`, `a j` and the hypothesis (`a i < a j ↔ b i < b j`,
and symmetrically for `j i`, both read off `congrFun (congrFun h _) _` and
`propext`), the three cases match up via `compare_lt_iff_lt`,
`compare_eq_iff_eq`, `compare_gt_iff_gt`. Totality of the linear order turns
"neither `<` nor `>`" into `=` on both sides. ≈ 20 lines.

Then: `c a = f (otp a) = f (otp b) = c b`.

### 4.6 Abstract, manifest

`abstract.md`: what is proved (three statements), that the graph form is
discharged inside the submission by a glue proof from the multicolour form,
and that the submission is dependency-free and intended as an assumption
target. `manifest.yaml`: `title` per D1; `bibEntries` for Ramsey 1930 (*On a
problem of formal logic*), Erdős–Rado 1952 (*Combinatorial theorems on
classifications of subsets of a given set*) and the Mählmann thesis (already
present verbatim in Lax5's manifest — copy it) for the order-type form;
`authors` as `lax init` scaffolds (Jan decides, as in Lax12).

---

## 5. Rewiring

### 5A — Changes to `sparsity-lectures-plan.md`'s design (do not edit that file here)

Three passages of that plan are superseded. For whoever owns it:

1. **§"Concept surface" → "Proof-internal (no concepts)"**, the clause
   *"plus copies of whatever `Lax5Proofs.Ramsey` / `Lax5Proofs.BipartiteRamsey`
   material `NDImpliesUQW` consumes"* — replace with: the Ramsey inputs of
   `NDImpliesUQW` are **assumed** from LaxR (`finite-ramsey`), not copied;
   only the notes' own bipartite Ramsey lemmas (3.9, 3.10) are copied.

2. **Design (b), the line "Two `Lax5Proofs` files are copied wholesale into
   LaxS: `LaxSProofs/Ramsey.lean`, `LaxSProofs/BipartiteRamsey.lean`"** —
   replace with:

   - `Lax12Proofs/BipartiteRamsey.lean` — copied verbatim from
     `Lax5Proofs/BipartiteRamsey.lean` (737 lines) as planned, with the
     namespace rename and the `ShallowTopologicalMinor` import retarget to
     `Lax12Proofs.TopologicalMinors`. Unchanged from the current plan.
   - `Lax12Proofs/Ramsey.lean` — **not** a copy of the 239-line proof but a
     ~90-line bridge file that keeps the namespace `Lax12Proofs.Ramsey` and
     the two lemma signatures `ramsey` and `multicolor_ramsey` **verbatim**,
     re-deriving them from the LaxR axioms. Because the signatures are
     preserved, `BipartiteRamsey.lean` and the ported `NDImpliesUQW` need no
     edits beyond the imports they were already getting.

3. **Design (c) "Ramsey copy list"** — replaced in full by §5A.4 below.

4. **New Ramsey wiring for `sparsity-lectures`:**

   - `proofs/lakefile.toml` gains a second git-pinned require, on LaxR's
     concepts at its current record triple (`lax pull-db` first):

     ```toml
     [[require]]
     name = "LaxR"
     git = "https://github.com/lax-archive/lax-submissions"
     rev = "<LaxR draft commit>"
     subDir = "finite-ramsey/concepts"
     ```

   - `Lax12Proofs/Ramsey.lean` contains exactly two helper lemmas:

     * `multicolor_ramsey` — from `LaxR.MulticolorRamsey.exists_monochromatic_set`.
       **Compiled green** (verification log, `Back.lean`); ~35 lines: take the
       concept at `k := sizes.length`, `s := Finset.univ.sup (fun i => sizes.get i)`,
       transport along `e := Fintype.equivFin V` by colouring
       `fun p => c (Sym2.map e.symm p)`, push the monochromatic set back with
       `e.symm '' S` (`Set.ncard_image_of_injective`,
       `Set.ncard_eq_toFinset_card'`, `Set.coe_toFinset`). The `sizes ≠ []`
       argument is kept in the signature (and unused) so consumers are
       untouched.
     * `ramsey` — from `LaxR.Ramsey.exists_clique_or_indepSet`, same signature
       as today (`¬G.CliqueFree a ∨ ¬Gᶜ.CliqueFree b` over `{V : Type}` with
       instances). ~45 lines and the only bridge in this plan not pre-verified.
       Recipe: apply the concept to `G.comap (e.symm : Fin (Fintype.card V) → V)`
       (`SimpleGraph.comap` needs no injectivity and its complement agrees with
       the comap of the complement because `e.symm` is injective); a clique
       `S : Set (Fin n)` of `ncard ≥ a` maps to the `G`-clique `e.symm '' S`
       (`Set.ncard_image_of_injective`); shrink to exactly `a` elements with
       `Set.exists_subset_ncard_eq`, convert with `Set.toFinset` into
       `SimpleGraph.IsNClique` and conclude with
       `SimpleGraph.IsNClique.not_cliqueFree`; the independent-set branch goes
       through `SimpleGraph.isNClique_compl`.
     * `compl_induce_eq` is not needed and disappears from Lax12.

   - The frontmattered proof `Lax12Proofs/NowhereDenseUQW.lean`
     (concluding `Lax12.NowhereDenseUQW.uniformlyQuasiWide_of_nowhereDense`)
     gains

     ```yaml
     assumptions:
       - LaxR.Ramsey.exists_clique_or_indepSet
       - LaxR.MulticolorRamsey.exists_monochromatic_set
     ```

     (`NDImpliesUQW/Full.lean:339,349` uses `ramsey`; its
     `iterated_bipartite_ramsey` branch at 382/414 pulls in
     `multicolor_ramsey` through Lemma 3.9. Both therefore appear in the
     computed axiom set; `lax build` output confirms before committing.)

   - `abstract.md` of `sparsity-lectures` says that Ramsey's theorem is
     assumed from the `finite-ramsey` submission rather than reproved.

   - Net effect on LaxS: −239 lines of copied Ramsey, +90 of bridge, one extra
     pin, and the archive shows nd ⇒ UQW resting on Ramsey's theorem.

   - **Ordering constraint for that plan:** its P3 (`lax submit sparsity-lectures`)
     must come *after* LaxR is a submitted draft, and its P2 must build against
     the pushed LaxR commit. If the in-flight P2 has already copied
     `Ramsey.lean`, the change is local: delete the copy, add the bridge file,
     add the require, add the `assumptions:` block.

### 5B — Lax5 diff list

Assumes the sparsity extraction has already happened (`Source/` deleted,
`BipartiteRamsey.lean` deleted). If Ramsey is extracted first instead, the same
diffs apply and `BipartiteRamsey.lean` additionally needs
`import Lax5Proofs.Ramsey` to keep resolving — which it does, since the
replacement file keeps the module name.

- **`proofs/lakefile.toml`** — add the LaxR require (same block as §5A, `name = "LaxR"`).

- **`proofs/Lax5Proofs/Ramsey.lean`** — 239 lines → ~45. Keeps
  `namespace Lax5Proofs.Ramsey` and the exact signature of `multicolor_ramsey`,
  now proved from `LaxR.MulticolorRamsey.exists_monochromatic_set` (the
  compiled bridge of §5A.4). `ramsey` and `compl_induce_eq` are **dropped**:
  after the sparsity extraction, `NowhereDenseBridge.lean` is the only
  consumer left and it uses `multicolor_ramsey` alone
  (`NowhereDenseBridge.lean:428,436,440,464`). New import: `LaxR.MulticolorRamsey`.
  **`NowhereDenseBridge.lean` is not edited.**

- **`proofs/Lax5Proofs/TupleRamsey.lean`** — 646 lines → ~250. Delete lines
  85–439 (the Ramsey core listed in §4.4). Keep `orderType` (the local
  `Ordering`-valued one, used pervasively by `SubdividedBicliqueRamsey`),
  `existsMonotoneUnbounded`, `glueLT`, `orderType_append_of_lt`,
  `bipartite_tuple_ramsey`. Re-prove `tuple_ramsey` with its current signature
  from `LaxR.TupleRamsey.exists_orderType_homogeneous`:

  * for each `M`, obtain the concept's `N` and set `Nfin M := N`; the property
    `P n M` of the existing `existsMonotoneUnbounded` call is unchanged, so
    the monotone-unbounded packaging is reused verbatim;
  * inside `P`, rebuild the factoring function `f` from homogeneity by choice:
    `f ot := if h : ∃ a, (∀ i, a i ∈ I) ∧ otpProp a = ot' then c (choose h) else ⟨0, hk⟩`
    — or, simpler, define `f ot := if h : ∃ a, (∀ i, a i ∈ I) ∧ orderTypeC a = …`;
    the clean route is to keep `f` defined on `Ordering`-valued order types and
    use the ⇒ direction of the `otp`/`orderType` correspondence
    (`otp a = otp b → orderType a = orderType b`, immediate from
    `compare_lt_iff_lt`), plus `Classical.choice` for the order types no tuple
    realizes. `0 < k` is available in `tuple_ramsey`'s signature, so the
    default colour exists. ≈ 60 lines.

  **`SubdividedBicliqueRamsey.lean` is not edited.**

- **`proofs/Lax5Proofs/Corollary6a.lean`** — frontmatter only:

  ```yaml
  conclusion: Lax5.WeaklySparseDependent.nowhereDense_of_weaklySparse_of_monadicallyDependent
  assumptions:
    - LaxR.MulticolorRamsey.exists_monochromatic_set
    - LaxR.TupleRamsey.exists_orderType_homogeneous
  ```

  plus a sentence in `# Proof strategy`: the two Ramsey inputs (the
  monochromatic-subset extraction inside the nowhere-dense bridge and the
  order-type homogeneity behind Lemma 13.8) are assumed from the
  `finite-ramsey` submission. Verified by import graph: `Corollary6a` is the
  only frontmattered Lax5 proof whose closure reaches `NowhereDenseBridge` or
  `SubdividedBicliqueRamsey`.

- **`proofs/Lax5Proofs/Theorem2.lean`** — no change *provided*
  `sparsity-lectures-plan.md`'s rewiring of `Corollary6.lean` (compose the two
  statements instead of importing the two proofs) lands. If it does not,
  `Theorem2`'s computed axiom set additionally contains the two LaxR statements
  and its `assumptions:` block must list them. Check against `lax build`
  output.

- **`abstract.md`** — one clause in the proof-provenance paragraph: Ramsey's
  theorem and its tuple form are assumed from the `finite-ramsey` submission.

- Net: −840 lines, +2 bridge bodies, one extra pin, zero edits to the two
  largest Lax5 proof files.

### 5C — Submit order and pin choreography

1. **LaxR first.** `lax init finite-ramsey` (allocates the id; every `LaxR` in
   this document resolves then), write concepts + proofs, `lax build finite-ramsey --replay`,
   commit, push, `lax submit finite-ramsey` (draft), `lax pull-db`. LaxR has no
   requires beyond mathlib, so nothing gates it.
2. **Freeze LaxR.** Its record triple is now the pin target for two
   submissions. Any re-draft at a new commit invalidates both pins; since LaxR
   depends on nothing, nothing can force it to move. Registering it (at the
   *same* commit, so the triple is unchanged) once the dependents are green
   makes the freeze permanent — see open question Q5.
3. **`sparsity-lectures` (Lax12)** builds against the pushed LaxR commit during
   development, pins the record triple, `lax submit sparsity-lectures` (draft),
   `lax pull-db`.
4. **Lax5 re-draft** pins both LaxR and Lax12 at their current triples, builds,
   `lax build monadic-dependence-neighborhood-complexity --replay`, resubmit
   draft.
5. Lax1 and Lax2 are untouched throughout; nothing pins Lax5.

If Lax5 is rewired *before* the sparsity extraction lands (they are
independent), steps 3 and 4 swap and Lax5 temporarily keeps `BipartiteRamsey.lean`,
which continues to work against the replacement `Ramsey.lean`.

---

## 6. Phases

Same discipline as the sparsity plan: one agent per phase, review between
phases, Jan checkpoints before each `lax submit`.

- **P1 — scaffold + concepts.** `lax init finite-ramsey`; write the four
  concept modules of §3 verbatim (modulo the id rename), `LaxR.lean`,
  `abstract.md`, `manifest.yaml`; `lake build` green in `concepts/`; styleguide
  self-check (no `Classical`, no `Bool`, no proofs, docstring on every
  declaration, `title`/`type` + `# Formalization notes` in all four module
  annotations, exactly one axiom in each of the three theorem-concepts and zero
  in `OrderTypes`).
- **P2 — proof package.** Port `PairRamsey.lean` and `TupleCore.lean`; write
  the three frontmattered proofs (§4.2, §4.3, §4.5) and the `otp` bridge;
  `lax build finite-ramsey --replay` green; `lean_verify` on each frontmattered
  theorem to confirm the axiom sets (`Ramsey` must show exactly the multicolour
  statement plus background axioms; the other two, background only).
- **P3 — submit.** Commit (only `finite-ramsey/` and this plan; Jan's WIP stays
  unstaged), push, `lax submit finite-ramsey` (draft), `lax pull-db`. [Jan
  checkpoint]
- **P4 — hand-off.** The rewiring of §5A goes to whoever owns
  `sparsity-lectures-plan.md`; §5B goes to that plan's P4 (Lax5 reroute), which
  is the natural place since it is already rewriting Lax5's lakefile and
  frontmatter. Update README's submission list and memory.

---

## 7. Open questions for Jan

1. **Include the tuple/order-type Ramsey theorem, or ship pairs only?**
   Including it adds ~360 ported lines, one theorem-concept and one
   definition-concept, and is what makes the submission worth citing beyond
   the sparsity pipeline (it is the Erdős–Rado theorem in the model-theoretic
   form). *Recommendation: include.* Deferring costs nothing structurally —
   Lax5 would simply keep `TupleRamsey.lean` whole — but a v2 of LaxR means a
   re-draft and a repin round for its dependents, which is exactly what a
   frozen fundamentals submission should avoid.
2. **Name.** `finite-ramsey/`, title *Finite Ramsey Theorems for Pairs and
   Tuples*, versus `ramsey-fundamentals/`. *Recommendation: `finite-ramsey/`* —
   the archive names directories after content (`word-ram/`, `sparsity-lectures/`),
   and "fundamentals" is a role, not a subject; other fundamentals get their own
   content-named directories.
3. **Rewire Lax5 too, or leave it zero-churn?** Rewiring costs a second pin in
   `Lax5-proofs` and buys −840 lines and a visible Ramsey dependency for the
   weakly-sparse direction. *Recommendation: rewire* — the trick of preserving
   the local lemma signatures keeps `NowhereDenseBridge.lean` and
   `SubdividedBicliqueRamsey.lean` untouched, so the churn is two small files
   and one frontmatter block.
4. **Two statements for pairs (graph form + multicolour), or only the
   multicolour one?** The graph form is a 30-line glue proof away and would
   otherwise be re-derived inside every consumer. *Recommendation: keep both* —
   it is the citable form, and the glue proof makes the derivation visible
   (Lax2 precedent) rather than hiding it in a proof package.
5. **Register LaxR early?** Drafts can be replaced, and every replacement at a
   new commit breaks the Lax12 and Lax5 pins. *Recommendation: submit as a
   draft, then register at the same commit once both dependents build green* —
   the triple does not move, and from then on the pin can never break.

---

## 8. Risks and gotchas

- `lax init` allocates the real id; every `LaxR`/`LaxRProofs` above resolves
  then (the sparsity plan hit the same and it was mechanical).
- The one bridge in this plan that was **not** pre-compiled is the graph-form
  `ramsey` re-derivation for Lax12 (§5A.4). Recipe given; budget an hour.
  Fallback if it fights back: state the graph-form concept over `Fin n` *and*
  let Lax12 use the multicolour bridge directly, colouring pairs by adjacency
  inline — i.e. inline the §4.3 glue in Lax12 and transport once.
- `Lax5Proofs/TupleRamsey.lean`'s `tupleRamseyAtSize` carries a stale
  "**Proof strategy (not yet formalized)**" docstring; the lemma *is* proved
  (no `sorry` anywhere in the four files). Fix the docstring in the port.
- Do not `lake update`; toolchain and mathlib pins are archive-wide.
- Jan's unrelated WIP (`vc-contracts/`, `vc-night-brief.md`, `NIGHTLOG.md`)
  stays unstaged.
- Concurrent agents are working under `sparsity-lectures/`; this plan touches
  nothing there.

---

## 9. Verification log (P0)

Compiled with `lake env lean` against the pinned toolchain/mathlib from
`monadic-dependence-neighborhood-complexity/{concepts,proofs}`:

- All four concept modules of §3 (declarations and axioms, `autoImplicit = false`):
  **green**, no warnings.
- §4.3 glue proof of `exists_clique_or_indepSet` from the multicolour axiom:
  **green** (needs `Mathlib.Tactic.FinCases`).
- §4.2 proof of `exists_monochromatic_set` from the real
  `Lax5Proofs.Ramsey.multicolor_ramsey`: **green**.
- §5A.4 reverse bridge `multicolor_ramsey` (local signature, over `{V : Type}`
  with instances) from the multicolour axiom: **green** (only warning: the
  `sizes ≠ []` argument is unused — deliberately kept for signature
  compatibility).

Not yet compiled: the graph-form reverse bridge (§5A.4, second bullet), the
`otp`/`orderType` correspondence (§4.5), and the re-proof of `tuple_ramsey`
(§5B).

---

## 10. Implementation log (P1 + P2)

Executed 2026-07-27 by the implementation agent. Everything below is fact, not
design; it supersedes the `LaxR` placeholder of §§1–9.

### Allocated id

`lax init finite-ramsey` allocated **`Lax14`**. Resolutions:

| placeholder | actual |
| --- | --- |
| `LaxR` (package/namespace) | `Lax14` |
| `LaxRProofs` | `Lax14Proofs` |
| `concepts/LaxR/…` | `finite-ramsey/concepts/Lax14/…` |
| require `name = "LaxR"`, `subDir = "finite-ramsey/concepts"` | `name = "Lax14"`, same `subDir` |

### Concept axiom names for downstream packages

These are the permanent assumption targets. Downstream `assumptions:` blocks
and `open`/`import` lines use exactly these:

| module to import | statement (axiom) to assume |
| --- | --- |
| `Lax14.MulticolorRamsey` | `Lax14.MulticolorRamsey.exists_monochromatic_set` |
| `Lax14.Ramsey` | `Lax14.Ramsey.exists_clique_or_indepSet` |
| `Lax14.TupleRamsey` | `Lax14.TupleRamsey.exists_orderType_homogeneous` |
| `Lax14.OrderTypes` | *(definition-concept, no axiom)* — exports `Lax14.OrderTypes.orderType` |

Statement types are exactly as printed in §3 with `LaxR` → `Lax14`; no
signature moved during implementation.

Note for the bridge writers (`sparsity-lectures` P2, Lax5 P4): the concept
`orderType` is `Prop`-valued (`Fin ℓ → Fin ℓ → Prop`), while the local
`Lax5Proofs.TupleRamsey.orderType` is `Ordering`-valued
(`Fin ℓ × Fin ℓ → Ordering`). The correspondence lemma proved here is
`Lax14Proofs.TupleRamsey.otp_eq_of_orderType_eq` (⇐ direction: equal
`Prop`-valued order types force equal `Ordering`-valued ones), but it lives in
the **proof** package, which downstream packages cannot import — they pin
`finite-ramsey/concepts` only. The ⇒ direction they need for the
`tuple_ramsey` re-proof (§5B) is the easy one (`compare_lt_iff_lt`) and must
be re-derived locally; the ⇐ direction, if needed, is ~15 lines and can be
copied from `finite-ramsey/proofs/Lax14Proofs/TupleRamsey.lean`.

### Files as built

    finite-ramsey/manifest.yaml                     -- title per D1, 3 bibEntries, authors: []
    finite-ramsey/abstract.md
    finite-ramsey/concepts/Lax14.lean               -- 4 imports
    finite-ramsey/concepts/Lax14/OrderTypes.lean        definition, 0 axioms
    finite-ramsey/concepts/Lax14/MulticolorRamsey.lean   theorem, 1 axiom
    finite-ramsey/concepts/Lax14/Ramsey.lean             theorem, 1 axiom
    finite-ramsey/concepts/Lax14/TupleRamsey.lean        theorem, 1 axiom
    finite-ramsey/proofs/Lax14Proofs.lean            -- 5 imports
    finite-ramsey/proofs/Lax14Proofs/PairRamsey.lean       239 lines, ported, helpers
    finite-ramsey/proofs/Lax14Proofs/MulticolorRamsey.lean frontmattered proof
    finite-ramsey/proofs/Lax14Proofs/Ramsey.lean           frontmattered glue proof
    finite-ramsey/proofs/Lax14Proofs/TupleCore.lean        381 lines, ported, helpers
    finite-ramsey/proofs/Lax14Proofs/TupleRamsey.lean      frontmattered proof + otp bridge

### Build and axiom-set status

- `lake build` in `concepts/`: green (979 jobs), no warnings.
- `lake build` in `proofs/`: green (1093 jobs), no warnings.
- `lax build finite-ramsey --replay`: **OK, no violations.**
- `#print axioms` on the three frontmattered theorems:
  * `Lax14Proofs.MulticolorRamsey.exists_monochromatic_set` — `[propext, Classical.choice, Quot.sound]`
  * `Lax14Proofs.Ramsey.exists_clique_or_indepSet` — `[propext, Classical.choice, Quot.sound, Lax14.MulticolorRamsey.exists_monochromatic_set]` (exactly the declared assumption)
  * `Lax14Proofs.TupleRamsey.exists_orderType_homogeneous` — `[propext, Classical.choice, Quot.sound]`
- No `sorry` anywhere; nothing generated is tracked.

Not done here (by instruction): commit, push, `lax submit`, README submission
list, memory update. §5A/§5B rewiring untouched; no other submission directory
was modified.

### Deviations from the plan

**Concepts — none.** All four modules of §3 compiled verbatim (modulo the id
rename); statements, docstrings and formalization notes are as drafted.

**Proofs — the §4.2 and §4.3 bodies compiled verbatim** as promised by the
verification log. The remaining deviations are all in the ported helpers and
in the two items §9 listed as uncompiled:

1. **`TupleCore.lean` is not inside `section Helpers`.** §4.4 says to copy
   lines 15–22 and 85–439 of `Lax5Proofs/TupleRamsey.lean`, which straddles
   the `section Helpers` opened at line 24 and closed at 518. Since
   `existsMonotoneUnbounded` (33–84) is deliberately not copied, the section
   wrapper was dropped with it. No effect: the section carried no `variable`s
   and `private` is file-scoped anyway.

2. **`orderType_comp_strictMono` was also renamed to `otp_comp_strictMono`.**
   §4.4 only prescribes renaming the `Ordering`-valued `orderType` def to
   `otp`; leaving the lemma name unrenamed would have left a helper named
   after a notion the file no longer mentions. Statement unchanged.

3. **`tupleRamseyAtSize` docstring edits beyond the prescribed one.** The
   stale "**Proof strategy (not yet formalized).**" was fixed to "**Proof
   strategy.**" as §8 requires; additionally the sentence "define
   `f : orderType → Fin k`" became "define `f` on order types", which the
   mechanical `orderType` → `otp` rename would otherwise have turned into the
   nonsensical "`f : otp → Fin k`". `TupleCore.lean` also got a new module
   docstring (it is a new file; the source's module docstring described a
   different file).

4. **`otp_eq_of_orderType_eq` is stated more generally than §4.5 sketches.**
   The plan's signature is `{n ℓ : ℕ} {a b : Fin ℓ → Fin n}`; the implemented
   one is `{V : Type*} [LinearOrder V] {ℓ : ℕ} {a b : Fin ℓ → V}`, matching
   the generality of `otp` and of the concept's `orderType`. It costs nothing
   and makes the lemma reusable by the downstream bridges. The proof is the
   sketched one (`funext` on the coordinate pair, `lt_trichotomy`, the two
   `Prop` equalities read off by `congrFun`/`iff_of_eq`, then
   `compare_lt_iff_lt` / `compare_eq_iff_eq` / `compare_gt_iff_gt`), 15 lines
   rather than the budgeted 20.

5. **`k = 0` in the tuple proof.** §4.5's quantifier map says to close it with
   `(c (fun _ => ⟨0, _⟩)).elim0` and notes `ℓ = 0` needs `Fin.elim0`. It does
   not: `fun _ => ⟨0, hn⟩` is a well-typed `Fin ℓ → Fin n` for every `ℓ`
   including `0`, so one line covers both cases. `N := 1` as planned.

6. **`bibEntries`.** §4.6 prescribes Ramsey 1930, Erdős–Rado 1952 and the
   Mählmann thesis. The Mählmann entry is copied verbatim from Lax5's
   manifest; the other two were written here (`Ramsey1930`, `ErdosRado1952`,
   both with DOIs). `authors: []` as `lax init` scaffolds, per §4.6.

7. **Not a deviation, recorded for §5B.** The submission-side name of the
   ported two-colour graph statement is `Lax14Proofs.PairRamsey.ramsey` and of
   the list-indexed one `Lax14Proofs.PairRamsey.multicolor_ramsey` — both
   private to this proof package. Downstream must go through the concept
   axioms, never these.
