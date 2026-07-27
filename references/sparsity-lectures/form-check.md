# Form check: `sparsity-lectures` concepts vs. the Warsaw "Sparsity" lecture notes

Checked 2026-07-27 against the actual course notes, both editions. Every
verbatim quote below is a transcription from the downloaded PDFs (text
extracted with `pdftotext -layout`; math re-typeset in LaTeX-ish ASCII).

## Source documents

**Primary (the one the vendored code cites).**

> Marcin Pilipczuk, Michał Pilipczuk. *Sparsity* — lecture notes for the
> course "Sparsity", winter term 2019/20, Faculty of Mathematics,
> Informatics and Mechanics, University of Warsaw.
> Course page: <https://www.mimuw.edu.pl/~mp248287/sparsity2/>
> Chapters (individual PDFs), with the compilation date printed on the
> title page of each:
> - Chapter 1, *Measuring sparsity*, 28 pp., compiled January 24, 2020 —
>   `https://www.mimuw.edu.pl/~mp248287/sparsity2/lectures/chapter1.pdf`
> - Chapter 2, *Structural measures*, 22 pp., compiled November 22, 2019 —
>   `.../chapter2.pdf`
> - Chapter 3, *Model-checking FO* — `.../chapter3.pdf`
> - Chapter 4, *Uniform quasi-wideness*, 14 pp., compiled December 12, 2019 —
>   `.../chapter4.pdf`
> - Chapter 5, *Beyond Sparsity* — `.../chapter5.pdf`
> - Chapter 6, *Polynomial expansion* — `.../chapter6.pdf`

The 2019/20 edition is the one whose numbering matches the vendored code:
its Chapter 2 contains **Lemma 2.5**, **Lemma 2.6**, **Corollary 2.7**
exactly as cited. Instructors on the 2019/20 page are *Marcin Pilipczuk
and Michał Pilipczuk*; the notes carry no author line inside the PDFs.

**Secondary (previous edition).**

> Michał Pilipczuk, Sebastian Siebertz. *Sparsity* — lecture notes,
> winter term 2017/18, University of Warsaw.
> <https://www.mimuw.edu.pl/~mp248287/sparsity>, chapters at
> `.../lectures/lecture{1..6}.pdf`.

The 2017/18 edition is textually the ancestor: same wording, same proofs,
but statements are numbered **sequentially per chapter** (Lemma 2, Lemma
3, Corollary 4, Lemma 7, Lemma 8, …) rather than by section, and it
writes `col_r` where 2019/20 writes `scol_r`. Where an item below differs
between editions this is stated explicitly; where it does not, the two
editions agree verbatim modulo the numbering and the `col`/`scol` rename.

There is **no compiled single-file or arXiv version** of these notes;
web search turns up only the two course pages. Suggested manifest
`bibEntry` (2019/20, the edition with the matching numbering):

```
@misc{pilipczuk-sparsity-notes,
  author = {Marcin Pilipczuk and Micha{\l} Pilipczuk},
  title  = {Sparsity --- lecture notes for the course ``Sparsity'', winter term 2019/20},
  year   = {2020},
  note   = {University of Warsaw, Faculty of Mathematics, Informatics and Mechanics.
            Chapter~1 compiled 2020-01-24; Chapter~2 compiled 2019-11-22;
            Chapter~4 compiled 2019-12-12},
  url    = {https://www.mimuw.edu.pl/~mp248287/sparsity2/}
}
```

Local copies: `ed2019/chapter{1..6}.pdf` + `.txt`, `ed2017/lecture{1..6}.pdf` + `.txt`.

---

## Item 1 — Depth-*r* minor / shallow minor

**Notes, 2019/20 Chapter 1, Definitions 1.10, 2.2, 2.3:**

> **Definition 1.10.** A graph *H* is a *minor* of *G*, written *H* ⪯ *G*,
> if there is a *minor model* φ of *H* in *G*: a map φ which assigns to
> every vertex *v* ∈ V(*H*) a connected subgraph φ(*v*) ⊆ *G* of *G* and
> to every edge *e* ∈ E(*H*) an edge φ(*e*) ∈ E(*G*) such that
> 1. if *u*, *v* ∈ V(*H*) with *u* ≠ *v* then V(φ(*v*)) ∩ V(φ(*u*)) = ∅ and
> 2. if *e* = *uv* ∈ E(*H*) then φ(*e*) = *u'v'* ∈ E(*G*) for vertices
>    *u'* ∈ V(φ(*u*)) and *v'* ∈ V(φ(*v*)).
>
> The set φ(*v*) for a vertex *v* ∈ V(*H*) is called the *branch set* of *v*.

> **Definition 2.2.** The *radius* of a connected graph *G* is
> rad(*G*) = min_{u∈V(G)} max_{v∈V(G)} dist(*u*,*v*).

> **Definition 2.3.** Let *H*, *G* be graphs and let *d* ∈ ℕ. The graph
> *H* is a *depth-d minor* of *G*, written *H* ⪯_d *G*, if there is a
> minor model φ of *H* in *G* such that the branch set φ(*v*) ⊆ *G* has
> radius at most *d* for all *v* ∈ V(*G*).

(2017/18 Definition 6 is the same sentence with `r` in place of `d`. The
"*v* ∈ V(*G*)" at the end is a typo for V(*H*) in both editions.)

**Terminology.** The notes say **"depth-*d* minor"** for the relation and
**"radius at most *d*"** for the branch-set condition; "shallow minor" is
used only informally in running text ("*d*-shallow minor", "shallow minor
model"). There is **no** *r*/2 convention anywhere; depth *d* means branch
sets of radius ≤ *d*, full stop.

**Design.** `ShallowMinorModel r H G` with fields `branch`, `center`,
`center_mem`, `disjoint`, `radius_le` (every branch-set element reached
from `center u` by a walk of length ≤ `r` staying inside the branch set),
`adj : H.Adj u v → ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y`.

**Verdict: MATCHES.** `∃ center, ∀ x ∈ branch, dist ≤ r inside the branch
set` is literally `rad(φ(v)) ≤ r` and subsumes connectedness, so the
notes' "connected subgraph of radius at most *d*" is captured exactly.
Two packaging deviations, both content-preserving and already documented
in the design's formalization notes: (i) the notes' φ *chooses* an edge
φ(*e*) per edge of *H*, the design asserts existence — equivalent by
choice; (ii) walks instead of paths — equivalent, since shortcutting a
walk shrinks its support.

Naming nit only: the design docstring says "depth-*r* minor" in prose and
`ShallowMinorModel`/`HasShallowMinor` in code. The notes' own headline
term is *depth-r minor*. No change needed unless Jan wants the identifier
renamed to match.

---

## Item 2 — Nowhere dense

**Notes, 2019/20 Chapter 1, Definitions 2.4 and 2.6:**

> **Definition 2.4.** For a graph *G* and *d* ∈ ℕ we define
> ∇_d(*G*) := sup { |E(*H*)|/|V(*H*)| : *H* ⪯_d *G* } and
> ω_d(*G*) := sup { *t* : *K_t* ⪯_d *G* }.
> Further, for a class of graphs *C* and *d* ∈ ℕ, we define
> ∇_d(*C*) := sup_{G∈C} ∇_d(*G*) and ω_d(*C*) := sup_{G∈C} ω_d(*G*).

> **Definition 2.6.** A class *C* of graphs is *nowhere dense* if
> ω_d(*C*) < +∞ for every *d* ∈ ℕ.
> Equivalently, there is a function *t* : ℕ → ℕ such that for all *d* ∈ ℕ
> and *G* ∈ *C*, we have ω_d(*G*) ≤ *t*(*d*).

and the immediately following remark:

> Note that every graph is a subgraph of some clique, so nowhere denseness
> is equivalent to requiring that for every depth *d* ∈ ℕ we exclude at
> least one graph as a depth-*d* minor.

(2017/18 Definition 8 states the `∃t : ℕ → ℕ` form as the *primary*
definition: "A class *C* of graphs is nowhere dense if there is a function
*t* : ℕ → ℕ such that for all *r* and *G* ∈ *C*, ω_r(*G*) ≤ *t*(*r*)".)

**Design.**
```lean
def NowhereDense (C : GraphClass) : Prop :=
  ∀ r : ℕ, ∃ t : ℕ, ∀ n G, C n G → ¬ HasShallowMinor G r (⊤ : SimpleGraph (Fin t))
```

**Verdict: MATCHES.** The design's `∀r ∃t` (a per-depth clique excluded
from every member) is exactly the notes' `ω_d(C) < +∞ for every d`, and
literally the equivalent form the notes spell out in the remark. Swapping
the notes' `∃t : ℕ → ℕ, ∀d` for the design's `∀d ∃t` is the same statement
(no uniformity is lost; `t` may depend on `d`). No change.

---

## Item 3 — Grad ∇_r and the density predicate

**Notes:** Definition 2.3 / 2.4 above, verbatim:

> ∇_d(*G*) := sup { |E(*H*)| / |V(*H*)| : *H* ⪯_d *G* }

with the sanity remark (2019/20 Ch. 1, after Def. 2.6):

> Observe that the depth-0 minors of a graph are exactly its subgraphs,
> hence for every graph *G* we have ∇_0(*G*) = ½ · mad(*G*).

**There is no factor 2 in the notes' ∇.** It is `|E|/|V|`, not `2|E|/|V|`
and not `|E|/|V|` over subgraphs-of-minors. (This is the standard NOdM
convention; the notes make it unambiguous via the ∇_0 = ½ mad remark.
2017/18 Chapter 1's Lemma 6 states `∇_r(G) ≤ Δ^{r+1}` where 2019/20's
Lemma 2.7 states the corrected `∇_d(G) ≤ Δ^{d+1}/2` — an edition
discrepancy, but in a lemma the submission does not use.)

Topological grad, 2019/20 Chapter 1, Definitions 2.15–2.16:

> **Definition 2.15.** A graph *H* is a *topological depth-d minor* of
> *G*, written *H* ⪯^top_d *G*, if there is a model φ of *H* in *G* such
> that the paths φ(*e*) have length at most 2*d*+1 for all *e* ∈ E(*H*).
> In this definition we use length 2*d*+1 to reflect the basic relation
> with the minor order: *H* ⪯^top_d *G* entails *H* ⪯_d *G*.

> **Definition 2.16.** Fix *d* ∈ ℕ. For a graph *G* we define
> ∇̃_d(*G*) := sup { |E(*H*)|/|V(*H*)| : *H* ⪯^top_d *G* } and
> ω̃_d(*G*) := sup { *t* : *K_t* ⪯^top_d *G* }.

**Design.**
```lean
def HasDensityAtMost (G) (r d : ℕ) : Prop :=
  ∀ m (H : SimpleGraph (Fin m)), HasShallowMinor G r H → H.edgeSet.ncard ≤ d * m
```
plus a class-level `HasSubpolynomialDensity`. No numeric `grad` is
introduced.

**Verdict: MATCHES on the constant convention, DEVIATES on surface shape
(deliberately, and harmlessly).** `HasDensityAtMost G r d` is precisely
`∇_r(G) ≤ d` for `d : ℕ` — the sup-of-ratio and the `∀H, |E| ≤ d·|V|`
forms are interchangeable, and the design correctly counts edges once,
not twice, matching the notes. The only real gap is that the notes give
∇_r a *name and a value*, while the design has only the ≤-predicate. That
costs nothing for the four statements the submission makes; it costs the
archive the ability to say `∇_r(G)`. Flag for Jan, no fix required.

---

## Item 4 — The nowhere-dense density characterization

**Notes, 2019/20 Chapter 1, Theorem 3.1** (2017/18 Chapter 1, Theorem 20 —
word-for-word identical):

> **Theorem 3.1.** Suppose *C* is a nowhere dense class of graphs. Then
> for every *r* ∈ ℕ and every ε > 0 there exists a constant
> *N* = *N*(*r*, ε) such that for every graph *G* ∈ *C*⊙*r* with *n* ≥ *N*
> vertices, we have that *G* has less than *n*^{1+ε} edges.

with, immediately after:

> Observe that Theorem 3.1 is equivalent to saying that there is a
> function *f*(*r*, ε) such that every graph *G* ∈ *C*⊙*r* has at most
> *f*(*r*, ε)·|V(*G*)|^{1+ε} edges, without any lower bound on its size.

and (Definition 2.13) the reduct notation:

> *C*⊙*d* = { *H* : *H* is a depth-*d* minor of some *G* ∈ *C* }.

So: **threshold form is the headline; the multiplicative-constant form is
stated by the notes themselves as equivalent.** It is stated as a
**one-directional implication**, not an iff (the notes discuss the
dichotomy in prose but do not state a converse theorem). Attribution in
the notes: "The proof of Theorem 3.1 that we are going to present is due
to Zdeněk Dvořák." **The notes never attribute this theorem to
Nešetřil–Ossona de Mendez.** It is also *not* a limsup form.

**Design.**
```lean
def HasSubpolynomialDensity (C : GraphClass) : Prop :=
  ∀ (r : ℕ) (ε : ℝ), 0 < ε → ∃ c : ℝ, ∀ n G, C n G →
    ∀ m (H : SimpleGraph (Fin m)), HasShallowMinor G r H →
      (H.edgeSet.ncard : ℝ) ≤ c * (m : ℝ) ^ (1 + ε)
```
plus `axiom hasSubpolynomialDensity_of_nowhereDense`, whose docstring says
"…this is the density characterization of nowhere denseness of Nešetřil
and Ossona de Mendez", and mentions the converse.

**Verdict: MATCHES the notes' own equivalent form; one attribution
deviation.**
- Quantifier shape: notes `∀r ∀ε ∃N`, design `∀r ∀ε ∃c` — the notes state
  these equivalent, and the design's formalization note gives the same
  argument (m² bound). Fine.
- `< n^{1+ε}` vs `≤ c·m^{1+ε}`: the notes' own remark uses `at most
  f(r,ε)·|V|^{1+ε}`. Fine.
- `G ∈ C⊙r` vs "every depth-*r* minor *H* of a member": `C⊙r` is *defined*
  as exactly that set. Fine.
- **Attribution.** Minimal change: the docstring of
  `NowhereDenseDensity.lean` should not claim the theorem for
  Nešetřil–Ossona de Mendez if the intent is "use the notes' form". The
  notes credit the presented proof to Dvořák and state only the forward
  implication. Suggested edit: drop or hedge the "of Nešetřil and Ossona
  de Mendez" clause, or say "…due to Nešetřil and Ossona de Mendez; the
  proof in the source notes is Dvořák's." (Historically the result *is*
  NOdM's; the point is only that the cited document does not say so.)

---

## Item 5 — THE CRITICAL ITEM: the admissibility bound

**Notes, 2019/20 Chapter 2, Lemma 3.2** (2017/18 Chapter 2, Lemma 8 —
identical formula):

> **Lemma 3.2.** For every *r* ∈ ℕ and graph *G*, the following holds
>
>     adm_r(G)  ≤  1 + 6r ⌈∇̃_{r−1}(G)⌉³

Note carefully, verbatim from the notes:
- the parameter is **⌈∇̃_{r−1}(G)⌉** — the **ceiling** of the **topological**
  grad, at depth **r − 1**;
- the constant is **6r**, and the power is **3**: `1 + 6·r·d³`;
- the bound is on **adm_r(G)** (the minimum over orderings), not
  adm_r(G, σ);
- the section it lives in is announced as: "…we will prove that if an
  algorithm for computing the *r*-admissibility of a graph fails to
  produce an ordering with small admissibility, this is because it
  encounters an obstacle in the form of a **dense depth-(r−1) topological
  minor**."

The proof's inner statement is isolated as a separate lemma, which is the
cleanest "hypothesis form" the notes offer:

> **Lemma 4.1.** Suppose *G* is a graph and *S* ⊆ V(*G*) is a vertex
> subset such that b_r(*S*, *v*) > 6*rd*³ for all vertices *v* ∈ *S*, for
> some *r*, *d* ∈ ℕ. Then *G* contains a depth-(*r*−1) topological minor
> of edge density larger than *d*.

and inside the proof of Lemma 3.2 the working hypothesis is used as:
"Let *d* := ⌈∇̃_{r−1}(*G*)⌉ … which is a contradiction with *J* being a
depth-(*r*−1) topological minor of *G*."

The complementary direction (also in the same section) is:

> **Lemma 3.1.** For every *r* ∈ ℕ and graph *G* the following holds:
> ∇_r(*G*) ≤ wcol_{4r+1}(*G*).

**Design.**
```lean
axiom adm_le_of_hasDensityAtMost (G : SimpleGraph (Fin n)) (r d : ℕ)
    (h : HasDensityAtMost G r d) : adm G r ≤ 1 + 6 * r * d ^ 3
```
i.e. hypothesis = every **depth-r ordinary minor** has ≤ d·|V| edges
(`∇_r(G) ≤ d`), conclusion = `adm_r(G) ≤ 1 + 6·r·d³`. The vendored
catalog theorem `adm_le_of_topGrad_bound` has the notes' hypothesis:
`∀ H, IsShallowTopologicalMinor H G (r-1) → |E(H)| ≤ d·|V(H)|`.

**Verdict: DEVIATES — twice, in the same direction (weakening), and the
constant is exactly right.**

| aspect | notes (Lemma 3.2 / 4.1) | design | sound? |
|---|---|---|---|
| constant | `1 + 6·r·d³` | `1 + 6·r·d³` | identical |
| parameter | `d = ⌈∇̃_{r−1}(G)⌉`, a **ceiling** — so `d : ℕ` with `∇̃_{r−1}(G) ≤ d` | `d : ℕ` with `∇_r(G) ≤ d` | ✓ |
| minor kind | **topological** (⪯^top) | ordinary (⪯) | ✓ weakening |
| depth index | **r − 1** | r | ✓ weakening |
| conclusion | `adm_r(G)` (min over orderings) | `adm G r` (`sInf`, = min over orderings) | identical |

Soundness of both weakenings, spelled out: the notes' own Definition 2.15
says `H ⪯^top_d G` entails `H ⪯_d G`, and a depth-(r−1) minor is a
depth-r minor (radius ≤ r−1 ≤ r). So
`∇_r(G) ≤ d  ⟹  ∇_{r−1}(G) ≤ d  ⟹  ∇̃_{r−1}(G) ≤ d`, i.e. the design's
hypothesis is strictly stronger and the design's statement follows from
the notes'. Nothing is claimed that the notes do not prove; the archive
simply records a weaker theorem.

**Minimal change to adopt the notes' form**, if Jan chooses to:
1. add a `ShallowTopologicalMinorModel` (edge-indexed routed paths, path
   length ≤ 2(r−1)+1, internally disjoint, pins injective) and a
   `HasTopDensityAtMost G r d` predicate to the surface — the design's
   decision (1) rejects exactly this on styleguide grounds;
2. restate as
   `axiom adm_le_of_hasTopDensityAtMost (G) (r d : ℕ)
      (h : HasTopDensityAtMost G (r - 1) d) : adm G r ≤ 1 + 6 * r * d ^ 3`,
   reintroducing truncated `ℕ` subtraction into the hypothesis (or index
   by `r` and conclude at `r + 1`, which is the same statement with no
   truncation: `HasTopDensityAtMost G r d → adm G (r+1) ≤ 1 + 6*(r+1)*d³`).

A **middle option** that removes only the *depth* deviation and keeps
topological minors out: state the hypothesis at depth `r` but conclude at
`r + 1`:
`HasDensityAtMost G r d → adm G (r + 1) ≤ 1 + 6 * (r + 1) * d ^ 3`.
Also implied by the catalog theorem, also truncation-free, and closer to
the notes' index pairing (hypothesis one below the conclusion). This is
the cheapest partial adoption if Jan dislikes the current `r`/`r` pairing.

**Jan's call.** The two facts he needs are: (a) the notes' hypothesis is
`⌈∇̃_{r−1}(G)⌉`, ceiling of topological grad at depth `r−1`; (b) the
constant `1 + 6r·d³` in the design is verbatim the notes' constant.

---

## Item 6 — Lemma 2.5: strong coloring number vs. admissibility

**Notes, 2019/20 Chapter 2, Lemma 2.5** (= 2017/18 Chapter 2, Lemma 2,
with `col` for `scol`):

> **Lemma 2.5.** For every *r* ∈ ℕ, graph *G*, and its vertex ordering σ,
> the following holds:
>
>     scol_r(G, σ)  ≤  1 + (adm_r(G, σ) − 1)^r

**Design.** `axiom scol_le_of_adm (G) (r) : scol G r ≤ 1 + (adm G r - 1) ^ r`.

**Verdict: MATCHES in formula; DEVIATES in that the notes state it
per-ordering.** The notes prove it for a *fixed* σ; the design states the
minimized (parameter-level) form. The minimized form is *not* stated for
Lemma 2.5 alone in the notes, but the notes do state the minimized form of
the chain in Corollary 2.7 ("In particular, for every *r* ∈ ℕ and graph
*G* we have: adm_r(G) ≤ scol_r(G) ≤ wcol_r(G) ≤ 1 + r(adm_r(G) − 1)^{r²}").
The minimized Lemma 2.5 follows from the per-σ one by instantiating at an
adm-optimal σ (RHS monotone in adm), which is what the design's
formalization note says. Constant, exponent and the `−1` are verbatim.
**No change needed**; if Jan wants literal fidelity, the per-σ form would
require exposing `scol G π r` / `adm G π r` per-ordering variants on the
surface, which the design deliberately does not.

---

## Item 7 — Lemma 2.6 and Corollary 2.7

**Notes, 2019/20 Chapter 2, Lemma 2.6** (= 2017/18 Lemma 3):

> **Lemma 2.6.** For every *r* ∈ ℕ, graph *G*, and its vertex ordering σ,
> the following holds:
>
>     wcol_r(G, σ)  ≤  1 + r(scol_r(G, σ) − 1)^r

**Notes, Corollary 2.7** (= 2017/18 Corollary 4):

> **Corollary 2.7.** For every *r* ∈ ℕ, graph *G*, and its vertex ordering
> σ, the following holds:
>
>     adm_r(G, σ) ≤ scol_r(G, σ) ≤ wcol_r(G, σ) ≤ 1 + r(adm_r(G, σ) − 1)^{r²}
>
> In particular, for every *r* ∈ ℕ and graph *G* we have:
>
>     adm_r(G) ≤ scol_r(G) ≤ wcol_r(G) ≤ 1 + r(adm_r(G) − 1)^{r²}

(The preceding **Proposition 2.4** is the trivial chain
`adm_r(G,σ) ≤ scol_r(G,σ) ≤ wcol_r(G,σ)`.)

**Design.** `axiom wcol_le_of_scol : wcol G r ≤ 1 + r * (scol G r - 1) ^ r`;
Corollary 2.7 gets **no** concept — its arithmetic moves into the headline
glue proof.

**Verdict: MATCHES (Lemma 2.6) with the same per-σ→minimized caveat as
item 6.** Note the exact exponent in the notes' Corollary 2.7 is **r²**
(not `r`), i.e. `1 + r·(adm_r − 1)^{r²}` — the design's prose in decision
(2) writes exactly `wcol ≤ 1 + r·(adm-1)^(r²)`, correct. Also worth
recording for the design: the trivial half of Corollary 2.7
(`adm ≤ scol ≤ wcol`, notes' Proposition 2.4) is *not* stated anywhere in
the design; the glue only needs the upper direction, so this is fine, but
the archive will not record Proposition 2.4.

---

## Item 8 — Definitions of wcol_r, scol_r, adm_r

**Notes, 2019/20 Chapter 2 (2017/18 identical wording, `col` for `scol`):**

> By a *vertex ordering* of *G* we mean any enumeration of V(*G*) with
> numbers from 1 to |V(*G*)|, i.e., a bijective function
> σ : V(*G*) → {1, …, |V(*G*)|}. We often think of σ as the linear order
> ≤_σ …

> **Definition 2.1.** Let *G* be a graph, let σ be a vertex ordering of
> *G*, and let *r* ∈ ℕ. For vertices *u*, *v* ∈ V(*G*) with *u* ≤_σ *v*,
> we say that:
> - *u* is **strongly *r*-reachable** from *v*, if there is a **path** of
>   length at most *r* from *u* to *v* whose every internal vertex *w*
>   satisfies *v* <_σ *w*; and
> - *u* is **weakly *r*-reachable** from *v*, if there is a **path** of
>   length at most *r* from *u* to *v* whose every internal vertex *w*
>   satisfies *u* <_σ *w*.
>
> For a vertex *v*, the set of vertices strongly, respectively weakly,
> *r*-reachable from *v* in σ is denoted by SReach_r[*G*, σ, *v*],
> respectively by WReach_r[*G*, σ, *v*].
>
> Note that **every vertex is both weakly and strongly *r*-reachable from
> itself.**

> **Definition 2.2.** … The *r*-admissibility of a vertex *v* of *G*,
> denoted adm_r(*G*, σ, *v*), is equal to **one plus** the maximum size of
> a family of paths 𝒫 with the following properties:
> - every path from 𝒫 has length at most *r* and leads from *v* to some
>   vertex smaller than *v* in σ;
> - paths from 𝒫 are pairwise vertex-disjoint apart from sharing the
>   endpoint *v*.
>
> … Note also that the *r*-admissibility is equal **not to |𝒫|**, where 𝒫
> is a path family as above, **but to 1 + |𝒫|**. The rationale behind the
> +1 summand is to be consistent with the choice of definitions for weak
> and strong reachability…

> **Definition 2.3.** … wcol_r(*G*, σ) := max_{v} |WReach_r[*G*, σ, *v*]|,
> scol_r(*G*, σ) := max_{v} |SReach_r[*G*, σ, *v*]|,
> adm_r(*G*, σ) := max_{v} adm_r(*G*, σ, *v*).
> The weak *r*-coloring number, the strong *r*-coloring number, and the
> *r*-admissibility of *G* are defined as **the minimum among vertex
> orderings** σ of *G* of the respective parameter for σ. That is, if by
> Π(*G*) we denote the set of vertex orderings of *G*, then
> wcol_r(*G*) := min_{σ∈Π(G)} wcol_r(*G*, σ), etc.
>
> Note that for *r* = 1, all the above three notions are equal to the
> **degeneracy plus one**.

Point by point against the checklist:

| question | notes' answer |
|---|---|
| paths or walks | **paths** |
| is the vertex itself counted | **yes** — "every vertex is both weakly and strongly *r*-reachable from itself", so wcol_r ≥ 1, scol_r ≥ 1 on a nonempty graph |
| weak/strong reachability | Definition 2.1 above; the *precondition* `u ≤_σ v` is part of the definition, the difference is which endpoint the internal vertices must exceed (`v <_σ w` strong, `u <_σ w` weak) |
| adm counts *k* or *k*+1 | **k + 1** ("one plus the maximum size of a family of paths"), explicitly justified as consistency with reachability sets counting *v* |
| ordering | an **enumeration** σ : V(G) → {1,…,n}, i.e. a bijection, "often thought of as the linear order ≤_σ" |

**Design.** `wreach`/`sreach` as `Set (Fin n)` over **walks**, both
containing `v`; `wcol`/`scol` as `Nat.sInf {k | ∃π, ∀v, ncard ≤ k}` with
`π : Equiv.Perm (Fin n)`; `AdmFamily … r k v` a `Fin k`-indexed family and
`HasAdmAtMost G r k := ∃π, ∀ v j, Nonempty (AdmFamily G π r j v) → j + 1 ≤ k`,
`adm := sInf {k | HasAdmAtMost G r k}`.

**Verdict: MATCHES on every substantive point.**
- ordering as `Equiv.Perm (Fin n)` = the notes' bijective enumeration ✓
- `v` counted in both reachability sets ✓ ("Both sets contain `v`")
- the `+1` in admissibility is present (`j + 1 ≤ k`) ✓ and the design's
  docstring gives the notes' own rationale
- min over orderings realized as `sInf` over achievable bounds ✓
- **walks vs paths**: the only deviation, addressed in the design's
  formalization notes, and genuinely equivalent (shortcutting a walk to a
  path only shrinks its support, so the reachability sets and the maximum
  family sizes coincide). No change.
- One asymmetry worth noting: the design's `wreach` demands `π u ≤ π y`
  for **all** support vertices (which subsumes the notes' precondition
  `u ≤_σ v`), whereas `sreach` carries `π u ≤ π v` as a separate conjunct.
  That is exactly the notes' structure — Definition 2.1's precondition is
  automatic in the weak case and not in the strong case. ✓

---

## Item 9 — Nowhere dense ⇒ subpolynomial wcol

**Notes, 2019/20 Chapter 2, Theorem 3.4** (= 2017/18 Chapter 2, Theorem 10,
verbatim):

> **Theorem 3.4.** Let *C* be nowhere dense class of graphs. Then there is
> a function *f* : ℕ × ℝ → ℕ such that wcol_r(*G*) ≤ *f*(*r*, ε)·|V(*G*)|^ε
> for all *r* ∈ ℕ, ε > 0, and *G* ∈ *C*.

and its companion for bounded expansion,

> **Theorem 3.3.** Let *C* be a class of graphs. Then the following
> conditions are equivalent. 1. *C* has bounded expansion. 2. There is a
> function *f* : ℕ → ℕ such that wcol_r(*G*) ≤ *f*(*r*) for all *G* ∈ *C*
> and *r* ∈ ℕ. 3. … scol_r … 4. … adm_r …

**Design.**
```lean
def HasSubpolynomialWcol (C : GraphClass) : Prop :=
  ∀ (r : ℕ) (ε : ℝ), 0 < ε → ∃ c : ℝ, ∀ n G, C n G →
    ∀ m (H : SimpleGraph (Fin m)), H ⊑ G → (wcol H r : ℝ) ≤ c * (m : ℝ) ^ ε
axiom hasSubpolynomialWcol_of_nowhereDense (C) (h : NowhereDense C) : HasSubpolynomialWcol C
```

**Verdict: DEVIATES (design is stronger — over subgraphs, not members).**
- The notes quantify over **members** *G* ∈ *C* only. The design
  quantifies over **subgraph copies** `H ⊑ G` of members, each measured by
  its own vertex count. There is no subgraph-closure hypothesis on `C` in
  either.
- The design's form is *derivable* from the notes' (apply Theorem 3.4 to
  the subgraph closure of *C*, which is nowhere dense — the notes'
  Corollary 2.14 gives closure of nowhere denseness under reducts, and
  subgraphs are depth-0 minors), so nothing unsound; but the archived
  statement is not the notes' statement.
- Quantifier order: notes `∃f : ℕ×ℝ → ℕ` outside `∀r ∀ε`; design
  `∀r ∀ε ∃c`. Equivalent (currying + choice), and the design's order is
  the readable one.
- The notes' `f` lands in ℕ, the design's `c` in ℝ. Immaterial.

**Minimal change to adopt the notes' form**: drop the `H ⊑ G`
quantification —
`∀ r ε, 0 < ε → ∃ c, ∀ n G, C n G → (wcol G r : ℝ) ≤ c * (n : ℝ) ^ ε`.
**Recommendation: do not.** The design notes (correctly) that
`HasSubpolynomialWcol` is byte-for-byte the Lax5 declaration, so changing
it breaks the `rfl` transport that the whole LaxS↔Lax5 architecture rests
on. Record this as a knowing, documented deviation instead: the design's
docstring already says "Since nowhere denseness survives taking subgraphs,
the uniformity of that predicate over subgraph copies of members loses
nothing here."

---

## Item 10 — Uniform quasi-wideness

**Notes, 2019/20 Chapter 4, Definition 3.1:**

> **Definition 3.1.** A class of graph *C* is called *uniformly
> quasi-wide* if **for every *r* ∈ ℕ there exists a function
> *N_r* : ℕ → ℕ and a constant *s_r* ∈ ℕ** such that for all *m* ∈ ℕ,
> *G* ∈ *C*, and *A* ⊆ V(*G*) with |*A*| ≥ *N_r*(*m*), there exists
> *S* ⊆ V(*G*) with |*S*| ≤ *s_r* and *B* ⊆ *A* − *S* with |*B*| ≥ *m*
> such that *B* is distance-*r* independent in *G* − *S*.
>
> … Constants *s_r* are sometimes called the **margins**, while *N_r*(·)
> are the **wideness functions**.

(Recall from the chapter intro: "a vertex subset *A* ⊆ V(*G*) in a graph
*G* is *distance-r independent* if any two different vertices *a*, *b* ∈ *A*
are at distance larger than *r*.")

**2017/18 Chapter 3, Definition 2** — same content, different quantifier
packaging:

> A class of graph *C* is called uniformly quasi-wide if there are
> functions *N* : ℕ×ℕ → ℕ and *s* : ℕ → ℕ such that for all *m*, *r* ∈ ℕ,
> *G* ∈ *C* and *A* ⊆ V(*G*) with |*A*| ≥ *N*(*m*, *r*) there exists
> *S* ⊆ V(*G*) with |*S*| ≤ *s*(*r*) and *B* ⊆ *A* − *S* with |*B*| ≥ *m*
> such that *B* is *r*-independent in *G* − *S*.

Both editions: **N depends on r and m; s depends on r only**; **no
subgraph-closure assumption**; `S ⊆ V(G)` unrestricted (not required
disjoint from `A`, but `B ⊆ A − S`).

**The theorem.** 2019/20 Chapter 4:

> **Theorem 3.2.** A class *C* of graphs is uniformly quasi-wide if and
> only if it is nowhere dense.
>
> **Lemma 3.3.** If a class *C* is uniformly quasi-wide, then *C* is
> nowhere dense.
>
> **Lemma 3.4.** If a class *C* is nowhere dense, then *C* is uniformly
> quasi-wide.

(2017/18: Theorem 2, Lemma 3, Lemma 4.)

**Remarks the notes attach to Lemma 3.4** (2019/20, end of §3):

> First, it should be clear that it is algorithmic: a straightforward
> implementation of the proof gives a polynomial-time procedure that given
> *r*, *m* ∈ ℕ together with *G* and *A* of appropriate size, outputs
> suitable *S* and *B*. … Second, the provide[d] proof yields
> tower-Ramsey bounds on the function *N_r*(*m*) … There is a smarter
> (though, more involved) way of executing the proof of this lemma, which
> actually yields polynomial bounds. As a consequence, the following
> statement is true: **if *C* is nowhere dense, then *C* is uniformly
> quasi-wide with margins *s_r* and wideness functions *N_r*(·), where for
> every fixed *r* ∈ ℕ, the function *N_r*(*m*) is a polynomial of *m***.

(2017/18 states the algorithmic version as its own **Theorem 11**.)

**Design.**
```lean
def UniformlyQuasiWide (C : GraphClass) : Prop :=
  ∀ r : ℕ, ∃ (N : ℕ → ℕ) (s : ℕ), ∀ (m n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    ∀ A : Set (Fin n), N m ≤ A.ncard →
      ∃ S B : Set (Fin n), S.ncard ≤ s ∧ B ⊆ A \ S ∧ m ≤ B.ncard ∧
        DistIndependent (deleteVerts G S) r B
axiom uniformlyQuasiWide_of_nowhereDense (C) (h : NowhereDense C) : UniformlyQuasiWide C
```

**Verdict: MATCHES, essentially exactly.** Clause by clause against
Definition 3.1: `∀r ∃(N : ℕ→ℕ)(s : ℕ)` ✓ (the notes' `N_r`, `s_r`, in the
notes' own 2019/20 packaging rather than 2017/18's curried `N : ℕ×ℕ→ℕ`);
`∀m, G ∈ C, A ⊆ V(G), N m ≤ |A|` ✓; `∃S ⊆ V(G), |S| ≤ s` ✓; `B ⊆ A − S`
✓ (`B ⊆ A \ S`); `|B| ≥ m` ✓; `B` distance-*r* independent in `G − S` ✓
(via `deleteVerts`, which isolates rather than removes — since `B ⊆ A \ S`
the two agree, as the design's note says). No subgraph-closure hypothesis
in either ✓.

The theorem-concept states only Lemma 3.4 (the hard direction), which is
exactly a lemma of the notes; the design explicitly declines to conjoin
the converse (notes' Lemma 3.3 / Theorem 3.2). Consistent with the
one-axiom rule and with the notes' own splitting.

Not adopted (correctly, as extra content): the polynomial-`N_r` refinement
and the algorithmic version. Worth mentioning in the docstring only if
Jan wants the archive to record what the notes claim beyond the bare
implication.

---

## Item 11 — Bipartite Ramsey lemmas ("Lemma 3.10")

**Confirmed: `iterated_bipartite_ramsey` is Lemma 3.10 of the 2019/20
notes, Chapter 4 (*Uniform quasi-wideness*)** — not of Mählmann's thesis.
The same statement is Lemma 10 of the 2017/18 notes, Chapter 3.

The chapter's Ramsey material, in order (2019/20 numbering):

> **Theorem 3.7.** Let *a*, *b* ∈ ℕ. Then there exists a number *R*(*a*,*b*)
> such that for every coloring of the edges of a complete graph on
> *R*(*a*,*b*) vertices with colors red and blue we will either find a
> clique on *a* vertices whose edges are all blue or a clique on *b*
> vertices whose edges are all red.

(with `R(a,b) ≤ C(a+b−2, a−1)` proved in-line.)

> **Theorem 3.8.** Let *n*₁, …, *n_k* ∈ ℕ. There exists a number
> *R*(*n*₁,…,*n_k*) such that for every coloring of the edges of a
> complete graph on *R*(*n*₁,…,*n_k*) vertices with *k* different colors
> *c*₁,…,*c_k* we will find for some 1 ≤ *i* ≤ *k* a clique on *n_i*
> vertices all of whose edges are colored with color *c_i*.

> **Lemma 3.9.** Let *G* be a bipartite graph with sides *A* and *B*. Let
> *m*, *t*, *d* ∈ ℕ. If |*A*| ≥ *R*(*t*, …, *t*, *m*), where *t* is
> repeated ⌊(*d*−1)/2⌋ times [the notes print `(d−1)/2`], then at least one
> of the following assertions holds.
> (a) *A* contains a set *A*₀ ⊆ *A* of size *m* such that no two vertices
>     of *A*₀ have a common neighbor;
> (b) in *G* there is a 1-subdivision of *K_t* with all principal vertices
>     contained in *A*; or
> (c) *B* contains a vertex of degree at least *d*.

> For convenience, we write *R_d*(*t*, *m*) for *R*(*t*, …, *t*, *m*)
> where the first argument is repeated (*d*−1)/2 times. Then let
> *R*⋆(*s*, *t*, *m*) := *t* if *s* = 0; *R_k*(*t*, *m*) if *s* ≥ 1, where
> *k* = *R*⋆(*s*−1, *t*, *m*).

> **Lemma 3.10.** Let *G* be a bipartite graph with partitions *A* and
> *B*. If |*A*| ≥ *R*⋆(*t*, *t*, *m*), then at least one of the following
> assertions holds.
> (a) *A* contains a set *A*₀ ⊆ *A* of size *m* and *B* contains a set *S*
>     of size less than *t* such that no two vertices of *A*₀ have a
>     common neighbor outside of *S*;
> (b) in *G* there is a 1-subdivision of *K_t* with all principal vertices
>     contained in *A*;
> (c) in *G* there is a complete bipartite subgraph *K_{t,t}*.

**Edition difference (argument order of R⋆ only).** 2017/18 writes
`R⋆(t, m, d, s)` with the recursion on the *last* argument and states
Lemma 10 with the hypothesis `|A| ≥ R⋆(t, m, t, t)`; 2019/20 writes
`R⋆(s, t, m)` with the recursion on the *first* and states
`|A| ≥ R⋆(t, t, m)`. Same function, same lemma. 2017/18's Lemma 9 also
omits the explicit `d` in the Lemma-10 recursion step ("apply Lemma 9 to
the graph *G*[*A_i* ∪ *B_i*]" without naming `d`); 2019/20 fixes this to
"with *d* = *R*⋆(*t*−*i*−1, *t*, *m*)". **Prefer the 2019/20 wording** for
any "ramsey fundamentals" submission.

Also relevant to that submission, from the same chapter, the two
step-reduction lemmas the uqw induction uses:

> **Lemma 3.5.** Let *A* be a distance-2*j* independent set in *G*. Let
> *H* ⪯_j *G* be the depth-*j* minor of *G* [obtained by contracting the
> radius-*j* balls around *A*] …
> **Lemma 3.6.** Let *A* be a distance-(2*j*+1) independent set in *G*.
> Let *H* ⪯_j *G* be the depth-*j* minor …

(text truncated in the extraction; read `ed2019/chapter4.pdf` pp. 3–4 if
these are needed verbatim.)

**Verdict for the design: N/A (not part of `sparsity-lectures`).** The
citation "Lemma 3.10" in the vendored code resolves correctly to the
2019/20 notes' Chapter 4. A separate "ramsey fundamentals" submission
would state Theorem 3.7 / Theorem 3.8 / Lemma 3.9 / Lemma 3.10 in the
forms quoted above.

---

## Summary table

| # | item | verdict |
|---|---|---|
| 1 | depth-*r* minor | MATCHES (notes say "depth-*r* minor", branch sets of radius ≤ *r*; no *r*/2 convention) |
| 2 | nowhere dense | MATCHES (design's `∀r ∃t` is the notes' own stated equivalent of ω_r(C) < ∞) |
| 3 | grad ∇_r | MATCHES on convention (`|E|/|V|`, no factor 2); design has no numeric grad — deliberate, flagged |
| 4 | density characterization | MATCHES the notes' stated-equivalent constant form; **attribution deviates** (notes credit Dvořák's proof, never name NOdM) |
| 5 | **admissibility bound** | **DEVIATES** — notes: `adm_r(G) ≤ 1 + 6r⌈∇̃_{r−1}(G)⌉³` (topological grad, depth *r*−1, ceiling). Constant identical. Design's version is a sound weakening. Jan's call. |
| 6 | Lemma 2.5 | MATCHES formula verbatim; notes state it per-ordering, design minimized |
| 7 | Lemma 2.6 / Cor 2.7 | MATCHES formula verbatim (Cor 2.7 exponent is *r*²); Proposition 2.4 (`adm ≤ scol ≤ wcol`) not recorded |
| 8 | wcol/scol/adm definitions | MATCHES on all substantive points (vertex counted, adm = 1+\|𝒫\|, min over enumerations); walks-for-paths is the only deviation |
| 9 | nowhere dense ⇒ subpoly wcol | **DEVIATES** — notes quantify over members only, design over subgraph copies. Sound, stronger, but keep it (Lax5 `rfl` transport) |
| 10 | uniform quasi-wideness | MATCHES Definition 3.1 clause for clause; theorem-concept = notes' Lemma 3.4 |
| 11 | bipartite Ramsey | Confirmed: notes' Chapter 4, Lemma 3.9 and **Lemma 3.10** (2019/20); 2017/18 = Lemma 9/10 with permuted `R⋆` arguments |
