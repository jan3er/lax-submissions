# Writing a Lax submission

This document is the working brief for anyone — human or agent — creating
the next submission in this repository. It condenses the parts of the Lax
spec a submission author needs, and then states the style this repository
holds itself to. Read the styleguide as seriously as the rules: these are
**flagship submissions**, the examples future contributors will imitate, and
the elegance of the concept packages is the whole point.

The normative rule set lives in the Lax spec (`lax spec` prints the exact
version the installed CLI enforces). When this document and the spec
disagree, the spec wins.

The two submissions in this repository — `twin-width-treewidth-separation/`
(Lax1) and `twin-width-mixed-minor-number/` (Lax2) — are the reference
implementations of everything below. When in doubt, open them and imitate.

---

## 1. What the archive is

Lax is the social and archival layer for automated Lean formalization. Its
content comes in two kinds:

- A **concept** pairs a mathematical object stated in natural language (as
  it would appear in a paper) with a faithful Lean encoding. Concepts
  contain **no proofs**: they carry exactly what is needed to pin down the
  semantics of a statement or definition, and nothing more. Reviewers will
  publicly endorse concepts as faithful, staking their names on them —
  concepts are written *for humans*.
- A **proof** is ordinary Lean code discharging a claim made by a concept.
  The kernel checks it, so proofs can be arbitrarily ugly and entirely
  machine-written without compromising trust.

A **submission** is a citable unit containing concepts and proofs. The two
are decoupled: a submission may leave its own proof obligations open, and
may discharge obligations of other submissions. Submissions are frozen in
time — Lean, Lake, and mathlib versions are pinned archive-wide.

The asymmetry drives everything in this guide: **all trust flows through
the concept package, all cleverness belongs in the proof package.**

## 2. Layout and environment

Archive environment (must match exactly):

- toolchain `leanprover/lean4:v4.30.0` (verbatim content of every
  `lean-toolchain`), `specVersion: "1"`
- mathlib pinned to `c5ea00351c28e24afc9f0f84379aa41082b1188f`, required by
  every package
- `autoImplicit = false` everywhere
- background axioms: `propext`, `Classical.choice`, `Quot.sound` — nothing
  else may appear in any axiom set

A submission with id `LaxN` is a folder:

    mysubmission/
      manifest.yaml
      abstract.md              -- non-empty, rendered on the website
      LICENSE                  -- Apache 2.0, verbatim
      concepts/
        lakefile.toml
        lean-toolchain
        LaxN.lean              -- root module: one import line per concept, nothing else
        LaxN/Foo.lean          -- one file per concept, no subfolders
      proofs/
        lakefile.toml
        lean-toolchain
        LaxNProofs.lean        -- root module, same shape
        LaxNProofs/...

`build-output.json`, `lake-manifest.json`, and `.lake/` are generated —
never check them in (the scaffold's `.gitignore` covers them). `lax init`
produces this whole layout; never author `lake-manifest.json` or run
`lake update`.

`manifest.yaml` allows exactly these keys — `specVersion`, `id`,
`leanVersion` (`"v4.30.0"`), `mathlibVersion` (the pin), `title`, `authors`
(list of `name` + optional `orcid`/`github`), `bibEntries` (verbatim BibTeX
strings). See the two existing manifests.

Lakefiles are whitelisted: `name`, `defaultTargets`, `[leanOptions]` with
`autoImplicit = false`, `[[require]]` entries, one `[[lean_lib]]`. Package
and lib are both named `LaxN` (concepts) / `LaxNProofs` (proofs). Both
packages require mathlib at the pin. The proof package requires its own
concept package via `path = "../concepts"`. A dependency on another
submission pins the **exact** repository, commit, and subfolder of that
submission's current record — see `twin-width-mixed-minor-number/concepts/
lakefile.toml` for a live example.

Namespaces: everything a concept module `LaxN/Foo.lean` declares lives
under `LaxN.Foo`; everything in the proof package under `LaxNProofs`.

Imports: own package, Lean core, mathlib, and required packages only.
Mathlib's dependencies (`Batteries`, `Aesop`, …) are not importable —
import the corresponding mathlib module instead.

## 3. Concepts, statements, proofs — the mechanics

- Every non-root module of the concept package is a **concept**. Its
  **statements** are the `axiom`s it declares. Concepts declare statements
  but never use them: the axiom set of every concept declaration must be
  background-only (plus, for a statement, itself).
- A **proof** is a proof-package `theorem` whose docstring carries yaml
  frontmatter with a `conclusion:` naming a statement it discharges; the
  kernel checks definitional equality of the types. Declarations without
  frontmatter are helpers the archive ignores. Every axiom used anywhere in
  the proof package must be a background axiom or a statement of a
  *directly required* concept package.

### Annotations

A concept is annotated by a single module docstring `/-! … -/`; a proof by
its ordinary docstring `/-- … -/`. Both are markdown with minimal yaml
frontmatter. Text before the first `#` heading is the main description;
`#` headings split off extra sections rendered as separate blocks.

Concept annotation:

    /-!
    ---
    title: Twin-width
    type: definition            -- or: theorem
    ---
    Pure-mathematical description, exactly as a paper would state it.

    # Formalization notes

    Why the encoding is what it is: which fields are derivable and hence
    omitted, why an infimum ranges over a nonempty set, etc.
    -/

Proof annotation:

    /--
    ---
    conclusion: Lax1.ExponentialSeparation.twin_width_can_be_exponential_in_treewidth
    ---
    One-paragraph summary of what is proved.

    # Proof strategy

    The high-level idea, especially how source material is bridged to the
    submitted concepts.

    # Attribution

    Where the proof comes from.
    -/

Unrecognized frontmatter keys are build errors. The `description` (main
text) and `title` are required for concepts. Write prose as **Markdown, not
TeX** — docstrings render no math: `*k*`-division, `2^k`, backticks for
Lean names.

## 4. The styleguide: elegance above all

The archive's entire value rests on a reviewer reading a concept and
endorsing it as faithful. A concept package is therefore judged the way a
paper's definitions are judged: by whether a domain expert reads it once
and nods. Elegance is not polish applied at the end — it is the product.

**Concepts read like the paper, not like a formalization.** State the
mathematics the way the literature states it. If the natural definition
talks about partitions, encode partitions — not a state machine that
happens to simulate them. The flagship example: twin-width in
`Lax1/TwinWidth.lean` is a sequence of vertex partitions whose red degrees
are *derived* from homogeneity in the graph. The source development's
trigraph machinery (carrying red/black edge state alongside) is
mathematically equivalent and formally convenient — and lives entirely in
the proof package, bridged by an invariant.

**Plain structures and Prop-valued predicates; no def-encodings.** A
mathematical property is a `Prop`, a mathematical object is a `structure`
whose fields are its defining data and properties. Avoid `Bool`-valued
encodings, decidability plumbing, and `Classical` noise in concept code —
the two flagship concept packages contain zero `Classical` mentions.
Matrix entries in `Lax2/MixedMinorNumber.lean` are `Prop`, so the
graph-to-matrix bridge is literally `G.Adj`.

**Carry nothing derivable.** Every structure field is something a reviewer
must check; fields that follow from the others are review surface wasted.
`Division` has four fields because disjointness and convexity follow from
ordering and covering; `ContractionSequence` has six because partition-hood
of every state follows from "starts at singletons and merges". When you
drop a derivable field, say so in the formalization notes — and prove the
derived facts in the proof package where they are needed.

**Uniform numeric conventions.** A graph parameter is a
`HasXAtMost : … → ℕ → Prop` predicate plus `x := sInf {d | HasXAtMost … d}`
(or `sSup` for a "largest such" parameter). `Nat.sInf ∅ = 0` and bounded
`sSup` handle degenerate cases without special-case hatches — but the
formalization notes must argue why the set is nonempty or bounded, so the
reader knows the convention is never actually exercised.

**Statements over canonical types.** Theorems quantify over concrete,
canonical carriers — `∃ n, ∃ G : SimpleGraph (Fin n), …` — not over
arbitrary types with existentially bundled instances. When two parameters
must share a signature so a theorem can apply to both *directly*, make the
signature an `abbrev` (see `GraphParam` in `Lax1`): the statement then
mentions `twinWidth` and `mixedMinorNumber` themselves, with no
eta-expanded wrapper lambdas a reviewer would have to unfold.

**One concept per reviewable idea.** A concept is the unit of endorsement.
Lax1 has three: treewidth, twin-width, the separation theorem — each one
sitting a reviewer can hold in their head. Do not pack unrelated
definitions into one module, and do not shred one definition across many.
A definition-concept carries the complete definition of one notion; a
theorem-concept states one result over imported definition-concepts.

**Docstring every declaration.** Each `def`, `structure`, field, and
`axiom` in a concept gets a one- or two-sentence docstring saying what it
is mathematically. The module's annotation carries the paper-level prose;
declaration docstrings carry the local reading aid.

**Proofs absorb all the ugliness.** Bridging lemmas, ported source
developments, 800-line inductions — all fine, all invisible to the
endorsement surface. The proof package's job is to connect whatever
material exists (typically a ported development in its own idiom) to the
clean concepts, ideally by proving the submitted notion pointwise *equal*
to the source notion and transporting the source theorem across.

**Abstracts are for mathematicians.** `abstract.md` states what is proved,
in what form, and how the concept surface is organized into review units —
see the two existing abstracts for the register.

## 5. Workflow

    cd <this repo>
    lax init mysubmission        # allocates LaxN, scaffolds, provisions mathlib
    # ... write concepts and proofs ...
    lax build mysubmission       # full local pipeline; add --replay for the kernel check
    git add ... && git commit
    git push                     # HEAD must be on the remote
    lax submit mysubmission      # draft; --register to freeze

Notes learned the hard way:

- `lake build` inside `concepts/` or `proofs/` works at any time for fast
  iteration (init pre-provisions everything; nothing is downloaded).
- Depending on another submission: the require's `(git, rev, subDir)` must
  match the dependency's **current** record triple exactly. So submit the
  dependency first, pin the exact submitted commit, and run `lax pull-db`
  before building the dependent — a re-draft of the dependency moves the
  triple and breaks downstream pins until they are updated.
- `lax submit` derives the triple from a clean worktree's HEAD. To submit a
  dependency at a pinned historical commit while the branch has moved on,
  submit from a temp clone checked out at that commit.
- Lean warnings do not fail a build; every rule violation is collected and
  reported at once.

### Lean 4.30 / pinned-mathlib gotchas

- `tauto` can time out on de-Morgan-shaped iffs after `propext` rewrites;
  `rw [not_and_or, not_and_or]` closes them by `rfl`.
- `rw` with bare commutativity lemmas rewrites the wrong occurrence;
  instantiate explicitly (`(A := …) (B := …)`) or state oriented lemmas.
- `Nat.sSup_empty` does not exist; use `csSup_empty` + `bot_le`.
- The ncard/Finset bridge is `Set.ncard_coe_finset` (lowercase f) at this
  pin.
- Structures with instance fields can break `Finset.univ` synthesis when
  the goal mentions `(someDef D).Node`: prove `∀`-lemmas about `D.Node`
  first, then `exact` into the defeq goal.

## 6. Pre-submit checklist

- [ ] `lax build --replay` passes with no violations
- [ ] every concept: `title` + `type` frontmatter, paper-level description,
      `# Formalization notes` justifying every encoding choice
- [ ] every proof: `conclusion` frontmatter, summary, `# Proof strategy`,
      `# Attribution`
- [ ] concept packages: no `Classical`, no `Bool`-encodings, no derivable
      structure fields, no proofs, docstrings on every declaration
- [ ] statements phrased over canonical types, parameters via
      `HasXAtMost` + `sInf`/`sSup`
- [ ] prose is Markdown (no TeX in docstrings); abstract reads like a
      paper abstract
- [ ] generated files untracked; dependency pins match the current records

---

## Appendix: local archive ops

The drafts in this repository were submitted against a locally run server.
Recipe (fake GitHub auth is a test seam, never production):

    # server
    LAX_FAKE_GITHUB=1 LAX_FAKE_GITHUB_USERS="EdouardBonnet:1" \
      lax-server serve --home ~/.lax-server --port 8080

    # CLI environment
    export LAX_SERVER_URL=http://localhost:8080
    export LAX_GITHUB_TOKEN=tok-EdouardBonnet
    export LAX_DB_URL=file:///home/jan/.lax-server/db.git

To reset the archive: stop the server, delete `db.git`, `home/db`, `jobs`,
`site`, and `store/submissions` under `~/.lax-server` (**keep**
`store/mathlib` and `home/tools`), restart — the server bootstraps a fresh
database. Allocate ids via `POST /init`. If a pre-existing warm store fails
with "holds no trusted mathlib artifacts", re-run `lax-server warm` (cheap
no-op migration).
