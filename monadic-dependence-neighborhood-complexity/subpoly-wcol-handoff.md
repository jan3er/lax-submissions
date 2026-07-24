# Subpolynomial wcol proof handoff

The in-progress proof files are parked at:

`/tmp/monadic-dependence-neighborhood-complexity-subpoly-wcol`

They discharge `Lax5.NowhereDenseWcol.hasSubpolynomialWcol_of_nowhereDense`
using the axiom-free proof linked from
<https://main.autoformalize.pages.dev/catalog/Catalog.SparsityLectures.NDSubpolynomialWcol/>.

## Parked contents

- `proofs/Lax5Proofs/NowhereDenseWcol.lean`: the bridge to this submission's
  canonical graph classes, shallow-minor model, and permutation-based `wcol`.
- `proofs/Lax5Proofs/Source/Catalog/SparsityLectures/`: the vendored catalog
  proof chain (16 files, 6,131 lines), renamed below `Lax5Proofs.Source`.
- `HANDOFF.md`: detailed status and resume instructions.

The vendored catalog theorem and all its dependencies build successfully
against this repository's pinned Lean/mathlib. The bridge is close but its
latest revision has not yet built: resume at the `rankPerm`/`OrderIso`
instance mismatch described in the parked `HANDOFF.md`.

Do not touch the unrelated existing edits in
`proofs/Lax5Proofs/Sparsification.lean` or `../todo.md`.
