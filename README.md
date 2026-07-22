# lax-submissions

Lax archive submissions, ported from Édouard Bonnet's twin-width
formalization (github.com/EdouardBonnet/leaning, `twin-width/`, MIT).

Current archive content (fresh database, both in the **draft** state, meant
to be polished into exemplary concept packages):

- `twin-width-treewidth-separation/` — **Lax1**: twin-width can be
  exponential in treewidth (three concepts: treewidth, twin-width, and the
  separation theorem). Natural phrasing: plain structures and Prop-valued
  predicates instead of the def-encodings of the earlier lineage.
- `twin-width-mixed-minor-number/` — **Lax2**: twin-width and mixed minor
  number are functionally equivalent (two concepts: mixed minor number and
  the equivalence theorem). A draft depending on the Lax1 draft.

Historical lineage, no longer in the database:
`twin-width-treewidth-exponential/` and
`twin-width-mixed-minor-equivalence/` are the original ports;
`twin-width-treewidth-exponential-reviewable/` and
`twin-width-mixed-minor-equivalence-reviewable/` grouped them into
reviewable concepts (the previous Lax3/Lax4), still def-encoded due to
earlier lax limitations.

Each current folder is a lax submission (`lax build` must pass); see the
manifest and `abstract.md` inside.
