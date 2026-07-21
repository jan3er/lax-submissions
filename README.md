# lax-submissions

Lax archive submissions, ported from Édouard Bonnet's twin-width
formalization (github.com/EdouardBonnet/leaning, `twin-width/`, MIT).

- `twin-width-treewidth-exponential-reviewable/` — **Lax3**: twin-width can
  be exponential in treewidth (three concepts: treewidth, twin-width, and the
  separation theorem). Registered replacement for Lax1.
- `twin-width-mixed-minor-equivalence-reviewable/` — **Lax4**: twin-width and
  mixed minor number are functionally equivalent (two concepts: mixed minor
  number and the equivalence theorem). Builds on Lax3 and replaces Lax2.

The `twin-width-treewidth-exponential/` and
`twin-width-mixed-minor-equivalence/` folders preserve the Lax1/Lax2 source
lineage. Their registered archive revisions are immutable historical
snapshots.

Each folder is a lax submission (`lax build` must pass); see the manifest
and `abstract.md` inside.
