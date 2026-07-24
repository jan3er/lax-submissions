# lax-submissions

Flagship submissions for the Lax archive, ported from Édouard Bonnet's
twin-width formalization (github.com/EdouardBonnet/leaning, `twin-width/`,
MIT).

Current archive content (both in the **draft** state, serving as the
exemplary concept packages future contributors imitate):

- `twin-width-treewidth-separation/` — **Lax1**: twin-width can be
  exponential in treewidth (three concepts: treewidth, twin-width, and the
  separation theorem).
- `twin-width-mixed-minor-number/` — **Lax2**: twin-width and mixed minor
  number are functionally equivalent (two concepts: mixed minor number and
  the equivalence theorem). Depends on the Lax1 draft.

Each folder is a lax submission (`lax build` must pass); see the manifest
and `abstract.md` inside.

**Creating the next submission? Read [SUBMISSION-GUIDE.md](SUBMISSION-GUIDE.md)
first** — it condenses the spec and states the styleguide these flagship
packages are held to.
