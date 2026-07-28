# Contract V6 — wrap-up (Jan-visible)

Session scope: the submission's outward-facing record catches up with the
discharge. Files: `ram-linear-time/abstract.md`, `ram-linear-time/notes.md`,
regenerate `ram-linear-time/build-output.json` (via the `lax` CLI — `lax
build` in `ram-linear-time/`; if the CLI misbehaves, log the failure and skip
this item, never hand-edit the JSON). **No concept edits; no proof edits**
unless `lax build` itself reports a defect. Commit when done. Read first:
`NIGHTLOG.md` tail (V4/V5 entries — you need the achieved constant),
`vc-ladder-plan.md` §V6, `abstract.md` in full, `notes.md`, and the V5
docstring in `proofs/Lax11Proofs/VCMain.lean`.

## Edits

1. **`abstract.md`, final paragraph.** It currently reads "The vertex cover
   statement is open" and defends leaving obligations open. That defense is
   now obsolete for this statement: replace the paragraph with one saying the
   statement is now discharged — the bounded search tree in the same
   while-language, costed by the same loop rule, with the parameter
   dependence explicit (`c · 2^k · (|x|+1)` with the achieved `c` if the
   sibling paragraphs quote constants — check whether they do and match
   their level of detail). Keep the submission's larger point (concepts
   decoupled from proofs, honesty about what is decided vs proved) if it
   still has a home elsewhere in the abstract; do not delete claims that
   remain true of *other* parts. Match the register of the surrounding
   text; one paragraph, no more.
2. **`notes.md`, the vertex-cover bullet.** Its items now live in two
   places: the concept file's notes (unchanged) and the new conclusion
   annotation in `proofs/Lax11Proofs/VCMain.lean`. Rewrite the bullet in the
   style of the CC bullet above it, and delete the "open obligation"
   sentence.
3. **`build-output.json`.** Regenerate; verify it records the new proof of
   `exists_fptTime_program_vertexCover` with `assumptions: []` and that the
   theorem's `sections` list the docstring's headers. Note: the file may be
   gitignored (it was regenerated before without being committed) — check
   `git status` and stage only what the repo actually tracks.

## Wrap-up

- Commit message: `Lax11 vc: wrap-up — abstract and notes record the discharge`.
- `NIGHTLOG.md` entry per the protocol in `vc-night-brief.md`, marked
  prominently **for Jan's morning review**, listing: the achieved constant,
  the four commits of the campaign, anything you chose that Jan might undo
  (abstract wording), and that `lax submit` remains Jan's call. Do not stage
  `NIGHTLOG.md`.
