# Contract V5 — assembly and audit (`VCMain.lean`)

Session scope: new file `ram-linear-time/proofs/Lax11Proofs/VCMain.lean`
(import `Lax11Proofs.VCLoop`), plus wiring the five VC modules into the root
`Lax11Proofs.lean` (append, in order: `VCSpec`, `VC`, `VCScan`, `VCLoop`,
`VCMain` — they are currently not imported there, so the default `lake build`
skips them). Nothing else; **never edit `concepts/`**. Commit when green.
Read first (skim): `NIGHTLOG.md` tail, `vc-ladder-plan.md` §V5, the frozen
statement in `ram-linear-time/concepts/Lax11/VertexCover.lean`, then the
house model **`CCSweep.lean` from `ccExt` to the end of `ccCom_run`** (the
read-phase assembly you will mirror almost line for line) and **`CCMain.lean`
in full** (const lemma, docstring shape, endgame). In `VCLoop.lean`:
`searchLoop_run`, `Rep`. In `VCSpec.lean`: `inv_init`, `ans_eq`,
`pot_init_le`, `pot_init`.

## Deliverables

### 1. Extents and constant

```lean
/-- The array extents the driver runs with. -/
def vcExt (n m k : ℕ) (a : String) : ℕ :=
  if a = "off" then n + 1 else if a = "tgt" then 2 * m
  else if a = "mark" then n else k
```

```lean
theorem const_eq : layout.const = 37 := by
  simp [Layout.const, Layout.idxLen, layout]
```

(37 is what session 1 computed for six arrays; if `simp`/`decide` yields a
different numeral, use the true one and thread it through — log it.)

### 2. The end-to-end run

```lean
theorem vcCom_run {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k m : ℕ}
    (hx : EncodesInstance x n G k) (hm : edgeCount x = m) :
    ∃ (σ' : Env) (K : ℕ), Run vcCom (initEnv (vcExt n m k) x) σ' K ∧
      σ'.out = [if G.vertexCoverNum ≤ (k : ℕ∞) then 1 else 0] ∧
      K ≤ 900 * 2 ^ k * (x.length + 1) := by
```

(One wrinkle vs CC: `hm` is stated on `x = g ++ [k]`; `edgeCount` reads index
1, and `g` has length ≥ 3, so `edgeCount x = edgeCount g` — derive it via
`List.getD_append` / `getD` on the concatenation, or simply state `hm` as
`edgeCount x = m` and prove `edgeCount g = m` from it. Pick whichever
composes; the endgame below instantiates `m := edgeCount x` like CCMain. The
`open Classical in` on the concept statement means the `if` needs
`Classical` decidability — put `open Classical in` where required.)

Proof shape, mirroring `ccCom_run`:

- Destructure `hx : ∃ g, x = g ++ [k] ∧ EncodesGraph g n G` as
  `⟨g, rfl, hg⟩`. From `hg.length_eq`: `g.length = 3 + n + 2 * m`, so
  `g = n :: m :: rest` with `rest.length = 1 + n + 2 * m` (CC's rcases
  pattern), and the tape is `n :: m :: (rest ++ [k])`.
  `ys := rest.take (n+1)`, `zs := rest.drop (n+1)`; `hyd`/`hzd` give
  `offset g` / `target g` exactly as in CC (the helper lemmas `getD_take`,
  `getD_drop`, `getD_cons_cons` live in `CCSweep` and are importable).
- The reads: `read n`, `read m`, `len := n + 1`, `readLoop "off" "len"`
  (`ys`, rest of tape `zs ++ [k]`), `m2 := m + m`, `readLoop "tgt" "m2"`
  (`zs`, rest `[k]`), `read "bud"` (leaves `inp = []`). Note the second
  read-loop limit is **"m2"**, not "len" — `m2` must still hold `2 * m` when
  the search starts, which it does because `readLoop`'s frame condition
  spares everything but `"i"`, `"t"`.
- Initial configuration `C₀ := (⟨[], 0, k, 0⟩ : Config n)`. Establish
  `Rep n m k O T C₀ σ₇`: `m2 = 2*m`; `off`/`tgt` from the read loops; `mode`,
  `top`, `ans` are `0` because `initEnv` zeroes every scalar and nothing in
  the read phase touches them (chase the frame conditions); `bud = k` from
  the last read; mark clause with `MK := fun _ => 0` — `initEnv` gives
  `List.replicate n 0`, convert by `replicate_eq_arrOf`, and
  `marked [] = ∅` makes the indicator trivially right; stack clause with
  `SU = SV = SP := fun _ => 0`, the `∀ i < 0` condition vacuous. Invariant:
  `inv_init`.
- `searchLoop_run` (note `vcCom`'s loop is literally
  `.while (.lt (.var "mode") (.lit 2)) outerBody` — definitionally the
  statement's loop). Get `C'`, mode 2, `Rep`, `Inv`, `inp`/`out` preserved.
- The answer: `ans_eq hInv' rfl : C'.ans = if G.vertexCoverNum ≤ (k : ℕ∞)
  then 1 else 0`; `Run.write` of `.var "ans"` with `τ'.vars "ans" = C'.ans`
  from Rep; `out` goes from `[]` to `[C'.ans]`.
- Cost: read phase is `≤ 12*(n+1) + 12*(2*m) + 30`-ish (sum the numerals, no
  fighting); loop `≤ (100*m + 50*n + 104) * pot C₀ + 4` and
  `pot C₀ ≤ 4 * 2 ^ k` (`pot_init_le`); write `2`. Then with
  `X := x.length + 1 = 5 + n + 2*m` (from `length_eq` plus the appended
  `[k]`): `n ≤ X`, `2*m ≤ X`, so `100*m + 50*n + 104 ≤ 204 * X`, giving
  loop `≤ 816 * 2^k * X + 4` and total `≤ 900 * 2^k * X` with room. Do the
  nonlinear steps by `calc` with `Nat.mul_le_mul` / `Nat.mul_le_mul_left`
  and `Nat.one_le_two_pow` (for absorbing additive slack into `2^k * X`);
  hand `omega` only linear residues — it cannot multiply variables. If V4b
  shipped a factor other than 104, rescale; any numeral ≤ 2048 in place of
  900 is acceptable, smallest convenient wins, none fought for.

### 3. The endgame theorem

Statement **verbatim** from the concept (with `open Classical in` if needed):

```lean
theorem exists_fptTime_program_vertexCover :
    ∃ (p : Program) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ),
      ComputesInTime p {x | EncodesInstance x n G k}
        (fun _ => if G.vertexCoverNum ≤ (k : ℕ∞) then [1] else [0])
        (fun x => c * 2 ^ k * (x.length + 1))
```

Witness `⟨vcProgram, 37 * 900, ...⟩` (or the true product), via
`computesInTime_of_run vcCom_ok`, extents `vcExt n (edgeCount x) k`,
mirroring `CCMain.exists_linearTime_program_ccLabels`. Watch the output
shape: the concept's function returns `[1]`/`[0]` — `if_pos`/`if_neg` push
the `if` inside the list, or state `vcCom_run`'s out as the `if` of lists
directly if that composes better. For the final `L.const * K ≤ c * 2^k *
(x.length+1)`: `generalize 2 ^ k * (x.length + 1) = z` (after `rw
[const_eq]` and associativity) so `omega` sees a linear goal.

Docstring: proof-package frontmatter, exactly CCMain's shape —

```
/--
---
conclusion: Lax11.VertexCover.exists_fptTime_program_vertexCover
---
<prose: what is computed, within what bound, by which witness>

# Proof strategy
<the bounded search tree; the invariant J splitting Ok between the active
marking and the stored alternatives; the tree potential 4·2^b − 3 amortizing
the whole search in one loop rule; the flat scan amortized over slots and
owners; where 2^k enters (pot of the initial configuration) and where the
constant comes from (37 machine steps per IMP+ unit × the per-unit loop
factor)>

# What the program is allowed to help itself to
<the honesty section, only if there is something to say — e.g. the budget is
not stored in frames because both children of the 2^k tree run at b − 1, and
the mark array is never initialized because fresh memory is zeroed and 0 is
the unmarked marker; say why neither smuggles work out of the bound>

# Attribution
<the opening result of parameterized complexity; the textbook bounded search
tree, e.g. Downey–Fellows; the base 2 is the point — no reduction rules>
-/
```

Voice: match CCMain/CourcelleMain — declarative, no hedging, no bullet
spam. Keep it shorter than CCMain's; this is the second driver on the same
substrate and may say so.

### 4. Audit

- `lake build` in `proofs/` green, no warnings from your files.
- `lean_verify` on `Lax11Proofs.VCMain.exists_fptTime_program_vertexCover`
  (fully qualified — check your namespace): axioms must be exactly
  `propext`, `Classical.choice`, `Quot.sound`. Paste the result in the log.
- Commit `VCMain.lean` + `Lax11Proofs.lean` only, message
  `Lax11 vc: the 2^k discharge — assembly, endgame, constant <c>`.
- Append a session entry to `NIGHTLOG.md` (protocol in `vc-night-brief.md`,
  include the achieved constant), do not stage it.
