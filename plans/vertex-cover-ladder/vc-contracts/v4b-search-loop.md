# Contract V4b — `searchLoop_run` (VCLoop.lean)

Session scope: append to `ram-linear-time/proofs/Lax11Proofs/VCLoop.lean` the
outer-loop lemma, one application of `Run.while_pot` on top of
`outerBody_run`. Nothing else. Commit when green. Read first (skim):
`NIGHTLOG.md` tail, `vc-ladder-plan.md` §V4, then `VCLoop.lean` in full
(`Rep`, `potN`, `phasesOf`, `potN_eq`, `outerBody_run`), `VCSpec.lean`
(`Inv`, `pot`), and `VCScan.lean`'s closing `Run.while_pot` application as
the style model. `Run.while_pot` is in `Reasoning.lean` (conclusion:
`K + Φ σ' ≤ Φ σ + 1 + b.size`).

## Statement (contract — keep this signature)

```lean
theorem searchLoop_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ j < 2 * m, T j = target g j)
    {C₀ : Config n} {σ : Env} (hRep : Rep n m k O T C₀ σ) (hInv : Inv G k C₀) :
    ∃ (C' : Config n) (τ' : Env) (K : ℕ),
      Run (.while (.lt (.var "mode") (.lit 2)) outerBody) σ τ' K ∧
      Rep n m k O T C' τ' ∧ Inv G k C' ∧ C'.mode = 2 ∧
      τ'.inp = σ.inp ∧ τ'.out = σ.out ∧
      K ≤ (100 * m + 50 * n + 104) * pot C₀ + 4
```

## The proof shape (checked on paper)

- Loop invariant handed to `Run.while_pot`:
  `I τ := ∃ C, Rep n m k O T C τ ∧ Inv G k C ∧ τ.inp = σ.inp ∧ τ.out = σ.out`.
- Potential (total on `Env`, per the file's doc comment):
  `Φ τ := (100 * m + 50 * n + 104) * potN (τ.vars "mode") (τ.vars "bud") (phasesOf τ)`.
- `hdef`: the condition reads no array — `fun τ _ => ⟨_, rfl⟩`.
- `hstep`: from `I τ` and the condition true get `C.mode < 2` (Rep pins
  `τ.vars "mode" = C.mode`; `Cond.eval` of `.lt (.var _) (.lit _)` unfolds by
  `simp`). Apply `outerBody_run`; the new state satisfies `I` by its Rep/Inv
  and inp/out clauses (transitivity with the old ones). The payment: with
  `b.size = 3` (it is `.lt (.var "mode") (.lit 2)`; `simp [Cond.size,
  Expr.size]` or the `size_*` simp lemmas), the obligation
  `1 + 3 + K + Φ τ' ≤ Φ τ` follows from `K ≤ 100*m + 50*n + 100`,
  `pot C' + 1 ≤ pot C`, and `potN_eq` on both ends (its `hlen` comes from
  Inv's `C.bud + C.frames.length = k`); the arithmetic is
  `4 + K + F·p' ≤ F·(p' + 1) ≤ F·p` for `F = 100*m + 50*n + 104` — after
  `Nat.mul_le_mul_left` / `Nat.mul_succ`, `omega` (or `nlinarith`-free
  `calc`) closes it. Do **not** let `omega` face the bare product; introduce
  `have := potN_eq ...` rewrites first.
- Exit: condition false gives `¬ (C'.mode < 2)` through Rep; Inv's
  `C'.mode ≤ 2` makes it `= 2`.
- Final bound: `while_pot` returns `K + Φ τ' ≤ Φ σ + 1 + b.size`; rewrite
  `Φ σ = F * pot C₀` by `potN_eq` and drop `Φ τ'`.

## House rules

- Loose constants, `.mono`/`≤` slack everywhere; if V4a shipped with a larger
  body bound than `100*m + 50*n + 100`, raise the factor `104` to keep
  `4 + K ≤ F` and note it in the log (V5 only needs `F ≤ numeral·(x.length+1)`).
- Zero `sorry`; `lake build` green in `proofs/`; commit **only**
  `VCLoop.lean`, message `Lax11 vc: the outer loop — while_pot over the tree potential`.
- Append a session entry to `NIGHTLOG.md` (protocol in `vc-night-brief.md`),
  do not stage it.
