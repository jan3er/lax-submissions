# Contract V4a — `outerBody_run` (VCLoop.lean)

Session scope: append to `ram-linear-time/proofs/Lax11Proofs/VCLoop.lean` the
body-transition lemma of the outer loop, split as three theorems. Nothing else.
Commit when green. Read first (skim): `vc-ladder-plan.md` (§algorithm, §VC4),
`NIGHTLOG.md` tail (VC session 1), then the files you build on: `VCSpec.lean`
(Config, Inv, the six `inv_*` and `pot_*` lemmas), `VC.lean` (the program),
`VCScan.lean` (`scan_run`, and its proof as the style model), `VCLoop.lean`
(Rep, the indicator and reverse-indexing lemmas). Everything you need already
exists; this milestone is assembly, not invention.

## Statements (contract — keep these signatures; names may not change)

```lean
theorem descendBody_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ j < 2 * m, T j = target g j)
    {C : Config n} {τ : Env} (hRep : Rep n m k O T C τ)
    (hInv : Inv G k C) (hmode : C.mode = 0) :
    ∃ (C' : Config n) (τ' : Env) (K : ℕ),
      Run descendBody τ τ' K ∧ Rep n m k O T C' τ' ∧ Inv G k C' ∧
      pot C' + 1 ≤ pot C ∧ K ≤ 100 * m + 50 * n + 96 ∧
      τ'.inp = τ.inp ∧ τ'.out = τ.out

theorem backtrackBody_run
    {C : Config n} {τ : Env} (hRep : Rep n m k O T C τ)
    (hInv : Inv G k C) (hmode : C.mode = 1) :
    ∃ (C' : Config n) (τ' : Env) (K : ℕ),
      Run backtrackBody τ τ' K ∧ Rep n m k O T C' τ' ∧ Inv G k C' ∧
      pot C' + 1 ≤ pot C ∧ K ≤ 96 ∧
      τ'.inp = τ.inp ∧ τ'.out = τ.out

theorem outerBody_run (hg : EncodesGraph g n G) (hm : edgeCount g = m)
    (hO : ∀ i ≤ n, O i = offset g i) (hT : ∀ j < 2 * m, T j = target g j)
    {C : Config n} {τ : Env} (hRep : Rep n m k O T C τ)
    (hInv : Inv G k C) (hmode : C.mode < 2) :
    ∃ (C' : Config n) (τ' : Env) (K : ℕ),
      Run outerBody τ τ' K ∧ Rep n m k O T C' τ' ∧ Inv G k C' ∧
      pot C' + 1 ≤ pot C ∧ K ≤ 100 * m + 50 * n + 100 ∧
      τ'.inp = τ.inp ∧ τ'.out = τ.out
```

(`g n m k G O T` are the file's `variable`s. The numerals 96/100 have slack;
if a case genuinely exceeds one, raise it and say so in the log — but the
**total** `100*m + 50*n + 100` is load-bearing for V4b's loop potential factor
`100*m + 50*n + 104`; if you must exceed it, raise both in the log entry.
Downstream only needs the factor `≤ numeral·(x.length+1)`, so slack is fine.)

## The case analysis (all six checked on paper — they line up exactly)

Derive once from `hInv`: `hlen : C.frames.length ≤ k` (from
`C.bud + C.frames.length = k`). Rep gives `τ.vars "mode" = C.mode` etc.;
`outerBody = .ite (.eq (.var "mode") (.lit 0)) descendBody backtrackBody`
dispatches on `C.mode` (`hmode : C.mode < 2` plus the Inv clause `C.mode ≤ 2`
give the two cases 0 and 1).

**descend** (`C.mode = 0`): destructure Rep's mark clause `⟨MK, hmark, hMK⟩`
and run `scan_run hg hm hO hT` (its preconditions `m2`, `off`, `tgt`, `mark`
are Rep clauses). Cost exactly `100*m + 50*n + 10`. Its frame condition
spares every Rep scalar (`m2, mode, bud, ans, top`) and all arrays. Then
`.ite (.eq (.var "found") (.lit 0))`:

1. **found = 0** — success exit. `C' := ⟨C.frames, 2, C.bud, 1⟩`.
   Machine: `ans := 1; mode := 2`. Invariant: `inv_found_cover` with the cover
   from `isVertexCover_of_slots hg (marked C.frames)`; its slot hypothesis
   comes from the scan's "every slot covered" clause via `mem_of_indicator_ne
   hMK` (for the owner `o < n` and the target, whose `< n` bound the slot
   hypothesis hands you). Pay: `pot_found`.
2. **found = 1, C.bud = 0** — stuck. `C' := ⟨C.frames, 1, 0, C.ans⟩`.
   Machine: `mode := 1`. The scan gives `eu, ev < n`, `Adjn G eu ev`
   (destructure: `Adjn G a b = ∃ ha hb, G.Adj ⟨a,ha⟩ ⟨b,hb⟩`), and
   `MK eu = MK ev = 0`; turn the latter into `∉ marked C.frames` via
   `not_mem_of_indicator_eq hMK`. Invariant: `inv_stuck`. Pay: `pot_stuck`
   (note its statement is at `bud = 0` on the nose — rewrite with
   `hb : C.bud = 0` first). Test used: `.ite (.eq (.var "bud") (.lit 0))`.
3. **found = 1, C.bud > 0** — push. With `u := ⟨eu, _⟩, v := ⟨ev, _⟩ : Fin n`,
   `C' := ⟨Frame.mk u v false :: C.frames, 0, C.bud - 1, C.ans⟩`.
   Machine: stores `stkU/stkV/stkP` at `top`, store `mark[eu] := 1`,
   `top := top + 1`, `bud := bud - 1`. Store-in-range: `top =
   C.frames.length < k` since `C.bud + C.frames.length = k` and `C.bud > 0`
   (arrays are `arrOf k _`, length `k`); `eu < n` for the mark store.
   New array functions via `set_arrOf`. Rep of the stack: index
   `C.frames.length` is the new frame by `reverse_getElem_top`, lower indices
   by `reverse_getElem_lt` (both directions of the cons). Mark indicator:
   `marked (f :: fs) = insert u (marked fs)` (`marked_cons`, `chosen_false`);
   new `MK'` is `if w = eu then 1 else MK w` — for `w ≠ eu` membership in the
   insert reduces to the old membership since `(⟨w,_⟩ : Fin n) = u ↔ w = eu`
   by `Fin.ext_iff`. Invariant: `inv_push` (adjacency from `Adjn`,
   non-membership as in case 2). Pay: `pot_push`.

**backtrack** (`C.mode = 1`): `.ite (.eq (.var "top") (.lit 0))`, and
`τ.vars "top" = C.frames.length`.

4. **top = 0** — failure exit. `C.frames = []` (`List.length_eq_zero_iff`).
   `C' := ⟨[], 2, C.bud, 0⟩`. Machine: `ans := 0; mode := 2`.
   Invariant: `inv_fail`. Pay: `pot_fail`.
5. **top > 0, top frame phase 0** — flip. `C.frames = f :: fs`
   (`List.exists_cons_of_ne_nil` or match on the list), and the reads
   `pu := stkU[top-1]`, `pv := stkV[top-1]`, `stkP[top-1]` hit index
   `fs.length`, which is the top frame by `reverse_getElem_top`: `pu = f.u`,
   `pv = f.v`, and the phase test selects on `f.ph` (indicator `0`/`1`).
   For `f.ph = false`, destructure `f = ⟨u, v, false⟩`.
   `C' := ⟨Frame.mk u v true :: fs, 0, C.bud, C.ans⟩`. Machine:
   `mark[pu] := 0; mark[pv] := 1; stkP[top-1] := 1; mode := 0`
   (in-range: `pu, pv < n` are the `Fin n` coercions; `fs.length < k`).
   New mark function: `if w = ev then 1 else if w = eu then 0 else MK w`
   (the `pv` write is last, so it wins — this matches `mem_marked_flip`,
   whose Healthy hypothesis comes from Inv with `hfr` rewritten; `v ≠ u` is
   inside it, no separate argument needed). Stack Rep: `SP` set at
   `fs.length`; the head swap leaves lower indices equal via
   `reverse_getElem_lt` applied on both the old and the new cons.
   Invariant: `inv_flip`. Pay: `pot_flip`.
6. **top > 0, phase 1** — pop. `f = ⟨u, v, true⟩`,
   `C' := ⟨fs, 1, C.bud + 1, C.ans⟩`. Machine: `mark[pv] := 0;
   bud := bud + 1; top := top - 1`. Mark via `mem_marked_pop` (same shape as
   case 5, one write). Stack arrays unchanged; the `∀ i < fs.length` clause
   transports by `reverse_getElem_lt`. Invariant: `inv_pop`. Pay: `pot_pop`
   (stated at `b + 1` — it matches `C.bud + 1` on the nose).

## House rules that bite here

- Build `Run` derivations by hand exactly as `scan_run` does:
  `Run.ite_true/ite_false` with an explicit `Cond.eval` fact, `Run.seq`,
  `Run.assign (v := _)`, `Run.store (idx := _) (v := _)` (needs the in-range
  proof), then one `.mono` per case to the numeral — never fight for tight
  costs, `omega` closes them.
- Array reads in conditions/exprs: `getElem?_arrOf` with the `< k` / `< n`
  bound; `set_arrOf` for stores. `simp [hτ', ...]` with a `set τ' := ... with
  hτ'` per case is the house pattern for re-establishing Rep.
- Re-establish **every** Rep clause per case, including the untouched ones
  (`m2`, `off`, `tgt`) — the frame conditions of `setVar`/`setArr` simp away.
- Never `simp` with concept definitions; `omega` can't see structure fields
  (`have := hInv.2.1` style first).
- `lean_goal` / `lean_multi_attempt` over rebuild loops; the build is warm.
- Zero `sorry`; `lake build` green in `proofs/`; commit **only**
  `VCLoop.lean`, message `Lax11 vc: the outer-loop body — six transitions, one lemma`.
- Append a session entry to `NIGHTLOG.md` (protocol in `vc-night-brief.md`),
  do not stage it.
