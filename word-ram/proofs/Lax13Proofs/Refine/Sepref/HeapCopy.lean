import Lax13Proofs.Refine.Sepref.HeapAlloc
import Lax13Proofs.Refine.Ir.SepSolver

/-!
# The range-copy loop — `dst[0..n) := src[0..n)`

Leaf **P4.5.A.4**, the named gap of the P5.E re-seat (ledger **E34**).
`Iicf/Impl/ArrayListGrow.lean` exhibited growth as `mopAlloc (2·cap)` followed
by an element-wise copy, priced but **not realized**: "its IR realization is a
bounded `while` over two heap ranges, and no such loop rule is landed yet".
This file lands it.

Nothing here is new combinator theory.  `Examples/ArrayFill.lean` already
builds `while i < n do { A[i] := v; i := i + one }` with an exact credit
vector, through `fillPayload` / `fillInv` / `fill_step` / `fill_guard` /
`fill_body_triple` / `fill_exit` / `fill_loop` / `fill_triple`.  The copy loop
is that skeleton with two changes: two `↦ₕ` ranges (A.1) instead of one
whole-name array, and an `aget`+`aset` body instead of a bare `aset`.

## The program, and what it costs

```
while si < se do { t := heap[si]; heap[di] := t; si := si + one; di := di + one }
```

`si` and `di` are **cursors**, not counters: they hold the absolute heap
addresses `sp + j` and `dp + j`, which is exactly the shape A.1's
`haget_triple` / `haset_triple` take their index cell in (judgment call
D-A1c).  There is therefore no separate index cell and no separate `n` cell:
the bound rides in `se`, holding `sp + n`, and the loop is over the source
cursor.  That is one `add` per iteration cheaper than a counter loop, which
would have to recompute `sp + i` and `dp + i` from `i`.

The price, per iteration, is `blitPayload`:

| unit | why |
|---|---|
| `ir.while` | this iteration's guard evaluation |
| `ir.aget` | the read |
| `ir.aset` | the write |
| `ir.add` | bumping `si` |
| `ir.add` | bumping `di` |

and the whole loop costs `blitCost n = ir.while + n • blitPayload`, i.e.

```
(n + 1) · ir.while + n · ir.aget + n · ir.aset + 2n · ir.add
```

`blitCost_eq` states that as an **equation** on the credit vector, and the
leading `ir.while` is the trailing *failed* guard test — wave A's convention
(judgment call D-d of `Syntax.lean`, and `ArrayFill.lean`'s header): a loop
charges one `ir.while` per guard evaluation, so `n` iterations charge `n + 1`.

**This corrects a recorded cost.**  `ArrayListGrow.lean`'s `arlCopyCost n` was
`n • (ir.aget + ir.aset)` — no `ir.while`, no `ir.add`.  That was the cost
function nobody consumed, and therefore the cost function nobody checked: it
is *understated*, in the same way `implHeapSwimCost` / `implHeapSinkCost` were
(ledger **F11**), and by the same mechanism.  The emitted loop's real cost is
derived here from the program and `arlCopyCost` is redefined to be it.  In
particular `arlCopyCost 0` is **not** `0`: an empty copy still evaluates the
guard once and pays one `ir.while`.

## Disjointness (judgment call D-A4a)

The two ranges must not overlap, and the premise that says so is the
**separating conjunction itself**: the precondition owns `sp ↦ₕ xs` *and*
`dp ↦ₕ zs`, and A.1's `ptoH_sepConj_overlap` is the compiled fact that two
overlapping ranges cannot both be owned.  So the triple below carries no
arithmetic side condition like `dp + n ≤ sp ∨ sp + n ≤ dp`; it carries the
ownership, which is strictly stronger (it also rules out sharing a range with
the frame) and is the form every other rule in this tower states.
`blitPre_overlap_false` pins the consequence as a theorem — at overlapping
bases the precondition is `sepFalse`, so the triple is vacuous there rather
than wrong — and `§5` exhibits a *satisfying* state, so it is not vacuous at
the disjoint instance either.

In the growth case the ranges are disjoint by construction: `mopAlloc` carves
the new block out of `avail hp _`, which owns nothing below `hp`
(`avail_owns_nothing_below`), and the live block is below it.

## Touched-only costs

The loop charges the live prefix `n`, never the capacity: `n` is `se - sp`,
supplied by the caller, and nothing in `blitCost` mentions `xs.length` or
`zs.length`.  An `O(capacity)` sweep here would be an `n²` in every consumer
that grows repeatedly.

## Judgment calls

**D-A4a — disjointness is ownership, not arithmetic.**  Above.

**D-A4b — the measure is `(k, v)`: iterations remaining, *and* the temporary's
current value.**  `ArrayFill.lean`'s loop needs no temporary; ours reads into
`t` and writes out of it, so `t`'s value changes every iteration and the
invariant has to say what it is.  Making it existential (`junkCell t`) inside
the invariant would hide a conjunct from the frame inferencer, which matches
conjuncts syntactically.  Instead the measure is `ℕ × Val` with the
well-founded relation `InvImage (·<·) Prod.fst` — `while_triple` takes an
arbitrary `τ` and an arbitrary well-founded `r`, so this costs nothing — and
`t ↦ᵥ v` is an ordinary conjunct.  The existential appears exactly once, in
the *postcondition*, where the exit value is genuinely unknown; `blitPost_eq`
records that it is `junkCell t`, the `Sepref` idiom for a dead temporary.

**D-A4c — the registered rule is a `mop`, not an `irWhileIT`.**  The abstract
side of `hnr_mop_blit` is `mopBlit`, a `consume (returnT …)` — `hnr_mop_alloc`'s
idiom — rather than a loop combinator.  The copy is *atomic at the abstract
level*: a caller who wants the copied list does not want to reason about a
loop, and the ESOP'21 discipline is precisely that the loop is the
implementation.  This also sidesteps the `irWhileIT` invariant hazard recorded
at ledger **E20/E22**: `irWhileIT_of_not_inv` makes a failed invariant equal
`NRest.fail`, the *top* of the order, so strengthening an `irWhileIT`
invariant enlarges the spec and weakens every `hnRefine` beneath it.  There is
no `irWhileIT` here, so there is no invariant to get backwards; the real
invariant is the seam hypothesis `n ≤ xs.length`, `n ≤ zs.length` on the rule.

**D-A4d — registration (ledger E29).**  `hnr_mop_blit` **is** registered in
`sepref_fr_rules`.  A copy loop is loop-interior by nature, so this is the
direction E29 warns about; it is nevertheless right, and safe, because the
program `blitProg` is *closed and allocation-free* — it is a `while` over
`aget`/`aset`/`add` on `heapName` and five caller-supplied cells, and it
neither mentions `hpName` nor contains `allocProg`.  `blitProg_pinned` pins
the emitted term by kernel computation, so synthesis cannot use this rule to
place an allocation inside a loop: there is no allocation in it to place.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## 1. The copied list

`hblit dst src n` is `dst` with its first `n` entries overwritten by the first
`n` of `src`.  Three facts are all the loop needs — its length, what one more
write does to it, and what it is at `n = 0` — exactly the three
`ArrayFill.lean` needs of `filled`. -/

/-- `dst`, with its first `n` entries replaced by the first `n` of `src`. -/
def hblit (dst src : List Val) (n : ℕ) : List Val := src.take n ++ dst.drop n

@[simp] theorem hblit_zero (dst src : List Val) : hblit dst src 0 = dst := by
  simp [hblit]

theorem hblit_length {dst src : List Val} {n : ℕ} (hs : n ≤ src.length)
    (hd : n ≤ dst.length) : (hblit dst src n).length = dst.length := by
  simp only [hblit, List.length_append, List.length_take, List.length_drop]
  omega

/-- Writing the next source entry at the next destination slot extends the
copied prefix by one — the one list fact the loop body needs. -/
theorem hblit_set {dst src : List Val} {j : ℕ} {w : Val} (hs : j < src.length)
    (hd : j < dst.length) (hw : src[j] = w) :
    (hblit dst src j).set j w = hblit dst src (j + 1) := by
  subst hw
  unfold hblit
  have hlen : (src.take j).length = j := by rw [List.length_take]; omega
  rw [List.set_append_right j src[j] (by rw [hlen])]
  have hdrop : dst.drop j = dst[j] :: dst.drop (j + 1) := (List.getElem_cons_drop hd).symm
  have htake : src.take (j + 1) = src.take j ++ [src[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hs]
    rfl
  rw [hlen, Nat.sub_self, hdrop, List.set_cons_zero, htake, List.append_assoc]
  rfl

/-- Once the whole source prefix has been copied into a fresh zero block, the
result is the prefix followed by the allocator's zeros — `arlGrow`'s buffer,
on the nose. -/
theorem hblit_replicate (src : List Val) (n k : ℕ) :
    hblit (List.replicate k 0) src n = src.take n ++ List.replicate (k - n) 0 := by
  simp [hblit, List.drop_replicate]

/-! ## 2. The program and its price -/

/-- The loop body: read, write, bump both cursors. -/
def blitBody (t si di one : String) : Com :=
  .seq (.aget t heapName si)
    (.seq (.aset heapName di t)
      (.seq (.add si si one) (.add di di one)))

/-- The copy loop: `while si < se do body`. -/
def blitProg (t si di se one : String) : Com :=
  .while (.lt (.cell si) (.cell se)) (blitBody t si di one)

/-- What one iteration costs: its guard evaluation, its read, its write, and
the two cursor bumps. -/
def blitPayload : ECost :=
  ACost.cost Currency.«while» ((1 : ℕ) : ℕ∞) +
    (ACost.cost Currency.aget ((1 : ℕ) : ℕ∞) +
      (ACost.cost Currency.aset ((1 : ℕ) : ℕ∞) +
        (ACost.cost Currency.add ((1 : ℕ) : ℕ∞) + ACost.cost Currency.add ((1 : ℕ) : ℕ∞))))

/-- The payload as five atomic credit assertions — the `fri_prepare_simps`
extension point (`ArrayFill.lean`'s judgment call D-aj), and what makes one
iteration's price visible to the solver as five conjuncts. -/
@[fri_prepare_simps] theorem credits_blitPayload :
    (¤blitPayload : Assn) =
      ¤¤Currency.«while» 1 ∗ ¤¤Currency.aget 1 ∗ ¤¤Currency.aset 1 ∗
        ¤¤Currency.add 1 ∗ ¤¤Currency.add 1 := by
  rw [blitPayload, credits_add, credits_add, credits_add, credits_add]
  rfl

/-- **The copy's exact price.**  The trailing failed guard, plus `n` payloads.
An equation, not a bound. -/
noncomputable def blitCost (n : ℕ) : ECost := irUnit Currency.«while» + n • blitPayload

/-- `n • cost c 1 = cost c n`, the one arithmetic step `blitCost_eq` needs. -/
private theorem nsmul_irUnit (c : String) (n : ℕ) :
    n • (ACost.cost c ((1 : ℕ) : ℕ∞)) = ACost.cost c ((n : ℕ) : ℕ∞) := by
  refine ACost.toFun_injective (funext fun k => ?_)
  rw [ACost.toFun_nsmul, ACost.toFun_cost, ACost.toFun_cost]
  split <;> simp [nsmul_eq_mul]

/-- **The cost vector, spelled out.**  `n + 1` guard evaluations, `n` reads,
`n` writes, `2n` increments, and nothing else. -/
theorem blitCost_eq (n : ℕ) :
    blitCost n =
      ACost.cost Currency.«while» ((n + 1 : ℕ) : ℕ∞) +
        (ACost.cost Currency.aget ((n : ℕ) : ℕ∞) +
          (ACost.cost Currency.aset ((n : ℕ) : ℕ∞) +
            ACost.cost Currency.add ((2 * n : ℕ) : ℕ∞))) := by
  rw [blitCost, blitPayload, smul_add, smul_add, smul_add, smul_add,
    nsmul_irUnit, nsmul_irUnit, nsmul_irUnit, nsmul_irUnit]
  rw [show ((2 * n : ℕ) : ℕ∞) = ((n : ℕ) : ℕ∞) + ((n : ℕ) : ℕ∞) by
    rw [← Nat.cast_add]; congr 1; omega]
  rw [← ACost.cost_add_cost, show ((n + 1 : ℕ) : ℕ∞) = ((1 : ℕ) : ℕ∞) + ((n : ℕ) : ℕ∞) by
    rw [← Nat.cast_add]; congr 1; omega]
  simp only [irUnit, Nat.cast_one, ← ACost.cost_add_cost]
  abel

/-- **The empty copy is not free.**  At `n = 0` the loop copies nothing and
pays exactly one `ir.while`: the single failed guard test.  This is the
negative control the old `arlCopyCost_zero : arlCopyCost 0 = 0` failed. -/
theorem blitCost_zero : blitCost 0 = irUnit Currency.«while» := by
  simp [blitCost]

theorem blitCost_succ (n : ℕ) : blitCost (n + 1) = blitCost n + blitPayload := by
  simp only [blitCost, succ_nsmul]
  abel

/-- …and therefore not zero.  The negative control the old
`arlCopyCost_zero : arlCopyCost 0 = 0` failed. -/
theorem blitCost_zero_ne_zero : blitCost 0 ≠ 0 := by
  rw [blitCost_zero]
  intro h
  have := congrArg (fun c => ACost.toFun c Currency.«while») h
  simp [irUnit] at this

/-! ## 3. The loop triple

The invariant at "`k` iterations still to run and the temporary holding `v`"
(judgment calls D-A4b, and `ArrayFill.lean`'s D-ag/D-ah for the shape): the
cursors are at offset `n - k`, the destination's first `n - k` entries have
been copied, and the balance carries `k` payloads. -/

/-- The loop invariant, at measure `(k, v)`. -/
def blitInv (t si di se one : String) (sp dp n : ℕ) (xs zs : List Val)
    (k : ℕ) (v : Val) : Assn :=
  ⌜k ≤ n⌝ ∗ ¤(k • blitPayload) ∗ (t ↦ᵥ v) ∗ (si ↦ᵥ (sp + (n - k))) ∗
    (di ↦ᵥ (dp + (n - k))) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
    (sp ↦ₕ xs) ∗ (dp ↦ₕ hblit zs xs (n - k))

@[fri_prepare_simps] theorem blitInv_def (t si di se one : String) (sp dp n : ℕ)
    (xs zs : List Val) (k : ℕ) (v : Val) :
    blitInv t si di se one sp dp n xs zs k v =
      (⌜k ≤ n⌝ ∗ ¤(k • blitPayload) ∗ (t ↦ᵥ v) ∗ (si ↦ᵥ (sp + (n - k))) ∗
        (di ↦ᵥ (dp + (n - k))) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
        (sp ↦ₕ xs) ∗ (dp ↦ₕ hblit zs xs (n - k))) := rfl

/-- What the loop leaves: both cursors past the copied range, the source
untouched, the destination carrying the copied prefix, no credits — and the
temporary holding *something*, which is all a dead temporary ever says. -/
def blitPost (t si di se one : String) (sp dp n : ℕ) (xs zs : List Val) : Assn :=
  ∃ᵃ v, ((t ↦ᵥ v) ∗ (si ↦ᵥ (sp + n)) ∗ (di ↦ᵥ (dp + n)) ∗ (se ↦ᵥ (sp + n)) ∗
    (one ↦ᵥ 1) ∗ (sp ↦ₕ xs) ∗ (dp ↦ₕ hblit zs xs n))

/-- …and that `something` is the `Sepref` layer's `junkCell`. -/
theorem blitPost_eq (t si di se one : String) (sp dp n : ℕ) (xs zs : List Val) :
    blitPost t si di se one sp dp n xs zs =
      (junkCell t ∗ (si ↦ᵥ (sp + n)) ∗ (di ↦ᵥ (dp + n)) ∗ (se ↦ᵥ (sp + n)) ∗
        (one ↦ᵥ 1) ∗ (sp ↦ₕ xs) ∗ (dp ↦ₕ hblit zs xs n)) := by
  rw [junkCell_def, sepEx_sepConj]
  rfl

/-! ### One iteration

Stated with every offset explicit — `m` before, `m'` after — so that the
solver's matches are syntactic.  Four `ir_frame`s: read, write, bump, bump. -/

theorem blit_step (t si di se one : String) (sp dp n : ℕ) (xs zs : List Val)
    (v w : Val) (m m' k : ℕ) (hm' : m' = m + 1) (hmk : m + k + 1 = n)
    (hxs : n ≤ xs.length) (hzs : n ≤ zs.length) (hw : xs[m]? = some w) :
    irTriple
      (¤blitPayload ∗ ¤(k • blitPayload) ∗ (t ↦ᵥ v) ∗ (si ↦ᵥ (sp + m)) ∗
        (di ↦ᵥ (dp + m)) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
        (sp ↦ₕ xs) ∗ (dp ↦ₕ hblit zs xs m))
      (blitBody t si di one)
      (¤¤Currency.«while» 1 ∗ ¤(k • blitPayload) ∗ (t ↦ᵥ w) ∗ (si ↦ᵥ (sp + m')) ∗
        (di ↦ᵥ (dp + m')) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
        (sp ↦ₕ xs) ∗ (dp ↦ₕ hblit zs xs m')) := by
  subst hm'
  have hms : m < xs.length := by omega
  have hmd : m < zs.length := by omega
  obtain ⟨hlt', hwe⟩ := List.getElem?_eq_some_iff.1 hw
  have hlend : (hblit zs xs m).length = zs.length :=
    hblit_length (by omega) (by omega)
  have hmd' : m < (hblit zs xs m).length := by rw [hlend]; exact hmd
  have hset : (hblit zs xs m).set m w = hblit zs xs (m + 1) := hblit_set hms hmd hwe
  -- read
  refine seq_triple
    (R := ¤¤Currency.aset 1 ∗ ¤¤Currency.add 1 ∗ ¤¤Currency.add 1 ∗
      ¤¤Currency.«while» 1 ∗ ¤(k • blitPayload) ∗ (t ↦ᵥ w) ∗ (si ↦ᵥ (sp + m)) ∗
      (di ↦ᵥ (dp + m)) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
      (sp ↦ₕ xs) ∗ (dp ↦ₕ hblit zs xs m)) ?_ ?_
  · ir_frame (haget_triple t si v sp m xs w hms hwe)
  -- write
  refine seq_triple
    (R := ¤¤Currency.add 1 ∗ ¤¤Currency.add 1 ∗
      ¤¤Currency.«while» 1 ∗ ¤(k • blitPayload) ∗ (t ↦ᵥ w) ∗ (si ↦ᵥ (sp + m)) ∗
      (di ↦ᵥ (dp + m)) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
      (sp ↦ₕ xs) ∗ (dp ↦ₕ (hblit zs xs m).set m w)) ?_ ?_
  · ir_frame (haset_triple di t dp m (hblit zs xs m) w hmd')
  rw [hset]
  -- bump the source cursor
  refine seq_triple
    (R := ¤¤Currency.add 1 ∗
      ¤¤Currency.«while» 1 ∗ ¤(k • blitPayload) ∗ (t ↦ᵥ w) ∗ (si ↦ᵥ (sp + m + 1)) ∗
      (di ↦ᵥ (dp + m)) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
      (sp ↦ₕ xs) ∗ (dp ↦ₕ hblit zs xs (m + 1))) ?_ ?_
  · ir_frame (binop_self_triple .add si one (sp + m) 1)
  -- bump the destination cursor
  rw [show sp + (m + 1) = sp + m + 1 by omega, show dp + (m + 1) = dp + m + 1 by omega]
  ir_frame (binop_self_triple .add di one (dp + m) 1)

/-! ### The three obligations of `while_triple` -/

/-- The guard is determined by the measure: with `k ≤ n` from the invariant's
own pure conjunct, `si < se` holds exactly when `k > 0`. -/
theorem blit_guard (t si di se one : String) (sp dp n : ℕ) (xs zs : List Val)
    (F : Assn) (p : ℕ × Val) (s : State) (cr : ECost)
    (h : irSTATE ((¤¤Currency.«while» 1 ∗
      blitInv t si di se one sp dp n xs zs p.1 p.2) ∗ F) (s, cr)) :
    (Cond.lt (.cell si) (.cell se)).eval s = some (decide (0 < p.1)) := by
  have hkn : p.1 ≤ n := pure_of_frame h (by fri)
  have hi : s.vars si = some (sp + (n - p.1)) := ptoVar_of_frame h (by fri)
  have he : s.vars se = some (sp + n) := ptoVar_of_frame h (by fri)
  have hdec : decide (sp + (n - p.1) < sp + n) = decide (0 < p.1) := by
    rcases Nat.eq_zero_or_pos p.1 with hz | hpos
    · simp [hz]
    · have h1 : sp + (n - p.1) < sp + n := by omega
      simp [h1, hpos]
  simp only [Cond.eval_lt, Operand.eval_cell, hi, he, Option.bind_some, Option.map_some, hdec]

/-- One iteration, as `while_triple` asks for it: pay the body, hand back the
next guard's credit, and land at a smaller measure. -/
theorem blit_body_triple (t si di se one : String) (sp dp n : ℕ) (xs zs : List Val)
    (hxs : n ≤ xs.length) (hzs : n ≤ zs.length) (p : ℕ × Val)
    (hk : decide (0 < p.1) = true) :
    irTriple (blitInv t si di se one sp dp n xs zs p.1 p.2) (blitBody t si di one)
      (∃ᵃ q, ⌜(q : ℕ × Val).1 < p.1⌝ ∗ ¤¤Currency.«while» 1 ∗
        blitInv t si di se one sp dp n xs zs q.1 q.2) := by
  obtain ⟨k, v⟩ := p
  have hk0 : 0 < k := of_decide_eq_true hk
  refine irTriple_pure (fun hkn => ?_)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hlt : n - (j + 1) < xs.length := by omega
  obtain ⟨w, hw⟩ : ∃ w, xs[n - (j + 1)]? = some w :=
    ⟨xs[n - (j + 1)], List.getElem?_eq_getElem hlt⟩
  refine irTriple_ex (β := ℕ × Val) (j, w) ?_
  ir_frame (blit_step t si di se one sp dp n xs zs v w (n - (j + 1)) (n - j) j
    (by omega) (by omega) hxs hzs hw)

/-- On exit the measure is zero, so both cursors are past the range and the
whole prefix has been copied. -/
theorem blit_exit (t si di se one : String) (sp dp n : ℕ) (xs zs : List Val)
    (p : ℕ × Val) (hk : decide (0 < p.1) = false) :
    blitInv t si di se one sp dp n xs zs p.1 p.2 ⊢
      blitPost t si di se one sp dp n xs zs := by
  obtain ⟨k, v⟩ := p
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · simp [h] at hk
  subst hk0
  have hent : blitInv t si di se one sp dp n xs zs 0 v ⊢
      ((t ↦ᵥ v) ∗ (si ↦ᵥ (sp + n)) ∗ (di ↦ᵥ (dp + n)) ∗ (se ↦ᵥ (sp + n)) ∗
        (one ↦ᵥ 1) ∗ (sp ↦ₕ xs) ∗ (dp ↦ₕ hblit zs xs n)) := by
    simp only [blitInv_def, Nat.sub_zero]
    fri
  exact fun h hh => ⟨v, hent h hh⟩

/-- The loop: `n` iterations, `n` payloads, the measure is the number of
iterations still to run paired with the temporary's value (D-A4b). -/
theorem blit_loop (t si di se one : String) (sp dp n : ℕ) (xs zs : List Val)
    (hxs : n ≤ xs.length) (hzs : n ≤ zs.length) (v₀ : Val) :
    irTriple (¤¤Currency.«while» 1 ∗ blitInv t si di se one sp dp n xs zs n v₀)
      (blitProg t si di se one) (blitPost t si di se one sp dp n xs zs) :=
  while_triple (r := fun a b : ℕ × Val => a.1 < b.1)
    (InvImage.wf Prod.fst Nat.lt_wfRel.wf)
    (blit_guard t si di se one sp dp n xs zs)
    (blit_body_triple t si di se one sp dp n xs zs hxs hzs)
    (blit_exit t si di se one sp dp n xs zs) (n, v₀)

/-- **The copy triple.**  Own the two disjoint ranges, the temporary, the two
cursors at their bases, the bound cell and the unit cell, and `blitCost n`
credits; get back the destination with the first `n` source entries copied
into it, the source untouched, and no credits left over.  The price is an
equation (`blitCost_eq`), not a bound. -/
theorem blit_triple (t si di se one : String) (sp dp n : ℕ) (xs zs : List Val)
    (hxs : n ≤ xs.length) (hzs : n ≤ zs.length) (v₀ : Val) :
    irTriple
      (¤(blitCost n) ∗ (t ↦ᵥ v₀) ∗ (si ↦ᵥ sp) ∗ (di ↦ᵥ dp) ∗ (se ↦ᵥ (sp + n)) ∗
        (one ↦ᵥ 1) ∗ (sp ↦ₕ xs) ∗ (dp ↦ₕ zs))
      (blitProg t si di se one) (blitPost t si di se one sp dp n xs zs) := by
  have h := blit_loop t si di se one sp dp n xs zs hxs hzs v₀
  simp only [blitInv_def, Nat.sub_self, Nat.add_zero, hblit_zero] at h
  rw [blitCost, credits_add, ← costCredits_one]
  exact irTriple_frame h (by fri) (by fri)

/-- The same in the source's garbage-collecting form. -/
theorem blit_rule (t si di se one : String) (sp dp n : ℕ) (xs zs : List Val)
    (hxs : n ≤ xs.length) (hzs : n ≤ zs.length) (v₀ : Val) :
    irHtriple
      (¤(blitCost n) ∗ (t ↦ᵥ v₀) ∗ (si ↦ᵥ sp) ∗ (di ↦ᵥ dp) ∗ (se ↦ᵥ (sp + n)) ∗
        (one ↦ᵥ 1) ∗ (sp ↦ₕ xs) ∗ (dp ↦ₕ zs))
      (blitProg t si di se one) (blitPost t si di se one sp dp n xs zs) :=
  (blit_triple t si di se one sp dp n xs zs hxs hzs v₀).gc

/-! ## 4. The mop and the registered rule

`mopBlit` is the abstract copy: return the copied list, pay the loop's exact
price.  There is **no `assert`** — the bounds are ownership facts the caller
already supplies as `sp ↦ₕ xs` and `dp ↦ₕ zs`, exactly as `mopAlloc` has no
assert because the space is ownership (judgment call D-A2). -/

/-- **The abstract copy.**  `mop_array_blit`, at this leaf. -/
noncomputable def mopBlit (dst src : List Val) (n : ℕ) : NRest (List Val) ECost :=
  NRest.consume (NRest.returnT (hblit dst src n)) (blitCost n)

theorem mopBlit_def (dst src : List Val) (n : ℕ) :
    mopBlit dst src n = NRest.consume (NRest.returnT (hblit dst src n)) (blitCost n) := rfl

/-- Copying never fails.  As with `mopAlloc`, that is the point: it is what
lets the operation above it be restated unconditionally. -/
theorem mopBlit_nofail (dst src : List Val) (n : ℕ) : (mopBlit dst src n).nofailT :=
  nofailT_consume_iff.2 (NRest.nofailT_returnT _)

/-- The triple in the shape `hnRefineI_spect` consumes: the price on the
abstract side, the destination block in the judgment's result slot at the
base-pointer cell `dc`.  `dc` is *not* the cursor `di`: the cursor moves, so
the block's base has to be remembered somewhere that does not. -/
theorem blit_junk_rule (t si di se one dc : String) (sp dp n : ℕ) (xs zs : List Val)
    (hxs : n ≤ xs.length) (hzs : n ≤ zs.length) :
    irHtriple (¤(blitCost n) ∗
        (junkCell t ∗ (si ↦ᵥ sp) ∗ (di ↦ᵥ dp) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
          (sp ↦ₕ xs) ∗ (dc ↦ᵥ dp) ∗ (dp ↦ₕ zs)))
      (blitProg t si di se one)
      ((junkCell t ∗ (si ↦ᵥ (sp + n)) ∗ (di ↦ᵥ (dp + n)) ∗ (se ↦ᵥ (sp + n)) ∗
          (one ↦ᵥ 1) ∗ (sp ↦ₕ xs)) ∗ heapBlockAssn (hblit zs xs n) dc) := by
  have e₁ : (¤(blitCost n) ∗
      (junkCell t ∗ (si ↦ᵥ sp) ∗ (di ↦ᵥ dp) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
        (sp ↦ₕ xs) ∗ (dc ↦ᵥ dp) ∗ (dp ↦ₕ zs)))
      = (junkCell t ∗ (¤(blitCost n) ∗ (si ↦ᵥ sp) ∗ (di ↦ᵥ dp) ∗ (se ↦ᵥ (sp + n)) ∗
        (one ↦ᵥ 1) ∗ (sp ↦ₕ xs) ∗ (dc ↦ᵥ dp) ∗ (dp ↦ₕ zs))) := by
    ac_rfl
  rw [e₁]
  refine irHtriple_junk fun v₀ => ?_
  refine cons_rule (irTriple.gc (frame_rule (wp := wp) (α := irα) (dc ↦ᵥ dp)
      (blit_triple t si di se one sp dp n xs zs hxs hzs v₀)))
    (fun s hs => ?_) (fun _ s hs => ?_)
  · revert hs
    have e₂ : ((t ↦ᵥ v₀) ∗ (¤(blitCost n) ∗ (si ↦ᵥ sp) ∗ (di ↦ᵥ dp) ∗ (se ↦ᵥ (sp + n)) ∗
        (one ↦ᵥ 1) ∗ (sp ↦ₕ xs) ∗ (dc ↦ᵥ dp) ∗ (dp ↦ₕ zs)))
        = ((¤(blitCost n) ∗ (t ↦ᵥ v₀) ∗ (si ↦ᵥ sp) ∗ (di ↦ᵥ dp) ∗ (se ↦ᵥ (sp + n)) ∗
          (one ↦ᵥ 1) ∗ (sp ↦ₕ xs) ∗ (dp ↦ₕ zs)) ∗ (dc ↦ᵥ dp)) := by
      ac_rfl
    rw [e₂]
    exact fun h => h
  · revert hs
    rw [blitPost_eq]
    have e₃ : ((junkCell t ∗ (si ↦ᵥ (sp + n)) ∗ (di ↦ᵥ (dp + n)) ∗ (se ↦ᵥ (sp + n)) ∗
        (one ↦ᵥ 1) ∗ (sp ↦ₕ xs) ∗ (dp ↦ₕ hblit zs xs n)) ∗ (dc ↦ᵥ dp))
        = ((junkCell t ∗ (si ↦ᵥ (sp + n)) ∗ (di ↦ᵥ (dp + n)) ∗ (se ↦ᵥ (sp + n)) ∗
          (one ↦ᵥ 1) ∗ (sp ↦ₕ xs)) ∗ ((dc ↦ᵥ dp) ∗ (dp ↦ₕ hblit zs xs n))) := by
      ac_rfl
    rw [e₃]
    have hblk : ((dc ↦ᵥ dp) ∗ (dp ↦ₕ hblit zs xs n))
        ⊢ heapBlockAssn (hblit zs xs n) dc := fun _ hh => ⟨dp, hh⟩
    exact conj_entails_mono (sepConj_mono_right hblk) (entails_refl GC) s

/-- **The registered rule.**  `sepref_synth` can consume this: an `hnRefine`
over `irSTATE` like every other rule in `Sepref/IrOps.lean`, in
`hnr_mop_alloc`'s idiom.  The source range and the two cursors survive in the
context; the destination block is delivered in the result slot at `dc`
(judgment calls D-A4c, D-A4d). -/
@[sepref_fr_rules]
theorem hnr_mop_blit (t si di se one dc : String) (sp dp n : ℕ) (xs zs : List Val)
    (hxs : n ≤ xs.length) (hzs : n ≤ zs.length) :
    hnRefine
      (junkCell t ∗ (si ↦ᵥ sp) ∗ (di ↦ᵥ dp) ∗ (se ↦ᵥ (sp + n)) ∗ (one ↦ᵥ 1) ∗
        (sp ↦ₕ xs) ∗ (dc ↦ᵥ dp) ∗ (dp ↦ₕ zs))
      (blitProg t si di se one)
      (junkCell t ∗ (si ↦ᵥ (sp + n)) ∗ (di ↦ᵥ (dp + n)) ∗ (se ↦ᵥ (sp + n)) ∗
        (one ↦ᵥ 1) ∗ (sp ↦ₕ xs))
      dc heapBlockAssn (mopBlit zs xs n) :=
  hnRefineI_spect (blit_junk_rule t si di se one dc sp dp n xs zs hxs hzs)

/-! ## 5. Gates and negative controls (falsification law, clause 2)

This loop is *authored* — the source's `array_copy` is an LLVM intrinsic, not
a while loop over two `ll_range`s — so it is not exempt.  Four controls, and
each of them bites. -/

/-- **The emitted program, pinned.**  Nothing here is an allocation: no
`hpName`, no `allocProg`, so registering `hnr_mop_blit` cannot let synthesis
place an allocation inside a loop (judgment call D-A4d). -/
theorem blitProg_pinned (t si di se one : String) :
    blitProg t si di se one =
      Com.while (.lt (.cell si) (.cell se))
        (.seq (.aget t heapName si)
          (.seq (.aset heapName di t)
            (.seq (.binop .add si si one) (.binop .add di di one)))) := rfl

#guard blitProg "t" "si" "di" "se" "one" =
  Com.while (.lt (.cell "si") (.cell "se"))
    (.seq (.aget "t" heapName "si")
      (.seq (.aset heapName "di" "t")
        (.seq (.binop .add "si" "si" "one") (.binop .add "di" "di" "one"))))

/-- **Negative control 1 — overlapping ranges are not derivable.**  The
precondition owns both ranges, so at overlapping bases it is `sepFalse` and
nothing at all can satisfy it.  This is the disjointness premise, and it is
the separating conjunction (judgment call D-A4a). -/
theorem blitPre_overlap_false {sp dp : ℕ} {xs zs : List Val} (hle : sp ≤ dp)
    (h1 : dp < sp + xs.length) (h2 : 0 < zs.length) :
    ((sp ↦ₕ xs) ∗ (dp ↦ₕ zs)) = (sepFalse : Assn) :=
  ptoH_sepConj_overlap hle h1 h2

/-- …and at the shape growth would hit if the allocator ever returned the
block it was copying from. -/
theorem blitPre_self_false (p : ℕ) (v w : Val) (xs zs : List Val) :
    ((p ↦ₕ (v :: xs)) ∗ (p ↦ₕ (w :: zs))) = (sepFalse : Assn) :=
  ptoH_sepConj_self p v w xs zs

namespace BlitGate

open Lax13Proofs.Refine.Ir.Gate (costVector readVars readArrs)
open Plausible

/-! ### The list level, by computation -/

-- The copied prefix really is the source prefix, and the tail is untouched.
#guard hblit [0, 0, 0, 0] [7, 8, 9] 3 = [7, 8, 9, 0]
#guard hblit [1, 2, 3, 4] [7, 8, 9] 2 = [7, 8, 3, 4]
#guard hblit [1, 2, 3, 4] [7, 8, 9] 0 = [1, 2, 3, 4]

-- Negative control: copying the wrong count is not the copy.
#guard hblit [0, 0, 0, 0] [7, 8, 9] 2 ≠ hblit [0, 0, 0, 0] [7, 8, 9] 3

-- The one-more-write law, sampled at every cut point.
#test ∀ m : ℕ, (hblit [1, 2, 3, 4] [7, 8, 9] (m % 3)).set (m % 3)
  ([7, 8, 9] : List Val)[m % 3]! = hblit [1, 2, 3, 4] [7, 8, 9] (m % 3 + 1)

/-! ### The program level, end to end

`sp = 0` holding `[7, 8, 9]`, `dp = 4` holding `[0, 0, 0, 0]`, `n = 3`. -/

/-- The heap: the source block at `[0, 3)`, a gap, the destination at
`[4, 8)`. -/
def gateHeap : List Val := [7, 8, 9, 0, 0, 0, 0, 0]

def blitDemoState : State :=
  State.ofPairs [("t", 0), ("si", 0), ("di", 4), ("se", 3), ("one", 1)]
    [(heapName, gateHeap)]

def blitDemoProg : Com := blitProg "t" "si" "di" "se" "one"

def blitDemoOut : State × Cost :=
  (evalFuel 60 blitDemoProg blitDemoState).getD (blitDemoState, 0)

theorem blitDemo_evalFuel : evalFuel 60 blitDemoProg blitDemoState = some blitDemoOut := rfl

theorem blitDemo_bigStep : BigStep blitDemoProg blitDemoState blitDemoOut.1 blitDemoOut.2 :=
  bigStep_of_evalFuel blitDemo_evalFuel

-- The destination now holds the source prefix; the source is untouched.
#guard readArrs blitDemoOut.1 [heapName] = [(heapName, some [7, 8, 9, 0, 7, 8, 9, 0])]

-- **The differential test.**  What the loop leaves in `[4, 8)` is exactly
-- what `hblit` says it should be.
#guard ((readArrs blitDemoOut.1 [heapName]).head?.map fun r => (r.2.getD []).drop 4)
  = some (hblit [0, 0, 0, 0] [7, 8, 9] 3)

-- Both cursors are past the range.
#guard readVars blitDemoOut.1 ["si", "di", "se", "one"]
  = [("si", some 3), ("di", some 7), ("se", some 3), ("one", some 1)]

-- **The cost vector.**  Four guard evaluations for three iterations, three
-- reads, three writes, six increments, and nothing else.
#guard costVector blitDemoOut.2 =
  [("ir.skip", 0), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 3), ("ir.aset", 3),
   ("ir.ite", 0), ("ir.while", 4), ("ir.add", 6), ("ir.sub", 0), ("ir.mul", 0),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-! ### The cost as a function of `n`

`blitCost_eq` says `(n+1)·while + n·aget + n·aset + 2n·add`.  Wave A's
`evalFuel` twin agrees with `BigStep` in both directions, so a `Plausible`
check on the twin is a check on the semantics — and these are the checks that
would have caught `arlCopyCost`'s two missing currencies. -/

def blitState (n : ℕ) : State :=
  State.ofPairs [("t", 0), ("si", 0), ("di", n), ("se", n), ("one", 1)]
    [(heapName, List.replicate n 5 ++ List.replicate n 0)]

def blitFuel (n : ℕ) : ℕ := 6 * n + 10

#test ∀ m : ℕ, ((evalFuel (blitFuel (m % 6)) (blitProg "t" "si" "di" "se" "one")
  (blitState (m % 6))).map fun r => r.1.arrs heapName)
  = some (some (List.replicate (m % 6) 5 ++ List.replicate (m % 6) 5))

#test ∀ m : ℕ, ((evalFuel (blitFuel (m % 6)) (blitProg "t" "si" "di" "se" "one")
  (blitState (m % 6))).map fun r => r.2.toFun Currency.«while») = some (m % 6 + 1)

#test ∀ m : ℕ, ((evalFuel (blitFuel (m % 6)) (blitProg "t" "si" "di" "se" "one")
  (blitState (m % 6))).map fun r => r.2.toFun Currency.aget) = some (m % 6)

#test ∀ m : ℕ, ((evalFuel (blitFuel (m % 6)) (blitProg "t" "si" "di" "se" "one")
  (blitState (m % 6))).map fun r => r.2.toFun Currency.aset) = some (m % 6)

#test ∀ m : ℕ, ((evalFuel (blitFuel (m % 6)) (blitProg "t" "si" "di" "se" "one")
  (blitState (m % 6))).map fun r => r.2.toFun Currency.add) = some (2 * (m % 6))

/-! ### Negative controls that bite -/

-- **Control 2 — the `ir.while` unit is not optional.**  Three iterations do
-- not pay three guard credits, and by determinism no derivation does.
#guard ¬ (blitDemoOut.2.toFun Currency.«while» = 3)

theorem blit_no_wrong_while {s' : State} {κ : Cost}
    (h : BigStep blitDemoProg blitDemoState s' κ) : κ.toFun Currency.«while» ≠ 3 := by
  obtain ⟨-, rfl⟩ := BigStep.unique blitDemo_bigStep h
  decide

-- **Control 3 — the `ir.add` units are not optional.**  The old
-- `arlCopyCost` charged none; the loop pays two per iteration.
#guard ¬ (blitDemoOut.2.toFun Currency.add = 0)

theorem blit_no_free_add {s' : State} {κ : Cost}
    (h : BigStep blitDemoProg blitDemoState s' κ) : κ.toFun Currency.add ≠ 0 := by
  obtain ⟨-, rfl⟩ := BigStep.unique blitDemo_bigStep h
  decide

-- **Control 4 — the empty copy is not free.**  `n = 0` copies nothing and
-- still pays the one failed guard.
#guard costVector ((evalFuel 10 (blitProg "t" "si" "di" "se" "one")
    (blitState 0)).getD (blitState 0, 0)).2 =
  [("ir.skip", 0), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 0), ("ir.aset", 0),
   ("ir.ite", 0), ("ir.while", 1), ("ir.add", 0), ("ir.sub", 0), ("ir.mul", 0),
   ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0), ("ir.shiftl", 0),
   ("ir.shiftr", 0)]

/-- **Control 5 — the triple is not derivable with one payload too few.**
Drop a single iteration's credits and the invariant cannot hand the last
iteration what it does not hold. -/
example : True := by
  fail_if_success
    (have : irTriple
        (¤(irUnit Currency.«while» + (2 : ℕ) • blitPayload) ∗ ("t" ↦ᵥ 0) ∗
          ("si" ↦ᵥ 0) ∗ ("di" ↦ᵥ 4) ∗ ("se" ↦ᵥ (0 + 3)) ∗ ("one" ↦ᵥ 1) ∗
          ((0 : ℕ) ↦ₕ [7, 8, 9]) ∗ ((4 : ℕ) ↦ₕ [0, 0, 0, 0]))
        (blitProg "t" "si" "di" "se" "one")
        (blitPost "t" "si" "di" "se" "one" 0 4 3 [7, 8, 9] [0, 0, 0, 0]) := by
      exact blit_triple "t" "si" "di" "se" "one" 0 4 3 [7, 8, 9] [0, 0, 0, 0]
        (by simp) (by simp) 0)
  trivial

/-- **Non-vacuity.**  The two overlap controls above say the precondition is
`sepFalse` when the ranges overlap; this says it is *not* `sepFalse` when they
do not.  Without it every theorem in this file could be vacuous. -/
def blitGateFrame : Assn :=
  EXACT ((vcells blitDemoState, acells blitDemoState,
    ((hcells blitDemoState).eraseRange 0 3).eraseRange 4 4), 0)

theorem blitGate_ranges_hold :
    irSTATE (((0 : ℕ) ↦ₕ [7, 8, 9]) ∗ (((4 : ℕ) ↦ₕ [0, 0, 0, 0]) ∗ blitGateFrame))
      (blitDemoState, 0) := by
  refine ptoH_sepConj_iff.2 ⟨?_, ?_⟩
  · intro j hj
    have hj3 : j < 3 := by simpa using hj
    interval_cases j <;> rfl
  · refine ptoH_sepConj_iff.2 ⟨?_, ?_⟩
    · intro j hj
      have hj4 : j < 4 := by simpa using hj
      interval_cases j <;> rfl
    · rfl

end BlitGate

/-! ## 6. Axiom hygiene -/

/-- info: 'Lax13Proofs.Refine.Sepref.blit_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blit_triple

/-- info: 'Lax13Proofs.Refine.Sepref.hnr_mop_blit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_blit

/-- info: 'Lax13Proofs.Refine.Sepref.blitCost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blitCost_eq

end Lax13Proofs.Refine.Sepref
