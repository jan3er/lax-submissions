import Lax13Proofs.Refine.Iicf.ExercisesA

/-!
# Recursive per-arena passes over a trail array — deviation D5's exercise

`Iicf/IicfTrailArray.lean` built the touched-only array and proved its
characteristic theorem (`treset_cost_touched_only`: reset's price is a
function of the touch counter alone). `Iicf/ExercisesA.lean` §2 ran it
*straight-line* — two rounds, hand-written. Neither exercised the shape
the ND-MC C0 time bound actually stands on, and D5 asks for it: a
**driver that recurses over arenas**, running one pass per arena into a
single size-`n` scratch structure and restoring it between arenas.

That shape is where the `touched-only-costs` discipline bites. The naive
driver re-zeroes the whole scratch array per arena and pays
`n · (number of arenas)`; on ND-MC's cluster decomposition that is `n²`
and the sublinear headline is gone. The trail array charges the reset at
the number of *touched cells*, so the same driver pays
`Σ_arena |active set|` — and that sum is what the abstract algorithm
already budgets.

## The program

`clusterLoad`, smallest honest instance. The arenas are a CSR-style
block structure `off`/`mem` over the carrier `0…n-1`: arena `a` owns the
slots `off[a] … off[a+1] - 1`, and `mem[k]` is the carrier index that
slot `k` activates. The driver is

```
a := 0; acc := 0
while a < m:                       -- outer: one pass per arena
  k := off[a]; kend := off[a+1]
  while k < kend:                  -- inner: the arena's active set
    u := mem[k]
    w := A[u]                      -- tget: read what is there
    A[u] := w + 1                  -- tset: write, and push u on the trail
    acc := acc + w                 -- the *use* of the loaded array
    k := k + 1
  treset A                         -- pops exactly the writes of this arena
  a := a + 1
```

so each arena loads its active set into the shared scratch, reads it,
and hands it back clean. `acc` ends up counting, over all arenas, the
in-arena repeats — a use that genuinely reads the loaded contents, and
one whose answer is wrong if the reset does not actually clean up.

Both loops go through `sepref_synth` in one command (§4). Nothing below
writes a frame clause, a permutation, or an `Ir.Com` by hand.

## The acceptance criterion

§6. The cashed cost of the whole driver is

```
clusterCost off a j = (sizesSum off a j) • touchUnit + j • arenaConst + irUnit ir.while
```

— linear in the **total number of touches** `Σ_arena |arena|`, plus a
constant per arena, plus one. `n` does not occur: `clusterCost` does not
even take `n` as an argument, which is `treset_cost_touched_only`'s
"note what it is a function of" one level up. Read at a single currency
the statement is sharpest:
`(clusterCost off a j).toFun ir.aset = 3 * sizesSum off a j` — the array
writes are *exactly* three per touch, with no `n` and no arena count in
the formula at all.

The one `O(n)` charge the discipline allows is the initial fill, paid
once: `clusterTotalCost n off m = tinitCost n + clusterCost off 0 m`, and
`n` occurs in the first summand and nowhere else (§6.4).

The negative control (§7.3) is a proof, not an example: the naive
per-arena re-zero admits **no** bound of the touched-only shape
`c₁ · touches + c₂ · arenas + c₃`, for any constants whatsoever.

## Judgment calls (R0/D-c…)

**R0/D-c — the trail array is a component of *both* loop states, not of
the frame.** It is tempting to leave it in the outer loop's frame: it is
`(replicate n dflt, 0)` at entry to every arena and again at exit, so
the frame really is restored. But `hnr_while`'s body post *is* the loop
frame, and the body mutates the array in between — P4/D-ec's rule, which
is about the body, not about the endpoints. So the outer state is
`(a, acc, trail)` at `("a", "acc", ("A", "T", "t"))` and the inner state
is `(k, acc, trail)` at `("k0", "acc", ("A", "T", "t"))`, the two sharing
the accumulator's cell and the array's three cells exactly as
`BfsQSynth`'s drain and scan loops share `"dist"`, `"q"` and `"tl"`. The
value proof then carries `s.2.2 = (List.replicate n dflt, 0)` as an
explicit hypothesis of the outer loop lemma, preserved because
`mop_treset` returns that constant — which is the mathematical content
of "the arenas do not interfere".

**R0/D-d — the write value is `w + 1`, not the literal `1`, and that is
forced.** `hnr_mop_tset` asks the caller for `hnCtxt natAssn v V` *and*
`hnCtxt natAssn 1 one` as two conjuncts. With `v = 1` those are the same
assertion, the separation logic is precise, and a precondition owning one
cell holding `1` cannot supply both. Writing the incremented value read
back a moment earlier is the natural program anyway (it is what makes
`acc` a repeat count), and its cell is distinct from `"one"` by
construction. Fallback: own two constant cells both holding `1`.

**R0/D-e — two in-place scalar ops are declared here, for P7/D-bb's
reason.** `acc := acc + w` and `k := k + 1` are components of loop states,
so the loop rule fixes their cells; `hnr_mop_binop` (junk destination) is
tried before `hnr_mop_binop_self` and does not backtrack, and at both
points a scratch cell is free. `mopSucc` (BfsQSynth's, restated here so
this file does not import the BFS package) and `mopAddIn` are the same
fix: a distinct abstract operation with exactly one rule, the in-place
one. Note the contrast with `a1 := a + 1` in the outer body, which is a
*fresh temporary* and is therefore left as a plain `mopBinop` — the
pipeline routes it to a scratch cell, which is what it should do.

**R0/D-f — the reset's two scratch cells are the inner pass's.** The
synthesized program is `resetCom "A" "T" "t" "u" "w" "D" "one"`: the
allocator reused `"u"` and `"w"`, dead by then, as the pop loop's index
and slot temporaries. Nothing asked it to; it is what the frame matcher
found. Recorded because a reader counting registers should not expect two
more.

**R0/D-g — the touch counter counts *writes*, so a repeated index inside
one arena is charged twice.** `IicfTrailArray`'s P6/D-p: the push is
unconditional. The falsification block (§2) pins this rather than
papering over it — arena 1 of the sample writes slot `4` twice and pops
three times for two distinct cells — and it is why `ArenaOk` requires
`|arena| ≤ n` rather than `|{distinct cells}| ≤ n`. It is also why
`sizesSum` (a sum of arena *widths*) is the right resource: it is an
upper bound for distinct cells and the exact write count.
-/

namespace Lax13Proofs.Refine

namespace TrailRecursion

open Sepref Sepref.Iicf Ir NRest

/-- The state shape shared by both loops: a counter, the accumulator, and
the trail array's abstract value. -/
abbrev TSt : Type := ℕ × ℕ × (List ℕ × ℕ)

/-! ## 1. Two in-place scalar operations (R0/D-e) -/

/-- `x := x + 1`, as an operation of its own so that the operator phase
cannot route it through a scratch cell (P7/D-bb). -/
noncomputable def mopSucc (m : ℕ) : NRest ℕ ECost := mopBinop .add m 1

theorem mopSucc_eq (m : ℕ) : mopSucc m = mopBinop .add m 1 := rfl

@[sepref_fr_rules]
theorem hnr_mop_succ (x z : String) (m : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn 1 z) (.binop .add x x z)
      (hnCtxt natAssn 1 z) x natAssn (mopSucc m) := by
  rw [mopSucc_eq]; exact hnr_mop_binop_self .add x z m 1

attribute [irreducible] mopSucc

/-- `x := x + z`, likewise. -/
noncomputable def mopAddIn (m w : ℕ) : NRest ℕ ECost := mopBinop .add m w

theorem mopAddIn_eq (m w : ℕ) : mopAddIn m w = mopBinop .add m w := rfl

@[sepref_fr_rules]
theorem hnr_mop_addIn (x z : String) (m w : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn w z) (.binop .add x x z)
      (hnCtxt natAssn w z) x natAssn (mopAddIn m w) := by
  rw [mopAddIn_eq]; exact hnr_mop_binop_self .add x z m w

attribute [irreducible] mopAddIn

/-! ## 2. Refute before prove

The driver is *run* before anything is proved about it, on a concrete
block structure with a deliberately repeated index. The functions below
are not an independent specification: `innerStep` and `arenaStep` are
exactly what §5's value lemmas prove the abstract loop bodies equal to,
so a `#guard` here is a `#guard` about the abstract program. -/

/-- The width of arena `a`. -/
def arenaSize (off : List ℕ) (a : ℕ) : ℕ := off[a + 1]! - off[a]!

/-- The total number of *touches* — writes, not distinct cells (R0/D-g) —
of the arenas `a, a+1, …, a+j-1`. -/
def sizesSum (off : List ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | a, j + 1 => arenaSize off a + sizesSum off (a + 1) j

/-- One slot of one arena: read the cell the slot activates, accumulate
what was there, write it back incremented (which pushes the cell on the
trail and spends one unit of touch budget), advance. -/
def innerStep (mem : List ℕ) (s : TSt) : TSt :=
  (s.1 + 1, s.2.1 + s.2.2.1[mem[s.1]!]!,
    (s.2.2.1.set mem[s.1]! (s.2.2.1[mem[s.1]!]! + 1), s.2.2.2 + 1))

/-- `j` slots of one arena. -/
def innerRun (mem : List ℕ) : ℕ → TSt → TSt
  | 0, s => s
  | j + 1, s => innerRun mem j (innerStep mem s)

/-- One whole arena: the inner pass over its slots, then the reset — the
array back to all-default and the touch budget back to full. -/
def arenaStep (dflt n : ℕ) (off mem : List ℕ) (s : TSt) : TSt :=
  (s.1 + 1, (innerRun mem (arenaSize off s.1) (off[s.1]!, s.2.1, s.2.2)).2.1,
    (List.replicate n dflt, 0))

/-- `j` arenas. -/
def arenaRun (dflt n : ℕ) (off mem : List ℕ) : ℕ → TSt → TSt
  | 0, s => s
  | j + 1, s => arenaRun dflt n off mem j (arenaStep dflt n off mem s)

/-! ### The sample

Carrier `n = 6`, three arenas: `{1, 3}`, `{4, 4, 1}` and `{3}`. The
middle one activates slot `4` **twice** — the repeat that separates
"writes" from "distinct cells" — and it also revisits slot `1`, which
arena `0` already touched, so the reset is load-bearing for the answer. -/

def sOff : List ℕ := [0, 2, 5, 6]

def sMem : List ℕ := [1, 3, 4, 4, 1, 3]

/-- The driver's entry state: arena `0`, empty accumulator, a clean
length-6 array. -/
def sInit : TSt := (0, 0, (List.replicate 6 0, 0))

def sOut : TSt := arenaRun 0 6 sOff sMem 3 sInit

-- The three arena widths, and their sum — the total touch count.
#guard arenaSize sOff 0 = 2
#guard arenaSize sOff 1 = 3
#guard arenaSize sOff 2 = 1
#guard sizesSum sOff 0 3 = 6
#guard sizesSum sOff 0 3 = sMem.length

-- All three arenas run; the accumulator sees exactly the one repeat.
#guard sOut.1 = 3
#guard sOut.2.1 = 1
-- …and the scratch array is handed back clean, which is the whole point
-- of the reset: the next arena starts from all-default.
#guard sOut.2.2 = (List.replicate 6 0, 0)

-- The intermediate states, arena by arena: after arena 0 the array is
-- clean again and the accumulator is still 0; the repeat is charged in
-- arena 1.
#guard (arenaRun 0 6 sOff sMem 1 sInit) = (1, 0, (List.replicate 6 0, 0))
#guard (arenaRun 0 6 sOff sMem 2 sInit) = (2, 1, (List.replicate 6 0, 0))

-- **The touch counter counts writes, not distinct cells (R0/D-g).**
-- Arena 1 activates `{4, 4, 1}`: two distinct cells, three writes, and
-- the counter — hence the number of pops the reset performs — is three.
#guard (innerRun sMem 3 (2, 0, (List.replicate 6 0, 0))).2.2.2 = 3
#guard ((innerRun sMem 3 (2, 0, (List.replicate 6 0, 0))).2.2.1.filter
  (fun v => decide (0 < v))).length = 2

-- …and the array it leaves behind before the reset: slot 4 holds 2.
#guard (innerRun sMem 3 (2, 0, (List.replicate 6 0, 0))).2.2.1 = [0, 1, 0, 0, 2, 0]

-- **Negative control 1.** The reset is load-bearing: without it a later
-- arena sees an earlier one's marks (arena 1 revisits slot `1`, arena 2
-- revisits slot `3`). Running the three inner passes back to back on one
-- array — the driver with the reset deleted — gives `3`, not `1`.
#guard (innerRun sMem 1 (innerRun sMem 3 (innerRun sMem 2 sInit))).2.1 = 3
/--
error: Expression
  decide ((innerRun sMem 1 (innerRun sMem 3 (innerRun sMem 2 sInit))).2.1 = sOut.2.1)
did not evaluate to `true`
-/
#guard_msgs in
#guard (innerRun sMem 1 (innerRun sMem 3 (innerRun sMem 2 sInit))).2.1 = sOut.2.1

-- **Negative control 2.** The total touch count is not the carrier size,
-- and not the carrier size times the arena count.
/--
error: Expression
  decide (sizesSum sOff 0 3 = 3 * 6)
did not evaluate to `true`
-/
#guard_msgs in
#guard sizesSum sOff 0 3 = 3 * 6

-- **Negative control 3.** An empty arena list touches nothing and leaves
-- the state alone — the edge the cost formula has to get right.
#guard arenaRun 0 6 sOff sMem 0 sInit = sInit
#guard sizesSum sOff 0 0 = 0

-- …and an arena with an empty active set is a no-op too. `off` here has
-- `off[1] = off[0]`, so arena `0` is empty.
#guard arenaRun 0 6 [0, 0, 1] [5] 1 (0, 0, (List.replicate 6 0, 0))
  = (1, 0, (List.replicate 6 0, 0))
#guard arenaSize [0, 0, 1] 0 = 0

/-! ## 3. The abstract program

Two loops, written at the interface layer: `mopAget` for the block
structure, `mop_tget` / `mop_tset` / `mop_treset` for the scratch, and
the two in-place scalar ops of §1. Nothing here mentions an assertion, a
cell, a `Com` or a cost. -/

/-- The inner pass needs no invariant: the index bounds are discharged
inside the operations' own `assert`s (P4/D-ed), and `hnr_while` reads
termination off the abstract loop's non-failure (R0/D-b). -/
def innerI : TSt → Prop := fun _ => True

/-- The inner guard: `k < kend`. -/
def innerBf (kend : ℕ) : TSt → Bool := fun s => decide (s.1 < kend)

/-- **One slot**: read the slot's carrier index, read that cell, write it
back incremented, accumulate the old value, advance. -/
noncomputable def innerF (n : ℕ) (mem : List ℕ) : TSt → NRest TSt ECost := fun s =>
  bindT (mopAget mem s.1) fun u =>
    bindT (mop_tget s.2.2 u) fun w =>
      bindT (mopBinop .add w 1) fun w1 =>
        bindT (mop_tset n s.2.2 u w1) fun tr =>
          bindT (mopAddIn s.2.1 w) fun acc =>
            bindT (mopSucc s.1) fun k =>
              bindT (mopPair acc tr) fun p => mopPair k p

/-- **One arena's pass.** -/
noncomputable def innerLoop (n : ℕ) (mem : List ℕ) (kend : ℕ) (s₀ : TSt) : NRest TSt ECost :=
  irWhileIT innerI (innerBf kend) (innerF n mem) s₀

/-- Assembling the inner loop's state: `hnr_while` reads a loop's state
off a *single* `hnCtxt` conjunct, so a loop entered in the middle of a
block has to have its state built (P7/D-bi). -/
noncomputable def pack3 (a b : ℕ) (tr : List ℕ × ℕ) : NRest TSt ECost :=
  bindT (mopPair b tr) fun p => mopPair a p

def outerI : TSt → Prop := fun _ => True

/-- The outer guard: `a < m`. -/
def outerBf (m : ℕ) : TSt → Bool := fun s => decide (s.1 < m)

/-- **One arena**: the row bounds, the inner pass, the reset, the bump.
The reset is the only thing between two arenas, and it is what the
`n · (number of arenas)` term would have been. -/
noncomputable def arenaF (dflt n : ℕ) (off mem : List ℕ) : TSt → NRest TSt ECost := fun s =>
  bindT (mopAget off s.1) fun k0 =>
    bindT (mopBinop .add s.1 1) fun a1 =>
      bindT (mopAget off a1) fun kend =>
        bindT (pack3 k0 s.2.1 s.2.2) fun z0 =>
          bindT (innerLoop n mem kend z0) fun r =>
            bindT (mop_treset dflt n r.2.2) fun tr =>
              bindT (mopSucc s.1) fun a' =>
                bindT (mopPair r.2.1 tr) fun p => mopPair a' p

/-- **The driver.** -/
noncomputable def clusterLoop (dflt n : ℕ) (off mem : List ℕ) (m : ℕ) (s₀ : TSt) :
    NRest TSt ECost :=
  irWhileIT outerI (outerBf m) (arenaF dflt n off mem) s₀

/-! ## 4. The synthesis

One command each. The inner pass is synthesized standalone first — it is
the interesting half, and having it alone makes the nesting's cost
visible — and then the whole driver, nested loops and all, in a single
`sepref_synth`. -/

/--
info: sepref_synth Lax13Proofs.Refine.TrailRecursion.innerSynth:
  Com.while (Cond.lt (Operand.cell "k") (Operand.cell "kend"))
    ((Com.aget "u" "mem" "k").seq
      ((tgetCom "w" "A" "u").seq
        ((Com.binop Imp.Bop.add "w1" "w" "one").seq
          ((tsetCom "A" "T" "t" "u" "w1" "one").seq
            ((Com.binop Imp.Bop.add "acc" "acc" "w").seq
              ((Com.binop Imp.Bop.add "k" "k" "one").seq (Com.skip.seq Com.skip)))))))
-/
#guard_msgs in
sepref_synth innerSynth (dflt n : ℕ) (mem : List ℕ) (kend : ℕ) (s₀ : TSt) :
  hnRefine (hnCtxt (natAssn ×ₐ natAssn ×ₐ trailAssn dflt n) s₀ ("k", "acc", ("A", "T", "t")) ∗
      hnCtxt arrayAssn mem "mem" ∗ hnCtxt natAssn kend "kend" ∗
      hnCtxt natAssn 1 "one" ∗ junkCell "u" ∗ junkCell "w" ∗ junkCell "w1")
    _ _ ("k", "acc", ("A", "T", "t")) (natAssn ×ₐ natAssn ×ₐ trailAssn dflt n)
    (innerLoop n mem kend s₀)

/-! **The whole driver**, nested loops and all. The reset's two scratch
cells are `"u"` and `"w"` — the inner pass's, dead by then and reused by
the allocator (R0/D-f). -/

set_option maxHeartbeats 1000000 in
sepref_synth clusterSynth (dflt n : ℕ) (off mem : List ℕ) (m : ℕ) (s₀ : TSt) :
  hnRefine (hnCtxt (natAssn ×ₐ natAssn ×ₐ trailAssn dflt n) s₀ ("a", "acc", ("A", "T", "t")) ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn mem "mem" ∗
      hnCtxt natAssn m "m" ∗ hnCtxt natAssn dflt "D" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "k0" ∗ junkCell "a1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "w" ∗
      junkCell "w1")
    _ _ ("a", "acc", ("A", "T", "t")) (natAssn ×ₐ natAssn ×ₐ trailAssn dflt n)
    (clusterLoop dflt n off mem m s₀)

-- The synthesized program, pinned. Two `while`s, the outer one carrying
-- the reset's pop loop after the inner one.
#guard clusterSynth_impl =
  Com.while (Cond.lt (Operand.cell "a") (Operand.cell "m"))
    ((Com.aget "k0" "off" "a").seq
      ((Com.binop Imp.Bop.add "a1" "a" "one").seq
        ((Com.aget "kend" "off" "a1").seq
          ((Com.skip.seq Com.skip).seq
            ((Com.while (Cond.lt (Operand.cell "k0") (Operand.cell "kend"))
                  ((Com.aget "u" "mem" "k0").seq
                    ((tgetCom "w" "A" "u").seq
                      ((Com.binop Imp.Bop.add "w1" "w" "one").seq
                        ((tsetCom "A" "T" "t" "u" "w1" "one").seq
                          ((Com.binop Imp.Bop.add "acc" "acc" "w").seq
                            ((Com.binop Imp.Bop.add "k0" "k0" "one").seq
                              (Com.skip.seq Com.skip)))))))).seq
              ((resetCom "A" "T" "t" "u" "w" "D" "one").seq
                ((Com.binop Imp.Bop.add "a" "a" "one").seq (Com.skip.seq Com.skip))))))))

/-- The caller's ownership, named. -/
def clusterPre (dflt n : ℕ) (off mem : List ℕ) (m : ℕ) (s₀ : TSt) : Assn :=
  hnCtxt (natAssn ×ₐ natAssn ×ₐ trailAssn dflt n) s₀ ("a", "acc", ("A", "T", "t")) ∗
    hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn mem "mem" ∗
    hnCtxt natAssn m "m" ∗ hnCtxt natAssn dflt "D" ∗ hnCtxt natAssn 1 "one" ∗
    junkCell "k0" ∗ junkCell "a1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "w" ∗
    junkCell "w1"

/-! ## 5. What the driver computes and what it spends

Each op's price is what §4's synthesis spent; each loop's value is proved
equal to §2's twin. -/

/-- One slot's price: the `mem` read, the `tget`, the increment, the
`tset`, the accumulation, the advance, and the two tuple steps. -/
noncomputable def innerStepCost : ECost :=
  irUnit Currency.aget + irUnit Currency.aget + irUnit Currency.add + tsetCost +
    irUnit Currency.add + irUnit Currency.add + irUnit Currency.skip + irUnit Currency.skip

/-- …and one arena's pass: one slot per touch, one guard evaluation per
touch plus the exit's. -/
noncomputable def innerLoopCost (j : ℕ) : ECost :=
  j • innerStepCost + (j + 1) • irUnit Currency.«while»

theorem innerF_eq (n : ℕ) (mem : List ℕ) (s : TSt) (h1 : s.1 < mem.length)
    (h2 : mem[s.1]! < s.2.2.1.length) (h3 : mem[s.1]! < n) (h4 : s.2.2.2 < n) :
    innerF n mem s = NRest.consume (NRest.returnT (innerStep mem s)) innerStepCost := by
  show NRest.bindT (mopAget mem s.1) _ = _
  simp only [mop_tget, mop_tset, mopAget_def, mopBinop_def, mopAddIn_eq, mopSucc_eq, mopPair_def,
    NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos (show mem[s.1]! < n ∧ s.2.2.2 < n
      from ⟨h3, h4⟩), NRest.returnT_bindT, bindT_unit, NRest.consume_consume, innerStep,
    innerStepCost, Imp.Bop.apply_add, binopCurrency_add]
  congr 1
  ac_rfl

theorem innerRun_index (mem : List ℕ) : ∀ (j : ℕ) (s : TSt), (innerRun mem j s).1 = s.1 + j := by
  intro j
  induction j with
  | zero => intro s; simp [innerRun]
  | succ j ih => intro s; rw [innerRun, ih]; show s.1 + 1 + j = s.1 + (j + 1); omega

theorem innerRun_counter (mem : List ℕ) :
    ∀ (j : ℕ) (s : TSt), (innerRun mem j s).2.2.2 = s.2.2.2 + j := by
  intro j
  induction j with
  | zero => intro s; simp [innerRun]
  | succ j ih => intro s; rw [innerRun, ih]; show s.2.2.2 + 1 + j = s.2.2.2 + (j + 1); omega

theorem innerRun_len (mem : List ℕ) :
    ∀ (j : ℕ) (s : TSt), (innerRun mem j s).2.2.1.length = s.2.2.1.length := by
  intro j
  induction j with
  | zero => intro s; simp [innerRun]
  | succ j ih => intro s; rw [innerRun, ih]; show (s.2.2.1.set _ _).length = _; simp

/-- **The inner pass's value and price.** `j` touches, at a price with
no `n` in it. -/
theorem innerLoop_value (n : ℕ) (mem : List ℕ) :
    ∀ (j : ℕ) (s : TSt), s.2.2.1.length = n →
      (∀ i, s.1 ≤ i → i < s.1 + j → i < mem.length ∧ mem[i]! < n) → s.2.2.2 + j ≤ n →
      innerLoop n mem (s.1 + j) s
        = NRest.consume (NRest.returnT (innerRun mem j s)) (innerLoopCost j) := by
  intro j
  induction j with
  | zero =>
    intro s _ _ _
    have hb : innerBf (s.1 + 0) s = false := by simp [innerBf]
    show irWhileIT innerI (innerBf (s.1 + 0)) (innerF n mem) s = _
    rw [irWhileIT_of_false (show innerI s from trivial) hb]
    congr 1
    simp [innerLoopCost]
  | succ j ih =>
    intro s hlen hmem hcnt
    have hb : innerBf (s.1 + (j + 1)) s = true := by simp [innerBf]
    obtain ⟨h1, h3⟩ := hmem s.1 (le_refl _) (by omega)
    have h2 : mem[s.1]! < s.2.2.1.length := by rw [hlen]; exact h3
    have h4 : s.2.2.2 < n := by omega
    have hstep : s.1 + (j + 1) = (innerStep mem s).1 + j := by
      show s.1 + (j + 1) = s.1 + 1 + j; omega
    show irWhileIT innerI (innerBf (s.1 + (j + 1))) (innerF n mem) s = _
    rw [irWhileIT_of_true (show innerI s from trivial) hb,
      innerF_eq n mem s h1 h2 h3 h4, bindT_unit, hstep]
    show NRest.consume (NRest.consume
      (innerLoop n mem ((innerStep mem s).1 + j) (innerStep mem s)) innerStepCost) _ = _
    have hlen' : (innerStep mem s).2.2.1.length = n := by
      show (s.2.2.1.set _ _).length = n
      simpa using hlen
    have hmem' : ∀ i, (innerStep mem s).1 ≤ i → i < (innerStep mem s).1 + j →
        i < mem.length ∧ mem[i]! < n := by
      intro i hi hj
      have hi' : s.1 + 1 ≤ i := hi
      have hj' : i < s.1 + 1 + j := hj
      exact hmem i (by omega) (by omega)
    have hcnt' : (innerStep mem s).2.2.2 + j ≤ n := by
      show s.2.2.2 + 1 + j ≤ n
      omega
    rw [ih (innerStep mem s) hlen' hmem' hcnt',
      NRest.consume_consume, NRest.consume_consume]
    congr 1
    all_goals first
      | rfl
      | (simp only [innerLoopCost, succ_nsmul]; abel)

/-! ### One arena -/

/-- The static facts that keep arena `a`'s reads in range and its touch
budget inside the trail's capacity (R0/D-g: the budget bounds *writes*,
so what has to fit is the arena's width). -/
def ArenaOk (n : ℕ) (off mem : List ℕ) (a : ℕ) : Prop :=
  a + 1 < off.length ∧ off[a]! ≤ off[a + 1]! ∧ arenaSize off a ≤ n ∧
    ∀ i, off[a]! ≤ i → i < off[a + 1]! → i < mem.length ∧ mem[i]! < n

/-- One arena's price: the two row bounds and the increment between them,
the state-building pair, the pass, **the reset — priced at the arena's
touches, not at `n`** — the bump, and the two tuple steps. -/
noncomputable def arenaCost (sz : ℕ) : ECost :=
  irUnit Currency.aget + irUnit Currency.add + irUnit Currency.aget +
    irUnit Currency.skip + irUnit Currency.skip + innerLoopCost sz + resetCost sz +
    irUnit Currency.add + irUnit Currency.skip + irUnit Currency.skip

theorem pack3_eq (a b : ℕ) (tr : List ℕ × ℕ) :
    pack3 a b tr
      = NRest.consume (NRest.returnT ((a, b, tr) : TSt))
          (irUnit Currency.skip + irUnit Currency.skip) := by
  show NRest.bindT (mopPair b tr) _ = _
  rw [mopPair_def, bindT_unit, mopPair_def, NRest.consume_consume]

theorem arenaF_eq (dflt n : ℕ) (off mem : List ℕ) (s : TSt)
    (hs : s.2.2 = (List.replicate n dflt, 0)) (hok : ArenaOk n off mem s.1) :
    arenaF dflt n off mem s
      = NRest.consume (NRest.returnT (arenaStep dflt n off mem s))
          (arenaCost (arenaSize off s.1)) := by
  obtain ⟨hlen1, hmono, hcap, hmem⟩ := hok
  have hlen0 : s.1 < off.length := by omega
  have harr : s.2.2.1.length = n := by rw [hs]; simp
  have hcnt0 : s.2.2.2 = 0 := by rw [hs]
  set sz := arenaSize off s.1 with hszdef
  have hkend : off[s.1 + 1]! = off[s.1]! + sz := by rw [hszdef, arenaSize]; omega
  have hinner : innerLoop n mem (off[s.1]! + sz) (off[s.1]!, s.2.1, s.2.2)
      = NRest.consume (NRest.returnT (innerRun mem sz (off[s.1]!, s.2.1, s.2.2)))
          (innerLoopCost sz) := by
    refine innerLoop_value n mem sz (off[s.1]!, s.2.1, s.2.2) harr (fun i hi hj => ?_) ?_
    · exact hmem i hi (by rw [hkend]; exact hj)
    · show s.2.2.2 + sz ≤ n; omega
  have hpop : (innerRun mem sz (off[s.1]!, s.2.1, s.2.2)).2.2.2 = sz := by
    rw [innerRun_counter]; show s.2.2.2 + sz = sz; omega
  show NRest.bindT (mopAget off s.1) _ = _
  simp only [mopAget_def, mopBinop_def, mopSucc_eq, mopPair_def, mop_treset, pack3_eq,
    NRest.assert_pos hlen0, NRest.assert_pos hlen1, NRest.returnT_bindT, bindT_unit,
    Imp.Bop.apply_add, binopCurrency_add, hkend, hinner, hpop, NRest.consume_consume,
    arenaStep, arenaCost, ← hszdef]
  congr 1
  ac_rfl

/-! ### The driver -/

/-- **The driver's price**, arena by arena: one guard evaluation and one
arena, `j` times, plus the exit's guard. -/
noncomputable def clusterCost (off : List ℕ) : ℕ → ℕ → ECost
  | _, 0 => irUnit Currency.«while»
  | a, j + 1 => irUnit Currency.«while» + arenaCost (arenaSize off a) + clusterCost off (a + 1) j

/-- **The driver's value and price.** The hypothesis `s.2.2 = (replicate
n dflt, 0)` is the arenas' non-interference: the reset restores it, so
the induction carries it (R0/D-c). -/
theorem clusterLoop_value (dflt n : ℕ) (off mem : List ℕ) :
    ∀ (j : ℕ) (s : TSt), s.2.2 = (List.replicate n dflt, 0) →
      (∀ a, s.1 ≤ a → a < s.1 + j → ArenaOk n off mem a) →
      clusterLoop dflt n off mem (s.1 + j) s
        = NRest.consume (NRest.returnT (arenaRun dflt n off mem j s)) (clusterCost off s.1 j) := by
  intro j
  induction j with
  | zero =>
    intro s _ _
    have hb : outerBf (s.1 + 0) s = false := by simp [outerBf]
    show irWhileIT outerI (outerBf (s.1 + 0)) (arenaF dflt n off mem) s = _
    rw [irWhileIT_of_false (show outerI s from trivial) hb]
    rfl
  | succ j ih =>
    intro s hs hok
    have hb : outerBf (s.1 + (j + 1)) s = true := by simp [outerBf]
    have hstep : s.1 + (j + 1) = (arenaStep dflt n off mem s).1 + j := by
      show s.1 + (j + 1) = s.1 + 1 + j; omega
    show irWhileIT outerI (outerBf (s.1 + (j + 1))) (arenaF dflt n off mem) s = _
    rw [irWhileIT_of_true (show outerI s from trivial) hb,
      arenaF_eq dflt n off mem s hs (hok s.1 (le_refl _) (by omega)), bindT_unit, hstep]
    show NRest.consume (NRest.consume (clusterLoop dflt n off mem
      ((arenaStep dflt n off mem s).1 + j) (arenaStep dflt n off mem s)) _) _ = _
    have hok' : ∀ a, (arenaStep dflt n off mem s).1 ≤ a →
        a < (arenaStep dflt n off mem s).1 + j → ArenaOk n off mem a := by
      intro a ha hb'
      have ha' : s.1 + 1 ≤ a := ha
      have hb'' : a < s.1 + 1 + j := hb'
      exact hok a (by omega) (by omega)
    rw [ih (arenaStep dflt n off mem s) rfl hok',
      NRest.consume_consume, NRest.consume_consume,
      show (arenaStep dflt n off mem s).1 = s.1 + 1 from rfl]
    congr 1

/-! ## 6. The acceptance criterion — the cost is touched-only

This is what the file exists for. `clusterCost` is re-read as
`touches • touchUnit + arenas • arenaConst + one`: linear in the *total
number of touches*, constant per arena, and with **no term in which the
carrier size `n` and the arena count multiply**. `n` does not occur at
all — `clusterCost` does not take it. -/

/-- **The price of one touch**: the slot's own work, the pop that undoes
it, and the two guard evaluations (inner and reset) that carry them. -/
noncomputable def touchUnit : ECost :=
  innerStepCost + resetStepCost + irUnit Currency.«while» + irUnit Currency.«while»

/-- **The price of one arena, independent of its size**: the outer
guard, the two row bounds and the increment between them, the two tuple
steps that build the inner state, the inner pass's and the reset's exit
guards, the bump, and the two tuple steps that rebuild the outer
state. -/
noncomputable def arenaConst : ECost :=
  irUnit Currency.«while» + irUnit Currency.aget + irUnit Currency.add + irUnit Currency.aget +
    irUnit Currency.skip + irUnit Currency.skip + irUnit Currency.«while» +
    irUnit Currency.«while» + irUnit Currency.add + irUnit Currency.skip + irUnit Currency.skip

/-- One arena, re-read: its size enters *linearly*, through `touchUnit`
alone. -/
theorem arenaCost_split (sz : ℕ) :
    irUnit Currency.«while» + arenaCost sz = sz • touchUnit + arenaConst := by
  simp only [arenaCost, innerLoopCost, resetCost, touchUnit, arenaConst, smul_add, succ_nsmul]
  abel

/-- **The characteristic theorem.** The driver's price is
`touches • touchUnit + arenas • arenaConst + one`. Both `touchUnit` and
`arenaConst` are constants — they do not mention `off`, `mem`, `n`, the
arena count or any arena's size — and `sizesSum off a j` is exactly the
total number of touches (§2). There is no `n · j` term because there is
no `n`. -/
theorem clusterCost_touched_only (off : List ℕ) :
    ∀ (a j : ℕ), clusterCost off a j
      = (sizesSum off a j) • touchUnit + j • arenaConst + irUnit Currency.«while» := by
  intro a j
  induction j generalizing a with
  | zero => simp [clusterCost, sizesSum]
  | succ j ih =>
    rw [clusterCost, ih (a + 1), sizesSum, add_smul, succ_nsmul,
      show irUnit Currency.«while» + arenaCost (arenaSize off a)
        + ((sizesSum off (a + 1) j) • touchUnit + j • arenaConst + irUnit Currency.«while»)
        = (irUnit Currency.«while» + arenaCost (arenaSize off a))
          + ((sizesSum off (a + 1) j) • touchUnit + j • arenaConst
            + irUnit Currency.«while») from by abel,
      arenaCost_split]
    abel

/-! ### 6.1 The same theorem at one currency

Sharpest form: the driver's *array writes* are exactly three per touch —
two for the `tset` (the trail push and the data write) and one for the
pop that undoes it. The carrier size and the arena count do not appear
in the formula at all. -/

theorem touchUnit_aset : touchUnit.toFun Currency.aset = 3 := by decide +kernel
theorem arenaConst_aset : arenaConst.toFun Currency.aset = 0 := by decide +kernel

theorem irUnit_while_aset : (irUnit Currency.«while»).toFun Currency.aset = 0 := by
  decide +kernel

theorem clusterCost_aset (off : List ℕ) (a j : ℕ) :
    (clusterCost off a j).toFun Currency.aset = 3 * (sizesSum off a j) := by
  rw [clusterCost_touched_only, ACost.toFun_add, ACost.toFun_add, ACost.toFun_nsmul,
    ACost.toFun_nsmul, touchUnit_aset, arenaConst_aset, irUnit_while_aset]
  simp [mul_comm]

/-- …and the aget count, which the per-arena constant *does* contribute
to: three per touch's neighbourhood plus two row reads per arena. Still
no product of `n` with anything. -/
theorem touchUnit_aget : touchUnit.toFun Currency.aget = 3 := by decide +kernel
theorem arenaConst_aget : arenaConst.toFun Currency.aget = 2 := by decide +kernel

/-! ### 6.1b The criterion, on the synthesized program

`clusterSynth` (§4) is the deep `Ir.Com`. Put together with the value
theorem and the re-reading above, this is the deliverable in one
statement: **the synthesized driver refines a program whose whole cost is
`touches • touchUnit + arenas • arenaConst + one`** — and nothing in that
expression is the carrier size. -/

theorem clusterSynth_touched_only (dflt n : ℕ) (off mem : List ℕ) (j : ℕ) (s₀ : TSt)
    (hs : s₀.2.2 = (List.replicate n dflt, 0))
    (hok : ∀ a, s₀.1 ≤ a → a < s₀.1 + j → ArenaOk n off mem a) :
    ∃ Γ' : Assn,
      hnRefine (clusterPre dflt n off mem (s₀.1 + j) s₀) clusterSynth_impl Γ'
        ("a", "acc", ("A", "T", "t")) (natAssn ×ₐ natAssn ×ₐ trailAssn dflt n)
        (NRest.consume (NRest.returnT (arenaRun dflt n off mem j s₀))
          ((sizesSum off s₀.1 j) • touchUnit + j • arenaConst + irUnit Currency.«while»)) := by
  have h := clusterSynth dflt n off mem (s₀.1 + j) s₀
  rw [clusterLoop_value dflt n off mem j s₀ hs hok, clusterCost_touched_only] at h
  exact ⟨_, h⟩

/-! ### 6.2 The carrier does not enter

`clusterCost` has no `n` argument at all, so "the same block structure
costs the same at every carrier size" is not a theorem about the formula
— it is a reading of its signature, exactly as `resetCost k`'s signature
is what `treset_cost_touched_only` reads. What *is* a theorem is the
same fact about the two **runs**, which do mention their carriers. -/

set_option linter.unusedVariables false in
/-- Two *runs* of the driver, at carriers of wildly different sizes, over
the same block structure — same price. -/
theorem clusterLoop_cost_carrier_free (dflt₁ dflt₂ n₁ n₂ : ℕ) (off mem : List ℕ) (j : ℕ)
    (s₁ s₂ : TSt) (h₁ : s₁.2.2 = (List.replicate n₁ dflt₁, 0))
    (h₂ : s₂.2.2 = (List.replicate n₂ dflt₂, 0)) (ha : s₁.1 = s₂.1)
    (hok₁ : ∀ a, s₁.1 ≤ a → a < s₁.1 + j → ArenaOk n₁ off mem a)
    (hok₂ : ∀ a, s₂.1 ≤ a → a < s₂.1 + j → ArenaOk n₂ off mem a) :
    ∃ c : ECost,
      clusterLoop dflt₁ n₁ off mem (s₁.1 + j) s₁
          = NRest.consume (NRest.returnT (arenaRun dflt₁ n₁ off mem j s₁)) c ∧
        clusterLoop dflt₂ n₂ off mem (s₂.1 + j) s₂
          = NRest.consume (NRest.returnT (arenaRun dflt₂ n₂ off mem j s₂)) c := by
  refine ⟨clusterCost off s₁.1 j, clusterLoop_value dflt₁ n₁ off mem j s₁ h₁ hok₁, ?_⟩
  rw [ha]
  exact clusterLoop_value dflt₂ n₂ off mem j s₂ h₂ hok₂

/-! ### 6.3 The costs, pinned

Concrete readings on §2's sample: three arenas, six touches, carrier 6 —
and then the very same numbers at carrier 6000. -/

theorem sample_aset : (clusterCost sOff 0 3).toFun Currency.aset = 18 := by decide +kernel

theorem sample_aget : (clusterCost sOff 0 3).toFun Currency.aget = 24 := by decide +kernel

theorem sample_while : (clusterCost sOff 0 3).toFun Currency.«while» = 22 := by decide +kernel

-- **Negative control.** The driver does not write once per slot per
-- arena: `3 · 6 · 6 = 108` is what the naive re-zero would cost, and it
-- is not what this costs.
/-- error: Tactic `decide` proved that the proposition
  (clusterCost sOff 0 3).toFun Currency.aset = 108
is false -/
#guard_msgs in
example : (clusterCost sOff 0 3).toFun Currency.aset = 108 := by decide +kernel

/-! ### 6.4 The one-time `O(n)` charge

`touched-only-costs.md` allows exactly one: the initial fill. The whole
program — establish the scratch, then drive the arenas — is priced
`tinitCost n + clusterCost off 0 m`, and `n` occurs in the first summand
and nowhere else. `tinitProg` is `Iicf/IicfTrailArray.lean` §8's, whose
lift from junk (`hnr_trail_init`) is landed there; composing it with §4's
`Com` is one `hnr_seq` and is left as backlog, because what the criterion
is about is the *driver*. -/

noncomputable def clusterProg (dflt n : ℕ) (off mem : List ℕ) (m : ℕ) (xs : List ℕ) :
    NRest TSt ECost :=
  bindT (tinitProg dflt xs) fun s₀ => clusterLoop dflt n off mem m (0, 0, s₀)

/-- The whole program's price: the one-time fill, then the driver. -/
noncomputable def clusterTotalCost (n : ℕ) (off : List ℕ) (m : ℕ) : ECost :=
  tinitCost n + clusterCost off 0 m

theorem clusterProg_value (dflt n : ℕ) (off mem xs : List ℕ) (m : ℕ) (hxs : xs.length = n)
    (hok : ∀ a, a < m → ArenaOk n off mem a) :
    clusterProg dflt n off mem m xs
      = NRest.consume (NRest.returnT (arenaRun dflt n off mem m (0, 0, (List.replicate n dflt, 0))))
          (clusterTotalCost n off m) := by
  have hok' : ∀ a, ((0, 0, (List.replicate n dflt, 0)) : TSt).1 ≤ a →
      a < ((0, 0, (List.replicate n dflt, 0)) : TSt).1 + m → ArenaOk n off mem a := by
    intro a _ ha
    have ha' : a < 0 + m := ha
    exact hok a (by omega)
  have h := clusterLoop_value dflt n off mem m ((0, 0, (List.replicate n dflt, 0)) : TSt) rfl hok'
  rw [show ((0, 0, (List.replicate n dflt, 0)) : TSt).1 + m = m from by
    show 0 + m = m; omega] at h
  show NRest.bindT (tinitProg dflt xs) _ = _
  rw [tinitProg_value dflt xs, hxs, bindT_unit, h, NRest.consume_consume]
  congr 1

/-! ## 7. Gate

§2 falsified the driver's *values*. This falsifies its *cost claim*: the
naive per-arena re-zero is shown to admit no touched-only bound at all,
and the shape of the sum is pinned at the edges. -/

/-! ### 7.1 The edges of the cost statement -/

/-- No arenas: one guard evaluation, nothing else. -/
theorem clusterCost_zero (off : List ℕ) (a : ℕ) :
    clusterCost off a 0 = irUnit Currency.«while» := rfl

/-- An empty arena is *not* free — it costs `arenaConst`, which is the
per-arena term the criterion explicitly allows — but it costs nothing
per touch. -/
theorem arenaCost_empty : irUnit Currency.«while» + arenaCost 0 = arenaConst := by
  simp [arenaCost_split]

/-- One more touch is exactly one more `touchUnit`, whatever the arena
and whatever the carrier. -/
theorem clusterCost_succ_touch (off : List ℕ) (a j : ℕ) :
    clusterCost off a (j + 1)
      = (arenaSize off a) • touchUnit + arenaConst + clusterCost off (a + 1) j := by
  rw [clusterCost, ← arenaCost_split]

/-! ### 7.2 The naive driver, as arithmetic

The comparison is made at one currency — array writes — because that is
where the two drivers differ and because the count is exact on both
sides. Ours: `3` per touch (`clusterCost_aset`). The naive one: `1` per
touch (a plain `aset`, no trail push) and `n` per arena for the
re-zeroing fill. -/

/-- The naive driver's array-write count: one per touch, plus a full
re-zero of the carrier per arena. -/
def naiveAsets (n arenas touches : ℕ) : ℕ := touches + arenas * n

set_option linter.unusedVariables false in
/-- Ours, for comparison, as a function of the same three numbers — and
`n` is not among the ones it uses. -/
def trailAsets (n arenas touches : ℕ) : ℕ := 3 * touches

theorem trailAsets_eq (off : List ℕ) (a j n : ℕ) :
    (clusterCost off a j).toFun Currency.aset = trailAsets n j (sizesSum off a j) :=
  clusterCost_aset off a j

-- On §2's sample at carrier 6: ours 18, the naive one 24.
#guard trailAsets 6 3 6 = 18
#guard naiveAsets 6 3 6 = 24
-- …and at carrier 6000, with the *same* arenas and the same touches:
-- ours is unchanged, the naive one is a thousand times worse.
#guard trailAsets 6000 3 6 = 18
#guard naiveAsets 6000 3 6 = 18006

/-! ### 7.3 The negative control, as a theorem

Not "the naive driver is worse on this input" but "the naive driver has
**no** bound of the touched-only shape". A touched-only bound is
`c₁ · touches + c₂ · arenas + c₃` for constants fixed before the input;
for every such triple there is a carrier and an arena family that breaks
it. The family is the honest one: single-element arenas, so
`touches = arenas` and the trail driver's own count `3 · touches` is of
the shape with `c₁ = 3`. -/

theorem naive_no_touched_only_bound (c₁ c₂ c₃ : ℕ) :
    ∃ n arenas : ℕ, 0 < n ∧ ¬ (naiveAsets n arenas arenas ≤ c₁ * arenas + c₂ * arenas + c₃) := by
  refine ⟨c₁ + c₂ + 2, c₃ + 1, by omega, fun h => ?_⟩
  rw [naiveAsets] at h
  have e : (c₃ + 1) + (c₃ + 1) * (c₁ + c₂ + 2)
      = (c₁ * (c₃ + 1) + c₂ * (c₃ + 1)) + 3 * (c₃ + 1) := by ring
  rw [e] at h
  generalize c₁ * (c₃ + 1) = A at h
  generalize c₂ * (c₃ + 1) = B at h
  omega

/-- …and the positive counterpart, on the same family: the trail driver
*is* of that shape, with `c₁ = 3` and `c₂ = c₃ = 0`, at every carrier. -/
theorem trail_touched_only_bound (n arenas : ℕ) :
    trailAsets n arenas arenas ≤ 3 * arenas + 0 * arenas + 0 :=
  le_of_eq (by simp [trailAsets])

/-! ### 7.4 Axioms -/

/-- info: 'Lax13Proofs.Refine.TrailRecursion.clusterSynth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterSynth

/-- info: 'Lax13Proofs.Refine.TrailRecursion.innerSynth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms innerSynth

/-- info: 'Lax13Proofs.Refine.TrailRecursion.clusterLoop_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterLoop_value

/-- info: 'Lax13Proofs.Refine.TrailRecursion.clusterCost_touched_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterCost_touched_only

/-- info: 'Lax13Proofs.Refine.TrailRecursion.clusterProg_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterProg_value

/-- info: 'Lax13Proofs.Refine.TrailRecursion.clusterSynth_touched_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clusterSynth_touched_only

/-! ## 8. Telemetry (the wave's acceptance numbers)

* **Authored lines: 415.** `wc -l` is 893; a nesting-aware scan
  classifies 113 as blank and 365 as comment (inside a block comment or a
  docstring, or a `--` line). The two pinned `sepref_synth` outputs and
  the six pinned `#print axioms` lines sit inside docstrings and are
  therefore in the comment bucket. Of the 415, the two abstract loop
  bodies and the two loop wrappers are 20 lines and the two
  `sepref_synth` invocations 12; the rest is the falsification block, the
  value lemmas and the cost algebra.

* **Hand-written frame clauses: 0.** Nothing in this file rewrites with
  `sepConj_assoc`, `sepConj_comm`, `ac_rfl` *on assertions*,
  `irSTATE_rot`, `fri`, `iicf_perm`, `hnRefine_pre_perm`,
  `hnRefine_frame` or `entails_of_eq`. The two `ac_rfl`s (in `innerF_eq`
  and `arenaF_eq`) are on **cost sums** (`ECost`, an `AddCommMonoid`),
  under a `congr 1`, not on `∗`. The `∗`-lists in the two `sepref_synth`
  goals and in `clusterPre` are interface — what the caller owns — and
  every permutation, split and frame that turns them into rule instances
  is inferred, *including the ones that reach inside the nested loop's
  state to hand the trail array to `mop_treset`*.

* **Bespoke tactics: 0.** Two `sepref_synth` invocations; the rest is
  `rw`/`simp only`/`omega`/`abel`/`decide +kernel`.

* **Interface ops consumed: 6** — `mopAget`, `mopBinop`, `mopPair` (P4
  primitives); `mop_tget`, `mop_tset`, `mop_treset`
  (`Iicf/IicfTrailArray.lean`, all three with synthesized
  implementations) — plus the two in-place scalar ops declared here
  (§1), and `mop_array_fill` through `tinitProg` in §6.4.

* **Wall clock**, warm build, `lake env lean` on the single file: **15.5
  s**, of which the two `sepref_synth` invocations and the ten
  `decide +kernel` cost pins are the bulk. The nested synthesis
  (`clusterSynth`) needed `maxHeartbeats 1000000`; the standalone inner
  loop needed none.

* **Axioms.** `#print axioms` is pinned above for `innerSynth`,
  `clusterSynth`, `clusterLoop_value`, `clusterCost_touched_only`,
  `clusterProg_value` and `clusterSynth_touched_only`: all six are
  `[propext, Classical.choice, Quot.sound]` and nothing else.

* **Backlog.** (i) `Lax13Proofs.lean` does not import this module; adding
  the line is the landing wave's, since this file was written under a
  do-not-edit-existing-files constraint. (ii) §6.4's `clusterProg` is
  costed but not synthesized end to end: `hnr_trail_init`
  (`Iicf/IicfTrailArray.lean` §8) is not a `sepref_fr_rules` entry — it
  cannot be, its precondition is junk — so composing it with
  `clusterSynth_impl` is one `hnr_seq` plus one state build, written by
  hand. Nothing about the criterion depends on it: the `O(n)` fill is the
  charge the discipline *allows*. (iii) That `acc` counts in-arena
  repeats is checked on the sample (§2), not proved; the wave's gate is
  the cost, not the driver's functional specification. -/

end TrailRecursion

end Lax13Proofs.Refine
