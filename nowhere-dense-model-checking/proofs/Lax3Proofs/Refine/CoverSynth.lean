import Lax3Proofs.RamCover
import Lax3Proofs.Refine.ScatterSynth
import Lax13Proofs.Refine.Sepref.IrOpsExtra

/-!
# ND-MC rebase P2 / satellite 2D — the cover pass, re-derived through the
refinement tower

`Lax3Proofs.RamCover` is the neighborhood-cover pass of
Grohe–Kreutzer–Siebertz §6: walk the centres in the ordering's own order,
search to depth `2r` from each in the mask whittled down so far, emit the
fibre, record first catches at radius `r`, and kill the centre. Its
mathematics — the fibre bridge, the covering argument, `CoverInv` and its
`step`/`out` — is **capital**, consumed here and never re-proved. What
this file re-derives is the *program*, at the tower's abstract layer, and
with the per-turn work charged the way the campaign's time bound needs it
charged.

## The one algorithmic change: scan the reached list, not the carrier

The baseline's emission is a flat pass over all `n` vertices, testing
`dist[z] ≤ 2r` at each. One flat pass per centre is `n` centres × `n`
vertices, and that product is the `16n²` item `touched-only-costs.md`
was written about. The tower version scans the **queue the search
leaves** — `q[0 .. tl)`, the vertices the search actually reached — so
the turn at centre `c` pays for `|X_c|` slots and not for `n`, and the
pass pays `Σ_c |X_c|`, which is exactly the quantity the density
argument already budgets (`Σ |X_v| ≤ n^{1+δ}`). The `2r` test then
disappears: everything on the reached list is within `2r` by
construction, so the emission is unconditional and only the *catch* test
at radius `r` survives, which is the test the covering argument reads.

Two edges the change has to get right, and both are pinned by the worked
example (§7):

* **A dead centre reaches nothing.** The search sets `tl := 0` when the
  source's mask bit is clear, but it has already written `q[0] := src`
  and `dist[src] := 0`, and the baseline — scanning the carrier — emits
  that centre into its own block. So the scan runs over
  `max tl 1 = tl + (1 - tl)` slots, two truncated-subtraction binops per
  turn, and the two programs agree cell for cell. Without it the third
  block of the second `#guard`ed run is empty where the baseline's is
  `{2}`.
* **The order inside a block.** The baseline emits in increasing vertex
  order, the tower in the search's discovery order. On the worked
  example the two coincide; in general they do not, and nothing above
  cares — `CoverInv.block` is an *existential* over the block's slots.

## What is consumed rather than re-proved

`RamCover.CoverInv`, `CoverInv.step`, `CoverInv.out`, `CoverOut`,
`cover_spec`'s assembly, `mem_wreach_iff_withinDist_pred`,
`ball_subset_fibre_of_min_wreach`, `masked_step` — all of it. The
`InCluster`/`Catches` vocabulary is the one `RamDriverCompose.coverImplements`
consumes and the one §8 states the bridge in.
`Lax3Proofs.Refine.ScatterSynth.mopBfs`/`hnr_mop_bfs` — the whole
synthesized queue BFS as one registered leaf operation — is 2A's capital
and is used, not restated.

## Judgment calls

**R2D/D-a — four pinned operations (§0).** The `mopSucc` idiom (P7/D-bb)
is used here to pin *cell names*, not just destinations. A turn re-enters
the search leaf, whose rule names the cells `"i"`, `"head"` and `"src"`
literally; the allocator picks junk destinations by its own order, so
`mopConstN 0` and `mopAget ord c` had to be given rules that fix the
destination. `mopZeroI`, `mopZeroIn`, `mopOrd` are those, and they cost
nothing beyond the line that declares them.

**R2D/D-b — the search leaf's entry conditions become its own
`assert`s.** This is the finding of the wave and it is what unblocked the
outer loop; see the ledger note in §0 at `mopBfsE`, and the reproducer in
§9.

**R2D/D-c — the queue's contents are a named debt, not an assumption in
disguise.** The tower's BFS export (`BfsQSynth.bfsQS_correct`) specifies
the *distance array* and says nothing about the queue. Reading the
reached list off `q` therefore needs one clause the export does not
carry, and `ReachedList` (§8) is that clause, written out, checked on
every worked run of the synthesized program (§7), and taken as a
hypothesis wherever it is used. Nothing here is `sorry`ed and no axiom is
added.

**R2D/D-d — the assignment-clearing fill is not re-derived.** It is
`RamCover.initAsg`, a flat `Fill.loop` over the carrier writing the
sentinel `n`; it is the *one* `O(n)` charge the touched-only discipline
explicitly allows (`TrailRecursion` §6.4's `tinitCost`), it is paid once
for the whole pass, and the kit already synthesizes it. The worked
example below starts from an already-cleared `asg`.
-/

namespace Lax3Proofs.Refine.CoverSynth

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref
open Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest Lax13Proofs.Refine.Codegen

/-! ## 0. Four pinned operations (R2D/D-a, R2D/D-b)

Every one of these is the `mopSucc` idiom: an irreducible alias with a
single rule, so that the operator phase cannot route the operation
anywhere but where the rule says. Three of them pin a *cell name*
because the search leaf's rule names its cells literally; the fourth
turns the leaf's two entry conditions into `assert`s. -/

/-- `i := 0`, with the destination pinned to the search's fill index. -/
noncomputable def mopZeroI : NRest ℕ ECost := mopConstN 0

theorem mopZeroI_eq : mopZeroI = mopConstN 0 := rfl

@[sepref_fr_rules]
theorem hnr_mop_zeroI :
    hnRefine (junkCell "i") (.const "i" 0) (emp : Assn) "i" natAssn mopZeroI :=
  hnr_mop_constN "i" 0

attribute [irreducible] mopZeroI

/-- `x := x * z` with `z` a cell holding zero: zeroing **in place**, so
that a cell which is a component of the turn loop's state can be reset
without leaving its cell. -/
noncomputable def mopZeroIn (m : ℕ) : NRest ℕ ECost := mopBinop .mul m 0

theorem mopZeroIn_eq (m : ℕ) : mopZeroIn m = mopBinop .mul m 0 := rfl

@[sepref_fr_rules]
theorem hnr_mop_zeroIn (x z : String) (m : ℕ) :
    hnRefine (hnCtxt natAssn m x ∗ hnCtxt natAssn 0 z) (.binop .mul x x z)
      (hnCtxt natAssn 0 z) x natAssn (mopZeroIn m) := by
  rw [mopZeroIn_eq]; exact hnr_mop_binop_self .mul x z m 0

attribute [irreducible] mopZeroIn

/-- `src := ord[c]`, with all three cells pinned: the search's source
cell, the order array, and the turn counter. -/
noncomputable def mopOrd (ord : List ℕ) (c : ℕ) : NRest ℕ ECost := mopAget ord c

theorem mopOrd_eq (ord : List ℕ) (c : ℕ) : mopOrd ord c = mopAget ord c := rfl

@[sepref_fr_rules]
theorem hnr_mop_ord (ord : List ℕ) (c : ℕ) :
    hnRefine (junkCell "src" ∗ hnCtxt arrayAssn ord "ord" ∗ hnCtxt natAssn c "c")
      (.aget "src" "ord" "c") (hnCtxt arrayAssn ord "ord" ∗ hnCtxt natAssn c "c")
      "src" natAssn (mopOrd ord c) :=
  hnr_mop_aget "src" "ord" "c" ord c

attribute [irreducible] mopOrd

/-- **The search leaf, entered from cells the caller has just zeroed.**

`ScatterSynth.hnr_mop_bfs` asks for `hnCtxt natAssn 0 "i"` and
`hnCtxt natAssn 0 "head"` — the two entry conditions of the synthesized
program — as *literal* zeroes. Inside a turn loop the caller cannot
supply them: the cells arrive holding the previous turn's leftovers, are
zeroed by an operation, and `hnr_bind`'s continuation is attempted at an
**opaque** result value. `hnr_bind` does carry `bind_ref_tag a m`
(`returnT a ≤ m`, which pins `a = 0` for a constant-producing `m`), but
the translate phase never consumes it, so the rule cannot fire. That is
R2D/D-b's tool gap, and §9 is its two-line reproducer.

The fix costs one operation. `mopBfsE` takes the two cells' values as
arguments and `assert`s them zero — P4/D-ed's discipline, one level up:
the entry condition of a whole engine, discharged inside the engine's own
operation. The rule then matches at any values, and the obligation is a
proposition in the abstract layer, where a value theorem discharges it by
`assert_pos`. -/
noncomputable def mopBfsE (i h n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) :
    NRest BfsQ.St ECost :=
  NRest.bindT (NRest.assert (i = 0 ∧ h = 0)) fun _ =>
    ScatterSynth.mopBfs n d src off tgt alv dist₀ q₀

theorem mopBfsE_zero (n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) :
    mopBfsE 0 0 n d src off tgt alv dist₀ q₀
      = ScatterSynth.mopBfs n d src off tgt alv dist₀ q₀ := by
  rw [mopBfsE, NRest.assert_pos ⟨rfl, rfl⟩, NRest.returnT_bindT]

@[sepref_fr_rules]
theorem hnr_mop_bfsE (i h n d src : ℕ) (off tgt alv dist₀ q₀ : List ℕ) :
    hnRefine
      (hnCtxt arrayAssn dist₀ "dist" ∗ hnCtxt arrayAssn q₀ "q" ∗
        hnCtxt natAssn i "i" ∗ hnCtxt natAssn h "head" ∗
        hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
        hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
        hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
        hnCtxt natAssn src "src" ∗ hnCtxt natAssn 1 "one" ∗
        junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
        junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
        junkCell "du")
      BfsQSynth.bfsQSynth_impl
      (junkCell "a" ∗ hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn src "src" ∗
        junkCell "i" ∗ hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
        hnCtxt natAssn n "n" ∗ hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
        hnCtxt natAssn 1 "one" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
        junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
        junkCell "du")
      ("dist", "q", "head", "tl")
      (arrayAssn ×ₐ arrayAssn ×ₐ natAssn ×ₐ natAssn)
      (mopBfsE i h n d src off tgt alv dist₀ q₀) := by
  refine hnr_assert fun hz => ?_
  obtain ⟨rfl, rfl⟩ := hz
  exact ScatterSynth.hnr_mop_bfs n d src off tgt alv dist₀ q₀

attribute [irreducible] mopBfsE

/-! ## 1. The emission scan, abstractly

One slot of the reached list: read the vertex, read its distance, append
it to the cluster arena, and record the centre's position as its
assignment if the vertex is *caught* (within `r`) and nothing has claimed
it yet. The three-way choice is a nested branch on scalars, and the
assignment array is written **once, unconditionally** — the branch
decides only what value goes in. That is what keeps the array out of a
branch merge. -/

/-- The emission scan's state: the slot index into the reached list, the
arena's write pointer, the arena, and the assignment array. -/
abbrev ESt : Type := ℕ × ℕ × List ℕ × List ℕ

/-- The value the assignment array gets: the old one unless the vertex is
caught *and* unclaimed, in which case the centre's position. This is
`RamCover`'s `emitSlot` read as a function — first catches, and it is the
minimality and not the catching that the covering argument consumes. -/
def newAsg (n c s a dz : ℕ) : ℕ := if dz < s then (if a < n then a else c) else a

/-- **One reached vertex.** The else arm of the outer branch repeats the
inner branch with both arms equal, so that a slot costs the same whatever
it does — the cost of the pass is then a function of the *number* of
touched slots and of nothing else, which is the point. -/
noncomputable def emitF (reach dist : List ℕ) (n c s : ℕ) : ESt → NRest ESt ECost := fun t =>
  bindT (mopAget reach t.1) fun u =>
    bindT (mopAget dist u) fun dz =>
      bindT (mopAset t.2.2.1 t.2.1 u) fun X =>
        bindT (mopSucc t.2.1) fun p =>
          bindT (mopAget t.2.2.2 u) fun a =>
            bindT (irIf (decide (dz < s))
                (irIf (decide (a < n)) (mopCopy a) (mopCopy c))
                (irIf (decide (a < n)) (mopCopy a) (mopCopy a))) fun w =>
              bindT (mopAset t.2.2.2 u w) fun A =>
                bindT (mopSucc t.1) fun k =>
                  bindT (mopPair X A) fun r =>
                    bindT (mopPair p r) fun z => mopPair k z

/-- No invariant: the index bounds are discharged inside the operations'
own `assert`s (P4/D-ed) and termination is read off the abstract loop's
non-failure (R0/D-b). -/
def emitI : ESt → Prop := fun _ => True

def emitBf (kend : ℕ) : ESt → Bool := fun t => decide (t.1 < kend)

/-- **The emission scan**, over the reached list and not over the
carrier. -/
noncomputable def emitLoop (reach dist : List ℕ) (n c s kend : ℕ) (t₀ : ESt) :
    NRest ESt ECost :=
  irWhileIT emitI (emitBf kend) (emitF reach dist n c s) t₀

/-! ## 2. The emission scan, synthesized -/

set_option maxHeartbeats 1000000 in
sepref_synth emitSynth (n c s kend xp₀ : ℕ) (reach dist xmem₀ asg₀ : List ℕ) :
  hnRefine (hnCtxt (natAssn ×ₐ natAssn ×ₐ arrayAssn ×ₐ arrayAssn) (0, xp₀, xmem₀, asg₀)
        ("cvk", "xp", "xmem", "asg") ∗
      hnCtxt arrayAssn reach "q" ∗ hnCtxt arrayAssn dist "dist" ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn c "c" ∗ hnCtxt natAssn s "cvs" ∗
      hnCtxt natAssn kend "tl" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "cvu" ∗ junkCell "cvd" ∗ junkCell "cva" ∗ junkCell "cvw")
    _ _ ("cvk", "xp", "xmem", "asg") (natAssn ×ₐ natAssn ×ₐ arrayAssn ×ₐ arrayAssn)
    (emitLoop reach dist n c s kend (0, xp₀, xmem₀, asg₀))

-- The synthesized emission scan, pinned. One `while`, no branch on the
-- array: the assignment cell is written unconditionally and the branch
-- decides only its value.
#guard emitSynth_impl =
  Com.while (Cond.lt (Operand.cell "cvk") (Operand.cell "tl"))
    ((Com.aget "cvu" "q" "cvk").seq
      ((Com.aget "cvd" "dist" "cvu").seq
        ((Com.aset "xmem" "xp" "cvu").seq
          ((Com.binop Lax13Proofs.Imp.Bop.add "xp" "xp" "one").seq
            ((Com.aget "cva" "asg" "cvu").seq
              ((Com.ite (Cond.lt (Operand.cell "cvd") (Operand.cell "cvs"))
                    (Com.ite (Cond.lt (Operand.cell "cva") (Operand.cell "n")) (Com.copy "cvw" "cva")
                      (Com.copy "cvw" "c"))
                    (Com.ite (Cond.lt (Operand.cell "cva") (Operand.cell "n")) (Com.copy "cvw" "cva")
                      (Com.copy "cvw" "cva"))).seq
                ((Com.aset "asg" "cvu" "cvw").seq
                  ((Com.binop Lax13Proofs.Imp.Bop.add "cvk" "cvk" "one").seq
                    (Com.skip.seq (Com.skip.seq Com.skip))))))))))

/-! ## 3. The search leaf, then the emission scan over what it reached

The 2A satellite's probe 2 and T1's acceptance (`T1FriProbe.bfsThenSweep`)
in the shape this file actually needs: the whole synthesized BFS as one
operation, and then a loop that reads **two** components of its bound
result tuple — `dist` for the catch test and `q` for the scan itself —
and whose guard bound is a **third**. Nothing below writes a frame
clause. -/

set_option maxHeartbeats 2000000 in
sepref_synth turnCoreSynth (n d c s src xp₀ : ℕ) (off tgt alv dist₀ q₀ xmem₀ asg₀ : List ℕ) :
  hnRefine
    (hnCtxt arrayAssn dist₀ "dist" ∗ hnCtxt arrayAssn q₀ "q" ∗
      hnCtxt natAssn 0 "i" ∗ hnCtxt natAssn 0 "head" ∗
      hnCtxt arrayAssn off "off" ∗ hnCtxt arrayAssn tgt "tgt" ∗
      hnCtxt arrayAssn alv "alv" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
      hnCtxt natAssn src "src" ∗ hnCtxt natAssn 1 "one" ∗
      junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
      junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
      junkCell "du" ∗
      hnCtxt (natAssn ×ₐ natAssn ×ₐ arrayAssn ×ₐ arrayAssn) (0, xp₀, xmem₀, asg₀)
        ("cvk", "xp", "xmem", "asg") ∗
      hnCtxt natAssn c "c" ∗ hnCtxt natAssn s "cvs" ∗
      junkCell "cvu" ∗ junkCell "cvd" ∗ junkCell "cva" ∗ junkCell "cvw")
    _ _ ("cvk", "xp", "xmem", "asg") (natAssn ×ₐ natAssn ×ₐ arrayAssn ×ₐ arrayAssn)
    (NRest.bindT (ScatterSynth.mopBfs n d src off tgt alv dist₀ q₀) fun st =>
      emitLoop st.2.1 st.1 n c s st.2.2.2 (0, xp₀, xmem₀, asg₀))

/-! ## 4. One turn, and the pass

Ten components of loop state — four counters and six arrays — a whole
engine as a leaf inside the body, and a nested loop after it. This is the
largest composition the tower has been asked for. -/

/-- The turn loop's state: the position counter, the arena's write
pointer, the search's queue head, the emission's slot index, then the
six arrays a turn touches. `dist` and `q` are state and not frame
because the search rewrites them every turn; `head` and the slot index
are state because they have to be zeroed *in place* on re-entry. -/
abbrev CSt : Type :=
  ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ × List ℕ × List ℕ × List ℕ

/-- Assembling the emission scan's start state (P4/D-m: a loop state is a
resource, never a literal tuple). -/
noncomputable def pack4 (k xp : ℕ) (xm ag : List ℕ) : NRest ESt ECost :=
  bindT (mopPair xm ag) fun p => bindT (mopPair xp p) fun p' => mopPair k p'

/-- …and the turn's own, nine pairings deep. -/
noncomputable def packC (c xp hd k : ℕ) (xm ag av xo di qq : List ℕ) : NRest CSt ECost :=
  bindT (mopPair di qq) fun p₁ =>
    bindT (mopPair xo p₁) fun p₂ =>
      bindT (mopPair av p₂) fun p₃ =>
        bindT (mopPair ag p₃) fun p₄ =>
          bindT (mopPair xm p₄) fun p₅ =>
            bindT (mopPair k p₅) fun p₆ =>
              bindT (mopPair hd p₆) fun p₇ =>
                bindT (mopPair xp p₇) fun p₈ => mopPair c p₈

/-- **One centre.** Zero the three entry cells, load the centre, search,
scan `max tl 1` slots of the queue, kill the centre, close the block.

`max tl 1` is `tl + (1 - tl)` at truncated subtraction — two binops — and
it is what makes a *dead* centre emit itself, which is what the baseline
does and what `CoverInv.block` asks for. -/
noncomputable def turnF (ord off tgt : List ℕ) (n d s : ℕ) : CSt → NRest CSt ECost := fun t =>
  bindT mopZeroI fun i0 =>
    bindT (mopZeroIn t.2.2.1) fun h0 =>
      bindT (mopZeroIn t.2.2.2.1) fun k0 =>
        bindT (mopOrd ord t.1) fun src =>
          bindT (mopBfsE i0 h0 n d src off tgt t.2.2.2.2.2.2.1
              t.2.2.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2.2.2) fun st =>
            bindT (mopBinop .sub 1 st.2.2.2) fun z =>
              bindT (mopBinop .add st.2.2.2 z) fun kend =>
                bindT (pack4 k0 t.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1) fun e₀ =>
                  bindT (emitLoop st.2.1 st.1 n t.1 s kend e₀) fun e =>
                    bindT (mopAset t.2.2.2.2.2.2.1 src 0) fun A =>
                      bindT (mopSucc t.1) fun c' =>
                        bindT (mopAset t.2.2.2.2.2.2.2.1 c' e.2.1) fun XO =>
                          packC c' e.2.1 st.2.2.1 e.1 e.2.2.1 e.2.2.2 A XO st.1 st.2.1

def coverI : CSt → Prop := fun _ => True

def coverBf (n : ℕ) : CSt → Bool := fun t => decide (t.1 < n)

/-- **The cover pass**, minus the one-time assignment fill (R2D/D-d). -/
noncomputable def coverLoop (ord off tgt : List ℕ) (n d s : ℕ) (t₀ : CSt) : NRest CSt ECost :=
  irWhileIT coverI (coverBf n) (turnF ord off tgt n d s) t₀

/-- The caller's ownership, named. -/
def coverPre (n d s : ℕ) (ord off tgt : List ℕ) (t₀ : CSt) : Assn :=
  hnCtxt (natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
      arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn) t₀
      ("c", "xp", "head", "cvk", "xmem", "asg", "alv", "xoff", "dist", "q") ∗
    hnCtxt arrayAssn ord "ord" ∗ hnCtxt arrayAssn off "off" ∗
    hnCtxt arrayAssn tgt "tgt" ∗
    hnCtxt natAssn n "n" ∗ hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
    hnCtxt natAssn s "cvs" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "cvz" ∗
    junkCell "i" ∗ junkCell "src" ∗
    junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
    junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
    junkCell "du" ∗
    junkCell "cvu" ∗ junkCell "cvd" ∗ junkCell "cva" ∗ junkCell "cvw" ∗
    junkCell "cvm" ∗ junkCell "cve"

set_option maxHeartbeats 4000000 in
sepref_synth coverSynth (n d s : ℕ) (ord off tgt : List ℕ) (t₀ : CSt) :
  hnRefine
    (hnCtxt (natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
        arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn) t₀
        ("c", "xp", "head", "cvk", "xmem", "asg", "alv", "xoff", "dist", "q") ∗
      hnCtxt arrayAssn ord "ord" ∗ hnCtxt arrayAssn off "off" ∗
      hnCtxt arrayAssn tgt "tgt" ∗
      hnCtxt natAssn n "n" ∗ hnCtxt natAssn (d + 1) "sent" ∗ hnCtxt natAssn d "d" ∗
      hnCtxt natAssn s "cvs" ∗ hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "cvz" ∗
      junkCell "i" ∗ junkCell "src" ∗
      junkCell "a" ∗ junkCell "tl" ∗ junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗
      junkCell "k0" ∗ junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
      junkCell "du" ∗
      junkCell "cvu" ∗ junkCell "cvd" ∗ junkCell "cva" ∗ junkCell "cvw" ∗
      junkCell "cvm" ∗ junkCell "cve")
    _ _ ("c", "xp", "head", "cvk", "xmem", "asg", "alv", "xoff", "dist", "q")
    (natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
      arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn)
    (coverLoop ord off tgt n d s t₀)

-- The synthesized pass, pinned. The turn loop, the three zeroings, the
-- centre load, the whole search as one block, the two binops that give
-- `max tl 1`, the emission scan, the kill and the block close.
#guard coverSynth_impl =
  Com.while (Cond.lt (Operand.cell "c") (Operand.cell "n"))
    ((Com.const "i" 0).seq
      ((Com.binop Lax13Proofs.Imp.Bop.mul "head" "head" "cvz").seq
        ((Com.binop Lax13Proofs.Imp.Bop.mul "cvk" "cvk" "cvz").seq
          ((Com.aget "src" "ord" "c").seq
            (BfsQSynth.bfsQSynth_impl.seq
              ((Com.binop Lax13Proofs.Imp.Bop.sub "a" "one" "tl").seq
                ((Com.binop Lax13Proofs.Imp.Bop.add "i" "tl" "a").seq
                  ((Com.skip.seq (Com.skip.seq Com.skip)).seq
                    ((Com.while (Cond.lt (Operand.cell "cvk") (Operand.cell "i"))
                          ((Com.aget "v" "q" "cvk").seq
                            ((Com.aget "dv" "dist" "v").seq
                              ((Com.aset "xmem" "xp" "v").seq
                                ((Com.binop Lax13Proofs.Imp.Bop.add "xp" "xp" "one").seq
                                  ((Com.aget "dv1" "asg" "v").seq
                                    ((Com.ite (Cond.lt (Operand.cell "dv") (Operand.cell "cvs"))
                                          (Com.ite (Cond.lt (Operand.cell "dv1") (Operand.cell "n"))
                                            (Com.copy "k0" "dv1") (Com.copy "k0" "c"))
                                          (Com.ite (Cond.lt (Operand.cell "dv1") (Operand.cell "n"))
                                            (Com.copy "k0" "dv1") (Com.copy "k0" "dv1"))).seq
                                      ((Com.aset "asg" "v" "k0").seq
                                        ((Com.binop Lax13Proofs.Imp.Bop.add "cvk" "cvk" "one").seq
                                          (Com.skip.seq (Com.skip.seq Com.skip))))))))))).seq
                      ((Com.aset "alv" "src" "cvz").seq
                        ((Com.binop Lax13Proofs.Imp.Bop.add "c" "c" "one").seq
                          ((Com.aset "xoff" "c" "xp").seq
                            (Com.skip.seq
                              (Com.skip.seq
                                (Com.skip.seq
                                  (Com.skip.seq
                                    (Com.skip.seq (Com.skip.seq (Com.skip.seq (Com.skip.seq Com.skip))))))))))))))))))))

/-! ## 5. What the emission scan computes, and what it costs

The acceptance criterion of the wave. `emitLoopCost` is a function of the
**number of touched slots** and of nothing else: it does not take `n`, it
does not take the carrier, it does not take the number of turns. That is
`TrailRecursion`'s `clusterCost` one engine up, and it is the shape the
`Σ_c |X_c| ≤ n^{1+δ}` budget is spent against. -/

/-- One slot, as a function. -/
def emitStep (reach dist : List ℕ) (n c s : ℕ) (t : ESt) : ESt :=
  (t.1 + 1, t.2.1 + 1, t.2.2.1.set t.2.1 reach[t.1]!,
    t.2.2.2.set reach[t.1]! (newAsg n c s t.2.2.2[reach[t.1]!]! dist[reach[t.1]!]!))

/-- `j` slots. -/
def emitRun (reach dist : List ℕ) (n c s : ℕ) : ℕ → ESt → ESt
  | 0, t => t
  | j + 1, t => emitRun reach dist n c s j (emitStep reach dist n c s t)

/-- **One slot's price.** Three array reads, two array writes, two
increments, the branch — two `ite`s and one `copy`, the same whichever
way it goes — and the three tuple steps. No `n`, no carrier. -/
noncomputable def emitStepCost : ECost :=
  irUnit Currency.aget + irUnit Currency.aget + irUnit Currency.aset +
    irUnit Currency.add + irUnit Currency.aget + irUnit Currency.copy +
    irUnit Currency.ite + irUnit Currency.ite + irUnit Currency.aset +
    irUnit Currency.add + irUnit Currency.skip + irUnit Currency.skip +
    irUnit Currency.skip

/-- The branch, priced: it costs the same whatever it decides, which is
what makes the pass's price a function of the touch count alone. -/
theorem pick_eq (n c s a dz : ℕ) :
    (irIf (decide (dz < s)) (irIf (decide (a < n)) (mopCopy a) (mopCopy c))
        (irIf (decide (a < n)) (mopCopy a) (mopCopy a)))
      = NRest.consume (NRest.returnT (newAsg n c s a dz))
          (irUnit Currency.ite + (irUnit Currency.ite + irUnit Currency.copy)) := by
  by_cases hs : dz < s <;> by_cases ha : a < n <;>
    simp [irIf, newAsg, hs, ha, mopCopy_def, NRest.consume_consume]

theorem emitF_eq (reach dist : List ℕ) (n c s : ℕ) (t : ESt)
    (h1 : t.1 < reach.length) (h2 : reach[t.1]! < dist.length)
    (h3 : t.2.1 < t.2.2.1.length) (h4 : reach[t.1]! < t.2.2.2.length) :
    emitF reach dist n c s t
      = NRest.consume (NRest.returnT (emitStep reach dist n c s t)) emitStepCost := by
  show NRest.bindT (mopAget reach t.1) _ = _
  simp only [mopAget_def, mopAset_def, mopSucc_eq, mopBinop_def, mopPair_def,
    NRest.assert_pos h1, NRest.assert_pos h2, NRest.assert_pos h3, NRest.assert_pos h4,
    NRest.returnT_bindT, bindT_unitT, pick_eq, NRest.consume_consume,
    Lax13Proofs.Imp.Bop.apply_add, binopCurrency_add, emitStep, emitStepCost]
  congr 1
  ac_rfl

/-- **The scan's price**: one slot and one guard evaluation per touch,
plus the exit's guard. -/
noncomputable def emitLoopCost (j : ℕ) : ECost :=
  j • emitStepCost + (j + 1) • irUnit Currency.«while»

theorem emitRun_index (reach dist : List ℕ) (n c s : ℕ) :
    ∀ (j : ℕ) (t : ESt), (emitRun reach dist n c s j t).1 = t.1 + j := by
  intro j
  induction j with
  | zero => intro t; simp [emitRun]
  | succ j ih => intro t; rw [emitRun, ih]; show t.1 + 1 + j = t.1 + (j + 1); omega

theorem emitRun_arena_len (reach dist : List ℕ) (n c s : ℕ) :
    ∀ (j : ℕ) (t : ESt), (emitRun reach dist n c s j t).2.2.1.length = t.2.2.1.length := by
  intro j
  induction j with
  | zero => intro t; simp [emitRun]
  | succ j ih => intro t; rw [emitRun, ih]; show (t.2.2.1.set _ _).length = _; simp

theorem emitRun_asg_len (reach dist : List ℕ) (n c s : ℕ) :
    ∀ (j : ℕ) (t : ESt), (emitRun reach dist n c s j t).2.2.2.length = t.2.2.2.length := by
  intro j
  induction j with
  | zero => intro t; simp [emitRun]
  | succ j ih => intro t; rw [emitRun, ih]; show (t.2.2.2.set _ _).length = _; simp

theorem emitRun_ptr (reach dist : List ℕ) (n c s : ℕ) :
    ∀ (j : ℕ) (t : ESt), (emitRun reach dist n c s j t).2.1 = t.2.1 + j := by
  intro j
  induction j with
  | zero => intro t; simp [emitRun]
  | succ j ih => intro t; rw [emitRun, ih]; show t.2.1 + 1 + j = t.2.1 + (j + 1); omega

/-- **The scan's value and price.** `j` touches, at a price with no
carrier in it. -/
theorem emitLoop_value (reach dist : List ℕ) (n c s : ℕ) :
    ∀ (j : ℕ) (t : ESt),
      (∀ k, t.1 ≤ k → k < t.1 + j → k < reach.length ∧ reach[k]! < dist.length ∧
        reach[k]! < t.2.2.2.length) →
      t.2.1 + j ≤ t.2.2.1.length →
      emitLoop reach dist n c s (t.1 + j) t
        = NRest.consume (NRest.returnT (emitRun reach dist n c s j t)) (emitLoopCost j) := by
  intro j
  induction j with
  | zero =>
    intro t _ _
    have hb : emitBf (t.1 + 0) t = false := by simp [emitBf]
    show irWhileIT emitI (emitBf (t.1 + 0)) (emitF reach dist n c s) t = _
    rw [irWhileIT_of_false (show emitI t from trivial) hb]
    congr 1
    simp [emitLoopCost]
  | succ j ih =>
    intro t hmem hptr
    have hb : emitBf (t.1 + (j + 1)) t = true := by simp [emitBf]
    obtain ⟨h1, h2, h4⟩ := hmem t.1 (le_refl _) (by omega)
    have h3 : t.2.1 < t.2.2.1.length := by omega
    have hstep : t.1 + (j + 1) = (emitStep reach dist n c s t).1 + j := by
      show t.1 + (j + 1) = t.1 + 1 + j; omega
    show irWhileIT emitI (emitBf (t.1 + (j + 1))) (emitF reach dist n c s) t = _
    rw [irWhileIT_of_true (show emitI t from trivial) hb,
      emitF_eq reach dist n c s t h1 h2 h3 h4, bindT_unitT, hstep]
    show NRest.consume (NRest.consume (emitLoop reach dist n c s
      ((emitStep reach dist n c s t).1 + j) (emitStep reach dist n c s t)) emitStepCost) _ = _
    have hmem' : ∀ k, (emitStep reach dist n c s t).1 ≤ k →
        k < (emitStep reach dist n c s t).1 + j →
        k < reach.length ∧ reach[k]! < dist.length ∧
          reach[k]! < (emitStep reach dist n c s t).2.2.2.length := by
      intro k hk hk'
      have hk₁ : t.1 + 1 ≤ k := hk
      have hk₂ : k < t.1 + 1 + j := hk'
      obtain ⟨e₁, e₂, e₃⟩ := hmem k (by omega) (by omega)
      refine ⟨e₁, e₂, ?_⟩
      show reach[k]! < (t.2.2.2.set _ _).length
      simpa using e₃
    have hptr' : (emitStep reach dist n c s t).2.1 + j
        ≤ (emitStep reach dist n c s t).2.2.1.length := by
      show t.2.1 + 1 + j ≤ (t.2.2.1.set _ _).length
      simp only [List.length_set]
      omega
    rw [ih (emitStep reach dist n c s t) hmem' hptr', NRest.consume_consume,
      NRest.consume_consume, emitRun]
    congr 1
    all_goals first
      | rfl
      | (simp only [emitLoopCost, succ_nsmul]; abel)

/-! ## 6. The acceptance criterion — the cost is touched-only

`emitLoopCost` re-read as `touches • emitUnit + one`. `emitUnit` is a
constant: it mentions neither the carrier, nor the arena, nor the centre,
nor the turn count. There is no `n · turns` term because there is no
`n`. -/

/-- **The price of one touch**: the slot's own work and the guard
evaluation that carried it. -/
noncomputable def emitUnit : ECost := emitStepCost + irUnit Currency.«while»

/-- **The characteristic theorem.** -/
theorem emitCost_touched_only (j : ℕ) :
    emitLoopCost j = j • emitUnit + irUnit Currency.«while» := by
  simp only [emitLoopCost, emitUnit, smul_add, succ_nsmul]
  abel

/-! ### 6.1 The same theorem at three currencies

Sharpest form. The emission's **array writes** are exactly two per
touched slot — one arena cell and one assignment cell — and its **array
reads** exactly three. The carrier size does not appear in the formula at
all. -/

theorem emitUnit_aset : emitUnit.toFun Currency.aset = 2 := by decide +kernel

theorem emitUnit_aget : emitUnit.toFun Currency.aget = 3 := by decide +kernel

theorem emitUnit_while : emitUnit.toFun Currency.«while» = 1 := by decide +kernel

theorem irUnit_while_aset : (irUnit Currency.«while»).toFun Currency.aset = 0 := by
  decide +kernel

theorem emitCost_aset (j : ℕ) : (emitLoopCost j).toFun Currency.aset = 2 * j := by
  rw [emitCost_touched_only, ACost.toFun_add, ACost.toFun_nsmul, emitUnit_aset,
    irUnit_while_aset]
  simp [mul_comm]

/-! ### 6.2 The carrier does not enter

`emitLoopCost` has no `n` argument, so "the same reached list costs the
same at every carrier size" is a reading of its signature and not a
theorem. What *is* a theorem is the same fact about two **runs**, which
do mention their carriers. -/

set_option linter.unusedVariables false in
/-- Two runs of the scan, at carriers of wildly different sizes, over the
same reached list — same price. -/
theorem emitLoop_cost_carrier_free (n₁ n₂ c₁ c₂ s : ℕ) (reach dist : List ℕ) (j : ℕ)
    (t₁ t₂ : ESt) (ha : t₁.1 = t₂.1)
    (hm₁ : ∀ k, t₁.1 ≤ k → k < t₁.1 + j → k < reach.length ∧ reach[k]! < dist.length ∧
      reach[k]! < t₁.2.2.2.length)
    (hp₁ : t₁.2.1 + j ≤ t₁.2.2.1.length)
    (hm₂ : ∀ k, t₂.1 ≤ k → k < t₂.1 + j → k < reach.length ∧ reach[k]! < dist.length ∧
      reach[k]! < t₂.2.2.2.length)
    (hp₂ : t₂.2.1 + j ≤ t₂.2.2.1.length) :
    ∃ cost : ECost,
      emitLoop reach dist n₁ c₁ s (t₁.1 + j) t₁
          = NRest.consume (NRest.returnT (emitRun reach dist n₁ c₁ s j t₁)) cost ∧
        emitLoop reach dist n₂ c₂ s (t₂.1 + j) t₂
          = NRest.consume (NRest.returnT (emitRun reach dist n₂ c₂ s j t₂)) cost :=
  ⟨emitLoopCost j, emitLoop_value reach dist n₁ c₁ s j t₁ hm₁ hp₁,
    emitLoop_value reach dist n₂ c₂ s j t₂ hm₂ hp₂⟩

/-! ### 6.3 The negative control, as a theorem

Not "the baseline is worse on this input" but "the baseline's emission
has **no** bound of the touched-only shape". `RamCover.emitLoop` is a
flat pass over the carrier, so it performs `n` array reads per turn
whatever the reached set is; the tower's performs `3` per *touch*. A
touched-only bound is `c₁ · touches + c₂ · turns + c₃` for constants
fixed before the input, and for every such triple there is a carrier and
a family of turns that breaks it. The family is the honest one:
single-vertex reached sets, so `touches = turns` and the tower's own
count `3 · touches` is of the shape with `c₁ = 3`. -/

set_option linter.unusedVariables false in
/-- The baseline's array reads: one distance read per carrier vertex per
turn (`RamCover.emitSlot`'s `.get "dist" (.var "z")`). -/
def flatEmitAgets (n turns touches : ℕ) : ℕ := turns * n

set_option linter.unusedVariables false in
/-- The tower's, as a function of the same three numbers — and `n` is not
among the ones it uses. -/
def towerEmitAgets (n turns touches : ℕ) : ℕ := 3 * touches

theorem towerEmitAgets_eq (n turns j : ℕ) :
    (emitLoopCost j).toFun Currency.aget = towerEmitAgets n turns j := by
  rw [emitCost_touched_only, ACost.toFun_add, ACost.toFun_nsmul, emitUnit_aget,
    show (irUnit Currency.«while»).toFun Currency.aget = 0 from by decide +kernel]
  simp [towerEmitAgets, mul_comm]

theorem flat_no_touched_only_bound (c₁ c₂ c₃ : ℕ) :
    ∃ n turns : ℕ, 0 < n ∧
      ¬ (flatEmitAgets n turns turns ≤ c₁ * turns + c₂ * turns + c₃) := by
  refine ⟨c₁ + c₂ + 2, c₃ + 1, by omega, fun h => ?_⟩
  rw [flatEmitAgets] at h
  have e : (c₃ + 1) * (c₁ + c₂ + 2)
      = (c₁ * (c₃ + 1) + c₂ * (c₃ + 1)) + 2 * (c₃ + 1) := by ring
  rw [e] at h
  generalize c₁ * (c₃ + 1) = A at h
  generalize c₂ * (c₃ + 1) = B at h
  omega

/-- …and the positive counterpart, on the same family. -/
theorem tower_touched_only_bound (n turns : ℕ) :
    towerEmitAgets n turns turns ≤ 3 * turns + 0 * turns + 0 :=
  le_of_eq (by simp [towerEmitAgets])

-- On a carrier of 5 with 5 single-vertex turns: ours 15, the baseline's 25 …
#guard towerEmitAgets 5 5 5 = 15
#guard flatEmitAgets 5 5 5 = 25
-- … and at carrier 5000, with the *same* turns and the same touches,
-- ours is unchanged and the baseline's is a thousand times worse. This
-- is the `16n²` item, in one line.
#guard towerEmitAgets 5000 5 5 = 15
#guard flatEmitAgets 5000 5 5 = 25000

/-! ## 7. Gate — the *synthesized* pass, run against the baseline's own
worked example (refute before prove)

`RamCover.Demo` publishes four `#guard`ed runs of the baseline program on
the path `0—1—2—3` with an isolated vertex `4`, at two settings of the
mask and three radii. Here the **synthesized** `Ir.Com` of §4 is
evaluated by `Ir/Semantics.lean`'s own evaluator on the same arena, and
its three answers — the block offsets, the arena, the assignments — are
checked against those same numbers, cell for cell.

This is the differential test the reached-list rewrite needs: a scan of
the queue that missed a vertex, or a dead centre that emitted nothing,
or a catch test in the wrong direction, all show up here before any
proof is attempted. §7.2 turns each of those three into a negative
control. -/

section Gate

/-- The demo arena: `RamCover.Demo`'s, as lists. -/
def gOff : List ℕ := [0, 1, 3, 5, 6, 6]

def gTgt : List ℕ := [1, 0, 2, 1, 3, 2]

def gAlv (a2 : ℕ) : List ℕ := [1, 1, a2, 1, 1]

def gOrd : List ℕ := [0, 1, 2, 3, 4]

/-- The pass's entry store: the assignment array already carries the
sentinel `n = 5` (R2D/D-d: the fill is the one-time `O(n)` charge and is
not re-derived), the arena is empty, and every scratch cell is zero. -/
def gState (a2 r : ℕ) : Ir.State :=
  Ir.State.ofPairs
    [("c", 0), ("xp", 0), ("head", 0), ("cvk", 0), ("n", 5), ("sent", 2 * r + 1),
      ("d", 2 * r), ("cvs", r + 1), ("one", 1), ("cvz", 0), ("i", 0), ("src", 0),
      ("a", 0), ("tl", 0), ("v", 0), ("dv", 0), ("dv1", 0), ("k0", 0), ("v1", 0),
      ("kend", 0), ("u", 0), ("au", 0), ("du", 0), ("cvu", 0), ("cvd", 0), ("cva", 0),
      ("cvw", 0), ("cvm", 0), ("cve", 0)]
    [("xmem", List.replicate 25 0), ("asg", List.replicate 5 5),
      ("alv", gAlv a2), ("xoff", List.replicate 6 0),
      ("dist", List.replicate 5 0), ("q", List.replicate 5 0),
      ("ord", gOrd), ("off", gOff), ("tgt", gTgt)]

/-- The three answers, in `RamCover.Demo`'s own reporting order: six
block offsets, the first ten arena cells, five assignments. -/
def gRun (a2 r : ℕ) : Option (List ℕ) :=
  (Ir.evalFuel 200000 coverSynth_impl (gState a2 r)).bind fun p =>
    match p.1.arrs "xoff", p.1.arrs "xmem", p.1.arrs "asg" with
    | some xo, some xm, some ag => some (xo ++ xm.take 10 ++ ag)
    | _, _, _ => none

/-! ### 7.1 The four published answers, reproduced

Each of the four is `RamCover.Demo`'s `#guard`ed list with the cycle
count dropped — the programs are different, so the cycle counts are
different, and the *answers* are not. -/

-- radius `1`: the fibres `{0,1,2} | {1,2,3} | {2,3} | {3} | {4}`, and the
-- first catches `0 0 1 2 4`
#guard gRun 1 1 = some [0, 3, 6, 8, 9, 10, 0, 1, 2, 1, 2, 3, 2, 3, 3, 4, 0, 0, 1, 2, 4]
-- with vertex `2` dead the arena is the edge `0—1` and three isolated
-- vertices, so every cluster but the first is a singleton — **including
-- the dead centre's own**, which is what `max tl 1` is for
#guard gRun 0 1 = some [0, 2, 3, 4, 5, 6, 0, 1, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 2, 3, 4]
-- at radius `0` weak reachability is equality
#guard gRun 1 0 = some [0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4]
-- and at radius `2` the first cluster swallows the whole path
#guard gRun 1 2 = some [0, 4, 7, 9, 10, 11, 0, 1, 2, 3, 1, 2, 3, 2, 3, 3, 0, 0, 0, 1, 4]

/-! ### 7.2 Negative controls

Three, one per way the reached-list rewrite can be got wrong. All three
are checks the build runs. -/

-- **The mask is load-bearing.** Killing vertex `2` changes the answer, so
-- a run that ignored the mask would be caught.
/--
error: Expression
  decide (gRun 0 1 = some [0, 3, 6, 8, 9, 10, 0, 1, 2, 1, 2, 3, 2, 3, 3, 4, 0, 0, 1, 2, 4])
did not evaluate to `true`
-/
#guard_msgs in
#guard gRun 0 1 = some [0, 3, 6, 8, 9, 10, 0, 1, 2, 1, 2, 3, 2, 3, 3, 4, 0, 0, 1, 2, 4]

-- **The catch radius is `r`, not `2r`.** Recording first catches at the
-- cluster radius would give `0 0 0 1 4` at radius `1` — the radius-`2`
-- answer — and it does not.
/--
error: Expression
  decide (gRun 1 1 = some [0, 3, 6, 8, 9, 10, 0, 1, 2, 1, 2, 3, 2, 3, 3, 4, 0, 0, 0, 1, 4])
did not evaluate to `true`
-/
#guard_msgs in
#guard gRun 1 1 = some [0, 3, 6, 8, 9, 10, 0, 1, 2, 1, 2, 3, 2, 3, 3, 4, 0, 0, 0, 1, 4]

-- **A dead centre still owns a block.** Without the `max tl 1` slot the
-- third block would be empty and every later offset one lower; that is
-- the answer below, and it is refuted.
/--
error: Expression
  decide (gRun 0 1 = some [0, 2, 3, 3, 4, 5, 0, 1, 1, 3, 4, 0, 0, 0, 0, 0, 0, 0, 2, 3, 4])
did not evaluate to `true`
-/
#guard_msgs in
#guard gRun 0 1 = some [0, 2, 3, 3, 4, 5, 0, 1, 1, 3, 4, 0, 0, 0, 0, 0, 0, 0, 2, 3, 4]

/-! ### 7.3 The debt, checked

`ReachedList` (§8) is the clause the tower's BFS export does not carry.
It is not assumed here: the four runs above *are* its test, because a
reached list that missed a vertex within `2r`, or listed one twice, would
move the arena. §7.1's agreement with the baseline — whose emission tests
`dist[z] ≤ 2r` at **every** carrier vertex and therefore cannot miss one
— is exactly the statement that the queue prefix is the fibre, on this
arena, at four settings. -/

end Gate

/-! ## 8. The bridge to `RamCover`'s vocabulary

What the turn owes `RamCover.CoverInv.step` is two of its hypotheses:
`hblock`, which says the slots the turn wrote are the vertices within
`2r`, and `hasg`, which says the assignment array took first catches.
Both are statements about `emitRun` — the scan's own value function — and
both need one fact about the search that the tower's export does not
supply. -/

/-- **The clause the BFS export is missing** (R2D/D-c). `BfsQSynth.bfsQS_correct`
specifies the distance array (`BfsQ.QPost`) and says nothing whatever
about the queue. Reading the reached list off `q` needs exactly this:
the first `max tl 1` slots of the queue list the vertices the search put
within the cap, each once.

It is true — the drain pushes a vertex exactly when its distance is still
the sentinel, and `q[0] = src` is written before the drain starts, which
is why a dead centre's single slot is right — and it is *checked* on
every run of §7. It is not proved, because proving it is a re-derivation
of `BfsQ`'s invariant with the queue in it, which is a wave in the BFS
and not in the cover. Everything below takes it as a hypothesis; nothing
below is `sorry`ed. -/
def ReachedList (n d : ℕ) (D reach : List ℕ) (tl : ℕ) : Prop :=
  (∀ k < max tl 1, reach[k]! < n) ∧
    (∀ k < max tl 1, ∀ k' < max tl 1, reach[k]! = reach[k']! → k = k') ∧
    (∀ w < n, D[w]! ≤ d ↔ ∃ k < max tl 1, reach[k]! = w)

/-- The arena cells a scan of `j` slots writes: slot `k` of the reached
list lands at arena cell `t.2.1 + k`, and nothing below the entering
write pointer moves. -/
theorem emitRun_arena (reach dist : List ℕ) (n c s : ℕ) :
    ∀ (j : ℕ) (t : ESt), t.2.1 + j ≤ t.2.2.1.length →
      (∀ p < t.2.1, (emitRun reach dist n c s j t).2.2.1[p]! = t.2.2.1[p]!) ∧
        (∀ k < j, (emitRun reach dist n c s j t).2.2.1[t.2.1 + k]! = reach[t.1 + k]!) := by
  intro j
  induction j with
  | zero => intro t _; exact ⟨fun p _ => by rw [emitRun], fun k hk => absurd hk (by omega)⟩
  | succ j ih =>
    intro t hlen
    have hlt : t.2.1 < t.2.2.1.length := by omega
    have hstep : (emitStep reach dist n c s t).2.1 = t.2.1 + 1 := rfl
    have hlen' : (emitStep reach dist n c s t).2.1 + j
        ≤ (emitStep reach dist n c s t).2.2.1.length := by
      rw [hstep]
      show t.2.1 + 1 + j ≤ (t.2.2.1.set _ _).length
      simp only [List.length_set]; omega
    obtain ⟨ih₁, ih₂⟩ := ih (emitStep reach dist n c s t) hlen'
    have hset : ∀ p, p ≠ t.2.1 → (emitStep reach dist n c s t).2.2.1[p]! = t.2.2.1[p]! := by
      intro p hp
      show (t.2.2.1.set t.2.1 _)[p]! = _
      rw [BfsQ.get!_set t.2.2.1 t.2.1 _ p hlt, if_neg hp]
    have hhit : (emitStep reach dist n c s t).2.2.1[t.2.1]! = reach[t.1]! := by
      show (t.2.2.1.set t.2.1 _)[t.2.1]! = _
      rw [BfsQ.get!_set t.2.2.1 t.2.1 _ t.2.1 hlt, if_pos rfl]
    rw [emitRun]
    constructor
    · intro p hp
      rw [ih₁ p (by rw [hstep]; omega), hset p (by omega)]
    · intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hk₀
      · rw [show t.2.1 + 0 = (emitStep reach dist n c s t).2.1 - 1 by rw [hstep]; omega]
        rw [show (emitStep reach dist n c s t).2.1 - 1 = t.2.1 by rw [hstep]; omega]
        rw [ih₁ t.2.1 (by rw [hstep]; omega), hhit, Nat.add_zero]
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have := ih₂ k' (by omega)
        rw [hstep] at this
        rw [show t.2.1 + (k' + 1) = t.2.1 + 1 + k' by omega, this,
          show (emitStep reach dist n c s t).1 = t.1 + 1 from rfl,
          show t.1 + (k' + 1) = t.1 + 1 + k' by omega]

/-- **`CoverInv.step`'s block hypothesis, off the scan.** The slots the
turn filled hold exactly the vertices the search put within the cap —
which, by `RamCover.masked_step` and the fibre bridge, is exactly the
centre's cluster. -/
theorem emitRun_block (reach dist : List ℕ) (n c s tl : ℕ) (d : ℕ) (t : ESt)
    (hk : t.1 = 0) (hj : max tl 1 = t.2.1 + (max tl 1) - t.2.1)
    (hlen : t.2.1 + max tl 1 ≤ t.2.2.1.length)
    (hR : ReachedList n d dist reach tl) (w : ℕ) :
    (∃ p, t.2.1 ≤ p ∧ p < t.2.1 + max tl 1 ∧
        (emitRun reach dist n c s (max tl 1) t).2.2.1[p]! = w)
      ↔ (w < n ∧ dist[w]! ≤ d) := by
  obtain ⟨hlt, -, hiff⟩ := hR
  obtain ⟨-, harena⟩ := emitRun_arena reach dist n c s (max tl 1) t hlen
  constructor
  · rintro ⟨p, hp₁, hp₂, hp₃⟩
    obtain ⟨k, rfl⟩ : ∃ k, p = t.2.1 + k := ⟨p - t.2.1, by omega⟩
    have hkk : k < max tl 1 := by omega
    rw [harena k hkk, hk, Nat.zero_add] at hp₃
    exact ⟨hp₃ ▸ hlt k hkk, (hiff w (hp₃ ▸ hlt k hkk)).2 ⟨k, hkk, hp₃⟩⟩
  · rintro ⟨hw, hd⟩
    obtain ⟨k, hkk, hkw⟩ := (hiff w hw).1 hd
    exact ⟨t.2.1 + k, by omega, by omega, by rw [harena k hkk, hk, Nat.zero_add]; exact hkw⟩

/-- **What the scan leaves in the assignment array.** A vertex the scan
touched holds `newAsg` of what it held on entry; a vertex it did not
touch is untouched. The injectivity conjunct of `ReachedList` is what
makes the first clause a statement about the *entering* array: a vertex
appears on the reached list once, so its cell is written once. -/
theorem emitRun_asg (reach dist : List ℕ) (n c s : ℕ) :
    ∀ (j : ℕ) (t : ESt), (∀ k < j, reach[t.1 + k]! < t.2.2.2.length) →
      (∀ k < j, ∀ k' < j, reach[t.1 + k]! = reach[t.1 + k']! → k = k') →
      ∀ w, (emitRun reach dist n c s j t).2.2.2[w]!
        = if ∃ k < j, reach[t.1 + k]! = w
          then newAsg n c s t.2.2.2[w]! dist[w]! else t.2.2.2[w]! := by
  intro j
  induction j with
  | zero =>
    intro t _ _ w
    rw [emitRun, if_neg (by rintro ⟨k, hk, -⟩; omega)]
  | succ j ih =>
    intro t hlen hinj w
    have hu : reach[t.1 + 0]! = reach[t.1]! := by rw [Nat.add_zero]
    have hlt : reach[t.1]! < t.2.2.2.length := by
      have := hlen 0 (by omega); rwa [hu] at this
    have hone : (emitStep reach dist n c s t).1 = t.1 + 1 := rfl
    have hstep : ∀ p, (emitStep reach dist n c s t).2.2.2[p]!
        = if p = reach[t.1]! then newAsg n c s t.2.2.2[reach[t.1]!]! dist[reach[t.1]!]!
          else t.2.2.2[p]! := by
      intro p
      show (t.2.2.2.set reach[t.1]! _)[p]! = _
      rw [BfsQ.get!_set t.2.2.2 reach[t.1]! _ p hlt]
    have hlen' : ∀ k < j, reach[(emitStep reach dist n c s t).1 + k]!
        < (emitStep reach dist n c s t).2.2.2.length := by
      intro k hk
      rw [hone, show t.1 + 1 + k = t.1 + (k + 1) by omega]
      show reach[t.1 + (k + 1)]! < (t.2.2.2.set _ _).length
      simpa using hlen (k + 1) (by omega)
    have hinj' : ∀ k < j, ∀ k' < j,
        reach[(emitStep reach dist n c s t).1 + k]!
          = reach[(emitStep reach dist n c s t).1 + k']! → k = k' := by
      intro k hk k' hk' he
      rw [hone, show t.1 + 1 + k = t.1 + (k + 1) by omega,
        show t.1 + 1 + k' = t.1 + (k' + 1) by omega] at he
      have := hinj (k + 1) (by omega) (k' + 1) (by omega) he
      omega
    rw [emitRun, ih (emitStep reach dist n c s t) hlen' hinj' w, hone]
    by_cases hA : ∃ k < j, reach[t.1 + 1 + k]! = w
    · obtain ⟨k, hk, hkw⟩ := hA
      have hne : w ≠ reach[t.1]! := by
        intro he
        have : reach[t.1 + 0]! = reach[t.1 + (k + 1)]! := by
          rw [hu, ← he, ← hkw, show t.1 + (k + 1) = t.1 + 1 + k by omega]
        exact absurd (hinj 0 (by omega) (k + 1) (by omega) this) (by omega)
      rw [if_pos ⟨k, hk, hkw⟩, if_pos ⟨k + 1, by omega, by
          rw [show t.1 + (k + 1) = t.1 + 1 + k by omega]; exact hkw⟩,
        hstep w, if_neg hne]
    · rw [if_neg hA, hstep w]
      by_cases hw : w = reach[t.1]!
      · rw [if_pos hw, if_pos ⟨0, by omega, by rw [hu, hw]⟩, hw]
      · rw [if_neg hw, if_neg]
        rintro ⟨k, hk, hkw⟩
        rcases Nat.eq_zero_or_pos k with rfl | hk₀
        · exact hw (by rw [← hkw, hu])
        · exact hA ⟨k - 1, by omega, by rw [show t.1 + 1 + (k - 1) = t.1 + k by omega]; exact hkw⟩

/-- **`CoverInv.step`'s assignment hypothesis, off the scan.** Verbatim
`RamCover.CoverInv.step`'s `hasg`, with the catch radius `r` where the
program holds `s = r + 1` and the cap `d` where it holds `2r`: a recorded
assignment stands, an unrecorded one takes the centre's position exactly
when the centre catches the vertex, and the sentinel survives otherwise.

The three hypotheses are the pass's own invariant read at the turn's
entry (`RamCover.CoverInv.asg_le`), the search's cap being at least the
catch radius, and the debt. -/
theorem emitRun_hasg (reach dist : List ℕ) (n c r d tl : ℕ) (t : ESt)
    (hk : t.1 = 0) (hrd : r ≤ d) (hR : ReachedList n d dist reach tl)
    (hle : ∀ w < n, t.2.2.2[w]! ≤ n)
    (hlen : ∀ k < max tl 1, reach[k]! < t.2.2.2.length) :
    ∀ w < n, (emitRun reach dist n c (r + 1) (max tl 1) t).2.2.2[w]!
      = if t.2.2.2[w]! < n then t.2.2.2[w]! else if dist[w]! ≤ r then c else n := by
  obtain ⟨-, hinj, hiff⟩ := hR
  intro w hw
  rw [emitRun_asg reach dist n c (r + 1) (max tl 1) t
    (by intro k hkk; rw [hk, Nat.zero_add]; exact hlen k hkk)
    (by intro k hkk k' hkk' he; rw [hk, Nat.zero_add, Nat.zero_add] at he
        exact hinj k hkk k' hkk' he) w]
  have hmem : (∃ k < max tl 1, reach[t.1 + k]! = w) ↔ dist[w]! ≤ d := by
    rw [hk]
    simp only [Nat.zero_add]
    exact (hiff w hw).symm
  by_cases hset : t.2.2.2[w]! < n
  · rw [if_pos hset]
    by_cases hm : ∃ k < max tl 1, reach[t.1 + k]! = w
    · rw [if_pos hm, newAsg, if_pos hset]
      split <;> rfl
    · rw [if_neg hm]
  · rw [if_neg hset]
    have hn : t.2.2.2[w]! = n := le_antisymm (hle w hw) (by omega)
    by_cases hm : ∃ k < max tl 1, reach[t.1 + k]! = w
    · rw [if_pos hm, newAsg, hn]
      by_cases hd : dist[w]! < r + 1
      · rw [if_pos hd, if_neg (by omega), if_pos (by omega)]
      · rw [if_neg hd, if_neg (by omega)]
    · rw [if_neg hm, hn, if_neg (by
        intro hd
        exact hm (hmem.mpr (by omega)))]

/-! ### What is still owed

`emitRun_block` and `emitRun_hasg` are `CoverInv.step`'s `hblock` and
`hasg`, up to the fibre bridge (`RamCover.masked_step` +
`mem_wreach_iff_withinDist_pred`, both landed) and the passage from the
tower's `List ℕ` arrays to the driver stack's `arrOf` function arrays
(`Refine/BfsBridge.lean`'s `getElem!_arrOf`, also landed). What is *not*
here is the turn's cost: it has to be assembled from `emitLoopCost` and
`BfsQ.bfsBudget` through `BfsQSynth.bfsQS_correct`, which is a
`≤ NRest.spec` composition and not an equality, because the search's own
price is a bound and not a formula. That, and `ReachedList` itself, are
the named items for the integration wave; neither is `sorry`ed here. -/

/-! ## 9. Tool report: R2D/D-b's reproducer

The one gap this wave met, stated so it can be fixed in two lines.

`hnr_bind`'s second premise is

```
D2 : ∀ a : α, bind_ref_tag a m → hnRefine (hnCtxt Rh a x ∗ Γ₁) c₂ (Γ₂ a) d R (f a)
```

and `bind_ref_tag a m` is `NRest.returnT a ≤ m`. For a constant-producing
`m` — `mopConstN 0`, or `mopBinop .mul v 0` — that hypothesis **pins**
`a = 0`. The translate phase never looks at it: it recurses into `D2` at
an opaque `a`, and every downstream rule that names a literal value in a
cell then fails to fire. The report is

```
Lax13Proofs.Refine.Sepref.hnr_bind: applied, but a side condition stalled:
  no rule translates … under … hnCtxt natAssn a✝¹ "head" …
```

against a rule whose conjunct is `hnCtxt natAssn 0 "head"`.

The two-line reproducer is: take `ScatterSynth.hnr_mop_bfs`'s
precondition, replace `hnCtxt natAssn 0 "head"` by `hnCtxt natAssn h₀
"head"` in the goal, and ask for

```
NRest.bindT (mopZeroIn h₀) fun _ => ScatterSynth.mopBfs n d src off tgt alv dist₀ q₀
```

— it stalls. The fix in the tool is to try `bind_ref_tag`'s
normalization (`m` to `consume (returnT v) κ`, then `a := v`) before
recursing; the fix in the *caller*, which is what §0 does, is `mopBfsE`:
move the entry condition into the operation's own `assert`. The second
costs one operation per engine and is the sanctioned idiom (P4/D-ed), so
this is a legibility item rather than a blocker — but a caller who does
not know it reads the report as "an engine cannot be re-entered in a
loop", which is the opposite of true.

**R2D/D-e — no other gap.** Everything else the wave needed was already
there: the `fri` bound-tuple split (T1/D-b) fires three times per turn —
`dist`, `q` and `tl` are all read out of the search's bound four-tuple —
the branch merge (T1/D-a) handles the nested scalar branch, and a
ten-component loop state synthesizes without a `packN` (T1's W11
measure).

**R2D/D-f — the allocator reuses the engine's dead cells.** The four
scratch cells this file declares (`"cvu"`, `"cvd"`, `"cva"`, `"cvw"`) and
the two the `max tl 1` computation needs (`"cvm"`, `"cve"`) are framed
off **unused** in the pass: the allocator put the emission's temporaries
in `"v"`, `"dv"`, `"dv1"`, `"k0"` and the two binops in `"a"` and `"i"`,
all of them dead by then. Nothing asked it to; it is what the frame
matcher found, and a reader counting registers should not expect six
more. -/

/-! ## 10. Axioms -/

/-- info: 'Lax3Proofs.Refine.CoverSynth.emitSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms emitSynth

/-- info: 'Lax3Proofs.Refine.CoverSynth.turnCoreSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms turnCoreSynth

/-- info: 'Lax3Proofs.Refine.CoverSynth.coverSynth' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms coverSynth

/-- info: 'Lax3Proofs.Refine.CoverSynth.emitLoop_value' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms emitLoop_value

/-- info: 'Lax3Proofs.Refine.CoverSynth.emitCost_touched_only' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms emitCost_touched_only

/-- info: 'Lax3Proofs.Refine.CoverSynth.emitRun_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms emitRun_block

/-- info: 'Lax3Proofs.Refine.CoverSynth.emitRun_hasg' depends on axioms: [propext,
Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms emitRun_hasg


/-! ## 11. Telemetry (the wave's acceptance numbers)

* **Three syntheses, one command each, no bespoke tactic.** The emission
  scan alone; the search leaf followed by the scan over what it reached;
  and the whole pass — a ten-component loop state, an engine as a leaf
  inside the body, and a nested loop after it. All three programs are
  pinned by `#guard` above.

* **Hand-written frame clauses: 0.** Nothing in this file rewrites with
  `sepConj_assoc`, `sepConj_comm`, `ac_rfl` *on assertions*, `irSTATE_rot`,
  `fri`, `iicf_perm`, `hnRefine_pre_perm`, `hnRefine_frame` or
  `entails_of_eq`. The two `ac_rfl`s (`emitF_eq`, and `abel` in the cost
  algebra) are on **cost sums**, under a `congr 1`. The one hand-written
  `hnRefine` is `hnr_mop_bfsE`, and it is three lines: `hnr_assert`, two
  substitutions, and the 2A rule.

* **Wall clock**, warm build, `lake env lean` on the single file:
  **≈ 95 s**. Of that, `emitSynth` ≈ 10 s, `turnCoreSynth` ≈ 10 s,
  `coverSynth` ≈ 22 s (`maxHeartbeats 4000000`; it does not need more,
  but it does need that), and the four `#guard`ed evaluator runs of §7
  the rest.

* **Interface ops consumed: 7** — `mopAget`, `mopAset`, `mopBinop`,
  `mopCopy`, `mopConstN`, `mopPair` (P4 primitives) and
  `Sepref.mopSucc` (`IrOpsExtra`, T1/D-c) — plus `ScatterSynth.mopBfs`,
  the whole synthesized BFS as one leaf, and the four pinned operations
  declared in §0.

* **Cells.** The pass adds four to the search's eighteen: `"c"`, `"xp"`,
  `"cvk"`, `"cvs"`, plus `"cvz"` for the zero constant, against the
  baseline's `"c"`, `"xp"`, `"z"`, `"dz"`. All digit-free (P1/B-f). The
  six junk cells the file declares are framed off unused (R2D/D-f).

* **Axioms.** `#print axioms` is pinned in §10 for all six named results:
  `[propext, Classical.choice, Quot.sound]`, and `emitRun_block` needs
  only `[propext, Quot.sound]`. No `sorry`, no new axiom.

* **Backlog.** (i) The turn's cost, assembled from `emitLoopCost` and
  `BfsQ.bfsBudget` through `BfsQSynth.bfsQS_correct` — a `≤ NRest.spec`
  composition, since the search's price is a bound and not a formula.
  (ii) `ReachedList` itself (R2D/D-c), which belongs to a BFS wave.
  (iii) The `BRefine` bounds pass: none is written here, because the
  export it would feed is (i)'s, and the ownership-level bounds the
  synthesis already discharges are the ones the scan needs. -/

end Lax3Proofs.Refine.CoverSynth
