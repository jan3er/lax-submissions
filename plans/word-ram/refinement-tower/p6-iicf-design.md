# P6 design record — collections (IICF port, narrow)

2026-07-30, supervisor-authored, from `p6-iicf-extracts.md` (source:
IICF at the pin). Scope per plan: plain arrays; Trail-backed
touched-only arrays as the default array instance (ledger D5); CSR
graphs; stack; queue; bitmask sets. Each: abstract interface, hnr
rules, credit specs. Acceptance: every structure's rules consumed by
the P4 translator on an exercise program with no bespoke tactic work.

## What the extracts say (and what carries over)

The source's IICF skeleton — Intf/Impl split, `sepref_decl_op`
interface ops, Impl rules as raw-hnr `FCOMP` interface-param rules,
`intf_of_assn` — is identical in the cost and no-cost forks; cost
enters only in the Impl hnr rules. Key consequence for us: **our mop
layer (pinned ir.* currencies) already plays the role of the source's
raw op layer**, and the Intf/Impl distinction maps onto:

- **Interface op** = an NREST operation on the abstract type (List,
  Finset, pair), with a cost stated in ir.* currency multisets
  (D6-P6-1: the source's Intf layer is cost-silent; ours cannot be,
  because our hnRefine has no hidden cost notation — the cost IS the
  interface).
- **Impl** = a compound `Ir.Com` + an hnr rule from the interface op to
  a **composite assertion over fixed named cells** (the no-alloc
  substrate: a structure never allocates; it lives at caller-chosen
  cell names, capacity fixed at init — D6-P6-2, replacing every
  source `*_new`/`*_free` op with init-from-junk / entailment-to-junk
  lemmas in the P4 junkCell discipline).

**The Impl rules are synthesized, not hand-proved (D6-P6-3):** each
structure op's compound `Ir.Com` is produced by our own `sepref_synth`
from the primitive mops (the source proves its Impl layer "by sepref"
identically), then the resulting hnr theorem is registered
`@[sepref_fr_rules]` so consumers see one op = one rule. This dogfoods
the P4 pipeline and keeps every cost honest by construction.

Composite assertions must be frame-matchable by the P4 matcher (pairs
`hnCtxt` conjuncts by concrete cell name): expose the cells as a tuple
descriptor `d` (the `prodAssn`/`hnCtxt_prodAssn` machinery from P4
handles splitting), one assertion definition per structure with an
unfold lemma into its cell conjuncts.

## The structures

Module home: `word-ram/proofs/Lax13Proofs/Refine/Iicf/`.

1. **Plain arrays** (`IicfArray.lean`) — mostly exists (`arrayAssn`,
   mopAget/mopAset). Add the interface completions: `mop_array_fill`
   (the P3 fill loop as one op, cost linear), `mop_array_copy_range`
   if an exercise needs it, length as a *static* parameter (lists know
   their length abstractly; no runtime length op — D6-P6-4).
2. **Trail-backed touched-only arrays** (`IicfTrailArray.lean`) — the
   D5 default. Abstract type: `(xs : List Val) × (k : ℕ)` — the array
   with a *touch budget counter* (the abstract cost carrier that makes
   reset's touched-proportional cost sayable abstractly). Cells:
   `(A, T, t)` — data array, trail array (capacity = |xs|… flag if you
   choose differently), trail top. Assertion existentially owns the
   trail contents: entries of `A` off the trail are the default `dflt`;
   `k` = trail length. Ops: `tget` (= aget, k unchanged), `tset`
   (aset + trail push, k+1), `treset` (pop-loop restoring `dflt`,
   result `(replicate n dflt, 0)`, cost `(k+1)`·loop-unit-multiset).
   This is the touched-only-costs discipline from the ND-MC campaign
   made a library object.
3. **Stack** (`IicfStack.lean`) — abstract `List Val` (top = head),
   cells `(S, top)`, capacity static. `push` (assert len < cap),
   `pop` (assert nonempty; result into a destination cell), `isEmpty`
   via the fused-guard CondRefine route (top = 0) rather than a bool
   op — D6-P6-5.
4. **Queue** (`IicfQueue.lean`) — one-shot FIFO over `(Q, head, tail)`
   (no wraparound: capacity = total enqueues, the BFS discipline —
   D6-P6-6, matches the baseline's `Queue.drain` shape). `enq`, `deq`,
   emptiness as fused guard `head < tail` / `head = tail`.
5. **CSR graphs** (`IicfCsr.lean`) — thin. Abstract type: the pair of
   lists `(off, tgt)` with the CSR well-formedness as an assertion-side
   pure conjunct (monotone offsets, targets in range). Cells
   `("off","tgt")` (caller-named). Ops: `rowStart v`, `rowEnd v`
   (agets into off), `slotTarget k` (aget into tgt). Row iteration is
   a plain while loop at the abstract level (FOREACH is unported
   backlog; do NOT port it now — D6-P6-7).
6. **Bitmask sets** (`IicfBitmask.lean`) — abstract `Finset ℕ` over a
   single scalar cell holding `∑ i ∈ S, 2^i`. `bmEmpty` (const 0),
   `bmInsert i` (or with shiftl), `bmMem i` (shiftr+and, result 0/1,
   membership as fused guard on the result cell). Elements must be
   < the word budget for codegen (`B > 2^n`) — record in the file
   header that this is the standard mask trade-off (ND-MC uses it),
   costed at codegen, invisible at this layer.

Costs: every op's cost is a concrete `ECost` multiset of ir.*
currencies, computed by what `sepref_synth` actually consumed —
pinned by `#guard`-style checks where computable.

## Acceptance (per structure, in each file or one Exercises.lean)

An exercise program written at the abstract layer and pushed through
`sepref` mechanically — zero bespoke tactics, zero hand frame clauses:
arrays: in-place histogram-style pass; trail: write–reset–reuse
across two rounds (demonstrating reset cost ∝ touched, not length);
stack: push-drain sum; queue: enq-drain sum; CSR: degree sum of one
vertex's row / total slot count; bitmask: insert-then-count-members
over a small loop. Each with computable-twin `#guard`s + one negative
control, axioms pinned.

## Wave plan

Two parallel Opus satellites branched from the current campaign head:
- **P6-A** (`refine-p6-arrays`): interface conventions module
  (`Iicf/Basic.lean` — naming, registration idiom, init-from-junk
  pattern) + IicfArray + IicfTrailArray (+ their exercises).
- **P6-B** (`refine-p6-structs`): IicfStack + IicfQueue + IicfCsr +
  IicfBitmask (+ exercises). Follows the SAME conventions section of
  this record (not P6-A's file — parallel safety); supervisor
  reconciles any convention drift at merge, flags it.

Flag ranges: supervisor D6-P6-1…7 above; P6-A flags P6/D-h…;
P6-B flags P6/D-ba…. Refute-before-prove per standing practice.
Budget: 2–3 sessions; one overnight at observed velocity.
