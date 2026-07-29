import Mathlib.Tactic

/-!
The rule databases of the Sepref translate phase.

`thys/sepref/Sepref_Translate.thy` declares its three rule collections in
its header, quoted in `plans/word-ram/refinement-tower/p4-sepref-extracts.md`
§2:

```
These frame-based rules are in the named theorem collection
sepref_fr_rules, and the collection sepref_copy_rules
contains rules to handle copying of parameters.
Apart from the frame-based rules described above, there is also a set of
rules for combinators, in the collection sepref_comb_rules,
where no automatic copying of parameters is applied.
```

i.e. the `named_theorems sepref_fr_rules`, `sepref_comb_rules`,
`sepref_copy_rules` of that theory's preamble.

This module declares those three databases and nothing else, for the
substrate reason `Autoref/Attrs.lean` documents at length (P1 delta B7):
Lean runs `initialize` blocks at *import* time, so an attribute is not
available to the module that declares it, and every rule that wants a tag
has to live downstream. `Sepref/IrOps.lean` and `Sepref/CombRules.lean`
are those downstream modules.

**P4/D-aa — the three Sepref DBs are declared here, not in
`Autoref/Attrs.lean`.** The P4 brief points at the shared DB-attribute
module; the *implementation* is indeed shared (`register_label_attr`, the
one mechanism design record §10 default 3 asks for), but the declaration
site follows P3's own precedent — `Ir/Attrs.lean` declares the five
`Frame_Infer`/`Basic_VCG` databases next to the layer that populates
them rather than in `Autoref/Attrs.lean`. Keeping the per-layer file
means the Sepref layer adds no edit to a file two other waves are
reading, and the source's own file layout (each theory declaring its own
`named_theorems`) is what is reproduced. Fallback: move the three
declarations into `Autoref/Attrs.lean` and delete this file; no rule
statement changes, only the import line of the two consumers.
-/

namespace Lax13Proofs.Refine.Sepref

/-- The source's `named_theorems sepref_fr_rules` (`Sepref_Translate.thy`):
the *frame-based* rule set — one `hn_refine` rule per abstract operation,
applied with frame inference, with automatic copying of parameters that
are still needed. Populated by `Sepref/IrOps.lean` with the IR's per-op
rules at the currencies `Ir/Syntax.lean` declares. -/
register_label_attr sepref_fr_rules

/-- The source's `named_theorems sepref_comb_rules`: the *combinator* rule
set, applied without automatic copying — the source's `hn_bind`,
`hnr_If`, `hn_monadic_WHILE_lin` live here. Populated by
`Sepref/CombRules.lean` (and by `hnr_seq`, which is stated in
`Sepref/Basic.lean`, i.e. upstream of this declaration; wave C registers
it). -/
register_label_attr sepref_comb_rules

/-- The source's `named_theorems sepref_copy_rules`: the rules by which
the translate phase copies a parameter that a synthesized operation would
destroy but that is still live. Declared now, populated when a consumer
forces it: under P4/D-c the substrate has no dealloc and ownership is
downgraded rather than freed, so the copy discipline enters only where a
*destructive* op (`aset`, an in-place `binop`) meets a still-live
argument — the `Com.copy` op priced at `Currency.copy` is the program the
rules will produce. -/
register_label_attr sepref_copy_rules

end Lax13Proofs.Refine.Sepref
