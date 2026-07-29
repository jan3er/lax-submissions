import Mathlib.Tactic

/-!
The rule databases of the IR's frame inferencer.

`thys/lib/Frame_Infer.thy` declares its rule sets in four lines, quoted
verbatim in `plans/word-ram/refinement-tower/p3-sl-deep-extracts.md` §2:

```isabelle
named_simpset fri_prepare_simps = HOL_basic_ss_nomatch
named_theorems fri_rules
named_theorems fri_red_rules
named_theorems fri_end_rules
```

and `thys/lib/Basic_VCG.thy` declares the VCG's own rule sets, of which
the one wave C populates is

```isabelle
named_theorems vcg_rules
```

This module declares those five databases and nothing else, for the
substrate reason `Autoref/Attrs.lean` already documents at length
(P1 delta B7): Lean runs `initialize` blocks at *import* time, so an
attribute is not available to the module that declares it, and every
rule that wants a tag has to live downstream. `Ir/SepSolver.lean` — the
solver and its rules — is that downstream module.

The port of the databases themselves, the four structural rules they
feed, and the search loop that consults them are all in
`Ir/SepSolver.lean`; its header carries the fidelity ledger
(judgment calls D-y … D-af) for the whole of wave C.
-/

namespace Lax13Proofs.Refine.Ir

/-- The source's `named_simpset fri_prepare_simps` (`Frame_Infer.thy`):
the normalization set `start_tac` runs before frame inference begins —
associativity and `emp` normalization in the source, and here also the
assertion-level splitting rules that turn a compound credit assertion
into a `∗`-list of atomic ones. `Ir/SepSolver.lean` populates it with
the IR's own splitters; a consumer that defines a bundled cost (a loop's
per-iteration payload, say) tags its own splitting lemma here and the
solver sees the parts. -/
register_simp_attr fri_prepare_simps

/-- The source's `named_theorems fri_rules`: the *step* set. A member is
an entailment `P ⊢ Q` between single conjuncts, instantiated into
`fri_step_rl` to consume one conjunct of the precondition against one
conjunct of the target. -/
register_label_attr fri_rules

/-- The source's `named_theorems fri_red_rules`: the *reduction* set. A
member is an `is_sep_red P' Q' P Q` fact, instantiated into
`fri_reduce_rl` to rewrite one precondition/target conjunct pair into a
smaller one under an arbitrary residue. -/
register_label_attr fri_red_rules

/-- The source's `named_theorems fri_end_rules`: what the solver tries,
after `entails_refl`, once the target side is down to `FRI_END` and only
the residue-versus-frame entailment is left. -/
register_label_attr fri_end_rules

/-- `Basic_VCG.thy`'s `named_theorems vcg_rules`: the Hoare triples the
VCG applies with framing (as opposed to `vcg_decomp_rules`, which it
applies as they are). Populated by `Ir/SepSolver.lean` with the IR's
per-op rules in their source-shaped, pure-side-condition form; P4's
`hn_refine` layer is the intended consumer. -/
register_label_attr vcg_rules

end Lax13Proofs.Refine.Ir
