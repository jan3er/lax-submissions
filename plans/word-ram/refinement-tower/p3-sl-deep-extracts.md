# P3 source extracts (deep) — `cost_framework`, frame inference, the SL class surface, memory-op triples

Deep companion to `p3-ir-sl-extracts.md` (the shape-level P3 extract) and
`design.md` §3 P3 + §11. Fetched 2026-07-29, verbatim, from
`isabelle_llvm_time` @ `42dd7f5` (pin per `design.md` §1), files retrieved
via `raw.githubusercontent.com/lammich/isabelle_llvm_time/42dd7f59998d76047bb4b6bce76d8f67b53a08b6/thys/<path>`,
byte-exact via `curl`:

| file | bytes |
|---|---|
| `thys/vcg/Sep_Generic_Wp.thy` | 37336 |
| `thys/lib/Frame_Infer.thy` | 19685 |
| `thys/vcg/LLVM_VCG_Main.thy` | 185 |
| `thys/lib/Sep_Algebra_Add.thy` | 20802 |
| `thys/lib/Basic_VCG.thy` | 26097 |
| `thys/vcg/LLVM_Shallow_RS.thy` | 50902 |

Isabelle source uses the `\<foo>` cartouche/symbol spelling throughout;
every fenced block below has been mechanically converted to the Unicode
glyphs (`⇒`, `∀`, `⟹`, `↑`, `⊢`, `□`, `⟦…⟧`, …) that Isabelle/jEdit
displays, so the extract reads the way the source's authors read it.
`**`/`∧*` are the source's own two notations for the *same* `sep_conj`
constant (infixr, defined once) — both appear verbatim below exactly as
each source file happened to write it.

Directory listing for `thys/vcg/` (per pin, superseding the partial
listing in `p3-ir-sl-extracts.md`): `LLVM_Memory_RS.thy`,
`LLVM_Shallow_RS.thy` (50902 b), `LLVM_VCG_Main.thy` (185 b),
`Sep_Array_Block_RS.thy`, `Sep_Block_Allocator_RS.thy`,
**`Sep_Generic_Wp.thy`** (37336 b), `Sep_Lift.thy`,
`Sep_Value_RS.thy`. `thys/lib/`'s `Frame_Infer.thy` (19685 b),
`Sep_Algebra_Add.thy` (20802 b) and `Basic_VCG.thy` (26097 b) are the
three additional `thys/lib` files this extract needed beyond the P3
shape extract's list.

One additional, non-artifact source was needed for item 4 (the
sep-algebra class surface): `Sep_Algebra_Add.thy` imports
`"Separation_Algebra.Sep_Tactics"`, the AFP entry by Gerwin Klein and
Rafal Kolanski (2012) — this is a *library dependency* of the artifact,
not part of it, so its own git history is the AFP's, not
`isabelle_llvm_time`'s. Fetched from the GitHub mirror
`isabelle-prover/mirror-afp-2020` (the AFP release contemporary with
Isabelle2020, which predates the artifact's 2021-03-02 pin by about the
right margin for the artifact to depend on it) at
`thys/Separation_Algebra/{Separation_Algebra,Sep_Tactics}.thy` (28808 b
+ 4113 b). Diffed against the AFP-devel current mirror's copy of the
same file (28990 b): the size delta is small and the class definitions
below are unchanged between the two, so the two-versions-back pin
introduces no risk to this extract's fidelity claim. `Sep_Tactics.thy`
itself is pure ML tactic scaffolding (`sep_select`, `sep_subst`, …, an
AFP-side precursor to `Frame_Infer.thy`'s own `sep_drule`/`sep_rule`)
and contributes no class or constant surface, so nothing from it is
quoted below.

## 1. The `cost_framework` locale, its `wp`, and the LLVM interpretation

The locale the shape-level extract's Gaps section deferred — full
header, all four named assumptions, the cost-carrying `wp` it defines,
and its three basic reasoning lemmas (`Sep_Generic_Wp.thy`, section "a
General framework for abstract and concrete costs"):

```isabelle
locale cost_framework =
  fixes
    I :: "'cc::{monoid_add} ⇒ 'ca ⇒ bool"
  and minus :: "'ca ⇒ 'cc ⇒ 'ca" -- ‹takes abstract credits, and returns the effect of consuming
                                        the concrete resources›
assumes minus_0[simp]: "⋀y. minus y 0 = y"
  and I_0[simp,intro!]: "I 0 cr"
  and minus_minus_add: "⋀a b c. minus (minus a b) c = minus a (b + c)"
  -- ‹TODO: maybe some of these are redundant›
  and I1: "⋀a b c. I (a + b) c ⟹ I b (minus c a)"
  and I2: "⋀a b c. I (a + b) c ⟹ I a c"
  and I3:  "⋀a b c. I a (minus c b) ⟹ I b c ⟹ I (b + a) c"
begin

  definition  wp :: "('d, 'e, _, 'a, 'f) M ⇒ _ ⇒ _" where
    "wp m Q ≡ λ(s,cr). mwp (run m s) bot bot bot (λr c s. Q r (s,minus cr c) ∧ I c cr)"

  interpretation generic_wp wp
    apply unfold_locales
    unfolding wp_def fun_eq_iff inf_fun_def inf_bool_def mwp_def
    by (auto split: mres.split)

  lemma wp_return: "wp (return x) Q s ⟷ Q x s"
    by (auto simp: wp_def run_simps minus_0 I_0)

  lemma wp_fail: "¬ wp (fail x) Q s"
    by (auto simp: wp_def run_simps)

  lemma wp_fcheck: "wp (fcheck e Φ) Q s ⟷ Φ ∧ Q () s"
    by (auto simp: wp_def run_simps minus_0 I_0 split: if_splits)

  lemma wp_bind: "wp (m⤳f) Q s = wp m (λx. wp (f x) Q) s"
    apply (auto simp: wp_def run_simps split: prod.splits)
    unfolding mwp_def apply (auto split: mres.splits simp add: minus_minus_add)
    subgoal by (metis I1)
    subgoal by (metis I2)
    subgoal by (metis I3)
    done

  lemma wp_consume: "wp (consume c) Q (s,cr) ⟷ I c cr ∧ Q () (s,minus cr c)"
    unfolding wp_def mwp_def consume_def by (auto split: mres.split)

end
```

Reading the four assumptions against `design.md`'s ledger: `minus_0`
("consuming nothing leaves the balance unchanged"), `I_0` ("the zero
cost is always affordable, whatever the balance"), `minus_minus_add`
(sequential consumption is additive — `minus (minus a b) c = minus a
(b+c)`, the associativity `bind`'s cost-threading needs), and `I1`–`I3`
are the three splitting lemmas that make `wp_bind`'s proof go through:
`I1`/`I2` split an affordability fact for a sum into affordability of
each summand (with the balance correspondingly reduced for the second),
`I3` re-assembles them. `I` and `minus` are exactly `design.md`'s
"invariant that has to hold between the credits available and the
resources spent" and "deduct resources from credits" — nothing else
about the type of costs or credits is assumed at this level, which is
the whole point: `wp` is defined generically over *any* `(I, minus)`
pair satisfying these four laws, and `htriple`/`frame_rule`/`cons_rule`
come for free via the `generic_wp` interpretation two lines in.

`mwp`, the case-dispatcher `wp` is built on (`thys/lib/Monad.thy`,
already partly visible via `run_simps`/`mwp_def` above but not itself
quoted in the P0/P3 shape extracts): a thin `case_mres` wrapper letting
`wp`'s definition read as "nonterminating/failed ↦ `bot`, exception ↦
`bot`, success `x` with cost `c` and new state `s` ↦ `S x c s`":

```isabelle
definition "mwp m N F E S ≡ case_mres N F E S m"

lemma mwp_simps[simp]:
  "mwp NTERM N F E S = N"
  "mwp (FAIL msg) N F E S = F msg"
  "mwp (EXC e c s) N F E S = E e c s"
  "mwp (SUCC x c s) N F E S = S x c s"
  by (auto simp: mwp_def)
```

**Absence noted:** no `wp_get`/`wp_set` lemma exists anywhere in the six
files fetched for this extract (grepped) — `get`/`set` (the raw
state-read/write primitives of the `M`-monad, `thys/lib/Monad.thy`,
already quoted in `p3-ir-sl-extracts.md` §3) get no bespoke `wp`
unfolding lemma of their own; the source evidently expects them
unfolded via `wp_bind`/`wp_consume`'s combination with `mwp_simps`
(`get`/`set` are `consume 0`-costed successes, so `wp_consume` at
`c=0`, simplified by `minus_0`, already covers them). What the locale
*does* carry, immediately downstream in `LLVM_Shallow_RS.thy` (same
section, "The if command …" / "The while command …"), are the `wp_if`/
`wp_while`-analogues design.md's P3 row anticipates control flow
needing: the `llc_if`/`llc_while` combinators are *defined* in terms of
`consume`+`bind`, and reasoned about via normalization/decomposition
rules rather than dedicated `wp_if`/`wp_while` equations:

```isabelle
lemma llc_if_simps[vcg_normalize_simps]:
  "llc_if 1 t e = doM {consume (cost ''if'' 1); t}"
  "r≠0 ⟹ llc_if r t e = doM {consume (cost ''if'' 1); t}"
  "llc_if 0 t e = doM {consume (cost ''if'' 1); e}"
  by (auto simp: llc_if_def)

lemma llc_if_simp[vcg_normalize_simps]:
  "wp (llc_if b t e) Q s ⟷ wp (ll_consume (cost ''if'' 1))
      (λ_ s. (to_bool b ⟶ wp t Q s) ∧ (¬to_bool b ⟶ wp e Q s)) s"
  unfolding llc_if_def by (auto simp add: vcg_normalize_simps)

lemma llc_while_unfold:
  "llc_while b f σ = doM { ll_consume (cost ''call'' 1); ctd ← b σ;
     llc_if ctd (doM { σ←f σ; llc_while b f σ}) (return σ)}"
  unfolding llc_while_def
  apply (rewrite REC'_unfold[OF reflexive], pf_mono_prover)
  by (simp add: ll_call_def)
```

— one `''if''` credit is charged per branch taken, one `''call''`
credit per loop iteration entered — and the actual reasoning principle
consumed by proofs is the invariant/variant `vcg_decomp_erules` rule
(`LLVM_Shallow_RS.thy`, "Standard while rule"), which frames an
invariant `I σ t` (`t` a well-founded-decreasing measure) through the
loop body and discharges the loop as one VCG step:

```isabelle
lemma llc_while_annot_rule[vcg_decomp_erules]:
  assumes "llSTATE P s"
  assumes "FRAME P (I σ t) F"
  assumes WF: "SOLVE_AUTO_DEFER (wf R)"
  assumes STEP: "⋀σ t s. ⟦ llSTATE ((I σ t ** F)) s ⟧ ⟹ EXTRACT (wp (doM {ll_consume (cost ''call'' 1); ctd ← b σ; ll_consume (cost ''if'' 1); return ctd}) (λctd s⇩1.
    (to_bool ctd ⟶ wp (f σ) (λσ' s⇩2. llPOST (EXS t'. I σ' t' ** ↑((t',t)∈R) ** F) s⇩2) s⇩1)
  ∧ (¬to_bool ctd ⟶ Q σ s⇩1)
    ) s)"
  shows "wp (llc_while_annot I R b f σ) Q s"
```

(proof: 20-odd lines instantiating `basic_while_rule`, a well-founded
induction on the measure `t`, elided — the *shape* is the payload: one
VCG-visible rule per combinator, invariant/variant supplied by the
user, side goal `wf R` deferred to `SOLVE_AUTO_DEFER`.)

**The LLVM interpretation** — how the generic locale is instantiated
for the concrete/abstract cost pair the whole artifact runs on
(`cost = (String,ℕ) acost` concrete, `ecost = (String,ℕ∞) acost`
abstract), i.e. exactly the ℕ∞ seam design.md flags as P3's first
decision (`design.md` §10.1):

```isabelle
definition le_cost_ecost :: "cost ⇒ ecost ⇒ bool"
  where "le_cost_ecost cc ca ≡ ∀x. enat (the_acost cc x) ≤ (the_acost ca x)"

definition minus_ecost_cost :: "ecost ⇒ cost ⇒ ecost"
  where "minus_ecost_cost ca cc ≡ acostC (λx. (the_acost ca x) - enat (the_acost cc x))"

interpretation cost_framework le_cost_ecost minus_ecost_cost
  unfolding le_cost_ecost_def minus_ecost_cost_def
  apply (rule cost_framework.fun_cost_framework)
  apply standard
  apply (auto simp flip: zero_enat_def)
  ‹four automated subgoals (metis/smt/meson) discharging the pointwise
   lifting of the nat-instance cost_framework onto acost-valued
   currencies — elided, they are pure enat arithmetic, not calculus›
```

This `interpretation` is **unnamed**, so it deposits `wp`
(unqualified), `wp_bind`, `wp_consume`, `wp_return`, … directly as
top-level facts for the `(cost, ecost)` instance — there is no separate
"LLVM `wp`"; the LLVM layer's `llvm_htriple` is simply this same `wp`
composed with the LLVM state-abstraction function `ll_α` and
`GC`-absorption (`LLVM_Shallow_RS.thy`):

```isabelle
type_synonym ll_astate = "llvm_amemory × ecost"
definition "ll_α ≡ lift_α_cost llvm_α"
abbreviation llvm_htriple
  :: "ll_assn ⇒ 'a llM ⇒ ('a ⇒ ll_assn) ⇒ bool"
  where "llvm_htriple ≡ htriple_gc GC ll_α"
abbreviation "llSTATE ≡ STATE ll_α"
abbreviation "llPOST ≡ POSTCOND ll_α"
abbreviation (input) ll_cost_assn ("$$") where "ll_cost_assn ≡ λname n. $lift_acost (cost name n)"
```

Two presentation-only restatements of `wp` at this instance, useful for
reading the port's own `Ir.wp` against (both proved `unfolding wp_def`,
i.e. definitional, not new content):

```isabelle
lemma wp_alt: "wp m Q (s,cr::ecost) = (∃r (c::cost) s'. run m s = SUCC r c s'
    ∧ Q r (s', minus_ecost_cost cr c) ∧ le_cost_ecost c cr )"
```

— "the program succeeds with result `r`, concrete cost `c`, new state
`s'`; `c` must be affordable against the balance `cr`; the postcondition
holds of the new state paired with the balance after deduction." This
is the sentence `Ir/Wp.lean`'s `Ir.wp` needs to read the same way.

## 2. Frame inference (`thys/lib/Frame_Infer.thy`) — entailment and the FRI solver

The entailment connective (note: this `⊢`/`entails` is *not* part of
the AFP separation-algebra class — it is added here, on top of it):

```isabelle
definition "entails" :: "('a::sep_algebra ⇒ bool) ⇒ _ ⇒ _" (infix "⊢" 25) where "P ⊢ Q ≡ ∀s. P s ⟶ Q s"
lemma entails_refl[intro!,simp]: "P ⊢ P" by (simp add: entails_def)
lemma entails_false[simp, intro!]: "sep_false ⊢ Q" by (simp add: entails_def)
lemma entails_true[simp, intro!]: "P ⊢ sep_true" by (simp add: entails_def)
lemma entails_trans[trans]: "P ⊢ Q ⟹ Q ⊢ R ⟹ P ⊢ R"
  by (simp add: entails_def)
lemma entails_mp: "⟦Q ⊢ Q'; P ⊢ Q ∧* F⟧ ⟹ P ⊢ Q' ∧* F"
  apply (clarsimp simp: entails_def)
  using sep_conj_impl1 by blast
lemma conj_entails_mono: "P⊢P' ⟹ Q⊢Q' ⟹ P**Q ⊢ P'**Q'"
  apply (clarsimp simp: entails_def)
  using sep_conj_impl by blast
lemma entails_exI: "P⊢Q x ⟹ P⊢(EXS x. Q x)"
  by (metis (mono_tags, lifting) entails_def)
lemma entails_pureI: "⟦pure_part P ⟹ P⊢Q⟧ ⟹ P⊢Q"
  by (auto simp: entails_def intro: pure_partI)
```

The `FRAME_INFER`/`FRAME`/`ENTAILS` tags the ML solver drives, and the
three structural rules it resolves against (prepare/end/step/reduce —
these four ARE the whole calculus of frame inference; everything else
is search control):

```isabelle
definition "FRI_END ≡ □"
definition "FRAME_INFER P Qs F ≡ P ⊢ Qs ** F"

lemma fri_prepare: "FRAME_INFER Ps (Qs**FRI_END) F ⟹ FRAME_INFER Ps Qs F"
  by (auto simp: FRI_END_def)

lemma fri_prepare_round: "FRAME_INFER (□**Ps) Qs F ⟹ FRAME_INFER Ps Qs F"
  by simp

lemma fri_end: -- ‹Potential premises get solved by entails_refl.›
  "Ps ⊢ F ⟹ FRAME_INFER Ps FRI_END F"
  by (auto simp: FRAME_INFER_def FRI_END_def)

lemma fri_step_rl:
  assumes "P ⊢ Q"  -- ‹Gets instantiated with frame_infer_rules›
  assumes "FRAME_INFER Ps Qs F"
  shows "FRAME_INFER (P**Ps) (Q**Qs) F"
  using assms unfolding FRAME_INFER_def by (simp add: conj_entails_mono)

lemma fri_reduce_rl:
  assumes "is_sep_red P' Q' P Q"
  assumes "FRAME_INFER (P'**Ps) (Q'**Qs) F"
  shows "FRAME_INFER (P**Ps) (Q**Qs) F"
  using assms unfolding FRAME_INFER_def by (auto dest: is_sep_redD)

definition "FRAME P Q F ≡ P ⊢ Q ** F"
definition "ENTAILS P Q ≡ P ⊢ Q"

lemma fri_startI:
  "⟦pure_part P ⟹ FRAME_INFER P Q F⟧ ⟹ FRAME P Q F"
  "⟦pure_part P ⟹ FRAME_INFER P Q □⟧ ⟹ ENTAILS P Q"
  unfolding FRAME_INFER_def FRAME_def ENTAILS_def by (auto intro: entails_pureI)
```

`is_sep_red P' Q' P Q` (defined a few lines above `fri_reduce_rl`) is
the "safe rewrite under a frame" relation the reduce-step consumes:
`is_sep_red P' Q' P Q ≡ ∀Ps Qs. (P'**Ps⊢Q'**Qs) ⟶ (P**Ps⊢Q**Qs)` — "if
the smaller entailment holds for any residue, so does the bigger one";
this is what lets the solver discharge e.g. `⋃*i∈I. P i ⊢ ⋃*i∈I-{k}. P i
** P k` in one step (`fri_red_img_si` and friends, later in the same
file) instead of unfolding the whole finite family.

The registered rule sets the ML tactic consults, in the order it
consults them:

```isabelle
named_simpset fri_prepare_simps = HOL_basic_ss_nomatch
named_theorems fri_rules
named_theorems fri_red_rules
named_theorems fri_end_rules
```

The ML algorithm (`structure Frame_Infer`, same file) — described
structurally, its body is pure search-control ML not worth quoting
line-by-line:

- **`start_tac`**: simp with `fri_prepare_simps` (associativity/`emp`
  normalization); repeatedly strip existentials/`sep_true` off the
  goal's *front* (`fri_exI`, `fri_trueI`); apply `fri_prepare`, which
  moves the whole target list `Qs` behind a `FRI_END` marker so the
  main loop always has a "consumed so far / still to match" split
  visible in the term.
- **one `round_tac`**: `start_round_tac` (peel a leading `□` off the
  premise list, re-associate); **`rotations_tac`**: cycle through every
  cyclic rotation of the premise conjunction `P₁**…**Pₙ` (via the
  `fri_prems_cong` congruence and a `sep_conj_commute`/`_assoc`
  rewriting loop) so that whichever premise conjunct the *first*
  registered `fri_rules`/`fri_red_rules` lemma matches ends up in front;
  **`solve_round_tac`**: resolve with `fri_step_rl OF [rule]` for every
  `fri_rules` lemma and `fri_reduce_rl OF [rule]` for every
  `fri_red_rules` lemma, i.e. try to consume one leading conjunct of the
  precondition against one leading conjunct of the goal (or reduce one
  precondition conjunct via an `is_sep_red` fact) — first match wins,
  `Basic_VCG.step_precond_tac` immediately discharges any `PRECOND`
  side-goal the matched rule created via the registered solver
  infrastructure (§3).
- **`end_tac`**: once the goal side is down to `FRI_END`, try
  `entails_refl` first (`P⊢P` is always attempted before any registered
  `fri_end_rules` lemma — the one hard-coded priority in the whole
  algorithm), then the `fri_end_rules` list (`entails_true`,
  `empty_ent_GC`, `entails_GC`, the credit-absorption rule
  `$c**P⊢GC` — `LLVM_Shallow_RS.thy` — so any left-over credits at the
  end of a frame match are swallowed by a trailing `GC` in the goal).
- **`infer_tac`**: `start_tac` then repeat `(end_tac ORELSE round_tac)`
  until nothing changes — i.e. keep consuming premise conjuncts against
  goal conjuncts, rotating for a match each round, until either the goal
  is fully matched (`end_tac` fires) or no round makes further
  progress (in which case the residual entailment is left as a subgoal
  for the caller — the solver does not fail silently, it stalls
  visibly).

Registration into the *generic* VCG's solver table (this is the wiring
that makes `vcg` call frame inference automatically whenever a rule
introduces a `PRECOND (FRAME …)`/`PRECOND (ENTAILS …)` side-condition,
§3 below):

```isabelle
declaration ‹
  K (Basic_VCG.add_solver (@{thms fri_startI},@{binding infer_frame},Frame_Infer.infer_tac))
›
```

## 3. The VCG assembly — goal forms, top-level tactic loop, named rule sets

`thys/vcg/LLVM_VCG_Main.thy` in full — confirms the "assembly" is
nothing but an import; there is no separate top-level VCG theory, the
machinery lives in `Sep_Generic_Wp.thy` (goal-form tags) and
`thys/lib/Basic_VCG.thy` (the generic rule-application engine
`Frame_Infer.thy` plugs into):

```isabelle
section ‹LLVM Verification Condition Generator›
theory LLVM_VCG_Main
imports LLVM_Shallow_RS
begin
  text ‹Entrypoint to the LLVM VCG, with minimal setup›
end
```

**Goal forms** (`Sep_Generic_Wp.thy`) — `STATE`/`POSTCOND` are the two
shapes every VCG-visible goal is stated in: "assertion `P` holds of the
state `s`, read through abstraction `α`" for preconditions/mid-proof
states, and the same thing tagged `POSTCOND` (definitionally identical,
`[vcg_tag_defs]`) once the goal has become a postcondition target so
the tactic knows not to re-decompose it the same way:

```isabelle
definition STATE :: "('s ⇒ 'a::sep_algebra) ⇒ ('a ⇒ bool) ⇒ 's ⇒ bool"
  where "STATE α P s ≡ P (α s)"

lemma STATE_extract[vcg_normalize_simps]:
  "STATE α (↑Φ) h ⟷ Φ ∧ STATE α □ h"
  "STATE α (↑Φ ** P) h ⟷ Φ ∧ STATE α P h"
  "STATE α (EXS x. Q x) h ⟷ (∃x. STATE α (Q x) h)"
  "STATE α (λ_. False) h ⟷ False"
  "STATE α ((λ_. False) ** P) h ⟷ False"
  by (auto simp: STATE_def sep_algebra_simps pred_lift_extract_simps)

definition POSTCOND :: "('s ⇒ 'a::sep_algebra) ⇒ ('a ⇒ bool) ⇒ 's ⇒ bool"
  where [vcg_tag_defs]: "POSTCOND α ≡ STATE α"

lemma start_entailsE:
  assumes "STATE α P h"
  assumes "ENTAILS P P'"
  shows "STATE α P' h"
  using assms unfolding STATE_def ENTAILS_def entails_def by auto
```

At the LLVM instance these specialize to `llSTATE ≡ STATE ll_α`,
`llPOST ≡ POSTCOND ll_α` (§1). The hookup from `htriple`/`htripleF` into
this same `STATE`/frame-solving machinery — the rule that literally
turns "prove `wp c Q' s`" into "find `P'` such that `STATE α P' s`
holds, frame-match `P'` against a registered triple's precondition `P`,
then check the triple's postcondition entails the goal's `Q'`" —
(`Sep_Generic_Wp.thy`, inside `context generic_wp begin … end`):

```isabelle
lemma htriple_vcg_frame_erule[vcg_frame_erules]:
  assumes S: "STATE α P' s"
  assumes F: "PRECOND (FRAME P' P F)"
  assumes HT: "htriple α P c Q"
  assumes P: "⋀r s. STATE α (Q r ** F) s ⟹ PRECOND (EXTRACT (Q' r s))"
  shows "wp c Q' s"
```

**Tags and named rule sets** (`thys/lib/Basic_VCG.thy`) — `PRECOND`
marks a side-condition that must be discharged (by a registered solver,
below) for the rule carrying it to be considered applicable; `PRIO`
attaches a numeral priority so rules are tried highest-first;
`VCG_DECOMP_RULE`/`VCG_DECOMP_ERULE`/`VCG_RULE` classify a rule as
pure-decomposition, elimination-style decomposition, or "needs framing"
respectively — only the third kind gets run through `Frame_Infer`'s
machinery to produce a *framed* rule before use:

```isabelle
definition [vcg_tag_defs]: "PRECOND Φ ≡ Φ"
definition PRIO :: "'a::numeral ⇒ bool" where [vcg_tag_defs]: "PRIO _ ≡ True"

named_theorems vcg_normalize_simps ‹Additional normalization rules›
named_theorems vcg_normalize_congs ‹Additional normalization congruences›
named_theorems vcg_normalize_nosplits ‹Split rules to be removed for normalization›

named_theorems vcg_decomp_rules
named_theorems vcg_decomp_erules
named_theorems vcg_rules
named_theorems vcg_frame_rules
named_theorems vcg_frame_erules

definition VCG_DECOMP_RULE :: "bool ⇒ bool" where [vcg_tag_defs]: "VCG_DECOMP_RULE x ≡ x"
definition VCG_DECOMP_ERULE :: "bool ⇒ bool" where [vcg_tag_defs]: "VCG_DECOMP_ERULE x ≡ x"
definition VCG_RULE :: "bool ⇒ bool" where [vcg_tag_defs]: "VCG_RULE x ≡ x"
```

**The tactic loop's ML surface**, structurally (`Basic_VCG.thy`, ML
`structure Basic_VCG`; quoted where the logic is small enough to be
worth quoting, described otherwise):

```isabelle
fun solve_precond_tac ctxt =
  resolve_tac ctxt @{thms PRECONDI} THEN_ELSE' (solve ctxt, K all_tac)

fun step_precond_tac ctxt tac =
  tac THEN_ALL_NEW_FWD solve_precond_tac ctxt

fun vcg_normalize_tac ctxt = let
  val ctxt = ctxt
    addsimps Named_Theorems.get ctxt @{named_theorems vcg_normalize_simps}
    |> fold Simplifier.add_cong (Named_Theorems.get ctxt @{named_theorems vcg_normalize_congs})
    |> fold Splitter.del_split (Named_Theorems.get ctxt @{named_theorems vcg_normalize_nosplits})
in CONCL_COND' (is_Trueprop) THEN_ELSE' (…clarsimp with conclusion-recovery…, K all_tac) end

fun vcg_step_tac ctxt =
  vcg_normalize_tac ctxt THEN_ALL_NEW (
    step_precond_tac ctxt (vcg_rl_tac ctxt)
    ORELSE' solve ctxt
  )
```

— i.e. one VCG step is: normalize (simp with `vcg_normalize_simps`,
splits pruned per `vcg_normalize_nosplits`, recovering the goal if the
simplifier buried it in the assumptions), then either apply one rule
(decomposition rule as-is, or a `vcg_rules`/`vcg_frame_rules` lemma
turned into a *framed* rule by `frame_rl` — which tries every
registered `vcg_frame_rules`/`vcg_frame_erules` combinator against the
raw rule until one type-checks, i.e. `htriple_vcg_frame_erule` above is
exactly such a combinator) and immediately discharge any `PRECOND`
subgoals the rule introduced via the solver registry, or (if no rule
applies) fall through to the solver registry directly. Rules are picked
by `biresolve_tac` over the list from `get_rules`, sorted by `PRIO`
descending (default priority 100 if untagged). The user-facing method
is the fixpoint of one step:

```isabelle
method vcg_rl = vcg_ensure_defer_slot, vcg_rl_internal
method vcg_step = vcg_ensure_defer_slot, vcg_step_internal
method vcg = vcg_ensure_defer_slot, vcg_step_internal+
```

**Solver registry**: keyed by an `Item_Net` indexed on the *conclusion*
of a registered trigger theorem, so a subgoal is dispatched to a solver
by matching its head constant — this is how `PRECOND (FRAME …)` reaches
`Frame_Infer.infer_tac` (§2's `add_solver` call) without the VCG engine
knowing anything about separation logic. Other default registrations in
the same file: `solve_asm` (assumption/`TrueI`/`refl`/`order_refl`, for
`SOLVE_ASM`-tagged pure goals), `solve_auto`/`solve_auto_defer`/
`solve_default_auto` (`auto_tac`, optionally deferring unsolved
schematic-free goals to a "defer slot" so later VCG steps can supply
missing instantiations first), `xform_normalize` (re-runs
`vcg_normalize_tac` on `NORMALIZE`-tagged goals). None of this is
separation-logic-specific; `Frame_Infer.thy`'s registration is the only
domain-specific solver in the whole engine, which is exactly the
"generic VCG, one pluggable solver per side-condition shape"
architecture design.md's P3 row asks `Ir/SepSolver.lean` to reproduce.

## 4. The separation-algebra class surface (the PCM interface)

From the AFP `Separation_Algebra` entry (imported by
`Sep_Algebra_Add.thy` as `"Separation_Algebra.Sep_Tactics"`) — the
carrier operations (`##` disjointness, `+`, `0`) and their axioms, in
two layers exactly as the source stacks them:

```isabelle
class pre_sep_algebra = zero + plus +
  fixes sep_disj :: "'a => 'a => bool" (infix "##" 60)
  assumes sep_disj_zero [simp]: "x ## 0"
  assumes sep_disj_commuteI: "x ## y ⟹ y ## x"
  assumes sep_add_zero [simp]: "x + 0 = x"
  assumes sep_add_commute: "x ## y ⟹ x + y = y + x"
  assumes sep_add_assoc:
    "⟦ x ## y; y ## z; x ## z ⟧ ⟹ (x + y) + z = x + (y + z)"
-- ‹begin…end block of derived lemmas (sep_disj_commute, sep_add_left_commute, …) elided›

class sep_algebra = pre_sep_algebra +
  assumes sep_disj_addD1: "⟦ x ## y + z; y ## z ⟧ ⟹ x ## y"
  assumes sep_disj_addI1: "⟦ x ## y + z; y ## z ⟧ ⟹ x + y ##  z"
begin

definition sep_conj :: "('a ⇒ bool) ⇒ ('a ⇒ bool) ⇒ ('a ⇒ bool)" (infixr "**" 35)
  where "P ** Q ≡ λh. ∃x y. x ## y ∧ h = x + y ∧ P x ∧ Q y"
notation sep_conj (infixr "∧*" 35)

definition sep_empty :: "'a ⇒ bool" ("□") where "□ ≡ λh. h = 0"

definition sep_impl :: "('a ⇒ bool) ⇒ ('a ⇒ bool) ⇒ ('a ⇒ bool)" (infixr "⟶*" 25)
  where "P ⟶* Q ≡ λh. ∀h'. h ## h' ∧ P h' ⟶ Q (h + h')"

definition sep_substate :: "'a => 'a => bool" (infix "⪯" 60) where
  "x ⪯ y ≡ ∃z. x ## z ∧ x + z = y"

abbreviation "sep_true ≡ 〈True〉"
abbreviation "sep_false ≡ 〈False〉"

definition sep_list_conj :: "('a ⇒ bool) list ⇒ ('a ⇒ bool)"  ("⋀* _" [60] 90) where
  "sep_list_conj Ps ≡ foldl (**) □ Ps"

-- ‹remainder of the begin…end block: ~90 lemmas of sep_conj/sep_impl/
   pure/intuitionistic/strictly_exact properties, elided — none of it
   is new axiomatic content, all derived from the definitions above›
end
```

`stronger_sep_algebra` — a single stronger disjointness axiom that
`sep_algebra`'s two follow from, and which `sep_conj`'s two ambient
notations (`**`/`∧*`) plus every product/function/option instance in
`Sep_Algebra_Add.thy` are actually stated against:

```isabelle
class stronger_sep_algebra = pre_sep_algebra +
  assumes sep_add_disj_eq [simp]: "y ## z ⟹ x ## y + z = (x ## y ∧ x ## z)"
begin
  lemma sep_disj_add_eq [simp]: "x ## y ⟹ x + y ## z = (x ## z ∧ y ## z)"
    by (metis sep_add_disj_eq sep_disj_commute)
  subclass sep_algebra by standard auto
end
```

The artifact's own addition on top (`Sep_Algebra_Add.thy`) —
`unique_zero_sep_algebra` (`x##x ⟹ x=0`, i.e. nothing overlaps itself
except the empty resource; this is the class every named-cell-style
instance in the file — `fun`, `option`, `prod`, and the `tsa_opt`
"trivial sep algebra option" type below — is actually pushed into):

```isabelle
class unique_zero_sep_algebra = stronger_sep_algebra +
  assumes unique_zero: "x##x ⟹ x=0"
```

`tsa_opt` — a two-constructor "empty or exactly one owned value" type,
`unique_zero_sep_algebra` by construction (`sep_disj` is "one side is
`ZERO`"), and *this*, not `option`, is the shape the artifact actually
uses when a single named/addressed thing is owned exactly-or-not-at-all:

```isabelle
datatype 'a tsa_opt = ZERO | TRIV (the_tsa: 'a)

instantiation tsa_opt :: (type) unique_zero_sep_algebra begin
  definition sep_disj_tsa_opt :: "'a tsa_opt ⇒ 'a tsa_opt ⇒ bool"
    where "a##b ⟷ a=ZERO ∨ b=ZERO"
  definition "a+b ≡ (case (a,b) of (ZERO,x) ⇒ x | (x,ZERO) ⇒ x)"
  definition "0 = ZERO"
end
```

Pure assertions, `EXACT`, and finite-family assertions — the vocabulary
`llvm_htriple` preconditions/postconditions above are built from, all
in `Sep_Algebra_Add.thy` (not the AFP: the AFP only has `pred_K Φ`,
which makes *no* claim about the heap; `↑Φ` additionally requires the
heap be `□`, which is what a deallocation-aware SL needs):

```isabelle
definition pred_lift :: "bool ⇒ 'a::sep_algebra ⇒ bool" ("↑_" [100] 100)
  where "(↑Φ) s ≡ Φ ∧ □ s"

definition pure_part :: "('a::sep_algebra ⇒ bool) ⇒ bool" where
  "pure_part A ≡ Ex A"

definition EXACT :: "'a::sep_algebra ⇒ 'a ⇒ bool" where [simp]: "EXACT h h' ≡ h'=h"
lemma strictly_exact_EXACT[simp]: "strictly_exact (EXACT h)"
lemma EXACT_split: "a##b ⟹ EXACT (a+b) = (EXACT a ** EXACT b)"
lemma EXACT_zero[simp]: "EXACT 0 = □"
```

`EXACT h` is "the resource is *precisely* `h`" — this is what `$c`
(§1's `time_credits_assn`, `SND (EXACT c)`, already quoted in
`p3-ir-sl-extracts.md`) and every points-to assertion below are stated
in terms of. `sep_set_img` (syntax `⋃*i∈I. P i`, `Sep_Algebra_Add.thy`
"Finite Assertion Families") folds `**` over a finite index set —
`ll_range` (§5) is `sep_set_img` over a pointer's index range, one
`ll_pto` conjunct per array cell — the natural model for "own a whole
named array" as a finite conjunction of "own this one named cell"
facts:

```isabelle
definition "sep_set_img S P ≡ ↑(finite S) ** sep_folding.F P S"
syntax "_SEP_SET_IMG" :: "pttrn ⇒ 'a set ⇒ ('b ⇒ bool) ⇒ ('b ⇒ bool)"  ("(3⋃*_∈_./ _)" [0, 0, 10] 10)
```

`entails`/`⊢` itself is **not** part of this AFP class surface — it is
`Frame_Infer.thy`'s own addition (§2), layered on top of the same
`sep_algebra` carrier.

## 5. Two credit-carrying htriples: load and store

The pointer/array assertion vocabulary (`LLVM_Shallow_RS.thy`,
"Pointers"/"Assertion to range of array") — `ll_pto` owns exactly one
cell's value at an address (via `FST`, i.e. the credit half of the
`(state,credit)` product is forced to `0` — a points-to fact carries no
credits of its own), `ll_range` owns a whole index range as a
`sep_set_img` of `ll_pto`s:

```isabelle
definition ll_pto :: "('a::llvm_rep, 'a ptr) dr_assn"
  where "ll_pto ≡ mk_assn (λv p. FST (llvm_pto (to_val v) (the_raw_ptr p)))"

definition "ll_range I ≡ mk_assn (λf p. ↑(abase p) ** (⋃*i∈I. ↿ll_pto (f i) (p +⇩a i)))"
```

The single-cell pair — the load/store acceptance shape at its simplest
(`llvm_htriple`, proved `by vcg` — the whole proof is one VCG run
against `ll_load_def`/`ll_store_def` unfolded, nothing hand-written):

```isabelle
lemma ll_load_rule[vcg_rules]:
  "llvm_htriple ($$ ''load'' 1 ** ↿ll_pto x p) (ll_load p) (λr. ↑(r=x) ** ↿ll_pto x p)"
  unfolding ll_load_def ll_pto_def by vcg

lemma ll_store_rule[vcg_rules]:
  "llvm_htriple ($$ ''store'' 1 ** ↿ll_pto xx p) (ll_store x p) (λ_. ↿ll_pto x p)"
  unfolding ll_store_def ll_pto_def by vcg
```

Reading `ll_load_rule`: pay one `''load''` credit, own the cell `p ↦
x`; get back `x`, still owning `p ↦ x` (load doesn't consume the cell).
`ll_store_rule`: pay one `''store''` credit, own `p ↦ xx` for *any*
prior value `xx`; after, own `p ↦ x` — the new value. This is precisely
the shape design.md's array `get`/`set` triples (`Ir/Triples.lean`) are
asked to reproduce over named cells instead of addresses.

The array/range pair — the direct acceptance-shape precedent for *our*
array get/set (same file, "Rules for load and store from indexed
pointer, wrt. range"; proofs are three-line VCG scripts —
`fri_extract_basic`/`open_ll_range` opens the `sep_set_img` at the
indexed cell, `fri_extract`+`vcg` close the rest — elided, not
hand-reasoning):

```isabelle
lemma ll_load_rule_range[vcg_rules]:
  shows "llvm_htriple ($$ ''load'' 1 ** ↿(ll_range I) a p ** ↑⇩!( p' ~⇩a p ∧ p' -⇩a p ∈ I ))
    (ll_load p') (λr. ↑(r = a (p' -⇩a p)) ** ↿(ll_range I) a p)"
  unfolding vcg_tag_defs
  apply (rule htriple_vcgI') apply fri_extract_basic
  apply (simp add: open_ll_range) apply fri_extract by vcg

lemma ll_store_rule_range[vcg_rules]:
  shows "llvm_htriple ($$ ''store'' 1 ** ↿(ll_range I) a p ** ↑⇩!( p' ~⇩a p ∧ p' -⇩a p ∈ I ))
    (ll_store x p') (λ_. ↿(ll_range I) (a(p' -⇩a p := x)) p)"
  unfolding vcg_tag_defs
  apply (rule htriple_vcgI') apply fri_extract_basic
  apply (simp add: open_ll_range) apply fri_extract by vcg
```

(`↑⇩!Φ` is `pred_lift_AUTO`, `Basic_VCG.thy`'s `↑SOLVE_AUTO Φ` — a pure
side-condition tagged for the `solve_auto` solver, §3; `~⇩a`/`-⇩a`/`+⇩a`
are the `addr_algebra` compatibility/difference/offset operations the
pointer-arithmetic side condition is stated over.) Reading
`ll_load_rule_range`: own the whole range `I` as array `a` based at
`p`; provided the accessed pointer `p'` is compatible with `p` and its
offset lands in `I`, loading `p'` costs one `''load''` credit and
returns `a` at that offset, the whole range assertion unchanged. This —
own-the-whole-array, index-bounds as a *side condition* discharged by
the auto-solver, single-cell read/write leaving the rest of the array
assertion untouched — is exactly the shape our array `get`/`set`
triples need, translated from "index compatible with base pointer" to
"index `<` array length" over named-cell arrays.

## Gaps

- `wp_get`/`wp_set` do not exist under any name in the six files
  fetched (confirmed by grep across all of them); noted in §1 as an
  absence rather than an extract.
- The `cost_framework` instance's own four-assumption discharge (the
  `interpretation cost_framework le_cost_ecost minus_ecost_cost` proof,
  §1) is five lines of `metis`/`smt`/`meson` automation over `enat`
  arithmetic with no calculus content beyond "this is what `ℕ∞`
  truncated subtraction happens to satisfy" — elided per the task's
  "ML bodies elided with structural description" instruction, extended
  here to a dense automated Isar proof of the same character.
- `thys/lib/Sep_Tactics.thy`'s AFP precursor (fetched, 4113 b) was not
  quoted: it is pure `sep_select`/`sep_subst` tactic scaffolding,
  superseded for VCG purposes by `Frame_Infer.thy`'s own
  `sep_drule`/`sep_rule` (already in `p3-ir-sl-extracts.md`'s
  companion file's scope, not re-quoted here).
- `Separation_Algebra.thy`/`Sep_Tactics.thy` were fetched from the
  `mirror-afp-2020` GitHub mirror rather than a source contemporary
  bit-for-bit with the artifact's exact Isabelle version; the class
  surface is stable (28808 b there vs 28990 b in the current AFP-devel
  mirror, no semantic difference in the definitions quoted) but this
  is not the same byte-exact guarantee as the `isabelle_llvm_time`
  quotes above, which are pinned to the artifact's own commit. Flagged
  for Jan's review per the provenance note at the top of this file.
- `thys/basic/kernel/LLVM_Shallow_RS.thy` does not exist at this pin —
  the file actually named that (containing `llSTATE`/`ll_α`/
  `llvm_htriple`) lives at `thys/vcg/LLVM_Shallow_RS.thy`;
  `p3-ir-sl-extracts.md`'s header listed the wrong directory for it
  (harmless, since the extract itself came from the right file) — noted
  here so a future re-fetch doesn't stumble on the same path.

## Port notes for `Ir/Assn`+`Wp`+`Triples`+`SepSolver`

`Ir/Wp.lean` should define `Ir.wp` exactly at `cost_framework`'s
generality: a two-parameter class fixing `I : Cost → ECost → Prop` and
`minus : ECost → Cost → ECost` with the four laws above, then `wp c Q ≡
fun (s, cr) => <case on Ir semantics> ∧ I c cr` — `frame_rule`/
`cons_rule` follow for free from one `wp_comm_inf`-shaped lemma, exactly
as `generic_wp` gives them to every instance here. Default the IR's
own instance to `le_cost_ecost`/`minus_ecost_cost`'s shape (`ℕ` vs `ℕ∞`
pointwise), i.e. reuse the *proof*, not just the type, since it is
already generic over the currency-name type. `Ir/Assn.lean`'s PCM
should be built from `pre_sep_algebra`→`sep_algebra`→
`stronger_sep_algebra`→`unique_zero_sep_algebra` in that order (only
the last is actually used downstream), with named cells modeled as
`tsa_opt`-shaped (`Empty | Owned val`) rather than `Option`, since
`tsa_opt` is already `unique_zero_sep_algebra` and `Option` here is not
proved to be. `EXACT`/`pred_lift`(`↑`)/`sep_set_img`(finite family `**`)
port verbatim — `sep_set_img` in particular is the right shape for "own
a whole named array," one `tsa_opt`-cell conjunct per index, matching
`ll_range`'s architecture but over names instead of an address range
compatibility side-condition (ledger D2: drop the `abase`/`~⇩a`/`-⇩a`
pointer-compatibility side-conditions entirely, since named cells need
no such notion — an index bound check replaces it). `Ir/Triples.lean`'s
`get`/`set` triples should mirror `ll_load_rule`/`ll_store_rule`'s
single-cell shape and `ll_load_rule_range`/`ll_store_rule_range`'s
array shape one-for-one, replacing pointer-arithmetic side conditions
with `i < a.length`. `Ir/SepSolver.lean` should port
`Frame_Infer.thy`'s four structural rules (`fri_prepare`/`fri_end`/
`fri_step_rl`/`fri_reduce_rl`) and its rotate-then-match search loop
verbatim (§2) — the algorithm is small and entirely non-HOU (matches
one leading conjunct at a time by literal rotation, never higher-order
unification), which is exactly why it was judged portable under Lean's
weaker HOU in `design.md`'s P3 row. The registered-solver architecture
(§3: a table keyed by a tagged goal's head constant, `PRECOND`/`PRIO`
tags, `vcg_decomp_rules`/`vcg_rules`/`vcg_frame_rules` split by whether
framing is needed) is worth reproducing as `Ir/Wp.lean`'s VCG driver
structure even though it is infrastructure, not calculus (charter rule
3): it is what makes `SepSolver` pluggable into the same driver rather
than hand-wired, and it is a small, legible piece of ML with a direct
Lean 4 `MetaM`/attribute-table analogue. Block/address memory model
divergence (ledger D2) is confined to exactly two places in everything
above: the `abase`/pointer-compatibility side conditions in
`ll_range`'s htriples (replaced by index-bound checks) and `ll_pto`'s
underlying `llvm_pto`/raw-pointer definition (replaced by a named-cell
lookup) — the locale, the credit machinery, the frame solver, and the
VCG driver are all address-agnostic and port with no shape change at
all.
