import Lax13Proofs.Refine.Ir.Wp

/-!
The IR's credit-carrying Hoare triples, one per operation.

Port of the rule *shapes* of `thys/vcg/LLVM_Shallow_RS.thy` at the pin
recorded in `plans/word-ram/refinement-tower/design.md` §1
(`isabelle_llvm_time` @ `42dd7f5`), quoted in
`plans/word-ram/refinement-tower/p3-sl-deep-extracts.md` §5:

```isabelle
lemma ll_load_rule[vcg_rules]:
  "llvm_htriple ($$ ''load'' 1 ** ↿ll_pto x p) (ll_load p) (λr. ↑(r=x) ** ↿ll_pto x p)"
lemma ll_store_rule[vcg_rules]:
  "llvm_htriple ($$ ''store'' 1 ** ↿ll_pto xx p) (ll_store x p) (λ_. ↿ll_pto x p)"
```

and their range variants `ll_load_rule_range` / `ll_store_rule_range`,
plus the loop rule `llc_while_annot_rule` of the same file. Read
`ll_load_rule` as the extract does — "pay one `load` credit, own the
cell `p ↦ x`; get back `x`, still owning `p ↦ x`" — and every rule below
is that sentence with a name in place of an address.

Two structural facts make these one-liners rather than VCG scripts:
`Wp.lean`'s equation suite (each primitive's `wp` is `wp_consume` glued
to the op's effect) and `Assn.lean`'s four extraction lemmas
(`ptoVar_vars` / `ptoVar_setVar` / `ptoArr_arrs` / `ptoArr_setArr`) plus
`costCredits_split`. The source's proofs are `by vcg`, i.e. its solver
does the same three steps; wave C's `Ir/SepSolver.lean` is what turns
these applications into a tactic.

## Judgment calls

**D-t — the single-cell and the range rule coincide.** The source needs
two array rules (`ll_load_rule` at one `ll_pto`, `ll_load_rule_range` at
an `ll_range`) because an LLVM array is an address range whose ownership
splits index by index. Ours has one, because `a ↦ₐ xs` owns the whole
named array (judgment call D-m of `Assn.lean`) — `aget_rule` *is* the
range rule, with the source's pointer-compatibility side conditions
(`p' ~ₐ p ∧ p' -ₐ p ∈ I`) replaced by the index bound `k < xs.length`,
exactly as the extract's port notes prescribe.

**D-u — side conditions are hypotheses of the rule, not `↑!` conjuncts
of the precondition.** The source writes `↑⇩!(…)`, a pure conjunct
tagged for its auto-solver, because its rules are applied by an ML
tactic that must discharge them on the spot. Ours are applied by term
application until wave C lands the solver, so they are ordinary Lean
hypotheses; `aget_rule_pure` below records that the two shapes are one
`cons_rule` step apart, and it is the shape wave C will register.

**D-v — every rule comes in two forms.** `…_triple` is the exact triple
(`htriple`), `…_rule` the garbage-collecting one
(`irHtriple = htripleGc GC irα`, the source's `llvm_htriple`), derived
by `htriple_to_gc`. The source only ever states the second; the first is
kept because P4 composes triples, and composing exact triples does not
leak a `GC` into every intermediate assertion.

**D-w — aliasing is handled by the logic, not by side conditions.**
`copy_rule` needs no `x ≠ y` and `binop_rule` no `y ≠ z`: if the names
coincide the precondition contains `x ↦ᵥ v ∗ x ↦ᵥ w`, which is
`sepFalse` (`Assn.lean`'s `ptoVar_sepConj_self`), so the triple holds
vacuously and is simply not applicable. This is the source's discipline
for pointers, unchanged. A consumer that really wants `x := y ⊕ y` gets
it from Sepref's monadify phase, which splits duplicate arguments
(design record §3, P4 row 2).

**D-x — the loop rule is `llc_while_annot_rule`'s, with the invariant
carrying the credits.** The source's rule takes an annotated invariant
`I σ t` over an abstract loop state and a well-founded `R`, frames it
through the body, and charges one `''call''` credit per iteration
entered. Ours takes `Inv : τ → Assn` and the same well-founded `r`,
charges one `ir.while` credit per guard evaluation (judgment call D-h of
`Semantics.lean`), and requires the body to re-establish
`∃ᵃ t', ⌜r t' t⌝ ∗ ¤¤ir.while 1 ∗ Inv t'` — i.e. the invariant must hold
the credits for the iterations still to come. That *is* the ESOP'21
per-iteration discipline: `credits_add` splits one iteration's price off
the balance the invariant carries.
-/

namespace Lax13Proofs.Refine.Ir

/-! ## 1. The two triple forms -/

/-- The exact triple: `htriple` at the IR's `wp` and abstraction, with
the postcondition at `R = Unit` (judgment call D-q of `Wp.lean`). -/
abbrev irTriple (P : Assn) (c : Com) (Q : Assn) : Prop :=
  htriple wp irα P c (fun (_ : Unit) => Q)

/-- The source's `llvm_htriple ≡ htriple_gc GC ll_α`: the triple every
`…_rule` below is stated in, whose postcondition absorbs whatever the
program did not spend. -/
abbrev irHtriple (P : Assn) (c : Com) (Q : Assn) : Prop :=
  htripleGc wp GC irα P c (fun (_ : Unit) => Q)

/-- The source's `htriple_to_gc`, at the IR. -/
theorem irTriple.gc {P : Assn} {c : Com} {Q : Assn} (h : irTriple P c Q) : irHtriple P c Q :=
  htriple_to_gc empty_ent_GC h

/-! ## 2. The per-op triples

Each pays exactly `¤¤"ir.<op>" 1` — the currency `Syntax.lean` declares
for that op and the semantics charges for it — and owns exactly the
names it touches. -/

/-- `skip`: pay for it, and that is all (judgment call D-c of
`Syntax.lean`: `skip` is not free, because IMP+ charges for it). -/
theorem skip_triple : irTriple (¤¤Currency.skip 1) .skip (□ : Assn) := by
  intro F p hp
  obtain ⟨s, cr⟩ := p
  obtain ⟨hafford, hrest⟩ := costCredits_split hp
  rw [wp_skip]
  refine ⟨hafford, ?_⟩
  rw [emp_sepConj]
  exact hrest

/-- `x := n`: own the destination cell, whatever it held. -/
theorem const_triple (x : String) (n v : Val) :
    irTriple (¤¤Currency.const 1 ∗ x ↦ᵥ v) (.const x n) (x ↦ᵥ n) := by
  intro F p hp
  obtain ⟨s, cr⟩ := p
  rw [sepConj_assoc] at hp
  obtain ⟨hafford, hrest⟩ := costCredits_split hp
  rw [wp_const]
  refine ⟨by rw [ptoVar_vars hrest]; simp, hafford, ptoVar_setVar hrest⟩

/-- `x := y`: the source's `ll_load_rule` shape at scalar cells — the
source cell is kept, the destination is overwritten. -/
theorem copy_triple (x y : String) (v w : Val) :
    irTriple (¤¤Currency.copy 1 ∗ x ↦ᵥ v ∗ y ↦ᵥ w) (.copy x y) (x ↦ᵥ w ∗ y ↦ᵥ w) := by
  intro F p hp
  obtain ⟨s, cr⟩ := p
  rw [sepConj_assoc] at hp
  obtain ⟨hafford, hrest⟩ := costCredits_split hp
  rw [sepConj_assoc] at hrest
  have hy : s.vars y = some w := ptoVar_vars (irSTATE_rot hrest)
  rw [wp_copy]
  refine ⟨by rw [ptoVar_vars hrest]; simp, w, hy, hafford, ?_⟩
  rw [sepConj_assoc]
  exact ptoVar_setVar hrest

/-- `x := y ⊕ z`, one rule for all nine operators: the currency is
`binopCurrency op` and the value is IMP+'s own `Bop.apply` (judgment
call D-a of `Syntax.lean`), so no operator can drift between the
semantics, this rule and P5's lowering. -/
theorem binop_triple (op : Imp.Bop) (x y z : String) (v m n : Val) :
    irTriple (¤¤(binopCurrency op) 1 ∗ x ↦ᵥ v ∗ y ↦ᵥ m ∗ z ↦ᵥ n) (.binop op x y z)
      (x ↦ᵥ op.apply m n ∗ y ↦ᵥ m ∗ z ↦ᵥ n) := by
  intro F p hp
  obtain ⟨s, cr⟩ := p
  rw [sepConj_assoc] at hp
  obtain ⟨hafford, hrest⟩ := costCredits_split hp
  rw [sepConj_assoc, sepConj_assoc] at hrest
  have hy : s.vars y = some m := ptoVar_vars (irSTATE_rot hrest)
  have hz : s.vars z = some n := ptoVar_vars (irSTATE_rot3 hrest)
  rw [wp_binop]
  refine ⟨by rw [ptoVar_vars hrest]; simp, m, n, hy, hz, hafford, ?_⟩
  rw [sepConj_assoc, sepConj_assoc]
  exact ptoVar_setVar hrest

/-- `x := x ⊕ z`, the in-place case. Judgment call D-w says the general
rule is simply inapplicable when the destination is an operand, because
its precondition is then `sepFalse`; in-place update is far too common
to leave to the monadify phase (`i := i + one` is every loop's step), so
the aliased instance gets its own rule, owning the one cell once. Its
proof is `binop_triple`'s with `y := x`. -/
theorem binop_self_triple (op : Imp.Bop) (x z : String) (m n : Val) :
    irTriple (¤¤(binopCurrency op) 1 ∗ x ↦ᵥ m ∗ z ↦ᵥ n) (.binop op x x z)
      (x ↦ᵥ op.apply m n ∗ z ↦ᵥ n) := by
  intro F p hp
  obtain ⟨s, cr⟩ := p
  rw [sepConj_assoc] at hp
  obtain ⟨hafford, hrest⟩ := costCredits_split hp
  rw [sepConj_assoc] at hrest
  have hx : s.vars x = some m := ptoVar_vars hrest
  have hz : s.vars z = some n := ptoVar_vars (irSTATE_rot hrest)
  rw [wp_binop]
  refine ⟨by rw [hx]; simp, m, n, hx, hz, hafford, ?_⟩
  rw [sepConj_assoc]
  exact ptoVar_setVar hrest

/-- `x := a[i]`: the source's `ll_load_rule_range`, at a named array
(judgment calls D-t, D-u). The array assertion is unchanged — a read
does not consume the array — and the index bound is the side condition
its pointer-compatibility premises become. -/
theorem aget_triple (x a i : String) (v k w : Val) (xs : List Val) (hw : xs[k]? = some w) :
    irTriple (¤¤Currency.aget 1 ∗ x ↦ᵥ v ∗ a ↦ₐ xs ∗ i ↦ᵥ k) (.aget x a i)
      (x ↦ᵥ w ∗ a ↦ₐ xs ∗ i ↦ᵥ k) := by
  intro F p hp
  obtain ⟨s, cr⟩ := p
  rw [sepConj_assoc] at hp
  obtain ⟨hafford, hrest⟩ := costCredits_split hp
  rw [sepConj_assoc, sepConj_assoc] at hrest
  have ha : s.arrs a = some xs := ptoArr_arrs (irSTATE_rot hrest)
  have hi : s.vars i = some k := ptoVar_vars (irSTATE_rot3 hrest)
  rw [wp_aget]
  refine ⟨by rw [ptoVar_vars hrest]; simp, k, xs, w, hi, ha, hw, hafford, ?_⟩
  rw [sepConj_assoc, sepConj_assoc]
  exact ptoVar_setVar hrest

/-- `a[i] := v`: the source's `ll_store_rule_range`. The array is
returned updated at the one index, everything else in it untouched. -/
theorem aset_triple (a i v : String) (k n : Val) (xs : List Val) (hk : k < xs.length) :
    irTriple (¤¤Currency.aset 1 ∗ a ↦ₐ xs ∗ i ↦ᵥ k ∗ v ↦ᵥ n) (.aset a i v)
      (a ↦ₐ xs.set k n ∗ i ↦ᵥ k ∗ v ↦ᵥ n) := by
  intro F p hp
  obtain ⟨s, cr⟩ := p
  rw [sepConj_assoc] at hp
  obtain ⟨hafford, hrest⟩ := costCredits_split hp
  rw [sepConj_assoc, sepConj_assoc] at hrest
  have hi : s.vars i = some k := ptoVar_vars (irSTATE_rot hrest)
  have hv : s.vars v = some n := ptoVar_vars (irSTATE_rot3 hrest)
  have ha : s.arrs a = some xs := ptoArr_arrs hrest
  rw [wp_aset]
  refine ⟨k, n, xs, hi, hv, ha, hk, hafford, ?_⟩
  rw [sepConj_assoc, sepConj_assoc]
  exact ptoArr_setArr hrest

/-! ### The garbage-collecting forms

The source states only these (`llvm_htriple` *is* `htriple_gc GC ll_α`);
`Triples.lean` keeps both (judgment call D-v). -/

theorem skip_rule : irHtriple (¤¤Currency.skip 1) .skip (□ : Assn) := skip_triple.gc

theorem const_rule (x : String) (n v : Val) :
    irHtriple (¤¤Currency.const 1 ∗ x ↦ᵥ v) (.const x n) (x ↦ᵥ n) := (const_triple x n v).gc

theorem copy_rule (x y : String) (v w : Val) :
    irHtriple (¤¤Currency.copy 1 ∗ x ↦ᵥ v ∗ y ↦ᵥ w) (.copy x y) (x ↦ᵥ w ∗ y ↦ᵥ w) :=
  (copy_triple x y v w).gc

theorem binop_rule (op : Imp.Bop) (x y z : String) (v m n : Val) :
    irHtriple (¤¤(binopCurrency op) 1 ∗ x ↦ᵥ v ∗ y ↦ᵥ m ∗ z ↦ᵥ n) (.binop op x y z)
      (x ↦ᵥ op.apply m n ∗ y ↦ᵥ m ∗ z ↦ᵥ n) := (binop_triple op x y z v m n).gc

theorem binop_self_rule (op : Imp.Bop) (x z : String) (m n : Val) :
    irHtriple (¤¤(binopCurrency op) 1 ∗ x ↦ᵥ m ∗ z ↦ᵥ n) (.binop op x x z)
      (x ↦ᵥ op.apply m n ∗ z ↦ᵥ n) := (binop_self_triple op x z m n).gc

theorem aget_rule (x a i : String) (v k w : Val) (xs : List Val) (hw : xs[k]? = some w) :
    irHtriple (¤¤Currency.aget 1 ∗ x ↦ᵥ v ∗ a ↦ₐ xs ∗ i ↦ᵥ k) (.aget x a i)
      (x ↦ᵥ w ∗ a ↦ₐ xs ∗ i ↦ᵥ k) := (aget_triple x a i v k w xs hw).gc

theorem aset_rule (a i v : String) (k n : Val) (xs : List Val) (hk : k < xs.length) :
    irHtriple (¤¤Currency.aset 1 ∗ a ↦ₐ xs ∗ i ↦ᵥ k ∗ v ↦ᵥ n) (.aset a i v)
      (a ↦ₐ xs.set k n ∗ i ↦ᵥ k ∗ v ↦ᵥ n) := (aset_triple a i v k n xs hk).gc

/-- The source's own shape for an array rule, with the index bound as a
pure conjunct of the precondition rather than a hypothesis (judgment
call D-u): the two are one `cons_rule` step apart, and this is the form
wave C's solver will register. -/
theorem aget_rule_pure (x a i : String) (v k : Val) (xs : List Val) :
    irHtriple (⌜k < xs.length⌝ ∗ ¤¤Currency.aget 1 ∗ x ↦ᵥ v ∗ a ↦ₐ xs ∗ i ↦ᵥ k) (.aget x a i)
      (x ↦ᵥ xs.getD k 0 ∗ a ↦ₐ xs ∗ i ↦ᵥ k) := by
  intro F p hp
  rw [sepConj_assoc, predLift_sepConj_iff] at hp
  obtain ⟨hk, hp⟩ := hp
  have hw : xs[k]? = some (xs.getD k 0) := by
    rw [List.getElem?_eq_getElem hk]
    simp [List.getD, List.getElem?_eq_getElem hk]
  exact aget_rule x a i v k _ xs hw F p hp

/-! ## 3. The structural rules -/

/-- Sequential composition: the source's `bind` rule at `seq` (judgment
call D-r of `Wp.lean`), through `wp_seq`. -/
theorem seq_triple {P R Q : Assn} {c d : Com} (hc : irTriple P c R) (hd : irTriple R d Q) :
    irTriple P (.seq c d) Q := by
  intro F p hp
  rw [wp_seq]
  refine wp_mono_ir (fun _ q hq => ?_) (hc F p hp)
  exact hd F q hq

/-- A conditional: pay for the test, then run the branch the guard
selects. The guard's value must be determined by the precondition — the
source gets this for free because its `llc_if` tests a *register* whose
value the assertion fixes; ours reads cells, so the hypothesis says so
explicitly, and `ptoVar_vars` is what discharges it. -/
theorem ite_triple {P Q : Assn} {b : Cond} {c d : Com} {t : Bool}
    (hb : ∀ (F : Assn) (s : State) (cr : ECost), irSTATE (P ∗ F) (s, cr) → b.eval s = some t)
    (hbr : irTriple P (if t then c else d) Q) :
    irTriple (¤¤Currency.ite 1 ∗ P) (.ite b c d) Q := by
  intro F p hp
  obtain ⟨s, cr⟩ := p
  rw [sepConj_assoc] at hp
  obtain ⟨hafford, hrest⟩ := costCredits_split hp
  rw [wp_ite]
  exact ⟨t, hb F s _ hrest, hafford, hbr F _ hrest⟩

/-- The source's `llc_while_annot_rule` (judgment call D-x): an
invariant indexed by a measure, a well-founded relation on the measure,
one `ir.while` credit per guard evaluation, and a body that
re-establishes the invariant — with the next iteration's credits — at a
smaller measure. -/
theorem while_triple {τ : Type} {r : τ → τ → Prop} (hwf : WellFounded r) {Inv : τ → Assn}
    {Q : Assn} {b : Cond} {c : Com} {g : τ → Bool}
    (hguard : ∀ (F : Assn) (t : τ) (s : State) (cr : ECost),
      irSTATE ((¤¤Currency.«while» 1 ∗ Inv t) ∗ F) (s, cr) → b.eval s = some (g t))
    (hbody : ∀ t, g t = true →
      irTriple (Inv t) c (∃ᵃ t', ⌜r t' t⌝ ∗ ¤¤Currency.«while» 1 ∗ Inv t'))
    (hexit : ∀ t, g t = false → Inv t ⊢ Q)
    (t₀ : τ) : irTriple (¤¤Currency.«while» 1 ∗ Inv t₀) (.while b c) Q := by
  intro F p hp
  refine wp_while_wf (r := r) hwf
    (J := fun t q => irSTATE ((¤¤Currency.«while» 1 ∗ Inv t) ∗ F) q) ?_ hp
  intro t s cr hJ
  have hg := hguard F t s cr hJ
  rw [sepConj_assoc] at hJ
  obtain ⟨hafford, hrest⟩ := costCredits_split hJ
  refine ⟨hafford, g t, hg, ?_, ?_⟩
  · intro ht
    refine wp_mono_ir (fun _ q hq => ?_) (hbody t ht F _ hrest)
    rw [sepEx_sepConj] at hq
    obtain ⟨t', hq⟩ := hq
    rw [sepConj_assoc, predLift_sepConj_iff] at hq
    exact ⟨t', hq.1, hq.2⟩
  · intro ht
    exact conj_entails_mono (hexit t ht) (entails_refl F) _ hrest

theorem seq_rule {P R Q : Assn} {c d : Com} (hc : irTriple P c R) (hd : irTriple R d Q) :
    irHtriple P (.seq c d) Q := (seq_triple hc hd).gc

theorem ite_rule {P Q : Assn} {b : Cond} {c d : Com} {t : Bool}
    (hb : ∀ (F : Assn) (s : State) (cr : ECost), irSTATE (P ∗ F) (s, cr) → b.eval s = some t)
    (hbr : irTriple P (if t then c else d) Q) :
    irHtriple (¤¤Currency.ite 1 ∗ P) (.ite b c d) Q := (ite_triple hb hbr).gc

theorem while_rule {τ : Type} {r : τ → τ → Prop} (hwf : WellFounded r) {Inv : τ → Assn}
    {Q : Assn} {b : Cond} {c : Com} {g : τ → Bool}
    (hguard : ∀ (F : Assn) (t : τ) (s : State) (cr : ECost),
      irSTATE ((¤¤Currency.«while» 1 ∗ Inv t) ∗ F) (s, cr) → b.eval s = some (g t))
    (hbody : ∀ t, g t = true →
      irTriple (Inv t) c (∃ᵃ t', ⌜r t' t⌝ ∗ ¤¤Currency.«while» 1 ∗ Inv t'))
    (hexit : ∀ t, g t = false → Inv t ⊢ Q)
    (t₀ : τ) : irHtriple (¤¤Currency.«while» 1 ∗ Inv t₀) (.while b c) Q :=
  (while_triple hwf hguard hbody hexit t₀).gc

/-! ## 4. The gate (ledger D4)

Two of wave A's three gate programs, run end to end: an assertion, a
triple, a `wp`, and — through `wp`'s own definition — a `BigStep` whose
final state and cost vector are the ones `Semantics.lean`'s gate pinned.
Then the negative control: with one credit too few, the triple is *not*
derivable. -/

namespace Gate

/-! Wave A's own `roundtrip` (`x := A[i]; A[j] := x`) and its state
`roundtripState` (`A = [3,1,4]`, `i = 0`, `j = 2`), reused verbatim from
`Semantics.lean`'s gate — the programs the wave-A gate pinned by
`#guard` are the programs this wave proves triples about. -/

/-- The precondition: one `aget` credit, one `aset` credit, and the four
names the program touches. -/
def rtPre : Assn :=
  ¤¤Currency.aget 1 ∗ ¤¤Currency.aset 1 ∗
    "x" ↦ᵥ 0 ∗ "A" ↦ₐ [3, 1, 4] ∗ "i" ↦ᵥ 0 ∗ "j" ↦ᵥ 2

/-- The intermediate assertion: after the read, before the write. -/
def rtMid : Assn :=
  ¤¤Currency.aset 1 ∗ "A" ↦ₐ [3, 1, 4] ∗ "j" ↦ᵥ 2 ∗ "x" ↦ᵥ 3 ∗ "i" ↦ᵥ 0

/-- The postcondition: the array updated at index 2, the cells as the
run leaves them — the state `Semantics.lean`'s gate pinned by `#guard`. -/
def rtPost : Assn :=
  "A" ↦ₐ [3, 1, 3] ∗ "j" ↦ᵥ 2 ∗ "x" ↦ᵥ 3 ∗ "i" ↦ᵥ 0

theorem rt_set : ([3, 1, 4] : List Val).set 2 3 = [3, 1, 3] := rfl

/-- The first half, framed by what the write will need. -/
theorem rt_aget : irTriple rtPre (.aget "x" "A" "i") rtMid := by
  have h := frame_rule (¤¤Currency.aset 1 ∗ "j" ↦ᵥ 2)
    (aget_triple "x" "A" "i" 0 0 3 [3, 1, 4] (by decide))
  have e₁ : rtPre = (¤¤Currency.aget 1 ∗ "x" ↦ᵥ 0 ∗ "A" ↦ₐ [3, 1, 4] ∗ "i" ↦ᵥ 0) ∗
      (¤¤Currency.aset 1 ∗ "j" ↦ᵥ 2) := by
    unfold rtPre; ac_rfl
  have e₂ : ("x" ↦ᵥ 3 ∗ "A" ↦ₐ [3, 1, 4] ∗ "i" ↦ᵥ 0) ∗ (¤¤Currency.aset 1 ∗ "j" ↦ᵥ 2)
      = rtMid := by
    unfold rtMid; ac_rfl
  rw [e₁, ← e₂]
  exact h

/-- The second half, framed by the cell the write does not touch. -/
theorem rt_aset : irTriple rtMid (.aset "A" "j" "x") rtPost := by
  have h := frame_rule ("i" ↦ᵥ 0) (aset_triple "A" "j" "x" 2 3 [3, 1, 4] (by decide))
  rw [rt_set] at h
  have e₁ : rtMid = (¤¤Currency.aset 1 ∗ "A" ↦ₐ [3, 1, 4] ∗ "j" ↦ᵥ 2 ∗ "x" ↦ᵥ 3) ∗
      ("i" ↦ᵥ 0) := by
    unfold rtMid; ac_rfl
  have e₂ : ("A" ↦ₐ [3, 1, 3] ∗ "j" ↦ᵥ 2 ∗ "x" ↦ᵥ 3) ∗ ("i" ↦ᵥ 0) = rtPost := by
    unfold rtPost; ac_rfl
  rw [e₁, ← e₂]
  exact h

/-- …composed: the whole program, one triple, two credits. -/
theorem rt_triple : irTriple rtPre roundtrip rtPost := seq_triple rt_aget rt_aset

/-- …and in the source's garbage-collecting form. -/
theorem rt_rule : irHtriple rtPre roundtrip rtPost := rt_triple.gc

/-- The balance the triple asks for: one `aget`, one `aset`. -/
def rtBalance : ECost :=
  ACost.cost Currency.aget (1 : ℕ∞) + ACost.cost Currency.aset (1 : ℕ∞)

/-- The frame: everything in wave A's state that `rtPre` does not own —
which, at that state, is nothing at all, but writing it as an `EXACT`
resource is what lets the assertion be checked by `rfl` rather than by
extensionality over the name space. -/
def rtFrame : Assn :=
  EXACT (((((vcells roundtripState).erase "x").erase "i").erase "j",
    (acells roundtripState).erase "A", hcells roundtripState), 0)

/-- The precondition really does hold of wave A's state: each conjunct
is checked by kernel computation on the state's association lists. -/
theorem rtPre_holds : irSTATE (rtPre ∗ rtFrame) (roundtripState, rtBalance) := by
  show (rtPre ∗ rtFrame)
    ((vcells roundtripState, acells roundtripState, hcells roundtripState), rtBalance)
  simp only [rtPre, sepConj_assoc, costCredits_def]
  refine credits_sepConj_iff.2 ⟨ACost.cost Currency.aset (1 : ℕ∞), rfl, ?_⟩
  refine credits_sepConj_iff.2 ⟨0, (add_zero _).symm, ?_⟩
  refine ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  refine ptoArr_sepConj_iff.2 ⟨rfl, ?_⟩
  refine ptoVar_sepConj_iff.2 ⟨rfl, ?_⟩
  exact ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩

/-- End to end: the assertion holds of wave A's state, so the triple's
`wp` holds, so the program *runs* — and the array it leaves behind is
read off the postcondition, while its cost is the one wave A's `#guard`
pinned. -/
theorem rt_runs :
    ∃ s' κ, BigStep roundtrip roundtripState s' κ ∧ s'.arrs "A" = some [3, 1, 3] ∧
      κ.toFun Currency.aget = 1 ∧ κ.toFun Currency.aset = 1 ∧ κ.toFun Currency.«while» = 0 := by
  obtain ⟨s', κ, hrun, hpost, -⟩ := rt_triple rtFrame (roundtripState, rtBalance) rtPre_holds
  refine ⟨s', κ, hrun, ?_, ?_, ?_, ?_⟩
  · exact ptoArr_arrs (by simpa only [rtPost, sepConj_assoc] using hpost)
  all_goals
    obtain ⟨-, rfl⟩ := hrun.unique roundtrip_bigStep
    rfl

/-! ### The loop rule, on wave A's `countdown`

`one := 1; while 0 < n do n := n - one`, the third of wave A's gate
programs. The invariant is indexed by the value of `n`, and it *carries
the credits for the iterations still to come* — `k • (ir.while + ir.sub)`
— which is the ESOP'21 per-iteration discipline in one line: the body
spends one `ir.sub` and hands back the `ir.while` credit the *next*
guard evaluation needs, which is exactly what `while_triple`'s body
obligation asks for. -/

/-- What one iteration costs: its guard evaluation and its subtraction. -/
def cdPayload : ECost := ACost.cost Currency.«while» (1 : ℕ∞) + ACost.cost Currency.sub (1 : ℕ∞)

/-- The loop invariant at `n = k`: the two cells, and the credits for the
`k` iterations that remain. -/
def cdInv (k : ℕ) : Assn := "n" ↦ᵥ k ∗ "one" ↦ᵥ 1 ∗ ¤(k • cdPayload)

/-- What the loop leaves: `n` at zero, `one` untouched, no credits. -/
def cdPost : Assn := "n" ↦ᵥ 0 ∗ "one" ↦ᵥ 1

/-- The guard is determined by the measure. -/
theorem cd_guard (F : Assn) (k : ℕ) (s : State) (cr : ECost)
    (h : irSTATE ((¤¤Currency.«while» 1 ∗ cdInv k) ∗ F) (s, cr)) :
    (Cond.lt (.lit 0) (.cell "n")).eval s = some (decide (0 < k)) := by
  rw [sepConj_assoc] at h
  obtain ⟨-, h⟩ := costCredits_split h
  simp only [cdInv, sepConj_assoc] at h
  have hn := ptoVar_vars h
  simp [hn]

/-- One iteration: pay the subtraction, decrease the measure, hand back
the next guard's credit. -/
theorem cd_body (k : ℕ) (hk : decide (0 < k) = true) :
    irTriple (cdInv k) (.sub "n" "n" "one")
      (∃ᵃ k', ⌜k' < k⌝ ∗ ¤¤Currency.«while» 1 ∗ cdInv k') := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := of_decide_eq_true hk; omega⟩
  have hs : ((j + 1) • cdPayload : ECost) = cdPayload + j • cdPayload := by
    ext k
    simp only [ACost.toFun_nsmul, ACost.toFun_add, add_nsmul, one_nsmul]
    exact add_comm _ _
  have hsplit : ((j + 1) • cdPayload : ECost)
      = ACost.cost Currency.sub (1 : ℕ∞) + (ACost.cost Currency.«while» (1 : ℕ∞)
        + j • cdPayload) := by
    rw [hs]
    unfold cdPayload
    rw [add_assoc]
    exact add_left_comm _ _ _
  have hbody := frame_rule (¤(ACost.cost Currency.«while» (1 : ℕ∞) + j • cdPayload))
    (binop_self_triple .sub "n" "one" (j + 1) 1)
  refine cons_rule hbody (fun q hq => ?_) (fun _ q hq => ?_)
  · have e : cdInv (j + 1) = (¤¤Currency.sub 1 ∗ "n" ↦ᵥ (j + 1) ∗ "one" ↦ᵥ 1) ∗
        ¤(ACost.cost Currency.«while» (1 : ℕ∞) + j • cdPayload) := by
      simp only [cdInv, costCredits_def, hsplit, credits_add]
      ac_rfl
    rw [e] at hq
    exact hq
  · refine ⟨j, ?_⟩
    show (⌜j < j + 1⌝ ∗ ¤¤Currency.«while» 1 ∗ cdInv j) q
    rw [predLift_sepConj_iff]
    refine ⟨Nat.lt_succ_self j, ?_⟩
    have hv : Imp.Bop.sub.apply (j + 1) 1 = j := by simp [Imp.Bop.apply]
    have e : ("n" ↦ᵥ Imp.Bop.sub.apply (j + 1) 1 ∗ "one" ↦ᵥ 1) ∗
        ¤(ACost.cost Currency.«while» (1 : ℕ∞) + j • cdPayload)
        = ¤¤Currency.«while» 1 ∗ cdInv j := by
      simp only [hv, cdInv, costCredits_def, credits_add]
      ac_rfl
    rw [e] at hq
    exact hq

/-- The loop, by `while_triple`: `k` iterations, `k` payloads, and the
measure is `n` itself. -/
theorem cd_while (k : ℕ) :
    irTriple (¤¤Currency.«while» 1 ∗ cdInv k)
      (.while (.lt (.lit 0) (.cell "n")) (.sub "n" "n" "one")) cdPost :=
  while_triple (r := fun a b => a < b) Nat.lt_wfRel.wf cd_guard cd_body
    (fun t ht => by
      have h0 : t = 0 := by
        rcases Nat.eq_zero_or_pos t with h | h
        · exact h
        · simp [h] at ht
      subst h0
      have e : cdInv 0 = cdPost := by simp [cdInv, cdPost]
      intro h hh
      rwa [e] at hh) k

/-! ### Negative control: one credit too few

A triple that does not pay for its op is not derivable — and the reason
is visible in `wp` itself: the run needs `I κ cr`, and an empty balance
affords nothing. -/

/-- A one-cell state, and the frame that owns the rest of it. -/
def nzState : State := State.ofPairs [("x", 0)] []

/-- The `const` triple with no credits at all is not derivable: it would
have to run an op priced at one `ir.const` against an empty balance. -/
theorem const_not_derivable : ¬ irTriple ("x" ↦ᵥ 0) (.const "x" 7) ("x" ↦ᵥ 7) := by
  intro h
  have hstate : irSTATE (("x" ↦ᵥ 0) ∗
      EXACT (((vcells nzState).erase "x", acells nzState, hcells nzState), 0)) (nzState, 0) :=
    ptoVar_sepConj_iff.2 ⟨rfl, rfl⟩
  obtain ⟨s', κ, hrun, -, hi⟩ := h _ (nzState, 0) hstate
  rw [bigStep_const_iff] at hrun
  obtain ⟨-, -, rfl⟩ := hrun
  have := hi Currency.const
  simp at this

/-- The same fact stated on `wp` directly. -/
theorem wp_const_no_credits (Q : Unit → State × ECost → Prop) :
    ¬ wp (.const "x" 7) Q (nzState, 0) := by
  rw [wp_const]
  rintro ⟨-, hi, -⟩
  have := hi Currency.const
  simp at this

end Gate

end Lax13Proofs.Refine.Ir
