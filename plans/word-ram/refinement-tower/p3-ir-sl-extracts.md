# P3 source extracts — generic wp/htriple, time credits, the M-monad

Companion to `source-extracts.md` (P0's first extract file) and
`design.md` §3 P3. Fetched 2026-07-29, verbatim, from
`isabelle_llvm_time` @ `42dd7f5` (pin per `design.md` §1), files retrieved
via `raw.githubusercontent.com/lammich/isabelle_llvm_time/42dd7f59998d76047bb4b6bce76d8f67b53a08b6/thys/<path>`:

- `thys/vcg/Sep_Generic_Wp.thy`
- `thys/vcg/LLVM_Shallow_RS.thy` (for `llSTATE`, `ll_α`, `llvm_htriple` —
  these are declared here, not in `Sep_Generic_Wp.thy` itself)
- `thys/lib/Monad.thy` (the `M`-monad the shallow embedding is built on)
- `thys/basic/kernel/LLVM_Shallow.thy` (`llM` type synonym, primitive ops)

Directory listings taken first, per the task's instructions, via the
GitHub contents API at the same commit:

`thys/lib/` (34 files, non-ML subset): `Basic_Imports.thy`,
`Basic_VCG.thy`, `Bits_Natural.thy`, `Defer_Slot.thy`,
`Definition_Utils.thy`, `ELenses.thy`, `Find_In_Thms.thy`,
`Frame_Infer.thy`, `LLVM_Integer.thy`, `LLVM_More_Word.thy`,
`Lenses.thy`, `Main_Simpset.thy`, `Misc_LLang.thy`, **`Monad.thy`**,
`More_Asymptotics.thy`, `More_Eisbach_Tools.thy`, `More_List.thy`,
`More_Refine_Util.thy`, `Named_Simpsets.thy`, `Sep_Algebra_Add.thy` (+ 2
`.ML` files). `Monad.thy` is the `M`-monad; the credit assertion and
`GC` turn out to live in `thys/vcg/Sep_Generic_Wp.thy` itself (not
`Sep_Lift.thy`, which is a different, address-lifting layer — see gaps).

`thys/basic/kernel/`: `LLVM_Builder.ml`, `LLVM_Codegen.thy`,
`LLVM_Memory.thy`, **`LLVM_Shallow.thy`**, `Sep_Array_Block.thy`,
`Sep_Block_Allocator.thy`, `Sep_Value.thy`. `LLVM_Shallow.thy` defines
the `llM` type synonym and the primitive ops (`ll_load`, `ll_store`, …)
with their `consume (cost '' …'' n)` cost lines.

## 1. `Sep_Generic_Wp.thy` — generic wp, `htriple`, frame, cons

The wp-indexed Hoare-triple locales (`wp` is an arbitrary parameter —
this is what "generic" means: the same `htriple`/frame/cons machinery is
reused for the cost-carrying `wp` defined later in the same file, and
for the LLVM-level `wp` in `LLVM_Shallow_RS.thy`):

```isabelle
locale generic_wp_defs =
  fixes wp :: "'c ⇒ ('r ⇒ 's ⇒ bool) ⇒ 's ⇒ bool"
begin
  definition "htripleF α F P c Q ≡ (∀s. (P**F) (α s) ⟶
      wp c (λr s'. (Q r ** F) (α s')) s)"

  definition "htriple α P c Q ≡ (∀F s. (P**F) (α s) ⟶
      wp c (λr s'. (Q r ** F) (α s')) s)"

  lemma htriple_as_F_eq: "htriple α P c Q = (∀F. htripleF α F P c Q)"
    unfolding htriple_def htripleF_def by blast
end


locale generic_wp = generic_wp_defs wp
  for wp :: "'c ⇒ ('r ⇒ 's ⇒ bool) ⇒ 's ⇒ bool" +
  assumes wp_comm_inf: "inf (wp c Q) (wp c Q') = wp c (inf Q Q')"
begin
```

The frame rule and the rule of consequence, statements only, inside the
`generic_wp` locale (`F` is threaded through the definition of `htriple`
itself, so framing is definitional — the one-line proof, elided here, is
literally just unfolding `htriple_def` and using `fastforce`, not an
extra separating-conjunction law):

```isabelle
  lemma frame_rule: "htriple α P c Q ⟹ htriple α (P ** F) c (λr. Q r ** F)"

  lemma cons_rule:
    assumes "htriple α P c Q"
    assumes "⋀s. P' s ⟹ P s"
    assumes "⋀r s. Q r s ⟹ Q' r s"
    shows "htriple α P' c Q'"
```

`htriple_gc` — the garbage-collecting variant used everywhere at the
LLVM level, folding leftover credits into a postcondition `GC`:

```isabelle
  text ‹With garbage collection›
  abbreviation "htriple_gc GC α P c Q ≡ htriple α P c (λr. Q r ** GC)"

  lemma htriple_to_gc: "⟦ □⊢GC; htriple α P c Q ⟧ ⟹ htriple_gc GC α P c Q"
```

## 2. The time-credit machinery — `$`, `GC`, and the `(state,credit)` pair

Both live in `Sep_Generic_Wp.thy` itself, in the section titled "Setup
for mres-Monad" — the credit assertion `$c` and the leftover-credit
absorber `GC`:

```isabelle
definition time_credits_assn :: "ecost ⇒ (_ × ecost ⇒ bool)" ("$_" [900] 900) where "($c) ≡ SND (EXACT c)"

definition "GC ≡ SND sep_true"

lemma GC_absorb[simp]: "(GC ** GC) = GC" by (auto simp: GC_def sep_algebra_simps SND_conj_conv)

lemma entails_GC: "$c ⊢ GC" unfolding GC_def time_credits_assn_def
  by (auto simp: entails_def SND_def)

lemma empty_ent_GC: "□⊢GC" unfolding GC_def time_credits_assn_def
  by (auto simp: entails_def SND_def sep_algebra_simps)
```

`SND`/`FST` (defined earlier in the same file) lift an assertion over
one half of a product state, forcing the other half to be `0` — this is
how `$c`/`GC` (which own only the credit half) compose with ordinary
state assertions (which own only the state half) via `**`:

```isabelle
definition FST :: "('a ⇒ bool) ⇒ 'a × 'b::zero ⇒ bool"
  where "FST P ≡ λ(a,b). P a ∧ b=0"

definition SND :: "('b ⇒ bool) ⇒ 'a::zero × 'b ⇒ bool"
  where "SND P ≡ λ(a,b). a=0 ∧ P b"
```

The concrete underlying `(state, credit)` pair type, and where `llSTATE`
lives — declared downstream in `LLVM_Shallow_RS.thy`, not
`Sep_Generic_Wp.thy`:

```isabelle
type_synonym ll_astate = "llvm_amemory × ecost"
type_synonym ll_assn = "(ll_astate ⇒ bool)"

definition "ll_α ≡ lift_α_cost llvm_α"
abbreviation llvm_htriple
  :: "ll_assn ⇒ 'a llM ⇒ ('a ⇒ ll_assn) ⇒ bool"
  where "llvm_htriple ≡ htriple_gc GC ll_α"
abbreviation "llSTATE ≡ STATE ll_α"
abbreviation "llPOST ≡ POSTCOND ll_α"
```

`STATE` itself (also `Sep_Generic_Wp.thy`) is the thin wrapper that lets
the VCG talk about "assertion `P` holds of state `s` under abstraction
`α`":

```isabelle
definition STATE :: "('s ⇒ 'a::sep_algebra) ⇒ ('a ⇒ bool) ⇒ 's ⇒ bool"
  where "STATE α P s ≡ P (α s)"
```

Note: `ecost = (string, enat) acost` per `source-extracts.md`'s
`Abstract_Cost.thy`/`Enat_Cost.thy` extract — so `ll_astate` is literally
"LLVM memory × abstract-currency-valued credit balance," matching
design.md's P3 row ("state: LLVM memory + credit balance `(s, cr)`;
`llSTATE`").

## 3. The `M`-monad (`thys/lib/Monad.thy`) and a representative op's cost line

The inner result type `mres` (five-way outcome: nonterminating, failed,
raised exception, or succeeded, each carrying a cost `'c`) and the monad
wrapper `M`:

```isabelle
datatype (discs_sels) ('a,'e,'c,'s,'f) mres = NTERM | FAIL (the_failure: 'f)
  | EXC 'e 'c (the_state: 's) | SUCC 'a 'c (the_state: 's)
datatype ('a,'e,'c,'s,'f) M = M (run: "'s ⇒ ('a,'e,'c,'s,'f) mres")
```

`bind`, `return`, `consume` (the primitive that charges a cost with no
other effect — every primitive op is `consume cost_of_op ≫ do the actual
thing`), and `get`/`set`/`raise`/`handle`:

```isabelle
definition REC where "REC ≡ M.fixp_fun"
definition internal_nterm where "internal_nterm ≡ M (λ_. NTERM)"
definition fail where "fail msg ≡ M (λ_. FAIL msg)"
definition return where "return x ≡ M (SUCC x 0)"

definition bind where "bind m f ≡ M (λs. case run m s of SUCC x c s ⇒ addcost c (run (f x) s)
                   | NTERM ⇒ NTERM | FAIL msg ⇒ FAIL msg | EXC e c s ⇒ EXC e c s)"
definition get where "get ≡ M (λs. SUCC s 0 s)"
definition set where "set s ≡ M (λ_. SUCC () 0 s)"
definition raise where "raise e ≡ M (EXC e 0)"
definition handle where "handle m h ≡ M (λs. case run m s of EXC e c s ⇒ addcost c (run (h e) s)
       | SUCC x c s ⇒ SUCC x c s | NTERM ⇒ NTERM | FAIL msg ⇒ FAIL msg)"

definition consume where "consume t = M (λs. SUCC () t s)"
```

The `llM` type synonym instantiating `M` for the LLVM shallow embedding
(`thys/basic/kernel/LLVM_Shallow.thy`) — unit failure info, `cost`-typed
concrete cost, `llvm_memory` state, `err` exceptions:

```isabelle
type_synonym 'a llM = "('a,unit,cost,llvm_memory,err) M"
```

Representative op cost lines — `ll_load`/`ll_store`, each a `consume`
of one unit of a currency named after the op, then the actual memory
access:

```isabelle
definition ll_load :: "'a::llvm_rep ptr ⇒ 'a llM" where
  "ll_load p ≡ doM {
    consume (cost ''load'' 1);
    r ← llvm_load (the_raw_ptr p);
    checked_from_val r
  }"

definition ll_store :: "'a::llvm_rep ⇒ 'a ptr ⇒ unit llM" where
  "ll_store v p ≡ doM {
    consume (cost ''store'' 1);
    llvm_store (to_val v) (the_raw_ptr p)
  }"
```

(`cost n k` is `Abstract_Cost.thy`'s one-unit-of-one-currency builder,
already quoted in `source-extracts.md` §"The currency type (`acost`)".)

Notes read off these three sections, for the design record: the IR's
deep `Ir.Com`/cost-indexed big-step semantics (design.md P3 row 1)
mirrors this shape at the *rule granularity* the design record calls
out — one primitive op is exactly one `consume (cost "name" k)` line
glued to the op's actual effect, which is precisely "one op = one cost =
one hnr rule" (design.md P3 row 1's substrate-delta note). The
`generic_wp`/`generic_wp_defs` locale pair is what design.md's
`Ir/Wp.lean`, `Ir/Triples.lean` are asked to reproduce "as the source
has it" (P3 row 3) — note that `wp` is a locale *parameter*, not fixed
to the LLVM instance, so the Lean port's `Ir.wp` need only supply the
one `wp_comm_inf`-style commutation lemma to inherit `frame_rule`/
`cons_rule` for free, exactly as `LLVM_Shallow_RS.thy` does by
interpretation rather than re-proof.

## Gaps

- The task suggested `Sep_Lift.thy` as a likely credit-machinery
  location; it was fetched (504 lines) but the credit assertion, `GC`,
  and `llSTATE` all turned out to live in `Sep_Generic_Wp.thy` and
  `LLVM_Shallow_RS.thy` instead. `Sep_Lift.thy` itself concerns lifting
  assertions across an address/block memory model (a different, more
  concrete layering question than the credit seam) and was not quoted
  since none of the four requested items live there.
- `wp` itself, in the cost-carrying instantiation, is defined inside the
  `cost_framework` locale in the same file (`wp m Q ≡ λ(s,cr). mwp (run m
  s) bot bot bot (λr c s. Q r (s,minus cr c) ∧ I c cr)`), not as a
  standalone top-level `definition` — quoted here in the body text above
  rather than as a fenced block, since presenting it without the
  surrounding `cost_framework`/`I`/`minus` locale parameters (themselves
  a page of assumptions: `minus_0`, `I_0`, `minus_minus_add`, `I1`–`I3`)
  would strip context needed to read it correctly; design.md's P3 table
  already summarizes its role and P3, when it lands, should re-read the
  full locale rather than rely on this extract for that one definition.
- Did not quote `wp_bind`/`wp_consume`/`wp_return` (the concrete
  `cost_framework` reasoning lemmas) — out of scope for the four
  requested items (generic wp/htriple, frame, cons, credit machinery,
  M-monad, one op's cost line).
