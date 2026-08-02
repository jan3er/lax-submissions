import Lax13Proofs.Refine.Sepref.HeapAlloc

/-!
Element-level ownership: the exclusive-or (EO) array layer.

Leaf **P4.5.B** of `plans/word-ram/tower-expansion/p4.5-design.md`
(design note §3 B), on top of A.1's range ownership (`Refine/Ir/Heap.lean`)
and A.2/A.3's allocator (`Refine/Sepref/HeapAlloc.lean`).

Source pin `isabelle_llvm_time` @ `42dd7f5`, `thys/ds/Proto_EOArray.thy`
and `thys/sepref/Hnr_Primitives_Experiment.thy`:

```isabelle
oelem_assn A ≡ mk_assn (λNone ⇒ λ_. □ | Some x ⇒ λxi. ↑A x xi)          (:79)
nao_assn A ≡ mk_assn (λxs p. EXS xsi. ↑narray_assn xsi p
                              ** ↑(list_assn (oelem_assn A)) xs xsi)     (:144)
eoarray_assn A ≡ ↑(nao_assn (mk_assn A))                (Hnr_Prim… :234)

lo_init:         list_assn (oelem_assn A) (replicate n None) (replicate n x) = □
lo_free:         set xs ⊆ {None} ⟹ list_assn (oelem_assn A) xs xsi = ↑(length xsi = length xs)
lo_extract_elem: i<length xs ⟹ xs!i = Some x ⟹
                   list_assn (oelem_assn A) xs ys
                     = (↑A x (ys!i) ** list_assn (oelem_assn A) (xs[i:=None]) ys)
lo_insert_elem:  i<length xs ⟹ xs!i = None ⟹
                   list_assn (oelem_assn A) (xs[i:=Some x]) (ys[i:=y])
                     = (↑A x y ** list_assn (oelem_assn A) xs ys)

mop_oarray_extract xs i =
  doN { ASSERT (i<length xs ∧ xs!i≠None);
        consume (RETURNT (the (xs!i), xs[i:=None])) (lift_acost mop_array_nth_cost) }
mop_oarray_upd xs i x =
  do { ASSERT (i<length xs ∧ xs!i=None);
       consume (RETURNT (xs[i:=Some x])) (lift_acost mop_array_upd_cost) }
```

The four `lo_*` laws are **equations**, and that exactness is the whole
point of the layer: it is what makes a move or a swap cost *exactly* the
loads and stores it performs rather than a bound, and it is the mechanism
behind the source's `myswap`. All four land as equations below
(`loAssn_replicate_none`, `loAssn_all_none`, `loAssn_extract`,
`loAssn_insert`), and `loAssn_extract_insert` / `loAssn_insert_extract`
record that `extract` and `upd` are exact inverses on the ownership tag.

## D-B1 — the carrier, resolved

The design note's open decision D-B1 asked what the Lean carrier for
`oelem_assn` is "given that our assertion layer is not `mk_assn`-shaped",
and expected it to fall out of `p ↦ₕ xs` directly. **It does, and the
reason is that it does not have to touch the range at all.** `mk_assn` is
the source's wrapper turning a two-argument predicate into a *dual*
assertion; our assertions are plain `α → κ → Assn` functions already
(`Sepref/Basic.lean`'s P4/D-a), so `oelem_assn A` is a two-case function
and nothing else. The `lo_*` laws are laws of `list_assn (oelem_assn A)` —
statements about the *element list*, not about the block — so the range
layer enters exactly once, in `naoAssn`, where A.1's `p ↦ₕ xsi` plays
`narray_assn xsi p` verbatim. No new range lemma was needed; A.1's
`ptoH_append` / `ptoH_focus` are not used here at all, and that is the
positive content of D-B1's answer.

## Judgment calls

**D-B1a — `A` stays a parameter, and that is load-bearing.** It would be
cheaper to fix `A` at the identity (our elements are words). It would
also be *vacuous*: with a pure `A` the whole ownership discipline
degenerates, because the concrete backing `xsi` is existentially
quantified, so a `None` slot can always be re-filled with the physical
word that is still sitting there and the tag "extracted" carries no
resource. Non-vacuity requires an `A` that owns memory. `A` is therefore
a parameter throughout, and the gate instantiates it at
`boxAssn v w := w ↦ₕ [v]` — an element that *is* a one-cell heap block,
the shape the source's own consumer (an array of pointers) has — where
double extraction is `sepFalse` and the negative controls bite.

**D-B1b — the extracted element lands in `eoCellAssn A`, because our IR
has no SSA registers.** The source's rule returns the element as a value
into a fresh register under `A`. Three-address code has no fresh
registers (P4/D-ab), so the element's *word* lands in an owned scalar
cell and the element's *resource* comes with it:
`eoCellAssn A a x = ∃ᵃ w, (x ↦ᵥ w) ∗ A a w`. Note what survives an `upd`:
the cell `x` does — our substrate never deallocates a cell — but only as
`junkCell x`; `A a w` has moved into the array. That split is exactly why
`upd` is linear in the element without being linear in the register.

**D-B1c — cost: one unit, and the address arithmetic is the caller's.**
The source pays `cost load 1 + cost ofs_ptr 1` for a read and
`cost store 1 + cost ofs_ptr 1` for a write, because `array_nth` is
`ofs_ptr` followed by `load`. Ours pays **one** `ir.aget` (resp. one
`ir.aset`) and no `ofs_ptr` currency is invented, because A.1's
`haget_triple` / `haset_triple` take the **absolute** address `p + j` in
the index cell: address arithmetic is not part of the access. It is not
hidden either — a caller that must form `p + j` emits an ordinary
`binop .add`, pays its own `ir.add` unit, and that unit shows up in the
caller's cost vector; `HeapEOGate.addrExtractCost` pins a
compute-then-read chain whose vector carries **both** an `ir.add` and an
`ir.aget`, so nothing is being smuggled. What collapses here is the
source's two-instruction *sequence*, not a charge.

**D-B1d — registration: the in-place forms are the `sepref_fr_rules`
default (ledger E29).** `extract` and `upd` are loop-interior operations
on an array the caller already holds, so both registered rules are stated
at a **pinned** base pointer (`eoarrayAssnAt A p`) and hand the array back
at the same base and the same cell. Neither allocates. The packed form
`eoarrayAssn` (base pointer existential, `heapBlockAssn`'s shape) exists
for interfaces that must hide the pointer, is reachable by
`eoarrayAssnAt_entails_eoarrayAssn`, and is deliberately **not**
registered: E29's failure mode is synthesis silently picking an
allocating or repacking form inside a loop and failing at the consumer
bridge, and the way to prevent it is to leave only the in-place form in
the database.

## Falsification (clause 2)

This carrier is authored, so refute-before-prove applies in full. §5
carries the four controls the leaf names — no double extract, no `upd`
into an occupied slot, no overlapping EO arrays, no ownership tag
surviving an extract — each as a *theorem of impossibility* **and** a
compiled `#guard`, and every one of them was flipped and confirmed to
fail. The flips that matter most are the two that would make the layer
look sound while being empty: replacing `boxAssn` by a pure assertion
makes `boxAssn_sepConj_self` false (two copies are jointly satisfiable at
the empty resource) and makes `tag_not_recoverable` false (the tag is
recoverable there), which is the evidence behind D-B1a; and offering
`insert_needs_none` a slot that really *is* `None` turns its `≠` into
`lo_insert_elem`'s equation, which is the evidence that the `= None`
premise is what makes it bite.
-/

namespace Lax13Proofs.Refine.Sepref

open Ir NRest

/-! ## 1. `oelem_assn` and `list_assn (oelem_assn A)` -/

/-- The source's `oelem_assn A`: a slot that is `None` owns **nothing**,
a slot that is `Some x` owns whatever `A` says about the word sitting
there. This is the whole of D-B1: no `mk_assn`, no range. -/
def oelemAssn {α : Type} (A : α → Val → Assn) : Option α → Val → Assn
  | none, _ => (□ : Assn)
  | some x, xi => A x xi

@[simp] theorem oelemAssn_none {α : Type} (A : α → Val → Assn) (w : Val) :
    oelemAssn A none w = (□ : Assn) := rfl

@[simp] theorem oelemAssn_some {α : Type} (A : α → Val → Assn) (x : α) (w : Val) :
    oelemAssn A (some x) w = A x w := rfl

/-- The source's `list_assn (oelem_assn A)`: the `∗`-fold of the element
assertions down two lists of equal length. Unequal lengths are
`sepFalse`, exactly as `list_assn` is in the source — which is why no
separate length conjunct is needed anywhere below. -/
def loAssn {α : Type} (A : α → Val → Assn) : List (Option α) → List Val → Assn
  | [], [] => (□ : Assn)
  | x :: xs, y :: ys => oelemAssn A x y ∗ loAssn A xs ys
  | _, _ => (sepFalse : Assn)

@[simp] theorem loAssn_nil {α : Type} (A : α → Val → Assn) : loAssn A [] [] = (□ : Assn) := rfl

@[simp] theorem loAssn_cons {α : Type} (A : α → Val → Assn) (x : Option α) (y : Val)
    (xs : List (Option α)) (ys : List Val) :
    loAssn A (x :: xs) (y :: ys) = (oelemAssn A x y ∗ loAssn A xs ys) := rfl

@[simp] theorem loAssn_nil_cons {α : Type} (A : α → Val → Assn) (y : Val) (ys : List Val) :
    loAssn A [] (y :: ys) = (sepFalse : Assn) := rfl

@[simp] theorem loAssn_cons_nil {α : Type} (A : α → Val → Assn) (x : Option α)
    (xs : List (Option α)) : loAssn A (x :: xs) [] = (sepFalse : Assn) := rfl

/-! ### Two absorption facts about `sepFalse`

Stated here because the length-mismatch branch of every proof below
needs them and `Assn.lean` states only the entailments. -/

theorem sepFalse_sepConj (P : Assn) : ((sepFalse : Assn) ∗ P) = (sepFalse : Assn) := by
  funext h
  refine propext ⟨?_, fun h' => h'.elim⟩
  rintro ⟨u, v, hd, huv, hu, hv⟩
  exact hu.elim

theorem sepConj_sepFalse (P : Assn) : (P ∗ (sepFalse : Assn)) = (sepFalse : Assn) := by
  funext h
  refine propext ⟨?_, fun h' => h'.elim⟩
  rintro ⟨u, v, hd, huv, hu, hv⟩
  exact hv.elim

theorem predLift_of_false {Φ : Prop} (h : ¬ Φ) : (⌜Φ⌝ : Assn) = (sepFalse : Assn) := by
  funext hh
  exact propext ⟨fun hx => absurd hx.1 h, fun hx => hx.elim⟩

/-- The lengths agree wherever the assertion holds — the fact `list_assn`
carries implicitly in the source. -/
theorem loAssn_length {α : Type} {A : α → Val → Assn} :
    ∀ (xs : List (Option α)) (ys : List Val) (h : AState), loAssn A xs ys h → ys.length = xs.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: xs, _ :: ys, _, h => by
    obtain ⟨-, v, -, -, -, hv⟩ := h
    simpa using loAssn_length xs ys v hv

/-- …so at unequal lengths the assertion *is* `sepFalse`. -/
theorem loAssn_of_length_ne {α : Type} {A : α → Val → Assn} {xs : List (Option α)}
    {ys : List Val} (h : ys.length ≠ xs.length) : loAssn A xs ys = (sepFalse : Assn) := by
  funext hh
  exact propext ⟨fun hx => absurd (loAssn_length xs ys hh hx) h, fun hx => hx.elim⟩

/-! ## 2. The four structural laws, as equations

`lo_init`, `lo_free`, `lo_extract_elem`, `lo_insert_elem`. Every one is
an **equation**: an entailment in either of the last two would be exactly
the weakening that turns an exact move cost into a bounded one. -/

/-- **`lo_free`.** An all-`None` element list owns nothing at all — it is
the pure statement that the lengths agree, whatever the concrete backing
holds. This is what lets a freed EO array return to *raw* availability
(`HeapAlloc.availRaw`) with no per-cell work. -/
theorem loAssn_all_none {α : Type} {A : α → Val → Assn} :
    ∀ (xs : List (Option α)) (ys : List Val), (∀ z ∈ xs, z = none) →
      loAssn A xs ys = (⌜ys.length = xs.length⌝ : Assn)
  | [], [], _ => by rw [loAssn_nil]; exact (predLift_of_true rfl).symm
  | [], _ :: _, _ => by rw [loAssn_nil_cons, predLift_of_false (by simp)]
  | _ :: _, [], _ => by rw [loAssn_cons_nil, predLift_of_false (by simp)]
  | x :: xs, y :: ys, h => by
    have hx : x = none := h x (by simp)
    subst hx
    rw [loAssn_cons, oelemAssn_none, emp_sepConj,
      loAssn_all_none xs ys (fun z hz => h z (by simp [hz]))]
    simp

/-- **`lo_init`.** A freshly created EO array — every slot `None` — owns
no element memory whatever the concrete backing is. This is the theorem
`HeapAlloc`'s A.3 header appeals to when it says leaf B's arrays need no
zeroed backing: raw space is enough. -/
theorem loAssn_replicate_none {α : Type} {A : α → Val → Assn} (n : ℕ) (ys : List Val)
    (h : ys.length = n) : loAssn A (List.replicate n (none : Option α)) ys = (□ : Assn) := by
  rw [loAssn_all_none _ _ (fun z hz => List.eq_of_mem_replicate hz),
    List.length_replicate, predLift_of_true h]

/-- **`lo_extract_elem`**, as an equation: the element resource at slot
`j` splits off, and what remains is the same list with the slot tagged
`None`. Read left to right this is `extract`; read right to left it is
the join, which is why `lo_insert_elem` costs nothing extra. -/
theorem loAssn_extract {α : Type} {A : α → Val → Assn} :
    ∀ (xs : List (Option α)) (ys : List Val) (j : ℕ) (e : α) (hj : j < xs.length)
      (hj' : j < ys.length), xs[j] = some e →
      loAssn A xs ys = (A e ys[j] ∗ loAssn A (xs.set j none) ys)
  | [], _, _, _, hj, _, _ => absurd hj (by simp)
  | _ :: _, [], _, _, _, hj', _ => absurd hj' (by simp)
  | x :: xs, y :: ys, 0, e, _, _, hxj => by
    have hx : x = some e := by simpa using hxj
    subst hx
    simp
  | x :: xs, y :: ys, j + 1, e, hj, hj', hxj => by
    have hj2 : j < xs.length := by simpa using hj
    have hj3 : j < ys.length := by simpa using hj'
    have hxj2 : xs[j] = some e := by simpa using hxj
    rw [loAssn_cons, loAssn_extract xs ys j e hj2 hj3 hxj2]
    show _ = (A e (y :: ys)[j + 1] ∗ loAssn A ((x :: xs).set (j + 1) none) (y :: ys))
    rw [List.set_cons_succ, loAssn_cons]
    show (oelemAssn A x y ∗ A e ys[j] ∗ loAssn A (xs.set j none) ys)
      = (A e ys[j] ∗ oelemAssn A x y ∗ loAssn A (xs.set j none) ys)
    rw [sepConj_left_comm]

/-- **`lo_insert_elem`**, as an equation: writing an element into a slot
tagged `None` *consumes* the element resource and nothing else. The
`xs[j] = none` premise is load-bearing — without it the equation is false
(`HeapEOGate.insert_needs_none`), because the slot's old resource would
be silently overwritten, which is precisely how a linear move becomes a
leaking overwrite. -/
theorem loAssn_insert {α : Type} {A : α → Val → Assn} :
    ∀ (xs : List (Option α)) (ys : List Val) (j : ℕ) (e : α) (y : Val) (hj : j < xs.length)
      (_hj' : j < ys.length), xs[j] = none →
      loAssn A (xs.set j (some e)) (ys.set j y) = (A e y ∗ loAssn A xs ys)
  | [], _, _, _, _, hj, _, _ => absurd hj (by simp)
  | _ :: _, [], _, _, _, _, hj', _ => absurd hj' (by simp)
  | x :: xs, y₀ :: ys, 0, e, y, _, _, hxj => by
    have hx : x = none := by simpa using hxj
    subst hx
    simp
  | x :: xs, y₀ :: ys, j + 1, e, y, hj, hj', hxj => by
    have hj2 : j < xs.length := by simpa using hj
    have hj3 : j < ys.length := by simpa using hj'
    have hxj2 : xs[j] = none := by simpa using hxj
    rw [List.set_cons_succ, List.set_cons_succ, loAssn_cons,
      loAssn_insert xs ys j e y hj2 hj3 hxj2, loAssn_cons, sepConj_left_comm]

/-! ### `extract` and `upd` are exact inverses

Both directions round-trip on the nose — tag list *and* backing — and
both fall straight out of the two equations above. That exactness is what
"exact rather than bounded" means: a move loses nothing, so a swap costs
its four accesses rather than a bound on them. -/

/-- A `None` slot's backing word is irrelevant. This is the reason the
source quantifies the concrete backing existentially at all, and it is
what lets a freed EO array come back as *raw* space. -/
theorem loAssn_set_backing {α : Type} {A : α → Val → Assn} :
    ∀ (xs : List (Option α)) (ys : List Val) (j : ℕ) (y : Val) (hj : j < xs.length)
      (_hj' : j < ys.length), xs[j] = none → loAssn A xs (ys.set j y) = loAssn A xs ys
  | [], _, _, _, hj, _, _ => absurd hj (by simp)
  | _ :: _, [], _, _, _, hj', _ => absurd hj' (by simp)
  | x :: xs, _ :: ys, 0, y, _, _, hxj => by
    have hx : x = none := by simpa using hxj
    subst hx
    simp
  | x :: xs, y₀ :: ys, j + 1, y, hj, hj', hxj => by
    have hj2 : j < xs.length := by simpa using hj
    have hj3 : j < ys.length := by simpa using hj'
    have hxj2 : xs[j] = none := by simpa using hxj
    rw [List.set_cons_succ, loAssn_cons, loAssn_cons,
      loAssn_set_backing xs ys j y hj2 hj3 hxj2]

/-- `upd` after `extract` is the identity on the tag list. -/
theorem set_none_set_some {α : Type} {xs : List (Option α)} {j : ℕ} {e : α}
    (hj : j < xs.length) (hxj : xs[j] = some e) :
    (xs.set j none).set j (some e) = xs := by
  rw [List.set_set, ← hxj, List.set_getElem_self hj]

/-- …and `extract` after `upd` is too. -/
theorem set_some_set_none {α : Type} {xs : List (Option α)} {j : ℕ} {e : α}
    (hj : j < xs.length) (hxj : xs[j] = none) :
    (xs.set j (some e)).set j none = xs := by
  rw [List.set_set, ← hxj, List.set_getElem_self hj]

/-- **Extract then insert restores the array**, on the nose. -/
theorem loAssn_extract_insert {α : Type} {A : α → Val → Assn} {xs : List (Option α)}
    {ys : List Val} {j : ℕ} {e : α} (hj : j < xs.length) (hj' : j < ys.length)
    (hxj : xs[j] = some e) :
    loAssn A ((xs.set j none).set j (some e)) (ys.set j ys[j]) = loAssn A xs ys := by
  rw [set_none_set_some hj hxj, List.set_getElem_self hj']

/-- **Insert then extract restores it too** — the tag is `None` again and
the backing word the `upd` wrote is irrelevant, so the assertion is the
one we started with. -/
theorem loAssn_insert_extract {α : Type} {A : α → Val → Assn} {xs : List (Option α)}
    {ys : List Val} {j : ℕ} {e : α} {y : Val} (hj : j < xs.length) (hj' : j < ys.length)
    (hxj : xs[j] = none) :
    loAssn A ((xs.set j (some e)).set j none) (ys.set j y) = loAssn A xs ys := by
  rw [set_some_set_none hj hxj, loAssn_set_backing xs ys j y hj hj' hxj]

/-! ## 3. `nao_assn` and `eoarray_assn`

The range layer enters here and nowhere else: A.1's `p ↦ₕ xsi` plays the
source's `narray_assn xsi p`, and the concrete backing is existentially
quantified exactly as the source's `EXS xsi` quantifies it. -/

/-- The source's `nao_assn A`: an EO array whose concrete value is its
**base pointer**. The backing `xsi` is hidden — that is what makes a
`None` slot's contents irrelevant — and `loAssn` pins `xsi.length` to
`xs.length` on its own. -/
def naoAssn {α : Type} (A : α → Val → Assn) : List (Option α) → Val → Assn :=
  fun xs p => ∃ᵃ xsi, ((p ↦ₕ xsi) ∗ loAssn A xs xsi)

theorem naoAssn_def {α : Type} (A : α → Val → Assn) (xs : List (Option α)) (p : Val) :
    naoAssn A xs p = ∃ᵃ xsi, ((p ↦ₕ xsi) ∗ loAssn A xs xsi) := rfl

/-- Packing a concrete backing into the array assertion. -/
theorem ptoH_loAssn_entails_naoAssn {α : Type} (A : α → Val → Assn) (p : Val)
    (xs : List (Option α)) (xsi : List Val) :
    ((p ↦ₕ xsi) ∗ loAssn A xs xsi) ⊢ naoAssn A xs p := fun _ h => ⟨xsi, h⟩

/-- The source's `eoarray_assn A`, at a **pinned** base pointer: the cell
`c` holds the base and that base carries the EO array. This is the form
the two registered rules of §4 are stated at (judgment call D-B1d) — an
in-place operation must be able to name the address it reads. -/
def eoarrayAssnAt {α : Type} (A : α → Val → Assn) (p : Val) : List (Option α) → String → Assn :=
  fun xs c => (c ↦ᵥ p) ∗ naoAssn A xs p

theorem eoarrayAssnAt_def {α : Type} (A : α → Val → Assn) (p : Val) (xs : List (Option α))
    (c : String) : eoarrayAssnAt A p xs c = ((c ↦ᵥ p) ∗ naoAssn A xs p) := rfl

/-- …and with the base pointer hidden, in `HeapAlloc.heapBlockAssn`'s
shape. Deliberately **not** registered (D-B1d). -/
def eoarrayAssn {α : Type} (A : α → Val → Assn) : List (Option α) → String → Assn :=
  fun xs c => ∃ᵃ p, eoarrayAssnAt A p xs c

theorem eoarrayAssnAt_entails_eoarrayAssn {α : Type} (A : α → Val → Assn) (p : Val)
    (xs : List (Option α)) (c : String) :
    eoarrayAssnAt A p xs c ⊢ eoarrayAssn A xs c := fun _ h => ⟨p, h⟩

/-- **The element, in a cell** (judgment call D-B1b): the word is in `x`
and the element's own resource comes with it. For a pure `A` this is
`natAssn`; for a heap-owning `A` it is the moved block. -/
def eoCellAssn {α : Type} (A : α → Val → Assn) : α → String → Assn :=
  fun a x => ∃ᵃ w, ((x ↦ᵥ w) ∗ A a w)

theorem eoCellAssn_def {α : Type} (A : α → Val → Assn) (a : α) (x : String) :
    eoCellAssn A a x = ∃ᵃ w, ((x ↦ᵥ w) ∗ A a w) := rfl

theorem ptoVar_entails_eoCellAssn {α : Type} (A : α → Val → Assn) (a : α) (x : String)
    (w : Val) : ((x ↦ᵥ w) ∗ A a w) ⊢ eoCellAssn A a x := fun _ h => ⟨w, h⟩

/-- The cell survives an `upd`; the element's resource does not. Note
what this is **not**: `eoCellAssn A a x ⊢ junkCell x` is false at a
heap-owning `A`, because `junkCell x` owns the cell and nothing else
while `eoCellAssn A a x` owns the element as well. The cell comes back
from the `upd` triple because the triple *keeps* `x ↦ᵥ w` while handing
`A a w` to the array — not because the element assertion could be
weakened to junk. -/
theorem ptoVar_entails_junkCell (x : String) (w : Val) : (x ↦ᵥ w) ⊢ junkCell x :=
  fun _ h => ⟨w, h⟩

/-! ## 4. The two operations and their registered rules -/

/-- **`mop_oarray_extract`.** Both halves of the source's `ASSERT` are
kept: the index is in range **and** the slot is occupied. The result is
the element together with the array, its slot now tagged `None` — the tag
is what the linearity rides on. Price: one `ir.aget` (judgment call
D-B1c). -/
noncomputable def mopOarrayExtract {α : Type} [Inhabited α] (xs : List (Option α)) (j : ℕ) :
    NRest (α × List (Option α)) ECost :=
  NRest.bindT (NRest.assert (j < xs.length ∧ xs[j]! ≠ none)) fun _ =>
    NRest.consume (NRest.returnT ((xs[j]!).get!, xs.set j none)) (irUnit Currency.aget)

theorem mopOarrayExtract_def {α : Type} [Inhabited α] (xs : List (Option α)) (j : ℕ) :
    mopOarrayExtract xs j =
      NRest.bindT (NRest.assert (j < xs.length ∧ xs[j]! ≠ none)) fun _ =>
        NRest.consume (NRest.returnT ((xs[j]!).get!, xs.set j none)) (irUnit Currency.aget) := rfl

/-- **`mop_oarray_upd`.** The `xs[j] = none` half of the `ASSERT` is the
one that is easy to drop and must not be: without it the operation is an
overwrite, not a move, and the slot's old element resource leaks. Price:
one `ir.aset`. -/
noncomputable def mopOarrayUpd {α : Type} (xs : List (Option α)) (j : ℕ) (e : α) :
    NRest (List (Option α)) ECost :=
  NRest.bindT (NRest.assert (j < xs.length ∧ xs[j]! = none)) fun _ =>
    NRest.consume (NRest.returnT (xs.set j (some e))) (irUnit Currency.aset)

theorem mopOarrayUpd_def {α : Type} (xs : List (Option α)) (j : ℕ) (e : α) :
    mopOarrayUpd xs j e =
      NRest.bindT (NRest.assert (j < xs.length ∧ xs[j]! = none)) fun _ =>
        NRest.consume (NRest.returnT (xs.set j (some e))) (irUnit Currency.aset) := rfl

/-! ### Two eliminators

`irHtriple_junk`'s siblings: one for the existential backing that
`naoAssn` hides, one for the length-mismatch branch. -/

/-- Eliminating an existential from a triple's precondition — the shape
`naoAssn`'s hidden backing puts it in. -/
theorem irHtriple_sepEx {β : Type} {P : β → Assn} {Q R : Assn} {c : Com}
    (h : ∀ y, irHtriple (P y ∗ Q) c R) : irHtriple ((∃ᵃ y, P y) ∗ Q) c R := by
  intro F p hp
  rw [sepConj_assoc, sepEx_sepConj] at hp
  obtain ⟨y, hy⟩ := hp
  exact h y F p (by rw [sepConj_assoc]; exact hy)

/-- An unsatisfiable precondition proves anything — the branch where the
hidden backing has the wrong length. -/
theorem irHtriple_of_sepFalse {Q : Assn} {c : Com} : irHtriple (sepFalse : Assn) c Q := by
  intro F p hp
  obtain ⟨u, v, hd, huv, hu, hv⟩ := hp
  exact hu.elim

/-! ### `extract` -/

/-- **The extract triple.** Pay one `ir.aget`, own a junk destination,
the array at a known base and the index cell holding the *absolute*
address `p + j`; get the element in the destination and the array back
with slot `j` tagged `None`. The index cell survives (a read consumes
nothing); the array's ownership at `xs` does **not** — it is the result. -/
theorem oarrayExtract_junk_rule {α : Type} (A : α → Val → Assn) (x c idx : String)
    (p j : ℕ) (xs : List (Option α)) (e : α) (hj : j < xs.length) (hxj : xs[j] = some e) :
    irHtriple (¤(irUnit Currency.aget) ∗
        (junkCell x ∗ hnCtxt (eoarrayAssnAt A p) xs c ∗ hnCtxt natAssn (p + j) idx))
      (.aget x heapName idx)
      (hnCtxt natAssn (p + j) idx ∗
        (eoCellAssn A ×ₐ eoarrayAssnAt A p) (e, xs.set j none) (x, c)) := by
  have e₁ : (¤(irUnit Currency.aget) ∗
      (junkCell x ∗ hnCtxt (eoarrayAssnAt A p) xs c ∗ hnCtxt natAssn (p + j) idx))
      = junkCell x ∗ (¤(irUnit Currency.aget) ∗
        hnCtxt (eoarrayAssnAt A p) xs c ∗ hnCtxt natAssn (p + j) idx) := by ac_rfl
  rw [e₁]
  refine irHtriple_junk fun v => ?_
  have e₂ : ((x ↦ᵥ v) ∗ (¤(irUnit Currency.aget) ∗
      hnCtxt (eoarrayAssnAt A p) xs c ∗ hnCtxt natAssn (p + j) idx))
      = (∃ᵃ xsi, ((p ↦ₕ xsi) ∗ loAssn A xs xsi)) ∗
        ((x ↦ᵥ v) ∗ ¤(irUnit Currency.aget) ∗ (c ↦ᵥ p) ∗ (idx ↦ᵥ (p + j))) := by
    simp only [hnCtxt_def, natAssn_def, eoarrayAssnAt_def, naoAssn_def]
    ac_rfl
  rw [e₂]
  refine irHtriple_sepEx fun xsi => ?_
  by_cases hlen : xsi.length = xs.length
  · have hj' : j < xsi.length := by omega
    rw [loAssn_extract xs xsi j e hj hj' hxj]
    have hbase := frame_rule (wp := wp) (α := irα)
      ((c ↦ᵥ p) ∗ A e xsi[j] ∗ loAssn A (xs.set j none) xsi)
      (haget_triple x idx v p j xsi xsi[j] hj' rfl)
    refine irTriple.gc (cons_rule hbase (fun s hs => ?_) (fun _ s hs => ?_))
    · revert hs
      have ePre : (((p ↦ₕ xsi) ∗ A e xsi[j] ∗ loAssn A (xs.set j none) xsi) ∗
          ((x ↦ᵥ v) ∗ ¤(irUnit Currency.aget) ∗ (c ↦ᵥ p) ∗ (idx ↦ᵥ (p + j))))
          = ((¤¤Currency.aget 1 ∗ (x ↦ᵥ v) ∗ (p ↦ₕ xsi) ∗ (idx ↦ᵥ (p + j))) ∗
            ((c ↦ᵥ p) ∗ A e xsi[j] ∗ loAssn A (xs.set j none) xsi)) := by
        rw [costCredits_one]
        ac_rfl
      rw [ePre]
      exact fun h => h
    · revert hs
      have ePost : ((((x ↦ᵥ xsi[j]) ∗ (p ↦ₕ xsi) ∗ (idx ↦ᵥ (p + j)))) ∗
          ((c ↦ᵥ p) ∗ A e xsi[j] ∗ loAssn A (xs.set j none) xsi))
          = ((idx ↦ᵥ (p + j)) ∗ ((x ↦ᵥ xsi[j]) ∗ A e xsi[j]) ∗
            ((c ↦ᵥ p) ∗ (p ↦ₕ xsi) ∗ loAssn A (xs.set j none) xsi)) := by
        ac_rfl
      have eGoal : (hnCtxt natAssn (p + j) idx ∗
          (eoCellAssn A ×ₐ eoarrayAssnAt A p) (e, xs.set j none) (x, c))
          = ((idx ↦ᵥ (p + j)) ∗ eoCellAssn A e x ∗ ((c ↦ᵥ p) ∗ naoAssn A (xs.set j none) p)) := by
        simp only [hnCtxt_def, natAssn_def, prodAssn, eoarrayAssnAt_def]
      rw [ePost, eGoal]
      exact sepConj_mono_right (conj_entails_mono (ptoVar_entails_eoCellAssn A e x xsi[j])
        (sepConj_mono_right (ptoH_loAssn_entails_naoAssn A p (xs.set j none) xsi))) s
  · simp only [loAssn_of_length_ne hlen, sepConj_sepFalse, sepFalse_sepConj]
    exact irHtriple_of_sepFalse

/-- **The registered extract rule.** In `hnr_mop_aget`'s idiom for the
destination and `hnr_mop_aset`'s for the linearity: the array's ownership
at `xs` is absent from `Γ'`, and the result slot carries the pair
(element, array-with-the-slot-emptied). The index bound and the
occupancy of the slot both come from the `mop`'s own `assert`, through
`hnr_assert`. -/
@[sepref_fr_rules]
theorem hnr_mop_oarray_extract {α : Type} [Inhabited α] (A : α → Val → Assn)
    (x c idx : String) (p j : ℕ) (xs : List (Option α)) :
    hnRefine (junkCell x ∗ hnCtxt (eoarrayAssnAt A p) xs c ∗ hnCtxt natAssn (p + j) idx)
      (.aget x heapName idx) (hnCtxt natAssn (p + j) idx) (x, c)
      (eoCellAssn A ×ₐ eoarrayAssnAt A p) (mopOarrayExtract xs j) := by
  rw [mopOarrayExtract_def]
  refine hnr_assert fun h => ?_
  obtain ⟨hj, hne⟩ := h
  have hval : xs[j]! = xs[j] := getElem!_pos xs j hj
  obtain ⟨e, he⟩ : ∃ e, xs[j] = some e := by
    rcases hx : xs[j] with _ | e
    · rw [hval, hx] at hne; exact absurd rfl hne
    · exact ⟨e, rfl⟩
  have hget : (xs[j]!).get! = e := by rw [hval, he]; rfl
  rw [hget]
  exact hnRefineI_spect (oarrayExtract_junk_rule A x c idx p j xs e hj he)

/-! ### `upd` -/

/-- **The upd triple.** Pay one `ir.aset`, give up the element (cell and
resource), the array at a known base and the index cell holding `p + j`;
get the array back with slot `j` holding the element, and the cell back
as junk. The element's resource does not reappear anywhere — that is the
move. -/
theorem oarrayUpd_mop_rule {α : Type} (A : α → Val → Assn) (x c idx : String)
    (p j : ℕ) (xs : List (Option α)) (e : α) (hj : j < xs.length) (hxj : xs[j] = none) :
    irHtriple (¤(irUnit Currency.aset) ∗
        (hnCtxt (eoarrayAssnAt A p) xs c ∗ hnCtxt natAssn (p + j) idx ∗
          hnCtxt (eoCellAssn A) e x))
      (.aset heapName idx x)
      ((junkCell x ∗ hnCtxt natAssn (p + j) idx) ∗ eoarrayAssnAt A p (xs.set j (some e)) c) := by
  have e₁ : (¤(irUnit Currency.aset) ∗
      (hnCtxt (eoarrayAssnAt A p) xs c ∗ hnCtxt natAssn (p + j) idx ∗
        hnCtxt (eoCellAssn A) e x))
      = (∃ᵃ xsi, ((p ↦ₕ xsi) ∗ loAssn A xs xsi)) ∗
        (¤(irUnit Currency.aset) ∗ (c ↦ᵥ p) ∗ (idx ↦ᵥ (p + j)) ∗ eoCellAssn A e x) := by
    simp only [hnCtxt_def, natAssn_def, eoarrayAssnAt_def, naoAssn_def]
    ac_rfl
  rw [e₁]
  refine irHtriple_sepEx fun xsi => ?_
  have e₂ : (((p ↦ₕ xsi) ∗ loAssn A xs xsi) ∗
      (¤(irUnit Currency.aset) ∗ (c ↦ᵥ p) ∗ (idx ↦ᵥ (p + j)) ∗ eoCellAssn A e x))
      = (∃ᵃ w, ((x ↦ᵥ w) ∗ A e w)) ∗
        (((p ↦ₕ xsi) ∗ loAssn A xs xsi) ∗
          ¤(irUnit Currency.aset) ∗ (c ↦ᵥ p) ∗ (idx ↦ᵥ (p + j))) := by
    simp only [eoCellAssn_def]
    ac_rfl
  rw [e₂]
  refine irHtriple_sepEx fun w => ?_
  by_cases hlen : xsi.length = xs.length
  · have hj' : j < xsi.length := by omega
    have hbase := frame_rule (wp := wp) (α := irα)
      ((c ↦ᵥ p) ∗ A e w ∗ loAssn A xs xsi)
      (haset_triple idx x p j xsi w hj')
    refine irTriple.gc (cons_rule hbase (fun s hs => ?_) (fun _ s hs => ?_))
    · revert hs
      have ePre : (((x ↦ᵥ w) ∗ A e w) ∗
          (((p ↦ₕ xsi) ∗ loAssn A xs xsi) ∗
            ¤(irUnit Currency.aset) ∗ (c ↦ᵥ p) ∗ (idx ↦ᵥ (p + j))))
          = ((¤¤Currency.aset 1 ∗ (p ↦ₕ xsi) ∗ (idx ↦ᵥ (p + j)) ∗ (x ↦ᵥ w)) ∗
            ((c ↦ᵥ p) ∗ A e w ∗ loAssn A xs xsi)) := by
        rw [costCredits_one]
        ac_rfl
      rw [ePre]
      exact fun h => h
    · revert hs
      have ePost : (((p ↦ₕ xsi.set j w) ∗ (idx ↦ᵥ (p + j)) ∗ (x ↦ᵥ w)) ∗
          ((c ↦ᵥ p) ∗ A e w ∗ loAssn A xs xsi))
          = ((x ↦ᵥ w) ∗ (idx ↦ᵥ (p + j)) ∗ (c ↦ᵥ p) ∗
            ((p ↦ₕ xsi.set j w) ∗ (A e w ∗ loAssn A xs xsi))) := by
        ac_rfl
      have eGoal : ((junkCell x ∗ hnCtxt natAssn (p + j) idx) ∗
          eoarrayAssnAt A p (xs.set j (some e)) c)
          = (junkCell x ∗ (idx ↦ᵥ (p + j)) ∗ (c ↦ᵥ p) ∗ naoAssn A (xs.set j (some e)) p) := by
        simp only [hnCtxt_def, natAssn_def, eoarrayAssnAt_def]
        ac_rfl
      rw [ePost, eGoal, ← loAssn_insert xs xsi j e w hj hj' hxj]
      exact conj_entails_mono (ptoVar_entails_junkCell x w)
        (sepConj_mono_right (sepConj_mono_right
          (ptoH_loAssn_entails_naoAssn A p (xs.set j (some e)) (xsi.set j w)))) s
  · simp only [loAssn_of_length_ne hlen, sepConj_sepFalse, sepFalse_sepConj]
    exact irHtriple_of_sepFalse

/-- **The registered upd rule.** The linearity showcase at the element
level: `hnCtxt (eoCellAssn A) e x` is in `Γ` and **not** in `Γ'` — only
`junkCell x` comes back — so a second use of the element after this rule
is not derivable, while the *cell* is reusable, which is what a
three-address loop body needs. -/
@[sepref_fr_rules]
theorem hnr_mop_oarray_upd {α : Type} (A : α → Val → Assn) (x c idx : String)
    (p j : ℕ) (xs : List (Option α)) (e : α) :
    hnRefine (hnCtxt (eoarrayAssnAt A p) xs c ∗ hnCtxt natAssn (p + j) idx ∗
        hnCtxt (eoCellAssn A) e x)
      (.aset heapName idx x) (junkCell x ∗ hnCtxt natAssn (p + j) idx) c
      (eoarrayAssnAt A p) (mopOarrayUpd xs j e) := by
  rw [mopOarrayUpd_def]
  refine hnr_assert fun h => ?_
  obtain ⟨hj, hnone⟩ := h
  have hval : xs[j]! = xs[j] := getElem!_pos xs j hj
  exact hnRefineI_spect (oarrayUpd_mop_rule A x c idx p j xs e hj (by rw [← hval]; exact hnone))

/-! ## 5. Negative controls (falsification law, clause 2)

The carrier is authored, so the controls are theorems and compiled
checks, not comments. Each was flipped and confirmed to fail before the
positive direction was proved. -/

namespace HeapEOGate

open Plausible Ir.HeapGate

/-- **The non-vacuous instance** (judgment call D-B1a): an element that
*is* a one-cell heap block at the word stored in the slot. With a pure
`A` every control below would be vacuous, because the physical word
survives an extract and could be re-adopted; with `boxAssn` it cannot,
because the block is a resource. -/
def boxAssn : Val → Val → Assn := fun v w => (w ↦ₕ [v])

@[simp] theorem boxAssn_def (v w : Val) : boxAssn v w = (w ↦ₕ [v]) := rfl

/-! ### Control 1 — no double extract -/

/-- Extracting twice from the same slot **fails abstractly**: the second
`mop`'s own `ASSERT` is false, because the first extract left `None`
there. -/
theorem no_double_extract {α : Type} [Inhabited α] (xs : List (Option α)) (j : ℕ)
    (hj : j < xs.length) : ¬ (mopOarrayExtract (xs.set j none) j).nofailT := by
  rw [mopOarrayExtract_def, NRest.assert_neg, NRest.bindT_fail]
  · simp
  · rintro ⟨-, hne⟩
    exact hne (by rw [getElem!_pos _ j (by simpa using hj), List.getElem_set_self (by simpa using hj)])

/-- …and it fails **by ownership**, which is the reason that matters: at
the non-vacuous instance the element resource is not duplicable, so a
second copy of it is `sepFalse`. Flip `boxAssn` to a pure assertion and
this theorem is false. -/
theorem boxAssn_sepConj_self (v w : Val) :
    (boxAssn v w ∗ boxAssn v w) = (sepFalse : Assn) :=
  ptoH_sepConj_self w v v [] []

/-- The array still owning slot `j` and someone else holding that slot's
element at once is impossible: that is what makes `extract` a *move*. -/
theorem no_extract_and_keep {xs : List (Option Val)} {ys : List Val} {j : ℕ} {e : Val}
    (hj : j < xs.length) (hj' : j < ys.length) (hxj : xs[j] = some e) :
    (loAssn boxAssn xs ys ∗ boxAssn e ys[j]) = (sepFalse : Assn) := by
  rw [loAssn_extract xs ys j e hj hj' hxj, sepConj_assoc, sepConj_comm (loAssn _ _ _),
    ← sepConj_assoc, boxAssn_sepConj_self, sepFalse_sepConj]

/-! ### Control 2 — the ownership tag does not survive an extract -/

/-- **The tag is real.** After an extract the array does *not* entail its
pre-extract self: the element resource is gone and cannot be conjured,
even though the physical word is still sitting in the block. This is the
control that would be vacuous at a pure `A`. -/
theorem tag_not_recoverable :
    ¬ (loAssn boxAssn [none] [5] ⊢ loAssn boxAssn [some 7] [5]) := by
  have eEmpty : loAssn boxAssn ([none] : List (Option Val)) [5] = (□ : Assn) := by
    rw [loAssn_cons, oelemAssn_none, loAssn_nil, sepConj_emp]
  have eFull : loAssn boxAssn ([some 7] : List (Option Val)) [5] = ((5 : ℕ) ↦ₕ [7]) := by
    rw [loAssn_cons, oelemAssn_some, boxAssn_def, loAssn_nil, sepConj_emp]
  intro hent
  rw [eEmpty, eFull] at hent
  have h2 : ((5 : ℕ) ↦ₕ [7]) ((0, 0, 0), 0) := hent _ rfl
  have h3 : (0 : HCells) = hrange 5 [7] := h2.1.2.2
  have h4 := congrFun h3 5
  simp [hrange] at h4

/-! ### Control 3 — `upd` into an occupied slot -/

/-- Writing into a slot that is already `Some` **fails abstractly**. -/
theorem no_upd_occupied {α : Type} (xs : List (Option α)) (j : ℕ) (e e' : α)
    (hj : j < xs.length) : ¬ (mopOarrayUpd (xs.set j (some e')) j e).nofailT := by
  rw [mopOarrayUpd_def, NRest.assert_neg, NRest.bindT_fail]
  · simp
  · rintro ⟨-, hnone⟩
    rw [getElem!_pos _ j (by simpa using hj),
      List.getElem_set_self (by simpa using hj)] at hnone
    exact absurd hnone (by simp)

/-- **`lo_insert_elem`'s `= None` premise is load-bearing**: drop it and
the equation is *false*. At an occupied slot the left-hand side owns the
new element only, while the right-hand side owns the new element *and*
the old one — which is the leak that turns a linear move into an
overwrite. -/
theorem insert_needs_none :
    loAssn boxAssn ([some 9] : List (Option Val)) ([6] : List Val)
      ≠ (boxAssn 9 6 ∗ loAssn boxAssn [some 7] [5]) := by
  have hl : loAssn boxAssn ([some 9] : List (Option Val)) ([6] : List Val)
      = ((6 : ℕ) ↦ₕ [9]) := by
    rw [loAssn_cons, oelemAssn_some, boxAssn_def, loAssn_nil, sepConj_emp]
  have hr : (boxAssn 9 6 ∗ loAssn boxAssn ([some 7] : List (Option Val)) ([5] : List Val))
      = (((6 : ℕ) ↦ₕ [9]) ∗ ((5 : ℕ) ↦ₕ [7])) := by
    rw [boxAssn_def, loAssn_cons, oelemAssn_some, boxAssn_def, loAssn_nil, sepConj_emp]
  intro heq
  rw [hl, hr] at heq
  have h6 : ((6 : ℕ) ↦ₕ [9]) ((0, 0, hrange 6 [9]), 0) := ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  rw [heq] at h6
  obtain ⟨-, hF⟩ := ptoH_sepConj_iff.1 h6
  obtain ⟨-, -, hH, -⟩ := ptoH_apply.1 hF
  have h5 := congrFun hH 5
  simp [HCells.eraseRange, hrange] at h5

/-! ### Control 4 — overlapping EO arrays -/

/-- Two EO arrays whose ranges overlap cannot both be owned. This is
A.1's `ptoH_sepConj_overlap` lifted through the hidden backing, and it is
what makes an `extract`/`upd` pair at overlapping ranges underivable: the
precondition is unsatisfiable. -/
theorem naoAssn_overlap_false {α : Type} {A : α → Val → Assn} {p q : ℕ}
    {xs ys : List (Option α)} (hpq : p ≤ q) (h1 : q < p + xs.length) (h2 : 0 < ys.length) :
    (naoAssn A xs p ∗ naoAssn A ys q) = (sepFalse : Assn) := by
  funext h
  refine propext ⟨?_, fun h' => h'.elim⟩
  rintro ⟨u, v, hd, huv, ⟨xsi, hu⟩, ⟨ysi, hv⟩⟩
  have hlx : xsi.length = xs.length := by
    obtain ⟨u₁, u₂, -, -, -, hu₂⟩ := hu; exact loAssn_length xs xsi u₂ hu₂
  have hly : ysi.length = ys.length := by
    obtain ⟨v₁, v₂, -, -, -, hv₂⟩ := hv; exact loAssn_length ys ysi v₂ hv₂
  have h1 : (((p ↦ₕ xsi) ∗ loAssn A xs xsi) ∗ ((q ↦ₕ ysi) ∗ loAssn A ys ysi)) h :=
    ⟨u, v, hd, huv, hu, hv⟩
  have hperm : (((p ↦ₕ xsi) ∗ loAssn A xs xsi) ∗ ((q ↦ₕ ysi) ∗ loAssn A ys ysi))
      = (((p ↦ₕ xsi) ∗ (q ↦ₕ ysi)) ∗ (loAssn A xs xsi ∗ loAssn A ys ysi)) := by ac_rfl
  rw [hperm, ptoH_sepConj_overlap hpq (by omega) (by omega), sepFalse_sepConj] at h1
  exact h1.elim

/-- The same at the registered form: two overlapping in-place EO arrays
are jointly unsatisfiable, so no rule instance can ever see both. -/
theorem eoarrayAssnAt_overlap_false {α : Type} {A : α → Val → Assn} {p q : ℕ} {c c' : String}
    {xs ys : List (Option α)} (hpq : p ≤ q) (h1 : q < p + xs.length) (h2 : 0 < ys.length) :
    (eoarrayAssnAt A p xs c ∗ eoarrayAssnAt A q ys c') = (sepFalse : Assn) := by
  have e : (eoarrayAssnAt A p xs c ∗ eoarrayAssnAt A q ys c')
      = ((naoAssn A xs p ∗ naoAssn A ys q) ∗ ((c ↦ᵥ p) ∗ (c' ↦ᵥ q))) := by
    simp only [eoarrayAssnAt_def]
    ac_rfl
  rw [e, naoAssn_overlap_false hpq h1 h2, sepFalse_sepConj]

/-! ### The compiled gate

The abstract side by kernel computation, the resource side through
A.1's decidable `hrange`. -/

-- The tag really moves: extract empties the slot, and the emptied slot
-- is what the second extract's `ASSERT` rejects.
#guard (([some 3, some 4] : List (Option ℕ)).set 0 none) == [none, some 4]
#guard (([none, some 4] : List (Option ℕ))[0]!) == none
#guard !((([none, some 4] : List (Option ℕ))[0]!) != none)

-- …and `upd` refills exactly that slot and no other.
#guard (([none, some 4] : List (Option ℕ)).set 0 (some 3)) == [some 3, some 4]
#guard (([none, some 4] : List (Option ℕ)).set 0 (some 3)) != [some 3, none]

-- **`upd`'s `= None` premise, compiled**: the slot it is offered must
-- read `none`. Flip the expected value here and the guard fails.
#guard (([some 3, some 4] : List (Option ℕ))[0]!) != none

-- The instance `insert_needs_none` refutes, spelled as an `upd` into an
-- occupied slot: these are exactly `xs.set j (some 9)` and `ys.set j 6`
-- at `xs = [some 7]`, `ys = [5]`, `j = 0`.
#guard (([some 7] : List (Option ℕ)).set 0 (some 9)) == [some 9]
#guard (([5] : List ℕ).set 0 6) == [6]

-- extract-then-upd is the identity on the tag list…
#guard ((([some 3, some 4] : List (Option ℕ)).set 0 none).set 0 (some 3)) == [some 3, some 4]
-- …while extract-then-extract is not even offered a legal slot.
#guard ((([some 3, some 4] : List (Option ℕ)).set 0 none).set 0 none) == [none, some 4]

-- **The overlap control, by computation.** Two EO arrays of length 2 at
-- bases 2 and 3 share a cell, so their backings are not disjoint…
#guard !disjOnB idxs (hrange 2 [7, 8]) (hrange 3 [9, 9])
-- …while bases 2 and 4 are fine.
#guard disjOnB idxs (hrange 2 [7, 8]) (hrange 4 [9, 9])

-- **The boxed element is a resource.** Two copies of the same box
-- overlap; two boxes at different words do not. Were the first of these
-- `disjOnB`, `boxAssn_sepConj_self` would be false and every ownership
-- control above would be vacuous.
#guard !disjOnB idxs (hrange 5 [7]) (hrange 5 [7])
#guard disjOnB idxs (hrange 5 [7]) (hrange 6 [7])

-- Sampled: a box extracted from slot `j` never overlaps the box of a
-- different slot, whatever the slot contents.
#test ∀ m : ℕ, disjOnB idxs (hrange (m % 4) [1]) (hrange (m % 4 + 1) [2])

/-! ### The cost decision, pinned (judgment call D-B1c)

One unit per access, and the address arithmetic charged to the caller
where it happens rather than folded into the access. -/

/-- The extract's price, currency by currency: one `ir.aget`, no
`ofs_ptr`, nothing else. -/
def extractCost : List (String × ℕ∞) := Ir.Gate.creditVector (irUnit Currency.aget)

/-- The upd's price: one `ir.aset`. -/
def updCost : List (String × ℕ∞) := Ir.Gate.creditVector (irUnit Currency.aset)

#guard extractCost == [("ir.skip", 0), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 1),
  ("ir.aset", 0), ("ir.ite", 0), ("ir.while", 0), ("ir.add", 0), ("ir.sub", 0),
  ("ir.mul", 0), ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0),
  ("ir.shiftl", 0), ("ir.shiftr", 0)]

#guard updCost == [("ir.skip", 0), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 0),
  ("ir.aset", 1), ("ir.ite", 0), ("ir.while", 0), ("ir.add", 0), ("ir.sub", 0),
  ("ir.mul", 0), ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0),
  ("ir.shiftl", 0), ("ir.shiftr", 0)]

#guard extractCost != updCost

/-- **The arithmetic is not hidden.** A caller that must form the
absolute address `p + j` pays for it: this is the price of
`idx := base + off` followed by an extract, and it carries **both** an
`ir.add` and an `ir.aget`. The source's `ofs_ptr` charge has not
disappeared, it has moved to the instruction that does the work. -/
def addrExtractCost : List (String × ℕ∞) :=
  Ir.Gate.creditVector (irUnit (binopCurrency Imp.Bop.add) + irUnit Currency.aget)

#guard addrExtractCost == [("ir.skip", 0), ("ir.const", 0), ("ir.copy", 0), ("ir.aget", 1),
  ("ir.aset", 0), ("ir.ite", 0), ("ir.while", 0), ("ir.add", 1), ("ir.sub", 0),
  ("ir.mul", 0), ("ir.div", 0), ("ir.and", 0), ("ir.or", 0), ("ir.xor", 0),
  ("ir.shiftl", 0), ("ir.shiftr", 0)]

#guard addrExtractCost != extractCost

/-! ### Non-vacuity, and the synthesizer

The rules are instantiable at concrete arguments, and `sepref_synth`
really does find them: the acceptance criterion of A.1 (a layer the tower
cannot reach is not progress), at leaf B. -/

/-! #### The carrier is inhabited

Without this everything above could be an elaborate way of saying
`sepFalse`. A two-slot EO array based at heap index `1`, one slot holding
a boxed `7` whose box lives at heap index `5` and one slot `None`, is
satisfied by a concrete resource — and the resource owns exactly
`{1, 2}` (the block) together with `{5}` (the box), which is the
element-level ownership this leaf is about. -/

/-- The block `[1, 3)` and the box at `5` are disjoint resources. -/
theorem gate_disj : hrange 1 [5, 9] ## hrange 5 [7] := by
  intro i
  by_cases h : 1 ≤ i ∧ i < 3
  · exact Or.inr (hrange_apply_eq_zero (by omega))
  · exact Or.inl (hrange_apply_eq_zero h)

/-- The element part of that array *is* the box, on the nose: slot `0`
owns `5 ↦ₕ [7]` and slot `1` owns nothing. -/
theorem gate_loAssn :
    loAssn boxAssn ([some 7, none] : List (Option Val)) ([5, 9] : List Val)
      = ((5 : ℕ) ↦ₕ [7]) := by
  rw [loAssn_cons, oelemAssn_some, boxAssn_def, loAssn_cons, oelemAssn_none, loAssn_nil,
    sepConj_emp, sepConj_emp]

/-- **Non-vacuity.** The EO array assertion holds at a concrete
resource. -/
theorem gate_naoAssn_holds :
    naoAssn boxAssn [some 7, none] 1 ((0, 0, hrange 1 [5, 9] + hrange 5 [7]), 0) := by
  refine ⟨[5, 9], ((0, 0, hrange 1 [5, 9]), 0), ((0, 0, hrange 5 [7]), 0),
    ⟨⟨sep_zero_disj 0, sep_zero_disj 0, gate_disj⟩, trivial⟩, ?_, ⟨⟨rfl, rfl, rfl⟩, rfl⟩, ?_⟩
  · show ((0, 0, hrange 1 [5, 9] + hrange 5 [7]), (0 : ECost))
      = ((0, 0, hrange 1 [5, 9]), 0) + ((0, 0, hrange 5 [7]), 0)
    rw [Prod.mk_add_mk, Prod.mk_add_mk, Prod.mk_add_mk, sep_zero_add, sep_zero_add,
      sep_zero_add]
  · rw [gate_loAssn]
    exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩

/-- …and so does the registered form, with the base pointer in a cell. -/
theorem gate_eoarrayAssnAt_holds :
    eoarrayAssnAt boxAssn 1 [some 7, none] "c"
      ((Cells.single "c" 1, 0, hrange 1 [5, 9] + hrange 5 [7]), 0) := by
  refine ⟨((Cells.single "c" 1, 0, 0), 0), ((0, 0, hrange 1 [5, 9] + hrange 5 [7]), 0),
    ⟨⟨fun y => Tsa.disj_zero _, fun b => Tsa.zero_disj _, fun i => Tsa.zero_disj _⟩, trivial⟩,
    ?_, ⟨⟨rfl, rfl⟩, rfl⟩, gate_naoAssn_holds⟩
  show ((Cells.single "c" 1, 0, hrange 1 [5, 9] + hrange 5 [7]), (0 : ECost))
    = ((Cells.single "c" 1, 0, 0), 0) + ((0, 0, hrange 1 [5, 9] + hrange 5 [7]), 0)
  rw [Prod.mk_add_mk, Prod.mk_add_mk, Prod.mk_add_mk, sep_add_zero, sep_zero_add,
    sep_zero_add, sep_zero_add]

-- The resource that witness owns, index by index: the two block cells
-- and the box cell, and nothing else.
#guard idxs.all fun i =>
  ((hrange 1 [5, 9] + hrange 5 [7]) i == 0) == !(i == 1 || i == 2 || i == 5)

/-- The extract mop does not fail at a legal slot. -/
theorem mopOarrayExtract_nofail (xs : List (Option ℕ)) (j : ℕ) (hj : j < xs.length)
    (hne : xs[j]! ≠ none) : (mopOarrayExtract xs j).nofailT := by
  rw [mopOarrayExtract_def, NRest.assert_pos ⟨hj, hne⟩, NRest.returnT_bindT]
  exact nofailT_consume_iff.2 (NRest.nofailT_returnT _)

/-- The upd mop does not fail at an empty slot. -/
theorem mopOarrayUpd_nofail (xs : List (Option ℕ)) (j : ℕ) (e : ℕ) (hj : j < xs.length)
    (hnone : xs[j]! = none) : (mopOarrayUpd xs j e).nofailT := by
  rw [mopOarrayUpd_def, NRest.assert_pos ⟨hj, hnone⟩, NRest.returnT_bindT]
  exact nofailT_consume_iff.2 (NRest.nofailT_returnT _)

/-- Positive control: the registered extract rule at concrete cells. -/
example : hnRefine (junkCell "x" ∗ hnCtxt (eoarrayAssnAt boxAssn 3) [some 7, none] "c" ∗
    hnCtxt natAssn (3 + 0) "i") (.aget "x" heapName "i") (hnCtxt natAssn (3 + 0) "i") ("x", "c")
    (eoCellAssn boxAssn ×ₐ eoarrayAssnAt boxAssn 3) (mopOarrayExtract [some 7, none] 0) :=
  hnr_mop_oarray_extract boxAssn "x" "c" "i" 3 0 [some 7, none]

/-- Positive control: the registered upd rule at concrete cells. -/
example : hnRefine (hnCtxt (eoarrayAssnAt boxAssn 3) [none, some 7] "c" ∗
    hnCtxt natAssn (3 + 0) "i" ∗ hnCtxt (eoCellAssn boxAssn) 9 "x") (.aset heapName "i" "x")
    (junkCell "x" ∗ hnCtxt natAssn (3 + 0) "i") "c" (eoarrayAssnAt boxAssn 3)
    (mopOarrayUpd [none, some 7] 0 9) :=
  hnr_mop_oarray_upd boxAssn "x" "c" "i" 3 0 [none, some 7] 9

/-! #### `sepref_synth` really does consume the rules -/

sepref_synth eoExtractSynth (p j : ℕ) (xs : List (Option ℕ)) :
  hnRefine (junkCell "x" ∗ hnCtxt (eoarrayAssnAt boxAssn p) xs "c" ∗
      hnCtxt natAssn (p + j) "i")
    _ _ ("x", "c") (eoCellAssn boxAssn ×ₐ eoarrayAssnAt boxAssn p) (mopOarrayExtract xs j)

-- The synthesized program, pinned: one heap read at the absolute address.
#guard eoExtractSynth_impl = Com.aget "x" heapName "i"

sepref_synth eoUpdSynth (p j : ℕ) (xs : List (Option ℕ)) (e : ℕ) :
  hnRefine (hnCtxt (eoarrayAssnAt boxAssn p) xs "c" ∗ hnCtxt natAssn (p + j) "i" ∗
      hnCtxt (eoCellAssn boxAssn) e "x")
    _ _ "c" (eoarrayAssnAt boxAssn p) (mopOarrayUpd xs j e)

#guard eoUpdSynth_impl = Com.aset heapName "i" "x"

/-! #### Axioms

The four laws and the two registered rules, on the three standard
axioms and nothing else. -/

/-- info: 'Lax13Proofs.Refine.Sepref.loAssn_replicate_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loAssn_replicate_none

/-- info: 'Lax13Proofs.Refine.Sepref.loAssn_all_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loAssn_all_none

/-- info: 'Lax13Proofs.Refine.Sepref.loAssn_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loAssn_extract

/-- info: 'Lax13Proofs.Refine.Sepref.loAssn_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loAssn_insert

/-- info: 'Lax13Proofs.Refine.Sepref.hnr_mop_oarray_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_oarray_extract

/-- info: 'Lax13Proofs.Refine.Sepref.hnr_mop_oarray_upd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hnr_mop_oarray_upd

/-- info: 'Lax13Proofs.Refine.Sepref.HeapEOGate.eoExtractSynth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eoExtractSynth

/-- info: 'Lax13Proofs.Refine.Sepref.HeapEOGate.eoUpdSynth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eoUpdSynth

end HeapEOGate

end Lax13Proofs.Refine.Sepref
