import Lax13Proofs.Refine.Ir.Triples

/-!
The heap ownership view: range ownership for arrays.

Leaf **P4.5.A.1** of `plans/word-ram/tower-expansion/p4.5-design.md`
(ledger **E25**). This is our `ll_range`: the missing granularity that
lets one array carry unboundedly many *independently ownable* regions,
which is what unconditional `push` needs and what judgment call **D-m**
of `Assn.lean` declined for P5 ("P5's lowering never needs a
sub-range" — P4.5 is where that stops being true).

Source pin `isabelle_llvm_time` @ `42dd7f5`, `thys/ds/Proto_EOArray.thy`
(quoted in the design note §3). The four laws leaf B must reproduce —
`lo_init`, `lo_free`, `lo_extract_elem`, `lo_insert_elem` — are
**equations**, and that exactness is the point: it is what makes later
move/swap costs exact rather than bounded. This file builds the *range*
layer they are stated over, and delivers split, join and single-index
focus as equations (`ptoH_append`, `ptoH_focus`, `ptoH_extract`).

## The architecture (decision D-A1)

One reserved array name — `Assn.lean`'s `heapName` — carries a second,
**per-index** view, and `AState` carries that view as its third memory
component. There is exactly one carrier, one `irα`, one `irSTATE` and
one `hnRefine`: a heap triple is an `irTriple` like any other, so
anything built here is registrable as an `@[sepref_fr_rules]` rule and
reachable by `sepref_synth`. The pieces:

* `HCells := ℕ → Tsa Val` and `hcells s i`, both in `Assn.lean` beside
  the component they belong to;
* `acells` sends `heapName` to `Tsa.zero`, so the heap name is
  **unownable** in the whole-name view. That is a soundness requirement,
  not hygiene: if the name were ownable in both views, framing a range
  assertion across a whole-name `aset` on that name would be unsound,
  because the two views are not disjoint in the underlying `Ir.State`.
  It is discharged by `not_irSTATE_ptoArr_heapName` below (nothing can
  ever own `heapName ↦ₐ xs` at any state) together with
  `acells_setArr_heapName` (a heap write is invisible to the whole-name
  view), and those two facts are exactly what let `haset_triple` keep
  the array frame untouched.
* `p ↦ₕ xs` owns indices `[p, p + xs.length)`, splits and joins at any
  point, and singleton ownership is `p ↦ₕ [v]`.

**No new `Ir.Com` constructor.** A heap access is an ordinary
`aget`/`aset` on `heapName` at a computed index, so the sixteen
currencies, `Currency.all`, `embed`, `weight`/`cash`, `BigStepB`,
`bpre`/`bwp` and `embed_sim` are inherited unchanged — the D3 codegen
obligation is discharged by inheritance rather than extended.

## Judgment calls

**D-A1a — the carrier is widened in place, and there is no second
logic.** An earlier revision of this file put the heap component in an
*extension* carrier `AState × HCells` with its own abstraction and its
own triple form, so that the thirteen probe/example sites which spell an
`AState` literally as `((vcells s, acells s), c)` would not have to
change. That is rejected: `hnRefine` (`Sepref/Basic.lean`) is defined
over `irSTATE`, so nothing stated in a second logic can ever produce a
registrable `sepref_fr_rules` rule, and A.2's allocator could not be
consumed by `sepref_synth` nor P5.E re-seat a structure onto the heap —
which is the whole purpose of P4.5. A transfer seam is *possible* (the
lift holds under a decidable "does not write `heapName`" side condition)
but it would thread that condition through every downstream rule
forever. The one-time cost is instead paid where it belongs: `AState`
is `(Cells Val × Cells (List Val) × HCells) × ECost`, and the thirteen
sites gained one tuple component each. The `ptoArr` interface
(`ptoArr_arrs`, `ptoArr_setArr`, `ptoArr_sepConj_self`, and the
`arrayAssn` defeq) is preserved verbatim: owning a name in the
whole-name view already forces `a ≠ heapName`, so those statements are
vacuous at the heap name and need no side condition.

The recorded alternative to D-A1 — mangled reserved *names* inside the
existing scalar component — was rejected as **unsound**, not merely
uglier: it makes `ptoVar_setVar` false at a mangled name (`setVar`
cannot change the reserved array such a name would have to read), and
`ptoVar_setVar` is what every landed op triple rests on.

**D-A1b — the range is a total function, not a `sep_set_img` fold.**
The source's `ll_range` is a finite `**`-fold of single-cell points-to
over an index set. Ours is the `HCells` element `hrange p xs`, which is
`Tsa.triv` exactly on `[p, p + xs.length)`. The two are the same
resource; the function form is the one that makes split/join *equations*
by `EXACT_split` rather than inductions over the index set, and it is
decidable, which is what the compiled negative controls below need.

**D-A1c — the heap triples take the index as `p + j`.** `aget_triple`
takes the whole array `xs` and an index `k` with `xs[k]? = some w`; the
heap forms take the range `p ↦ₕ xs`, an offset `j` into it, and the
program-level index cell holding `p + j`. That is the source's
`p' -ₐ p ∈ I` side condition in the shape the extract's port notes
prescribe for us — an offset bound rather than pointer compatibility.
-/

namespace Lax13Proofs.Refine.Ir

/-! ## 1. The range assertion

`hrange p xs` is our `ll_range`: the `HCells` resource owning the
indices `[p, p + xs.length)` and holding `xs` (judgment call D-A1b). -/

/-- The heap resource owning `[p, p + xs.length)` and holding `xs`. -/
def hrange (p : ℕ) (xs : List Val) : HCells :=
  fun i => Tsa.ofOption (if p ≤ i then xs[i - p]? else none)

/-- `p ↦ₕ xs`: the indices `[p, p + xs.length)` of the reserved heap
array exist and hold `xs`, and this assertion owns them. The source's
`ll_range`, at our one reserved name; the two `SND`s pick the heap out
of `AState`'s memory half, exactly as `↦ᵥ` and `↦ₐ` pick the other
two. -/
def ptoH (p : ℕ) (xs : List Val) : Assn := FST (SND (SND (EXACT (hrange p xs))))

@[inherit_doc] infix:70 " ↦ₕ " => ptoH

/-- What a range assertion says on the nose: it owns exactly those heap
indices, no scalars, no named arrays and no credits. -/
theorem ptoH_apply {p : ℕ} {xs : List Val} {V : Cells Val} {Ar : Cells (List Val)}
    {H : HCells} {cr : ECost} :
    (p ↦ₕ xs) ((V, Ar, H), cr) ↔ V = 0 ∧ Ar = 0 ∧ H = hrange p xs ∧ cr = 0 :=
  ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩⟩

/-! ### Pointwise reading -/

theorem hrange_apply_of_lt {p : ℕ} {xs : List Val} {i : ℕ} (h : i < p) :
    hrange p xs i = 0 := by
  simp [hrange, Nat.not_le.2 h]

theorem hrange_apply_mem {p : ℕ} {xs : List Val} {j : ℕ} (hj : j < xs.length) :
    hrange p xs (p + j) = .triv xs[j] := by
  simp [hrange, List.getElem?_eq_getElem hj]

theorem hrange_apply_of_ge {p : ℕ} {xs : List Val} {i : ℕ} (h : p + xs.length ≤ i) :
    hrange p xs i = 0 := by
  have hp : p ≤ i := le_trans (Nat.le_add_right _ _) h
  have : xs.length ≤ i - p := by omega
  simp [hrange, hp, List.getElem?_eq_none this]

/-- Outside the range, nothing is owned — the form the disjointness
proofs consume. -/
theorem hrange_apply_eq_zero {p : ℕ} {xs : List Val} {i : ℕ}
    (h : ¬ (p ≤ i ∧ i < p + xs.length)) : hrange p xs i = 0 := by
  rcases Nat.lt_or_ge i p with hi | hi
  · exact hrange_apply_of_lt hi
  · exact hrange_apply_of_ge (by omega)

@[simp] theorem hrange_nil (p : ℕ) : hrange p [] = 0 := by
  funext i; exact hrange_apply_eq_zero (by simp)

@[simp] theorem ptoH_nil (p : ℕ) : (p ↦ₕ []) = (□ : Assn) := by
  show FST (SND (SND (EXACT (hrange p [])))) = □
  rw [hrange_nil, EXACT_zero, SND_emp, SND_emp, FST_emp]

/-! ### Split and join, as one equation

`hrange_append` is the resource-level equation and `ptoH_append` the
assertion-level one. A range splits at *any* point and rejoins, and
singleton ownership is `p ↦ₕ [v]`. -/

theorem hrange_disj_append (p : ℕ) (xs ys : List Val) :
    hrange p xs ## hrange (p + xs.length) ys := by
  intro i
  rcases Nat.lt_or_ge i (p + xs.length) with hi | hi
  · exact Or.inr (hrange_apply_eq_zero (by omega))
  · exact Or.inl (hrange_apply_of_ge hi)

theorem hrange_append (p : ℕ) (xs ys : List Val) :
    hrange p (xs ++ ys) = hrange p xs + hrange (p + xs.length) ys := by
  funext i
  show hrange p (xs ++ ys) i = hrange p xs i + hrange (p + xs.length) ys i
  rcases Nat.lt_or_ge i p with hi | hi
  · rw [hrange_apply_of_lt hi, hrange_apply_of_lt hi,
      hrange_apply_of_lt (show i < p + xs.length by omega), sep_zero_add]
  · obtain ⟨j, rfl⟩ : ∃ j, i = p + j := ⟨i - p, by omega⟩
    rcases Nat.lt_or_ge j xs.length with hj | hj
    · have hj' : j < (xs ++ ys).length := by simp; omega
      rw [hrange_apply_mem hj', hrange_apply_mem hj,
        hrange_apply_of_lt (show p + j < p + xs.length by omega), sep_add_zero]
      congr 1
      exact List.getElem_append_left hj
    · rw [hrange_apply_of_ge (show p + xs.length ≤ p + j by omega), sep_zero_add]
      rcases Nat.lt_or_ge (j - xs.length) ys.length with hk | hk
      · have hj' : j < (xs ++ ys).length := by simp; omega
        have he : p + j = p + xs.length + (j - xs.length) := by omega
        rw [hrange_apply_mem hj', he, hrange_apply_mem hk]
        congr 1
        exact List.getElem_append_right hj
      · rw [hrange_apply_of_ge (show p + (xs ++ ys).length ≤ p + j by simp; omega),
          hrange_apply_of_ge (show p + xs.length + ys.length ≤ p + j by omega)]

/-- **Split and join**, as an equation: a range splits at any point and
rejoins. This is `ll_range`'s `sep_set_img` decomposition, and the
exactness is what the four `lo_*` laws of leaf B need. -/
theorem ptoH_append (p : ℕ) (xs ys : List Val) :
    (p ↦ₕ (xs ++ ys)) = (p ↦ₕ xs) ∗ ((p + xs.length) ↦ₕ ys) := by
  show FST (SND (SND (EXACT (hrange p (xs ++ ys))))) = _
  rw [hrange_append, EXACT_split (hrange_disj_append p xs ys), ← SND_sepConj, ← SND_sepConj,
    ← FST_sepConj]
  rfl

/-- **Single-index focus**, as an equation: the slot at offset `k` is
peeled out of the range and the two stumps are kept. The converse — the
join — is this equation read right to left, which is why `lo_insert_elem`
costs nothing extra at leaf B. -/
theorem ptoH_focus {p : ℕ} {xs : List Val} {k : ℕ} (hk : k < xs.length) :
    (p ↦ₕ xs) =
      (p ↦ₕ xs.take k) ∗ (((p + k) ↦ₕ [xs[k]]) ∗ ((p + k + 1) ↦ₕ xs.drop (k + 1))) := by
  have hdrop : xs.drop k = xs[k] :: xs.drop (k + 1) := (List.getElem_cons_drop hk).symm
  have hsplit : xs = xs.take k ++ ([xs[k]] ++ xs.drop (k + 1)) := by
    rw [List.singleton_append, ← hdrop, List.take_append_drop]
  have hlen : (xs.take k).length = k := by
    rw [List.length_take]; omega
  conv_lhs => rw [hsplit]
  rw [ptoH_append, ptoH_append, hlen, List.length_singleton]

/-- The `lo_extract_elem` shape: the focused slot in front. -/
theorem ptoH_extract {p : ℕ} {xs : List Val} {k : ℕ} (hk : k < xs.length) :
    (p ↦ₕ xs) =
      ((p + k) ↦ₕ [xs[k]]) ∗ ((p ↦ₕ xs.take k) ∗ ((p + k + 1) ↦ₕ xs.drop (k + 1))) := by
  rw [ptoH_focus hk, sepConj_left_comm]

/-! ### The extraction lemma

`ptoH_sepConj_iff` is `ptoArr_sepConj_iff` at a range: owning the range
splits the heap map into the range and the rest. -/

/-- The heap cells with the range `[p, p + n)` given up. The range
analogue of `Cells.erase`. -/
def HCells.eraseRange (H : HCells) (p n : ℕ) : HCells :=
  fun i => if p ≤ i ∧ i < p + n then 0 else H i

theorem hrange_disj_eraseRange (H : HCells) (p : ℕ) (xs : List Val) :
    hrange p xs ## H.eraseRange p xs.length := by
  intro i
  by_cases h : p ≤ i ∧ i < p + xs.length
  · exact Or.inr (by simp [HCells.eraseRange, h])
  · exact Or.inl (hrange_apply_eq_zero h)

/-- The decomposition every range extraction turns on — `Cells`'
`single_add_erase`, at a range. -/
theorem hrange_add_eraseRange {H : HCells} {p : ℕ} {xs : List Val}
    (h : ∀ j, (hj : j < xs.length) → H (p + j) = .triv xs[j]) :
    hrange p xs + H.eraseRange p xs.length = H := by
  funext i
  show hrange p xs i + H.eraseRange p xs.length i = H i
  by_cases hi : p ≤ i ∧ i < p + xs.length
  · obtain ⟨j, rfl⟩ : ∃ j, i = p + j := ⟨i - p, by omega⟩
    have hj : j < xs.length := by omega
    rw [hrange_apply_mem hj, Tsa.triv_add, h j hj]
  · rw [hrange_apply_eq_zero hi, sep_zero_add]
    simp [HCells.eraseRange, hi]

theorem ptoH_sepConj_iff {p : ℕ} {xs : List Val} {F : Assn} {V : Cells Val}
    {Ar : Cells (List Val)} {H : HCells} {cr : ECost} :
    ((p ↦ₕ xs) ∗ F) ((V, Ar, H), cr) ↔
      (∀ j, (hj : j < xs.length) → H (p + j) = .triv xs[j]) ∧
        F ((V, Ar, H.eraseRange p xs.length), cr) := by
  constructor
  · rintro ⟨⟨⟨pv, pa, ph⟩, pc⟩, ⟨⟨qv, qa, qh⟩, qc⟩, hd, hpq, hp, hq⟩
    obtain ⟨hp1, hp2, hp3, hp4⟩ := ptoH_apply.1 hp
    subst hp1; subst hp2; subst hp3; subst hp4
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at hpq
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hpq
    have hzero : ∀ j, j < xs.length → qh (p + j) = 0 := by
      intro j hj
      have hx : hrange p xs (p + j) ## qh (p + j) := hd.1.2.2 (p + j)
      rw [hrange_apply_mem hj] at hx
      exact Tsa.eq_zero_of_disj_triv (sep_disj_commuteI hx)
    refine ⟨?_, ?_⟩
    · intro j hj
      show hrange p xs (p + j) + qh (p + j) = _
      rw [hrange_apply_mem hj, Tsa.triv_add]
    · have herase : (hrange p xs + qh).eraseRange p xs.length = qh := by
        funext i
        by_cases hi : p ≤ i ∧ i < p + xs.length
        · obtain ⟨j, rfl⟩ : ∃ j, i = p + j := ⟨i - p, by omega⟩
          simp only [HCells.eraseRange, if_pos hi]
          exact (hzero j (by omega)).symm
        · simp only [HCells.eraseRange, if_neg hi]
          show hrange p xs i + qh i = qh i
          rw [hrange_apply_eq_zero hi, sep_zero_add]
      rw [herase, sep_zero_add, sep_zero_add, sep_zero_add]
      exact hq
  · rintro ⟨hval, hF⟩
    refine ⟨((0, 0, hrange p xs), 0), ((V, Ar, H.eraseRange p xs.length), cr),
      ⟨⟨sep_zero_disj V, sep_zero_disj Ar, hrange_disj_eraseRange H p xs⟩, trivial⟩, ?_,
      ⟨⟨rfl, rfl, rfl⟩, rfl⟩, hF⟩
    show ((V, Ar, H), cr) = ((0, 0, hrange p xs), 0) + ((V, Ar, H.eraseRange p xs.length), cr)
    rw [Prod.mk_add_mk, Prod.mk_add_mk, Prod.mk_add_mk, sep_zero_add, sep_zero_add,
      sep_zero_add, hrange_add_eraseRange hval]

/-! ### At a state

The two lemmas the op triples of §2 consume, in the shape of
`Assn.lean`'s `ptoArr_arrs` / `ptoArr_setArr`. -/

/-- Owning `p ↦ₕ xs` means the reserved array exists and holds `xs` at
the offsets the range covers. -/
theorem ptoH_get {p : ℕ} {xs : List Val} {F : Assn} {s : State} {cr : ECost}
    (h : irSTATE ((p ↦ₕ xs) ∗ F) (s, cr)) {j : ℕ} (hj : j < xs.length) :
    ∃ ys, s.arrs heapName = some ys ∧ ys[p + j]? = some xs[j] := by
  have h' : ((p ↦ₕ xs) ∗ F) ((vcells s, acells s, hcells s), cr) := h
  have h1 : hcells s (p + j) = .triv xs[j] := (ptoH_sepConj_iff.1 h').1 j hj
  rw [hcells_apply] at h1
  have h2 := Tsa.ofOption_eq_triv_iff.1 h1
  rcases hys : s.arrs heapName with _ | ys
  · rw [hys] at h2; simp at h2
  · rw [hys] at h2; exact ⟨ys, rfl, h2⟩

/-- …and writing one offset of it preserves the frame — including the
whole-name array frame, which is untouched because `heapName` is
unownable there (`acells_setArr_heapName`). -/
theorem ptoH_setArr {p : ℕ} {xs : List Val} {F : Assn} {s : State} {cr : ECost}
    {ys : List Val} {j : ℕ} {n : Val} (h : irSTATE ((p ↦ₕ xs) ∗ F) (s, cr))
    (hj : j < xs.length) (hys : s.arrs heapName = some ys) :
    irSTATE ((p ↦ₕ xs.set j n) ∗ F) (s.setArr heapName (ys.set (p + j) n), cr) := by
  have h' : ((p ↦ₕ xs) ∗ F) ((vcells s, acells s, hcells s), cr) := h
  obtain ⟨hval, hF⟩ := ptoH_sepConj_iff.1 h'
  obtain ⟨ys', hys', hyj⟩ := ptoH_get h hj
  rw [hys] at hys'
  obtain rfl := Option.some.inj hys'
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hyj
  have hcell : ∀ j', (hj' : j' < xs.length) → ys[p + j']? = some xs[j'] := by
    intro j' hj'
    have hv := hval j' hj'
    rw [hcells_apply, hys] at hv
    exact Tsa.ofOption_eq_triv_iff.1 hv
  show ((p ↦ₕ xs.set j n) ∗ F)
    ((vcells (s.setArr heapName (ys.set (p + j) n)),
      acells (s.setArr heapName (ys.set (p + j) n)),
      hcells (s.setArr heapName (ys.set (p + j) n))), cr)
  rw [vcells_setArr, acells_setArr_heapName, hcells_setArr_heapName]
  refine ptoH_sepConj_iff.2 ⟨?_, ?_⟩
  · intro j' hj'
    have hj'' : j' < xs.length := by simpa using hj'
    show Tsa.ofOption (ys.set (p + j) n)[p + j']? = _
    rcases eq_or_ne j' j with rfl | hne
    · rw [List.getElem?_set_self hlt, List.getElem_set_self hj']
      rfl
    · rw [List.getElem?_set_ne (show p + j ≠ p + j' by omega), hcell j' hj'',
        List.getElem_set_ne (Ne.symm hne) hj']
      rfl
  · have heq : HCells.eraseRange (fun i => Tsa.ofOption (ys.set (p + j) n)[i]?) p
        (xs.set j n).length = HCells.eraseRange (hcells s) p xs.length := by
      funext i
      rw [List.length_set]
      by_cases hi : p ≤ i ∧ i < p + xs.length
      · simp [HCells.eraseRange, hi]
      · have hne : p + j ≠ i := by rintro rfl; exact hi ⟨by omega, by omega⟩
        simp only [HCells.eraseRange, if_neg hi]
        rw [List.getElem?_set_ne hne, hcells_apply, hys]
        rfl
    rw [heq]
    exact hF

/-! ## 2. The heap-view triples

`Triples.lean`'s `aget_triple` / `aset_triple`, at `heapName` and a
range: pay one unit of the op's own currency, own the names you touch,
hand them back. Same triple form (`irTriple` / `irHtriple`), same
abstraction, same `wp`; no new `Ir.Com` constructor is involved — a heap
access *is* an `aget`/`aset` at a computed index — so the currencies and
the cost semantics are inherited verbatim. -/

/-- `x := heap[i]`, at offset `j` of an owned range: the source's
`ll_load_rule_range`, at the reserved name. The range assertion is
unchanged — a read does not consume it — and the offset bound is the
side condition its pointer-compatibility premises become
(judgment call D-A1c). -/
theorem haget_triple (x i : String) (v : Val) (p j : ℕ) (xs : List Val) (w : Val)
    (hj : j < xs.length) (hw : xs[j] = w) :
    irTriple (¤¤Currency.aget 1 ∗ x ↦ᵥ v ∗ (p ↦ₕ xs) ∗ i ↦ᵥ (p + j)) (.aget x heapName i)
      (x ↦ᵥ w ∗ (p ↦ₕ xs) ∗ i ↦ᵥ (p + j)) := by
  intro F q hq
  obtain ⟨s, cr⟩ := q
  rw [sepConj_assoc] at hq
  obtain ⟨hafford, hrest⟩ := costCredits_split hq
  rw [sepConj_assoc, sepConj_assoc] at hrest
  have hx : s.vars x = some v := ptoVar_vars hrest
  have hi : s.vars i = some (p + j) := ptoVar_vars (irSTATE_rot3 hrest)
  obtain ⟨ys, hys, hyj⟩ := ptoH_get (irSTATE_rot hrest) hj
  rw [wp_aget]
  refine ⟨by rw [hx]; simp, p + j, ys, w, hi, hys, by rw [hyj, hw], hafford, ?_⟩
  rw [sepConj_assoc, sepConj_assoc]
  exact ptoVar_setVar hrest

/-- `heap[i] := v`, at offset `j` of an owned range: the source's
`ll_store_rule_range`. The range is returned updated at the one offset,
everything else in it untouched, and the whole-name array frame is
untouched because the heap name is unownable there. -/
theorem haset_triple (i vn : String) (p j : ℕ) (xs : List Val) (n : Val)
    (hj : j < xs.length) :
    irTriple (¤¤Currency.aset 1 ∗ (p ↦ₕ xs) ∗ i ↦ᵥ (p + j) ∗ vn ↦ᵥ n) (.aset heapName i vn)
      ((p ↦ₕ xs.set j n) ∗ i ↦ᵥ (p + j) ∗ vn ↦ᵥ n) := by
  intro F q hq
  obtain ⟨s, cr⟩ := q
  rw [sepConj_assoc] at hq
  obtain ⟨hafford, hrest⟩ := costCredits_split hq
  rw [sepConj_assoc, sepConj_assoc] at hrest
  have hi : s.vars i = some (p + j) := ptoVar_vars (irSTATE_rot hrest)
  have hv : s.vars vn = some n := ptoVar_vars (irSTATE_rot3 hrest)
  obtain ⟨ys, hys, hyj⟩ := ptoH_get hrest hj
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hyj
  rw [wp_aset]
  refine ⟨p + j, n, ys, hi, hv, hys, hlt, hafford, ?_⟩
  rw [sepConj_assoc, sepConj_assoc]
  exact ptoH_setArr hrest hj hys

/-- The garbage-collecting forms, as `Triples.lean` states them
(judgment call D-v). `GC` absorbs leftover *credits* only, so a leaked
range stays a proof obligation rather than becoming garbage. -/
theorem haget_rule (x i : String) (v : Val) (p j : ℕ) (xs : List Val) (w : Val)
    (hj : j < xs.length) (hw : xs[j] = w) :
    irHtriple (¤¤Currency.aget 1 ∗ x ↦ᵥ v ∗ (p ↦ₕ xs) ∗ i ↦ᵥ (p + j)) (.aget x heapName i)
      (x ↦ᵥ w ∗ (p ↦ₕ xs) ∗ i ↦ᵥ (p + j)) :=
  (haget_triple x i v p j xs w hj hw).gc

theorem haset_rule (i vn : String) (p j : ℕ) (xs : List Val) (n : Val) (hj : j < xs.length) :
    irHtriple (¤¤Currency.aset 1 ∗ (p ↦ₕ xs) ∗ i ↦ᵥ (p + j) ∗ vn ↦ᵥ n) (.aset heapName i vn)
      ((p ↦ₕ xs.set j n) ∗ i ↦ᵥ (p + j) ∗ vn ↦ᵥ n) :=
  (haset_triple i vn p j xs n hj).gc

/-! ## 3. Negative controls

Falsification law, clause 2: this carrier is *authored* — it has no
source counterpart in our shape — so it is not exempt. The two the leaf
names are proved *and* compiled: overlapping ranges are not
simultaneously ownable, and the heap name is not ownable in the
whole-name view. -/

/-- **Negative control 1, as a theorem.** Two assertions cannot both own
a heap index: if the ranges overlap, their conjunction is `sepFalse`.
The `Assn.lean` analogue is `ptoArr_sepConj_self`. -/
theorem ptoH_sepConj_overlap {p q : ℕ} {xs ys : List Val} (hp : p ≤ q)
    (h1 : q < p + xs.length) (h2 : 0 < ys.length) :
    ((p ↦ₕ xs) ∗ (q ↦ₕ ys)) = (sepFalse : Assn) := by
  funext h
  obtain ⟨⟨V, Ar, H⟩, cr⟩ := h
  refine propext ⟨?_, fun h' => h'.elim⟩
  rintro ⟨⟨⟨pv, pa, ph⟩, pc⟩, ⟨⟨qv, qa, qh⟩, qc⟩, hd, -, hp', hq'⟩
  obtain ⟨-, -, rfl, -⟩ := ptoH_apply.1 hp'
  obtain ⟨-, -, rfl, -⟩ := ptoH_apply.1 hq'
  have hx : hrange p xs q ## hrange q ys q := hd.1.2.2 q
  obtain ⟨j, rfl⟩ : ∃ j, q = p + j := ⟨q - p, by omega⟩
  rw [hrange_apply_mem (show j < xs.length by omega),
    show p + j = (p + j) + 0 from rfl] at hx
  rw [hrange_apply_mem h2] at hx
  rcases hx with hx | hx <;> exact absurd hx (by simp)

/-- The same, at the shape that matters most: the same range twice. -/
theorem ptoH_sepConj_self (p : ℕ) (v w : Val) (xs ys : List Val) :
    ((p ↦ₕ (v :: xs)) ∗ (p ↦ₕ (w :: ys))) = (sepFalse : Assn) :=
  ptoH_sepConj_overlap (le_refl p) (by simp) (by simp)

/-- **Negative control 2, as a theorem.** The heap name is not ownable
in the whole-name view — at *any* state, whether or not the reserved
array exists. This is the disjointness decision D-A1 buys: it is what
makes `haset_triple`'s array frame sound, because no frame can ever
contain `heapName ↦ₐ ys`. -/
theorem not_irSTATE_ptoArr_heapName {xs : List Val} {F : Assn} {s : State} {cr : ECost} :
    ¬ irSTATE ((heapName ↦ₐ xs) ∗ F) (s, cr) := by
  intro h
  have h' : ((heapName ↦ₐ xs) ∗ F) ((vcells s, acells s, hcells s), cr) := h
  rw [ptoArr_sepConj_iff] at h'
  rw [acells_heapName] at h'
  exact absurd h'.1 (by simp)

/-! ### The compiled gate

Everything above, by computation. `hrange` is decidable by construction
(judgment call D-A1b), so the range algebra and both negative controls
are `#guard`-checkable, and the sampled forms are `Plausible`'s. Nothing
here is used by another module. -/

namespace HeapGate

open Plausible

/-- Disjointness of two heap resources, restricted to a list of
indices. -/
def disjOnB (idxs : List ℕ) (H K : HCells) : Bool :=
  idxs.all fun i => (H i == 0) || (K i == 0)

/-- The indices the checks below range over. -/
def idxs : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7]

-- A range owns exactly its own indices.
#guard idxs.all fun i => (hrange 2 [7, 8] i == 0) == !(2 ≤ i && i < 4)
#guard hrange 2 [7, 8] 2 == Tsa.triv 7
#guard hrange 2 [7, 8] 3 == Tsa.triv 8

-- Adjacent ranges compose…
#guard disjOnB idxs (hrange 2 [7, 8]) (hrange 4 [9])

-- …overlapping ones do not. **The negative control the leaf names.**
#guard !disjOnB idxs (hrange 2 [7, 8]) (hrange 3 [9])
#guard !disjOnB idxs (hrange 2 [7, 8]) (hrange 2 [9, 9])
#guard !disjOnB idxs (hrange 2 [7, 8]) (hrange 2 [7, 8])

-- Split and join, by computation: `hrange_append` at a sample.
#guard idxs.all fun i =>
  hrange 2 ([7, 8] ++ [9]) i == (hrange 2 [7, 8] + hrange 4 [9]) i

-- Focus: peeling offset 1 out of a three-cell range and putting the
-- three pieces back is the identity.
#guard idxs.all fun i =>
  hrange 2 [7, 8, 9] i
    == (hrange 2 [7] + (hrange 3 [8] + hrange 4 [9])) i

-- The empty range owns nothing, whatever the concrete contents — the
-- shape `lo_init` takes at leaf B.
#guard idxs.all fun i => hrange 2 [] i == 0

/-- A state that really does have a heap array, alongside an ordinary
one. -/
def gateState : State :=
  State.ofPairs [("i", 1)] [("A", [1, 2]), (heapName, [5, 6, 7])]

-- The reserved array is *there* in the state…
#guard gateState.arrs heapName == some [5, 6, 7]

-- …and it is owned per index in the heap view…
#guard hcells gateState 1 == Tsa.triv 6
#guard hcells gateState 3 == 0

-- …but owns **nothing** in the whole-name view. **The second negative
-- control the leaf names**: were this `≠ 0`, the two views would not be
-- disjoint and framing a range across a whole-name `aset` on the heap
-- would be unsound.
#guard acells gateState heapName == 0

-- Ordinary array names are untouched by the partition.
#guard acells gateState "A" == Tsa.triv [1, 2]

-- Sampled: disjointness of a range from the range that starts where it
-- ends, and non-disjointness of one that starts one cell earlier.
#test ∀ m : ℕ, disjOnB idxs (hrange (m % 3) [1, 2]) (hrange (m % 3 + 2) [3])
#test ∀ m : ℕ, !disjOnB idxs (hrange (m % 3) [1, 2]) (hrange (m % 3 + 1) [3])

-- Sampled: split and join at every cut point of a three-cell range.
#test ∀ m : ℕ, idxs.all fun i =>
  hrange 2 [7, 8, 9] i
    == (hrange 2 (List.take (m % 4) [7, 8, 9])
        + hrange (2 + m % 4) (List.drop (m % 4) [7, 8, 9])) i

/-- The overlap control at the assertion level: two overlapping ranges
are jointly unsatisfiable. -/
example (p : ℕ) (v w : Val) : ¬ purePart ((p ↦ₕ [v]) ∗ (p ↦ₕ [w])) := by
  rintro ⟨h, hh⟩
  rw [ptoH_sepConj_self] at hh
  exact hh.elim

/-- The heap-name control at the assertion level: no state satisfies a
whole-name assertion about the heap. -/
example (xs : List Val) : ¬ irSTATE ((heapName ↦ₐ xs) ∗ (□ : Assn)) (gateState, 0) :=
  not_irSTATE_ptoArr_heapName

/-- Everything at `gateState` that the range `1 ↦ₕ [6, 7]` does not own,
as an `EXACT` resource (`Triples.lean`'s `rtFrame` trick). -/
def gateFrame : Assn :=
  EXACT ((vcells gateState, acells gateState, (hcells gateState).eraseRange 1 2), 0)

/-- **Non-vacuity.** The range assertion is not merely consistent, it
*holds* at a concrete state: `gateState` really does satisfy
`1 ↦ₕ [6, 7] ∗ gateFrame`. Without this the triples of §2 could all be
vacuous. -/
theorem gate_range_holds : irSTATE ((1 ↦ₕ [6, 7]) ∗ gateFrame) (gateState, 0) := by
  refine ptoH_sepConj_iff.2 ⟨?_, rfl⟩
  intro j hj
  have hj2 : j < 2 := by simpa using hj
  interval_cases j <;> rfl

/-- Ownership really does read the state: a heap range at a concrete
state forces the array's contents. -/
example : ∃ ys, gateState.arrs heapName = some ys ∧ ys[1]? = some 6 :=
  ptoH_get (j := 0) gate_range_holds (by simp)

/-- Split and join, at concrete numerals: the range `[1, 3)` is the two
singleton ranges, on the nose. -/
example : (1 ↦ₕ [6, 7]) = ((1 ↦ₕ [6]) ∗ (2 ↦ₕ [7])) := by
  simpa using ptoH_append 1 [6] [7]

/-- **The triples are instantiable.** Both side conditions are
satisfiable at concrete arguments, so neither triple is vacuous by an
unsatisfiable premise: reading offset 1 of the range `1 ↦ₕ [6, 7]`
through the index cell `"i" ↦ᵥ 2` yields `7`… -/
example : irTriple (¤¤Currency.aget 1 ∗ "x" ↦ᵥ 0 ∗ (1 ↦ₕ [6, 7]) ∗ "i" ↦ᵥ 2)
    (.aget "x" heapName "i") ("x" ↦ᵥ 7 ∗ (1 ↦ₕ [6, 7]) ∗ "i" ↦ᵥ 2) :=
  haget_triple "x" "i" 0 1 1 [6, 7] 7 (by simp) rfl

/-- …and writing `9` there leaves the range `1 ↦ₕ [6, 9]`, with the
other offset untouched. -/
example : irTriple (¤¤Currency.aset 1 ∗ (1 ↦ₕ [6, 7]) ∗ "i" ↦ᵥ 2 ∗ "v" ↦ᵥ 9)
    (.aset heapName "i" "v") ((1 ↦ₕ [6, 9]) ∗ "i" ↦ᵥ 2 ∗ "v" ↦ᵥ 9) :=
  haset_triple "i" "v" 1 1 [6, 7] 9 (by simp)

end HeapGate

end Lax13Proofs.Refine.Ir
