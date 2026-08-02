import Lax3Proofs.Refine.BridgeSeamProbe
import Lax3Proofs.Refine.MassMath

/-!
**The arena width, retired from the word bound** — ND-MC rebase, wave
E-mem, retargeted by the seam probe's finding 3.

`Refine.BridgeSeamProbe.no_word_size_for_sparse` (§5 there) shows,
unconditionally, that the landed root theorem cannot cross the
`Spec → ComputesInTime` bridge: the driver's own `RamDriver.WordBound`
pins `n * n + ns + 2 * cap + 2 < B`, `Compile.Layout.FitsWords` pins
`B ≤ 2 ^ w`, and C0's domain admits word lengths at which `2 ^ w` is
only *linear* in `|x|`. The wave was briefed to repair this by replacing
the `n × n` block-membership representation by an almost-linear one.

**The first finding of this file is that the repair is not a change of
representation.** `Compile.Layout.span` is
`temps + scalars.length + arrays.length * B` (§1): the word length sees
the layout's array *count* and the value bound `B`, and it never sees
the length of an IMP+ array. `RamDriver.LevelMem` and
`RamDriver.DepthMem` are length clauses — `("xmem", n * n)`,
`(xmmName j, n * n)` — and they do not reach `FitsWords` at all. The
landed source says so itself: `Lax13Proofs.Transfer.Solves.run` carries
the note "the declared array lengths are chosen per input … and the
compiled program does not represent them at all", and
`Solves.computesInTime`'s only word-length hypothesis is `FitsWords`.
The single route from the `n × n` arena to the word length is therefore
the literal `n * n` inside `WordBound`, which is there because the
passes *form the arena pointer as a value* and every value of the
bounded semantics must be a word.

So the `n * n` term leaves the word bound as soon as the arena pointer
is known to stay almost-linear — with the `n × n` allocation left
exactly where it is. That is what this file compiles:

1. **§1** — the layout's word-length condition is blind to array
   lengths (`span_eq`, with the `12`-cell span of a layout whose IMP+
   array is `10 ^ 12` long).
2. **§2** — `WordBoundK B n K ns cap mb`, the driver's value bound with
   the arena width read at a degree parameter `K` instead of at the
   carrier: `n * K + n + ns + 2 * cap + 2 < B ∧ mb < B`. It is an exact
   generalization, not a weakening: `wordBoundK_pred_iff` says the
   landed `WordBound` *is* `WordBoundK` at `K = n - 1`, and every
   reading the driver takes off `WordBound` (`n_lt`, `succ_lt`,
   `ns_lt`, `mb_lt`, `cover`) is taken off `WordBoundK` too.
3. **§3, the headline** — the flip of finding 3, at C0's own quantifier
   order. For every layout with at least one array and every constant
   profile `(K, cap, mb)` there is a constant `c`, chosen *before* the
   instance, such that at **every** word `x` of C0's domain and every
   word length `w` that domain admits, a value bound `B` exists with
   `L.FitsWords B w ∧ WordBoundK B n K ns cap mb`
   (`word_size_for_encoded`). Finding 3's derivation does not merely
   fail against the new form — the new form is satisfiable everywhere
   the old one is refuted.
4. **§4 — the controls, and they bite.** The same statement is *false*
   for `RamDriver.WordBound` (`no_wordConst_at_square`, discharged from
   the landed `no_word_size_for_sparse`); false when the degree
   parameter is allowed to grow with the instance
   (`no_wordConst_at_linear_degree`); and false when the *layout's array
   count* grows with the instance (`no_wordConst_growing_layout`) — so
   the `span` conjunct is load-bearing and the flip rests on the
   driver's array count being constant in `n`, which it is (the
   per-depth, colour and table arrays are indexed by `ℓ`, `sigL` and
   `tablesAt`, all functions of `φ` and the class).
5. **§5 — the program-side enabling fact.** `RamCover.CoverInv`'s own
   ceiling on the write pointer is `ptr_le : xp ≤ c * n`, the trivial
   `n²`, and it is what the `n * n` in `WordBound` pays for.
   `CoverInv.ptr_le_mass` replaces it: against the *same* invariant,
   with the ordering's weak-reachability degree bounded by `d` — the
   root theorem's own `hdeg` slot — the pointer is at most `n * d` at
   every centre boundary, so the block scan's `xp + n` values are words
   under `WordBoundK` at `K = d` (`block_scan_lt`). The proof is
   `Refine.MassMath`'s double count read over the *prefix* of blocks the
   invariant has built, which is the only new mathematics the retirement
   needs.
6. **§6 — what is still open**, as a named `Prop` with its shape, never
   a `sorry`: `CoverImplementsK` is `RamCover.Implements` with
   `n * n + ns + 2 * r + 2 < B` replaced by `WordBoundK`'s arena clause
   and the degree hypothesis added. `implementsK_of_implements` compiles
   that this is a generalization — the landed obligation gives it at the
   trivial degree bound `d = n` — so re-walking the pass at the sharper
   invariant reading loses nothing.

**Scope, stated exactly.** Finding 3 is a *space* fact and this file is
its repair route; it is not a cost repair. `RamCover.coverCost` is still
`100 * n * n + 50 * n * ns + …`, `RamDriverCompose.coverSaveCost` still
charges `12 * (n * n)` and `RamDriverDescend`'s cluster load `16 * (n * n)`,
because the emission scan and the arena copies still walk the carrier.
Those are the E-order/B7 residue — the member-driven interiors — and
nothing here shortens them. What this file changes is that the residue
is now *only* cost: the bridge is no longer refuted on space grounds.
-/

namespace Lax3Proofs.Refine.ArenaWidth

open Lax11.GraphEncoding
open Lax3Proofs.RamDriver (WordBound)
open Lax3Proofs.Refine.BridgeSeamProbe (emptyWord length_emptyWord mem_emptyWord
  encodesGraph_emptyWord exists_pow_between no_word_size_for_sparse)

/-! ## 1. The word length never sees an array length

`Compile.Layout.FitsWords L B w` has three fields, and the only one that
could carry a memory size is `span : L.span B ≤ 2 ^ w`. `span` is
`temps + scalars.length + arrays.length * B`: the layout interleaves the
arrays, so an array occupies one cell per *value* below `B`, and the
length of the corresponding IMP+ list — `n * n` for `xmem` — occurs
nowhere. -/

section Span

/-- The span, unfolded. Array lengths do not occur. -/
theorem span_eq (L : Lax13Proofs.Compile.Layout) (B : ℕ) :
    L.span B = L.temps + L.scalars.length + L.arrays.length * B := rfl

/-- The layout of one array, at a value bound of `12`. The IMP+ array it
addresses may be `10 ^ 12` cells long — `RamDriver.LevelMem`'s
`("xmem", n * n)` at `n = 10 ^ 6` — and the span is still `12`. -/
def oneArray : Lax13Proofs.Compile.Layout := ⟨[], ["xmem"], 0⟩

#guard oneArray.span 12 = 12

-- and the length clause the driver actually carries is satisfiable at
-- that bound: `arrOf (n * n) g` is a list, not a word.
#guard (Lax13Proofs.Reasoning.arrOf (10 ^ 6) (fun _ => 0)).length = 10 ^ 6

end Span

/-! ## 2. The value bound with the arena width read at a degree

`WordBound B n ns cap mb` is `n * n + ns + 2 * cap + 2 < B ∧ mb < B`.
The `n * n` is the cluster arena's pointer ceiling. `WordBoundK` reads
that ceiling at a degree parameter `K` — `n * K` slots of arena, plus
the `n` slots one block scan may still add — and is otherwise the same
clause. -/

section Bound

variable {B n K ns cap mb : ℕ}

/-- **The new value bound**: the arena pointer at `n * K`, the block
scan's `+ n`, the block structure's `ns`, the search's `2 * cap`, and
the padded width. -/
def WordBoundK (B n K ns cap mb : ℕ) : Prop :=
  n * K + n + ns + 2 * cap + 2 < B ∧ mb < B

/-- The arena ceiling of the old bound is the new one at `K = n - 1`. -/
theorem mul_pred_add_self (n : ℕ) : n * (n - 1) + n = n * n := by
  cases n with
  | zero => rfl
  | succ m => simp [Nat.mul_succ, Nat.mul_comm]

/-- **The slot change is a generalization, not a weakening.** The landed
`WordBound` *is* `WordBoundK` at the trivial degree parameter. -/
theorem wordBoundK_pred_iff : WordBoundK B n (n - 1) ns cap mb ↔ WordBound B n ns cap mb := by
  rw [WordBoundK, RamDriver.WordBound, mul_pred_add_self]

/-- A smaller degree parameter is a weaker demand on `B`. -/
theorem wordBoundK_mono {K' : ℕ} (hK : K ≤ K') (h : WordBoundK B n K' ns cap mb) :
    WordBoundK B n K ns cap mb :=
  ⟨lt_of_le_of_lt (by
    have : n * K ≤ n * K' := Nat.mul_le_mul_left n hK
    omega) h.1, h.2⟩

/-- …so the landed bound gives the new one at every degree parameter
below `n - 1`, which is how a caller who has only `WordBound` still
enters. -/
theorem wordBoundK_of_wordBound (hK : K ≤ n - 1) (h : WordBound B n ns cap mb) :
    WordBoundK B n K ns cap mb :=
  wordBoundK_mono hK (wordBoundK_pred_iff.mpr h)

/-! ### Every reading the driver takes off `WordBound`, taken off
`WordBoundK`

`RamDriver.WordBound` is consumed through five projections. All five are
available from the new form, which is what makes the `hB` slot a *slot*
change: no consumer of the root theorem loses a fact. -/

theorem WordBoundK.one_lt (h : WordBoundK B n K ns cap mb) : 1 < B := by
  rw [WordBoundK] at h; omega

theorem WordBoundK.n_lt (h : WordBoundK B n K ns cap mb) : n < B := by
  rw [WordBoundK] at h; omega

theorem WordBoundK.succ_lt (h : WordBoundK B n K ns cap mb) : n + 1 < B := by
  rw [WordBoundK] at h; omega

theorem WordBoundK.ns_lt (h : WordBoundK B n K ns cap mb) : ns < B := by
  rw [WordBoundK] at h; omega

theorem WordBoundK.mb_lt (h : WordBoundK B n K ns cap mb) : mb < B := h.2

/-- The arena reading: every pointer the cover pass forms, including the
`n` slots of the block being scanned, is a word. -/
theorem WordBoundK.arena (h : WordBoundK B n K ns cap mb) :
    n * K + n + ns + 2 * cap + 2 < B := h.1

end Bound

/-! ## 3. The flip of finding 3

C0 fixes its constant `c` before the instance:

```
∃ p c T, … ∧ ∀ n G w, C n G → ComputesInTime w p
  {x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w} … T
```

so the statement to prove is: **one** `c`, then every `n`, `w` and every
member `x` of the domain, then a value bound. `wordConst` is that
constant, read off the layout and the constant profile; the theorem is
that it works everywhere. -/

section Flip

open Lax13Proofs.Compile (Layout)

/-- The constant C0's domain condition is stated with: the layout's
array count against the arena width and the search's parameters, plus
the layout's scalar block. -/
def wordConst (L : Layout) (K cap mb : ℕ) : ℕ :=
  L.arrays.length * (K + 2 * cap + mb + 4) + L.temps + L.scalars.length + 1

theorem wordConst_pos (L : Layout) (K cap mb : ℕ) : 0 < wordConst L K cap mb := by
  rw [wordConst]; omega

/-- The value bound the flip produces: linear in the length of the word.
-/
def boundAt (len K cap mb : ℕ) : ℕ := len * (K + 1) + 2 * cap + mb + 3

/-- **The headline.** At C0's own quantifier order: for every layout
with an array and every constant profile, the constant `wordConst`
admits, at every word of C0's domain and every word length that domain
allows, a value bound satisfying both the compile layout's fits-words
condition and the driver's arena bound at width `n * K`.

This is the exact negation of finding 3's shape. Nothing about the
graph, the class or the cost interface enters; the only input is that
the arena pointer is charged at `n * K` rather than at `n * n`. -/
theorem word_size_for_encoded (L : Layout) (hA : 1 ≤ L.arrays.length) (K cap mb : ℕ)
    {n ns w : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hdom : ∀ v ∈ x, wordConst L K cap mb * (x.length + v + 1) ≤ 2 ^ w) :
    ∃ B, L.FitsWords B w ∧ WordBoundK B n K ns cap mb := by
  -- the word's shape: `|x| = 3 + n + ns`
  have hlen3 : x.length = 3 + n + ns := by rw [hx.length_eq, hns]
  -- the domain condition at the word's first entry
  have hdom1 : wordConst L K cap mb * (x.length + 1) ≤ 2 ^ w := by
    obtain ⟨v, hv⟩ : ∃ v, v ∈ x := by
      cases x with
      | nil => simp only [List.length_nil] at hlen3; exact absurd hlen3 (by omega)
      | cons v t => exact ⟨v, by simp⟩
    exact le_trans (Nat.mul_le_mul_left _ (by omega)) (hdom v hv)
  set c := wordConst L K cap mb with hc
  set len := x.length with hlen
  set A := L.arrays.length with hAdef
  set S := L.temps + L.scalars.length with hS
  set E := K + 2 * cap + mb + 4 with hE
  refine ⟨boundAt len K cap mb, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [boundAt]; omega
  -- `B ≤ len * E ≤ A * E * len ≤ c * (len + 1) ≤ 2 ^ w`
  · refine le_trans ?_ hdom1
    rw [boundAt]
    have h1 : 2 * cap + mb + 3 ≤ len * (2 * cap + mb + 3) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h2 : len * (K + 1) + len * (2 * cap + mb + 3) = len * E := by rw [hE]; ring
    have h3 : len * E ≤ A * (E * len) := by
      rw [Nat.mul_comm len E]
      exact Nat.le_mul_of_pos_left _ (by omega)
    have h4 : A * (E * len) ≤ c * (len + 1) := by
      rw [hc, wordConst, ← hAdef, ← hE]
      have : A * (E * len) = A * E * len := by ring
      rw [this]
      calc A * E * len ≤ (A * E + L.temps + L.scalars.length + 1) * len :=
            Nat.mul_le_mul_right len (by omega)
        _ ≤ (A * E + L.temps + L.scalars.length + 1) * (len + 1) :=
            Nat.mul_le_mul_left _ (by omega)
    omega
  -- the span: `S + A * B ≤ S + A * E * len ≤ c * (len + 1) ≤ 2 ^ w`
  · refine le_trans ?_ hdom1
    rw [Lax13Proofs.Compile.Layout.span, ← hAdef, boundAt]
    have h1 : 2 * cap + mb + 3 ≤ len * (2 * cap + mb + 3) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h2 : len * (K + 1) + len * (2 * cap + mb + 3) = len * E := by rw [hE]; ring
    have hBle : len * (K + 1) + 2 * cap + mb + 3 ≤ len * E := by omega
    have h3 : A * (len * (K + 1) + 2 * cap + mb + 3) ≤ A * (len * E) :=
      Nat.mul_le_mul_left A hBle
    have h4 : L.temps + L.scalars.length + A * (len * E) ≤ c * (len + 1) := by
      rw [hc, wordConst, ← hAdef, ← hE]
      have hmul : A * (len * E) = A * E * len := by ring
      rw [hmul]
      calc L.temps + L.scalars.length + A * E * len
          ≤ (A * E + L.temps + L.scalars.length + 1) * len
              + (L.temps + L.scalars.length + 1) := by
            have : (A * E + L.temps + L.scalars.length + 1) * len
                = A * E * len + (L.temps + L.scalars.length + 1) * len := by ring
            rw [this]
            have : 0 ≤ (L.temps + L.scalars.length + 1) * len := Nat.zero_le _
            omega
        _ ≤ (A * E + L.temps + L.scalars.length + 1) * (len + 1) := by
            have : (A * E + L.temps + L.scalars.length + 1) * (len + 1)
                = (A * E + L.temps + L.scalars.length + 1) * len
                  + (A * E + L.temps + L.scalars.length + 1) := by ring
            omega
    have hS' : L.temps + L.scalars.length
        + A * (len * (K + 1) + 2 * cap + mb + 3) ≤ c * (len + 1) := by omega
    omega
  -- the arena clause: `n * K + n ≤ len * (K + 1)`
  · rw [boundAt]
    have h1 : n * K ≤ len * K := Nat.mul_le_mul_right K (by omega)
    have h2 : len * K + len = len * (K + 1) := by ring
    omega
  · rw [boundAt]; omega

/-- The same, packaged with the constant existentially quantified, in
C0's own shape: `c` before `n`, `w` and `x`. -/
theorem exists_wordConst (L : Layout) (hA : 1 ≤ L.arrays.length) (K cap mb : ℕ) :
    ∃ c : ℕ, 0 < c ∧ ∀ (n ns w : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
      EncodesGraph x n G → ns = 2 * edgeCount x →
      (∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w) →
      ∃ B, L.FitsWords B w ∧ WordBoundK B n K ns cap mb :=
  ⟨wordConst L K cap mb, wordConst_pos L K cap mb,
    fun _ _ _ _ _ hx hns hdom => word_size_for_encoded L hA K cap mb hx hns hdom⟩

end Flip

/-! ## 4. The controls, and they bite

Three refutations, each of the *same* statement §3 proves, with one
ingredient changed: the arena width, the degree parameter's dependence
on the instance, and the layout's array count. -/

section Controls

open Lax13Proofs.Compile (Layout)

/-- **Control 1 — the width is what does the work.** With
`RamDriver.WordBound` in place of `WordBoundK`, no constant works: this
is finding 3, restated in §3's shape and discharged from the landed
`no_word_size_for_sparse`. -/
theorem no_wordConst_at_square (L : Layout) (cap mb : ℕ) :
    ¬ ∃ c : ℕ, 0 < c ∧ ∀ (n ns w : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
      EncodesGraph x n G → ns = 2 * edgeCount x →
      (∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w) →
      ∃ B, L.FitsWords B w ∧ WordBound B n ns cap mb := by
  rintro ⟨c, hc, h⟩
  set n := 8 * c + 16 with hn
  have hcross : 4 * c * (n + 2) ≤ n * n := by rw [hn]; nlinarith
  obtain ⟨w, -, hdom, hkill⟩ := no_word_size_for_sparse c n hc hcross
  obtain ⟨B, hfit, hwb⟩ := h n 0 w (⊥ : SimpleGraph (Fin n)) (emptyWord n)
    (encodesGraph_emptyWord n) (by rw [show edgeCount (emptyWord n) = 0 from rfl]) hdom
  exact hkill L B 0 cap mb hfit hwb

/-- **Control 2 — the degree parameter must be a constant of the class,
not of the instance.** If it is allowed to grow with `n`, the new bound
is the old one again and the same refutation applies. -/
theorem no_wordConst_at_linear_degree (L : Layout) (cap mb : ℕ) :
    ¬ ∃ c : ℕ, 0 < c ∧ ∀ (n ns w : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
      EncodesGraph x n G → ns = 2 * edgeCount x →
      (∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w) →
      ∃ B, L.FitsWords B w ∧ WordBoundK B n n ns cap mb := by
  rintro ⟨c, hc, h⟩
  refine no_wordConst_at_square L cap mb ⟨c, hc, fun n ns w G x hx hns hdom => ?_⟩
  obtain ⟨B, hfit, hwb⟩ := h n ns w G x hx hns hdom
  refine ⟨B, hfit, ?_, hwb.2⟩
  have := hwb.1
  omega

/-- A layout whose array count grows with the instance. -/
def bigLayout (n : ℕ) : Layout := ⟨[], List.replicate n "a", 0⟩

@[simp] theorem bigLayout_arrays_length (n : ℕ) : (bigLayout n).arrays.length = n := by
  simp [bigLayout]

/-- The tight word length: C0's domain admits it, and it is at most
`4 * c * (n + 2)`. -/
theorem exists_w_tight (c n : ℕ) (hc : 0 < c) :
    ∃ w : ℕ, (∀ v ∈ emptyWord n, c * ((emptyWord n).length + v + 1) ≤ 2 ^ w) ∧
      2 ^ w ≤ 4 * c * (n + 2) := by
  obtain ⟨w, hw1, hw2⟩ := exists_pow_between (m := c * (2 * n + 4)) (by positivity)
  refine ⟨w, ?_, ?_⟩
  · intro v hv
    refine le_trans ?_ hw1
    rw [length_emptyWord]
    rcases mem_emptyWord hv with rfl | rfl <;> exact Nat.mul_le_mul_left c (by omega)
  · calc 2 ^ w ≤ 2 * (c * (2 * n + 4)) := hw2
      _ = 4 * c * (n + 2) := by ring

/-- **Control 3 — the `span` conjunct bites, and the flip rests on the
layout's array count being constant in the instance.** With an array
count that grows like `n`, no constant works even at the almost-linear
arena width: `span B = n * B` is quadratic again. (The driver's own
count is constant in `n` — the per-depth, colour and table arrays are
indexed by `ℓ`, `sigL cap mb j` and `tablesAt q_top cap mb φ j`, all
functions of the sentence and the class; that reading is an observation
about the driver's names and is not compiled here.) -/
theorem no_wordConst_growing_layout (K cap mb : ℕ) :
    ¬ ∃ c : ℕ, 0 < c ∧ ∀ (n ns w : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
      EncodesGraph x n G → ns = 2 * edgeCount x →
      (∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w) →
      ∃ B, (bigLayout n).FitsWords B w ∧ WordBoundK B n K ns cap mb := by
  rintro ⟨c, hc, h⟩
  set n := 8 * c + 16 with hn
  have hcross : 4 * c * (n + 2) ≤ n * n := by rw [hn]; nlinarith
  have hnpos : 0 < n := by omega
  obtain ⟨w, hdom, hw2⟩ := exists_w_tight c n hc
  obtain ⟨B, hfit, hwb⟩ := h n 0 w (⊥ : SimpleGraph (Fin n)) (emptyWord n)
    (encodesGraph_emptyWord n) (by rw [show edgeCount (emptyWord n) = 0 from rfl]) hdom
  have hnB : n < B := by have := hwb.1; omega
  have hspan := hfit.span
  rw [Lax13Proofs.Compile.Layout.span, bigLayout_arrays_length] at hspan
  have hsq : n * n < n * B := mul_lt_mul_of_pos_left hnB hnpos
  have hbig : n * n < 2 ^ w := by
    have : n * B ≤ 2 ^ w := by simpa [bigLayout] using hspan
    omega
  omega

/-- **The flip, at the refuting instance itself.** One `n`, one word,
one word length: the very `w` at which `no_word_size_for_sparse` refutes
the landed `WordBound` for *every* value bound admits a value bound for
`WordBoundK`. The two halves are read off the same C0 domain membership,
so this is not two different scopes compared — it is the same seam,
before and after the arena width leaves. -/
theorem flip_at_the_refuting_instance (L : Layout) (hA : 1 ≤ L.arrays.length)
    (K cap mb n : ℕ) (hcross : 4 * wordConst L K cap mb * (n + 2) ≤ n * n) :
    ∃ w : ℕ,
      (∀ B ns' cap' mb' : ℕ, L.FitsWords B w → ¬ WordBound B n ns' cap' mb') ∧
      (∃ B, L.FitsWords B w ∧ WordBoundK B n K 0 cap mb) := by
  obtain ⟨w, -, hdom, hkill⟩ :=
    no_word_size_for_sparse (wordConst L K cap mb) n (wordConst_pos L K cap mb) hcross
  exact ⟨w, fun B ns' cap' mb' hfit => hkill L B ns' cap' mb' hfit,
    word_size_for_encoded L hA K cap mb (G := (⊥ : SimpleGraph (Fin n)))
      (encodesGraph_emptyWord n) (by rw [show edgeCount (emptyWord n) = 0 from rfl]) hdom⟩

-- **the crossover is inhabited at a realistic profile**: one array,
-- degree bound `8`, radius cap `2`, padded width `10` — constant `27`,
-- and the refuting instance starts at `n = 200`.
#guard wordConst oneArray 8 2 10 = 27
#guard 4 * 27 * (200 + 2) ≤ 200 * 200
-- and the flip's own arena clause at that instance, at the value bound
-- `boundAt |x| K cap mb` for the edgeless word (`|x| = 203`):
-- `200 * 8 + 200 + 0 + 4 + 2 = 1806 < 1844`
#guard boundAt 203 8 2 10 = 1844
#guard 200 * 8 + 200 + 0 + 2 * 2 + 2 < boundAt 203 8 2 10
-- **the old bound at the same value bound**: `200 * 200 = 40000`
#guard ¬ (200 * 200 + 0 + 2 * 2 + 2 < boundAt 203 8 2 10)

/-! ### The numeric instance

The flip, at numerals, with both conditions evaluated — and the old
bound refuted at the *same* value bound, so the numbers are not
accidentally generous. Layout: two arrays, no scalars, no temps
(`A = 2`, `S = 0`); profile `K = 3`, `cap = 1`, `mb = 5`; instance
`n = 10`, `ns = 4`, `|x| = 17`, entries at most `10`. -/

#guard wordConst ⟨[], ["a", "b"], 0⟩ 3 1 5 = 29
#guard boundAt 17 3 1 5 = 78

-- C0's domain condition holds at `w = 10` for every entry of the word
#guard (List.range 11).all fun v => 29 * (17 + v + 1) ≤ 2 ^ 10
-- `FitsWords 78 10`: `1 < 78`, `78 ≤ 1024`, span `2 * 78 = 156 ≤ 1024`
#guard 1 < 78 && 78 ≤ 2 ^ 10 && (⟨[], ["a", "b"], 0⟩ : Layout).span 78 ≤ 2 ^ 10
-- `WordBoundK 78 10 3 4 1 5`: `10 * 3 + 10 + 4 + 2 + 2 = 48 < 78`, `5 < 78`
#guard 10 * 3 + 10 + 4 + 2 * 1 + 2 < 78 && 5 < 78
-- **and the old bound fails at the same value bound**: `100 + 4 + 2 + 2 = 108`
#guard ¬ (10 * 10 + 4 + 2 * 1 + 2 < 78)

end Controls

/-! ## 5. The program-side enabling fact: the arena pointer is
almost-linear at every centre boundary

`RamCover.CoverInv.ptr_le` is `xp ≤ c * n` — the trivial `n²`, and the
reason `WordBound` carries `n * n`. The invariant already carries
everything a sharper ceiling needs: `block` and `block_inj` for every
block below the current centre, `mono` and `zero` for the offsets, and
`ptr` for the pointer itself. Reading `Refine.MassMath`'s double count
over that *prefix* gives `xp ≤ n * d` with `d` the ordering's weak
reachability degree — which is the root theorem's own `hdeg` slot. -/

section Pointer

open Finset
open Lax12.ColoringNumbers (wreach)
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamCover
open Lax3Proofs.Refine.MassMath (blockSize clusterAt coverFam)

variable {n : ℕ} {G : SimpleGraph (Fin n)} {A₀ ord Xoff Xmem asg M : ℕ → ℕ}
  {π : Equiv.Perm (Fin n)} {r c xp d : ℕ}

/-- The blocks the invariant has built tile the arena below the write
pointer. -/
theorem sum_blockSize_inv (hI : CoverInv G A₀ π ord r c xp Xoff Xmem asg M) :
    ∀ k ≤ c, ∑ c' ∈ range k, blockSize Xoff c' = Xoff k := by
  intro k hk
  induction k with
  | zero => simp [blockSize, hI.zero]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih (by omega), blockSize]
      have := hI.mono k (by omega)
      omega

/-- **A built block's size is its cluster's size** — `MassMath`'s
`blockSize_eq_ncard`, read off the invariant rather than off the exit
condition, so it is available *during* the pass. -/
theorem blockSize_eq_ncard_inv (hI : CoverInv G A₀ π ord r c xp Xoff Xmem asg M)
    {c' : ℕ} (hc' : c' < c) :
    blockSize Xoff c' = (clusterAt G A₀ π ord r c').ncard := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (lt_of_lt_of_le hc' hI.pos_le) (by omega)
    · exact h
  have hbound : Xoff (c' + 1) ≤ xp := by
    rw [← hI.ptr]; exact hI.mono' (by omega) le_rfl
  have hlt : ∀ p ∈ Finset.Ico (Xoff c') (Xoff (c' + 1)), Xmem p < n := by
    intro p hp
    rw [Finset.mem_Ico] at hp
    exact hI.mem_lt p (lt_of_lt_of_le hp.2 hbound)
  set f : ℕ → Fin n := fun p => ⟨Xmem p % n, Nat.mod_lt _ hn⟩ with hf
  have hfval : ∀ p ∈ Finset.Ico (Xoff c') (Xoff (c' + 1)), ((f p : Fin n) : ℕ) = Xmem p :=
    fun p hp => Nat.mod_eq_of_lt (hlt p hp)
  have hinj' : Set.InjOn f ↑(Finset.Ico (Xoff c') (Xoff (c' + 1))) := by
    intro p hp q hq hpq
    have hp' := Finset.mem_Ico.mp (Finset.mem_coe.mp hp)
    have hq' := Finset.mem_Ico.mp (Finset.mem_coe.mp hq)
    have hval : Xmem p = Xmem q := by
      rw [← hfval p (Finset.mem_coe.mp hp), ← hfval q (Finset.mem_coe.mp hq), hpq]
    exact hI.block_inj c' hc' p q hp'.1 hp'.2 hq'.1 hq'.2 hval
  have himg : clusterAt G A₀ π ord r c' = f '' ↑(Finset.Ico (Xoff c') (Xoff (c' + 1))) := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp1, hp2, hp3⟩ := (hI.block c' hc' (z : ℕ)).mpr hz
      have hmem : p ∈ Finset.Ico (Xoff c') (Xoff (c' + 1)) := Finset.mem_Ico.mpr ⟨hp1, hp2⟩
      exact ⟨p, Finset.mem_coe.mpr hmem, Fin.ext (by rw [hfval p hmem, hp3])⟩
    · rintro ⟨p, hp, rfl⟩
      have hmem := Finset.mem_coe.mp hp
      have hmem' := Finset.mem_Ico.mp hmem
      show InCluster (masked G A₀) π r (ord c') ((f p : Fin n) : ℕ)
      rw [hfval p hmem]
      exact (hI.block c' hc' (Xmem p)).mp ⟨p, hmem'.1, hmem'.2, rfl⟩
  rw [himg, Set.InjOn.ncard_image hinj', Set.ncard_coe_finset, Nat.card_Ico, blockSize]

/-- The cover family's total size, against the carrier: `MassMath`'s
double count with the support taken to be everything. -/
theorem sum_coverFam_le (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d) :
    ∑ u : Fin n, (coverFam G A₀ π r u).ncard ≤ n * d := by
  classical
  have hdeg : ∀ w : Fin n, {u : Fin n | w ∈ coverFam G A₀ π r u}.ncard ≤ d := by
    intro w
    have : {u : Fin n | w ∈ coverFam G A₀ π r u} = wreach (masked G A₀) π (2 * r) w := by
      ext u; exact Iff.rfl
    rw [this]; exact hk w
  have huniv : (Set.univ : Set (Fin n)).ncard = n := by simp
  have := CoverDegree.sum_ncard_le_mul_of_subset (coverFam G A₀ π r) Set.univ d
    (fun _ => Set.subset_univ _) hdeg
  rwa [huniv] at this

/-- **The replacement for `CoverInv.ptr_le`.** At every centre boundary
of the cover pass the write pointer is at most `n * d`, with `d` the
ordering's weak `2r`-reachability degree — the root theorem's `hdeg`
slot verbatim. The landed clause `ptr_le : xp ≤ c * n` is the `n = d`
case and is what the `n * n` in `WordBound` pays for; this is the same
fact at the sharp constant. -/
theorem ptr_le_mass (hord : OrdersBy n π ord)
    (hI : CoverInv G A₀ π ord r c xp Xoff Xmem asg M)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d) :
    xp ≤ n * d := by
  classical
  have hsum : xp = ∑ c' ∈ range c, (clusterAt G A₀ π ord r c').ncard := by
    rw [← hI.ptr, ← sum_blockSize_inv hI c le_rfl]
    exact Finset.sum_congr rfl fun c' hc' => blockSize_eq_ncard_inv hI (mem_range.mp hc')
  have hsub : range c ⊆ range n := by
    intro y hy
    rw [Finset.mem_range] at hy ⊢
    exact lt_of_lt_of_le hy hI.pos_le
  have hmono : ∑ c' ∈ range c, (clusterAt G A₀ π ord r c').ncard
      ≤ ∑ c' ∈ range n, (clusterAt G A₀ π ord r c').ncard :=
    Finset.sum_le_sum_of_subset hsub
  rw [hsum]
  exact le_trans hmono
    (le_trans (le_of_eq (Refine.MassMath.sum_clusterAt_eq hord)) (sum_coverFam_le hk))

/-- **What the new slot buys the block scan.** `RamDriverOrder`'s
emission scan starts at the pointer and may add one slot per carrier
vertex, so the widest value it forms is `xp + n`; under `WordBoundK` at
`K = d` that is a word. This is the inequality the `n * n < B` reading
is replaced by, and it is where §5 meets §2. -/
theorem block_scan_lt {B ns cap mb : ℕ} (hord : OrdersBy n π ord)
    (hI : CoverInv G A₀ π ord r c xp Xoff Xmem asg M)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d)
    (hB : WordBoundK B n d ns cap mb) : xp + n < B := by
  have := ptr_le_mass hord hI hk
  have := hB.1
  omega

end Pointer

/-! ## 6. What is still open, named

The retirement is one obligation: the cover pass re-walked so that its
value bound is the arena's rather than the carrier's. §5 supplies the
mathematics — the invariant's own clauses give the sharp pointer
ceiling — and what remains is symbolic execution of the same text
against the sharper reading, which is a program wave and is not done
here. It is stated as a `Prop`, never a `sorry`. -/

section Open

open Lax3Proofs.RamCover
open Lax12.ColoringNumbers (wreach)
open Lax3Proofs.RamBfs (masked)

/-- **The open obligation**: `RamCover.Implements` with the carrier
value bound `n * n + ns + 2 * r + 2 < B` replaced by the arena bound at
the ordering's degree, and the degree hypothesis — which the driver
already holds at the root's `hdeg` slot — added.

The obstruction is recorded rather than worked around: the landed walk
discharges the array-range and word obligations of the emission scan
from `CoverInv.ptr_le : xp ≤ c * n`, and re-walking them from
`ptr_le_mass` touches every pass of `centreStep`. The *allocation* does
not move — `RamDriver.LevelMem`'s `("xmem", n * n)` and
`RamDriver.DepthMem`'s `(xmmName j, n * n)` stay exactly as they are,
because §1 shows the word length never reads an array length. -/
def CoverImplementsK (B n ns d : ℕ) (G : SimpleGraph (Fin n)) (A₀ O T ord : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (r : ℕ) : Prop :=
  RamBfs.CsrGraph G ns O T → OrdersBy n π ord →
    n * d + n + ns + 2 * r + 2 < B →
    (∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d) →
    (∀ z < n, A₀ z < B) →
    Lax13Proofs.Reasoning.Spec B
      (fun σ => CoverState B G A₀ π ns O T ord r σ ∧ σ.vars "c" < n) (centreStep r)
      (fun σ σ' => CoverState B G A₀ π ns O T ord r σ' ∧ σ'.vars "c" = σ.vars "c" + 1)
      (centreCost n ns)

/-- **The obligation is a generalization, not a weakening.** At the
trivial degree parameter `d = n` — where the degree hypothesis is free,
since a weakly reachable set is a set of vertices — the landed
obligation gives it. So the slot change costs no landed capital: what
the re-walk must add is exactly the sharp reading, at a `d` below `n`.
-/
theorem coverImplementsK_of_implements {B n ns : ℕ} {G : SimpleGraph (Fin n)}
    {A₀ O T ord : ℕ → ℕ} {π : Equiv.Perm (Fin n)} {r : ℕ}
    (h : Implements B n ns G A₀ O T ord π r) :
    CoverImplementsK B n ns n G A₀ O T ord π r :=
  fun hcsr hord hB _ hA => h hcsr hord (by omega) hA

end Open

/-! ## 7. The axiom check -/

#print axioms wordBoundK_pred_iff
#print axioms word_size_for_encoded
#print axioms exists_wordConst
#print axioms flip_at_the_refuting_instance
#print axioms no_wordConst_at_square
#print axioms no_wordConst_at_linear_degree
#print axioms no_wordConst_growing_layout
#print axioms ptr_le_mass
#print axioms block_scan_lt
#print axioms coverImplementsK_of_implements

end Lax3Proofs.Refine.ArenaWidth
