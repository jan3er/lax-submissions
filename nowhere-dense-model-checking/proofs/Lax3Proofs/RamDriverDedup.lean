import Mathlib.Data.List.GetD
import Lax3Proofs.RamDriverIO
import Lax3Proofs.C0Probe
import Lax3Proofs.TgtWidenProbe

/-!
**The dedup guard (rebase G1): a `CsrSimple` block structure out of an
`EncodesGraph` word.**

`Lax3Proofs.C0Probe`'s first finding is that the encoding surface and
the root theorem's slot `#6` do not meet: `Lax11.GraphEncoding`
*deliberately* permits a block to name a neighbour twice
(`C0Probe.dupWord` is such a word for `K₂`), while
`Lax3Proofs.RamElim.CsrSimple` — what the two eliminations of the
ordering phase read a degree off — forbids exactly that. So `CsrSimple`
cannot be assumed at the C0 boundary, where the input predicate is
`EncodesGraph` alone.

This file is the repair: a pass that runs *after* the decode and
compacts every row to its first occurrences.

§1 is the arithmetic of the compaction on the word — `firstDedup` on
lists, the row lists it is applied to, and the three functions
`dedupOffset`, `dedupTarget`, `dedupNs` that the compacted block
structure is. The headlines are `csrGraph_dedup` (the compaction is
still a block structure for the same graph) and `csrSimple_dedup` (and
now a simple one), plus `dedupNs_even` — the compacted slot count is
twice the edge count, which is what lets the machine's `"m"` be handed
back in the shape the driver's calling convention wants.

Nothing here restates the root theorem, and no existing file is
touched.
-/

namespace Lax3Proofs.RamDriverDedup

open Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## §1a First-occurrence dedup on lists

`List.dedup` keeps the *last* occurrence of each entry (it is
`pwFilter` from the right), and a compaction whose write pointer never
passes its read pointer keeps the *first*. So the list-level operation
is defined here rather than imported, and it is defined with the *seen
set* carried along — the machine's mark array read as a list, so that
the inner loop's invariant is one equation about this function. -/

/-- Keep the first occurrence of every entry not already in `seen`. -/
def firstDedupAux (seen : List ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: l => if a ∈ seen then firstDedupAux seen l else a :: firstDedupAux (a :: seen) l

/-- Keep the first occurrence of every entry, in order. -/
def firstDedup (l : List ℕ) : List ℕ := firstDedupAux [] l

@[simp] theorem firstDedupAux_nil (seen : List ℕ) : firstDedupAux seen [] = [] := rfl

theorem firstDedupAux_cons (seen : List ℕ) (a : ℕ) (l : List ℕ) :
    firstDedupAux seen (a :: l) =
      if a ∈ seen then firstDedupAux seen l else a :: firstDedupAux (a :: seen) l := rfl

@[simp] theorem firstDedup_nil : firstDedup [] = [] := rfl

/-- Dedup keeps exactly what the list names and the seen set does not. -/
theorem mem_firstDedupAux {v : ℕ} :
    ∀ (l seen : List ℕ), v ∈ firstDedupAux seen l ↔ v ∈ l ∧ v ∉ seen := by
  intro l
  induction l with
  | nil => intro seen; simp
  | cons a t ih =>
    intro seen
    rw [firstDedupAux_cons]
    by_cases ha : a ∈ seen
    · rw [if_pos ha, ih seen, List.mem_cons]
      constructor
      · rintro ⟨h₁, h₂⟩; exact ⟨Or.inr h₁, h₂⟩
      · rintro ⟨h₁ | h₁, h₂⟩
        · exact absurd (h₁ ▸ ha) h₂
        · exact ⟨h₁, h₂⟩
    · rw [if_neg ha, List.mem_cons, ih (a :: seen), List.mem_cons, List.mem_cons]
      constructor
      · rintro (rfl | ⟨h₁, h₂⟩)
        · exact ⟨Or.inl rfl, ha⟩
        · exact ⟨Or.inr h₁, fun h => h₂ (Or.inr h)⟩
      · rintro ⟨h₁ | h₁, h₂⟩
        · exact Or.inl h₁
        · by_cases hv : v = a
          · exact Or.inl hv
          · exact Or.inr ⟨h₁, by simp [hv, h₂]⟩

theorem mem_firstDedup {v : ℕ} {l : List ℕ} : v ∈ firstDedup l ↔ v ∈ l := by
  rw [firstDedup, mem_firstDedupAux]; simp

/-- Dedup leaves no entry twice. -/
theorem nodup_firstDedupAux : ∀ (l seen : List ℕ), (firstDedupAux seen l).Nodup := by
  intro l
  induction l with
  | nil => intro seen; simp
  | cons a t ih =>
    intro seen
    rw [firstDedupAux_cons]
    by_cases ha : a ∈ seen
    · rw [if_pos ha]; exact ih seen
    · rw [if_neg ha, List.nodup_cons]
      refine ⟨fun h => ?_, ih (a :: seen)⟩
      exact (mem_firstDedupAux t (a :: seen)).1 h |>.2 (List.mem_cons_self ..)

theorem nodup_firstDedup (l : List ℕ) : (firstDedup l).Nodup := nodup_firstDedupAux l []

/-- Dedup does not lengthen. -/
theorem length_firstDedupAux_le : ∀ (l seen : List ℕ),
    (firstDedupAux seen l).length ≤ l.length := by
  intro l
  induction l with
  | nil => intro seen; simp
  | cons a t ih =>
    intro seen
    rw [firstDedupAux_cons]
    by_cases ha : a ∈ seen
    · rw [if_pos ha]; exact le_trans (ih seen) (by simp)
    · rw [if_neg ha]; simpa using ih (a :: seen)

theorem length_firstDedup_le (l : List ℕ) : (firstDedup l).length ≤ l.length :=
  length_firstDedupAux_le l []

/-- **The step the machine takes**: one more entry either was already
named — and the compaction skips it — or is new, and the compaction
appends it. This is the whole of the pass's inner loop, on the list
side. -/
theorem firstDedupAux_concat (v : ℕ) :
    ∀ (l seen : List ℕ), firstDedupAux seen (l ++ [v]) =
      if v ∈ seen ∨ v ∈ l then firstDedupAux seen l
      else firstDedupAux seen l ++ [v] := by
  intro l
  induction l with
  | nil =>
    intro seen
    by_cases hv : v ∈ seen <;> simp [firstDedupAux_cons, hv]
  | cons a t ih =>
    intro seen
    rw [List.cons_append, firstDedupAux_cons, firstDedupAux_cons]
    by_cases ha : a ∈ seen
    · rw [if_pos ha, if_pos ha, ih seen]
      by_cases hv : v ∈ seen ∨ v ∈ t
      · rw [if_pos hv, if_pos (by tauto)]
      · have hva : v ≠ a := by rintro rfl; exact hv (Or.inl ha)
        rw [if_neg hv, if_neg (by simp only [List.mem_cons]; tauto)]
    · rw [if_neg ha, if_neg ha, ih (a :: seen)]
      by_cases hv : v ∈ (a :: seen) ∨ v ∈ t
      · rw [if_pos hv, if_pos (by simp only [List.mem_cons] at hv ⊢; tauto)]
      · rw [if_neg hv, if_neg (by simp only [List.mem_cons] at hv ⊢; tauto),
          List.cons_append]

theorem firstDedup_concat (l : List ℕ) (v : ℕ) :
    firstDedup (l ++ [v]) =
      if v ∈ l then firstDedup l else firstDedup l ++ [v] := by
  rw [firstDedup, firstDedup, firstDedupAux_concat]
  simp

/-! ## §1b The rows of a word, and the compacted block structure -/

/-- The targets of the slots `[a, b)`. -/
def slotList (T : ℕ → ℕ) (a b : ℕ) : List ℕ := (List.range' a (b - a)).map T

@[simp] theorem length_slotList (T : ℕ → ℕ) (a b : ℕ) :
    (slotList T a b).length = b - a := by simp [slotList]

theorem mem_slotList {T : ℕ → ℕ} {a b v : ℕ} :
    v ∈ slotList T a b ↔ ∃ j, a ≤ j ∧ j < b ∧ T j = v := by
  simp only [slotList, List.mem_map, List.mem_range']
  constructor
  · rintro ⟨j, ⟨i, hi, rfl⟩, h₃⟩; exact ⟨a + 1 * i, by omega, by omega, h₃⟩
  · rintro ⟨j, h₁, h₂, h₃⟩; exact ⟨j, ⟨j - a, by omega, by omega⟩, h₃⟩

theorem slotList_concat {T : ℕ → ℕ} {a b : ℕ} (hab : a ≤ b) :
    slotList T a (b + 1) = slotList T a b ++ [T b] := by
  have h : b + 1 - a = (b - a) + 1 := by omega
  have hb : a + 1 * (b - a) = b := by omega
  rw [slotList, slotList, h, List.range'_concat, hb]
  simp

theorem getD_slotList {T : ℕ → ℕ} {a b j : ℕ} (hj : j < b - a) :
    (slotList T a b).getD j 0 = T (a + j) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp [slotList]

/-- Row `u` of the word: the targets of its block. -/
def rowList (x : List ℕ) (u : ℕ) : List ℕ :=
  slotList (target x) (offset x u) (offset x (u + 1))

/-- Row `u` compacted. -/
def keepList (x : List ℕ) (u : ℕ) : List ℕ := firstDedup (rowList x u)

theorem nodup_keepList (x : List ℕ) (u : ℕ) : (keepList x u).Nodup :=
  nodup_firstDedup _

theorem mem_keepList {x : List ℕ} {u v : ℕ} :
    v ∈ keepList x u ↔ ∃ j, offset x u ≤ j ∧ j < offset x (u + 1) ∧ target x j = v := by
  rw [keepList, mem_firstDedup, rowList, mem_slotList]

theorem length_keepList_le (x : List ℕ) (u : ℕ) :
    (keepList x u).length ≤ offset x (u + 1) - offset x u := by
  rw [keepList, ← length_slotList (target x) (offset x u) (offset x (u + 1))]
  exact length_firstDedup_le _

/-- The compacted target array of the first `k` rows. -/
def keepUpto (x : List ℕ) (k : ℕ) : List ℕ :=
  ((List.range k).map (keepList x)).flatten

@[simp] theorem keepUpto_zero (x : List ℕ) : keepUpto x 0 = [] := by simp [keepUpto]

theorem keepUpto_succ (x : List ℕ) (k : ℕ) :
    keepUpto x (k + 1) = keepUpto x k ++ keepList x k := by
  simp [keepUpto, List.range_succ]

theorem keepUpto_prefix (x : List ℕ) {k m : ℕ} (h : k ≤ m) :
    ∃ s, keepUpto x m = keepUpto x k ++ s := by
  induction m with
  | zero => exact ⟨[], by simp [Nat.le_zero.1 h]⟩
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hk | hk
    · obtain ⟨s, hs⟩ := ih (by omega)
      exact ⟨s ++ keepList x m, by rw [keepUpto_succ, hs, List.append_assoc]⟩
    · have hkm : k = m + 1 := by omega
      exact ⟨[], by simp [hkm]⟩

/-- The `u`-th offset of the compacted block structure. -/
def dedupOffset (x : List ℕ) (u : ℕ) : ℕ := (keepUpto x u).length

/-- The compacted slot count. -/
def dedupNs (x : List ℕ) : ℕ := dedupOffset x (vertexCount x)

/-- The `j`-th target of the compacted block structure. -/
def dedupTarget (x : List ℕ) (j : ℕ) : ℕ := (keepUpto x (vertexCount x)).getD j 0

@[simp] theorem dedupOffset_zero (x : List ℕ) : dedupOffset x 0 = 0 := by
  simp [dedupOffset]

theorem dedupOffset_succ (x : List ℕ) (u : ℕ) :
    dedupOffset x (u + 1) = dedupOffset x u + (keepList x u).length := by
  simp [dedupOffset, keepUpto_succ]

theorem dedupOffset_mono' (x : List ℕ) {k m : ℕ} (h : k ≤ m) :
    dedupOffset x k ≤ dedupOffset x m := by
  obtain ⟨s, hs⟩ := keepUpto_prefix x h
  simp [dedupOffset, hs]

theorem dedupOffset_le_dedupNs (x : List ℕ) {k : ℕ} (h : k ≤ vertexCount x) :
    dedupOffset x k ≤ dedupNs x := dedupOffset_mono' x h

/-- **The compaction is a compaction**: never longer than the
encoding's own target array — the write pointer never passes the read
pointer. -/
theorem dedupOffset_le_offset {x : List ℕ} {n : ℕ} (_hn : vertexCount x = n)
    (hzero : offset x 0 = 0) (hmono : ∀ i < n, offset x i ≤ offset x (i + 1)) :
    ∀ k ≤ n, dedupOffset x k ≤ offset x k := by
  intro k hk
  induction k with
  | zero => simp [hzero]
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 := length_keepList_le x k
    have h3 := hmono k (by omega)
    rw [dedupOffset_succ]
    omega

theorem dedupNs_le {x : List ℕ} {n : ℕ} (hn : vertexCount x = n)
    (hzero : offset x 0 = 0) (hlast : offset x n = 2 * edgeCount x)
    (hmono : ∀ i < n, offset x i ≤ offset x (i + 1)) :
    dedupNs x ≤ 2 * edgeCount x := by
  rw [dedupNs, hn]
  exact hlast ▸ dedupOffset_le_offset hn hzero hmono n le_rfl

/-! ### The compacted array, cell by cell -/

theorem dedupTarget_eq {x : List ℕ} {u j : ℕ} (hu : u < vertexCount x)
    (hj : j < (keepList x u).length) :
    dedupTarget x (dedupOffset x u + j) = (keepList x u).getD j 0 := by
  obtain ⟨s, hs⟩ := keepUpto_prefix x (Nat.succ_le_of_lt hu)
  rw [keepUpto_succ] at hs
  rw [dedupTarget, hs, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp [dedupOffset]),
    List.getD_append _ _ _ _ (by simp [dedupOffset]; omega)]
  congr 1
  simp [dedupOffset]

/-- **A cell of the compacted array is a cell of the row it belongs
to.** -/
theorem mem_keepList_iff {x : List ℕ} {u v : ℕ} (hu : u < vertexCount x) :
    v ∈ keepList x u ↔
      ∃ j, dedupOffset x u ≤ j ∧ j < dedupOffset x (u + 1) ∧ dedupTarget x j = v := by
  rw [dedupOffset_succ]
  constructor
  · intro hv
    obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hv
    refine ⟨dedupOffset x u + i, by omega, by omega, ?_⟩
    rw [dedupTarget_eq hu hi, List.getD_eq_getElem _ _ hi, hiv]
  · rintro ⟨j, h₁, h₂, h₃⟩
    obtain ⟨i, hi⟩ : ∃ i, j = dedupOffset x u + i := ⟨j - dedupOffset x u, by omega⟩
    subst hi
    have hilen : i < (keepList x u).length := by omega
    rw [dedupTarget_eq hu hilen, List.getD_eq_getElem _ _ hilen] at h₃
    exact h₃ ▸ List.getElem_mem hilen

/-! ## §1c The two structural headlines -/

variable {n : ℕ} {G : SimpleGraph (Fin n)}

/-- Every entry of the compaction is an entry of some row. -/
theorem dedupTarget_lt {x : List ℕ} (hx : EncodesGraph x n G) {j : ℕ} (hj : j < dedupNs x) :
    dedupTarget x j < n := by
  have hlen : j < (keepUpto x (vertexCount x)).length := hj
  have hmem : dedupTarget x j ∈ keepUpto x (vertexCount x) := by
    rw [dedupTarget, List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  obtain ⟨l, hl, hml⟩ := List.mem_flatten.1 (by rwa [keepUpto] at hmem)
  obtain ⟨u, hu, hul⟩ := List.mem_map.1 hl
  subst hul
  obtain ⟨k, hk₁, hk₂, hk₃⟩ := mem_keepList.1 hml
  have hun : u < n := by rw [← hx.vertexCount_eq]; exact List.mem_range.1 hu
  have hkns : k < 2 * edgeCount x := by
    refine lt_of_lt_of_le hk₂ ?_
    rw [← hx.offset_last]
    exact RamBfs.offset_mono' hx (by omega) le_rfl
  exact hk₃ ▸ hx.target_lt k hkns

/-- **The compaction is a block structure for the same graph.** -/
theorem csrGraph_dedup {x : List ℕ} (hx : EncodesGraph x n G) :
    RamBfs.CsrGraph G (dedupNs x) (dedupOffset x) (dedupTarget x) where
  zero := dedupOffset_zero x
  last := by rw [dedupNs, hx.vertexCount_eq]
  mono i _ := dedupOffset_mono' x (Nat.le_succ i)
  target_lt j hj := dedupTarget_lt hx hj
  adj_iff u v := by
    have hun : (u : ℕ) < vertexCount x := by rw [hx.vertexCount_eq]; exact u.isLt
    rw [hx.adj_iff u v, ← mem_keepList, mem_keepList_iff hun]

/-- **And a simple one.** No row of the compaction names a vertex
twice — which is exactly what `C0Probe.encodesGraph_not_csrSimple`
shows the encoding itself does not give. -/
theorem csrSimple_dedup {x : List ℕ} (hx : EncodesGraph x n G) :
    RamElim.CsrSimple G (dedupNs x) (dedupOffset x) (dedupTarget x) where
  csr := csrGraph_dedup hx
  nodup u hu j₁ j₂ h₁ h₂ h₃ h₄ he := by
    have hun : u < vertexCount x := by rw [hx.vertexCount_eq]; exact hu
    rw [dedupOffset_succ] at h₂ h₄
    obtain ⟨i₁, hi₁⟩ : ∃ i, j₁ = dedupOffset x u + i := ⟨j₁ - dedupOffset x u, by omega⟩
    obtain ⟨i₂, hi₂⟩ : ∃ i, j₂ = dedupOffset x u + i := ⟨j₂ - dedupOffset x u, by omega⟩
    subst hi₁; subst hi₂
    have hl₁ : i₁ < (keepList x u).length := by omega
    have hl₂ : i₂ < (keepList x u).length := by omega
    rw [dedupTarget_eq hun hl₁, dedupTarget_eq hun hl₂,
      List.getD_eq_getElem _ _ hl₁, List.getD_eq_getElem _ _ hl₂] at he
    have := (List.Nodup.getElem_inj_iff (nodup_keepList x u)).1 he
    omega

/-! ## §1d The compacted slot count is even

`RamDriver`'s calling convention hands the slot count around as the
scalar `"m"` with `m + m = ns`, so the pass has to leave a *halved*
count behind — and can only do so because the compacted count is even.
It is: a compacted row lists each neighbour exactly once, so its length
is the degree of that vertex, and the sum of the degrees is twice the
number of edges. -/

/-- **The compacted slot count is twice the edge count**, in the form
the walk uses. -/
theorem dedupNs_even {x : List ℕ} (hx : EncodesGraph x n G) :
    ∃ e, dedupNs x = e + e := by
  classical
  -- a compacted row is the neighbourhood, listed once each
  have hdeg : ∀ u (hu : u < n), (keepList x u).length = G.degree ⟨u, hu⟩ := by
    intro u hu
    have hcard : (keepList x u).toFinset.card = (keepList x u).length :=
      List.toFinset_card_of_nodup (nodup_keepList x u)
    rw [← hcard, SimpleGraph.degree, ← Finset.card_image_of_injective
      (G.neighborFinset ⟨u, hu⟩) Fin.val_injective]
    congr 1
    ext v
    simp only [List.mem_toFinset, Finset.mem_image, SimpleGraph.mem_neighborFinset]
    constructor
    · intro hv
      obtain ⟨j, hj₁, hj₂, hj₃⟩ := mem_keepList.1 hv
      have hjns : j < 2 * edgeCount x := by
        refine lt_of_lt_of_le hj₂ ?_
        rw [← hx.offset_last]
        exact RamBfs.offset_mono' hx (by omega) le_rfl
      have hvn : v < n := hj₃ ▸ hx.target_lt j hjns
      exact ⟨⟨v, hvn⟩, (hx.adj_iff ⟨u, hu⟩ ⟨v, hvn⟩).2 ⟨j, hj₁, hj₂, hj₃⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact mem_keepList.2 ((hx.adj_iff ⟨u, hu⟩ w).1 hw)
  have hlist : ∀ k : ℕ, (List.map (List.length ∘ keepList x) (List.range k)).sum
      = ∑ u ∈ Finset.range k, (keepList x u).length := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp
  have hlen : dedupNs x = ∑ u ∈ Finset.range n, (keepList x u).length := by
    rw [dedupNs, hx.vertexCount_eq, dedupOffset, keepUpto, List.length_flatten,
      List.map_map, hlist n]
  have hsum : ∑ u ∈ Finset.range n, (keepList x u).length = ∑ v : Fin n, G.degree v := by
    rw [← Fin.sum_univ_eq_sum_range fun u => (keepList x u).length]
    exact Finset.sum_congr rfl fun v _ => hdeg (v : ℕ) v.isLt
  refine ⟨G.edgeFinset.card, ?_⟩
  rw [hlen, hsum, SimpleGraph.sum_degrees_eq_twice_card_edges]
  omega

/-! ## §2 The pass

`dedupCom` compacts every row in place. The write pointer `"dw"` never
passes the read pointer `"dj"` (a row's kept slots are never more than
its slots, and the rows before it were compacted first), so the
compaction can be done in the encoding's own target array.

The marks live in `"dmk"`, one cell per vertex, and are **cleaned
between rows** by walking the slots the row just wrote — the trail
discipline. That is what keeps the pass at `O(n + ns)`: a row pays for
its own marks and no row ever walks the whole mark array. A pass that
zeroed `"dmk"` per row would be `O(n · rows)`, which on a sparse class
member is the `n²` the C0 budget has no room for.

There is **no input-scaling literal in the program text**: every loop
bound is a `.var`, because one program has to serve every input at the
C0 boundary. -/

/-- One slot of the row being compacted: a target the row has already
named is skipped; a new one is marked, written at the write pointer,
and the write pointer moves. -/
def dedupSlot : Com :=
  .seq (.assign "dv" (.get "tgt" (.var "dj")))
    (.seq (.ite (.lt (.lit 0) (.get "dmk" (.var "dv")))
            .skip
            (.seq (.store "dmk" (.var "dv") (.lit 1))
              (.seq (.store "tgt" (.var "dw") (.var "dv"))
                (.assign "dw" (.add (.var "dw") (.lit 1))))))
      (.assign "dj" (.add (.var "dj") (.lit 1))))

/-- One slot of the trail: the marks a row set are cleared by walking
the slots that row wrote, and nothing else. -/
def dedupUnmark : Com :=
  .seq (.store "dmk" (.get "tgt" (.var "dk")) (.lit 0))
    (.assign "dk" (.add (.var "dk") (.lit 1)))

/-- One row: read the old block bounds, publish the new offset, compact
the block, then clean the trail. -/
def dedupRow : Com :=
  .seq (.assign "dj" (.get "off" (.var "di")))
    (.seq (.assign "de" (.get "off" (.add (.var "di") (.lit 1))))
      (.seq (.assign "ds" (.var "dw"))
        (.seq (.store "off" (.var "di") (.var "dw"))
          (.seq (.while (.lt (.var "dj") (.var "de")) dedupSlot)
            (.seq (.assign "dk" (.var "ds"))
              (.seq (.while (.lt (.var "dk") (.var "dw")) dedupUnmark)
                (.assign "di" (.add (.var "di") (.lit 1)))))))))

/-- The cells the compaction freed, zeroed. Above the *old* slot count
the tail is already zero (`RamDriver.DecodeMem`'s third clause) and the
pass does not touch it. -/
def dedupZero : Com :=
  .seq (.assign "dk" (.var "dw"))
    (.while (.lt (.var "dk") (.var "dq"))
      (.seq (.store "tgt" (.var "dk") (.lit 0))
        (.assign "dk" (.add (.var "dk") (.lit 1)))))

/-- The exported scalar: the driver's calling convention carries the
slot count as `"m"` with `m + m = ns`, so the pass halves the compacted
count. It is even — `dedupNs_even` — because a compacted row lists each
neighbour exactly once. -/
def dedupHalve : Com :=
  .seq (.assign "m" (.lit 0))
    (.seq (.assign "dk" (.lit 0))
      (.while (.lt (.var "dk") (.var "dw"))
        (.seq (.assign "dk" (.add (.var "dk") (.lit 2)))
          (.assign "m" (.add (.var "m") (.lit 1))))))

/-- **The dedup pass.** -/
def dedupCom : Com :=
  .seq (.assign "dq" (.add (.var "m") (.var "m")))
    (.seq (.assign "dw" (.lit 0))
      (.seq (.assign "di" (.lit 0))
        (.seq (.while (.lt (.var "di") (.var "n")) dedupRow)
          (.seq (.store "off" (.var "n") (.var "dw"))
            (.seq dedupZero dedupHalve)))))

/-! ## §2b The differential

The falsification gate, run: `decodeCom ; dedupCom` on real words,
through `TgtWidenProbe`'s fuelled interpreter (the mirror of
`Lax13Proofs.Bounds.BigStepB`, anchored there against the compiled
golden run). Three instances: the duplicate-bearing `K₂` of
`C0Probe`, a `K₃` whose first row interleaves *two* repeated
neighbours, and — the negative control — an already-simple word, which
must come out cell for cell unchanged. -/

open Lax3Proofs.TgtWidenProbe in
/-- The state the decode is entered in: the four arrays it writes at the
lengths `RamDriver.DecodeMem` asks for, the mark array of the pass, and
the word on the tape. -/
def decSt (n W : ℕ) (x : List ℕ) : PSt where
  vars := []
  arrs :=
    [("off", List.replicate (n + 1) 0), ("tgt", List.replicate W 0),
     (RamDriver.alvName 0, List.replicate n 0),
     (RamDriver.gamName 0, List.replicate n 0),
     ("dmk", List.replicate n 0)]
  inp := x

open Lax3Proofs.TgtWidenProbe in
/-- The composed pass, run on a word. -/
def decDedup (n W : ℕ) (x : List ℕ) : PRes :=
  exec pB pF (.seq RamDriver.decodeCom dedupCom) (decSt n W x)

/-! ### The witness: `C0Probe.dupWord`, whose row 0 is `[1, 1]` -/

open Lax3Proofs.TgtWidenProbe in
/-- The run of the composed pass on the duplicate-bearing `K₂`. -/
def dupRun : PRes := decDedup 2 8 C0Probe.dupWord

#guard dupRun.isOk

-- row 0 compacts from `[1, 1]` to `[1]`, row 1 from `[0, 0]` to `[0]`
#guard (List.range 3).map (dupRun.cell "off") = [0, 1, 2]
#guard (List.range 8).map (dupRun.cell "tgt") = [1, 0, 0, 0, 0, 0, 0, 0]

-- the freed cells (the old slots `2` and `3`) are zeroed, and the pad
-- above the old slot count was never written
#guard dupRun.cell "tgt" 2 = 0
#guard dupRun.cell "tgt" 3 = 0

-- the exported scalar pair: `m + m = dedupNs = 2`
#guard dupRun.scalar "m" = 1
#guard dupRun.scalar "dw" = 2

-- the marks are clean again — the trail was walked back
#guard (List.range 2).map (dupRun.cell "dmk") = [0, 0]

-- and the machine's answer is the arithmetic of §1, cell for cell
#guard dedupNs C0Probe.dupWord = 2
#guard (List.range 3).map (dedupOffset C0Probe.dupWord) = [0, 1, 2]
#guard (List.range 2).map (dedupTarget C0Probe.dupWord) = [1, 0]
#guard (List.range 3).map (dupRun.cell "off")
  = (List.range 3).map (dedupOffset C0Probe.dupWord)
#guard (List.range 2).map (dupRun.cell "tgt")
  = (List.range 2).map (dedupTarget C0Probe.dupWord)

/-- **The gate, positive half.** The very instantiation
`C0Probe.not_csrSimple_dupWord` refutes is `CsrSimple` after the
compaction. -/
theorem csrSimple_dupWord :
    RamElim.CsrSimple (⊤ : SimpleGraph (Fin 2)) (dedupNs C0Probe.dupWord)
      (dedupOffset C0Probe.dupWord) (dedupTarget C0Probe.dupWord) :=
  csrSimple_dedup C0Probe.encodesGraph_dupWord

/-! ### Refute the tempting strengthening

`dedupNs x = 2 * edgeCount x` is **false**: `dupWord` has `edgeCount 2`
and compacts to `2` slots, not `4`. So no lemma below may assume the
compacted count is the word's declared one — the pass has to *compute*
it, and the caller has to be handed it. -/

#guard ¬ (dedupNs C0Probe.dupWord = 2 * edgeCount C0Probe.dupWord)
#guard dedupNs C0Probe.dupWord = 2
#guard 2 * edgeCount C0Probe.dupWord = 4

/-- The refutation as a statement, not only a check. -/
theorem not_dedupNs_eq_two_mul_edgeCount :
    ∃ (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)),
      EncodesGraph x n G ∧ dedupNs x ≠ 2 * edgeCount x :=
  ⟨C0Probe.dupWord, 2, ⊤, C0Probe.encodesGraph_dupWord, by decide⟩

/-! ### A richer witness: interleaved repeats

`triWord` encodes the triangle with row `0` listing `1, 2, 1, 2` — two
neighbours, each twice, interleaved, so the write pointer falls two
behind the read pointer inside a single row and every later row is
written over cells it did not come from. -/

/-- The triangle, with row `0` repeating both of its neighbours. -/
def triWord : List ℕ := [3, 4, 0, 4, 6, 8, 1, 2, 1, 2, 0, 2, 0, 1]

#guard vertexCount triWord = 3
#guard edgeCount triWord = 4
#guard triWord.length = 3 + 3 + 2 * edgeCount triWord
#guard (List.range 4).map (offset triWord) = [0, 4, 6, 8]
#guard (List.range 8).map (target triWord) = [1, 2, 1, 2, 0, 2, 0, 1]

#guard dedupNs triWord = 6
#guard (List.range 4).map (dedupOffset triWord) = [0, 2, 4, 6]
#guard (List.range 6).map (dedupTarget triWord) = [1, 2, 0, 2, 0, 1]

open Lax3Proofs.TgtWidenProbe in
/-- The run of the composed pass on the triangle. -/
def triRun : PRes := decDedup 3 12 triWord

#guard triRun.isOk
#guard (List.range 4).map (triRun.cell "off") = [0, 2, 4, 6]
#guard (List.range 12).map (triRun.cell "tgt") = [1, 2, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0]
#guard triRun.scalar "m" = 3
#guard triRun.scalar "dw" = 6
#guard (List.range 3).map (triRun.cell "dmk") = [0, 0, 0]

-- the machine and the arithmetic agree, cell for cell
#guard (List.range 4).map (triRun.cell "off") = (List.range 4).map (dedupOffset triWord)
#guard (List.range 6).map (triRun.cell "tgt") = (List.range 6).map (dedupTarget triWord)

/-! ### The negative control: an already-simple word is unchanged

`simpleWord` is `K₂` without repeats. The pass must leave every cell of
`off` and `tgt` exactly where the decode put it, and hand back the
decode's own `"m"`. -/

/-- `K₂`, encoded without repeats. -/
def simpleWord : List ℕ := [2, 1, 0, 1, 2, 1, 0]

#guard vertexCount simpleWord = 2
#guard edgeCount simpleWord = 1
#guard simpleWord.length = 3 + 2 + 2 * edgeCount simpleWord
#guard (List.range 3).map (offset simpleWord) = [0, 1, 2]
#guard (List.range 2).map (target simpleWord) = [1, 0]

open Lax3Proofs.TgtWidenProbe in
/-- The decode alone, for the cell-for-cell comparison. -/
def simpleDecode : PRes := exec pB pF RamDriver.decodeCom (decSt 2 6 simpleWord)

open Lax3Proofs.TgtWidenProbe in
/-- The decode followed by the pass. -/
def simpleRun : PRes := decDedup 2 6 simpleWord

#guard simpleDecode.isOk
#guard simpleRun.isOk

-- **cell for cell unchanged**: the offsets, the targets, and the
-- exported scalar are the decode's own
#guard (List.range 3).map (simpleRun.cell "off") = (List.range 3).map (simpleDecode.cell "off")
#guard (List.range 6).map (simpleRun.cell "tgt") = (List.range 6).map (simpleDecode.cell "tgt")
#guard simpleRun.scalar "m" = simpleDecode.scalar "m"

-- and those are the values the encoding declares
#guard (List.range 3).map (simpleRun.cell "off") = [0, 1, 2]
#guard (List.range 6).map (simpleRun.cell "tgt") = [1, 0, 0, 0, 0, 0]
#guard simpleRun.scalar "m" = 1
#guard dedupNs simpleWord = 2
#guard 2 * edgeCount simpleWord = 2

-- the two masks the decode opened are untouched by the pass
#guard (List.range 2).map (simpleRun.cell (RamDriver.alvName 0)) = [1, 1]
#guard (List.range 2).map (simpleRun.cell (RamDriver.gamName 0)) = [1, 1]

/-! ### Why `DedupMem` is in the precondition, both halves

An IMP+ store out of range is **stuck**, not defaulted, so a memory
clause is not decoration: without one the pass has no run at all. And a
mark array that is present but not *zero* is worse than absent — the
pass runs and answers wrongly. Both halves are refuted here, in the
house style of `TgtWidenProbe`'s un-widened round. -/

open Lax3Proofs.TgtWidenProbe in
/-- The same state with the mark array **absent**. An array that was
never allocated is empty, so the first mark is out of range. -/
def noMarkSt (n W : ℕ) (x : List ℕ) : PSt where
  vars := []
  arrs :=
    [("off", List.replicate (n + 1) 0), ("tgt", List.replicate W 0),
     (RamDriver.alvName 0, List.replicate n 0),
     (RamDriver.gamName 0, List.replicate n 0)]
  inp := x

open Lax3Proofs.TgtWidenProbe in
-- **the sizing half**: without `"dmk"` the pass is stuck
#guard (exec pB pF (.seq RamDriver.decodeCom dedupCom) (noMarkSt 2 8 C0Probe.dupWord)).isStuck

open Lax3Proofs.TgtWidenProbe in
/-- The same state with the mark array present, sized, and **dirty**. -/
def dirtyMarkSt (n W : ℕ) (x : List ℕ) : PSt where
  vars := []
  arrs :=
    [("off", List.replicate (n + 1) 0), ("tgt", List.replicate W 0),
     (RamDriver.alvName 0, List.replicate n 0),
     (RamDriver.gamName 0, List.replicate n 0),
     ("dmk", List.replicate n 1)]
  inp := x

open Lax3Proofs.TgtWidenProbe in
/-- The run on a dirty mark array. -/
def dirtyRun : PRes := exec pB pF (.seq RamDriver.decodeCom dedupCom)
  (dirtyMarkSt 2 8 C0Probe.dupWord)

-- **the zeroing half**: it runs, and it is wrong — every target reads
-- as already seen, so the whole block structure is emptied
#guard dirtyRun.isOk
#guard dirtyRun.scalar "dw" = 0
#guard ¬ (dirtyRun.scalar "dw" = dedupNs C0Probe.dupWord)
#guard (List.range 3).map (dirtyRun.cell "off") = [0, 0, 0]
#guard ¬ ((List.range 3).map (dirtyRun.cell "off")
  = (List.range 3).map (dedupOffset C0Probe.dupWord))

/-! ## §3a The pass's frame, its memory clause, and the two loop
invariants' list arithmetic

The walk itself (`dedup_spec`) is **not** in this file yet; what is here
is everything it consumes that is not an `Env` manipulation: the
syntactic frame of the program, the memory clause the mark array needs,
and the two list-level transition lemmas that carry the inner loop and
the trail. Those two are where the design could have been wrong, and
they are proved. -/

/-- **The memory clause of the pass**: the one array the decode does not
allocate. It is `n` cells — one per vertex — and it starts, and is
handed back, all zero. -/
def DedupMem (n : ℕ) (σ : Env) : Prop :=
  (σ.arrs "dmk").length = n ∧ ∀ v ∈ σ.arrs "dmk", v = 0

theorem dedupMem_arrOf {n : ℕ} {σ : Env} (h : σ.arrs "dmk" = arrOf n (fun _ => 0)) :
    DedupMem n σ := by
  refine ⟨by rw [h]; simp, fun v hv => ?_⟩
  rw [h, arrOf] at hv
  obtain ⟨i, -, hi⟩ := List.mem_map.1 hv
  exact hi.symm

/-! ### The syntactic frame

Nine scalars and three arrays; the pass touches no tape. -/

theorem warrs_dedupSlot : dedupSlot.warrs = ["dmk", "tgt"] := by
  simp [dedupSlot, Com.warrs]

theorem warrs_dedupUnmark : dedupUnmark.warrs = ["dmk"] := by
  simp [dedupUnmark, Com.warrs]

theorem not_reads_dedupCom : ¬ dedupCom.reads := by
  simp [dedupCom, dedupRow, dedupSlot, dedupUnmark, dedupZero, dedupHalve, Com.reads]

theorem noWrite_dedupCom : dedupCom.NoWrite := by
  simp [dedupCom, dedupRow, dedupSlot, dedupUnmark, dedupZero, dedupHalve, Com.NoWrite]

/-- The scalars the pass writes. Everything else — `"n"` above all — it
leaves alone. -/
theorem frame_var_dedupCom {B : ℕ} {σ σ' : Env} {K : ℕ} (h : Run B dedupCom σ σ' K)
    (y : String) (h₁ : y ≠ "dq") (h₂ : y ≠ "dw") (h₃ : y ≠ "di") (h₄ : y ≠ "dj")
    (h₅ : y ≠ "de") (h₆ : y ≠ "ds") (h₇ : y ≠ "dk") (h₈ : y ≠ "dv") (h₉ : y ≠ "m") :
    σ'.vars y = σ.vars y :=
  h.frame_var y (by
    simp [dedupCom, dedupRow, dedupSlot, dedupUnmark, dedupZero, dedupHalve, Com.wvars,
      h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉])

/-- The arrays the pass writes: the two of the block structure and its
own marks. Every other array of a level — the two masks the decode
opened, and all of `RamDriver.OrderMem`'s scratch — is untouched. -/
theorem frame_arr_dedupCom {B : ℕ} {σ σ' : Env} {K : ℕ} (h : Run B dedupCom σ σ' K)
    (a : String) (h₁ : a ≠ "off") (h₂ : a ≠ "tgt") (h₃ : a ≠ "dmk") :
    σ'.arrs a = σ.arrs a :=
  h.frame_arr a (by
    simp [dedupCom, dedupRow, dedupSlot, dedupUnmark, dedupZero, dedupHalve, Com.warrs,
      h₁, h₂, h₃])

/-! ### The inner loop, on the list side

The slot loop's invariant is one equation: after reading the prefix `p`
of the row, the cells the pass has written are `firstDedup p` and the
marks are exactly its entries. `firstDedup_concat` is the step;
`mark_step` is the same step read on the mark array. -/

/-- **A new target extends both the written block and the mark set;** a
repeat extends neither. -/
theorem mark_step (p : List ℕ) (v : ℕ) :
    (fun w => if w ∈ firstDedup (p ++ [v]) then 1 else 0)
      = if v ∈ p then (fun w => if w ∈ firstDedup p then 1 else 0)
        else upd (fun w => if w ∈ firstDedup p then 1 else 0) v 1 := by
  rw [firstDedup_concat]
  by_cases hv : v ∈ p
  · rw [if_pos hv, if_pos hv]
  · rw [if_neg hv, if_neg hv]
    funext w
    rw [upd_apply]
    by_cases hw : w = v
    · subst hw; simp [mem_firstDedup, hv]
    · simp only [hw, if_false, List.mem_append, List.mem_singleton]
      simp

/-- The mark test the program makes is membership in the prefix. -/
theorem mark_test (p : List ℕ) (v : ℕ) :
    (0 < (if v ∈ firstDedup p then 1 else 0)) ↔ v ∈ p := by
  by_cases hv : v ∈ p <;> simp [mem_firstDedup, hv]

/-! ### The trail, on the list side

The marks a row set are cleared by walking the slots that row wrote —
never the whole mark array. `unmark_step` is one step of that walk, and
it is where the compaction's `Nodup` earns its keep: clearing the mark
of the `t`-th kept target does not clear a mark that is still standing,
because no later kept target equals it. -/

/-- **One step of the trail walk.** -/
theorem unmark_step {kept : List ℕ} (hnd : kept.Nodup) {t : ℕ} (ht : t < kept.length) :
    upd (fun w => if w ∈ kept.drop t then 1 else 0) (kept.getD t 0) 0
      = fun w => if w ∈ kept.drop (t + 1) then 1 else 0 := by
  have hsplit : kept.drop t = kept[t] :: kept.drop (t + 1) :=
    List.drop_eq_getElem_cons ht
  have hnotmem : kept[t] ∉ kept.drop (t + 1) := by
    have hd : (kept.drop t).Nodup := hnd.sublist (List.drop_sublist t kept)
    rw [hsplit, List.nodup_cons] at hd
    exact hd.1
  funext w
  rw [upd_apply, List.getD_eq_getElem _ _ ht]
  by_cases hw : w = kept[t]
  · subst hw; simp [hnotmem]
  · simp only [hw, if_false, hsplit, List.mem_cons]
    simp

/-- The trail walk starts at the whole kept block and ends empty. -/
theorem drop_zero_marks (kept : List ℕ) :
    (fun w => if w ∈ kept.drop 0 then 1 else 0) = fun w => if w ∈ kept then 1 else 0 := by
  rw [List.drop_zero]

theorem drop_len_marks (kept : List ℕ) :
    (fun w : ℕ => if w ∈ kept.drop kept.length then 1 else 0) = fun _ => 0 := by
  simp

/-! ## §4 The composed obligation

`DecodeImplementsD` is what the assembly consumes in place of
`RamDriver.DecodeImplements`: the same phase with the dedup guard
spliced in, the same postcondition template read at the *compacted*
data, and the one upgrade the wave exists for — the `CsrSimple` slot,
which `C0Probe.encodesGraph_not_csrSimple` shows no producer can close
from `EncodesGraph` without it.

The postcondition is destructured exactly as `RamDriver.driver_correct`
destructures the decode's, with `CsrSimple` and the compacted zero tail
added, so the B7 re-run's `obtain` pattern changes only by those two
conjuncts.

**Status.** The Prop is stated and its data (§1) is proved: the
compacted block structure exists, is a `CsrGraph` for the same graph, is
`CsrSimple`, has an even slot count, and is what the program computes on
the three differential instances of §2b. What is *not* in this file is
the `Spec` walk that discharges it — `dedup_spec` (the state-level
invariants of §3a's two lemmas, threaded through
`Csr.rowScan_spec`/`Spec.forRange`) and its composition with
`RamDriverIO.decodeImplements` through `Spec.seq`. Nothing below
asserts it; `DecodeImplementsD` is a definition, not a theorem, exactly
as `RamDriver.DecodeImplements` is. -/

/-- The compacted target array is zero above the compacted slot count —
for free, because a cell above it is a read past the end of the
compacted list. This is the fact that stands where `hpad0` used to be a
hypothesis. -/
theorem dedupTarget_eq_zero {x : List ℕ} {z : ℕ} (hz : dedupNs x ≤ z) :
    dedupTarget x z = 0 := by
  rw [dedupTarget, List.getD_eq_default]
  exact hz

/-- The pass's own cost: one turn per row, one per slot read, one per
slot written, one per freed cell, and one per two compacted slots. The
constants are the walk's to pin; the shape — linear in `n` and the
*old* slot count, with no `n · ns` term — is what the touched-only
discipline of the trail buys and what the C0 budget needs. -/
def dedupCost (n ns : ℕ) : ℕ := 60 * n + 60 * ns + 40

/-- **The decode with the dedup guard**, as the obligation the assembly
consumes. Precondition: the decode's own, plus `DedupMem` for the mark
array. Postcondition: the decode's own template at
`ns' = dedupNs x`, `O' = dedupOffset x`, `T' = dedupTarget x`, plus
`CsrSimple` and the compacted zero tail. -/
def DecodeImplementsD (B : ℕ) (x : List ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (ns W : ℕ) (T : ℕ → ℕ) (K : ℕ) : Prop :=
  (∀ v ∈ x, v < B) → n + 1 < B → ns < B → W < B → ns ≤ W →
    (∀ z, ns ≤ z → z < W → T z = 0) →
    Spec B (fun σ => RamDriver.DecodeMem n ns W σ ∧ RamDriver.OrderMem B n ns W σ ∧
        DedupMem n σ ∧ σ.inp = x ∧ σ.out = [])
      (.seq RamDriver.decodeCom dedupCom)
      (fun _ σ' => σ'.out = [] ∧
        RamBfs.CsrGraph G (dedupNs x) (dedupOffset x) (dedupTarget x) ∧
        RamElim.CsrSimple G (dedupNs x) (dedupOffset x) (dedupTarget x) ∧
        dedupNs x ≤ ns ∧
        (∀ z, dedupNs x ≤ z → z < W → dedupTarget x z = 0) ∧
        σ'.vars "n" = n ∧
        σ'.arrs "off" = arrOf (n + 1) (dedupOffset x) ∧
        σ'.arrs "tgt" = arrOf W (dedupTarget x) ∧
        σ'.vars "m" + σ'.vars "m" = dedupNs x ∧
        RamDriver.OrderMem B n (dedupNs x) W σ' ∧
        DedupMem n σ' ∧
        (∃ M, σ'.arrs (RamDriver.alvName 0) = arrOf n M ∧ ∀ v < n, M v = 1) ∧
        (∃ Gm, σ'.arrs (RamDriver.gamName 0) = arrOf n Gm ∧ ∀ v < n, Gm v = 1)) K

/-- **The data half of `DecodeImplementsD`, proved.** Every conjunct of
the postcondition that is a statement about the *word* rather than
about the machine holds, at the instantiation the composed obligation
reads them at. What remains for the walk is that the machine's arrays
hold these functions. -/
theorem dedup_data {x : List ℕ} (hx : EncodesGraph x n G) {ns : ℕ}
    (hns : ns = 2 * edgeCount x) :
    RamBfs.CsrGraph G (dedupNs x) (dedupOffset x) (dedupTarget x) ∧
      RamElim.CsrSimple G (dedupNs x) (dedupOffset x) (dedupTarget x) ∧
      dedupNs x ≤ ns ∧
      (∀ z, dedupNs x ≤ z → dedupTarget x z = 0) ∧
      ∃ e, dedupNs x = e + e := by
  refine ⟨csrGraph_dedup hx, csrSimple_dedup hx, ?_, fun z hz => dedupTarget_eq_zero hz,
    dedupNs_even hx⟩
  rw [hns]
  exact dedupNs_le hx.vertexCount_eq hx.offset_zero hx.offset_last hx.offset_mono

end Lax3Proofs.RamDriverDedup
