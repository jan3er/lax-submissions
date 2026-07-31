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

What is here is everything the walk consumes that is not an `Env`
manipulation: the syntactic frame of the program, the memory clause the
mark array needs, and the two list-level transition lemmas that carry
the inner loop and the trail. Those two are where the design could have
been wrong, and they are proved. The walk itself is §3c–§3h. -/

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

/-! ## §3b The row prefix, and the one inequality the pass rests on

The inner loop's invariant is an equation about `firstDedup` of the
*prefix* of the row read so far. These name that prefix, say what one
more slot does to it, and bound the write pointer by the read pointer —
which is what makes the compaction legal in the encoding's own array. -/

/-- The slots of row `i` read so far: the targets of `[offset x i, j)`. -/
def rowPfx (x : List ℕ) (i j : ℕ) : List ℕ := slotList (target x) (offset x i) j

/-- Those of them the compaction kept. -/
def rowKept (x : List ℕ) (i j : ℕ) : List ℕ := firstDedup (rowPfx x i j)

@[simp] theorem rowPfx_start (x : List ℕ) (i : ℕ) : rowPfx x i (offset x i) = [] := by
  simp [rowPfx, slotList]

@[simp] theorem rowKept_start (x : List ℕ) (i : ℕ) : rowKept x i (offset x i) = [] := by
  simp [rowKept]

theorem rowPfx_succ {x : List ℕ} {i j : ℕ} (h : offset x i ≤ j) :
    rowPfx x i (j + 1) = rowPfx x i j ++ [target x j] := slotList_concat h

theorem rowKept_succ {x : List ℕ} {i j : ℕ} (h : offset x i ≤ j) :
    rowKept x i (j + 1) =
      if target x j ∈ rowPfx x i j then rowKept x i j else rowKept x i j ++ [target x j] := by
  rw [rowKept, rowPfx_succ h, firstDedup_concat, rowKept]

theorem rowPfx_end (x : List ℕ) (i : ℕ) : rowPfx x i (offset x (i + 1)) = rowList x i := rfl

theorem rowKept_end (x : List ℕ) (i : ℕ) : rowKept x i (offset x (i + 1)) = keepList x i := rfl

@[simp] theorem length_rowPfx (x : List ℕ) (i j : ℕ) :
    (rowPfx x i j).length = j - offset x i := by simp [rowPfx]

theorem length_rowKept_le (x : List ℕ) (i j : ℕ) :
    (rowKept x i j).length ≤ j - offset x i := by
  rw [rowKept, ← length_rowPfx x i j]; exact length_firstDedup_le _

theorem nodup_rowKept (x : List ℕ) (i j : ℕ) : (rowKept x i j).Nodup :=
  nodup_firstDedup _

/-- The entries of a prefix are targets of the word, so they are
vertices — which is what makes the mark array's index legal. -/
theorem target_lt_of_row {x : List ℕ} (hx : EncodesGraph x n G) {i j : ℕ} (hi : i < n)
    (_h₁ : offset x i ≤ j) (h₂ : j < offset x (i + 1)) : target x j < n := by
  refine hx.target_lt j (lt_of_lt_of_le h₂ ?_)
  rw [← hx.offset_last]
  exact RamBfs.offset_mono' hx (by omega) le_rfl

/-- **The write pointer never passes the read pointer.** The rows below
`i` compacted into `dedupOffset x i ≤ offset x i` cells, and row `i`
itself has kept no more than it has read. -/
theorem write_le_read {x : List ℕ} (hx : EncodesGraph x n G) {i j : ℕ}
    (hi : i ≤ n) (hj : offset x i ≤ j) :
    dedupOffset x i + (rowKept x i j).length ≤ j := by
  have h1 : dedupOffset x i ≤ offset x i :=
    dedupOffset_le_offset hx.vertexCount_eq hx.offset_zero hx.offset_mono i hi
  have h2 := length_rowKept_le x i j
  omega

/-- The compacted target array is zero above the compacted slot count —
for free, because a cell above it is a read past the end of the
compacted list. This is the fact that stands where `hpad0` used to be a
hypothesis. -/
theorem dedupTarget_eq_zero {x : List ℕ} {z : ℕ} (hz : dedupNs x ≤ z) :
    dedupTarget x z = 0 := by
  rw [dedupTarget, List.getD_eq_default]
  exact hz

/-- The mark array, as the memory clause holds it. -/
theorem dedupMem_eq {n : ℕ} {σ : Env} (h : DedupMem n σ) :
    σ.arrs "dmk" = arrOf n (fun _ => 0) := by
  rw [← replicate_eq_arrOf]
  exact List.eq_replicate_iff.2 ⟨h.1, h.2⟩

/-- **What the compaction has written stays written.** The kept list of
a prefix is a prefix of the kept list of a longer one — so a cell the
inner loop has already published is a cell of the finished row, and the
invariant can name its content by `dedupTarget` from the moment it is
written. -/
theorem rowKept_mono {x : List ℕ} {i j : ℕ} (h₁ : offset x i ≤ j) :
    ∀ k, j ≤ k → ∃ t, rowKept x i k = rowKept x i j ++ t := by
  intro k
  induction k with
  | zero =>
    intro h
    exact ⟨[], by rw [show j = 0 by omega]; simp⟩
  | succ k ih =>
    intro h
    rcases Nat.lt_or_ge j (k + 1) with hk | hk
    · obtain ⟨t, ht⟩ := ih (by omega)
      have hik : offset x i ≤ k := by omega
      by_cases hv : target x k ∈ rowPfx x i k
      · exact ⟨t, by rw [rowKept_succ hik, if_pos hv, ht]⟩
      · exact ⟨t ++ [target x k], by rw [rowKept_succ hik, if_neg hv, ht, List.append_assoc]⟩
    · exact ⟨[], by rw [show j = k + 1 by omega]; simp⟩

/-- A cell the inner loop has published is the cell of the compacted
array it will remain. -/
theorem dedupTarget_rowKept {x : List ℕ} (hx : EncodesGraph x n G) {i j t : ℕ} (hi : i < n)
    (h₁ : offset x i ≤ j) (h₂ : j ≤ offset x (i + 1)) (ht : t < (rowKept x i j).length) :
    dedupTarget x (dedupOffset x i + t) = (rowKept x i j).getD t 0 := by
  obtain ⟨s, hs⟩ := rowKept_mono h₁ (offset x (i + 1)) h₂
  rw [rowKept_end] at hs
  have hlen : t < (keepList x i).length := by rw [hs]; simp; omega
  rw [dedupTarget_eq (by rw [hx.vertexCount_eq]; exact hi) hlen, hs,
    List.getD_append _ _ _ _ ht]

/-- The entries of a compacted row are vertices. -/
theorem mem_keepList_lt {x : List ℕ} (hx : EncodesGraph x n G) {u v : ℕ} (hu : u < n)
    (hv : v ∈ keepList x u) : v < n := by
  obtain ⟨j, hj₁, hj₂, hj₃⟩ := mem_keepList.1 hv
  exact hj₃ ▸ target_lt_of_row hx hu hj₁ hj₂

/-! ## §3c The three invariants

One per loop, and one clause they share. `TgtSplit` is the target array
mid-pass: the compaction below the write pointer, the encoding's own
above the read pointer, and — deliberately — *nothing at all* about the
cells between, which the compaction has already consumed and which no
later read touches. That silence is what makes an in-place compaction
statable; an invariant that named those cells would be false. -/

/-- **The target array mid-pass.** -/
def TgtSplit (x : List ℕ) (W : ℕ) (T : ℕ → ℕ) (dw rd : ℕ) (σ : Env) : Prop :=
  ∃ F, σ.arrs "tgt" = arrOf W F ∧
    (∀ j < dw, F j = dedupTarget x j) ∧
    (∀ j, rd ≤ j → j < W → F j = T j)

/-- The invariant of the outer loop, read at a row boundary. -/
def DedupOuter (x : List ℕ) (n ns W : ℕ) (T : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "di" ≤ n ∧ σ.vars "n" = n ∧ σ.vars "dq" = ns ∧
    σ.vars "dw" = dedupOffset x (σ.vars "di") ∧
    σ.arrs "off" =
      arrOf (n + 1) (fun k => if k < σ.vars "di" then dedupOffset x k else offset x k) ∧
    σ.arrs "dmk" = arrOf n (fun _ => 0) ∧
    TgtSplit x W T (dedupOffset x (σ.vars "di")) (offset x (σ.vars "di")) σ

/-- The invariant of the slot loop of row `i`: the marks are the entries
of the kept prefix, and the write pointer stands past them. -/
def DedupInner (x : List ℕ) (n ns W : ℕ) (T : ℕ → ℕ) (i : ℕ) (σ : Env) : Prop :=
  offset x i ≤ σ.vars "dj" ∧ σ.vars "dj" ≤ offset x (i + 1) ∧
    σ.vars "di" = i ∧ σ.vars "n" = n ∧ σ.vars "dq" = ns ∧
    σ.vars "de" = offset x (i + 1) ∧ σ.vars "ds" = dedupOffset x i ∧
    σ.vars "dw" = dedupOffset x i + (rowKept x i (σ.vars "dj")).length ∧
    σ.arrs "off" = arrOf (n + 1) (fun k => if k < i + 1 then dedupOffset x k else offset x k) ∧
    σ.arrs "dmk" = arrOf n (fun v => if v ∈ rowKept x i (σ.vars "dj") then 1 else 0) ∧
    TgtSplit x W T (dedupOffset x i + (rowKept x i (σ.vars "dj")).length) (σ.vars "dj") σ

/-- The invariant of the trail walk of row `i`: the marks still standing
are exactly the kept targets the walk has not reached. -/
def DedupUnmk (x : List ℕ) (n ns W : ℕ) (T : ℕ → ℕ) (i : ℕ) (σ : Env) : Prop :=
  dedupOffset x i ≤ σ.vars "dk" ∧ σ.vars "dk" ≤ dedupOffset x (i + 1) ∧
    σ.vars "di" = i ∧ σ.vars "n" = n ∧ σ.vars "dq" = ns ∧
    σ.vars "dw" = dedupOffset x (i + 1) ∧
    σ.arrs "off" = arrOf (n + 1) (fun k => if k < i + 1 then dedupOffset x k else offset x k) ∧
    σ.arrs "dmk" = arrOf n
      (fun v => if v ∈ (keepList x i).drop (σ.vars "dk" - dedupOffset x i) then 1 else 0) ∧
    TgtSplit x W T (dedupOffset x (i + 1)) (offset x (i + 1)) σ

/-- **Weakening the split.** A pass that neither wrote to `tgt` nor
moved a pointer outward keeps the clause; the write pointer may only
fall back and the read pointer only advance, since both directions
*shrink* what is claimed. -/
theorem tgtSplit_of {x : List ℕ} {W : ℕ} {T : ℕ → ℕ} {dw rd dw' rd' : ℕ} {σ σ' : Env}
    (h : TgtSplit x W T dw rd σ) (harr : σ'.arrs "tgt" = σ.arrs "tgt")
    (hdw : dw' ≤ dw) (hrd : rd ≤ rd') : TgtSplit x W T dw' rd' σ' := by
  obtain ⟨F, hF, hlo, hhi⟩ := h
  exact ⟨F, by rw [harr, hF], fun j hj => hlo j (by omega),
    fun j h₁ h₂ => hhi j (by omega) h₂⟩

/-! ## §3d One slot -/

/-- The mark the program tests, as a statement about the prefix. -/
theorem mem_rowKept {x : List ℕ} {i j v : ℕ} : v ∈ rowKept x i j ↔ v ∈ rowPfx x i j :=
  mem_firstDedup

theorem mark_test_row (x : List ℕ) (i j : ℕ) :
    (0 < (if target x j ∈ rowKept x i j then 1 else 0)) ↔ target x j ∈ rowPfx x i j :=
  mark_test _ _

set_option maxHeartbeats 1000000 in
/-- **One slot.** A target the row has already named is skipped; a new
one is marked, published at the write pointer, and the pointer moves.
The step on the list side is `firstDedup_concat`, read on the marks by
`mark_step` and tested by `mark_test`. -/
theorem dedupSlot_run {B ns W i : ℕ} {T : ℕ → ℕ} {x : List ℕ}
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hT : ∀ j < ns, T j = target x j)
    (hnB : n + 1 < B) (hnsB : ns < B) (hnsW : ns ≤ W) (hi : i < n)
    {σ : Env} (hI : DedupInner x n ns W T i σ) (hjlt : σ.vars "dj" < offset x (i + 1)) :
    ∃ σ' K, Run B dedupSlot σ σ' K ∧ K ≤ 22 ∧
      DedupInner x n ns W T i σ' ∧ σ'.vars "dj" = σ.vars "dj" + 1 := by
  classical
  obtain ⟨hj₁, hj₂, hdi, hn, hdq, hde, hds, hdw, hoff, hdmk, F, hF, hlo, hhi⟩ := hI
  have hts : TgtSplit x W T (dedupOffset x i + (rowKept x i (σ.vars "dj")).length)
      (σ.vars "dj") σ := ⟨F, hF, hlo, hhi⟩
  have hend : offset x (i + 1) ≤ ns := by
    rw [hns, ← hx.offset_last]
    exact RamBfs.offset_mono' hx (by omega) le_rfl
  have hjns : σ.vars "dj" < ns := by omega
  have hvn : target x (σ.vars "dj") < n := target_lt_of_row hx hi hj₁ hjlt
  have hwr : dedupOffset x i + (rowKept x i (σ.vars "dj")).length ≤ σ.vars "dj" :=
    write_le_read hx (by omega) hj₁
  have hFj : F (σ.vars "dj") = target x (σ.vars "dj") :=
    (hhi _ le_rfl (by omega)).trans (hT _ hjns)
  have htgtLen : σ.vars "dj" < (σ.arrs "tgt").length := by rw [hF, length_arrOf]; omega
  have htv : (σ.arrs "tgt").getD (σ.vars "dj") 0 = target x (σ.vars "dj") := by
    rw [hF, getD_arrOf F (by omega), hFj]
  have htvB : (σ.arrs "tgt").getD (σ.vars "dj") 0 < B := by rw [htv]; omega
  have hdwLen : σ.vars "dw" < (σ.arrs "tgt").length := by rw [hdw, hF, length_arrOf]; omega
  have hdwB : σ.vars "dw" + 1 < B := by rw [hdw]; omega
  have hjB : σ.vars "dj" + 1 < B := by omega
  -- the mark, read in the environment the branch tests it in
  have hvdv : (σ.setVar "dv" ((σ.arrs "tgt").getD (σ.vars "dj") 0)).vars "dv"
      = target x (σ.vars "dj") := by rw [vars_setVar, if_pos rfl, htv]
  have hdmkLen : ((σ.setVar "dv" ((σ.arrs "tgt").getD (σ.vars "dj") 0)).vars "dv")
      < ((σ.setVar "dv" ((σ.arrs "tgt").getD (σ.vars "dj") 0)).arrs "dmk").length := by
    rw [arrs_setVar, hvdv, hdmk, length_arrOf]; exact hvn
  have hdmkGet : ((σ.setVar "dv" ((σ.arrs "tgt").getD (σ.vars "dj") 0)).arrs "dmk").getD
      ((σ.setVar "dv" ((σ.arrs "tgt").getD (σ.vars "dj") 0)).vars "dv") 0
      = if target x (σ.vars "dj") ∈ rowPfx x i (σ.vars "dj") then 1 else 0 := by
    rw [arrs_setVar, hvdv, hdmk, getD_arrOf _ hvn]
    simp only [mem_rowKept]
  have hdmkGetB : ((σ.setVar "dv" ((σ.arrs "tgt").getD (σ.vars "dj") 0)).arrs "dmk").getD
      ((σ.setVar "dv" ((σ.arrs "tgt").getD (σ.vars "dj") 0)).vars "dv") 0 < B := by
    rw [hdmkGet]; split <;> omega
  run_vcg
  · -- the row has already named this target: the slot is passed over
    by_cases hin : target x (σ.vars "dj") ∈ rowPfx x i (σ.vars "dj")
    · have hkeep : rowKept x i (σ.vars "dj" + 1) = rowKept x i (σ.vars "dj") := by
        rw [rowKept_succ hj₁, if_pos hin]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
      · show offset x i ≤ σ.vars "dj" + 1
        omega
      · show σ.vars "dj" + 1 ≤ offset x (i + 1)
        omega
      · exact hdi
      · exact hn
      · exact hdq
      · exact hde
      · exact hds
      · show σ.vars "dw" = dedupOffset x i + (rowKept x i (σ.vars "dj" + 1)).length
        rw [hkeep]; exact hdw
      · exact hoff
      · show σ.arrs "dmk"
          = arrOf n (fun v => if v ∈ rowKept x i (σ.vars "dj" + 1) then 1 else 0)
        rw [hkeep]; exact hdmk
      · refine tgtSplit_of hts rfl ?_ ?_
        · show dedupOffset x i + (rowKept x i (σ.vars "dj" + 1)).length
              ≤ dedupOffset x i + (rowKept x i (σ.vars "dj")).length
          rw [hkeep]
        · show σ.vars "dj" ≤ σ.vars "dj" + 1
          omega
    · exfalso; rw [if_neg hin] at hdmkGet; omega
  · -- a new target: marked, published, and the write pointer moves
    by_cases hin : target x (σ.vars "dj") ∈ rowPfx x i (σ.vars "dj")
    · exfalso; rw [if_pos hin] at hdmkGet; omega
    · have hkeep : rowKept x i (σ.vars "dj" + 1)
          = rowKept x i (σ.vars "dj") ++ [target x (σ.vars "dj")] := by
        rw [rowKept_succ hj₁, if_neg hin]
      have hmk : (fun w => if w ∈ rowKept x i (σ.vars "dj" + 1) then 1 else 0)
          = upd (fun w => if w ∈ rowKept x i (σ.vars "dj") then 1 else 0)
              (target x (σ.vars "dj")) 1 := by
        have h := mark_step (rowPfx x i (σ.vars "dj")) (target x (σ.vars "dj"))
        rw [if_neg hin] at h
        rw [show rowKept x i (σ.vars "dj" + 1)
              = firstDedup (rowPfx x i (σ.vars "dj") ++ [target x (σ.vars "dj")]) by
            rw [rowKept, rowPfx_succ hj₁]]
        exact h
      have ht : (rowKept x i (σ.vars "dj")).length < (rowKept x i (σ.vars "dj" + 1)).length := by
        rw [hkeep]; simp
      have hcell : dedupTarget x (σ.vars "dw") = target x (σ.vars "dj") := by
        rw [hdw, dedupTarget_rowKept hx hi (j := σ.vars "dj" + 1) (by omega) (by omega) ht,
          hkeep]
        simp
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
      · show offset x i ≤ σ.vars "dj" + 1
        omega
      · show σ.vars "dj" + 1 ≤ offset x (i + 1)
        omega
      · exact hdi
      · exact hn
      · exact hdq
      · exact hde
      · exact hds
      · show σ.vars "dw" + 1 = dedupOffset x i + (rowKept x i (σ.vars "dj" + 1)).length
        rw [hkeep]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · exact hoff
      · show (σ.arrs "dmk").set ((σ.arrs "tgt").getD (σ.vars "dj") 0) 1
          = arrOf n (fun v => if v ∈ rowKept x i (σ.vars "dj" + 1) then 1 else 0)
        rw [htv, hdmk, set_arrOf_eq_upd, hmk]
      · refine ⟨upd F (σ.vars "dw") (target x (σ.vars "dj")), ?_, ?_, ?_⟩
        · show (σ.arrs "tgt").set (σ.vars "dw") ((σ.arrs "tgt").getD (σ.vars "dj") 0)
            = arrOf W (upd F (σ.vars "dw") (target x (σ.vars "dj")))
          rw [htv, hF, set_arrOf_eq_upd]
        · show ∀ j < dedupOffset x i + (rowKept x i (σ.vars "dj" + 1)).length,
            upd F (σ.vars "dw") (target x (σ.vars "dj")) j = dedupTarget x j
          rw [hkeep]
          simp only [List.length_append, List.length_cons, List.length_nil]
          intro j hj
          rcases Nat.lt_or_ge j (σ.vars "dw") with h | h
          · rw [upd_of_ne _ (by omega)]; exact hlo j (by omega)
          · rw [show j = σ.vars "dw" by omega, upd_self, hcell]
        · show ∀ j, σ.vars "dj" + 1 ≤ j → j < W →
            upd F (σ.vars "dw") (target x (σ.vars "dj")) j = T j
          intro j h₁ h₂
          rw [upd_of_ne _ (by omega)]
          exact hhi j (by omega) h₂
  · rw [vars_setArr, hvdv]; omega

/-! ## §3e One step of the trail -/

set_option maxHeartbeats 1000000 in
/-- **One step of the trail walk.** The mark of the `t`-th kept target is
cleared, and — `unmark_step`, where the compaction's `Nodup` earns its
keep — no mark that is still standing is cleared with it. -/
theorem dedupUnmark_run {B ns W i : ℕ} {T : ℕ → ℕ} {x : List ℕ}
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hnB : n + 1 < B) (hnsB : ns < B) (hnsW : ns ≤ W) (hi : i < n)
    {σ : Env} (hI : DedupUnmk x n ns W T i σ)
    (hklt : σ.vars "dk" < dedupOffset x (i + 1)) :
    ∃ σ' K, Run B dedupUnmark σ σ' K ∧ K ≤ 8 ∧
      DedupUnmk x n ns W T i σ' ∧ σ'.vars "dk" = σ.vars "dk" + 1 := by
  classical
  obtain ⟨hk₁, hk₂, hdi, hn, hdq, hdw, hoff, hdmk, F, hF, hlo, hhi⟩ := hI
  have hdo : dedupOffset x (i + 1) = dedupOffset x i + (keepList x i).length :=
    dedupOffset_succ x i
  have hnsle : dedupNs x ≤ ns := by
    rw [hns]
    exact dedupNs_le hx.vertexCount_eq hx.offset_zero hx.offset_last hx.offset_mono
  have hle : dedupOffset x (i + 1) ≤ dedupNs x :=
    dedupOffset_le_dedupNs x (by rw [hx.vertexCount_eq]; omega)
  have htlen : σ.vars "dk" - dedupOffset x i < (keepList x i).length := by omega
  have hval : F (σ.vars "dk") = (keepList x i).getD (σ.vars "dk" - dedupOffset x i) 0 := by
    rw [hlo _ (by omega)]
    conv_lhs => rw [show σ.vars "dk" = dedupOffset x i + (σ.vars "dk" - dedupOffset x i) by omega]
    exact dedupTarget_eq (by rw [hx.vertexCount_eq]; exact hi) htlen
  have hmem : (keepList x i).getD (σ.vars "dk" - dedupOffset x i) 0 ∈ keepList x i := by
    rw [List.getD_eq_getElem _ _ htlen]; exact List.getElem_mem htlen
  have hvn : (keepList x i).getD (σ.vars "dk" - dedupOffset x i) 0 < n :=
    mem_keepList_lt hx hi hmem
  have htgtLen : σ.vars "dk" < (σ.arrs "tgt").length := by rw [hF, length_arrOf]; omega
  have htv : (σ.arrs "tgt").getD (σ.vars "dk") 0
      = (keepList x i).getD (σ.vars "dk" - dedupOffset x i) 0 := by
    rw [hF, getD_arrOf F (by omega), hval]
  have htvB : (σ.arrs "tgt").getD (σ.vars "dk") 0 < B := by rw [htv]; omega
  have hdmkLen : (σ.arrs "tgt").getD (σ.vars "dk") 0 < (σ.arrs "dmk").length := by
    rw [htv, hdmk, length_arrOf]; exact hvn
  have hkB : σ.vars "dk" + 1 < B := by omega
  run_vcg
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · show dedupOffset x i ≤ σ.vars "dk" + 1
    omega
  · show σ.vars "dk" + 1 ≤ dedupOffset x (i + 1)
    omega
  · exact hdi
  · exact hn
  · exact hdq
  · exact hdw
  · exact hoff
  · show (σ.arrs "dmk").set ((σ.arrs "tgt").getD (σ.vars "dk") 0) 0
      = arrOf n (fun v =>
          if v ∈ (keepList x i).drop (σ.vars "dk" + 1 - dedupOffset x i) then 1 else 0)
    rw [htv, hdmk, set_arrOf_eq_upd,
      show σ.vars "dk" + 1 - dedupOffset x i = (σ.vars "dk" - dedupOffset x i) + 1 by omega,
      ← unmark_step (nodup_keepList x i) htlen]
  · exact tgtSplit_of ⟨F, hF, hlo, hhi⟩ rfl le_rfl le_rfl

/-! ## §3f One row -/

set_option maxHeartbeats 1000000 in
/-- **One row.** The bounds are read, the new offset published, the block
compacted by the kit's row scan, and the marks the row set are cleared by
walking the slots the row wrote — never the whole mark array, which is
what keeps the pass at `O(n + ns)`. -/
theorem dedupRow_run {B ns W i : ℕ} {T : ℕ → ℕ} {x : List ℕ}
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hT : ∀ j < ns, T j = target x j)
    (hnB : n + 1 < B) (hnsB : ns < B) (hnsW : ns ≤ W) (hi : i < n)
    {σ : Env} (hI : DedupOuter x n ns W T σ) (hiv : σ.vars "di" = i) :
    ∃ σ' K, Run B dedupRow σ σ' K ∧
      K ≤ 26 * (offset x (i + 1) - offset x i)
        + 12 * (dedupOffset x (i + 1) - dedupOffset x i) + 27 ∧
      DedupOuter x n ns W T σ' ∧ σ'.vars "di" = i + 1 := by
  classical
  obtain ⟨hile, hn, hdq, hdw, hoff, hdmk, hts⟩ := hI
  rw [hiv] at hile hdw hoff hts
  have hend : offset x (i + 1) ≤ ns := by
    rw [hns, ← hx.offset_last]
    exact RamBfs.offset_mono' hx (by omega) le_rfl
  have hmono : offset x i ≤ offset x (i + 1) := hx.offset_mono i hi
  have hdolt : dedupOffset x i ≤ offset x i :=
    dedupOffset_le_offset hx.vertexCount_eq hx.offset_zero hx.offset_mono i (by omega)
  have hdosucc : dedupOffset x (i + 1) = dedupOffset x i + (keepList x i).length :=
    dedupOffset_succ x i
  have hnsle : dedupNs x ≤ ns := by
    rw [hns]
    exact dedupNs_le hx.vertexCount_eq hx.offset_zero hx.offset_last hx.offset_mono
  have hdole : dedupOffset x (i + 1) ≤ dedupNs x :=
    dedupOffset_le_dedupNs x (by rw [hx.vertexCount_eq]; omega)
  -- the slot loop, and the trail loop, as the kit's row scan
  have hscan : Spec B
      (fun τ => DedupInner x n ns W T i τ ∧ τ.vars "dj" = offset x i)
      (.while (.lt (.var "dj") (.var "de")) dedupSlot)
      (fun _ τ' => DedupInner x n ns W T i τ' ∧ τ'.vars "dj" = offset x (i + 1))
      (26 * (offset x (i + 1) - offset x i) + 4) :=
    Csr.rowScan_spec B (26 * (offset x (i + 1) - offset x i) + 4) (offset x (i + 1)) 22
      "dj" "de" dedupSlot (DedupInner x n ns W T i) (by omega)
      (fun τ hτ => ⟨hτ.2.2.2.2.2.1, hτ.2.1⟩)
      (fun τ hτ hlt => by
        obtain ⟨τ', K', hr, hK', hI', hj'⟩ :=
          dedupSlot_run hx hns hT hnB hnsB hnsW hi hτ hlt
        exact ⟨τ', K', hr, hI', hj', hK'⟩)
      (fun _ hτ => hτ.1) (fun τ hτ => le_of_eq (by rw [hτ.2]))
  have hunmk : Spec B
      (fun τ => DedupUnmk x n ns W T i τ ∧ τ.vars "dk" = dedupOffset x i)
      (.while (.lt (.var "dk") (.var "dw")) dedupUnmark)
      (fun _ τ' => DedupUnmk x n ns W T i τ' ∧ τ'.vars "dk" = dedupOffset x (i + 1))
      (12 * (dedupOffset x (i + 1) - dedupOffset x i) + 4) :=
    Csr.rowScan_spec B (12 * (dedupOffset x (i + 1) - dedupOffset x i) + 4)
      (dedupOffset x (i + 1)) 8 "dk" "dw" dedupUnmark (DedupUnmk x n ns W T i) (by omega)
      (fun τ hτ => ⟨hτ.2.2.2.2.2.1, hτ.2.1⟩)
      (fun τ hτ hlt => by
        obtain ⟨τ', K', hr, hK', hI', hk'⟩ :=
          dedupUnmark_run hx hns hnB hnsB hnsW hi hτ hlt
        exact ⟨τ', K', hr, hI', hk', hK'⟩)
      (fun _ hτ => hτ.1) (fun τ hτ => le_of_eq (by rw [hτ.2]))
  -- the four reads and the one store the row does itself
  have hoffLen : (σ.arrs "off").length = n + 1 := by rw [hoff, length_arrOf]
  have hoffi : (σ.arrs "off").getD (σ.vars "di") 0 = offset x i := by
    rw [hiv, hoff, getD_arrOf _ (by omega)]; simp
  have hoffi1 : (σ.arrs "off").getD (σ.vars "di" + 1) 0 = offset x (i + 1) := by
    rw [hiv, hoff, getD_arrOf _ (by omega)]; simp
  have hdiLen : σ.vars "di" < (σ.arrs "off").length := by rw [hoffLen, hiv]; omega
  have hdi1Len : σ.vars "di" + 1 < (σ.arrs "off").length := by rw [hoffLen, hiv]; omega
  have hdiB : σ.vars "di" + 1 < B := by rw [hiv]; omega
  have hdwB : σ.vars "dw" < B := by rw [hdw]; omega
  run_vcg [hscan, hunmk]
  -- the row closes: the marks are clean again and the next row's offset stands
  · obtain ⟨hIu, hku⟩ := ‹DedupUnmk x n ns W T i _ ∧ _›
    obtain ⟨-, -, hdi', hn', hdq', hdw', hoff', hdmk', hts'⟩ := hIu
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [vars_setVar, reduceIte, hdi']; omega
    · simp only [vars_setVar]; exact hn'
    · simp only [vars_setVar]; exact hdq'
    · simp only [vars_setVar, reduceIte, hdi']; exact hdw'
    · simp only [arrs_setVar, vars_setVar, reduceIte, hdi']; exact hoff'
    · simp only [arrs_setVar]
      rw [hdmk', hku,
        show dedupOffset x (i + 1) - dedupOffset x i = (keepList x i).length by omega]
      exact congrArg (arrOf n) (drop_len_marks (keepList x i))
    · simp only [vars_setVar, reduceIte, hdi']
      exact tgtSplit_of hts' rfl le_rfl le_rfl
    · simp only [vars_setVar, reduceIte, hdi']
  -- the second offset read is a word
  · show (σ.arrs "off").getD (σ.vars "di" + 1) 0 < B
    rw [hoffi1]; omega
  -- the slot loop starts at the top of the row, with nothing kept yet
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show offset x i ≤ (σ.arrs "off").getD (σ.vars "di") 0
      rw [hoffi]
    · show (σ.arrs "off").getD (σ.vars "di") 0 ≤ offset x (i + 1)
      rw [hoffi]; omega
    · show σ.vars "di" = i
      exact hiv
    · exact hn
    · exact hdq
    · show (σ.arrs "off").getD (σ.vars "di" + 1) 0 = offset x (i + 1)
      exact hoffi1
    · show σ.vars "dw" = dedupOffset x i
      exact hdw
    · show σ.vars "dw"
        = dedupOffset x i + (rowKept x i ((σ.arrs "off").getD (σ.vars "di") 0)).length
      rw [hoffi, rowKept_start]; simpa using hdw
    · show (σ.arrs "off").set (σ.vars "di") (σ.vars "dw")
        = arrOf (n + 1) (fun k => if k < i + 1 then dedupOffset x k else offset x k)
      rw [hiv, hdw, hoff, set_arrOf_eq_upd]
      refine arrOf_congr (fun k _ => ?_)
      rcases eq_or_ne k i with rfl | hne
      · simp [upd]
      · rw [upd_of_ne _ hne]
        by_cases hki : k < i
        · simp [hki, show k < i + 1 by omega]
        · simp [hki, show ¬ (k < i + 1) by omega]
    · show σ.arrs "dmk"
        = arrOf n (fun v =>
            if v ∈ rowKept x i ((σ.arrs "off").getD (σ.vars "di") 0) then 1 else 0)
      rw [hoffi, rowKept_start]; simpa using hdmk
    · refine tgtSplit_of hts rfl ?_ ?_
      · show dedupOffset x i + (rowKept x i ((σ.arrs "off").getD (σ.vars "di") 0)).length
            ≤ dedupOffset x i
        rw [hoffi, rowKept_start]; simp
      · show offset x i ≤ (σ.arrs "off").getD (σ.vars "di") 0
        rw [hoffi]
    · show (σ.arrs "off").getD (σ.vars "di") 0 = offset x i
      exact hoffi
  -- the trail's start pointer is a word
  · obtain ⟨hIs, -⟩ := ‹DedupInner x n ns W T i _ ∧ _›
    rw [hIs.2.2.2.2.2.2.1]; omega
  -- the trail starts at the row's own first written slot
  · obtain ⟨hIs, hjs⟩ := ‹DedupInner x n ns W T i _ ∧ _›
    obtain ⟨-, -, hdi', hn', hdq', -, hds', hdw', hoff', hdmk', hts'⟩ := hIs
    rw [hjs, rowKept_end] at hdw' hdmk' hts'
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [vars_setVar, reduceIte, hds']; omega
    · simp only [vars_setVar, reduceIte, hds']; omega
    · simp only [vars_setVar]; exact hdi'
    · simp only [vars_setVar]; exact hn'
    · simp only [vars_setVar]; exact hdq'
    · exact hdw'.trans hdosucc.symm
    · simp only [arrs_setVar]; exact hoff'
    · simp only [arrs_setVar, vars_setVar, reduceIte, hds', Nat.sub_self, List.drop_zero]
      exact hdmk'
    · refine tgtSplit_of hts' rfl (le_of_eq ?_) le_rfl
      omega
    · simp only [vars_setVar, reduceIte, hds']
  -- the row counter is a word, before and after
  · obtain ⟨hIu, -⟩ := ‹DedupUnmk x n ns W T i _ ∧ _›
    rw [hIu.2.2.1]; omega
  · obtain ⟨hIu, -⟩ := ‹DedupUnmk x n ns W T i _ ∧ _›
    rw [hIu.2.2.1]; omega

/-! ## §3g Every row

The pass is amortized, not counted: a turn costs the length of the row it
walks plus the length of the row it keeps, and the rows tile the two
arrays, so the potential is "so much per row left, so much per slot
left, so much per kept slot left" and the whole sweep is linear. -/

set_option maxHeartbeats 1000000 in
/-- **Every row compacted.** -/
theorem dedupRows_spec {B ns W : ℕ} {T : ℕ → ℕ} {x : List ℕ}
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hT : ∀ j < ns, T j = target x j)
    (hnB : n + 1 < B) (hnsB : ns < B) (hnsW : ns ≤ W) :
    Spec B (DedupOuter x n ns W T)
      (.while (.lt (.var "di") (.var "n")) dedupRow)
      (fun _ σ' => DedupOuter x n ns W T σ' ∧ σ'.vars "di" = n)
      (31 * n + 26 * ns + 12 * dedupNs x + 4) := by
  refine (Spec.while_potential (DedupOuter x n ns W T)
    (fun σ => 31 * (n - σ.vars "di") + 26 * (ns - offset x (σ.vars "di"))
      + 12 * (dedupNs x - dedupOffset x (σ.vars "di")))
    (fun σ hσ => evalB_condLt_vars (by have := hσ.1; omega) (by rw [hσ.2.1]; omega))
    (fun σ hσ hb => ?_) (fun _ h => h)
    (fun σ _ => by simp only [size_condLt, size_var]; omega)).post (fun _ σ' _ hQ => ?_)
  · have hlt : σ.vars "di" < n := by
      have h := lt_of_condLt_true hb
      rw [hσ.2.1] at h; exact h
    obtain ⟨σ', K, hrun, hK, hI', hi'⟩ := dedupRow_run hx hns hT hnB hnsB hnsW hlt hσ rfl
    refine ⟨σ', K, hrun, hI', ?_⟩
    have h₁ : offset x (σ.vars "di") ≤ offset x (σ.vars "di" + 1) := hx.offset_mono _ hlt
    have h₂ : offset x (σ.vars "di" + 1) ≤ ns := by
      rw [hns, ← hx.offset_last]
      exact RamBfs.offset_mono' hx (by omega) le_rfl
    have h₃ : dedupOffset x (σ.vars "di") ≤ dedupOffset x (σ.vars "di" + 1) :=
      dedupOffset_mono' x (Nat.le_succ _)
    have h₄ : dedupOffset x (σ.vars "di" + 1) ≤ dedupNs x :=
      dedupOffset_le_dedupNs x (by rw [hx.vertexCount_eq]; omega)
    simp only [size_condLt, size_var, hi']
    omega
  · refine ⟨hQ.1, ?_⟩
    have h₀ := le_of_condLt_false hQ.2
    have h₁ := hQ.1.1
    have h₂ := hQ.1.2.1
    omega

/-! ## §3h The tail: the freed cells, and the exported scalar -/

/-- The invariant of the zeroing loop. The cells the compaction freed are
zeroed from the compacted count up to the *old* one; above the old count
the tail is the decode's own, and the pass never goes there. -/
def DedupZero (x : List ℕ) (n ns W : ℕ) (T : ℕ → ℕ) (σ : Env) : Prop :=
  dedupNs x ≤ σ.vars "dk" ∧ σ.vars "dk" ≤ ns ∧
    σ.vars "n" = n ∧ σ.vars "dq" = ns ∧ σ.vars "dw" = dedupNs x ∧
    σ.arrs "off" = arrOf (n + 1) (dedupOffset x) ∧
    σ.arrs "dmk" = arrOf n (fun _ => 0) ∧
    (∃ F, σ.arrs "tgt" = arrOf W F ∧
      (∀ j < σ.vars "dk", F j = dedupTarget x j) ∧
      (∀ j, ns ≤ j → j < W → F j = T j))

/-- The invariant of the halving loop: the counter is twice the scalar
the driver's calling convention wants back. -/
def DedupHalve (x : List ℕ) (n W : ℕ) (σ : Env) : Prop :=
  σ.vars "dk" = σ.vars "m" + σ.vars "m" ∧ σ.vars "dk" ≤ dedupNs x ∧
    σ.vars "dw" = dedupNs x ∧ σ.vars "n" = n ∧
    σ.arrs "off" = arrOf (n + 1) (dedupOffset x) ∧
    σ.arrs "dmk" = arrOf n (fun _ => 0) ∧
    σ.arrs "tgt" = arrOf W (dedupTarget x)

set_option maxHeartbeats 1000000 in
/-- One freed cell, zeroed. -/
theorem dedupZeroStep_run {B ns W : ℕ} {T : ℕ → ℕ} {x : List ℕ}
    (hnsB : ns < B) (hnsW : ns ≤ W)
    {σ : Env} (hI : DedupZero x n ns W T σ) (hklt : σ.vars "dk" < ns) :
    ∃ σ' K, Run B (.seq (.store "tgt" (.var "dk") (.lit 0))
        (.assign "dk" (.add (.var "dk") (.lit 1)))) σ σ' K ∧ K ≤ 7 ∧
      DedupZero x n ns W T σ' ∧ σ'.vars "dk" = σ.vars "dk" + 1 := by
  obtain ⟨hk₁, hk₂, hn, hdq, hdw, hoff, hdmk, F, hF, hlo, hhi⟩ := hI
  have htgtLen : σ.vars "dk" < (σ.arrs "tgt").length := by rw [hF, length_arrOf]; omega
  have hkB : σ.vars "dk" + 1 < B := by omega
  run_vcg
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · show dedupNs x ≤ σ.vars "dk" + 1
    omega
  · show σ.vars "dk" + 1 ≤ ns
    omega
  · exact hn
  · exact hdq
  · exact hdw
  · exact hoff
  · exact hdmk
  · refine ⟨upd F (σ.vars "dk") 0, ?_, ?_, ?_⟩
    · show (σ.arrs "tgt").set (σ.vars "dk") 0 = arrOf W (upd F (σ.vars "dk") 0)
      rw [hF, set_arrOf_eq_upd]
    · show ∀ j < σ.vars "dk" + 1, upd F (σ.vars "dk") 0 j = dedupTarget x j
      intro j hj
      rcases Nat.lt_or_ge j (σ.vars "dk") with h | h
      · rw [upd_of_ne _ (by omega)]; exact hlo j h
      · rw [show j = σ.vars "dk" by omega, upd_self,
          dedupTarget_eq_zero (by omega)]
    · show ∀ j, ns ≤ j → j < W → upd F (σ.vars "dk") 0 j = T j
      intro j h₁ h₂
      rw [upd_of_ne _ (by omega)]
      exact hhi j h₁ h₂

/-- The pass's own cost: one turn per row, one per slot read, one per
slot written, one per freed cell, and one per two compacted slots. The
constants are **the walk's**, and `dedup_spec` is what pins them: the
sweep pays `31` a row and `26` a slot, the trail `12` a kept slot, the
zeroing `11` a freed cell and the halving `12` per two — and since the
kept slots and the freed cells together are the old slots, that is
`31·n + 50·ns + 29`. The shape — linear in `n` and the *old* slot
count, with no `n · ns` term — is what the touched-only discipline of
the trail buys and what the C0 budget needs. -/
def dedupCost (n ns : ℕ) : ℕ := 31 * n + 50 * ns + 29

set_option maxHeartbeats 1000000 in
/-- **The pass.** The rows are compacted, the last offset published, the
freed cells zeroed, and the compacted count halved into the scalar the
driver's calling convention carries. -/
theorem dedup_spec {B ns W : ℕ} {T : ℕ → ℕ} {x : List ℕ}
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hT : ∀ j < ns, T j = target x j) (hpad : ∀ z, ns ≤ z → z < W → T z = 0)
    (hnB : n + 1 < B) (hnsB : ns < B) (hWB : W < B) (hnsW : ns ≤ W) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.vars "m" + σ.vars "m" = ns ∧
        σ.arrs "off" = arrOf (n + 1) (offset x) ∧ σ.arrs "tgt" = arrOf W T ∧
        DedupMem n σ)
      dedupCom
      (fun _ σ' => σ'.vars "n" = n ∧ σ'.vars "m" + σ'.vars "m" = dedupNs x ∧
        σ'.arrs "off" = arrOf (n + 1) (dedupOffset x) ∧
        σ'.arrs "tgt" = arrOf W (dedupTarget x) ∧ DedupMem n σ')
      (dedupCost n ns) := by
  classical
  have hnsle : dedupNs x ≤ ns := by
    rw [hns]
    exact dedupNs_le hx.vertexCount_eq hx.offset_zero hx.offset_last hx.offset_mono
  obtain ⟨e, he⟩ := dedupNs_even hx
  have hdns : dedupOffset x n = dedupNs x := by rw [dedupNs, hx.vertexCount_eq]
  have hlast : offset x n = ns := by rw [hx.offset_last, hns]
  have hrows := dedupRows_spec hx hns hT hnB hnsB hnsW
  have hzero : Spec B (fun τ => DedupZero x n ns W T τ ∧ τ.vars "dk" = dedupNs x)
      (.while (.lt (.var "dk") (.var "dq"))
        (.seq (.store "tgt" (.var "dk") (.lit 0))
          (.assign "dk" (.add (.var "dk") (.lit 1)))))
      (fun _ τ' => DedupZero x n ns W T τ' ∧ τ'.vars "dk" = ns)
      (11 * (ns - dedupNs x) + 4) :=
    Csr.rowScan_spec B (11 * (ns - dedupNs x) + 4) ns 7 "dk" "dq" _
      (DedupZero x n ns W T) (by omega)
      (fun τ hτ => ⟨hτ.2.2.2.1, hτ.2.1⟩)
      (fun τ hτ hlt => by
        obtain ⟨τ', K', hr, hK', hI', hk'⟩ := dedupZeroStep_run hnsB hnsW hτ hlt
        exact ⟨τ', K', hr, hI', hk', hK'⟩)
      (fun _ hτ => hτ.1) (fun τ hτ => le_of_eq (by rw [hτ.2]))
  have hhbody : Spec B
      (fun τ => DedupHalve x n W τ ∧
        (Cond.lt (Expr.var "dk") (Expr.var "dw")).evalB B τ = some true)
      (.seq (.assign "dk" (.add (.var "dk") (.lit 2)))
        (.assign "m" (.add (.var "m") (.lit 1))))
      (fun τ τ' => DedupHalve x n W τ' ∧
        dedupNs x - τ'.vars "dk" < dedupNs x - τ.vars "dk") 8 := by
    refine Spec.of_exists (fun τ hτ => ?_)
    obtain ⟨⟨hdk, hkle, hdw, hn', hoff', hdmk', htgt'⟩, hb⟩ := hτ
    have hlt : τ.vars "dk" < dedupNs x := by
      have h := lt_of_condLt_true hb; rw [hdw] at h; exact h
    have hkB : τ.vars "dk" + 2 < B := by omega
    have hmB : τ.vars "m" + 1 < B := by omega
    run_vcg
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show τ.vars "dk" + 2 = (τ.vars "m" + 1) + (τ.vars "m" + 1)
      omega
    · show τ.vars "dk" + 2 ≤ dedupNs x
      omega
    · exact hdw
    · exact hn'
    · exact hoff'
    · exact hdmk'
    · exact htgt'
    · show dedupNs x - (τ.vars "dk" + 2) < dedupNs x - τ.vars "dk"
      omega
  have hhalve : Spec B (DedupHalve x n W)
      (.while (.lt (.var "dk") (.var "dw"))
        (.seq (.assign "dk" (.add (.var "dk") (.lit 2)))
          (.assign "m" (.add (.var "m") (.lit 1)))))
      (fun _ τ' => DedupHalve x n W τ' ∧
        (Cond.lt (Expr.var "dk") (Expr.var "dw")).evalB B τ' = some false)
      (12 * dedupNs x + 4) :=
    Spec.while_count (DedupHalve x n W) (fun τ => dedupNs x - τ.vars "dk") 8
      (fun τ hτ => evalB_condLt_vars (by have := hτ.2.1; omega) (by rw [hτ.2.2.1]; omega))
      hhbody (fun _ h => h)
      (fun τ hτ => by simp only [size_condLt, size_var]; have := hτ.2.1; omega)
  have hcost : dedupCost n ns = 31 * n + 50 * ns + 29 := rfl
  run_vcg [hrows, hzero, hhalve]
  -- the exported scalar is the compacted count, halved
  · obtain ⟨hIh, hfalse⟩ := ‹DedupHalve x n W _ ∧ _›
    obtain ⟨hdk, hkle, hdw, hn', hoff', hdmk', htgt'⟩ := hIh
    have hge := le_of_condLt_false hfalse
    exact ⟨hn', by omega, hoff', htgt', dedupMem_arrOf hdmk'⟩
  -- the row sweep starts with an empty compaction
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (0 : ℕ) ≤ n
      omega
    · exact ‹σ.vars "n" = n›
    · exact ‹σ.vars "m" + σ.vars "m" = ns›
    · show (0 : ℕ) = dedupOffset x 0
      rw [dedupOffset_zero]
    · show σ.arrs "off"
        = arrOf (n + 1) (fun k => if k < 0 then dedupOffset x k else offset x k)
      rw [‹σ.arrs "off" = arrOf (n + 1) (offset x)›]
      exact arrOf_congr (fun k _ => by simp)
    · exact dedupMem_eq ‹DedupMem n σ›
    · refine ⟨T, ‹σ.arrs "tgt" = arrOf W T›, ?_, fun j _ _ => rfl⟩
      show ∀ j < dedupOffset x 0, T j = dedupTarget x j
      rw [dedupOffset_zero]
      exact fun j hj => absurd hj (by omega)
  -- the three words the last store and the two tail loops read
  · obtain ⟨hIo, hdi⟩ := ‹DedupOuter x n ns W T _ ∧ _›
    rw [hIo.2.1]; omega
  · obtain ⟨hIo, hdi⟩ := ‹DedupOuter x n ns W T _ ∧ _›
    have h := hIo.2.2.2.1
    rw [hdi, hdns] at h
    rw [h]; omega
  · obtain ⟨hIo, hdi⟩ := ‹DedupOuter x n ns W T _ ∧ _›
    rw [hIo.2.2.2.2.1, length_arrOf, hIo.2.1]
    omega
  · obtain ⟨hIo, hdi⟩ := ‹DedupOuter x n ns W T _ ∧ _›
    have h := hIo.2.2.2.1
    rw [hdi, hdns] at h
    simp only [vars_setArr]
    rw [h]; omega
  -- the zeroing starts at the compacted count, with the last offset published
  · obtain ⟨hIo, hdi⟩ := ‹DedupOuter x n ns W T _ ∧ _›
    obtain ⟨-, hn', hdq', hdw', hoff', hdmk', F, hF, hlo, hhi⟩ := hIo
    rw [hdi] at hdw' hoff' hlo hhi
    rw [hdns] at hdw' hlo
    rw [hlast] at hhi
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact le_of_eq hdw'.symm
    · exact le_trans (le_of_eq hdw') hnsle
    · exact hn'
    · exact hdq'
    · exact hdw'
    · simp only [arrs_setVar, arrs_setArr, vars_setArr]
      rw [hn', hdw', hoff', set_arrOf_eq_upd]
      refine arrOf_congr (fun k hk => ?_)
      rcases eq_or_ne k n with rfl | hne
      · rw [upd_self, hdns]
      · rw [upd_of_ne _ hne, if_pos (by omega)]
    · exact hdmk'
    · exact ⟨F, hF, fun j hj => hlo j (by rw [← hdw']; exact hj), hhi⟩
    · exact hdw'
  -- the halving starts at zero, on the finished block structure
  · obtain ⟨hIz, hdkz⟩ := ‹DedupZero x n ns W T _ ∧ _›
    obtain ⟨-, -, hn', -, hdw', hoff', hdmk', F, hF, hlo, hhi⟩ := hIz
    rw [hdkz] at hlo
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (0 : ℕ) = 0 + 0
      omega
    · show (0 : ℕ) ≤ dedupNs x
      omega
    · exact hdw'
    · exact hn'
    · exact hoff'
    · exact hdmk'
    · simp only [arrs_setVar]
      rw [hF]
      refine arrOf_congr (fun k hk => ?_)
      rcases Nat.lt_or_ge k ns with h | h
      · exact hlo k h
      · rw [hhi k h hk, hpad k h hk, dedupTarget_eq_zero (by omega)]

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

**Status (rebase G1b).** The Prop is stated *and discharged*:
`decodeImplementsD` below closes it, composing
`RamDriverIO.decodeImplements` at the padded target function with
`dedup_spec` — the walk of §3c–§3h — as one run. `DecodeImplementsD` is
still a definition and not a theorem, exactly as
`RamDriver.DecodeImplements` is; the theorem that closes it is separate,
and carries the encoding hypothesis and the slot-count equation the
Prop's own statement cannot.

One ledger line on the shape. The parameter `T` is **vestigial**: it
occurs nowhere in the precondition, the program or the postcondition,
and only in the hypothesis `∀ z, ns ≤ z → z < W → T z = 0`, which the
discharger therefore does not use — the decode is instantiated at the
pass's own `padTarget`, whose pad clause holds by construction. The
parameter is kept so that the obligation reads at the same arity as
`RamDriver.DecodeImplements`, which B7's `obtain` pattern is written
against; nothing is weakened by it. -/

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

/-- The decode's own target function: the encoding's targets below the
declared slot count, and the zero pad above it. This is what the decode
leaves in `tgt`, and what the dedup pass is handed. -/
def padTarget (x : List ℕ) (ns : ℕ) (j : ℕ) : ℕ := if j < ns then target x j else 0

theorem padTarget_lt {x : List ℕ} {ns j : ℕ} (h : j < ns) :
    padTarget x ns j = target x j := by rw [padTarget, if_pos h]

theorem padTarget_ge {x : List ℕ} {ns j : ℕ} (h : ns ≤ j) :
    padTarget x ns j = 0 := by rw [padTarget, if_neg (by omega)]

/-- **The engines' scratch survives the pass.** Its `Sized` clause and
its two word clauses survive *any* run; its eight zeroing clauses survive
this one because the pass writes only `off`, `tgt` and its own marks. The
slot count may be replaced by any smaller one, since it occurs in the
clause only as `ns ≤ W`. -/
theorem orderMem_dedup {B ns ns' W : ℕ} {σ σ' : Env} {K : ℕ}
    (h : RamDriver.OrderMem B n ns W σ) (hr : Run B dedupCom σ σ' K) (hns' : ns' ≤ W) :
    RamDriver.OrderMem B n ns' W σ' := by
  obtain ⟨-, hlwv, hsz, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, hw₁, hw₂⟩ := h
  refine ⟨hns',
    by rw [frame_var_dedupCom hr "lw" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hlwv,
    hsz.run hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    RamDriver.run_mem_arrs_lt hr "itg" hw₁, RamDriver.run_mem_arrs_lt hr "ntg" hw₂⟩
  · rw [frame_arr_dedupCom hr "elm" (by decide) (by decide) (by decide)]; exact h₁
  · rw [frame_arr_dedupCom hr "bh" (by decide) (by decide) (by decide)]; exact h₂
  · rw [frame_arr_dedupCom hr "ooff" (by decide) (by decide) (by decide)]; exact h₃
  · rw [frame_arr_dedupCom hr "noff" (by decide) (by decide) (by decide)]; exact h₄
  · rw [frame_arr_dedupCom hr "stf" (by decide) (by decide) (by decide)]; exact h₅
  · rw [frame_arr_dedupCom hr "sta" (by decide) (by decide) (by decide)]; exact h₆
  · rw [frame_arr_dedupCom hr "std" (by decide) (by decide) (by decide)]; exact h₇
  · rw [frame_arr_dedupCom hr "ste" (by decide) (by decide) (by decide)]; exact h₈

set_option maxHeartbeats 1000000 in
/-- **The obligation, discharged.** The decode is
`RamDriverIO.decodeImplements` at the padded target function; the guard
is `dedup_spec`; and the two are one run. Everything the level below
reads that the pass does not write crosses on the frame. -/
theorem decodeImplementsD {B ns W K : ℕ} {T : ℕ → ℕ} {x : List ℕ}
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hK : RamDriverIO.decodeCost n ns + dedupCost n ns ≤ K) :
    DecodeImplementsD B x G ns W T K := by
  classical
  intro hxB hnB hnsB hWB hnsW _hpad0
  have hnsle : dedupNs x ≤ ns := by
    rw [hns]
    exact dedupNs_le hx.vertexCount_eq hx.offset_zero hx.offset_last hx.offset_mono
  have hTlo : ∀ j < ns, padTarget x ns j = target x j := fun _ hj => padTarget_lt hj
  have hThi : ∀ z, ns ≤ z → z < W → padTarget x ns z = 0 := fun _ h₁ _ => padTarget_ge h₁
  have hdec := (RamDriverIO.decodeImplements (B := B) (Ws := W) (O := offset x)
      (T := padTarget x ns) hx hns (fun _ _ => rfl) hTlo le_rfl)
    hxB hnB hnsB hWB hnsW hThi
  have hpass := dedup_spec (B := B) (T := padTarget x ns) hx hns hTlo hThi hnB hnsB hWB hnsW
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hmem, hord, hdmem, hinp, hout⟩ := hσ
  obtain ⟨σ₁, r₁, ho₁, hcsr₁, hn₁, hoff₁, htgt₁, hm₁, hord₁, hM, hGm⟩ :=
    hdec σ ⟨hmem, hord, hinp, hout⟩
  have hfr₁ : σ₁.arrs "dmk" = σ.arrs "dmk" := r₁.frame_arr "dmk" (by decide)
  have hdmem₁ : DedupMem n σ₁ :=
    ⟨by rw [hfr₁]; exact hdmem.1, by rw [hfr₁]; exact hdmem.2⟩
  obtain ⟨σ₂, r₂, hn₂, hm₂, hoff₂, htgt₂, hdmem₂⟩ :=
    hpass σ₁ ⟨hn₁, hm₁, hoff₁, htgt₁, hdmem₁⟩
  refine ⟨σ₂, _, r₁.seq r₂, hK, ?_, csrGraph_dedup hx, csrSimple_dedup hx, hnsle,
    fun z hz _ => dedupTarget_eq_zero hz, hn₂, hoff₂, htgt₂, hm₂,
    orderMem_dedup hord₁ r₂ (le_trans hnsle hnsW), hdmem₂, ?_, ?_⟩
  · rw [r₂.out_eq noWrite_dedupCom, ho₁]
  · obtain ⟨M, hMa, hMv⟩ := hM
    exact ⟨M, by rw [frame_arr_dedupCom r₂ (RamDriver.alvName 0)
      (by decide) (by decide) (by decide)]; exact hMa, hMv⟩
  · obtain ⟨Gm, hGa, hGv⟩ := hGm
    exact ⟨Gm, by rw [frame_arr_dedupCom r₂ (RamDriver.gamName 0)
      (by decide) (by decide) (by decide)]; exact hGa, hGv⟩

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
