import Lax3Proofs.RamDriverOrder

/-!
The **augmentation round's walk**: `Lax3Proofs.RamAugment.Implements`.

The round is ten passes and one call over three block structures, and
every one of the ten is built out of `RamAugment.blockScan` — load a
row's two bounds, walk its slots, do something with each target. So the
first section of this file is that combinator, walked once, in a form
that nests: the caller says what a slot does and what it is keeping
track of, and gets back the row, scanned, at a cost of so much per
slot.

The block structures the round walks are *not* `Lax13Proofs`'s `Csr`
relation. That relation couples the target array's length to the last
offset, and every array of this round is cut to a caller-chosen width
`W` with the slots it actually uses a data-dependent prefix — which is
the whole reason `RamAugment.AugPre` asks for its arrays at `W`. So the
row view here is `Blocks`, which is `RamElim.InCsr` with the graph
forgotten: offsets, targets, a slot count and a length, and nothing
tying the last two together.
-/

namespace Lax3Proofs.RamDriverAugment

open Lax3Proofs.Augmentation Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.RamElim (CsrSimple InCsr ElimCert ElimPre ElimMem elimCost elimCom)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ### The block scan

`RamAugment.blockScan o t x j jend w c` is `Csr.loadRow` followed by
`Csr.scan` over a body that reads the slot into `w`, runs `c` and steps
the pointer. The three lemmas here take it apart in that order. -/

/-- The body of `RamAugment.blockScan`: read the slot into `w`, run the
caller's command, step the pointer. -/
def scanBody (t j w : String) (c : Com) : Com :=
  .seq (.assign w (.get t (.var j))) (.seq c (.assign j (.add (.var j) (.lit 1))))

theorem blockScan_eq (o t x j jend w : String) (c : Com) :
    RamAugment.blockScan o t x j jend w c
      = .seq (Csr.loadRow o x j jend) (Csr.scan j jend (scanBody t j w c)) := rfl

/-- **One slot.** The read of the target and the step of the pointer are
the walk; what the caller's command did is its own business, and enters
as a `Run` it has already built. -/
theorem scanBody_run {B : ℕ} {t j w : String} {c : Com} {len K : ℕ} {tgt : ℕ → ℕ}
    {τ τ' : Env} (htgt : τ.arrs t = arrOf len tgt) (hjlen : τ.vars j < len)
    (hjB : τ.vars j + 1 < B) (htB : tgt (τ.vars j) < B) (hB1 : 1 < B)
    (hrun : Run B c (τ.setVar w (tgt (τ.vars j))) τ' K) (hjfix : τ'.vars j = τ.vars j) :
    Run B (scanBody t j w c) τ (τ'.setVar j (τ.vars j + 1)) (K + 7) := by
  have e₁ : (Expr.get t (.var j)).evalB B τ = some (tgt (τ.vars j)) :=
    evalB_get (evalB_var (by omega)) (by rw [htgt, getElem?_arrOf tgt hjlen]) htB
  have e₂ : (Expr.add (.var j) (.lit 1)).evalB B τ' = some (τ.vars j + 1) := by
    have h := evalB_bin (B := B) (op := .add) (σ := τ') (m := τ'.vars j) (n := 1)
      (evalB_var (by omega)) (evalB_lit hB1) (by rw [hjfix]; simpa [Bop.apply] using hjB)
    rw [hjfix] at h
    simpa [Bop.apply] using h
  refine ((Run.assign e₁).seq (hrun.seq (Run.assign e₂))).mono ?_
  simp only [size_get, size_var, size_add, size_lit]; omega

/-- **A row, scanned.** The caller's invariant holds at the loop head;
what the combinator supplies is the loop condition, the exit fact and
the cost — eleven plus the body's, per slot. -/
theorem rowScan_run {B : ℕ} {t j jend w : String} {c : Com} {len Kb hi : ℕ}
    {tgt : ℕ → ℕ} {I : Env → Prop} {σ : Env}
    (hhiB : hi < B) (hB1 : 1 < B) (hhilen : hi ≤ len)
    (htgt : ∀ τ, I τ → τ.arrs t = arrOf len tgt)
    (htB : ∀ p < hi, tgt p < B)
    (hIb : ∀ τ, I τ → τ.vars jend = hi ∧ τ.vars j ≤ hi)
    (hstep : ∀ τ, I τ → τ.vars j < hi →
      ∃ τ' K, Run B c (τ.setVar w (tgt (τ.vars j))) τ' K ∧ K ≤ Kb ∧
        τ'.vars j = τ.vars j ∧ I (τ'.setVar j (τ.vars j + 1)))
    (hI : I σ) :
    ∃ σ' K, Run B (Csr.scan j jend (scanBody t j w c)) σ σ' K ∧
      K ≤ (Kb + 11) * (hi - σ.vars j) + 4 ∧ I σ' ∧ σ'.vars j = hi := by
  have hstep' : ∀ τ, I τ → τ.vars j < hi →
      ∃ τ' K, Run B (scanBody t j w c) τ τ' K ∧ I τ' ∧ τ'.vars j = τ.vars j + 1 ∧
        K ≤ Kb + 7 := by
    intro τ hτ hlt
    obtain ⟨τ', K, hr, hK, hjfix, hI'⟩ := hstep τ hτ hlt
    exact ⟨τ'.setVar j (τ.vars j + 1), K + 7,
      scanBody_run (htgt τ hτ) (by omega) (by omega) (htB _ hlt) hB1 hr hjfix, hI',
      by simp, by omega⟩
  obtain ⟨σ', hrun, hI', hj'⟩ :=
    (Csr.rowScan_spec B ((Kb + 11) * (hi - σ.vars j) + 4) hi (Kb + 7) j jend
      (scanBody t j w c) (P := fun τ => I τ ∧ τ.vars j = σ.vars j) I hhiB hIb
      hstep' (fun _ hτ => hτ.1) (fun τ hτ => by rw [hτ.2])).run ⟨hI, rfl⟩
  exact ⟨σ', _, hrun, le_rfl, hI', hj'⟩

/-- **The whole combinator.** The row's two bounds are read, the row is
scanned, and the caller is handed its invariant back with the pointer
at the end of the row. -/
theorem blockScan_run {B : ℕ} {o t x j jend w : String} {c : Com}
    {nv len Kb v : ℕ} {off tgt : ℕ → ℕ} {I : Env → Prop} {σ : Env}
    (hxj : x ≠ j) (hjje : j ≠ jend) (hB1 : 1 < B)
    (hv : v < nv) (hvB : v + 1 < B)
    (hoff : σ.arrs o = arrOf (nv + 1) off)
    (hle : off v ≤ off (v + 1)) (hhilen : off (v + 1) ≤ len) (hhiB : off (v + 1) < B)
    (hxv : σ.vars x = v)
    (htgt : ∀ τ, I τ → τ.arrs t = arrOf len tgt)
    (htB : ∀ p < off (v + 1), tgt p < B)
    (hIb : ∀ τ, I τ → τ.vars jend = off (v + 1) ∧ τ.vars j ≤ off (v + 1))
    (hstart : I ((σ.setVar j (off v)).setVar jend (off (v + 1))))
    (hstep : ∀ τ, I τ → τ.vars j < off (v + 1) →
      ∃ τ' K, Run B c (τ.setVar w (tgt (τ.vars j))) τ' K ∧ K ≤ Kb ∧
        τ'.vars j = τ.vars j ∧ I (τ'.setVar j (τ.vars j + 1))) :
    ∃ σ' K, Run B (RamAugment.blockScan o t x j jend w c) σ σ' K ∧
      K ≤ (Kb + 11) * (off (v + 1) - off v) + 12 ∧ I σ' ∧ σ'.vars j = off (v + 1) := by
  have e₁ : (Expr.get o (.var x)).evalB B σ = some (off v) := by
    refine evalB_get (k := v) ?_ ?_ (by omega)
    · rw [← hxv]; exact evalB_var (by omega)
    · rw [hoff, getElem?_arrOf off (by omega)]
  have hx₁ : (σ.setVar j (off v)).vars x = v := by simp [hxj, hxv]
  have hv1 : (Expr.add (.var x) (.lit 1)).evalB B (σ.setVar j (off v)) = some (v + 1) := by
    have h := evalB_bin (B := B) (op := .add) (σ := σ.setVar j (off v))
      (m := (σ.setVar j (off v)).vars x) (n := 1) (evalB_var (by rw [hx₁]; omega))
      (evalB_lit hB1) (by rw [hx₁]; simpa [Bop.apply] using hvB)
    rw [hx₁] at h
    simpa [Bop.apply] using h
  have e₂ : (Expr.get o (.add (.var x) (.lit 1))).evalB B (σ.setVar j (off v))
      = some (off (v + 1)) :=
    evalB_get hv1 (by rw [arrs_setVar, hoff, getElem?_arrOf off (by omega)]) hhiB
  set σ₁ := (σ.setVar j (off v)).setVar jend (off (v + 1)) with hσ₁
  have hjσ₁ : σ₁.vars j = off v := by simp [hσ₁, hjje]
  obtain ⟨σ', K, hrun, hK, hI', hj'⟩ :=
    rowScan_run (B := B) (t := t) (j := j) (jend := jend) (w := w) (c := c) (len := len)
      (Kb := Kb) (hi := off (v + 1)) (tgt := tgt) (I := I) (σ := σ₁) hhiB hB1 hhilen htgt
      (fun p hp => htB p hp) hIb hstep hstart
  refine ⟨σ', 8 + K, ((Run.assign e₁).seq (Run.assign e₂)).mono ?_ |>.seq hrun, ?_, hI', hj'⟩
  · simp only [size_get, size_var, size_add, size_lit]; omega
  · rw [hjσ₁] at hK; omega

/-! ### The vertex loop

`RamAugment.forVerts body` is `i := 0; while i < n do body; i := i+1`,
the shape of all ten passes. The combinator supplies the counter, the
condition and the increment; the caller supplies an invariant indexed by
the counter and a cost *per turn*, since a turn of a pass that scans a
block costs the length of that block and no constant will do. -/

theorem forVerts_run {B : ℕ} {body : Com} {n : ℕ} {costs : ℕ → ℕ} {I : ℕ → Env → Prop}
    {σ : Env} (hnB : n + 1 < B)
    (hn : ∀ i τ, I i τ → τ.vars "n" = n)
    (hiv : ∀ i τ, I i τ → τ.vars "i" = i)
    (_hin : ∀ i τ, I i τ → i ≤ n)
    (hstep : ∀ i, i < n → ∀ τ, I i τ →
      ∃ τ' K, Run B body τ τ' K ∧ K ≤ costs i ∧ τ'.vars "i" = i ∧
        I (i + 1) (τ'.setVar "i" (i + 1)))
    (hI0 : I 0 (σ.setVar "i" 0)) :
    ∃ σ' K, Run B (RamAugment.forVerts body) σ σ' K ∧
      K ≤ (∑ i ∈ Finset.range n, (costs i + 8)) + 8 ∧ I n σ' := by
  set J : Env → Prop := fun τ => ∃ i ≤ n, I i τ with hJ
  set Φ : Env → ℕ := fun τ => ∑ k ∈ Finset.Ico (τ.vars "i") n, (costs k + 8) with hΦ
  have hdef : ∀ τ, J τ → ∃ v, (Cond.lt (.var "i") (.var "n")).evalB B τ = some v := by
    rintro τ ⟨i, hi, hIi⟩
    exact evalB_condLt_vars (by rw [hiv i τ hIi]; omega) (by rw [hn i τ hIi]; omega)
  have hbody : ∀ τ, J τ → (Cond.lt (.var "i") (.var "n")).evalB B τ = some true →
      ∃ τ' K, Run B (.seq body (.assign "i" (.add (.var "i") (.lit 1)))) τ τ' K ∧ J τ' ∧
        1 + (Cond.lt (Expr.var "i") (Expr.var "n")).size + K + Φ τ' ≤ Φ τ := by
    rintro τ ⟨i, hi, hIi⟩ hc
    have hlt : i < n := by
      have := lt_of_condLt_true hc
      rw [hiv i τ hIi, hn i τ hIi] at this; exact this
    obtain ⟨τ', K, hr, hK, hi', hI'⟩ := hstep i hlt τ hIi
    have e : (Expr.add (.var "i") (.lit 1)).evalB B τ' = some (i + 1) := by
      have h := evalB_bin (B := B) (op := .add) (σ := τ') (m := τ'.vars "i") (n := 1)
        (evalB_var (by rw [hi']; omega)) (evalB_lit (by omega))
        (by rw [hi']; simpa [Bop.apply] using (by omega : i + 1 < B))
      rw [hi'] at h
      simpa [Bop.apply] using h
    refine ⟨τ'.setVar "i" (i + 1), K + 4, (hr.seq (Run.assign e)).mono (by simp),
      ⟨i + 1, by omega, hI'⟩, ?_⟩
    have hsplit : Φ τ = (costs i + 8) + ∑ k ∈ Finset.Ico (i + 1) n, (costs k + 8) := by
      rw [hΦ]
      simp only [hiv i τ hIi]
      exact Finset.sum_eq_sum_Ico_succ_bot hlt _
    have hτ' : Φ (τ'.setVar "i" (i + 1)) = ∑ k ∈ Finset.Ico (i + 1) n, (costs k + 8) := by
      rw [hΦ]; simp
    simp only [size_condLt, size_var, hτ', hsplit]
    omega
  obtain ⟨σ', K₀, hrun, hJ', hfalse, hpay⟩ :=
    Run.while_potential (B := B) J Φ hdef hbody (σ := σ.setVar "i" 0) ⟨0, by omega, hI0⟩
  obtain ⟨i, hi, hIi⟩ := hJ'
  have hex : i = n := by
    have h := le_of_condLt_false hfalse
    rw [hiv i σ' hIi, hn i σ' hIi] at h
    omega
  have hΦ0 : Φ (σ.setVar "i" 0) = ∑ k ∈ Finset.range n, (costs k + 8) := by
    rw [hΦ, Finset.range_eq_Ico]; simp
  have hΦn : Φ σ' = 0 := by
    show ∑ k ∈ Finset.Ico (σ'.vars "i") n, (costs k + 8) = 0
    rw [hiv i σ' hIi, hex]; simp
  refine ⟨σ', 2 + K₀, (Run.assign (v := 0) (evalB_lit (by omega))).seq hrun, ?_, hex ▸ hIi⟩
  rw [hΦ0, hΦn] at hpay
  simp only [size_condLt, size_var] at hpay
  omega

/-! ### The row view

`RamElim.InCsr` with the graph forgotten, and with the target array's
length *not* tied to the last offset: every array of this round is cut
to the caller's width `W` and uses a data-dependent prefix of it. -/

/-- `Blocks o t nv len m off tgt σ`: in `σ`, the array `o` holds `nv+1`
offsets cutting the first `m` cells of the `len`-cell array `t` into
`nv` blocks, and every one of those cells names a vertex. -/
structure Blocks (o t : String) (nv len m : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop where
  /-- The offsets. -/
  offArr : σ.arrs o = arrOf (nv + 1) off
  /-- The targets. -/
  tgtArr : σ.arrs t = arrOf len tgt
  /-- The first block starts at the start. -/
  zero : off 0 = 0
  /-- The last block ends at the slot count. -/
  last : off nv = m
  /-- The offsets do not decrease. -/
  mono : ∀ i < nv, off i ≤ off (i + 1)
  /-- The slots fit in the array. -/
  le : m ≤ len
  /-- Every slot names a vertex. -/
  target_lt : ∀ p < m, tgt p < nv

namespace Blocks

variable {o t : String} {nv len m : ℕ} {off tgt : ℕ → ℕ} {σ : Env}

theorem mono' (h : Blocks o t nv len m off tgt σ) {i k : ℕ} (hik : i ≤ k) (hk : k ≤ nv) :
    off i ≤ off k := by
  induction k with
  | zero => rw [show i = 0 by omega]
  | succ k ih =>
      rcases Nat.lt_or_ge i (k + 1) with hi | hi
      · exact le_trans (ih (by omega) (by omega)) (h.mono k (by omega))
      · rw [show i = k + 1 by omega]

theorem off_le (h : Blocks o t nv len m off tgt σ) {i : ℕ} (hi : i ≤ nv) : off i ≤ m := by
  rw [← h.last]; exact h.mono' hi le_rfl

/-- The rows tile the slots: the lengths add up to the slot count. -/
theorem sum_rowLen (h : Blocks o t nv len m off tgt σ) :
    ∑ i ∈ Finset.range nv, (off (i + 1) - off i) = m := by
  have key : ∀ k ≤ nv, ∑ i ∈ Finset.range k, (off (i + 1) - off i) = off k := by
    intro k
    induction k with
    | zero => intro _; simp [h.zero]
    | succ k ih =>
        intro hk
        rw [Finset.sum_range_succ, ih (by omega)]
        have := h.mono k (by omega)
        omega
  rw [key nv le_rfl, h.last]

/-- The relation is about two arrays, so a scalar assignment leaves it
alone. -/
theorem setVar (h : Blocks o t nv len m off tgt σ) (y : String) (x : ℕ) :
    Blocks o t nv len m off tgt (σ.setVar y x) :=
  ⟨by simpa using h.offArr, by simpa using h.tgtArr, h.zero, h.last, h.mono, h.le,
    h.target_lt⟩

/-- And so does a store into a third array. -/
theorem setArr_of_ne (h : Blocks o t nv len m off tgt σ) {b : String} (hbo : b ≠ o)
    (hbt : b ≠ t) (p x : ℕ) : Blocks o t nv len m off tgt (σ.setArr b p x) :=
  ⟨by rw [arrs_setArr, if_neg (Ne.symm hbo)]; exact h.offArr,
    by rw [arrs_setArr, if_neg (Ne.symm hbt)]; exact h.tgtArr, h.zero, h.last, h.mono, h.le,
    h.target_lt⟩

/-- The relation is a statement about two arrays, so it transports
along any state that agrees on them. -/
theorem of_eq (h : Blocks o t nv len m off tgt σ) {σ' : Env}
    (ho : σ'.arrs o = σ.arrs o) (ht : σ'.arrs t = σ.arrs t) :
    Blocks o t nv len m off tgt σ' :=
  ⟨ho.trans h.offArr, ht.trans h.tgtArr, h.zero, h.last, h.mono, h.le, h.target_lt⟩

/-- The block structure of the round's input, off `RamElim.InCsr`. -/
theorem of_inCsr {n W m : ℕ} {D : Orientation n} {DO DT : ℕ → ℕ} {σ : Env}
    (h : InCsr D m DO DT) (hoff : σ.arrs "doff" = arrOf (n + 1) DO)
    (htgt : σ.arrs "dtg" = arrOf W DT) (hmW : m ≤ W) :
    Blocks "doff" "dtg" n W m DO DT σ :=
  ⟨hoff, htgt, h.zero, h.last, h.mono, hmW, h.target_lt⟩

end Blocks

/-! ### What a counting sort counts

The three counting sorts of the round all count the same thing: how
often a target occurs among the slots scanned so far. Since the blocks
tile the slots, the count after `i` whole rows and the count at a
pointer inside row `i` are the same function of one number — the
pointer — which is why one invariant serves the outer pass and its
inner scan alike. -/

/-- How many of the first `p` slots carry the target `u`. -/
def slotCnt (T : ℕ → ℕ) (p u : ℕ) : ℕ := ((Finset.range p).filter (fun s => T s = u)).card

@[simp] theorem slotCnt_zero (T : ℕ → ℕ) (u : ℕ) : slotCnt T 0 u = 0 := by simp [slotCnt]

theorem slotCnt_succ (T : ℕ → ℕ) (p u : ℕ) :
    slotCnt T (p + 1) u = slotCnt T p u + (if T p = u then 1 else 0) := by
  classical
  rw [slotCnt, slotCnt, Finset.range_add_one, Finset.filter_insert]
  by_cases h : T p = u
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg h, if_neg h, Nat.add_zero]

theorem slotCnt_le (T : ℕ → ℕ) (p u : ℕ) : slotCnt T p u ≤ p :=
  le_trans (Finset.card_filter_le _ _) (by simp)

theorem slotCnt_mono (T : ℕ → ℕ) {p q : ℕ} (h : p ≤ q) (u : ℕ) :
    slotCnt T p u ≤ slotCnt T q u :=
  Finset.card_le_card (Finset.filter_subset_filter _ (by simpa using h))

/-- A slot that carries `u` is a slot of the block of `u`: the count is
strictly larger one slot on. -/
theorem slotCnt_lt_of_eq {T : ℕ → ℕ} {p u : ℕ} (h : T p = u) :
    slotCnt T p u < slotCnt T (p + 1) u := by rw [slotCnt_succ, if_pos h]; omega

/-- The counts add up to the number of slots. -/
theorem sum_slotCnt {T : ℕ → ℕ} {nv m : ℕ} (h : ∀ s < m, T s < nv) :
    ∑ u ∈ Finset.range nv, slotCnt T m u = m := by
  classical
  induction m with
  | zero => simp
  | succ p ih =>
      have hp : ∀ s < p, T s < nv := fun s hs => h s (by omega)
      have hTp : T p < nv := h p (by omega)
      rw [Finset.sum_congr rfl (fun u _ => slotCnt_succ T p u), Finset.sum_add_distrib, ih hp]
      simp [Finset.mem_range.2 hTp]

/-! ### The out-degrees

`RamAugment.outCount` walks every in-block of `D` and bumps, one place
up, the cell of every target it sees. Since the in-blocks tile the slot
array, the count after `i` whole rows and the count at a pointer inside
row `i` are the same function of the pointer, so one invariant does for
the pass and for its inner scan. -/

/-- What the out-degree count carries at a slot pointer. -/
def CountInv (n W m : ℕ) (DO DT : ℕ → ℕ) (p : ℕ) (τ : Env) : Prop :=
  τ.vars "n" = n ∧ Blocks "doff" "dtg" n W m DO DT τ ∧
    ∃ g, τ.arrs "ooff" = arrOf (n + 1) g ∧ g 0 = 0 ∧
      ∀ u < n, g (u + 1) = slotCnt DT p u

/-- **One slot of the out-degree count.** -/
theorem outCountSlot_run {B n W m i : ℕ} {DO DT : ℕ → ℕ} {ρ : Env}
    (hnB : n + 1 < B) (hmB : m < B) (hi : i < n)
    (hI : CountInv n W m DO DT (ρ.vars "j") ρ ∧ ρ.vars "i" = i ∧
      ρ.vars "jend" = DO (i + 1) ∧ DO i ≤ ρ.vars "j" ∧ ρ.vars "j" ≤ DO (i + 1))
    (hjlt : ρ.vars "j" < DO (i + 1)) :
    ∃ ρ' K, Run B (.store "ooff" (.add (.var "u") (.lit 1))
        (.add (.get "ooff" (.add (.var "u") (.lit 1))) (.lit 1)))
        (ρ.setVar "u" (DT (ρ.vars "j"))) ρ' K ∧ K ≤ 10 ∧ ρ'.vars "j" = ρ.vars "j" ∧
      (CountInv n W m DO DT ((ρ'.setVar "j" (ρ.vars "j" + 1)).vars "j")
          (ρ'.setVar "j" (ρ.vars "j" + 1)) ∧
        (ρ'.setVar "j" (ρ.vars "j" + 1)).vars "i" = i ∧
        (ρ'.setVar "j" (ρ.vars "j" + 1)).vars "jend" = DO (i + 1) ∧
        DO i ≤ (ρ'.setVar "j" (ρ.vars "j" + 1)).vars "j" ∧
        (ρ'.setVar "j" (ρ.vars "j" + 1)).vars "j" ≤ DO (i + 1)) := by
  obtain ⟨⟨hnv, hbl, g, hg, hg0, hgu⟩, hi', hje', hj1, hj2⟩ := hI
  have hmW : DO (i + 1) ≤ m := hbl.off_le (by omega)
  have hu : DT (ρ.vars "j") < n := hbl.target_lt _ (by omega)
  have hcnt : g (DT (ρ.vars "j") + 1) = slotCnt DT (ρ.vars "j") (DT (ρ.vars "j")) := hgu _ hu
  have hcB : g (DT (ρ.vars "j") + 1) + 1 < B := by
    have := slotCnt_le DT (ρ.vars "j") (DT (ρ.vars "j")); omega
  set ρ' := ρ.setVar "u" (DT (ρ.vars "j")) with hρ'
  have huρ : ρ'.vars "u" = DT (ρ.vars "j") := by simp [hρ']
  have eidx : (Expr.add (.var "u") (.lit 1)).evalB B ρ' = some (DT (ρ.vars "j") + 1) := by
    have h := evalB_bin (B := B) (op := .add) (σ := ρ') (m := ρ'.vars "u") (n := 1)
      (evalB_var (by rw [huρ]; omega)) (evalB_lit (by omega))
      (by rw [huρ]; simpa [Bop.apply] using (by omega : DT (ρ.vars "j") + 1 < B))
    rw [huρ] at h
    simpa [Bop.apply] using h
  have hooff' : ρ'.arrs "ooff" = arrOf (n + 1) g := by rw [hρ', arrs_setVar]; exact hg
  have eget : (Expr.get "ooff" (.add (.var "u") (.lit 1))).evalB B ρ'
      = some (g (DT (ρ.vars "j") + 1)) :=
    evalB_get eidx (by rw [hooff', getElem?_arrOf g (by omega)]) (by omega)
  have eval : (Expr.add (.get "ooff" (.add (.var "u") (.lit 1))) (.lit 1)).evalB B ρ'
      = some (g (DT (ρ.vars "j") + 1) + 1) := by
    have h := evalB_bin (B := B) (op := .add) (σ := ρ')
      (m := g (DT (ρ.vars "j") + 1)) (n := 1) eget (evalB_lit (by omega))
      (by simpa [Bop.apply] using hcB)
    simpa [Bop.apply] using h
  have hlen : DT (ρ.vars "j") + 1 < (ρ'.arrs "ooff").length := by
    rw [hooff', length_arrOf]; omega
  refine ⟨ρ'.setArr "ooff" (DT (ρ.vars "j") + 1) (g (DT (ρ.vars "j") + 1) + 1), 10,
    (Run.store eidx eval hlen).mono
      (by simp only [size_add, size_var, size_lit, size_get]; try omega),
    le_rfl, by simp [hρ'], ?_⟩
  refine ⟨⟨by simp [hρ', hnv], ?_, fun k => if k = DT (ρ.vars "j") + 1
      then g (DT (ρ.vars "j") + 1) + 1 else g k, ?_, by simp [hg0], fun u hu' => ?_⟩,
    by simp [hρ', hi'], by simp [hρ', hje'], by simp; omega, by simp; omega⟩
  · exact ((hbl.setVar "u" _).setArr_of_ne (by decide) (by decide) _ _).setVar "j" _
  · rw [arrs_setVar, arrs_setArr, if_pos rfl, hooff', set_arrOf]
  · show (if u + 1 = DT (ρ.vars "j") + 1 then g (DT (ρ.vars "j") + 1) + 1 else g (u + 1))
      = slotCnt DT (((ρ'.setArr "ooff" (DT (ρ.vars "j") + 1)
          (g (DT (ρ.vars "j") + 1) + 1)).setVar "j" (ρ.vars "j" + 1)).vars "j") u
    have hjj : ((ρ'.setArr "ooff" (DT (ρ.vars "j") + 1)
        (g (DT (ρ.vars "j") + 1) + 1)).setVar "j" (ρ.vars "j" + 1)).vars "j"
        = ρ.vars "j" + 1 := by simp
    rw [hjj, slotCnt_succ]
    by_cases h : DT (ρ.vars "j") = u
    · rw [if_pos (by omega), if_pos h, ← h, hcnt]
    · rw [if_neg (by omega), if_neg h, hgu u hu', Nat.add_zero]

/-- **The out-degrees, counted.** -/
theorem outCount_run {B n W m : ℕ} {DO DT : ℕ → ℕ} {σ : Env}
    (hnB : n + 1 < B) (hmB : m < B)
    (hn : σ.vars "n" = n) (hb : Blocks "doff" "dtg" n W m DO DT σ)
    (hooff : ∃ g, σ.arrs "ooff" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0) :
    ∃ σ' K, Run B RamAugment.outCount σ σ' K ∧ K ≤ 21 * m + 20 * n + 8 ∧
      CountInv n W m DO DT m σ' := by
  obtain ⟨g₀, hg₀, hz⟩ := hooff
  have hstep : ∀ i, i < n → ∀ τ, (CountInv n W m DO DT (DO i) τ ∧ τ.vars "i" = i ∧ i ≤ n) →
      ∃ τ' K, Run B (RamAugment.blockScan "doff" "dtg" "i" "j" "jend" "u"
          (.store "ooff" (.add (.var "u") (.lit 1))
            (.add (.get "ooff" (.add (.var "u") (.lit 1))) (.lit 1)))) τ τ' K ∧
        K ≤ 21 * (DO (i + 1) - DO i) + 12 ∧ τ'.vars "i" = i ∧
        (CountInv n W m DO DT (DO (i + 1)) (τ'.setVar "i" (i + 1)) ∧
          (τ'.setVar "i" (i + 1)).vars "i" = i + 1 ∧ i + 1 ≤ n) := by
    intro i hi τ hτ
    obtain ⟨hci, hiv, -⟩ := hτ
    have hbl := hci.2.1
    have hmW : DO (i + 1) ≤ m := hbl.off_le (by omega)
    have hle : DO i ≤ DO (i + 1) := hbl.mono i hi
    have hgz : ∃ g, ((τ.setVar "j" (DO i)).setVar "jend" (DO (i + 1))).arrs "ooff"
        = arrOf (n + 1) g ∧ g 0 = 0 ∧
        ∀ u < n, g (u + 1)
          = slotCnt DT (((τ.setVar "j" (DO i)).setVar "jend" (DO (i + 1))).vars "j") u := by
      obtain ⟨g, hg, hg0, hgu⟩ := hci.2.2
      exact ⟨g, by simpa using hg, hg0, by simpa using hgu⟩
    obtain ⟨τ', K, hr, hK, hI', hj'⟩ :=
      blockScan_run (B := B) (o := "doff") (t := "dtg") (x := "i") (j := "j") (jend := "jend")
        (w := "u") (nv := n) (len := W) (Kb := 10) (v := i) (off := DO) (tgt := DT)
        (I := fun ρ => CountInv n W m DO DT (ρ.vars "j") ρ ∧ ρ.vars "i" = i ∧
          ρ.vars "jend" = DO (i + 1) ∧ DO i ≤ ρ.vars "j" ∧ ρ.vars "j" ≤ DO (i + 1))
        (by decide) (by decide) (by omega) hi (by omega) hbl.offArr hle
        (le_trans hmW hbl.le) (by omega) hiv (fun ρ hρ => hρ.1.2.1.tgtArr)
        (fun p hp => lt_trans (hbl.target_lt p (by omega)) (by omega))
        (fun ρ hρ => ⟨hρ.2.2.1, hρ.2.2.2.2⟩)
        ⟨⟨by simpa using hci.1, (hbl.setVar "j" _).setVar "jend" _, hgz⟩, by simp [hiv],
          by simp, by simp, by simp [hle]⟩
        (fun ρ hρ hjlt => outCountSlot_run hnB hmB hi hρ hjlt)
    refine ⟨τ', K, hr, hK, hI'.2.1, ?_⟩
    obtain ⟨hc', -⟩ := hI'
    rw [hj'] at hc'
    exact ⟨⟨by simpa using hc'.1, hc'.2.1.setVar "i" _,
      by obtain ⟨g, hg, hg0, hgu⟩ := hc'.2.2; exact ⟨g, by simpa using hg, hg0, hgu⟩⟩,
      by simp, by omega⟩
  obtain ⟨σ', K, hrun, hK, hI⟩ :=
    forVerts_run (B := B) (n := n) (costs := fun i => 21 * (DO (i + 1) - DO i) + 12)
      (I := fun i τ => CountInv n W m DO DT (DO i) τ ∧ τ.vars "i" = i ∧ i ≤ n)
      (σ := σ) hnB (fun _ _ h => h.1.1) (fun _ _ h => h.2.1) (fun _ _ h => h.2.2) hstep
      ⟨⟨by simpa using hn, hb.setVar "i" 0,
        ⟨g₀, by simpa using hg₀, hz 0 (by omega),
          fun u hu => by rw [hb.zero, slotCnt_zero, hz _ (by omega)]⟩⟩, by simp, by omega⟩
  have hfin : CountInv n W m DO DT m σ' := by
    have h := hI.1; rw [hb.last] at h; exact h
  refine ⟨σ', K, hrun, le_trans hK ?_, hfin⟩
  have hsum : ∑ i ∈ Finset.range n, (21 * (DO (i + 1) - DO i) + 12 + 8)
      = 21 * m + 20 * n := by
    have hpt : ∀ i ∈ Finset.range n,
        21 * (DO (i + 1) - DO i) + 12 + 8 = 21 * (DO (i + 1) - DO i) + 20 :=
      fun i _ => by omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.mul_sum, hb.sum_rowLen,
      Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  omega

/-! ### The prefix sum

The three counting sorts of the round — the out-lists, the fraternity
graph, the new in-lists — turn their degrees into offsets with *the
same program*, differing only in the two array names it is written
over. So it is walked once here, and `RamAugment.outPrefix`,
`RamAugment.fratPrefix` and `RamAugment.asmPrefix` are three
instances. -/

/-- The running sum that turns degrees held one place up in `a` into
offsets, opening each block's fill pointer in `b` at its start. -/
def prefixCom (a b : String) : Com :=
  RamAugment.forVerts (.seq (.store a (.add (.var "i") (.lit 1))
      (.add (.get a (.add (.var "i") (.lit 1))) (.get a (.var "i"))))
    (.store b (.var "i") (.get a (.var "i"))))

theorem outPrefix_eq : RamAugment.outPrefix = prefixCom "ooff" "ofl" := rfl
theorem fratPrefix_eq : RamAugment.fratPrefix = prefixCom "off" "ffl" := rfl
theorem asmPrefix_eq : RamAugment.asmPrefix = prefixCom "noff" "nfl" := rfl

/-- **The prefix sum, walked.** -/
theorem prefixPass_run {B : ℕ} {a b : String} {n : ℕ} {d : ℕ → ℕ} {σ : Env}
    (hab : a ≠ b) (hnB : n + 1 < B) (hMB : RamElim.psum d n < B)
    (hn : σ.vars "n" = n)
    (hA : ∃ g, σ.arrs a = arrOf (n + 1) g ∧ g 0 = 0 ∧ ∀ u < n, g (u + 1) = d u)
    (hF : ∃ f, σ.arrs b = arrOf n f) :
    ∃ σ' K, Run B (prefixCom a b) σ σ' K ∧ K ≤ 23 * n + 8 ∧
      σ'.vars "n" = n ∧ σ'.arrs a = arrOf (n + 1) (RamElim.psum d) ∧
      σ'.arrs b = arrOf n (RamElim.psum d) := by
  obtain ⟨g₀, hg₀, hz₀, hd₀⟩ := hA
  obtain ⟨f₀, hf₀⟩ := hF
  have hPB : ∀ k ≤ n, RamElim.psum d k < B :=
    fun k hk => lt_of_le_of_lt (RamElim.psum_mono d hk) hMB
  have hstep : ∀ i, i < n → ∀ τ,
      (τ.vars "n" = n ∧ τ.vars "i" = i ∧ i ≤ n ∧
        (∃ g, τ.arrs a = arrOf (n + 1) g ∧ (∀ k ≤ i, g k = RamElim.psum d k) ∧
          ∀ u, i ≤ u → u < n → g (u + 1) = d u) ∧
        (∃ f, τ.arrs b = arrOf n f ∧ ∀ k < i, f k = RamElim.psum d k)) →
      ∃ τ' K, Run B (.seq (.store a (.add (.var "i") (.lit 1))
          (.add (.get a (.add (.var "i") (.lit 1))) (.get a (.var "i"))))
        (.store b (.var "i") (.get a (.var "i")))) τ τ' K ∧ K ≤ 15 ∧ τ'.vars "i" = i ∧
        ((τ'.setVar "i" (i + 1)).vars "n" = n ∧ (τ'.setVar "i" (i + 1)).vars "i" = i + 1 ∧
          i + 1 ≤ n ∧
          (∃ g, (τ'.setVar "i" (i + 1)).arrs a = arrOf (n + 1) g ∧
            (∀ k ≤ i + 1, g k = RamElim.psum d k) ∧
            ∀ u, i + 1 ≤ u → u < n → g (u + 1) = d u) ∧
          (∃ f, (τ'.setVar "i" (i + 1)).arrs b = arrOf n f ∧
            ∀ k < i + 1, f k = RamElim.psum d k)) := by
    intro i hi τ hτ
    obtain ⟨hnv, hiv, -, ⟨g, hga, hgl, hgh⟩, ⟨f, hfb, hfl⟩⟩ := hτ
    have hgi : g i = RamElim.psum d i := hgl i le_rfl
    have hgi1 : g (i + 1) = d i := hgh i le_rfl hi
    have hsucc : RamElim.psum d (i + 1) = RamElim.psum d i + d i := RamElim.psum_succ d i
    have hvalB : d i + RamElim.psum d i < B := by
      have := hPB (i + 1) (by omega); omega
    have eidx : (Expr.add (.var "i") (.lit 1)).evalB B τ = some (i + 1) := by
      have h := evalB_bin (B := B) (op := .add) (σ := τ) (m := τ.vars "i") (n := 1)
        (evalB_var (by rw [hiv]; omega)) (evalB_lit (by omega))
        (by rw [hiv]; simpa [Bop.apply] using (by omega : i + 1 < B))
      rw [hiv] at h
      simpa [Bop.apply] using h
    have eget1 : (Expr.get a (.add (.var "i") (.lit 1))).evalB B τ = some (d i) := by
      refine evalB_get eidx ?_ (by omega)
      rw [hga, getElem?_arrOf g (by omega), hgi1]
    have eivar : (Expr.var "i").evalB B τ = some i := by
      rw [← hiv]; exact evalB_var (by rw [hiv]; omega)
    have eget2 : (Expr.get a (.var "i")).evalB B τ = some (RamElim.psum d i) := by
      refine evalB_get eivar ?_ (hPB i (by omega))
      rw [hga, getElem?_arrOf g (by omega), hgi]
    have eval1 : (Expr.add (.get a (.add (.var "i") (.lit 1))) (.get a (.var "i"))).evalB B τ
        = some (d i + RamElim.psum d i) := by
      have h := evalB_bin (B := B) (op := .add) (σ := τ) (m := d i)
        (n := RamElim.psum d i) eget1 eget2 (by simpa [Bop.apply] using hvalB)
      simpa [Bop.apply] using h
    have hlen1 : i + 1 < (τ.arrs a).length := by rw [hga, length_arrOf]; omega
    set τ₁ := τ.setArr a (i + 1) (d i + RamElim.psum d i) with hτ₁
    set g' : ℕ → ℕ := fun k => if k = i + 1 then d i + RamElim.psum d i else g k with hg'
    have hga₁ : τ₁.arrs a = arrOf (n + 1) g' := by
      rw [hτ₁, arrs_setArr, if_pos rfl, hga, set_arrOf]
    have eivar₁ : (Expr.var "i").evalB B τ₁ = some i := by
      have : τ₁.vars "i" = i := by rw [hτ₁, vars_setArr, hiv]
      rw [← this]; exact evalB_var (by rw [this]; omega)
    have eget3 : (Expr.get a (.var "i")).evalB B τ₁ = some (RamElim.psum d i) := by
      refine evalB_get eivar₁ ?_ (hPB i (by omega))
      rw [hga₁, getElem?_arrOf g' (by omega), hg']
      simp only []
      rw [if_neg (by omega), hgi]
    have hlen2 : i < (τ₁.arrs b).length := by
      rw [hτ₁, arrs_setArr, if_neg (Ne.symm hab), hfb, length_arrOf]; omega
    refine ⟨τ₁.setArr b i (RamElim.psum d i), 15,
      ((Run.store eidx eval1 hlen1).seq (Run.store eivar₁ eget3 hlen2)).mono
        (by simp only [size_add, size_var, size_lit, size_get]; try omega),
      le_rfl, by rw [vars_setArr, hτ₁, vars_setArr, hiv], ?_⟩
    refine ⟨by simp [hτ₁, hnv], by simp, by omega,
      ⟨g', by rw [arrs_setVar, arrs_setArr, if_neg hab, hga₁], ?_, ?_⟩,
      ⟨fun k => if k = i then RamElim.psum d i else f k, ?_, ?_⟩⟩
    · intro k hk
      rw [hg']
      simp only []
      rcases Nat.lt_or_ge k (i + 1) with hk' | hk'
      · rw [if_neg (by omega)]; exact hgl k (by omega)
      · rw [if_pos (by omega), show k = i + 1 by omega, hsucc]; omega
    · intro u hu hun
      rw [hg']
      simp only []
      rw [if_neg (by omega)]
      exact hgh u (by omega) hun
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, hτ₁, arrs_setArr, if_neg (Ne.symm hab), hfb,
        set_arrOf]
    · intro k hk
      simp only []
      rcases Nat.lt_or_ge k i with hk' | hk'
      · rw [if_neg (by omega)]; exact hfl k hk'
      · rw [if_pos (by omega), show k = i by omega]
  obtain ⟨σ', K, hrun, hK, hI⟩ :=
    forVerts_run (B := B) (n := n) (costs := fun _ => 15)
      (I := fun i τ => τ.vars "n" = n ∧ τ.vars "i" = i ∧ i ≤ n ∧
        (∃ g, τ.arrs a = arrOf (n + 1) g ∧ (∀ k ≤ i, g k = RamElim.psum d k) ∧
          ∀ u, i ≤ u → u < n → g (u + 1) = d u) ∧
        (∃ f, τ.arrs b = arrOf n f ∧ ∀ k < i, f k = RamElim.psum d k))
      (σ := σ) hnB (fun _ _ h => h.1) (fun _ _ h => h.2.1) (fun _ _ h => h.2.2.1) hstep
      ⟨by simpa using hn, by simp, by omega,
        ⟨g₀, by simpa using hg₀, fun k hk => by rw [show k = 0 by omega, hz₀]; simp,
          fun u _ hun => hd₀ u hun⟩,
        ⟨f₀, by simpa using hf₀, fun k hk => absurd hk (by omega)⟩⟩
  obtain ⟨-, -, -, ⟨g, hga, hgl, -⟩, ⟨f, hfb, hfl⟩⟩ := id hI
  refine ⟨σ', K, hrun, ?_, hI.1, ?_, ?_⟩
  · refine le_trans hK (by simp [Finset.sum_const, Finset.card_range]; omega)
  · rw [hga]; exact RamDriverOrder.arrOf_congr fun k hk => hgl k (by omega)
  · rw [hfb]; exact RamDriverOrder.arrOf_congr fun k hk => hfl k hk

/-! ### The out-lists, scattered

The second half of the counting sort. Every slot of the input carries
its owner into the block of its target, and the block of `u` ends up
naming exactly the vertices that point at `u` — which, once the input
is read as `RamElim.InCsr`, is `RamAugment.outSet D u`.

The blocks the sort writes are the prefix sums of the counts, so they
are `outOff`; `Pts` is "the block structure records an arc from `z` to
`u`", and `PtsLt` is the same restricted to the slots already
scanned. -/

/-- Where the out-block of `u` starts. -/
def outOff (T : ℕ → ℕ) (m : ℕ) : ℕ → ℕ := RamElim.psum (fun z => slotCnt T m z)

theorem outOff_succ (T : ℕ → ℕ) (m u : ℕ) :
    outOff T m (u + 1) = outOff T m u + slotCnt T m u := RamElim.psum_succ _ u

@[simp] theorem outOff_zero (T : ℕ → ℕ) (m : ℕ) : outOff T m 0 = 0 := RamElim.psum_zero _

theorem outOff_mono (T : ℕ → ℕ) (m : ℕ) {u v : ℕ} (h : u ≤ v) :
    outOff T m u ≤ outOff T m v := RamElim.psum_mono _ h

theorem outOff_last {T : ℕ → ℕ} {nv m : ℕ} (h : ∀ s < m, T s < nv) :
    outOff T m nv = m := sum_slotCnt h

/-- The block structure records an arc from `z` to `u`. -/
def Pts (DO DT : ℕ → ℕ) (z u : ℕ) : Prop := ∃ s, DO z ≤ s ∧ s < DO (z + 1) ∧ DT s = u

/-- The same, restricted to the slots the scan has passed. -/
def PtsLt (DO DT : ℕ → ℕ) (p z u : ℕ) : Prop :=
  ∃ s, s < p ∧ DO z ≤ s ∧ s < DO (z + 1) ∧ DT s = u

theorem PtsLt.mono {DO DT : ℕ → ℕ} {p p' z u : ℕ} (h : PtsLt DO DT p z u) (hp : p ≤ p') :
    PtsLt DO DT p' z u := by
  obtain ⟨s, h₁, h₂, h₃, h₄⟩ := h; exact ⟨s, by omega, h₂, h₃, h₄⟩

theorem PtsLt.pts {DO DT : ℕ → ℕ} {p z u : ℕ} (h : PtsLt DO DT p z u) : Pts DO DT z u := by
  obtain ⟨s, -, h₂, h₃, h₄⟩ := h; exact ⟨s, h₂, h₃, h₄⟩

theorem Pts.ptsLt {o t : String} {nv len m : ℕ} {off tgt : ℕ → ℕ} {σ : Env}
    (hb : Blocks o t nv len m off tgt σ) {z u : ℕ} (hz : z < nv) (h : Pts off tgt z u) :
    PtsLt off tgt m z u := by
  obtain ⟨s, h₂, h₃, h₄⟩ := h
  exact ⟨s, lt_of_lt_of_le h₃ (hb.off_le hz), h₂, h₃, h₄⟩

/-- **A slot has one owner.** -/
theorem Blocks.owner_unique {o t : String} {nv len m : ℕ} {off tgt : ℕ → ℕ} {σ : Env}
    (h : Blocks o t nv len m off tgt σ) {z z' p : ℕ} (hz : z < nv) (hz' : z' < nv)
    (h₁ : off z ≤ p) (h₂ : p < off (z + 1)) (h₃ : off z' ≤ p) (h₄ : p < off (z' + 1)) :
    z = z' := by
  by_contra hne
  rcases Nat.lt_or_ge z z' with hlt | hge
  · have := h.mono' (show z + 1 ≤ z' by omega) (by omega); omega
  · have := h.mono' (show z' + 1 ≤ z by omega) (by omega); omega

/-- What the scatter carries at a slot pointer: the fill pointers at
their blocks' starts plus what has been written, and the written cells
naming exactly the arcs the scan has passed. -/
def ScatInv (n W m : ℕ) (DO DT : ℕ → ℕ) (p : ℕ) (τ : Env) : Prop :=
  τ.vars "n" = n ∧ Blocks "doff" "dtg" n W m DO DT τ ∧
    τ.arrs "ooff" = arrOf (n + 1) (outOff DT m) ∧
    (∃ fl, τ.arrs "ofl" = arrOf n fl ∧
      ∀ u < n, fl u = outOff DT m u + slotCnt DT p u) ∧
    (∃ OT, τ.arrs "otg" = arrOf W OT ∧
      (∀ u < n, ∀ q, outOff DT m u ≤ q → q < outOff DT m u + slotCnt DT p u →
        OT q < n ∧ PtsLt DO DT p (OT q) u) ∧
      (∀ u < n, ∀ z < n, PtsLt DO DT p z u →
        ∃ q, outOff DT m u ≤ q ∧ q < outOff DT m u + slotCnt DT p u ∧ OT q = z))

/-- **One slot of the scatter.** -/
theorem outFillSlot_run {B n W m i : ℕ} {DO DT : ℕ → ℕ} {ρ : Env}
    (hnB : n + 1 < B) (hmB : m < B) (hmW : m ≤ W) (hi : i < n)
    (hI : ScatInv n W m DO DT (ρ.vars "j") ρ ∧ ρ.vars "i" = i ∧
      ρ.vars "jend" = DO (i + 1) ∧ DO i ≤ ρ.vars "j" ∧ ρ.vars "j" ≤ DO (i + 1))
    (hjlt : ρ.vars "j" < DO (i + 1)) :
    ∃ ρ' K, Run B (.seq (.store "otg" (.get "ofl" (.var "u")) (.var "i"))
        (.store "ofl" (.var "u") (.add (.get "ofl" (.var "u")) (.lit 1))))
        (ρ.setVar "u" (DT (ρ.vars "j"))) ρ' K ∧ K ≤ 10 ∧ ρ'.vars "j" = ρ.vars "j" ∧
      (ScatInv n W m DO DT ((ρ'.setVar "j" (ρ.vars "j" + 1)).vars "j")
          (ρ'.setVar "j" (ρ.vars "j" + 1)) ∧
        (ρ'.setVar "j" (ρ.vars "j" + 1)).vars "i" = i ∧
        (ρ'.setVar "j" (ρ.vars "j" + 1)).vars "jend" = DO (i + 1) ∧
        DO i ≤ (ρ'.setVar "j" (ρ.vars "j" + 1)).vars "j" ∧
        (ρ'.setVar "j" (ρ.vars "j" + 1)).vars "j" ≤ DO (i + 1)) := by
  obtain ⟨⟨hnv, hbl, hoo, ⟨fl, hflA, hflE⟩, ⟨OT, hotA, hsnd, hcmp⟩⟩, hi', hje', hj1, hj2⟩ := hI
  set p := ρ.vars "j" with hp
  have hrow : DO (i + 1) ≤ m := hbl.off_le (by omega)
  have hpm : p < m := by omega
  have hu : DT p < n := hbl.target_lt _ hpm
  -- the fill pointer of the target's block, and that it is a slot of that block
  have hq₀ : fl (DT p) = outOff DT m (DT p) + slotCnt DT p (DT p) := hflE _ hu
  have hgrow : slotCnt DT p (DT p) < slotCnt DT m (DT p) :=
    lt_of_lt_of_le (slotCnt_lt_of_eq rfl) (slotCnt_mono DT (by omega) _)
  have hqlt : fl (DT p) < outOff DT m (DT p + 1) := by
    rw [hq₀, outOff_succ]; omega
  have hqm : fl (DT p) < m := by
    have : outOff DT m (DT p + 1) ≤ outOff DT m n :=
      outOff_mono DT m (by omega)
    have hlast : outOff DT m n = m := outOff_last (fun s hs => hbl.target_lt s hs)
    omega
  set ρ₀ := ρ.setVar "u" (DT p) with hρ₀
  have huρ : ρ₀.vars "u" = DT p := by simp [hρ₀]
  have hiρ : ρ₀.vars "i" = i := by simp [hρ₀, hi']
  have hflρ : ρ₀.arrs "ofl" = arrOf n fl := by rw [hρ₀, arrs_setVar]; exact hflA
  have hotρ : ρ₀.arrs "otg" = arrOf W OT := by rw [hρ₀, arrs_setVar]; exact hotA
  have euvar : (Expr.var "u").evalB B ρ₀ = some (DT p) := by
    rw [← huρ]; exact evalB_var (by rw [huρ]; omega)
  have egfl : (Expr.get "ofl" (.var "u")).evalB B ρ₀ = some (fl (DT p)) :=
    evalB_get euvar (by rw [hflρ, getElem?_arrOf fl hu]) (by omega)
  have eivar : (Expr.var "i").evalB B ρ₀ = some i := by
    rw [← hiρ]; exact evalB_var (by rw [hiρ]; omega)
  have hlen1 : fl (DT p) < (ρ₀.arrs "otg").length := by
    rw [hotρ, length_arrOf]; omega
  set ρ₁ := ρ₀.setArr "otg" (fl (DT p)) i with hρ₁
  set OT' : ℕ → ℕ := fun k => if k = fl (DT p) then i else OT k with hOT'
  have hotρ₁ : ρ₁.arrs "otg" = arrOf W OT' := by
    rw [hρ₁, arrs_setArr, if_pos rfl, hotρ, set_arrOf]
  have hflρ₁ : ρ₁.arrs "ofl" = arrOf n fl := by
    rw [hρ₁, arrs_setArr, if_neg (by decide), hflρ]
  have euvar₁ : (Expr.var "u").evalB B ρ₁ = some (DT p) := by
    have h : ρ₁.vars "u" = DT p := by rw [hρ₁, vars_setArr, huρ]
    rw [← h]; exact evalB_var (by rw [h]; omega)
  have egfl₁ : (Expr.get "ofl" (.var "u")).evalB B ρ₁ = some (fl (DT p)) :=
    evalB_get euvar₁ (by rw [hflρ₁, getElem?_arrOf fl hu]) (by omega)
  have eadd : (Expr.add (.get "ofl" (.var "u")) (.lit 1)).evalB B ρ₁
      = some (fl (DT p) + 1) := by
    have h := evalB_bin (B := B) (op := .add) (σ := ρ₁) (m := fl (DT p)) (n := 1)
      egfl₁ (evalB_lit (by omega)) (by simpa [Bop.apply] using (by omega : fl (DT p) + 1 < B))
    simpa [Bop.apply] using h
  have hlen2 : DT p < (ρ₁.arrs "ofl").length := by rw [hflρ₁, length_arrOf]; exact hu
  refine ⟨ρ₁.setArr "ofl" (DT p) (fl (DT p) + 1), 10,
    ((Run.store egfl eivar hlen1).seq (Run.store euvar₁ eadd hlen2)).mono
      (by simp only [size_add, size_var, size_lit, size_get]; try omega),
    le_rfl, by simp [hρ₁, hρ₀, ← hp], ?_⟩
  set fl' : ℕ → ℕ := fun k => if k = DT p then fl (DT p) + 1 else fl k with hfl'
  have hjnew : ((ρ₁.setArr "ofl" (DT p) (fl (DT p) + 1)).setVar "j" (p + 1)).vars "j" = p + 1 :=
    by simp
  have hcntnew : ∀ u, outOff DT m u + slotCnt DT (p + 1) u
      = outOff DT m u + slotCnt DT p u + (if DT p = u then 1 else 0) := by
    intro u; rw [slotCnt_succ]; omega
  refine ⟨⟨by simp [hρ₁, hρ₀, hnv], ?_, ?_, ⟨fl', ?_, ?_⟩, ⟨OT', ?_, ?_, ?_⟩⟩,
    by simp [hρ₁, hρ₀, hi'], by simp [hρ₁, hρ₀, hje'], by simp; omega, by simp; omega⟩
  · exact (((hbl.setVar "u" _).setArr_of_ne (by decide) (by decide) _ _).setArr_of_ne
      (by decide) (by decide) _ _).setVar "j" _
  · rw [arrs_setVar, arrs_setArr, if_neg (by decide), hρ₁, arrs_setArr, if_neg (by decide),
      hρ₀, arrs_setVar]
    exact hoo
  · rw [arrs_setVar, arrs_setArr, if_pos rfl, hflρ₁, set_arrOf]
  · intro u hun
    rw [hjnew, hcntnew, hfl']
    simp only []
    by_cases h : DT p = u
    · rw [if_pos (by omega), if_pos h, ← h, hq₀]
    · rw [if_neg (by omega), if_neg h, hflE u hun, Nat.add_zero]
  · rw [arrs_setVar, arrs_setArr, if_neg (by decide), hotρ₁]
  · intro u hun q hq₁ hq₂
    rw [hjnew, hcntnew] at hq₂
    by_cases h : DT p = u
    · subst h
      rw [if_pos rfl] at hq₂
      by_cases hqe : q = fl (DT p)
      · refine ⟨by rw [hOT']; simp only []; rw [if_pos hqe]; exact hi, ?_⟩
        rw [hOT']; simp only []; rw [if_pos hqe]
        exact ⟨p, by omega, hj1, hjlt, rfl⟩
      · have := hsnd (DT p) hun q hq₁ (by omega)
        refine ⟨by rw [hOT']; simp only []; rw [if_neg hqe]; exact this.1, ?_⟩
        rw [hOT']; simp only []; rw [if_neg hqe]
        exact this.2.mono (by omega)
    · rw [if_neg h, Nat.add_zero] at hq₂
      have hne : q ≠ fl (DT p) := by
        rcases Nat.lt_or_ge u (DT p) with hlt | hge
        · have h₁ : outOff DT m (u + 1) ≤ outOff DT m (DT p) := outOff_mono DT m (by omega)
          have h₂ : outOff DT m u + slotCnt DT p u ≤ outOff DT m (u + 1) := by
            rw [outOff_succ]
            have := slotCnt_mono DT (show p ≤ m by omega) u
            omega
          omega
        · have hge' : DT p + 1 ≤ u := by omega
          have h₁ : outOff DT m (DT p + 1) ≤ outOff DT m u := outOff_mono DT m hge'
          omega
      have := hsnd u hun q hq₁ hq₂
      refine ⟨by rw [hOT']; simp only []; rw [if_neg hne]; exact this.1, ?_⟩
      rw [hOT']; simp only []; rw [if_neg hne]
      exact this.2.mono (by omega)
  · intro u hun z hzn hpts
    rw [hjnew] at hpts
    obtain ⟨s, hs₁, hs₂, hs₃, hs₄⟩ := hpts
    rcases Nat.lt_or_ge s p with hsp | hsp
    · obtain ⟨q, hq₁, hq₂, hq₃⟩ := hcmp u hun z hzn ⟨s, hsp, hs₂, hs₃, hs₄⟩
      have hne : q ≠ fl (DT p) := by
        by_cases h : DT p = u
        · subst h; rw [hq₀]; omega
        · rcases Nat.lt_or_ge u (DT p) with hlt | hge
          · have h₁ : outOff DT m (u + 1) ≤ outOff DT m (DT p) := outOff_mono DT m (by omega)
            have h₂ : outOff DT m u + slotCnt DT p u ≤ outOff DT m (u + 1) := by
              rw [outOff_succ]
              have := slotCnt_mono DT (show p ≤ m by omega) u
              omega
            omega
          · have h₁ : outOff DT m (DT p + 1) ≤ outOff DT m u := outOff_mono DT m (by omega)
            omega
      refine ⟨q, hq₁, ?_, by rw [hOT']; simp only []; rw [if_neg hne]; exact hq₃⟩
      rw [hjnew, hcntnew]; omega
    · have hsq : s = p := by omega
      have hz : z = i := hbl.owner_unique hzn hi (hsq ▸ hs₂) (hsq ▸ hs₃) hj1 hjlt
      have hu4 : DT p = u := by rw [← hsq]; exact hs₄
      refine ⟨fl (DT p), by rw [hq₀, hu4]; omega, ?_, ?_⟩
      · rw [hjnew, slotCnt_succ, if_pos hu4, hq₀, hu4]; omega
      · rw [hOT']; simp only []; exact hz.symm

/-- **The arcs, written into the out-blocks.** -/
theorem outFill_run {B n W m : ℕ} {DO DT : ℕ → ℕ} {σ : Env}
    (hnB : n + 1 < B) (hmB : m < B) (hmW : m ≤ W)
    (hn : σ.vars "n" = n) (hb : Blocks "doff" "dtg" n W m DO DT σ)
    (hoo : σ.arrs "ooff" = arrOf (n + 1) (outOff DT m))
    (hfl : σ.arrs "ofl" = arrOf n (outOff DT m))
    (hot : ∃ g, σ.arrs "otg" = arrOf W g) :
    ∃ σ' K, Run B RamAugment.outFill σ σ' K ∧ K ≤ 21 * m + 20 * n + 8 ∧
      ScatInv n W m DO DT m σ' := by
  obtain ⟨OT₀, hot₀⟩ := hot
  have hstep : ∀ i, i < n → ∀ τ, (ScatInv n W m DO DT (DO i) τ ∧ τ.vars "i" = i ∧ i ≤ n) →
      ∃ τ' K, Run B (RamAugment.blockScan "doff" "dtg" "i" "j" "jend" "u"
          (.seq (.store "otg" (.get "ofl" (.var "u")) (.var "i"))
            (.store "ofl" (.var "u") (.add (.get "ofl" (.var "u")) (.lit 1)))))
          τ τ' K ∧
        K ≤ 21 * (DO (i + 1) - DO i) + 12 ∧ τ'.vars "i" = i ∧
        (ScatInv n W m DO DT (DO (i + 1)) (τ'.setVar "i" (i + 1)) ∧
          (τ'.setVar "i" (i + 1)).vars "i" = i + 1 ∧ i + 1 ≤ n) := by
    intro i hi τ hτ
    obtain ⟨hci, hiv, -⟩ := hτ
    have hbl := hci.2.1
    have hrow : DO (i + 1) ≤ m := hbl.off_le (by omega)
    have hle : DO i ≤ DO (i + 1) := hbl.mono i hi
    have hgz : ScatInv n W m DO DT
        (((τ.setVar "j" (DO i)).setVar "jend" (DO (i + 1))).vars "j")
        ((τ.setVar "j" (DO i)).setVar "jend" (DO (i + 1))) := by
      obtain ⟨h1, h2, h3, ⟨fl, hf1, hf2⟩, ⟨OT, ho1, ho2, ho3⟩⟩ := hci
      exact ⟨by simpa using h1, (h2.setVar "j" _).setVar "jend" _, by simpa using h3,
        ⟨fl, by simpa using hf1, by simpa using hf2⟩,
        ⟨OT, by simpa using ho1, by simpa using ho2, by simpa using ho3⟩⟩
    obtain ⟨τ', K, hr, hK, hI', hj'⟩ :=
      blockScan_run (B := B) (o := "doff") (t := "dtg") (x := "i") (j := "j") (jend := "jend")
        (w := "u") (nv := n) (len := W) (Kb := 10) (v := i) (off := DO) (tgt := DT)
        (I := fun ρ => ScatInv n W m DO DT (ρ.vars "j") ρ ∧ ρ.vars "i" = i ∧
          ρ.vars "jend" = DO (i + 1) ∧ DO i ≤ ρ.vars "j" ∧ ρ.vars "j" ≤ DO (i + 1))
        (by decide) (by decide) (by omega) hi (by omega) hbl.offArr hle
        (le_trans hrow hbl.le) (by omega) hiv (fun ρ hρ => hρ.1.2.1.tgtArr)
        (fun p hp => lt_trans (hbl.target_lt p (by omega)) (by omega))
        (fun ρ hρ => ⟨hρ.2.2.1, hρ.2.2.2.2⟩)
        ⟨hgz, by simp [hiv], by simp, by simp, by simp [hle]⟩
        (fun ρ hρ hjlt => outFillSlot_run hnB hmB hmW hi hρ hjlt)
    refine ⟨τ', K, hr, hK, hI'.2.1, ?_⟩
    obtain ⟨hc', -⟩ := hI'
    rw [hj'] at hc'
    obtain ⟨h1, h2, h3, ⟨fl, hf1, hf2⟩, ⟨OT, ho1, ho2, ho3⟩⟩ := hc'
    exact ⟨⟨by simpa using h1, h2.setVar "i" _, by simpa using h3,
      ⟨fl, by simpa using hf1, hf2⟩, ⟨OT, by simpa using ho1, ho2, ho3⟩⟩, by simp, by omega⟩
  obtain ⟨σ', K, hrun, hK, hI⟩ :=
    forVerts_run (B := B) (n := n) (costs := fun i => 21 * (DO (i + 1) - DO i) + 12)
      (I := fun i τ => ScatInv n W m DO DT (DO i) τ ∧ τ.vars "i" = i ∧ i ≤ n)
      (σ := σ) hnB (fun _ _ h => h.1.1) (fun _ _ h => h.2.1) (fun _ _ h => h.2.2) hstep
      ⟨⟨by simpa using hn, hb.setVar "i" 0, by simpa using hoo,
        ⟨outOff DT m, by simpa using hfl, fun u _ => by rw [hb.zero, slotCnt_zero]; omega⟩,
        ⟨OT₀, by simpa using hot₀,
          fun u _ q h₁ h₂ => absurd h₂ (by rw [hb.zero, slotCnt_zero]; omega),
          fun u _ z _ hz => absurd hz (by
            rw [hb.zero]; rintro ⟨s, hs, -, -, -⟩; omega)⟩⟩, by simp, by omega⟩
  have hfin : ScatInv n W m DO DT m σ' := by
    have h := hI.1; rw [hb.last] at h; exact h
  refine ⟨σ', K, hrun, le_trans hK ?_, hfin⟩
  have hsum : ∑ i ∈ Finset.range n, (21 * (DO (i + 1) - DO i) + 12 + 8)
      = 21 * m + 20 * n := by
    have hpt : ∀ i ∈ Finset.range n,
        21 * (DO (i + 1) - DO i) + 12 + 8 = 21 * (DO (i + 1) - DO i) + 20 :=
      fun i _ => by omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.mul_sum, hb.sum_rowLen,
      Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  omega

theorem outOff_eq (T : ℕ → ℕ) (m : ℕ) :
    outOff T m = RamElim.psum (fun z => slotCnt T m z) := rfl

/-- **What the counting sort leaves**: the out-lists, as a block
structure whose block of `u` names exactly the vertices that point at
`u`. -/
theorem ScatInv.blocks {n W m : ℕ} {DO DT : ℕ → ℕ} {σ : Env}
    (h : ScatInv n W m DO DT m σ) :
    ∃ OT, Blocks "ooff" "otg" n W m (outOff DT m) OT σ ∧
      (∀ u < n, ∀ q, outOff DT m u ≤ q → q < outOff DT m (u + 1) → Pts DO DT (OT q) u) ∧
      (∀ u < n, ∀ z < n, Pts DO DT z u →
        ∃ q, outOff DT m u ≤ q ∧ q < outOff DT m (u + 1) ∧ OT q = z) := by
  obtain ⟨hnv, hbl, hoo, ⟨fl, -, -⟩, ⟨OT, hot, hsnd, hcmp⟩⟩ := h
  have hlast : outOff DT m n = m := outOff_last (fun s hs => hbl.target_lt s hs)
  have hend : ∀ u, outOff DT m u + slotCnt DT m u = outOff DT m (u + 1) :=
    fun u => (outOff_succ DT m u).symm
  refine ⟨OT, ⟨hoo, hot, outOff_zero DT m, hlast, fun i _ => outOff_mono DT m (by omega),
    hbl.le, fun q hq => ?_⟩, fun u hu q h₁ h₂ => ?_, fun u hu z hz hp => ?_⟩
  · obtain ⟨w, hw, h₁, h₂⟩ :=
      RamElim.exists_block (ID := fun z => slotCnt DT m z) (m := n) (t := q)
        (by rw [← outOff_eq, hlast]; exact hq)
    rw [← outOff_eq] at h₁ h₂
    exact (hsnd w hw q h₁ (by rw [hend]; exact h₂)).1
  · exact (hsnd u hu q h₁ (by rw [hend]; exact h₂)).2.pts
  · obtain ⟨q, hq₁, hq₂, hq₃⟩ := hcmp u hu z hz (hp.ptsLt hbl hz)
    exact ⟨q, hq₁, by rw [← hend]; exact hq₂, hq₃⟩

/-! ### The out-lists

The three passes, sequenced. -/

/-- **The out-lists of `D`.** -/
theorem outPass_run {B n W m : ℕ} {DO DT : ℕ → ℕ} {σ : Env}
    (hnB : n + 1 < B) (hmB : m < B) (hmW : m ≤ W)
    (hn : σ.vars "n" = n) (hb : Blocks "doff" "dtg" n W m DO DT σ)
    (hooff : ∃ g, σ.arrs "ooff" = arrOf (n + 1) g ∧ ∀ k ≤ n, g k = 0)
    (hofl : ∃ g, σ.arrs "ofl" = arrOf n g) (hotg : ∃ g, σ.arrs "otg" = arrOf W g) :
    ∃ σ' K, Run B RamAugment.outPass σ σ' K ∧ K ≤ 42 * m + 63 * n + 24 ∧
      ScatInv n W m DO DT m σ' ∧
      (∀ a, a ≠ "ooff" → a ≠ "ofl" → a ≠ "otg" → σ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ "i" → y ≠ "j" → y ≠ "jend" → y ≠ "u" → σ'.vars y = σ.vars y) := by
  have hlast : outOff DT m n = m := outOff_last (fun s hs => hb.target_lt s hs)
  obtain ⟨σ₁, K₁, hr₁, hK₁, hI₁⟩ := outCount_run hnB hmB hn hb hooff
  have hfr₁ : ∀ a, a ≠ "ooff" → σ₁.arrs a = σ.arrs a :=
    fun a ha => hr₁.frame_arr a (by simp [RamAugment.outCount, RamAugment.forVerts,
      RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.warrs, ha])
  have hfv₁ : ∀ y, y ≠ "i" → y ≠ "j" → y ≠ "jend" → y ≠ "u" → σ₁.vars y = σ.vars y :=
    fun y h1 h2 h3 h4 => hr₁.frame_var y (by simp [RamAugment.outCount, RamAugment.forVerts,
      RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.wvars, h1, h2, h3, h4])
  obtain ⟨σ₂, K₂, hr₂, hK₂, hn₂, hoo₂, hfl₂⟩ :=
    prefixPass_run (B := B) (a := "ooff") (b := "ofl") (d := fun z => slotCnt DT m z)
      (by decide) hnB (by rw [← outOff_eq, hlast]; exact hmB) hI₁.1
      (by obtain ⟨g, hg, hg0, hgu⟩ := hI₁.2.2; exact ⟨g, hg, hg0, hgu⟩)
      (by obtain ⟨g, hg⟩ := hofl; exact ⟨g, by rw [hfr₁ "ofl" (by decide)]; exact hg⟩)
  have hfr₂ : ∀ a, a ≠ "ooff" → a ≠ "ofl" → σ₂.arrs a = σ₁.arrs a :=
    fun a ha hb' => hr₂.frame_arr a (by simp [prefixCom, RamAugment.forVerts, Com.warrs,
      ha, hb'])
  have hfv₂ : ∀ y, y ≠ "i" → σ₂.vars y = σ₁.vars y :=
    fun y hy => hr₂.frame_var y (by simp [prefixCom, RamAugment.forVerts, Com.wvars, hy])
  rw [← outOff_eq] at hoo₂ hfl₂
  obtain ⟨σ₃, K₃, hr₃, hK₃, hI₃⟩ :=
    outFill_run (B := B) (n := n) (W := W) (m := m) (DO := DO) (DT := DT) hnB hmB hmW hn₂
      (hI₁.2.1.of_eq (hfr₂ "doff" (by decide) (by decide))
        (hfr₂ "dtg" (by decide) (by decide))) hoo₂ hfl₂
      (by
        obtain ⟨g, hg⟩ := hotg
        refine ⟨g, ?_⟩
        rw [hfr₂ "otg" (by decide) (by decide), hfr₁ "otg" (by decide)]
        exact hg)
  have hfr₃ : ∀ a, a ≠ "otg" → a ≠ "ofl" → σ₃.arrs a = σ₂.arrs a :=
    fun a ha hb' => hr₃.frame_arr a (by simp [RamAugment.outFill, RamAugment.forVerts,
      RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.warrs, ha, hb'])
  have hfv₃ : ∀ y, y ≠ "i" → y ≠ "j" → y ≠ "jend" → y ≠ "u" → σ₃.vars y = σ₂.vars y :=
    fun y h1 h2 h3 h4 => hr₃.frame_var y (by simp [RamAugment.outFill, RamAugment.forVerts,
      RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.wvars, h1, h2, h3, h4])
  refine ⟨σ₃, K₁ + (K₂ + K₃), hr₁.seq (hr₂.seq hr₃), by omega, hI₃,
    fun a h1 h2 h3 => ?_, fun y h1 h2 h3 h4 => ?_⟩
  · rw [hfr₃ a h3 h2, hfr₂ a h1 h2, hfr₁ a h1]
  · rw [hfv₃ y h1 h2 h3 h4, hfv₂ y h1, hfv₁ y h1 h2 h3 h4]

/-- **The bridge to the assembly section.** What the sort writes into
the out-blocks is, read through `RamElim.InCsr`, exactly
`RamAugment.outSet`. -/
theorem pts_iff_mem_outSet {n m : ℕ} {D : Orientation n} {DO DT : ℕ → ℕ}
    (h : InCsr D m DO DT) {z u : ℕ} (hz : z < n) (hu : u < n) :
    Pts DO DT z u ↔ (⟨z, hz⟩ : Fin n) ∈ RamAugment.outSet D ⟨u, hu⟩ := by
  rw [RamAugment.mem_outSet, h.mem_iff ⟨z, hz⟩ ⟨u, hu⟩, Pts]

/-! ### The mask

`RamAugment.alvSet` is the one pass with no data in it: the whole
fraternity graph is in play, so every cell of the mask is one. -/

/-- **The mask the engine is handed.** -/
theorem alvSet_run {B n : ℕ} {σ : Env} (hnB : n + 1 < B) (hn : σ.vars "n" = n)
    (halv : ∃ g, σ.arrs "alv" = arrOf n g) :
    ∃ σ' K, Run B RamAugment.alvSet σ σ' K ∧ K ≤ 11 * n + 8 ∧
      σ'.vars "n" = n ∧ σ'.arrs "alv" = arrOf n (fun _ => 1) ∧
      (∀ a, a ≠ "alv" → σ'.arrs a = σ.arrs a) ∧ (∀ y, y ≠ "i" → σ'.vars y = σ.vars y) := by
  obtain ⟨g₀, hg₀⟩ := halv
  have hstep : ∀ i, i < n → ∀ τ,
      (τ.vars "n" = n ∧ τ.vars "i" = i ∧ i ≤ n ∧
        ∃ g, τ.arrs "alv" = arrOf n g ∧ ∀ k < i, g k = 1) →
      ∃ τ' K, Run B (.store "alv" (.var "i") (.lit 1)) τ τ' K ∧ K ≤ 3 ∧ τ'.vars "i" = i ∧
        ((τ'.setVar "i" (i + 1)).vars "n" = n ∧ (τ'.setVar "i" (i + 1)).vars "i" = i + 1 ∧
          i + 1 ≤ n ∧ ∃ g, (τ'.setVar "i" (i + 1)).arrs "alv" = arrOf n g ∧
            ∀ k < i + 1, g k = 1) := by
    rintro i hi τ ⟨hnv, hiv, -, g, hga, hgl⟩
    have eivar : (Expr.var "i").evalB B τ = some i := by
      rw [← hiv]; exact evalB_var (by rw [hiv]; omega)
    have hlen : i < (τ.arrs "alv").length := by rw [hga, length_arrOf]; exact hi
    refine ⟨τ.setArr "alv" i 1, 3, (Run.store eivar (evalB_lit (by omega)) hlen).mono (by simp),
      le_rfl, by simp [hiv], by simp [hnv], by simp, by omega,
      fun k => if k = i then 1 else g k, ?_, fun k hk => ?_⟩
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, hga, set_arrOf]
    · simp only []
      rcases Nat.lt_or_ge k i with hk' | hk'
      · rw [if_neg (by omega)]; exact hgl k hk'
      · rw [if_pos (by omega)]
  obtain ⟨σ', K, hrun, hK, hI⟩ :=
    forVerts_run (B := B) (n := n) (costs := fun _ => 3)
      (I := fun i τ => τ.vars "n" = n ∧ τ.vars "i" = i ∧ i ≤ n ∧
        ∃ g, τ.arrs "alv" = arrOf n g ∧ ∀ k < i, g k = 1)
      (σ := σ) hnB (fun _ _ h => h.1) (fun _ _ h => h.2.1) (fun _ _ h => h.2.2.1) hstep
      ⟨by simpa using hn, by simp, by omega,
        ⟨g₀, by simpa using hg₀, fun k hk => absurd hk (by omega)⟩⟩
  obtain ⟨hn', -, -, g, hga, hgl⟩ := id hI
  refine ⟨σ', K, hrun, le_trans hK (by simp [Finset.sum_const, Finset.card_range]; omega), hn',
    by rw [hga]; exact RamDriverOrder.arrOf_congr fun k hk => hgl k hk,
    fun a ha => hrun.frame_arr a ?_, fun y hy => hrun.frame_var y ?_⟩
  · simp [RamAugment.forVerts, Com.warrs, ha]
  · simp [RamAugment.forVerts, Com.wvars, hy]

/-! ### The definitions, checked against the round's own worked example

House discipline: the arithmetic this file introduces is *seen* on the
orientation `RamAugment.Demo` runs the round on — the four-vertex one
with in-lists `∅ | 0 | 0 1 | 2`, so `DO = 0, 0, 1, 3, 4` and
`DT = 0, 0, 1, 2` — where the out-lists are `1 2 | 2 | 3 | ` by hand.
The two program identities the file rests on, `blockScan_eq` and the
three `prefixCom` instances, are `rfl` and so are checked by the
elaborator. -/

namespace Demo

/-- The offsets of the in-lists `∅ | 0 | 0 1 | 2`. -/
def demoDO : ℕ → ℕ := fun i => if i = 0 then 0 else if i = 1 then 0 else
  if i = 2 then 1 else if i = 3 then 3 else 4

/-- Their targets `| 0 | 0 1 | 2`. -/
def demoDT : ℕ → ℕ := fun s => if s = 0 then 0 else if s = 1 then 0 else
  if s = 2 then 1 else 2

-- the out-degrees `2, 1, 1, 0` of `1 2 | 2 | 3 | `
#guard (List.range 4).map (slotCnt demoDT 4) = [2, 1, 1, 0]

-- and the out-block boundaries they sum to, the last of them the arc count
#guard (List.range 5).map (outOff demoDT 4) = [0, 2, 3, 4, 4]

end Demo

/-! ### The frontier

What this file discharges of `RamAugment.Implements`, and what it does
not.

**Done.** The two combinators every pass is built from — `blockScan_run`
and `forVerts_run` — the row view `Blocks` the round's over-wide arrays
need, the counting-sort arithmetic (`slotCnt`, `outOff`), the prefix
sum `prefixPass_run` (which is *literally* the program of
`RamAugment.outPrefix`, `RamAugment.fratPrefix` and
`RamAugment.asmPrefix` alike, so the other two counting sorts inherit
it), the whole of `RamAugment.outPass` (`outPass_run`, with the block
content read back as `RamAugment.outSet` by `pts_iff_mem_outSet`), and
`RamAugment.alvSet` (`alvSet_run`).

**Open.** `RamAugment.fratPass` and `RamAugment.asmPass` — the four
stamped enumerations — the `RamElim.elimCom` call, and the sequencing
of the five into `RamAugment.Implements`.

* The stamped enumerations are the file's one piece of new
  mathematics, and the shape they want is the one `ScatInv` already
  has: an invariant indexed by a *pointer* into the outer block
  structure, with a set-valued clause saying which vertices carry a
  stamp and a counter clause saying how many have been emitted. What is
  new against `ScatInv` is that a candidate can be reached twice, so
  the emitted set is a *support* and the counter is its cardinality —
  which is what `RamAugment.card_inN_augOr` is stated against, and what
  makes `fratCount` and `fratFill` agree.
* The `elimCom` call is closed outright by `RamAugment.ElimAvail` at
  `ns = fratSlots D`, since wave A2 made `RamElim.ElimPre`'s scratch
  width a caller's choice; nothing in this file is needed for it.
* The sequencing needs, per pass, the frame conditions
  `outPass_run` and `alvSet_run` already export — which array names a
  pass leaves alone — and nothing else. -/

end Lax3Proofs.RamDriverAugment
