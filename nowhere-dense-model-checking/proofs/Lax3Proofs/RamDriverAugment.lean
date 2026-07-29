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

/-! ### The row scan, charged per slot

`rowScan_run` charges every slot of a row the same, which is what a
pass whose per-slot work is a constant needs — and the three passes
above are of that kind. The nested passes are not: the turn of
`RamAugment.asmStamp` at a slot naming `w` walks *both* blocks of `w`,
and no constant bounds the out-block. So the scan is walked once more
with a cost function of the slot, and with the caller's invariant
indexed by the pointer rather than carrying it in the state — which is
also what an invariant accumulating a set wants, since the set it has
seen is a function of the pointer. -/

/-- **A row, scanned, at a cost per slot.** -/
theorem rowScanC_run {B : ℕ} {t j jend w : String} {c : Com} {len lo hi : ℕ}
    {costs tgt : ℕ → ℕ} {I : ℕ → Env → Prop} {σ : Env}
    (hhiB : hi < B) (hB1 : 1 < B) (hhilen : hi ≤ len)
    (htgt : ∀ p τ, I p τ → τ.arrs t = arrOf len tgt)
    (htB : ∀ p, p < hi → tgt p < B)
    (hIb : ∀ p τ, I p τ → τ.vars jend = hi ∧ τ.vars j = p ∧ p ≤ hi)
    (hstep : ∀ p τ, I p τ → p < hi →
      ∃ τ' K, Run B c (τ.setVar w (tgt p)) τ' K ∧ K ≤ costs p ∧ τ'.vars j = p ∧
        I (p + 1) (τ'.setVar j (p + 1)))
    (hI : I lo σ) :
    ∃ σ' K, Run B (Csr.scan j jend (scanBody t j w c)) σ σ' K ∧
      K ≤ (∑ p ∈ Finset.Ico lo hi, (costs p + 11)) + 4 ∧ I hi σ' := by
  set J : Env → Prop := fun τ => ∃ p, I p τ with hJ
  set Φ : Env → ℕ := fun τ => ∑ s ∈ Finset.Ico (τ.vars j) hi, (costs s + 11) with hΦ
  have hdef : ∀ τ, J τ → ∃ v, (Cond.lt (.var j) (.var jend)).evalB B τ = some v := by
    rintro τ ⟨p, hIp⟩
    obtain ⟨hje, hjv, hple⟩ := hIb p τ hIp
    exact evalB_condLt_vars (by rw [hjv]; omega) (by rw [hje]; omega)
  have hbody : ∀ τ, J τ → (Cond.lt (.var j) (.var jend)).evalB B τ = some true →
      ∃ τ' K, Run B (scanBody t j w c) τ τ' K ∧ J τ' ∧
        1 + (Cond.lt (Expr.var j) (Expr.var jend)).size + K + Φ τ' ≤ Φ τ := by
    rintro τ ⟨p, hIp⟩ hc
    obtain ⟨hje, hjv, hple⟩ := hIb p τ hIp
    have hlt : p < hi := by
      have h := lt_of_condLt_true hc
      rw [hjv, hje] at h; exact h
    obtain ⟨τ', K, hr, hK, hjfix, hI'⟩ := hstep p τ hIp hlt
    have hrun : Run B (scanBody t j w c) τ (τ'.setVar j (τ.vars j + 1)) (K + 7) :=
      scanBody_run (htgt p τ hIp) (by rw [hjv]; omega) (by rw [hjv]; omega)
        (by rw [hjv]; exact htB p hlt) hB1 (by rw [hjv]; exact hr) (by rw [hjfix, hjv])
    rw [hjv] at hrun
    refine ⟨τ'.setVar j (p + 1), K + 7, hrun, ⟨p + 1, hI'⟩, ?_⟩
    have hsplit : Φ τ = (costs p + 11) + ∑ s ∈ Finset.Ico (p + 1) hi, (costs s + 11) := by
      show ∑ s ∈ Finset.Ico (τ.vars j) hi, (costs s + 11) = _
      rw [hjv]; exact Finset.sum_eq_sum_Ico_succ_bot hlt _
    have hτ' : Φ (τ'.setVar j (p + 1)) = ∑ s ∈ Finset.Ico (p + 1) hi, (costs s + 11) := by
      show ∑ s ∈ Finset.Ico ((τ'.setVar j (p + 1)).vars j) hi, (costs s + 11) = _
      simp
    simp only [size_condLt, size_var, hτ', hsplit]
    omega
  obtain ⟨σ', K₀, hrun, hJ', hfalse, hpay⟩ :=
    Run.while_potential (B := B) J Φ hdef hbody (σ := σ) ⟨lo, hI⟩
  obtain ⟨p, hIp⟩ := hJ'
  obtain ⟨hje', hj', hple'⟩ := hIb p σ' hIp
  have hex : p = hi := by
    have h := le_of_condLt_false hfalse
    rw [hj', hje'] at h; omega
  have hΦ0 : Φ σ = ∑ s ∈ Finset.Ico lo hi, (costs s + 11) := by
    show ∑ s ∈ Finset.Ico (σ.vars j) hi, (costs s + 11) = _
    rw [(hIb lo σ hI).2.1]
  have hΦn : Φ σ' = 0 := by
    show ∑ s ∈ Finset.Ico (σ'.vars j) hi, (costs s + 11) = 0
    rw [hj', hex]; simp
  refine ⟨σ', K₀, hrun, ?_, hex ▸ hIp⟩
  rw [hΦ0, hΦn] at hpay
  simp only [size_condLt, size_var] at hpay
  omega

/-- **The whole combinator, at a cost per slot.** -/
theorem blockScanC_run {B : ℕ} {o t x j jend w : String} {c : Com}
    {nv len v : ℕ} {off tgt costs : ℕ → ℕ} {I : ℕ → Env → Prop} {σ : Env}
    (hxj : x ≠ j) (_hjje : j ≠ jend) (hB1 : 1 < B)
    (hv : v < nv) (hvB : v + 1 < B)
    (hoff : σ.arrs o = arrOf (nv + 1) off)
    (hle : off v ≤ off (v + 1)) (hhilen : off (v + 1) ≤ len) (hhiB : off (v + 1) < B)
    (hxv : σ.vars x = v)
    (htgt : ∀ p τ, I p τ → τ.arrs t = arrOf len tgt)
    (htB : ∀ p, p < off (v + 1) → tgt p < B)
    (hIb : ∀ p τ, I p τ → τ.vars jend = off (v + 1) ∧ τ.vars j = p ∧ p ≤ off (v + 1))
    (hstart : I (off v) ((σ.setVar j (off v)).setVar jend (off (v + 1))))
    (hstep : ∀ p τ, I p τ → p < off (v + 1) →
      ∃ τ' K, Run B c (τ.setVar w (tgt p)) τ' K ∧ K ≤ costs p ∧ τ'.vars j = p ∧
        I (p + 1) (τ'.setVar j (p + 1))) :
    ∃ σ' K, Run B (RamAugment.blockScan o t x j jend w c) σ σ' K ∧
      K ≤ (∑ p ∈ Finset.Ico (off v) (off (v + 1)), (costs p + 11)) + 12 ∧
      I (off (v + 1)) σ' := by
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
  obtain ⟨σ', K, hrun, hK, hI'⟩ :=
    rowScanC_run (B := B) (t := t) (j := j) (jend := jend) (w := w) (c := c) (len := len)
      (lo := off v) (hi := off (v + 1)) (costs := costs) (tgt := tgt) (I := I)
      (σ := (σ.setVar j (off v)).setVar jend (off (v + 1)))
      hhiB hB1 hhilen htgt htB hIb hstep hstart
  exact ⟨σ', 8 + K, ((Run.assign e₁).seq (Run.assign e₂)).mono
    (by simp only [size_get, size_var, size_add, size_lit]; omega) |>.seq hrun, by omega, hI'⟩

/-! ### What a nested scan accumulates

A scan of the row of `v` that contributes a set `f (tgt s)` at every
slot `s` has seen, by the time its pointer is at `p`, the union of
those; the whole row's contribution is that at the row's end. With `f`
a singleton this is the row's targets, and with `f` the contribution of
an inner scan it is what the nested walk enumerates. -/

/-- What a scan of the row of `v` has accumulated by the pointer `p`. -/
def accUpto (off tgt : ℕ → ℕ) (f : ℕ → Finset ℕ) (v p : ℕ) : Finset ℕ :=
  (Finset.Ico (off v) p).biUnion (fun s => f (tgt s))

/-- And the whole row's contribution. -/
def rowAcc (off tgt : ℕ → ℕ) (f : ℕ → Finset ℕ) (v : ℕ) : Finset ℕ :=
  accUpto off tgt f v (off (v + 1))

theorem mem_accUpto {off tgt : ℕ → ℕ} {f : ℕ → Finset ℕ} {v p u : ℕ} :
    u ∈ accUpto off tgt f v p ↔ ∃ s, off v ≤ s ∧ s < p ∧ u ∈ f (tgt s) := by
  rw [accUpto, Finset.mem_biUnion]
  constructor
  · rintro ⟨s, hs, hu⟩
    rw [Finset.mem_Ico] at hs
    exact ⟨s, hs.1, hs.2, hu⟩
  · rintro ⟨s, h₁, h₂, hu⟩
    exact ⟨s, Finset.mem_Ico.2 ⟨h₁, h₂⟩, hu⟩

theorem mem_rowAcc {off tgt : ℕ → ℕ} {f : ℕ → Finset ℕ} {v u : ℕ} :
    u ∈ rowAcc off tgt f v ↔ ∃ s, off v ≤ s ∧ s < off (v + 1) ∧ u ∈ f (tgt s) :=
  mem_accUpto

@[simp] theorem accUpto_start (off tgt : ℕ → ℕ) (f : ℕ → Finset ℕ) (v : ℕ) :
    accUpto off tgt f v (off v) = ∅ := by simp [accUpto]

theorem accUpto_succ {off tgt : ℕ → ℕ} {f : ℕ → Finset ℕ} {v p : ℕ} (h : off v ≤ p) :
    accUpto off tgt f v (p + 1) = accUpto off tgt f v p ∪ f (tgt p) := by
  classical
  rw [accUpto, accUpto, show p + 1 = Nat.succ p from rfl,
    Nat.Ico_succ_right_eq_insert_Ico h, Finset.biUnion_insert]
  exact Finset.union_comm _ _

/-- A `Finset (Fin n)` read at the number level, which is what a walk
over an array of vertex numbers speaks in. -/
def valSet {n : ℕ} (S : Finset (Fin n)) : Finset ℕ := S.image Fin.val

theorem mem_valSet {n : ℕ} {S : Finset (Fin n)} {k : ℕ} :
    k ∈ valSet S ↔ ∃ h : k < n, (⟨k, h⟩ : Fin n) ∈ S := by
  constructor
  · intro hk
    obtain ⟨v, hv, hvk⟩ := Finset.mem_image.1 hk
    refine ⟨hvk ▸ v.isLt, ?_⟩
    have he : (⟨k, hvk ▸ v.isLt⟩ : Fin n) = v := Fin.ext hvk.symm
    rw [he]; exact hv
  · rintro ⟨h, hm⟩
    exact Finset.mem_image.2 ⟨⟨k, h⟩, hm, rfl⟩

theorem mem_valSet_of {n : ℕ} {S : Finset (Fin n)} {v : Fin n} (h : v ∈ S) :
    (v : ℕ) ∈ valSet S := Finset.mem_image_of_mem _ h

theorem card_valSet {n : ℕ} (S : Finset (Fin n)) : (valSet S).card = S.card :=
  Finset.card_image_of_injective _ Fin.val_injective

theorem valSet_lt {n : ℕ} {S : Finset (Fin n)} {k : ℕ} (h : k ∈ valSet S) : k < n := by
  obtain ⟨h', -⟩ := mem_valSet.1 h; exact h'

/-! ### A weighted count over the slots

`sum_slotCnt` says the counts add up to the number of slots. Weighted,
it is the exchange the nested passes' cost needs: a sum over the slots
of something depending only on the slot's target is a sum over the
targets, each weighted by how often it occurs. -/

theorem sum_slot_weight {T : ℕ → ℕ} {nv : ℕ} (g : ℕ → ℕ) :
    ∀ m, (∀ s < m, T s < nv) →
      ∑ p ∈ Finset.range m, g (T p) = ∑ u ∈ Finset.range nv, slotCnt T m u * g u := by
  classical
  intro m
  induction m with
  | zero => intro _; simp
  | succ p ih =>
      intro h
      have hp : ∀ s < p, T s < nv := fun s hs => h s (by omega)
      have hTp : T p < nv := h p (by omega)
      have hc : ∀ u ∈ Finset.range nv, slotCnt T (p + 1) u * g u
          = slotCnt T p u * g u + (if T p = u then g u else 0) := by
        intro u _
        rw [slotCnt_succ]
        by_cases hu : T p = u
        · rw [if_pos hu, if_pos hu]; ring
        · rw [if_neg hu, if_neg hu]; ring
      rw [Finset.sum_range_succ, ih hp, Finset.sum_congr rfl hc, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_ite_eq (Finset.range nv) (T p) g, if_pos (Finset.mem_range.2 hTp)]

/-! ### The rows tile the slots

A count over the whole slot array splits into a count over each row,
which is what turns a statement about a block structure into a
statement about the array it cuts. What it is for here is the one place
in the round where the *inner* walk of a nested scan has no constant
bound: `RamAugment.asmStamp` walks the out-block of every vertex the
current one points at, and only the exchange below — an out-slot names
`w` as often as `w` has in-neighbours — keeps the pass linear. -/

theorem tile_filter_card {off : ℕ → ℕ} {nv m : ℕ} (hz : off 0 = 0) (hlast : off nv = m)
    (hmono : ∀ i < nv, off i ≤ off (i + 1)) (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range m).filter P).card
      = ∑ u ∈ Finset.range nv, ((Finset.Ico (off u) (off (u + 1))).filter P).card := by
  classical
  have key : ∀ k, k ≤ nv →
      ((Finset.range (off k)).filter P).card
        = ∑ u ∈ Finset.range k, ((Finset.Ico (off u) (off (u + 1))).filter P).card := by
    intro k
    induction k with
    | zero => intro _; simp [hz]
    | succ k ih =>
        intro hk
        have hmk : off k ≤ off (k + 1) := hmono k (by omega)
        have hsplit : Finset.range (off (k + 1))
            = Finset.range (off k) ∪ Finset.Ico (off k) (off (k + 1)) := by
          rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
            Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hmk]
        have hdis : Disjoint ((Finset.range (off k)).filter P)
            ((Finset.Ico (off k) (off (k + 1))).filter P) := by
          rw [Finset.disjoint_left]
          intro a ha ha'
          rw [Finset.mem_filter, Finset.mem_range] at ha
          rw [Finset.mem_filter, Finset.mem_Ico] at ha'
          omega
        rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdis, ih (by omega),
          Finset.sum_range_succ]
  rw [← hlast]; exact key nv le_rfl

/-- The in-degrees add up to the number of arcs. -/
theorem sum_card_inN {n m : ℕ} {D : Orientation n} {IO IT : ℕ → ℕ} (h : InCsr D m IO IT) :
    ∑ v : Fin n, (D.inN v).card = m := by
  have key : ∀ k, k ≤ n → ∑ i ∈ Finset.range k, (IO (i + 1) - IO i) = IO k := by
    intro k
    induction k with
    | zero => intro _; simp [h.zero]
    | succ k ih =>
        intro hk
        rw [Finset.sum_range_succ, ih (by omega)]
        have := h.mono k (by omega)
        omega
  rw [Finset.sum_congr rfl (fun v _ => (h.len v).symm),
    Fin.sum_univ_eq_sum_range (fun i => IO (i + 1) - IO i) n, key n le_rfl, h.last]

/-- The in-degree of a vertex, at the number level. -/
def inDeg {n : ℕ} (D : Orientation n) (w : ℕ) : ℕ :=
  if h : w < n then (D.inN ⟨w, h⟩).card else 0

theorem sum_inDeg {n m : ℕ} {D : Orientation n} {IO IT : ℕ → ℕ} (h : InCsr D m IO IT) :
    ∑ w ∈ Finset.range n, inDeg D w = m := by
  rw [← Fin.sum_univ_eq_sum_range (fun w => inDeg D w) n, ← sum_card_inN h]
  exact Finset.sum_congr rfl fun v _ => by rw [inDeg, dif_pos v.isLt]

/-- **The exchange.** An out-slot names `w` exactly as often as `w` has
in-neighbours: every one of them contributes a slot to a different
out-block, and the two counts add up to the same number of arcs, so
neither can be short anywhere. -/
theorem slotCnt_out_eq {n W m : ℕ} {D : Orientation n} {DO DT OT : ℕ → ℕ} {σ : Env}
    (hcsr : InCsr D m DO DT) (hbl : Blocks "ooff" "otg" n W m (outOff DT m) OT σ)
    (hcmp : ∀ u < n, ∀ z < n, Pts DO DT z u →
      ∃ q, outOff DT m u ≤ q ∧ q < outOff DT m (u + 1) ∧ OT q = z) :
    ∀ w ∈ Finset.range n, inDeg D w = slotCnt OT m w := by
  classical
  have hlow : ∀ w ∈ Finset.range n, inDeg D w ≤ slotCnt OT m w := by
    intro w hw
    rw [Finset.mem_range] at hw
    rw [inDeg, dif_pos hw, slotCnt,
      tile_filter_card hbl.zero hbl.last hbl.mono (fun s => OT s = w)]
    set F : ℕ → ℕ := fun u =>
      ((Finset.Ico (outOff DT m u) (outOff DT m (u + 1))).filter (fun s => OT s = w)).card
      with hF
    have hone : ∀ v : Fin n, v ∈ D.inN ⟨w, hw⟩ → 1 ≤ F (v : ℕ) := by
      intro v hv
      have hpts : Pts DO DT w (v : ℕ) :=
        (pts_iff_mem_outSet hcsr hw v.isLt).2 (RamAugment.mem_outSet.2 hv)
      obtain ⟨q, h₁, h₂, h₃⟩ := hcmp (v : ℕ) v.isLt w hw hpts
      refine Finset.card_pos.2 ⟨q, Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨h₁, h₂⟩, h₃⟩⟩
    calc (D.inN ⟨w, hw⟩).card = ∑ _v ∈ D.inN ⟨w, hw⟩, 1 := by simp
      _ ≤ ∑ v ∈ D.inN ⟨w, hw⟩, F (v : ℕ) := Finset.sum_le_sum fun v hv => hone v hv
      _ ≤ ∑ v : Fin n, F (v : ℕ) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = ∑ u ∈ Finset.range n, F u := Fin.sum_univ_eq_sum_range F n
  have hsum : ∑ w ∈ Finset.range n, inDeg D w = ∑ w ∈ Finset.range n, slotCnt OT m w := by
    rw [sum_inDeg hcsr, sum_slotCnt (fun s hs => hbl.target_lt s hs)]
  exact (Finset.sum_eq_sum_iff_of_le hlow).1 hsum

/-! ### The stamps

Every stamp walk of the round is the same command: scan a row and write
a literal into the cell of every target. What it leaves is the stamp
array carrying that literal on the row's targets and its old value
elsewhere — a set *union* at `b = 1` and a set *difference* at `b = 0`
— so one lemma serves the walk that sets a stamp and the walk that
clears it, which is exactly the pairing the round's passes are built
out of. -/

/-- The vertices a row names. -/
def rowTgt (off tgt : ℕ → ℕ) (v : ℕ) : Finset ℕ := rowAcc off tgt (fun z => {z}) v

theorem mem_rowTgt {off tgt : ℕ → ℕ} {v u : ℕ} :
    u ∈ rowTgt off tgt v ↔ ∃ s, off v ≤ s ∧ s < off (v + 1) ∧ tgt s = u := by
  rw [rowTgt, mem_rowAcc]
  constructor
  · rintro ⟨s, h₁, h₂, h₃⟩
    exact ⟨s, h₁, h₂, (Finset.mem_singleton.1 h₃).symm⟩
  · rintro ⟨s, h₁, h₂, h₃⟩
    exact ⟨s, h₁, h₂, Finset.mem_singleton.2 h₃.symm⟩

/-- What the stamp array `s` holds after a walk that wrote `b` into the
cells of `S`. -/
def Marks (s : String) (n b : ℕ) (S : Finset ℕ) (g : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ g', τ.arrs s = arrOf n g' ∧ ∀ k < n, g' k = if k ∈ S then b else g k

theorem Marks.congr {s : String} {n b : ℕ} {S S' : Finset ℕ} {g : ℕ → ℕ} {τ : Env}
    (h : Marks s n b S g τ) (hS : S = S') : Marks s n b S' g τ := hS ▸ h

/-- **A row of stamps.** -/
theorem stampRow_run {B : ℕ} {o t x j jend u s : String} {n nv len v b : ℕ}
    {off tgt g : ℕ → ℕ} {σ : Env}
    (hxj : x ≠ j) (hjje : j ≠ jend) (hju : j ≠ u) (hjeu : jend ≠ u) (hst : s ≠ t)
    (hB1 : 1 < B) (hv : v < nv) (hvB : v + 1 < B) (hbB : b < B) (hnB : n < B)
    (hoff : σ.arrs o = arrOf (nv + 1) off) (hle : off v ≤ off (v + 1))
    (hlen : off (v + 1) ≤ len) (hhiB : off (v + 1) < B) (hxv : σ.vars x = v)
    (htgt : σ.arrs t = arrOf len tgt) (htn : ∀ p, p < off (v + 1) → tgt p < n)
    (hsa : σ.arrs s = arrOf n g) :
    ∃ σ' K, Run B (RamAugment.blockScan o t x j jend u (.store s (.var u) (.lit b))) σ σ' K ∧
      K ≤ 14 * (off (v + 1) - off v) + 12 ∧ Marks s n b (rowTgt off tgt v) g σ' ∧
      (∀ a, a ≠ s → σ'.arrs a = σ.arrs a) ∧
      (∀ y, y ≠ j → y ≠ jend → y ≠ u → σ'.vars y = σ.vars y) := by
  classical
  obtain ⟨σ', K, hrun, hK, hI⟩ :=
    blockScanC_run (B := B) (o := o) (t := t) (x := x) (j := j) (jend := jend) (w := u)
      (c := .store s (.var u) (.lit b)) (nv := nv) (len := len) (v := v) (off := off)
      (tgt := tgt) (costs := fun _ => 3)
      (I := fun p τ => τ.arrs t = arrOf len tgt ∧
        Marks s n b (accUpto off tgt (fun z => {z}) v p) g τ ∧
        τ.vars jend = off (v + 1) ∧ τ.vars j = p ∧ off v ≤ p ∧ p ≤ off (v + 1))
      hxj hjje hB1 hv hvB hoff hle hlen hhiB hxv (fun _ _ h => h.1)
      (fun p hp => lt_trans (htn p hp) hnB)
      (fun _ _ h => ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩)
      ⟨by simpa using htgt,
        ⟨g, by simpa using hsa, fun k _ => by simp⟩,
        by simp, by simp [hjje], le_rfl, hle⟩
      (by
        rintro p τ ⟨htτ, ⟨g', hg', hgk⟩, hje, hjv, hlop, hple⟩ hp
        have hzn : tgt p < n := htn p hp
        set z := tgt p with hz
        have huz : (τ.setVar u z).vars u = z := by simp
        have eu : (Expr.var u).evalB B (τ.setVar u z) = some z := by
          have h := evalB_var (B := B) (x := u) (σ := τ.setVar u z) (by rw [huz]; omega)
          rwa [huz] at h
        have hsz : (τ.setVar u z).arrs s = arrOf n g' := by rw [arrs_setVar]; exact hg'
        have hlz : z < ((τ.setVar u z).arrs s).length := by rw [hsz, length_arrOf]; exact hzn
        refine ⟨(τ.setVar u z).setArr s z b, 3,
          (Run.store eu (evalB_lit hbB) hlz).mono (by simp), le_rfl,
          by simp [hju, hjv], ?_⟩
        refine ⟨by rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hst), arrs_setVar]; exact htτ,
          ⟨fun k => if k = z then b else g' k,
            by rw [arrs_setVar, arrs_setArr, if_pos rfl, hsz, set_arrOf], fun k hk => ?_⟩,
          by simp [hjeu, hje, Ne.symm hjje], by simp, by omega, by omega⟩
        rw [accUpto_succ hlop]
        simp only []
        by_cases hkz : k = z
        · rw [if_pos hkz, if_pos (Finset.mem_union_right _ (by simp [hkz, hz]))]
        · rw [if_neg hkz, hgk k hk]
          by_cases hka : k ∈ accUpto off tgt (fun w => ({w} : Finset ℕ)) v p
          · rw [if_pos hka, if_pos (Finset.mem_union_left _ hka)]
          · rw [if_neg hka, if_neg (by
              simp only [Finset.mem_union, Finset.mem_singleton]
              rintro (h | h)
              · exact hka h
              · exact hkz h)])
  refine ⟨σ', K, hrun, le_trans hK ?_, hI.2.1, fun a ha => hrun.frame_arr a ?_,
    fun y h1 h2 h3 => hrun.frame_var y ?_⟩
  · rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; omega
  · simp [RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.warrs, ha]
  · simp [RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.wvars, h1, h2, h3]

/-- Two stamping walks in a row, writing the same literal, stamp the
union. -/
theorem Marks.trans {s : String} {n b : ℕ} {S T : Finset ℕ} {g h : ℕ → ℕ} {τ : Env}
    (h₁ : ∀ k < n, h k = if k ∈ S then b else g k) (h₂ : Marks s n b T h τ) :
    Marks s n b (S ∪ T) g τ := by
  classical
  obtain ⟨g', hg', hk⟩ := h₂
  refine ⟨g', hg', fun k hkn => ?_⟩
  rw [hk k hkn, h₁ k hkn]
  by_cases hT : k ∈ T
  · rw [if_pos hT, if_pos (Finset.mem_union_right _ hT)]
  · rw [if_neg hT]
    by_cases hS : k ∈ S
    · rw [if_pos hS, if_pos (Finset.mem_union_left _ hS)]
    · rw [if_neg hS, if_neg (by simp [hS, hT])]

/-- **A nested walk of stamps.** The outer scan of the row of `v` runs,
at every target `z` it names, a walk that writes the same literal into
the cells of `f z`, touches no array but the stamp, and leaves the
outer pointers where it found them. -/
theorem stampNest_run {B : ℕ} {o t x j jend w s : String} {inner : Com}
    {n nv len v b : ℕ} {off tgt g ic : ℕ → ℕ} {fs : ℕ → Finset ℕ} {σ : Env}
    (hxj : x ≠ j) (hjje : j ≠ jend) (hjw : j ≠ w) (hjew : jend ≠ w) (hst : s ≠ t)
    (hB1 : 1 < B) (hv : v < nv) (hvB : v + 1 < B) (hnB : n < B)
    (hoff : σ.arrs o = arrOf (nv + 1) off) (hle : off v ≤ off (v + 1))
    (hlen : off (v + 1) ≤ len) (hhiB : off (v + 1) < B) (hxv : σ.vars x = v)
    (htgt : σ.arrs t = arrOf len tgt) (htn : ∀ p, p < off (v + 1) → tgt p < n)
    (hsa : σ.arrs s = arrOf n g)
    (hinner : ∀ (τ : Env) (z : ℕ) (h : ℕ → ℕ), (∀ a, a ≠ s → τ.arrs a = σ.arrs a) →
      τ.vars w = z → z < n → τ.arrs s = arrOf n h →
      ∃ τ' K, Run B inner τ τ' K ∧ K ≤ ic z ∧ Marks s n b (fs z) h τ' ∧
        (∀ a, a ≠ s → τ'.arrs a = τ.arrs a) ∧ τ'.vars j = τ.vars j ∧
        τ'.vars jend = τ.vars jend) :
    ∃ σ' K, Run B (RamAugment.blockScan o t x j jend w inner) σ σ' K ∧
      K ≤ (∑ p ∈ Finset.Ico (off v) (off (v + 1)), (ic (tgt p) + 11)) + 12 ∧
      Marks s n b (rowAcc off tgt fs v) g σ' ∧
      (∀ a, a ≠ s → σ'.arrs a = σ.arrs a) ∧
      (∀ y, y ∉ (RamAugment.blockScan o t x j jend w inner).wvars →
        σ'.vars y = σ.vars y) := by
  classical
  obtain ⟨σ', K, hrun, hK, hI⟩ :=
    blockScanC_run (B := B) (o := o) (t := t) (x := x) (j := j) (jend := jend) (w := w)
      (c := inner) (nv := nv) (len := len) (v := v) (off := off) (tgt := tgt)
      (costs := fun p => ic (tgt p))
      (I := fun p τ => (∀ a, a ≠ s → τ.arrs a = σ.arrs a) ∧
        Marks s n b (accUpto off tgt fs v p) g τ ∧
        τ.vars jend = off (v + 1) ∧ τ.vars j = p ∧ off v ≤ p ∧ p ≤ off (v + 1))
      hxj hjje hB1 hv hvB hoff hle hlen hhiB hxv
      (fun _ _ h => by rw [h.1 t (Ne.symm hst)]; exact htgt)
      (fun p hp => lt_trans (htn p hp) hnB)
      (fun _ _ h => ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩)
      ⟨fun a _ => by simp, ⟨g, by simpa using hsa, fun k _ => by simp⟩,
        by simp, by simp [hjje], le_rfl, hle⟩
      (by
        rintro p τ ⟨hfr, ⟨gp, hgp, hgk⟩, hje, hjv, hlop, hple⟩ hp
        have hzn : tgt p < n := htn p hp
        have hfr' : ∀ a, a ≠ s → (τ.setVar w (tgt p)).arrs a = σ.arrs a :=
          fun a ha => by rw [arrs_setVar]; exact hfr a ha
        obtain ⟨τ', K', hr, hK', hm, hfa, hj', hje'⟩ :=
          hinner (τ.setVar w (tgt p)) (tgt p) gp hfr' (by simp) hzn
            (by rw [arrs_setVar]; exact hgp)
        refine ⟨τ', K', hr, hK', by rw [hj', vars_setVar, if_neg hjw, hjv], ?_⟩
        refine ⟨fun a ha => by
            rw [arrs_setVar, hfa a ha, arrs_setVar]; exact hfr a ha,
          (Marks.trans hgk hm).congr (accUpto_succ hlop).symm,
          by rw [vars_setVar, if_neg (Ne.symm hjje), hje', vars_setVar, if_neg hjew, hje],
          by simp, by omega, by omega⟩)
  exact ⟨σ', K, hrun, hK, hI.2.1, hI.1, fun y hy => hrun.frame_var y hy⟩

/-! ### The stamped enumerations

The round's one piece of new mathematics. Four passes walk a candidate
list that repeats — a fraternal partner once per witness, a
transitively linked vertex once per intermediate — and each has to hand
its action every *member* of the list exactly once. The device is a
stamp: a candidate is emitted only if its cell is clear, and the cell
is set as it is emitted, so the emitted set is a *support* and what the
counter holds is its cardinality. That is the shape
`RamAugment.card_inN_augOr` is stated against, and it is what makes a
counting pass and the fill pass that follows it agree.

The interface is two predicates. `Emits` is the action's side: handed a
vertex it has not seen, it steps the caller's accounting by one.
`Guarded` is the guard's: handed any vertex, it either emits — which is
the accounting stepped and the stamp set — or does nothing, and which
of the two is a function `fe` of the vertex, valued in singletons and
the empty set, so that the walk's accumulated set is a union of those
and no decidability rides in the statement. -/

/-- What the action of an emitting walk does: handed a vertex `z` in
`"u"` that the walk has not emitted, it steps the accounting, leaves
the walk's two pointers alone, and writes no array but its own two. -/
def Emits (B n Ka : ℕ) (a₁ a₂ : String) (act : Com) (Cap : Finset ℕ)
    (Acc : Finset ℕ → Env → Prop) : Prop :=
  ∀ (S : Finset ℕ) (τ : Env) (z : ℕ), Acc S τ → τ.vars "u" = z → z < n → z ∉ S → z ∈ Cap →
    ∃ τ' K, Run B act τ τ' K ∧ K ≤ Ka ∧ Acc (insert z S) τ' ∧
      (∀ y, y ≠ "c" → τ'.vars y = τ.vars y) ∧
      (∀ a, a ≠ a₁ → a ≠ a₂ → τ'.arrs a = τ.arrs a)

/-- And what a guarded slot does: the emitted set grows by `fe z`, the
singleton when the guard fires and nothing when it does not. -/
def Guarded (B n Kg : ℕ) (grd : Com) (fe : ℕ → Finset ℕ) (Cap : Finset ℕ)
    (J : Finset ℕ → Env → Prop) : Prop :=
  ∀ (S : Finset ℕ) (τ : Env) (z : ℕ), J S τ → τ.vars "u" = z → z < n → fe z ⊆ Cap →
    ∃ τ' K, Run B grd τ τ' K ∧ K ≤ Kg ∧ J (S ∪ fe z) τ' ∧
      (∀ y, y ≠ "c" → τ'.vars y = τ.vars y)

/-- **A row of guarded emissions.** -/
theorem emitRow_run {B : ℕ} {o t x j jend : String} {grd : Com}
    {n nv len v Kg : ℕ} {off tgt : ℕ → ℕ} {fe : ℕ → Finset ℕ}
    {J : Finset ℕ → Env → Prop} {E₀ Cap : Finset ℕ} {σ : Env}
    (hxj : x ≠ j) (hjje : j ≠ jend) (hju : j ≠ "u") (hjeu : jend ≠ "u")
    (hjc : j ≠ "c") (hjec : jend ≠ "c")
    (hB1 : 1 < B) (hv : v < nv) (hvB : v + 1 < B) (hnB : n < B)
    (hoff : σ.arrs o = arrOf (nv + 1) off) (hle : off v ≤ off (v + 1))
    (hlen : off (v + 1) ≤ len) (hhiB : off (v + 1) < B) (hxv : σ.vars x = v)
    (htgt : ∀ S τ, J S τ → τ.arrs t = arrOf len tgt)
    (htn : ∀ p, p < off (v + 1) → tgt p < n)
    (hJv : ∀ S τ (y : String) (z : ℕ), (y = j ∨ y = jend ∨ y = "u") → J S τ →
      J S (τ.setVar y z))
    (hcap : ∀ p, off v ≤ p → p < off (v + 1) → fe (tgt p) ⊆ Cap)
    (hg : Guarded B n Kg grd fe Cap J) (hJ0 : J E₀ σ) :
    ∃ σ' K, Run B (RamAugment.blockScan o t x j jend "u" grd) σ σ' K ∧
      K ≤ (Kg + 11) * (off (v + 1) - off v) + 12 ∧
      J (E₀ ∪ rowAcc off tgt fe v) σ' ∧
      (∀ y, y ≠ j → y ≠ jend → y ≠ "u" → y ≠ "c" → σ'.vars y = σ.vars y) := by
  classical
  obtain ⟨σ', K, hrun, hK, hI⟩ :=
    blockScanC_run (B := B) (o := o) (t := t) (x := x) (j := j) (jend := jend) (w := "u")
      (c := grd) (nv := nv) (len := len) (v := v) (off := off) (tgt := tgt)
      (costs := fun _ => Kg)
      (I := fun p τ => J (E₀ ∪ accUpto off tgt fe v p) τ ∧
        τ.vars jend = off (v + 1) ∧ τ.vars j = p ∧ off v ≤ p ∧ p ≤ off (v + 1) ∧
        (∀ y, y ≠ j → y ≠ jend → y ≠ "u" → y ≠ "c" → τ.vars y = σ.vars y))
      hxj hjje hB1 hv hvB hoff hle hlen hhiB hxv (fun _ _ h => htgt _ _ h.1)
      (fun p hp => lt_trans (htn p hp) hnB)
      (fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.2.1⟩)
      ⟨by
          have h0 := hJv _ _ jend (off (v + 1)) (Or.inr (Or.inl rfl))
            (hJv _ _ j (off v) (Or.inl rfl) hJ0)
          simpa using h0,
        by simp, by simp [hjje], le_rfl, hle,
        fun y h1 h2 _ _ => by rw [vars_setVar, if_neg h2, vars_setVar, if_neg h1]⟩
      (by
        rintro p τ ⟨hJp, hje, hjv, hlop, hple, hfr⟩ hp
        obtain ⟨τ', K', hr, hK', hJ', hfv⟩ :=
          hg _ (τ.setVar "u" (tgt p)) (tgt p)
            (hJv _ _ "u" (tgt p) (Or.inr (Or.inr rfl)) hJp) (by simp) (htn p hp)
            (hcap p hlop hp)
        refine ⟨τ', K', hr, hK', by rw [hfv j hjc, vars_setVar, if_neg hju, hjv], ?_, ?_,
          by simp, by omega, by omega, ?_⟩
        · refine hJv _ _ j (p + 1) (Or.inl rfl) ?_
          rw [accUpto_succ hlop, ← Finset.union_assoc]
          exact hJ'
        · rw [vars_setVar, if_neg (Ne.symm hjje), hfv jend hjec, vars_setVar,
            if_neg hjeu, hje]
        · intro y h1 h2 h3 h4
          rw [vars_setVar, if_neg h1, hfv y h4, vars_setVar, if_neg h3]
          exact hfr y h1 h2 h3 h4)
  refine ⟨σ', K, hrun, le_trans hK ?_, hI.1, hI.2.2.2.2.2⟩
  rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  exact le_of_eq (by ring)

/-- **A row of unguarded emissions**, for the one list of the assembly
that carries no duplicate: the old in-block, whose slots name the
in-neighbours of the vertex and name each of them once. -/
theorem emitAllRow_run {B : ℕ} {o t x j jend a₁ a₂ : String} {act : Com}
    {n nv len v Ka : ℕ} {off tgt : ℕ → ℕ}
    {Acc : Finset ℕ → Env → Prop} {E₀ Cap : Finset ℕ} {σ : Env}
    (hxj : x ≠ j) (hjje : j ≠ jend) (hju : j ≠ "u") (hjeu : jend ≠ "u")
    (hjc : j ≠ "c") (hjec : jend ≠ "c")
    (hB1 : 1 < B) (hv : v < nv) (hvB : v + 1 < B) (hnB : n < B)
    (hoff : σ.arrs o = arrOf (nv + 1) off) (hle : off v ≤ off (v + 1))
    (hlen : off (v + 1) ≤ len) (hhiB : off (v + 1) < B) (hxv : σ.vars x = v)
    (htgt : ∀ S τ, Acc S τ → τ.arrs t = arrOf len tgt)
    (htn : ∀ p, p < off (v + 1) → tgt p < n)
    (hAv : ∀ S τ (y : String) (z : ℕ), (y = j ∨ y = jend ∨ y = "u") → Acc S τ →
      Acc S (τ.setVar y z))
    (hfresh : ∀ p, off v ≤ p → p < off (v + 1) →
      tgt p ∉ E₀ ∪ accUpto off tgt (fun z => {z}) v p)
    (hcap : ∀ p, off v ≤ p → p < off (v + 1) → tgt p ∈ Cap)
    (hAcc : Emits B n Ka a₁ a₂ act Cap Acc) (hA0 : Acc E₀ σ) :
    ∃ σ' K, Run B (RamAugment.blockScan o t x j jend "u" act) σ σ' K ∧
      K ≤ (Ka + 11) * (off (v + 1) - off v) + 12 ∧
      Acc (E₀ ∪ rowTgt off tgt v) σ' ∧
      (∀ y, y ≠ j → y ≠ jend → y ≠ "u" → y ≠ "c" → σ'.vars y = σ.vars y) ∧
      (∀ a, a ≠ a₁ → a ≠ a₂ → σ'.arrs a = σ.arrs a) := by
  classical
  obtain ⟨σ', K, hrun, hK, hI⟩ :=
    blockScanC_run (B := B) (o := o) (t := t) (x := x) (j := j) (jend := jend) (w := "u")
      (c := act) (nv := nv) (len := len) (v := v) (off := off) (tgt := tgt)
      (costs := fun _ => Ka)
      (I := fun p τ => Acc (E₀ ∪ accUpto off tgt (fun z => {z}) v p) τ ∧
        τ.vars jend = off (v + 1) ∧ τ.vars j = p ∧ off v ≤ p ∧ p ≤ off (v + 1) ∧
        (∀ y, y ≠ j → y ≠ jend → y ≠ "u" → y ≠ "c" → τ.vars y = σ.vars y) ∧
        (∀ a, a ≠ a₁ → a ≠ a₂ → τ.arrs a = σ.arrs a))
      hxj hjje hB1 hv hvB hoff hle hlen hhiB hxv (fun _ _ h => htgt _ _ h.1)
      (fun p hp => lt_trans (htn p hp) hnB)
      (fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.2.1⟩)
      ⟨by
          have h0 := hAv _ _ jend (off (v + 1)) (Or.inr (Or.inl rfl))
            (hAv _ _ j (off v) (Or.inl rfl) hA0)
          simpa using h0,
        by simp, by simp [hjje], le_rfl, hle,
        (fun y h1 h2 _ _ => by rw [vars_setVar, if_neg h2, vars_setVar, if_neg h1]),
        fun a _ _ => by simp⟩
      (by
        rintro p τ ⟨hAp, hje, hjv, hlop, hple, hfr, hfa⟩ hp
        obtain ⟨τ', K', hr, hK', hA', hfv, hga⟩ :=
          hAcc _ (τ.setVar "u" (tgt p)) (tgt p)
            (hAv _ _ "u" (tgt p) (Or.inr (Or.inr rfl)) hAp) (by simp) (htn p hp)
            (hfresh p hlop hp) (hcap p hlop hp)
        refine ⟨τ', K', hr, hK', by rw [hfv j hjc, vars_setVar, if_neg hju, hjv], ?_, ?_,
          by simp, by omega, by omega, ?_, ?_⟩
        · refine hAv _ _ j (p + 1) (Or.inl rfl) ?_
          rw [accUpto_succ hlop, ← Finset.union_assoc, Finset.union_singleton]
          exact hA'
        · rw [vars_setVar, if_neg (Ne.symm hjje), hfv jend hjec, vars_setVar,
            if_neg hjeu, hje]
        · intro y h1 h2 h3 h4
          rw [vars_setVar, if_neg h1, hfv y h4, vars_setVar, if_neg h3]
          exact hfr y h1 h2 h3 h4
        · intro a h1 h2
          rw [arrs_setVar, hga a h1 h2, arrs_setVar]
          exact hfa a h1 h2)
  refine ⟨σ', K, hrun, le_trans hK ?_, hI.1, hI.2.2.2.2.2.1, hI.2.2.2.2.2.2⟩
  rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  exact le_of_eq (by ring)

/-- **The emitting branch of a guard**: the vertex is stamped, and then
the action runs on it. -/
theorem emitBranch_run {B n Ka : ℕ} {a₁ a₂ sd : String} {act : Com}
    {Acc : Finset ℕ → Env → Prop} {S Base Cap : Finset ℕ} {τ : Env} {z : ℕ}
    (ha₁ : a₁ ≠ sd) (ha₂ : a₂ ≠ sd) (hB1 : 1 < B) (hnB : n < B)
    (hAccSt : ∀ S τ p x, Acc S τ → Acc S (τ.setArr sd p x))
    (hAcc : Emits B n Ka a₁ a₂ act Cap Acc)
    (hm : Marks sd n 1 (Base ∪ S) (fun _ => 0) τ) (hA : Acc S τ)
    (hu : τ.vars "u" = z) (hzn : z < n) (hz : z ∉ Base ∪ S) (hzc : z ∈ Cap) :
    ∃ τ' K, Run B (.seq (.store sd (.var "u") (.lit 1)) act) τ τ' K ∧ K ≤ Ka + 3 ∧
      Marks sd n 1 (Base ∪ insert z S) (fun _ => 0) τ' ∧ Acc (insert z S) τ' ∧
      (∀ y, y ≠ "c" → τ'.vars y = τ.vars y) ∧
      (∀ a, a ≠ a₁ → a ≠ a₂ → a ≠ sd → τ'.arrs a = τ.arrs a) := by
  classical
  obtain ⟨g, hg, hgk⟩ := hm
  have eu : (Expr.var "u").evalB B τ = some z := by
    have h := evalB_var (B := B) (x := "u") (σ := τ) (by rw [hu]; omega)
    rwa [hu] at h
  have hlz : z < (τ.arrs sd).length := by rw [hg, length_arrOf]; exact hzn
  have hrs : Run B (.store sd (.var "u") (.lit 1)) τ (τ.setArr sd z 1) 3 :=
    (Run.store eu (evalB_lit hB1) hlz).mono (by simp)
  have hm₁ : Marks sd n 1 (Base ∪ insert z S) (fun _ => 0) (τ.setArr sd z 1) := by
    refine ⟨fun k => if k = z then 1 else g k, by rw [arrs_setArr, if_pos rfl, hg, set_arrOf],
      fun k hk => ?_⟩
    simp only []
    by_cases hkz : k = z
    · rw [if_pos hkz, if_pos (by simp [hkz])]
    · rw [if_neg hkz, hgk k hk]
      by_cases hkb : k ∈ Base ∪ S
      · rw [if_pos hkb, if_pos (by
          rcases Finset.mem_union.1 hkb with h | h
          · exact Finset.mem_union_left _ h
          · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem h))]
      · rw [if_neg hkb, if_neg (by
          intro hc
          rcases Finset.mem_union.1 hc with h | h
          · exact hkb (Finset.mem_union_left _ h)
          · rcases Finset.mem_insert.1 h with h | h
            · exact hkz h
            · exact hkb (Finset.mem_union_right _ h))]
  obtain ⟨g₁, hg₁, hgk₁⟩ := hm₁
  obtain ⟨τ', K, hr, hK, hA', hj', hfa⟩ :=
    hAcc S (τ.setArr sd z 1) z (hAccSt S τ z 1 hA) (by rw [vars_setArr]; exact hu) hzn
      (fun hc => hz (Finset.mem_union_right _ hc)) hzc
  exact ⟨τ', 3 + K, hrs.seq hr, by omega,
    ⟨g₁, by rw [hfa sd (Ne.symm ha₁) (Ne.symm ha₂)]; exact hg₁, hgk₁⟩, hA',
    fun y hy => by rw [hj' y hy, vars_setArr],
    fun a h1 h2 h3 => by rw [hfa a h1 h2, arrs_setArr, if_neg h3]⟩

/-- **The fraternity guard.** The vertex is emitted unless its stamp is
set — which it is for the current vertex, stamped before the walk
starts, and for every partner already emitted. So the loop of the
fraternity graph is kept out with no test of its own, which is the
erasure in `RamAugment.fratNbrs_eq`. -/
theorem guardFrat_of_emits {B n Ka i : ℕ} {a₁ a₂ : String} {act : Com}
    {Acc : Finset ℕ → Env → Prop} {Cap : Finset ℕ}
    (ha₁ : a₁ ≠ "stf") (ha₂ : a₂ ≠ "stf") (hB1 : 1 < B) (hnB : n < B)
    (hAccSt : ∀ S τ p x, Acc S τ → Acc S (τ.setArr "stf" p x))
    (hAcc : Emits B n Ka a₁ a₂ act Cap Acc) :
    Guarded B n (Ka + 8)
      (.ite (.eq (.get "stf" (.var "u")) (.lit 0))
        (.seq (.store "stf" (.var "u") (.lit 1)) act) .skip)
      (fun z => if z = i then ∅ else {z}) Cap
      (fun S τ => Marks "stf" n 1 ({i} ∪ S) (fun _ => 0) τ ∧ Acc S τ) := by
  classical
  rintro S τ z ⟨hm, hA⟩ hu hzn hfe
  obtain ⟨g, hg, hgk⟩ := hm
  have eu : (Expr.var "u").evalB B τ = some z := by
    have h := evalB_var (B := B) (x := "u") (σ := τ) (by rw [hu]; omega)
    rwa [hu] at h
  have hgz : g z = if z ∈ ({i} : Finset ℕ) ∪ S then 1 else 0 := hgk z hzn
  have egz : (Expr.get "stf" (.var "u")).evalB B τ = some (g z) :=
    evalB_get eu (by rw [hg, getElem?_arrOf g hzn]) (by rw [hgz]; split <;> omega)
  have econd : (Cond.eq (.get "stf" (.var "u")) (.lit 0)).evalB B τ = some (g z == 0) :=
    evalB_condEq egz (evalB_lit (by omega))
  by_cases hin : z ∈ ({i} : Finset ℕ) ∪ S
  · have hgz1 : g z = 1 := by rw [hgz, if_pos hin]
    have hset : S ∪ (if z = i then (∅ : Finset ℕ) else {z}) = S := by
      by_cases hzi : z = i
      · rw [if_pos hzi, Finset.union_empty]
      · have hzS : z ∈ S := by
          rcases Finset.mem_union.1 hin with h | h
          · exact absurd (Finset.mem_singleton.1 h) hzi
          · exact h
        rw [if_neg hzi, Finset.union_singleton, Finset.insert_eq_self.2 hzS]
    refine ⟨τ, _, Run.ite_false (by rw [econd, hgz1]; rfl) Run.skip, ?_, ?_, fun y _ => rfl⟩
    · simp only [size_condEq, size_get, size_var, size_lit]; omega
    · simp only [hset]
      exact ⟨⟨g, hg, hgk⟩, hA⟩
  · have hgz0 : g z = 0 := by rw [hgz, if_neg hin]
    have hzi : z ≠ i := fun h => hin (Finset.mem_union_left _ (Finset.mem_singleton.2 h))
    obtain ⟨τ', K, hr, hK, hm', hA', hfv, -⟩ :=
      emitBranch_run (sd := "stf") (Base := ({i} : Finset ℕ)) ha₁ ha₂ hB1 hnB hAccSt hAcc
        ⟨g, hg, hgk⟩ hA hu hzn hin
        (hfe (by simp only [if_neg hzi]; exact Finset.mem_singleton_self z))
    have hset : S ∪ (if z = i then (∅ : Finset ℕ) else {z}) = insert z S := by
      rw [if_neg hzi, Finset.union_singleton]
    refine ⟨τ', _, Run.ite_true (by rw [econd, hgz0]; rfl) hr, ?_, ?_, hfv⟩
    · simp only [size_condEq, size_get, size_var, size_lit]; omega
    · simp only [hset]
      exact ⟨hm', hA'⟩

/-- Reading a stamp cell: the test is the membership. -/
theorem stampCond {B n : ℕ} {s : String} {S : Finset ℕ} {τ : Env} {z : ℕ}
    (hm : Marks s n 1 S (fun _ => 0) τ) (hu : τ.vars "u" = z) (hzn : z < n) (hB1 : 1 < B)
    (hnB : n < B) :
    (Cond.eq (.get s (.var "u")) (.lit 0)).evalB B τ = some (decide (z ∉ S)) := by
  classical
  obtain ⟨g, hg, hgk⟩ := hm
  have eu : (Expr.var "u").evalB B τ = some z := by
    have h := evalB_var (B := B) (x := "u") (σ := τ) (by rw [hu]; omega)
    rwa [hu] at h
  have hgz : g z = if z ∈ S then 1 else 0 := hgk z hzn
  have egz : (Expr.get s (.var "u")).evalB B τ = some (g z) :=
    evalB_get eu (by rw [hg, getElem?_arrOf g hzn]) (by rw [hgz]; split <;> omega)
  rw [evalB_condEq egz (evalB_lit (B := B) (n := 0) (by omega))]
  congr 1
  by_cases h : z ∈ S
  · rw [hgz, if_pos h]; simp [h]
  · rw [hgz, if_neg h]; simp [h]

/-- **The engine block's guard.** A candidate out of the elimination's
own in-block is kept unless `D` already carries the pair — which is the
first clause of `RamAugment.NewArc` — or it has been emitted. -/
theorem guardAsmIn_of_emits {B n Ka : ℕ} {a₁ a₂ : String} {act : Com}
    {Acc : Finset ℕ → Env → Prop} {A Cap : Finset ℕ}
    (ha₁ : a₁ ≠ "ste") (ha₂ : a₂ ≠ "ste") (hb₁ : a₁ ≠ "sta") (hb₂ : a₂ ≠ "sta")
    (hB1 : 1 < B) (hnB : n < B)
    (hAccSt : ∀ S τ p x, Acc S τ → Acc S (τ.setArr "ste" p x))
    (hAcc : Emits B n Ka a₁ a₂ act Cap Acc) :
    Guarded B n (Ka + 13)
      (.ite (.eq (.get "sta" (.var "u")) (.lit 0))
        (.ite (.eq (.get "ste" (.var "u")) (.lit 0))
          (.seq (.store "ste" (.var "u") (.lit 1)) act) .skip)
        .skip)
      (fun z => if z ∈ A then ∅ else {z}) Cap
      (fun S τ => Marks "ste" n 1 S (fun _ => 0) τ ∧
        Marks "sta" n 1 A (fun _ => 0) τ ∧ Acc S τ) := by
  classical
  rintro S τ z ⟨hme, hma, hA⟩ hu hzn hfe
  have ea := stampCond hma hu hzn hB1 hnB
  have ee := stampCond hme hu hzn hB1 hnB
  by_cases hzA : z ∈ A
  · refine ⟨τ, _, Run.ite_false (by rw [ea]; simp [hzA]) Run.skip, ?_, ?_, fun y _ => rfl⟩
    · simp only [size_condEq, size_get, size_var, size_lit]; omega
    · simp only [if_pos hzA, Finset.union_empty]
      exact ⟨hme, hma, hA⟩
  · by_cases hzS : z ∈ S
    · refine ⟨τ, _, Run.ite_true (by rw [ea]; simp [hzA])
        (Run.ite_false (by rw [ee]; simp [hzS]) Run.skip), ?_, ?_, fun y _ => rfl⟩
      · simp only [size_condEq, size_get, size_var, size_lit]; omega
      · simp only [if_neg hzA, Finset.union_singleton, Finset.insert_eq_self.2 hzS]
        exact ⟨hme, hma, hA⟩
    · obtain ⟨τ', K, hr, hK, hm', hA', hfv, hfr⟩ :=
        emitBranch_run (sd := "ste") (Base := (∅ : Finset ℕ)) ha₁ ha₂ hB1 hnB hAccSt hAcc
          (by rwa [Finset.empty_union]) hA hu hzn (by rwa [Finset.empty_union])
          (hfe (by simp only [if_neg hzA]; exact Finset.mem_singleton_self z))
      refine ⟨τ', _, Run.ite_true (by rw [ea]; simp [hzA])
        (Run.ite_true (by rw [ee]; simp [hzS]) hr), ?_, ?_, hfv⟩
      · simp only [size_condEq, size_get, size_var, size_lit]; omega
      · simp only [if_neg hzA, Finset.union_singleton]
        obtain ⟨ga, hga, hgak⟩ := hma
        exact ⟨by rwa [Finset.empty_union] at hm', ⟨ga, by
          rw [hfr "sta" (Ne.symm hb₁) (Ne.symm hb₂) (by decide)]; exact hga, hgak⟩, hA'⟩

/-- **The transitive candidates' guard.** The pair must not be one `D`
already carries, the candidate must not have been emitted, and if the
current vertex is demanded an arc *back* — which is what the stamp
`std` holds — the ranking decides. That is
`RamAugment.NewArc` read off three array cells and one comparison. -/
theorem guardAsmTrans_of_emits {B n Ka i : ℕ} {a₁ a₂ : String} {act : Com}
    {Acc : Finset ℕ → Env → Prop} {A Dm Cap : Finset ℕ} {R : ℕ → ℕ}
    (ha₁ : a₁ ≠ "ste") (ha₂ : a₂ ≠ "ste") (hb₁ : a₁ ≠ "sta") (hb₂ : a₂ ≠ "sta")
    (hc₁ : a₁ ≠ "std") (hc₂ : a₂ ≠ "std") (hd₁ : a₁ ≠ "rnk") (hd₂ : a₂ ≠ "rnk")
    (hB1 : 1 < B) (hnB : n < B) (hin : i < n) (hR : ∀ v, v < n → R v < n)
    (hAccSt : ∀ S τ p x, Acc S τ → Acc S (τ.setArr "ste" p x))
    (hAccI : ∀ S τ, Acc S τ → τ.vars "i" = i)
    (hAcc : Emits B n Ka a₁ a₂ act Cap Acc) :
    Guarded B n (Ka + 24)
      (.ite (.eq (.get "sta" (.var "u")) (.lit 0))
        (.ite (.eq (.get "ste" (.var "u")) (.lit 0))
          (.ite (.eq (.get "std" (.var "u")) (.lit 0))
            (.seq (.store "ste" (.var "u") (.lit 1)) act)
            (.ite (.lt (.get "rnk" (.var "u")) (.get "rnk" (.var "i")))
              (.seq (.store "ste" (.var "u") (.lit 1)) act) .skip))
          .skip)
        .skip)
      (fun z => if z ∈ A then ∅ else if z ∈ Dm ∧ ¬ R z < R i then ∅ else {z}) Cap
      (fun S τ => Marks "ste" n 1 S (fun _ => 0) τ ∧ Marks "sta" n 1 A (fun _ => 0) τ ∧
        Marks "std" n 1 Dm (fun _ => 0) τ ∧ τ.arrs "rnk" = arrOf n R ∧ Acc S τ) := by
  classical
  rintro S τ z ⟨hme, hma, hmd, hrnk, hA⟩ hu hzn hfe
  have ea := stampCond hma hu hzn hB1 hnB
  have ee := stampCond hme hu hzn hB1 hnB
  have ed := stampCond hmd hu hzn hB1 hnB
  have eu : (Expr.var "u").evalB B τ = some z := by
    have h := evalB_var (B := B) (x := "u") (σ := τ) (by rw [hu]; omega)
    rwa [hu] at h
  have hiv : τ.vars "i" = i := hAccI S τ hA
  have ei : (Expr.var "i").evalB B τ = some i := by
    have h := evalB_var (B := B) (x := "i") (σ := τ) (by rw [hiv]; omega)
    rwa [hiv] at h
  have elt : (Cond.lt (.get "rnk" (.var "u")) (.get "rnk" (.var "i"))).evalB B τ
      = some (decide (R z < R i)) :=
    evalB_condLt (evalB_get eu (by rw [hrnk, getElem?_arrOf R hzn]) (by
        have := hR z hzn; omega))
      (evalB_get ei (by rw [hrnk, getElem?_arrOf R hin]) (by have := hR i hin; omega))
  have hkeep : ∀ (τ' : Env), (∀ a, a ≠ a₁ → a ≠ a₂ → a ≠ "ste" → τ'.arrs a = τ.arrs a) →
      Marks "sta" n 1 A (fun _ => 0) τ' ∧ Marks "std" n 1 Dm (fun _ => 0) τ' ∧
        τ'.arrs "rnk" = arrOf n R := by
    intro τ' hfr
    obtain ⟨ga, hga, hgak⟩ := hma
    obtain ⟨gd, hgd, hgdk⟩ := hmd
    exact ⟨⟨ga, by rw [hfr "sta" (Ne.symm hb₁) (Ne.symm hb₂) (by decide)]; exact hga, hgak⟩,
      ⟨gd, by rw [hfr "std" (Ne.symm hc₁) (Ne.symm hc₂) (by decide)]; exact hgd, hgdk⟩,
      by rw [hfr "rnk" (Ne.symm hd₁) (Ne.symm hd₂) (by decide)]; exact hrnk⟩
  by_cases hzA : z ∈ A
  · refine ⟨τ, _, Run.ite_false (by rw [ea]; simp [hzA]) Run.skip, ?_, ?_, fun y _ => rfl⟩
    · simp only [size_condEq, size_get, size_var, size_lit]; omega
    · simp only [if_pos hzA, Finset.union_empty]
      exact ⟨hme, hma, hmd, hrnk, hA⟩
  · by_cases hzS : z ∈ S
    · refine ⟨τ, _, Run.ite_true (by rw [ea]; simp [hzA])
        (Run.ite_false (by rw [ee]; simp [hzS]) Run.skip), ?_, ?_, fun y _ => rfl⟩
      · simp only [size_condEq, size_get, size_var, size_lit]; omega
      · have hset : S ∪ (if z ∈ Dm ∧ ¬ R z < R i then (∅ : Finset ℕ) else {z}) = S := by
          split
          · exact Finset.union_empty _
          · rw [Finset.union_singleton, Finset.insert_eq_self.2 hzS]
        simp only [if_neg hzA, hset]
        exact ⟨hme, hma, hmd, hrnk, hA⟩
    · have hemitB : z ∈ Cap →
          ∃ τ' K, Run B (.seq (.store "ste" (.var "u") (.lit 1)) act) τ τ' K ∧ K ≤ Ka + 3 ∧
            Marks "ste" n 1 (insert z S) (fun _ => 0) τ' ∧ Acc (insert z S) τ' ∧
            (∀ y, y ≠ "c" → τ'.vars y = τ.vars y) ∧
            Marks "sta" n 1 A (fun _ => 0) τ' ∧ Marks "std" n 1 Dm (fun _ => 0) τ' ∧
            τ'.arrs "rnk" = arrOf n R := by
        intro hzc
        obtain ⟨τ', K, hr, hK, hm', hA', hfv, hfr⟩ :=
          emitBranch_run (sd := "ste") (Base := (∅ : Finset ℕ)) ha₁ ha₂ hB1 hnB hAccSt hAcc
            (by rwa [Finset.empty_union]) hA hu hzn (by rwa [Finset.empty_union]) hzc
        obtain ⟨hma', hmd', hrnk'⟩ := hkeep τ' hfr
        exact ⟨τ', K, hr, hK, by rwa [Finset.empty_union] at hm', hA', hfv,
          hma', hmd', hrnk'⟩
      by_cases hzD : z ∈ Dm
      · by_cases hlt : R z < R i
        · have hnc : ¬ (z ∈ Dm ∧ ¬ R z < R i) := by simp [hlt]
          obtain ⟨τ', K, hr, hK, hme', hA', hfv, hma', hmd', hrnk'⟩ :=
            hemitB (hfe (by
              simp only [if_neg hzA, if_neg hnc]; exact Finset.mem_singleton_self z))
          refine ⟨τ', _, Run.ite_true (by rw [ea]; simp [hzA])
            (Run.ite_true (by rw [ee]; simp [hzS])
              (Run.ite_false (by rw [ed]; simp [hzD])
                (Run.ite_true (by rw [elt]; simp [hlt]) hr))), ?_, ?_, hfv⟩
          · simp only [size_condEq, size_condLt, size_get, size_var, size_lit]; omega
          · simp only [if_neg hzA, if_neg hnc, Finset.union_singleton]
            exact ⟨hme', hma', hmd', hrnk', hA'⟩
        · refine ⟨τ, _, Run.ite_true (by rw [ea]; simp [hzA])
            (Run.ite_true (by rw [ee]; simp [hzS])
              (Run.ite_false (by rw [ed]; simp [hzD])
                (Run.ite_false (by rw [elt]; simp [hlt]) Run.skip))), ?_, ?_, fun y _ => rfl⟩
          · simp only [size_condEq, size_condLt, size_get, size_var, size_lit]; omega
          · simp only [if_neg hzA, if_pos (⟨hzD, hlt⟩ : z ∈ Dm ∧ ¬ R z < R i),
              Finset.union_empty]
            exact ⟨hme, hma, hmd, hrnk, hA⟩
      · have hnc : ¬ (z ∈ Dm ∧ ¬ R z < R i) := by simp [hzD]
        obtain ⟨τ', K, hr, hK, hme', hA', hfv, hma', hmd', hrnk'⟩ :=
          hemitB (hfe (by
            simp only [if_neg hzA, if_neg hnc]; exact Finset.mem_singleton_self z))
        refine ⟨τ', _, Run.ite_true (by rw [ea]; simp [hzA])
          (Run.ite_true (by rw [ee]; simp [hzS])
            (Run.ite_true (by rw [ed]; simp [hzD]) hr)), ?_, ?_, hfv⟩
        · simp only [size_condEq, size_get, size_var, size_lit]; omega
        · simp only [if_neg hzA, if_neg hnc, Finset.union_singleton]
          exact ⟨hme', hma', hmd', hrnk', hA'⟩

theorem subset_rowAcc {off tgt : ℕ → ℕ} {fs : ℕ → Finset ℕ} {v p : ℕ}
    (h₁ : off v ≤ p) (h₂ : p < off (v + 1)) : fs (tgt p) ⊆ rowAcc off tgt fs v :=
  fun _ hy => mem_rowAcc.2 ⟨p, h₁, h₂, hy⟩

/-- **A nested walk of guarded emissions**: for every target of the row
of the current vertex, the row of *that* vertex in a second block
structure is walked and its members emitted. This is
`RamAugment.fratScan` and the transitive half of `RamAugment.asmEmit`
alike; the inner rows are in-blocks, so one bound `dd` charges them
all. -/
theorem emitNest_run {B : ℕ} {o t o2 t2 : String} {grd : Com}
    {n nv len nv2 len2 v Kg dd : ℕ} {off tgt off2 tgt2 : ℕ → ℕ}
    {fe : ℕ → Finset ℕ} {J : Finset ℕ → Env → Prop} {E₀ Cap : Finset ℕ} {σ : Env}
    (hB1 : 1 < B) (hnB : n < B) (hv : v < nv) (hvB : v + 1 < B)
    (hoff : σ.arrs o = arrOf (nv + 1) off) (hle : off v ≤ off (v + 1))
    (hlen : off (v + 1) ≤ len) (hhiB : off (v + 1) < B) (hxv : σ.vars "i" = v)
    (htgt : ∀ S τ, J S τ → τ.arrs t = arrOf len tgt)
    (htn : ∀ p, p < off (v + 1) → tgt p < n) (hnnv2 : n ≤ nv2)
    (ho2 : ∀ S τ, J S τ → τ.arrs o2 = arrOf (nv2 + 1) off2)
    (ht2 : ∀ S τ, J S τ → τ.arrs t2 = arrOf len2 tgt2)
    (hmono2 : ∀ z, z < nv2 → off2 z ≤ off2 (z + 1))
    (hle2 : ∀ z, z < nv2 → off2 (z + 1) ≤ len2)
    (hB2 : ∀ z, z < nv2 → off2 (z + 1) < B)
    (htn2 : ∀ q, q < len2 → tgt2 q < n)
    (hd2 : ∀ z, z < nv2 → off2 (z + 1) - off2 z ≤ dd)
    (hJv : ∀ S τ (y : String) (z : ℕ),
      (y = "j" ∨ y = "jend" ∨ y = "w" ∨ y = "q" ∨ y = "qe" ∨ y = "u") → J S τ →
      J S (τ.setVar y z))
    (hcap : ∀ p, off v ≤ p → p < off (v + 1) → rowAcc off2 tgt2 fe (tgt p) ⊆ Cap)
    (hg : Guarded B n Kg grd fe Cap J) (hJ0 : J E₀ σ) :
    ∃ σ' K, Run B (RamAugment.blockScan o t "i" "j" "jend" "w"
        (RamAugment.blockScan o2 t2 "w" "q" "qe" "u" grd)) σ σ' K ∧
      K ≤ ((Kg + 11) * dd + 23) * (off (v + 1) - off v) + 12 ∧
      J (E₀ ∪ rowAcc off tgt (fun z => rowAcc off2 tgt2 fe z) v) σ' ∧
      (∀ y, y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" → y ≠ "u" → y ≠ "c" →
        σ'.vars y = σ.vars y) := by
  classical
  obtain ⟨σ', K, hrun, hK, hI⟩ :=
    blockScanC_run (B := B) (o := o) (t := t) (x := "i") (j := "j") (jend := "jend")
      (w := "w") (c := RamAugment.blockScan o2 t2 "w" "q" "qe" "u" grd) (nv := nv)
      (len := len) (v := v) (off := off) (tgt := tgt)
      (costs := fun _ => (Kg + 11) * dd + 12)
      (I := fun p τ => J (E₀ ∪ accUpto off tgt (fun z => rowAcc off2 tgt2 fe z) v p) τ ∧
        τ.vars "jend" = off (v + 1) ∧ τ.vars "j" = p ∧ off v ≤ p ∧ p ≤ off (v + 1) ∧
        (∀ y, y ≠ "j" → y ≠ "jend" → y ≠ "w" → y ≠ "q" → y ≠ "qe" → y ≠ "u" → y ≠ "c" →
          τ.vars y = σ.vars y))
      (by decide) (by decide) hB1 hv hvB hoff hle hlen hhiB hxv (fun _ _ h => htgt _ _ h.1)
      (fun p hp => lt_trans (htn p hp) hnB)
      (fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.2.1⟩)
      ⟨by
          have h0 := hJv _ _ "jend" (off (v + 1)) (Or.inr (Or.inl rfl))
            (hJv _ _ "j" (off v) (Or.inl rfl) hJ0)
          simpa using h0,
        by simp, by simp, le_rfl, hle,
        fun y h1 h2 _ _ _ _ _ => by rw [vars_setVar, if_neg h2, vars_setVar, if_neg h1]⟩
      (by
        rintro p τ ⟨hJp, hje, hjv, hlop, hple, hfr⟩ hp
        have hzn : tgt p < n := htn p hp
        have hznv : tgt p < nv2 := by omega
        have hJw : J (E₀ ∪ accUpto off tgt (fun z => rowAcc off2 tgt2 fe z) v p)
            (τ.setVar "w" (tgt p)) :=
          hJv _ _ "w" (tgt p) (Or.inr (Or.inr (Or.inl rfl))) hJp
        obtain ⟨σ'', K', hr, hK', hJ', hfv⟩ :=
          emitRow_run (B := B) (o := o2) (t := t2) (x := "w") (j := "q") (jend := "qe")
            (grd := grd) (n := n) (nv := nv2) (len := len2) (v := tgt p) (Kg := Kg)
            (off := off2) (tgt := tgt2) (fe := fe) (J := J)
            (E₀ := E₀ ∪ accUpto off tgt (fun z => rowAcc off2 tgt2 fe z) v p) (Cap := Cap)
            (σ := τ.setVar "w" (tgt p))
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            hB1 hznv (by omega) hnB (ho2 _ _ hJw) (hmono2 _ hznv) (hle2 _ hznv)
            (hB2 _ hznv) (by simp) ht2
            (fun q hq => htn2 q (lt_of_lt_of_le hq (hle2 _ hznv)))
            (fun S τ' y z hy hJ' => hJv S τ' y z (by
              rcases hy with rfl | rfl | rfl
              · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hJ')
            (fun q hq₁ hq₂ => subset_rowAcc hq₁ hq₂ |>.trans (hcap p hlop hp)) hg hJw
        refine ⟨σ'', K', hr, ?_, ?_, ?_, ?_, by simp, by omega, by omega, ?_⟩
        · exact le_trans hK' (by
            have := hd2 _ hznv
            exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) 12)
        · rw [hfv "j" (by decide) (by decide) (by decide) (by decide), vars_setVar,
            if_neg (by decide), hjv]
        · refine hJv _ _ "j" (p + 1) (Or.inl rfl) ?_
          rw [accUpto_succ hlop, ← Finset.union_assoc]
          exact hJ'
        · rw [vars_setVar, if_neg (by decide),
            hfv "jend" (by decide) (by decide) (by decide) (by decide), vars_setVar,
            if_neg (by decide), hje]
        · intro y h1 h2 h3 h4 h5 h6 h7
          rw [vars_setVar, if_neg h1, hfv y h4 h5 h6 h7, vars_setVar, if_neg h3]
          exact hfr y h1 h2 h3 h4 h5 h6 h7)
  refine ⟨σ', K, hrun, le_trans hK ?_, hI.1, hI.2.2.2.2.2⟩
  rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  exact le_of_eq (by ring)

/-! ### The two accountings

A counting pass keeps a counter, a fill pass keeps a fill pointer and
the cells below it. Both are `Emits`: handed a vertex they have not
seen, they step by one. -/

/-- What a counting pass carries: the counter holds the number of
vertices emitted. -/
def CntAcc (n i : ℕ) (S : Finset ℕ) (τ : Env) : Prop :=
  τ.vars "c" = S.card ∧ τ.vars "i" = i ∧ S ⊆ Finset.range n

theorem CntAcc.setArr {n i : ℕ} {S : Finset ℕ} {τ : Env} (h : CntAcc n i S τ)
    (a : String) (p x : ℕ) : CntAcc n i S (τ.setArr a p x) :=
  ⟨by rw [vars_setArr]; exact h.1, by rw [vars_setArr]; exact h.2.1, h.2.2⟩

theorem CntAcc.setVar {n i : ℕ} {S : Finset ℕ} {τ : Env} (h : CntAcc n i S τ) {y : String}
    (hc : y ≠ "c") (hi : y ≠ "i") (x : ℕ) : CntAcc n i S (τ.setVar y x) :=
  ⟨by rw [vars_setVar, if_neg (Ne.symm hc)]; exact h.1,
    by rw [vars_setVar, if_neg (Ne.symm hi)]; exact h.2.1, h.2.2⟩

/-- **The counting action.** -/
theorem cntAcc_emits {B n i : ℕ} {Cap : Finset ℕ} (hnB : n + 1 < B) :
    Emits B n 4 "@" "@" (.assign "c" (.add (.var "c") (.lit 1))) Cap
      (CntAcc n i) := by
  rintro S τ z ⟨hc, hi, hsub⟩ hu hzn hzS hzc
  have hcard : S.card ≤ n := by
    have h := Finset.card_le_card hsub
    rwa [Finset.card_range] at h
  have e : (Expr.add (.var "c") (.lit 1)).evalB B τ = some (S.card + 1) := by
    have h := evalB_bin (B := B) (op := .add) (σ := τ) (m := τ.vars "c") (n := 1)
      (evalB_var (by rw [hc]; omega)) (evalB_lit (by omega))
      (by rw [hc]; simpa [Bop.apply] using (by omega : S.card + 1 < B))
    rw [hc] at h
    simpa [Bop.apply] using h
  refine ⟨τ.setVar "c" (S.card + 1), 4, (Run.assign e).mono (by simp), le_rfl,
    ⟨by rw [vars_setVar, if_pos rfl, Finset.card_insert_of_notMem hzS], by simp [hi],
      fun k hk => ?_⟩,
    fun y hy => by rw [vars_setVar, if_neg hy], fun a _ _ => by simp⟩
  rcases Finset.mem_insert.1 hk with rfl | hk
  · exact Finset.mem_range.2 hzn
  · exact hsub hk

/-- What a fill pass carries: the fill pointer of the current vertex is
its block's start plus what has been emitted, and the cells between
name exactly the emitted set — once each, since the pointer advances
with them. -/
def FillAcc (ta fa : String) (n len i base : ℕ) (T : ℕ → ℕ) (Cap : Finset ℕ)
    (S : Finset ℕ) (τ : Env) : Prop :=
  τ.vars "i" = i ∧ S ⊆ Cap ∧
  (∃ f, τ.arrs fa = arrOf n f ∧ f i = base + S.card) ∧
  (∃ g, τ.arrs ta = arrOf len g ∧
    (∀ q, base ≤ q → q < base + S.card → g q ∈ S) ∧
    (∀ z, z ∈ S → ∃ q, base ≤ q ∧ q < base + S.card ∧ g q = z) ∧
    (∀ q, (q < base ∨ base + S.card ≤ q) → g q = T q))

theorem FillAcc.setArr {ta fa : String} {n len i base : ℕ} {T : ℕ → ℕ} {Cap S : Finset ℕ}
    {τ : Env} (h : FillAcc ta fa n len i base T Cap S τ) {a : String} (hta : a ≠ ta)
    (hfa : a ≠ fa) (p x : ℕ) : FillAcc ta fa n len i base T Cap S (τ.setArr a p x) := by
  obtain ⟨hi, hsub, ⟨f, hf, hfi⟩, ⟨g, hg, h₁, h₂, h₃⟩⟩ := h
  exact ⟨by rw [vars_setArr]; exact hi, hsub,
    ⟨f, by rw [arrs_setArr, if_neg (Ne.symm hfa)]; exact hf, hfi⟩,
    ⟨g, by rw [arrs_setArr, if_neg (Ne.symm hta)]; exact hg, h₁, h₂, h₃⟩⟩

theorem FillAcc.setVar {ta fa : String} {n len i base : ℕ} {T : ℕ → ℕ} {Cap S : Finset ℕ}
    {τ : Env} (h : FillAcc ta fa n len i base T Cap S τ) {y : String} (hy : y ≠ "i")
    (x : ℕ) : FillAcc ta fa n len i base T Cap S (τ.setVar y x) := by
  obtain ⟨hi, hsub, ⟨f, hf, hfi⟩, ⟨g, hg, h₁, h₂, h₃⟩⟩ := h
  exact ⟨by rw [vars_setVar, if_neg (Ne.symm hy)]; exact hi, hsub,
    ⟨f, by rw [arrs_setVar]; exact hf, hfi⟩, ⟨g, by rw [arrs_setVar]; exact hg, h₁, h₂, h₃⟩⟩

/-- **The fill action.** -/
theorem fillAcc_emits {B n len i base : ℕ} {ta fa : String} {T : ℕ → ℕ}
    {Cap : Finset ℕ} (htf : ta ≠ fa) (hin : i < n) (hnB : n < B) (hlenB : len < B)
    (hcap : base + Cap.card ≤ len) :
    Emits B n 10 ta fa
      (.seq (.store ta (.get fa (.var "i")) (.var "u"))
        (.store fa (.var "i") (.add (.get fa (.var "i")) (.lit 1))))
      Cap (FillAcc ta fa n len i base T Cap) := by
  classical
  rintro S τ z ⟨hi, hsub, ⟨f, hf, hfi⟩, ⟨g, hg, h₁, h₂, h₃⟩⟩ hu hzn hzS hzc
  have hins : insert z S ⊆ Cap := Finset.insert_subset hzc hsub
  have hlt : base + S.card < len := by
    have h := Finset.card_le_card hins
    rw [Finset.card_insert_of_notMem hzS] at h
    omega
  have ei : (Expr.var "i").evalB B τ = some i := by
    have h := evalB_var (B := B) (x := "i") (σ := τ) (by rw [hi]; omega)
    rwa [hi] at h
  have eu : (Expr.var "u").evalB B τ = some z := by
    have h := evalB_var (B := B) (x := "u") (σ := τ) (by rw [hu]; omega)
    rwa [hu] at h
  have egf : (Expr.get fa (.var "i")).evalB B τ = some (base + S.card) :=
    evalB_get ei (by rw [hf, getElem?_arrOf f hin, hfi]) (by omega)
  have hl₁ : base + S.card < (τ.arrs ta).length := by rw [hg, length_arrOf]; exact hlt
  set τ₁ := τ.setArr ta (base + S.card) z with hτ₁
  set g' : ℕ → ℕ := fun q => if q = base + S.card then z else g q with hg'
  have hga₁ : τ₁.arrs ta = arrOf len g' := by
    rw [hτ₁, arrs_setArr, if_pos rfl, hg, set_arrOf]
  have hfa₁ : τ₁.arrs fa = arrOf n f := by rw [hτ₁, arrs_setArr, if_neg (Ne.symm htf)]; exact hf
  have ei₁ : (Expr.var "i").evalB B τ₁ = some i := by
    have hv : τ₁.vars "i" = i := by rw [hτ₁, vars_setArr]; exact hi
    have h := evalB_var (B := B) (x := "i") (σ := τ₁) (by rw [hv]; omega)
    rwa [hv] at h
  have egf₁ : (Expr.get fa (.var "i")).evalB B τ₁ = some (base + S.card) :=
    evalB_get ei₁ (by rw [hfa₁, getElem?_arrOf f hin, hfi]) (by omega)
  have eadd : (Expr.add (.get fa (.var "i")) (.lit 1)).evalB B τ₁
      = some (base + S.card + 1) := by
    have h := evalB_bin (B := B) (op := .add) (σ := τ₁) (m := base + S.card) (n := 1)
      egf₁ (evalB_lit (by omega)) (by simpa [Bop.apply] using (by omega : base + S.card + 1 < B))
    simpa [Bop.apply] using h
  have hl₂ : i < (τ₁.arrs fa).length := by rw [hfa₁, length_arrOf]; exact hin
  have hcards : (insert z S).card = S.card + 1 := Finset.card_insert_of_notMem hzS
  refine ⟨τ₁.setArr fa i (base + S.card + 1), 10,
    ((Run.store egf eu hl₁).seq (Run.store ei₁ eadd hl₂)).mono
      (by simp only [size_get, size_var, size_lit, size_add]; omega), le_rfl, ?_,
    fun y _ => by rw [vars_setArr, hτ₁, vars_setArr],
    fun a ha hb => by rw [arrs_setArr, if_neg hb, hτ₁, arrs_setArr, if_neg ha]⟩
  refine ⟨by rw [vars_setArr, hτ₁, vars_setArr]; exact hi, hins,
    ⟨fun k => if k = i then base + S.card + 1 else f k,
      by rw [arrs_setArr, if_pos rfl, hfa₁, set_arrOf],
      by simp only []; rw [if_true, hcards]; omega⟩,
    ⟨g', by rw [arrs_setArr, if_neg htf, hga₁], ?_, ?_, ?_⟩⟩
  · intro q hq₁ hq₂
    rw [hcards] at hq₂
    by_cases hqe : q = base + S.card
    · rw [hg']; simp only []; rw [if_pos hqe]; exact Finset.mem_insert_self z S
    · rw [hg']; simp only []; rw [if_neg hqe]
      exact Finset.mem_insert_of_mem (h₁ q hq₁ (by omega))
  · intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact ⟨base + S.card, by omega, by rw [hcards]; omega, by simp [hg']⟩
    · obtain ⟨q, hq₁, hq₂, hq₃⟩ := h₂ y hy
      refine ⟨q, hq₁, by rw [hcards]; omega, ?_⟩
      rw [hg']; simp only []; rw [if_neg (by omega)]; exact hq₃
  · intro q hq
    rw [hcards] at hq
    rw [hg']; simp only []; rw [if_neg (by omega)]
    exact h₃ q (by omega)

/-- An accounting may carry along anything the action leaves alone. -/
theorem Emits.and {B n Ka : ℕ} {a₁ a₂ : String} {act : Com} {Cap : Finset ℕ}
    {Acc : Finset ℕ → Env → Prop} {P : Env → Prop}
    (h : Emits B n Ka a₁ a₂ act Cap Acc)
    (hP : ∀ τ τ', P τ → (∀ y, y ≠ "c" → τ'.vars y = τ.vars y) →
      (∀ a, a ≠ a₁ → a ≠ a₂ → τ'.arrs a = τ.arrs a) → P τ') :
    Emits B n Ka a₁ a₂ act Cap (fun S τ => Acc S τ ∧ P τ) := by
  rintro S τ z ⟨hA, hPτ⟩ hu hzn hzS hzc
  obtain ⟨τ', K, hr, hK, hA', hfv, hfa⟩ := h S τ z hA hu hzn hzS hzc
  exact ⟨τ', K, hr, hK, ⟨hA', hP τ τ' hPτ hfv hfa⟩, hfv, hfa⟩

/-! ### What the stamped walks enumerate

The two identities the round's specification is stated in, read on the
sets the walks accumulate. `RamAugment.fratNbrs_eq` is the fraternity
build and `RamAugment.inN_augOr_eq` the assembly; what is added here is
that the union of blocks each of them names on the right *is* the set
the corresponding nested scan accumulates. -/

/-- The offsets of an `InCsr` do not decrease, all the way up. -/
theorem incsr_mono' {n m : ℕ} {D : Orientation n} {IO IT : ℕ → ℕ} (h : InCsr D m IO IT)
    {i k : ℕ} (hik : i ≤ k) (hk : k ≤ n) : IO i ≤ IO k := by
  induction k with
  | zero => rw [show i = 0 by omega]
  | succ k ih =>
      rcases Nat.lt_or_ge i (k + 1) with hi | hi
      · exact le_trans (ih (by omega) (by omega)) (h.mono k (by omega))
      · rw [show i = k + 1 by omega]

theorem incsr_le {n m : ℕ} {D : Orientation n} {IO IT : ℕ → ℕ} (h : InCsr D m IO IT)
    {k : ℕ} (hk : k ≤ n) : IO k ≤ m := by
  rw [← h.last]; exact incsr_mono' h hk le_rfl

/-- **The fraternity walk enumerates the fraternal partners.** The
outer scan runs the out-block of `i` and the inner the in-block of what
it names, and the stamp on `i` itself is the erasure. -/
theorem fratRow_eq {n m : ℕ} {D : Orientation n} {DO DT OO OT : ℕ → ℕ}
    (hcsr : InCsr D m DO DT) (hOle : ∀ z, z < n → OO (z + 1) ≤ m)
    (hOTn : ∀ q, q < m → OT q < n) {i : ℕ} (hi : i < n)
    (hsnd : ∀ q, OO i ≤ q → q < OO (i + 1) → Pts DO DT (OT q) i)
    (hcmp : ∀ z, z < n → Pts DO DT z i → ∃ q, OO i ≤ q ∧ q < OO (i + 1) ∧ OT q = z) :
    rowAcc OO OT (fun w => rowAcc DO DT (fun y => if y = i then ∅ else {y}) w) i
      = valSet (RamAugment.fratNbrs D ⟨i, hi⟩) := by
  classical
  have hDle : ∀ z, z < n → DO (z + 1) ≤ m := fun z hz => incsr_le hcsr (by omega)
  ext y
  rw [mem_rowAcc, mem_valSet]
  constructor
  · rintro ⟨p, hp₁, hp₂, hy⟩
    rw [mem_rowAcc] at hy
    obtain ⟨q, hq₁, hq₂, hy'⟩ := hy
    have hw : OT p < n := hOTn p (lt_of_lt_of_le hp₂ (hOle i hi))
    have hqm : q < m := lt_of_lt_of_le hq₂ (hDle _ hw)
    have hyn : DT q < n := hcsr.target_lt q hqm
    by_cases hdi : DT q = i
    · rw [if_pos hdi] at hy'; exact absurd hy' (by simp)
    · rw [if_neg hdi, Finset.mem_singleton] at hy'
      subst hy'
      refine ⟨hyn, ?_⟩
      rw [RamAugment.fratNbrs_eq, Finset.mem_erase, Finset.mem_biUnion]
      refine ⟨fun hc => hdi (congrArg Fin.val hc), ⟨OT p, hw⟩, ?_, ?_⟩
      · exact (pts_iff_mem_outSet hcsr hw hi).1 (hsnd p hp₁ hp₂)
      · exact (hcsr.mem_iff ⟨OT p, hw⟩ ⟨DT q, hyn⟩).2 ⟨q, hq₁, hq₂, rfl⟩
  · rintro ⟨hyn, hmem⟩
    rw [RamAugment.fratNbrs_eq, Finset.mem_erase, Finset.mem_biUnion] at hmem
    obtain ⟨hne, w, hw, hyw⟩ := hmem
    obtain ⟨p, hp₁, hp₂, hp₃⟩ :=
      hcmp (w : ℕ) w.isLt ((pts_iff_mem_outSet hcsr w.isLt hi).2 (by simpa using hw))
    obtain ⟨q, hq₁, hq₂, hq₃⟩ := (hcsr.mem_iff w ⟨y, hyn⟩).1 hyw
    refine ⟨p, hp₁, hp₂, ?_⟩
    rw [mem_rowAcc]
    refine ⟨q, by rw [hp₃]; exact hq₁, by rw [hp₃]; exact hq₂, ?_⟩
    rw [hq₃, if_neg (fun hc => hne (Fin.ext (by simpa using hc)))]
    exact Finset.mem_singleton_self y

theorem valSet_union {n : ℕ} (S T : Finset (Fin n)) :
    valSet (S ∪ T) = valSet S ∪ valSet T := Finset.image_union _ _

/-- A row of the input block structure names the in-neighbours. -/
theorem rowTgt_eq_inN {n m : ℕ} {D : Orientation n} {DO DT : ℕ → ℕ}
    (hcsr : InCsr D m DO DT) {i : ℕ} (hi : i < n) :
    rowTgt DO DT i = valSet (D.inN ⟨i, hi⟩) := by
  ext y
  rw [mem_rowTgt, mem_valSet]
  constructor
  · rintro ⟨s, h₁, h₂, h₃⟩
    have hsm : s < m := lt_of_lt_of_le h₂ (incsr_le hcsr (by omega))
    have hyn : y < n := h₃ ▸ hcsr.target_lt s hsm
    exact ⟨hyn, (hcsr.mem_iff ⟨i, hi⟩ ⟨y, hyn⟩).2 ⟨s, h₁, h₂, h₃⟩⟩
  · rintro ⟨hyn, hmem⟩
    exact (hcsr.mem_iff ⟨i, hi⟩ ⟨y, hyn⟩).1 hmem

/-- **The transitive walk enumerates the transitive candidates.** The
outer scan runs the in-block of `i` and the inner the in-block of what
it names — so the pair is transitively linked — and the three tests are
`RamAugment.NewArc` read off `sta`, `std` and the ranking. -/
theorem transRow_eq {n m : ℕ} {D : Orientation n} {ρ : Fin n → ℕ} {DO DT R : ℕ → ℕ}
    (hcsr : InCsr D m DO DT) {i : ℕ} (hi : i < n) (hρ : ∀ v : Fin n, ρ v = R (v : ℕ)) :
    rowAcc DO DT (fun w => rowAcc DO DT
        (fun y => if y ∈ valSet (RamAugment.adjSet D ⟨i, hi⟩) then ∅
          else if y ∈ valSet (RamAugment.demandOut D ⟨i, hi⟩) ∧ ¬ R y < R i then ∅
          else {y}) w) i
      = valSet (RamAugment.transCand D ρ ⟨i, hi⟩) := by
  classical
  ext y
  rw [mem_rowAcc, mem_valSet]
  constructor
  · rintro ⟨p, hp₁, hp₂, hy⟩
    rw [mem_rowAcc] at hy
    obtain ⟨q, hq₁, hq₂, hy'⟩ := hy
    have hpm : p < m := lt_of_lt_of_le hp₂ (incsr_le hcsr (by omega))
    have hwn : DT p < n := hcsr.target_lt p hpm
    have hqm : q < m := lt_of_lt_of_le hq₂ (incsr_le hcsr (by omega))
    have hyn : DT q < n := hcsr.target_lt q hqm
    by_cases hA : DT q ∈ valSet (RamAugment.adjSet D ⟨i, hi⟩)
    · rw [if_pos hA] at hy'; exact absurd hy' (by simp)
    by_cases hD : DT q ∈ valSet (RamAugment.demandOut D ⟨i, hi⟩) ∧ ¬ R (DT q) < R i
    · rw [if_neg hA, if_pos hD] at hy'; exact absurd hy' (by simp)
    rw [if_neg hA, if_neg hD, Finset.mem_singleton] at hy'
    subst hy'
    refine ⟨hyn, RamAugment.mem_transCand.2 ⟨⟨⟨DT p, hwn⟩,
      (hcsr.mem_iff ⟨DT p, hwn⟩ ⟨DT q, hyn⟩).2 ⟨q, hq₁, hq₂, rfl⟩,
      (hcsr.mem_iff ⟨i, hi⟩ ⟨DT p, hwn⟩).2 ⟨p, hp₁, hp₂, rfl⟩⟩, ?_, ?_, ?_⟩⟩
    · exact fun hc => hA (mem_valSet.2 ⟨hyn, RamAugment.mem_adjSet.2 hc⟩)
    · exact Or.inl ⟨⟨DT p, hwn⟩,
        (hcsr.mem_iff ⟨DT p, hwn⟩ ⟨DT q, hyn⟩).2 ⟨q, hq₁, hq₂, rfl⟩,
        (hcsr.mem_iff ⟨i, hi⟩ ⟨DT p, hwn⟩).2 ⟨p, hp₁, hp₂, rfl⟩⟩
    · intro hdem
      have hmem : DT q ∈ valSet (RamAugment.demandOut D ⟨i, hi⟩) :=
        mem_valSet.2 ⟨hyn, RamAugment.mem_demandOut.2 hdem⟩
      rw [hρ, hρ]
      exact not_not.1 fun hc => hD ⟨hmem, hc⟩
  · rintro ⟨hyn, hmem⟩
    obtain ⟨⟨w, hyw, hwi⟩, hadj, -, himp⟩ := RamAugment.mem_transCand.1 hmem
    obtain ⟨p, hp₁, hp₂, hp₃⟩ := (hcsr.mem_iff ⟨i, hi⟩ w).1 hwi
    obtain ⟨q, hq₁, hq₂, hq₃⟩ := (hcsr.mem_iff w ⟨y, hyn⟩).1 hyw
    refine ⟨p, hp₁, hp₂, ?_⟩
    rw [mem_rowAcc]
    refine ⟨q, by rw [hp₃]; exact hq₁, by rw [hp₃]; exact hq₂, ?_⟩
    rw [hq₃, if_neg (fun hc => hadj (RamAugment.mem_adjSet.1 (by
      obtain ⟨h', hm'⟩ := mem_valSet.1 hc
      exact hm'))), if_neg (fun hc => ?_)]
    · exact Finset.mem_singleton_self y
    · obtain ⟨hdm, hlt⟩ := hc
      obtain ⟨h', hm'⟩ := mem_valSet.1 hdm
      refine hlt ?_
      have h := himp (RamAugment.mem_demandOut.1 hm')
      rwa [hρ ⟨y, hyn⟩, hρ ⟨i, hi⟩] at h

/-- **The engine block's walk enumerates the fraternal candidates.** -/
theorem fratCandRow_eq {n me : ℕ} {D : Orientation n} {ρ : Fin n → ℕ} {IO IT : ℕ → ℕ}
    (hE : InCsr (RamElim.ElimCert.elimOr (fratGraph D) ρ) me IO IT) {i : ℕ} (hi : i < n) :
    rowAcc IO IT (fun y => if y ∈ valSet (RamAugment.adjSet D ⟨i, hi⟩) then ∅ else {y}) i
      = valSet (RamAugment.fratCand D ρ ⟨i, hi⟩) := by
  classical
  ext y
  rw [mem_rowAcc, mem_valSet]
  constructor
  · rintro ⟨q, hq₁, hq₂, hy⟩
    have hqm : q < me := lt_of_lt_of_le hq₂ (incsr_le hE (by omega))
    have hyn : IT q < n := hE.target_lt q hqm
    by_cases hA : IT q ∈ valSet (RamAugment.adjSet D ⟨i, hi⟩)
    · rw [if_pos hA] at hy; exact absurd hy (by simp)
    rw [if_neg hA, Finset.mem_singleton] at hy
    subst hy
    refine ⟨hyn, ?_⟩
    rw [RamAugment.fratCand, mem_pick]
    exact ⟨(hE.mem_iff ⟨i, hi⟩ ⟨IT q, hyn⟩).2 ⟨q, hq₁, hq₂, rfl⟩,
      fun hc => hA (mem_valSet.2 ⟨hyn, RamAugment.mem_adjSet.2 hc⟩)⟩
  · rintro ⟨hyn, hmem⟩
    rw [RamAugment.fratCand, mem_pick] at hmem
    obtain ⟨hin, hadj⟩ := hmem
    obtain ⟨q, hq₁, hq₂, hq₃⟩ := (hE.mem_iff ⟨i, hi⟩ ⟨y, hyn⟩).1 hin
    refine ⟨q, hq₁, hq₂, ?_⟩
    rw [hq₃, if_neg (fun hc => hadj (RamAugment.mem_adjSet.1 (by
      obtain ⟨h', hm'⟩ := mem_valSet.1 hc
      exact hm')))]
    exact Finset.mem_singleton_self y

/-- **The assembly identity, on the sets the walks accumulate.** The
three lists the assembly emits — the old in-block, the transitive
candidates that pass the rule, the engine's own in-block minus what `D`
already carries — union to the block of `RamAugment.augOr`. -/
theorem asmRow_eq {n m me : ℕ} {D : Orientation n} {ρ : Fin n → ℕ} {DO DT IO IT R : ℕ → ℕ}
    (hcsr : InCsr D m DO DT)
    (hE : InCsr (RamElim.ElimCert.elimOr (fratGraph D) ρ) me IO IT)
    {i : ℕ} (hi : i < n) (hρ : ∀ v : Fin n, ρ v = R (v : ℕ)) :
    rowTgt DO DT i
        ∪ rowAcc DO DT (fun w => rowAcc DO DT
            (fun y => if y ∈ valSet (RamAugment.adjSet D ⟨i, hi⟩) then ∅
              else if y ∈ valSet (RamAugment.demandOut D ⟨i, hi⟩) ∧ ¬ R y < R i then ∅
              else {y}) w) i
        ∪ rowAcc IO IT
            (fun y => if y ∈ valSet (RamAugment.adjSet D ⟨i, hi⟩) then ∅ else {y}) i
      = valSet ((RamAugment.augOr D ρ).inN ⟨i, hi⟩) := by
  rw [rowTgt_eq_inN hcsr hi, transRow_eq hcsr hi hρ, fratCandRow_eq hE hi,
    RamAugment.inN_augOr_eq, valSet_union, valSet_union]

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

/-- The offsets of the out-lists `1 2 | 2 | 3 | ` the sort produces. -/
def demoOO : ℕ → ℕ := fun i => if i = 0 then 0 else if i = 1 then 2 else
  if i = 2 then 3 else 4

/-- Their targets. -/
def demoOT : ℕ → ℕ := fun s => if s = 0 then 1 else if s = 1 then 2 else
  if s = 2 then 2 else 3

-- the in-lists, read back off the block structure as sets
#guard (List.range 4).map (fun i => (rowTgt demoDO demoDT i).sort (· ≤ ·))
  = [[], [0], [0, 1], [2]]

-- the out-lists likewise
#guard (List.range 4).map (fun i => (rowTgt demoOO demoOT i).sort (· ≤ ·))
  = [[1, 2], [2], [3], []]

-- **the fraternity enumeration**: the out-block of `i`, then the in-block of
-- each of its targets, the stamp on `i` erasing the loop — the partners
-- `1 | 0 | | `, which is the single edge `{0,1}` the round's example names
#guard (List.range 4).map (fun i =>
    (rowAcc demoOO demoOT
      (fun w => rowAcc demoDO demoDT (fun y => if y = i then ∅ else {y}) w) i).sort (· ≤ ·))
  = [[1], [0], [], []]

-- and the slot count that edge takes, symmetrized: the round's reported `mf`
#guard ((List.range 4).map (fun i =>
    (rowAcc demoOO demoOT
      (fun w => rowAcc demoDO demoDT (fun y => if y = i then ∅ else {y}) w) i).card)).sum = 2

-- **the exchange**: an out-slot names `w` exactly as often as `w` has
-- in-neighbours, which is what `slotCnt_out_eq` says and what keeps the
-- assembly's stamping walk linear — in-degrees `0, 1, 2, 1` here
#guard (List.range 4).map (slotCnt demoOT 4) = [0, 1, 2, 1]

-- **the transitive enumeration**, unguarded: the in-block of `i`, then the
-- in-block of each of its targets — the candidates `| | 0 | 0 1` before the
-- arc rule, which are the transitive links `0 → 2`, `0 → 3`, `1 → 3`
#guard (List.range 4).map (fun i =>
    (rowAcc demoDO demoDT (fun w => rowAcc demoDO demoDT (fun y => {y}) w) i).sort (· ≤ ·))
  = [[], [], [0], [0, 1]]

end Demo

/-! ### The frontier

What this file discharges of `RamAugment.Implements`, and what it does
not.

**Done — the passes.** The combinators every pass is built from
(`blockScan_run` and `forVerts_run`, and `rowScanC_run` /
`blockScanC_run`, which charge a row *per slot* rather than uniformly —
the nested passes need that, since no constant bounds an out-block),
the row view `Blocks`, the counting-sort arithmetic (`slotCnt`,
`outOff`), the prefix sum `prefixPass_run` (literally the program of
`RamAugment.outPrefix`, `RamAugment.fratPrefix` and
`RamAugment.asmPrefix` alike), the whole of `RamAugment.outPass`
(`outPass_run`, with the block content read back as
`RamAugment.outSet` by `pts_iff_mem_outSet`), and `RamAugment.alvSet`
(`alvSet_run`).

**Done — the stamped-enumeration kit.** The device the four remaining
passes are made of, walked once each and parameterized so that a
counting pass and the fill pass that follows it use the same lemma.

* `Marks s n b S g τ` — the stamp array holds `b` on `S` and `g`
  elsewhere. `stampRow_run` is one row of stamps, `stampNest_run` a
  nested walk of them, and `Marks.trans` composes two walks that write
  the same literal. One lemma serves the walk that *sets* a stamp
  (`b = 1`, a union) and the walk that *clears* it (`b = 0`, a
  difference), which is the pairing every pass of the round uses.
* `Emits B n Ka a₁ a₂ act Cap Acc` — the action's contract: handed a
  vertex in `"u"` that it has not emitted and that lies in the capacity
  `Cap`, it steps the accounting by one, leaves every scalar but `"c"`
  alone and writes no array but its own two. `cntAcc_emits` is the
  counter and `fillAcc_emits` the fill pointer with the cells below it;
  `Emits.and` carries any array fact across an action.
  *The capacity is not decoration*: the fill's store needs room, and
  `base + Cap.card ≤ len` with `z ∈ Cap \ S` is what gives it.
* `Guarded B n Kg grd fe Cap J` — the guard's contract, with the
  emitted set growing by `fe z`, a singleton when the guard fires and
  `∅` when it does not, so no decidability rides in the statement.
  `guardFrat_of_emits`, `guardAsmIn_of_emits` and
  `guardAsmTrans_of_emits` are the round's three guards, at
  `Ka + 8`, `Ka + 13` and `Ka + 24`; `emitBranch_run` is their common
  emitting branch and `stampCond` the read of a stamp cell.
* `emitRow_run`, `emitAllRow_run` and `emitNest_run` are the walks:
  one row guarded, one row unguarded (for the old in-block, which
  carries no duplicate), and the nested walk of `RamAugment.fratScan`
  and of the transitive half of `RamAugment.asmEmit`. Each accumulates
  `accUpto` / `rowAcc` — the union over the slots passed — and each
  exports the scalar frame the next pass needs.

**Done — the mathematics.** The identities that say what those sets
*are*, so that nothing downstream has to look at a slot again.

* `fratRow_eq`: the fraternity walk's set is `valSet (fratNbrs D i)`.
* `transRow_eq`, `fratCandRow_eq` and `asmRow_eq`: the assembly's three
  lists union to `valSet ((augOr D ρ).inN i)`, which is
  `RamAugment.inN_augOr_eq` in the walk's vocabulary. `asmRow_eq` is
  the whole content of the assembly pass.
* `slotCnt_out_eq`: an out-slot names `w` exactly as often as `w` has
  in-neighbours. This is the one non-obvious *cost* fact of the round:
  `RamAugment.asmStamp` walks the out-block of every vertex the current
  one points at, and no constant bounds an out-block, so the pass is
  linear only by this exchange. `tile_filter_card` (the rows tile the
  slots) and `sum_slot_weight` (a weighted count over the slots is a
  weighted count over the targets) are what it is proved from, and
  `sum_slot_weight` is also what turns a per-slot cost into a bound.

All of it is checked on `RamAugment.Demo`'s four-vertex orientation in
the section above: the in-lists and out-lists read back off the block
structures, the fraternity enumeration coming out `1 | 0 | | ` with two
slots — the round's own reported `mf` — the exchange coming out at the
in-degrees, and the transitive enumeration coming out at the three
transitive links.

**Open.** The four passes' assembly and the sequencing. Everything
below is stated in the vocabulary above and needs no new mathematics.

1. `RamAugment.fratCount` and `RamAugment.fratFill`. One turn is
   `c := 0` (or nothing), `stf[i] := 1`, `emitNest_run` over
   `ooff`/`otg` then `doff`/`dtg` with `guardFrat_of_emits`,
   `stampNest_run` over the same two at `b = 0`, `stf[i] := 0`, and
   `off[i+1] := c`. The invariant of the turn is
   `Marks "stf" n 1 ({i} ∪ S) (fun _ => 0)` together with `CntAcc`
   (resp. `FillAcc "tgt" "ffl"`) and the four block-structure facts,
   carried by `Emits.and`. The emitted set is `fratRow_eq`'s, so the
   count is `(fratNbrs D i).card` and `RamAugment.fratSlots` is the sum
   — which is `off n` after `fratPrefix`, hence `mf`.
   `CsrSimple`'s `nodup` comes from `FillAcc`'s window clause: the
   cells below the pointer name the emitted set and the pointer counts
   them, so a repeat would make the count too small.
2. `RamAugment.asmStamp` is `stampRow_run` twice and `stampNest_run`
   once at `b`, giving `Marks "sta" n 1 (valSet (adjSet D i))` and
   `Marks "std" n 1 (valSet (demandOut D i))` at `b = 1` and their
   erasure at `b = 0` — the identities being `RamAugment.mem_adjSet`
   and `RamAugment.mem_demandOut`. `RamAugment.asmEmit` is
   `emitAllRow_run` (freshness from `InCsr`'s `len` and `mem_iff` by a
   card argument, since `E₀ = ∅` there), then `emitNest_run` with
   `guardAsmTrans_of_emits`, then `emitRow_run` with
   `guardAsmIn_of_emits`; `RamAugment.asmClearE` is `stampNest_run` and
   `stampRow_run` at `b = 0`. `asmRow_eq` is what the three emit.
3. The `RamElim.elimCom` call. `RamAugment.ElimAvail` gives
   `RamElim.ElimMem`, which carries the certificate but **not** the
   rank bound `∀ v < n, R v < n` — and the assembly reads `rnk[u]`, so
   without it there is no run. So the engine's five phase specs have to
   be re-sequenced here exactly as `RamDriverCompose.elimRank_spec`
   does, with a postcondition of `RamElim.ElimMem ∧ ∃ R, rnk = arrOf n
   R ∧ ∀ v < n, R v < n`. `elimRank_spec` itself is *not* enough: it
   post-processes to `RamElim.ElimPost`, which drops
   `RamElim.ElimCert` (`min_deg` and `attained` are nowhere in it), and
   `RamAugment.AugMem` asks for the certificate. Importing
   `RamDriverCompose` is acyclic but buys nothing for that reason.
4. The sequencing into `implements`, in the shape wave C2 pinned
   against `RamDriver.AugAvail`:
   `theorem implements {B n d nf W m : ℕ} {D : Orientation n}
   {DO DT : ℕ → ℕ} : RamAugment.Implements B n d nf W m D DO DT`,
   with no theorem-level hypotheses. `RamAugment.ElimAvail` is then
   unused, by 3.

**The cost, and why it fits.** Every walk above is charged per slot of
the block structure it walks. The out-lists and the fraternity build
are `O(m + n·d²)` by `Blocks.sum_rowLen` and the uniform bound `d` on
an in-block; the assembly's stamping walk is `O(n·d²)` by
`slotCnt_out_eq` and `sum_slot_weight`; the engine's is `elimCost n nf`
with `nf = fratSlots D ≤ n·d²`. With `augWidth n d ≤ W` that is
`O(n + W)` with a constant well inside `RamAugment.augCost`'s `8000`. -/

end Lax3Proofs.RamDriverAugment
